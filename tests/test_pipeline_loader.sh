#!/usr/bin/env bash
# Tests for lib/pipeline/pipeline-loader.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
export LOG_FILE="/dev/null"
source "$WIGGUM_HOME/lib/core/logger.sh"

# Reset the loader guard so we can source it
unset _PIPELINE_LOADER_LOADED
source "$WIGGUM_HOME/lib/pipeline/pipeline-loader.sh"

TEST_DIR=""
setup() {
    TEST_DIR=$(mktemp -d)
    # Reset pipeline state
    _PIPELINE_JSON_FILE=""
    _PIPELINE_JSON=""
    _PIPELINE_STEP_COUNT=0
    PIPELINE_NAME=""
}
teardown() {
    rm -rf "$TEST_DIR"
}

# =============================================================================
# pipeline_load - Valid Input Tests
# =============================================================================

test_load_valid_two_step_pipeline() {
    cat > "$TEST_DIR/pipeline.json" << 'PIPE'
{
    "name": "test-pipeline",
    "steps": [
        {
            "id": "step-one",
            "agent": "agent-alpha",
            "max": 3,
            "on_result": {
                "FAIL": { "jump": "abort" }
            },
            "readonly": false,
            "commit_after": true
        },
        {
            "id": "step-two",
            "agent": "agent-beta",
            "readonly": true,
            "commit_after": false
        }
    ]
}
PIPE

    pipeline_load "$TEST_DIR/pipeline.json"
    local rc=$?

    assert_equals "0" "$rc" "pipeline_load should return 0 for valid input"
    assert_equals "test-pipeline" "$PIPELINE_NAME" "Pipeline name should be set"
    assert_equals "2" "$(pipeline_step_count)" "Should have 2 steps"
    assert_equals "step-one" "$(pipeline_get 0 ".id")" "First step ID should be step-one"
    assert_equals "step-two" "$(pipeline_get 1 ".id")" "Second step ID should be step-two"
    assert_equals "agent-alpha" "$(pipeline_get 0 ".agent")" "First agent should be agent-alpha"
    assert_equals "agent-beta" "$(pipeline_get 1 ".agent")" "Second agent should be agent-beta"
    assert_equals "3" "$(pipeline_get_max 0)" "First step max should be 3"
    assert_equals "0" "$(pipeline_get_max 1)" "Second step max should be 0 (unlimited)"
}

# =============================================================================
# pipeline_load - Error Handling Tests
# =============================================================================

test_load_missing_file() {
    pipeline_load "$TEST_DIR/nonexistent.json" 2>/dev/null
    local rc=$?

    assert_equals "1" "$rc" "pipeline_load should return 1 for missing file"
}

test_load_invalid_json() {
    cat > "$TEST_DIR/bad.json" << 'PIPE'
{ this is not valid json [[[
PIPE

    pipeline_load "$TEST_DIR/bad.json" 2>/dev/null
    local rc=$?

    assert_equals "1" "$rc" "pipeline_load should return 1 for invalid JSON"
}

test_load_empty_steps_array() {
    cat > "$TEST_DIR/empty.json" << 'PIPE'
{
    "name": "empty-pipeline",
    "steps": []
}
PIPE

    pipeline_load "$TEST_DIR/empty.json" 2>/dev/null
    local rc=$?

    assert_equals "1" "$rc" "pipeline_load should return 1 for empty steps array"
}

test_load_duplicate_step_ids() {
    cat > "$TEST_DIR/dupes.json" << 'PIPE'
{
    "name": "dupe-pipeline",
    "steps": [
        { "id": "step-a", "agent": "agent-one" },
        { "id": "step-a", "agent": "agent-two" }
    ]
}
PIPE

    pipeline_load "$TEST_DIR/dupes.json" 2>/dev/null
    local rc=$?

    assert_equals "1" "$rc" "pipeline_load should return 1 for duplicate step IDs"
}

test_load_missing_step_id() {
    cat > "$TEST_DIR/no-id.json" << 'PIPE'
{
    "name": "no-id-pipeline",
    "steps": [
        { "agent": "agent-one" }
    ]
}
PIPE

    pipeline_load "$TEST_DIR/no-id.json" 2>/dev/null
    local rc=$?

    assert_equals "1" "$rc" "pipeline_load should return 1 for missing step ID"
}

test_load_missing_agent_field() {
    cat > "$TEST_DIR/no-agent.json" << 'PIPE'
{
    "name": "no-agent-pipeline",
    "steps": [
        { "id": "step-a" }
    ]
}
PIPE

    pipeline_load "$TEST_DIR/no-agent.json" 2>/dev/null
    local rc=$?

    assert_equals "1" "$rc" "pipeline_load should return 1 for missing agent field"
}

# =============================================================================
# pipeline_load - Field Parsing Tests
# =============================================================================

test_load_readonly_enabled_by_commit_after() {
    cat > "$TEST_DIR/fields.json" << 'PIPE'
{
    "name": "fields-pipeline",
    "steps": [
        {
            "id": "step-x",
            "agent": "agent-x",
            "max": 5,
            "on_max": "next",
            "readonly": true,
            "enabled_by": "FEATURE_FLAG_X",
            "commit_after": true
        },
        {
            "id": "step-y",
            "agent": "agent-y",
            "readonly": false,
            "enabled_by": "",
            "commit_after": false
        }
    ]
}
PIPE

    pipeline_load "$TEST_DIR/fields.json"
    local rc=$?

    assert_equals "0" "$rc" "pipeline_load should succeed"
    assert_equals "true" "$(pipeline_get 0 ".readonly" "false")" "First step readonly should be true"
    assert_equals "false" "$(pipeline_get 1 ".readonly" "false")" "Second step readonly should be false"
    assert_equals "FEATURE_FLAG_X" "$(pipeline_get 0 ".enabled_by")" "First step enabled_by should be FEATURE_FLAG_X"
    assert_equals "" "$(pipeline_get 1 ".enabled_by")" "Second step enabled_by should be empty"
    assert_equals "true" "$(pipeline_get 0 ".commit_after" "false")" "First step commit_after should be true"
    assert_equals "false" "$(pipeline_get 1 ".commit_after" "false")" "Second step commit_after should be false"
    assert_equals "5" "$(pipeline_get_max 0)" "First step max should be 5"
    assert_equals "next" "$(pipeline_get_on_max 0)" "First step on_max should be next"
    assert_equals "0" "$(pipeline_get_max 1)" "Second step max should default to 0"
    assert_equals "next" "$(pipeline_get_on_max 1)" "Second step on_max should default to next"
}

test_load_on_result_handlers() {
    cat > "$TEST_DIR/on-result.json" << 'PIPE'
{
    "name": "on-result-pipeline",
    "steps": [
        {
            "id": "step-a",
            "agent": "agent-a",
            "on_result": {
                "FAIL": { "jump": "abort" },
                "FIX": {
                    "id": "fix-a",
                    "agent": "agent-fix",
                    "max": 2,
                    "commit_after": true
                }
            }
        },
        {
            "id": "step-b",
            "agent": "agent-b"
        }
    ]
}
PIPE

    pipeline_load "$TEST_DIR/on-result.json"
    local rc=$?

    assert_equals "0" "$rc" "pipeline_load should succeed"

    # Check jump handler
    local fail_handler
    fail_handler=$(pipeline_get_on_result 0 "FAIL")
    assert_output_contains "$fail_handler" "abort" "FAIL handler should reference abort"

    # Check inline agent handler
    local fix_handler
    fix_handler=$(pipeline_get_on_result 0 "FIX")
    assert_output_contains "$fix_handler" "agent-fix" "FIX handler should reference agent-fix"
    assert_output_contains "$fix_handler" "fix-a" "FIX handler should have id fix-a"

    # No handler for PASS
    local pass_handler
    pass_handler=$(pipeline_get_on_result 0 "PASS")
    assert_equals "" "$pass_handler" "PASS handler should be empty (unhandled)"

    # No on_result for step-b
    local step_b_handler
    step_b_handler=$(pipeline_get_on_result 1 "FAIL")
    assert_equals "" "$step_b_handler" "step-b should have no FAIL handler"
}

test_load_max_and_on_max() {
    cat > "$TEST_DIR/max.json" << 'PIPE'
{
    "name": "max-pipeline",
    "steps": [
        {
            "id": "bounded",
            "agent": "agent-a",
            "max": 3,
            "on_max": "next"
        },
        {
            "id": "bounded-abort",
            "agent": "agent-b",
            "max": 5
        },
        {
            "id": "unbounded",
            "agent": "agent-c"
        }
    ]
}
PIPE

    pipeline_load "$TEST_DIR/max.json"
    local rc=$?

    assert_equals "0" "$rc" "pipeline_load should succeed"
    assert_equals "3" "$(pipeline_get_max 0)" "First step max should be 3"
    assert_equals "next" "$(pipeline_get_on_max 0)" "First step on_max should be next"
    assert_equals "5" "$(pipeline_get_max 1)" "Second step max should be 5"
    assert_equals "next" "$(pipeline_get_on_max 1)" "Second step on_max should default to next"
    assert_equals "0" "$(pipeline_get_max 2)" "Third step max should be 0 (unlimited)"
    assert_equals "next" "$(pipeline_get_on_max 2)" "Third step on_max should default to next"
}

test_load_validates_jump_targets() {
    cat > "$TEST_DIR/bad-jump.json" << 'PIPE'
{
    "name": "bad-jump-pipeline",
    "steps": [
        {
            "id": "step-a",
            "agent": "agent-a",
            "on_result": {
                "FAIL": { "jump": "nonexistent-step" }
            }
        }
    ]
}
PIPE

    pipeline_load "$TEST_DIR/bad-jump.json" 2>/dev/null
    local rc=$?

    assert_equals "1" "$rc" "pipeline_load should return 1 for unknown jump target"
}

test_load_allows_special_jump_targets() {
    cat > "$TEST_DIR/special-jumps.json" << 'PIPE'
{
    "name": "special-jumps-pipeline",
    "steps": [
        {
            "id": "step-a",
            "agent": "agent-a",
            "on_result": {
                "FAIL": { "jump": "abort" },
                "FIX": { "jump": "self" }
            }
        },
        {
            "id": "step-b",
            "agent": "agent-b",
            "on_result": {
                "FAIL": { "jump": "prev" },
                "STOP": { "jump": "next" }
            }
        },
        {
            "id": "step-c",
            "agent": "agent-c",
            "on_result": {
                "FAIL": { "jump": "step-a" }
            }
        }
    ]
}
PIPE

    pipeline_load "$TEST_DIR/special-jumps.json" 2>/dev/null
    local rc=$?

    assert_equals "0" "$rc" "pipeline_load should accept special jump targets (self/prev/next/abort) and valid step IDs"
}

test_load_hooks() {
    cat > "$TEST_DIR/hooks.json" << 'PIPE'
{
    "name": "hooks-pipeline",
    "steps": [
        {
            "id": "hooked-step",
            "agent": "hooked-agent",
            "hooks": {
                "pre": ["echo pre-hook-1", "echo pre-hook-2"],
                "post": ["echo post-hook-1"]
            }
        },
        {
            "id": "no-hooks-step",
            "agent": "plain-agent"
        }
    ]
}
PIPE

    pipeline_load "$TEST_DIR/hooks.json"
    local rc=$?

    assert_equals "0" "$rc" "pipeline_load should succeed"
    # The hooks are queried as JSON arrays
    local pre_hooks
    pre_hooks=$(pipeline_get_json 0 ".hooks.pre" "[]")
    assert_output_contains "$pre_hooks" "pre-hook-1" "First step pre hooks should contain pre-hook-1"
    assert_output_contains "$pre_hooks" "pre-hook-2" "First step pre hooks should contain pre-hook-2"
    local post_hooks
    post_hooks=$(pipeline_get_json 0 ".hooks.post" "[]")
    assert_output_contains "$post_hooks" "post-hook-1" "First step post hooks should contain post-hook-1"
    assert_equals "[]" "$(pipeline_get_json 1 ".hooks.pre" "[]")" "Second step pre hooks should be empty array"
    assert_equals "[]" "$(pipeline_get_json 1 ".hooks.post" "[]")" "Second step post hooks should be empty array"
}

# =============================================================================
# pipeline_load_builtin_defaults Tests
# =============================================================================

test_builtin_defaults_populates_seven_steps() {
    pipeline_load_builtin_defaults

    assert_equals "7" "$(pipeline_step_count)" "Built-in defaults should have 7 steps"
}

test_builtin_defaults_correct_step_ids() {
    pipeline_load_builtin_defaults

    assert_equals "planning" "$(pipeline_get 0 ".id")" "Step 0 ID should be planning"
    assert_equals "execution" "$(pipeline_get 1 ".id")" "Step 1 ID should be execution"
    assert_equals "summary" "$(pipeline_get 2 ".id")" "Step 2 ID should be summary"
    assert_equals "audit" "$(pipeline_get 3 ".id")" "Step 3 ID should be audit"
    assert_equals "test" "$(pipeline_get 4 ".id")" "Step 4 ID should be test"
    assert_equals "docs" "$(pipeline_get 5 ".id")" "Step 5 ID should be docs"
    assert_equals "validation" "$(pipeline_get 6 ".id")" "Step 6 ID should be validation"
    assert_equals "builtin-default" "$PIPELINE_NAME" "Pipeline name should be builtin-default"
}

test_builtin_defaults_has_on_result() {
    pipeline_load_builtin_defaults

    # execution should have FAIL->abort
    local exec_fail
    exec_fail=$(pipeline_get_on_result 1 "FAIL")
    assert_output_contains "$exec_fail" "abort" "Execution FAIL should jump to abort"

    # audit should have FIX inline agent
    local audit_fix
    audit_fix=$(pipeline_get_on_result 3 "FIX")
    assert_output_contains "$audit_fix" "audit-fix" "Audit FIX should have inline agent audit-fix"
    assert_output_contains "$audit_fix" "engineering.security-fix" "Audit FIX should reference security-fix agent"

    # execution should have max:3
    assert_equals "3" "$(pipeline_get_max 1)" "Execution max should be 3"

    # planning should have no FAIL handler (non-blocking equivalent)
    local plan_fail
    plan_fail=$(pipeline_get_on_result 0 "FAIL")
    assert_equals "" "$plan_fail" "Planning should have no FAIL handler"
}

# =============================================================================
# pipeline_resolve Tests
# =============================================================================

test_resolve_cli_pipeline_name() {
    # Create the config/pipelines directory with named pipeline
    mkdir -p "$WIGGUM_HOME/config/pipelines"
    cat > "$WIGGUM_HOME/config/pipelines/custom.json" << 'PIPE'
{"name": "custom", "steps": [{"id": "s1", "agent": "a1"}]}
PIPE

    local result
    result=$(pipeline_resolve "$TEST_DIR" "TASK-001" "custom")

    assert_equals "$WIGGUM_HOME/config/pipelines/custom.json" "$result" \
        "Should resolve CLI pipeline name to config/pipelines/<name>.json"

    # Clean up
    rm -f "$WIGGUM_HOME/config/pipelines/custom.json"
    rmdir "$WIGGUM_HOME/config/pipelines" 2>/dev/null || true
}

test_resolve_per_task_override() {
    # Create per-task pipeline override
    mkdir -p "$TEST_DIR/.ralph/pipelines"
    cat > "$TEST_DIR/.ralph/pipelines/TASK-042.json" << 'PIPE'
{"name": "task-specific", "steps": [{"id": "s1", "agent": "a1"}]}
PIPE

    local result
    result=$(pipeline_resolve "$TEST_DIR" "TASK-042" "")

    assert_equals "$TEST_DIR/.ralph/pipelines/TASK-042.json" "$result" \
        "Should resolve per-task override in .ralph/pipelines/<task-id>.json"
}

test_resolve_project_default() {
    # Create the project default pipeline config
    # Save any existing config/pipeline.json
    local backup=""
    if [ -f "$WIGGUM_HOME/config/pipeline.json" ]; then
        backup=$(cat "$WIGGUM_HOME/config/pipeline.json")
    fi

    mkdir -p "$WIGGUM_HOME/config"
    cat > "$WIGGUM_HOME/config/pipeline.json" << 'PIPE'
{"name": "project-default", "steps": [{"id": "s1", "agent": "a1"}]}
PIPE

    local result
    result=$(pipeline_resolve "$TEST_DIR" "TASK-001" "")

    assert_equals "$WIGGUM_HOME/config/pipeline.json" "$result" \
        "Should resolve project default config/pipeline.json"

    # Restore original
    if [ -n "$backup" ]; then
        echo "$backup" > "$WIGGUM_HOME/config/pipeline.json"
    else
        rm -f "$WIGGUM_HOME/config/pipeline.json"
    fi
}

test_resolve_returns_empty_for_builtin_fallback() {
    # Ensure no config files exist for this test
    # Use a project dir with no .ralph/pipelines and no matching config
    local isolated_dir
    isolated_dir=$(mktemp -d)

    # Temporarily move config/pipeline.json if it exists
    local had_default=0
    if [ -f "$WIGGUM_HOME/config/pipeline.json" ]; then
        mv "$WIGGUM_HOME/config/pipeline.json" "$WIGGUM_HOME/config/pipeline.json.bak"
        had_default=1
    fi

    local result
    result=$(pipeline_resolve "$isolated_dir" "TASK-999" "")

    assert_equals "" "$result" \
        "Should return empty string when no config is found (builtin fallback)"

    # Restore
    if [ "$had_default" -eq 1 ]; then
        mv "$WIGGUM_HOME/config/pipeline.json.bak" "$WIGGUM_HOME/config/pipeline.json"
    fi
    rm -rf "$isolated_dir"
}

# =============================================================================
# pipeline_find_step_index Tests
# =============================================================================

test_find_step_index_returns_correct_index() {
    # Load a known pipeline first
    cat > "$TEST_DIR/idx.json" << 'PIPE'
{"name":"idx","steps":[{"id":"alpha","agent":"a"},{"id":"beta","agent":"b"},{"id":"gamma","agent":"c"},{"id":"delta","agent":"d"}]}
PIPE
    pipeline_load "$TEST_DIR/idx.json"

    local idx
    idx=$(pipeline_find_step_index "gamma")

    assert_equals "2" "$idx" "Index of 'gamma' should be 2"
}

test_find_step_index_returns_negative_one_for_unknown() {
    cat > "$TEST_DIR/idx2.json" << 'PIPE'
{"name":"idx2","steps":[{"id":"alpha","agent":"a"},{"id":"beta","agent":"b"},{"id":"gamma","agent":"c"}]}
PIPE
    pipeline_load "$TEST_DIR/idx2.json"

    local idx
    idx=$(pipeline_find_step_index "nonexistent")

    assert_equals "-1" "$idx" "Index of unknown step should be -1"
}

# =============================================================================
# pipeline_step_count Tests
# =============================================================================

test_step_count_returns_correct_count() {
    cat > "$TEST_DIR/count.json" << 'PIPE'
{"name":"cnt","steps":[{"id":"one","agent":"a"},{"id":"two","agent":"b"},{"id":"three","agent":"c"},{"id":"four","agent":"d"},{"id":"five","agent":"e"}]}
PIPE
    pipeline_load "$TEST_DIR/count.json"

    local count
    count=$(pipeline_step_count)

    assert_equals "5" "$count" "Step count should be 5"
}

# =============================================================================
# pipeline_get / pipeline_get_json Tests
# =============================================================================

test_pipeline_get_returns_default_for_missing_field() {
    cat > "$TEST_DIR/get.json" << 'PIPE'
{"name":"get","steps":[{"id":"s1","agent":"a1"}]}
PIPE
    pipeline_load "$TEST_DIR/get.json"

    assert_equals "mydefault" "$(pipeline_get 0 ".nonexistent" "mydefault")" \
        "pipeline_get should return default for missing field"
}

test_pipeline_get_json_returns_config_object() {
    cat > "$TEST_DIR/getjson.json" << 'PIPE'
{"name":"getjson","steps":[{"id":"s1","agent":"a1","config":{"max_turns":99}}]}
PIPE
    pipeline_load "$TEST_DIR/getjson.json"

    local config
    config=$(pipeline_get_json 0 ".config")

    assert_output_contains "$config" "max_turns" "Config should contain max_turns"
    assert_output_contains "$config" "99" "Config should contain value 99"
}

# =============================================================================
# Run All Tests
# =============================================================================

# pipeline_load - valid input
run_test test_load_valid_two_step_pipeline

# pipeline_load - error handling
run_test test_load_missing_file
run_test test_load_invalid_json
run_test test_load_empty_steps_array
run_test test_load_duplicate_step_ids
run_test test_load_missing_step_id
run_test test_load_missing_agent_field

# pipeline_load - field parsing
run_test test_load_readonly_enabled_by_commit_after
run_test test_load_on_result_handlers
run_test test_load_max_and_on_max
run_test test_load_validates_jump_targets
run_test test_load_allows_special_jump_targets
run_test test_load_hooks

# pipeline_load_builtin_defaults
run_test test_builtin_defaults_populates_seven_steps
run_test test_builtin_defaults_correct_step_ids
run_test test_builtin_defaults_has_on_result

# pipeline_resolve
run_test test_resolve_cli_pipeline_name
run_test test_resolve_per_task_override
run_test test_resolve_project_default
run_test test_resolve_returns_empty_for_builtin_fallback

# pipeline_find_step_index
run_test test_find_step_index_returns_correct_index
run_test test_find_step_index_returns_negative_one_for_unknown

# pipeline_step_count
run_test test_step_count_returns_correct_count

# pipeline_get
run_test test_pipeline_get_returns_default_for_missing_field
run_test test_pipeline_get_json_returns_config_object

print_test_summary
exit_with_test_result
