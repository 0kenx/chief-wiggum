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
            "blocking": true,
            "readonly": false,
            "commit_after": true
        },
        {
            "id": "step-two",
            "agent": "agent-beta",
            "blocking": false,
            "readonly": true,
            "depends_on": "step-one",
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
    assert_equals "step-one" "$(pipeline_get 1 ".depends_on")" "Second step depends_on should be step-one"
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

test_load_unknown_depends_on_reference() {
    cat > "$TEST_DIR/bad-dep.json" << 'PIPE'
{
    "name": "bad-dep-pipeline",
    "steps": [
        { "id": "step-a", "agent": "agent-one" },
        { "id": "step-b", "agent": "agent-two", "depends_on": "nonexistent-step" }
    ]
}
PIPE

    pipeline_load "$TEST_DIR/bad-dep.json" 2>/dev/null
    local rc=$?

    assert_equals "1" "$rc" "pipeline_load should return 1 for unknown depends_on reference"
}

# =============================================================================
# pipeline_load - Field Parsing Tests
# =============================================================================

test_load_blocking_readonly_enabled_by_commit_after() {
    cat > "$TEST_DIR/fields.json" << 'PIPE'
{
    "name": "fields-pipeline",
    "steps": [
        {
            "id": "step-x",
            "agent": "agent-x",
            "blocking": true,
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
    assert_equals "true" "$(pipeline_get 0 ".blocking" "true")" "First step blocking should be true"
    assert_equals "true" "$(pipeline_get 1 ".blocking" "true")" "Second step blocking should default to true"
    assert_equals "true" "$(pipeline_get 0 ".readonly" "false")" "First step readonly should be true"
    assert_equals "false" "$(pipeline_get 1 ".readonly" "false")" "Second step readonly should be false"
    assert_equals "FEATURE_FLAG_X" "$(pipeline_get 0 ".enabled_by")" "First step enabled_by should be FEATURE_FLAG_X"
    assert_equals "" "$(pipeline_get 1 ".enabled_by")" "Second step enabled_by should be empty"
    assert_equals "true" "$(pipeline_get 0 ".commit_after" "false")" "First step commit_after should be true"
    assert_equals "false" "$(pipeline_get 1 ".commit_after" "false")" "Second step commit_after should be false"
}

test_load_fix_config() {
    cat > "$TEST_DIR/fix.json" << 'PIPE'
{
    "name": "fix-pipeline",
    "steps": [
        {
            "id": "audit-step",
            "agent": "security-audit",
            "fix": {
                "id": "audit-fix",
                "agent": "security-fix",
                "max_attempts": 5,
                "commit_after": true
            }
        },
        {
            "id": "plain-step",
            "agent": "plain-agent"
        }
    ]
}
PIPE

    pipeline_load "$TEST_DIR/fix.json"
    local rc=$?

    assert_equals "0" "$rc" "pipeline_load should succeed"
    assert_equals "security-fix" "$(pipeline_get_fix 0 ".agent")" "First step fix agent should be security-fix"
    assert_equals "5" "$(pipeline_get_fix 0 ".max_attempts" "2")" "First step fix max_attempts should be 5"
    assert_equals "true" "$(pipeline_get_fix 0 ".commit_after" "true")" "First step fix commit_after should be true"
    assert_equals "" "$(pipeline_get_fix 1 ".agent")" "Second step fix agent should be empty"
    assert_equals "2" "$(pipeline_get_fix 1 ".max_attempts" "2")" "Second step fix max_attempts should default to 2"
    assert_equals "true" "$(pipeline_get_fix 1 ".commit_after" "true")" "Second step fix commit_after should default to true"
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
# pipeline_get / pipeline_get_json / pipeline_get_fix Tests
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
run_test test_load_unknown_depends_on_reference

# pipeline_load - field parsing
run_test test_load_blocking_readonly_enabled_by_commit_after
run_test test_load_fix_config
run_test test_load_hooks

# pipeline_load_builtin_defaults
run_test test_builtin_defaults_populates_seven_steps
run_test test_builtin_defaults_correct_step_ids

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
