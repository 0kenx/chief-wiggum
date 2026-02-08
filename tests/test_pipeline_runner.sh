#!/usr/bin/env bash
# =============================================================================
# Tests for lib/pipeline/pipeline-runner.sh
#
# Tests pipeline execution including:
# - Step sequencing (runs in order)
# - enabled_by condition checking
# - on_result jump-based control flow
# - max visits and on_max handling
# - Inline agent handlers (fix loop)
# - Step config writing
# - start_from_step resolution
# =============================================================================

set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

TEST_DIR=""

# Stub functions that pipeline-runner.sh expects from system.task-worker context
_phase_start() { :; }
_phase_end() { :; }
_commit_subagent_changes() { :; }
export -f _phase_start _phase_end _commit_subagent_changes

# Source modules once at top level (pipeline-runner.sh has _pipeline_runner_reset
# for per-test state cleanup, avoiding expensive re-sourcing of the module chain)
export LOG_FILE="/dev/null"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/utils/activity-log.sh"
source "$WIGGUM_HOME/lib/pipeline/pipeline-loader.sh"
source "$WIGGUM_HOME/lib/pipeline/pipeline-runner.sh"

# Monotonic counter for unique result filenames (avoids forking date +%s)
_MOCK_EPOCH=0
_mock_epoch() { echo "$(( ++_MOCK_EPOCH ))"; }

setup() {
    TEST_DIR=$(mktemp -d)
    export LOG_FILE="$TEST_DIR/test.log"
    export WIGGUM_TASK_ID="TEST-001"

    # Create project and worker dirs
    mkdir -p "$TEST_DIR/project/.ralph/logs"
    mkdir -p "$TEST_DIR/worker/workspace" "$TEST_DIR/worker/logs" "$TEST_DIR/worker/results"

    activity_init "$TEST_DIR/project"
    _pipeline_runner_reset
}

teardown() {
    unset WIGGUM_TASK_ID WIGGUM_STEP_ID WIGGUM_STEP_READONLY
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# Helper: Create a pipeline JSON file
_create_pipeline() {
    local file="$1"
    local json="$2"
    echo "$json" > "$file"
    pipeline_load "$file" 2>/dev/null
}

# Helper: Create a mock agent that records invocations
_create_mock_agent() {
    local agent_name="$1"
    local result="${2:-PASS}"  # PASS, FAIL, FIX, STOP

    local agent_dir="$TEST_DIR/fake-home/lib/agents"
    mkdir -p "$agent_dir"

    cat > "$agent_dir/${agent_name}.sh" << EOF
agent_required_paths() { echo ""; }
agent_run() {
    local worker_dir="\$1"
    echo "${agent_name}" >> "$TEST_DIR/agent_invocations.txt"
    # Write result file in correct format: <epoch>-<step_id>-result.json
    local step_id="\${WIGGUM_STEP_ID:-unknown}"
    local epoch=\$(_mock_epoch)
    mkdir -p "\$worker_dir/results"
    echo '{"outputs": {"gate_result": "${result}"}}' > "\$worker_dir/results/\${epoch}-\${step_id}-result.json"
}
EOF
}

# Helper: Create a counting agent that returns different results on successive calls
_create_counting_agent() {
    local agent_name="$1"
    shift
    # Remaining args are results in order (e.g., "FIX" "PASS")
    local results=("$@")

    local agent_dir="$TEST_DIR/fake-home/lib/agents"
    mkdir -p "$agent_dir"

    local counter_file="$TEST_DIR/counter_${agent_name}.txt"
    echo "0" > "$counter_file"

    # Build results array in bash syntax
    local results_str=""
    for r in "${results[@]}"; do
        results_str="${results_str} \"$r\""
    done

    cat > "$agent_dir/${agent_name}.sh" << EOF
agent_required_paths() { echo ""; }
agent_run() {
    local worker_dir="\$1"
    echo "${agent_name}" >> "$TEST_DIR/agent_invocations.txt"
    local counter_file="$counter_file"
    local count=\$(cat "\$counter_file")
    local results=(${results_str})
    local result_count=\${#results[@]}
    local idx=\$((count % result_count))
    local result="\${results[\$idx]}"
    echo \$((count + 1)) > "\$counter_file"
    local step_id="\${WIGGUM_STEP_ID:-unknown}"
    local epoch=\$(_mock_epoch)
    mkdir -p "\$worker_dir/results"
    echo "{\"outputs\": {\"gate_result\": \"\$result\"}}" > "\$worker_dir/results/\${epoch}-\${step_id}-result.json"
}
EOF
}

# Stub: run_sub_agent calls agent_run from the mocked agent
run_sub_agent() {
    local agent_type="$1"
    local worker_dir="$2"
    local project_dir="$3"

    local agent_file="$TEST_DIR/fake-home/lib/agents/${agent_type}.sh"
    if [ -f "$agent_file" ]; then
        # shellcheck source=/dev/null
        source "$agent_file"
        agent_run "$worker_dir" "$project_dir"
    else
        echo "mock-agent:$agent_type" >> "$TEST_DIR/agent_invocations.txt"
        # Write a PASS result by default in correct format
        local step_id="${WIGGUM_STEP_ID:-unknown}"
        local epoch
        epoch=$(_mock_epoch)
        mkdir -p "$worker_dir/results"
        echo '{"outputs": {"gate_result": "PASS"}}' > "$worker_dir/results/${epoch}-${step_id}-result.json"
    fi
}

# =============================================================================
# Test: Pipeline runs steps in sequence
# =============================================================================
test_pipeline_runs_steps_in_order() {
    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-order",
        "steps": [
            {"id": "step-1", "agent": "agent-a"},
            {"id": "step-2", "agent": "agent-b"},
            {"id": "step-3", "agent": "agent-c"}
        ]
    }'

    _pipeline_runner_reset

    : > "$TEST_DIR/agent_invocations.txt"

    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" ""

    local invocations
    invocations=$(cat "$TEST_DIR/agent_invocations.txt")
    assert_output_contains "$invocations" "mock-agent:agent-a" "Step 1 agent should run"
    assert_output_contains "$invocations" "mock-agent:agent-b" "Step 2 agent should run"
    assert_output_contains "$invocations" "mock-agent:agent-c" "Step 3 agent should run"

    # Verify order (a before b before c)
    local line_a line_b line_c
    line_a=$(grep -n "agent-a" "$TEST_DIR/agent_invocations.txt" | head -1 | cut -d: -f1)
    line_b=$(grep -n "agent-b" "$TEST_DIR/agent_invocations.txt" | head -1 | cut -d: -f1)
    line_c=$(grep -n "agent-c" "$TEST_DIR/agent_invocations.txt" | head -1 | cut -d: -f1)

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    if [ "$line_a" -lt "$line_b" ] && [ "$line_b" -lt "$line_c" ]; then
        echo -e "  ${GREEN}✓${NC} Steps ran in correct order (a=$line_a, b=$line_b, c=$line_c)"
    else
        echo -e "  ${RED}✗${NC} Steps ran out of order (a=$line_a, b=$line_b, c=$line_c)"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
}

# =============================================================================
# Test: enabled_by skips steps when env var is not 'true'
# =============================================================================
test_pipeline_enabled_by_skips() {
    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-enabled-by",
        "steps": [
            {"id": "always", "agent": "agent-always"},
            {"id": "gated", "agent": "agent-gated", "enabled_by": "ENABLE_GATED_STEP"},
            {"id": "final", "agent": "agent-final"}
        ]
    }'

    _pipeline_runner_reset

    # Don't set ENABLE_GATED_STEP
    unset ENABLE_GATED_STEP 2>/dev/null || true
    : > "$TEST_DIR/agent_invocations.txt"

    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" ""

    local invocations
    invocations=$(cat "$TEST_DIR/agent_invocations.txt")
    assert_output_contains "$invocations" "agent-always" "Always step should run"
    assert_output_not_contains "$invocations" "agent-gated" "Gated step should be skipped"
    assert_output_contains "$invocations" "agent-final" "Final step should run"
}

# =============================================================================
# Test: enabled_by runs steps when env var is 'true'
# =============================================================================
test_pipeline_enabled_by_runs() {
    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-enabled-by-true",
        "steps": [
            {"id": "gated", "agent": "agent-gated", "enabled_by": "ENABLE_GATED_STEP"}
        ]
    }'

    _pipeline_runner_reset

    export ENABLE_GATED_STEP="true"
    : > "$TEST_DIR/agent_invocations.txt"

    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" ""

    local invocations
    invocations=$(cat "$TEST_DIR/agent_invocations.txt")
    assert_output_contains "$invocations" "agent-gated" "Gated step should run when enabled"
    unset ENABLE_GATED_STEP
}

# =============================================================================
# Test: on_result FAIL with jump:abort halts pipeline
# =============================================================================
test_pipeline_on_result_fail_abort() {
    _create_mock_agent "fail-agent" "FAIL"

    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-abort",
        "steps": [
            {"id": "blocker", "agent": "fail-agent", "on_result": {"FAIL": {"jump": "abort"}}},
            {"id": "after", "agent": "agent-after"}
        ]
    }'

    _pipeline_runner_reset

    : > "$TEST_DIR/agent_invocations.txt"
    local exit_code=0
    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" "" 2>/dev/null || exit_code=$?

    assert_equals "1" "$exit_code" "Pipeline should return 1 on FAIL->abort"

    local invocations
    invocations=$(cat "$TEST_DIR/agent_invocations.txt")
    assert_output_not_contains "$invocations" "agent-after" \
        "Steps after abort should not run"
}

# =============================================================================
# Test: No on_result handler for FAIL applies default behavior (abort)
# =============================================================================
test_pipeline_no_handler_continues() {
    _create_mock_agent "soft-fail" "FAIL"

    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-no-handler",
        "steps": [
            {"id": "soft", "agent": "soft-fail"},
            {"id": "continues", "agent": "agent-continues"}
        ]
    }'

    _pipeline_runner_reset

    : > "$TEST_DIR/agent_invocations.txt"
    local exit_code=0
    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" "" 2>/dev/null || exit_code=$?

    assert_equals "1" "$exit_code" "Pipeline should abort on FAIL without explicit handler"

    local invocations
    invocations=$(cat "$TEST_DIR/agent_invocations.txt")
    assert_output_not_contains "$invocations" "agent-continues" \
        "Steps after FAIL should NOT run when no handler present"
}

# =============================================================================
# Test: Jump to named step
# =============================================================================
test_pipeline_jump_to_named_step() {
    _create_mock_agent "fail-jump-agent" "FAIL"

    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-named-jump",
        "steps": [
            {"id": "step-a", "agent": "fail-jump-agent", "on_result": {"FAIL": {"jump": "step-c"}}},
            {"id": "step-b", "agent": "agent-b"},
            {"id": "step-c", "agent": "agent-c"}
        ]
    }'

    _pipeline_runner_reset

    : > "$TEST_DIR/agent_invocations.txt"
    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" ""

    local invocations
    invocations=$(cat "$TEST_DIR/agent_invocations.txt")
    assert_output_not_contains "$invocations" "agent-b" "Step B should be skipped by jump"
    assert_output_contains "$invocations" "agent-c" "Step C should run after jump"
}

# =============================================================================
# Test: Max visits triggers abort (explicit on_max: abort)
# =============================================================================
test_pipeline_max_visits_abort() {
    _create_mock_agent "always-fail" "FAIL"

    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-max-abort",
        "steps": [
            {"id": "looper", "agent": "always-fail", "max": 2, "on_max": "abort", "on_result": {"FAIL": {"jump": "self"}}},
            {"id": "after", "agent": "agent-after"}
        ]
    }'

    _pipeline_runner_reset

    : > "$TEST_DIR/agent_invocations.txt"
    local exit_code=0
    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" "" 2>/dev/null || exit_code=$?

    assert_equals "1" "$exit_code" "Pipeline should abort when max visits exceeded"

    # Should have run the step exactly max times (2)
    local invocation_count
    invocation_count=$(grep -c "always-fail" "$TEST_DIR/agent_invocations.txt")
    assert_equals "2" "$invocation_count" "Step should run exactly max (2) times"
}

# =============================================================================
# Test: Max visits with on_max:"next" continues pipeline
# =============================================================================
test_pipeline_max_visits_next() {
    _create_mock_agent "always-fail" "FAIL"

    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-max-next",
        "steps": [
            {"id": "looper", "agent": "always-fail", "max": 2, "on_max": "next", "on_result": {"FAIL": {"jump": "self"}}},
            {"id": "after", "agent": "agent-after"}
        ]
    }'

    _pipeline_runner_reset

    : > "$TEST_DIR/agent_invocations.txt"
    local exit_code=0
    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" "" || exit_code=$?

    assert_equals "0" "$exit_code" "Pipeline should continue when on_max is next"

    local invocations
    invocations=$(cat "$TEST_DIR/agent_invocations.txt")
    assert_output_contains "$invocations" "agent-after" "After step should run when on_max=next"
}

# =============================================================================
# Test: Inline agent FIX loop - FIX triggers inline, re-runs parent, PASS continues
# =============================================================================
test_pipeline_inline_agent_fix_loop() {
    # Parent returns FIX first, PASS second
    _create_counting_agent "audit-agent" "FIX" "PASS"
    # Inline fix agent always returns PASS
    _create_mock_agent "fix-agent" "PASS"

    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-inline-fix",
        "steps": [
            {
                "id": "audit",
                "agent": "audit-agent",
                "max": 3,
                "on_result": {
                    "FIX": {
                        "id": "audit-fix",
                        "agent": "fix-agent",
                        "max": 2,
                        "commit_after": true
                    }
                }
            },
            {"id": "after", "agent": "agent-after"}
        ]
    }'

    _pipeline_runner_reset

    : > "$TEST_DIR/agent_invocations.txt"
    local exit_code=0
    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" "" || exit_code=$?

    assert_equals "0" "$exit_code" "Pipeline should succeed after fix loop"

    local invocations
    invocations=$(cat "$TEST_DIR/agent_invocations.txt")

    # audit-agent should run twice (FIX then PASS)
    local audit_count
    audit_count=$(grep -c "audit-agent" "$TEST_DIR/agent_invocations.txt")
    assert_equals "2" "$audit_count" "Audit agent should run twice (FIX then PASS)"

    # fix-agent should run once
    local fix_count
    fix_count=$(grep -c "fix-agent" "$TEST_DIR/agent_invocations.txt")
    assert_equals "1" "$fix_count" "Fix agent should run once"

    # after step should run
    assert_output_contains "$invocations" "agent-after" "After step should run after successful fix"
}

# =============================================================================
# Test: Inline handler max exceeded triggers on_max
# =============================================================================
test_pipeline_inline_max_exceeded() {
    # Parent always returns FIX
    _create_mock_agent "always-fix" "FIX"
    # Fix agent always returns PASS (causing parent re-run via default)
    _create_mock_agent "fix-agent" "PASS"

    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-inline-max",
        "steps": [
            {
                "id": "audit",
                "agent": "always-fix",
                "max": 5,
                "on_result": {
                    "FIX": {
                        "id": "audit-fix",
                        "agent": "fix-agent",
                        "max": 2
                    }
                }
            },
            {"id": "after", "agent": "agent-after"}
        ]
    }'

    _pipeline_runner_reset

    : > "$TEST_DIR/agent_invocations.txt"
    local exit_code=0
    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" "" || exit_code=$?

    # inline max=2, on_max defaults to next (continues to after step)
    assert_equals "0" "$exit_code" "Pipeline should continue when inline handler max exceeded (default on_max: next)"

    # Fix agent should have run exactly 2 times
    local fix_count
    fix_count=$(grep -c "fix-agent" "$TEST_DIR/agent_invocations.txt")
    assert_equals "2" "$fix_count" "Fix agent should run exactly max (2) times"
}

# =============================================================================
# Test: jump:prev goes to previous step
# =============================================================================
test_pipeline_jump_prev() {
    # step-b returns FAIL first time, PASS second time
    _create_counting_agent "prev-agent" "FAIL" "PASS"

    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-jump-prev",
        "steps": [
            {"id": "step-a", "agent": "agent-a", "max": 3},
            {"id": "step-b", "agent": "prev-agent", "max": 3, "on_result": {"FAIL": {"jump": "prev"}}}
        ]
    }'

    _pipeline_runner_reset

    : > "$TEST_DIR/agent_invocations.txt"
    local exit_code=0
    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" "" || exit_code=$?

    assert_equals "0" "$exit_code" "Pipeline should succeed after prev jump and retry"

    # step-a should run twice (initial + after prev jump)
    local a_count
    a_count=$(grep -c "agent-a\|mock-agent:agent-a" "$TEST_DIR/agent_invocations.txt")
    assert_equals "2" "$a_count" "Step A should run twice (initial + after prev jump)"

    # step-b should run twice (FAIL then PASS)
    local b_count
    b_count=$(grep -c "prev-agent" "$TEST_DIR/agent_invocations.txt")
    assert_equals "2" "$b_count" "Step B should run twice (FAIL then PASS)"
}

# =============================================================================
# Test: STOP with abort handler halts pipeline
# =============================================================================
test_pipeline_stop_aborts() {
    _create_mock_agent "stop-agent" "STOP"

    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-stop",
        "steps": [
            {"id": "stopper", "agent": "stop-agent", "on_result": {"STOP": {"jump": "abort"}}},
            {"id": "after", "agent": "agent-after"}
        ]
    }'

    _pipeline_runner_reset

    : > "$TEST_DIR/agent_invocations.txt"
    local exit_code=0
    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" "" 2>/dev/null || exit_code=$?

    assert_equals "1" "$exit_code" "Pipeline should abort on STOP with abort handler"

    local invocations
    invocations=$(cat "$TEST_DIR/agent_invocations.txt")
    assert_output_not_contains "$invocations" "agent-after" "After step should not run"
}

# =============================================================================
# Test: on_max loop detection aborts pipeline
# =============================================================================
test_pipeline_on_max_loop_detection() {
    # Two steps that loop back to themselves (triggering max), with on_max jumping to each other
    # step-a always returns FAIL → jump:self, hits max, on_max → step-b
    # step-b always returns FAIL → jump:self, hits max, on_max → step-a
    # step-a already hit on_max in this cascade → loop detected
    _create_mock_agent "loop-agent-a" "FAIL"
    _create_mock_agent "loop-agent-b" "FAIL"

    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-on-max-loop",
        "steps": [
            {"id": "step-a", "agent": "loop-agent-a", "max": 1, "on_max": "step-b", "on_result": {"FAIL": {"jump": "self"}}},
            {"id": "step-b", "agent": "loop-agent-b", "max": 1, "on_max": "step-a", "on_result": {"FAIL": {"jump": "self"}}}
        ]
    }'

    _pipeline_runner_reset

    : > "$TEST_DIR/agent_invocations.txt"
    local exit_code=0
    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" "" 2>/dev/null || exit_code=$?

    # Flow:
    # 1. step-a runs (visit 1), FAIL → jump:self
    # 2. step-a max (1) exceeded → on_max:step-b, cascade[step-a]=1
    # 3. step-b runs (visit 1), FAIL → jump:self
    # 4. step-b max (1) exceeded → on_max:step-a, cascade[step-b]=1
    # 5. step-a max exceeded AND cascade[step-a]=1 → loop detected, abort
    assert_equals "1" "$exit_code" "Pipeline should abort on on_max loop detection"

    # Each agent should run exactly once (max=1)
    local a_count b_count
    a_count=$(grep -c "loop-agent-a" "$TEST_DIR/agent_invocations.txt") || a_count=0
    b_count=$(grep -c "loop-agent-b" "$TEST_DIR/agent_invocations.txt") || b_count=0
    assert_equals "1" "$a_count" "Step A should run exactly once before loop detected"
    assert_equals "1" "$b_count" "Step B should run exactly once before loop detected"
}

# =============================================================================
# Test: start_from_step skips earlier steps
# =============================================================================
test_pipeline_start_from_step() {
    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-start-from",
        "steps": [
            {"id": "step-1", "agent": "agent-1"},
            {"id": "step-2", "agent": "agent-2"},
            {"id": "step-3", "agent": "agent-3"}
        ]
    }'

    _pipeline_runner_reset

    : > "$TEST_DIR/agent_invocations.txt"
    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" "step-2"

    local invocations
    invocations=$(cat "$TEST_DIR/agent_invocations.txt")
    assert_output_not_contains "$invocations" "agent-1" "Step 1 should be skipped"
    assert_output_contains "$invocations" "agent-2" "Step 2 should run"
    assert_output_contains "$invocations" "agent-3" "Step 3 should run"
}

# =============================================================================
# Test: Pipeline config is written to worker dir with all steps
# =============================================================================
test_pipeline_writes_pipeline_config() {
    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-config",
        "steps": [
            {"id": "step-a", "agent": "agent-a", "config": {"max_turns": 10}},
            {"id": "step-b", "agent": "agent-b", "config": {"custom_key": "val"}}
        ]
    }'

    _pipeline_runner_reset

    : > "$TEST_DIR/agent_invocations.txt"
    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" ""

    assert_file_exists "$TEST_DIR/worker/pipeline-config.json" "Pipeline config should be written"

    # Check structure
    local pipeline_name
    pipeline_name=$(jq -r '.pipeline.name' "$TEST_DIR/worker/pipeline-config.json")
    assert_equals "test-config" "$pipeline_name" "Pipeline name should be in config"

    # Check that all steps are present
    local step_count
    step_count=$(jq '.steps | keys | length' "$TEST_DIR/worker/pipeline-config.json")
    assert_equals "2" "$step_count" "Pipeline config should contain 2 steps"

    # Check step config values
    local max_turns
    max_turns=$(jq -r '.steps["step-a"].config.max_turns' "$TEST_DIR/worker/pipeline-config.json")
    assert_equals "10" "$max_turns" "Step A config should contain max_turns=10"

    local custom_key
    custom_key=$(jq -r '.steps["step-b"].config.custom_key' "$TEST_DIR/worker/pipeline-config.json")
    assert_equals "val" "$custom_key" "Step B config should contain custom_key=val"
}

# =============================================================================
# Test: Pipeline config updates current step as pipeline progresses
# =============================================================================
test_pipeline_config_updates_current_step() {
    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-current",
        "steps": [
            {"id": "first", "agent": "agent-first"},
            {"id": "second", "agent": "agent-second"}
        ]
    }'

    _pipeline_runner_reset

    : > "$TEST_DIR/agent_invocations.txt"
    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" ""

    # After pipeline completes, current should point to last step
    local current_step_id current_step_idx
    current_step_id=$(jq -r '.current.step_id' "$TEST_DIR/worker/pipeline-config.json")
    current_step_idx=$(jq -r '.current.step_idx' "$TEST_DIR/worker/pipeline-config.json")

    assert_equals "second" "$current_step_id" "Current step ID should be 'second' after pipeline"
    assert_equals "1" "$current_step_idx" "Current step index should be 1 after pipeline"
}

# =============================================================================
# Test: Pipeline config includes inline handler steps
# =============================================================================
test_pipeline_config_includes_inline_handlers() {
    _create_mock_agent "main-agent" "FIX"
    _create_mock_agent "inline-fix" "PASS"

    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-inline",
        "steps": [
            {
                "id": "main",
                "agent": "main-agent",
                "max": 1,
                "on_max": "next",
                "on_result": {
                    "FIX": {
                        "id": "main-fix",
                        "agent": "inline-fix",
                        "max": 1,
                        "config": {"report_from": "main"}
                    }
                }
            }
        ]
    }'

    _pipeline_runner_reset

    : > "$TEST_DIR/agent_invocations.txt"
    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" ""

    # Check that inline handler is included in steps map
    local inline_agent
    inline_agent=$(jq -r '.steps["main-fix"].agent' "$TEST_DIR/worker/pipeline-config.json")
    assert_equals "inline-fix" "$inline_agent" "Inline handler should be in steps map"

    local inline_config
    inline_config=$(jq -r '.steps["main-fix"].config.report_from' "$TEST_DIR/worker/pipeline-config.json")
    assert_equals "main" "$inline_config" "Inline handler config should be preserved"
}

# =============================================================================
# Test: Missing workspace aborts pipeline
# =============================================================================
test_pipeline_aborts_on_missing_workspace() {
    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-missing-ws",
        "steps": [
            {"id": "step-1", "agent": "agent-1"}
        ]
    }'

    _pipeline_runner_reset

    : > "$TEST_DIR/agent_invocations.txt"
    local exit_code=0
    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/nonexistent-workspace" "" 2>/dev/null || exit_code=$?

    assert_equals "1" "$exit_code" "Should return 1 when workspace doesn't exist"
}

# =============================================================================
# Test: Activity log events are emitted for steps
# =============================================================================
test_pipeline_emits_activity_events() {
    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-activity",
        "steps": [
            {"id": "logged-step", "agent": "agent-logged"}
        ]
    }'

    _pipeline_runner_reset

    : > "$TEST_DIR/agent_invocations.txt"
    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" ""

    local activity_log="$TEST_DIR/project/.ralph/logs/activity.jsonl"
    assert_file_exists "$activity_log" "Activity log should exist"
    assert_file_contains "$activity_log" '"event":"step.started"' "Should log step.started"
    assert_file_contains "$activity_log" '"event":"step.completed"' "Should log step.completed"
    assert_file_contains "$activity_log" 'logged-step' "Should reference step ID"
}

# =============================================================================
# Test: Circuit breaker escalates repeated FIX to FAIL
# =============================================================================
test_pipeline_circuit_breaker_escalates_repeated_fix() {
    # Agent always returns FIX - circuit breaker should trigger after threshold
    _create_mock_agent "always-fix-agent" "FIX"

    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-circuit-breaker",
        "steps": [
            {
                "id": "fixer",
                "agent": "always-fix-agent",
                "max": 10,
                "on_result": {
                    "FIX": {"jump": "self"}
                }
            },
            {"id": "after", "agent": "agent-after"}
        ]
    }'

    _pipeline_runner_reset

    # Set low threshold for testing
    export WIGGUM_CIRCUIT_BREAKER_THRESHOLD=3
    _PIPELINE_CIRCUIT_BREAKER_THRESHOLD=3

    : > "$TEST_DIR/agent_invocations.txt"
    local exit_code=0
    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" "" 2>/dev/null || exit_code=$?

    # Pipeline should abort because circuit breaker escalates FIX to FAIL,
    # and FAIL's default_jump is abort
    assert_equals "1" "$exit_code" "Pipeline should abort after circuit breaker trips"

    # Agent should run exactly 3 times (threshold)
    local invocation_count
    invocation_count=$(grep -c "always-fix-agent" "$TEST_DIR/agent_invocations.txt")
    assert_equals "3" "$invocation_count" "Agent should run exactly threshold (3) times before circuit breaker"

    unset WIGGUM_CIRCUIT_BREAKER_THRESHOLD
}

# =============================================================================
# Test: Circuit breaker resets on different result
# =============================================================================
test_pipeline_circuit_breaker_resets_on_different_result() {
    # Agent returns FIX, FIX, PASS - should NOT trip circuit breaker (threshold=3)
    _create_counting_agent "mixed-agent" "FIX" "FIX" "PASS"

    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-cb-reset",
        "steps": [
            {
                "id": "mixed",
                "agent": "mixed-agent",
                "max": 10,
                "on_result": {
                    "FIX": {"jump": "self"}
                }
            },
            {"id": "after", "agent": "agent-after"}
        ]
    }'

    _pipeline_runner_reset

    export WIGGUM_CIRCUIT_BREAKER_THRESHOLD=3
    _PIPELINE_CIRCUIT_BREAKER_THRESHOLD=3

    : > "$TEST_DIR/agent_invocations.txt"
    local exit_code=0
    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" "" || exit_code=$?

    # Pipeline should succeed (FIX, FIX, PASS - only 2 consecutive FIXes, then PASS resets)
    assert_equals "0" "$exit_code" "Pipeline should succeed when result changes before threshold"

    local invocations
    invocations=$(cat "$TEST_DIR/agent_invocations.txt")
    assert_output_contains "$invocations" "agent-after" "After step should run"

    unset WIGGUM_CIRCUIT_BREAKER_THRESHOLD
}

# =============================================================================
# Test: Workspace disappearing before agent invocation is handled
# =============================================================================
test_pipeline_workspace_disappears_before_agent() {
    _create_pipeline "$TEST_DIR/pipeline.json" '{
        "name": "test-ws-disappear",
        "steps": [
            {"id": "step-1", "agent": "agent-1"}
        ]
    }'

    _pipeline_runner_reset

    # Override run_sub_agent to delete workspace before the mock agent runs
    # This simulates the workspace being deleted mid-pipeline
    run_sub_agent() {
        # Do nothing - the workspace check should catch the missing dir
        :
    }

    # Remove workspace AFTER pipeline_run_all starts but before step execution
    # We do this by removing it and relying on the pre-agent check
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR/worker/workspace"

    : > "$TEST_DIR/agent_invocations.txt"
    local exit_code=0
    pipeline_run_all "$TEST_DIR/worker" "$TEST_DIR/project" "$TEST_DIR/worker/workspace" "" 2>/dev/null || exit_code=$?

    assert_equals "1" "$exit_code" "Pipeline should abort when workspace disappears"
}

# =============================================================================
# Run all tests
# =============================================================================
run_test test_pipeline_runs_steps_in_order
run_test test_pipeline_enabled_by_skips
run_test test_pipeline_enabled_by_runs
run_test test_pipeline_on_result_fail_abort
run_test test_pipeline_no_handler_continues
run_test test_pipeline_jump_to_named_step
run_test test_pipeline_max_visits_abort
run_test test_pipeline_max_visits_next
run_test test_pipeline_inline_agent_fix_loop
run_test test_pipeline_inline_max_exceeded
run_test test_pipeline_jump_prev
run_test test_pipeline_stop_aborts
run_test test_pipeline_on_max_loop_detection
run_test test_pipeline_start_from_step
run_test test_pipeline_writes_pipeline_config
run_test test_pipeline_config_updates_current_step
run_test test_pipeline_config_includes_inline_handlers
run_test test_pipeline_aborts_on_missing_workspace
run_test test_pipeline_emits_activity_events
run_test test_pipeline_circuit_breaker_escalates_repeated_fix
run_test test_pipeline_circuit_breaker_resets_on_different_result
run_test test_pipeline_workspace_disappears_before_agent

print_test_summary
exit_with_test_result
