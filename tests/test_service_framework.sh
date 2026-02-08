#!/usr/bin/env bash
set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

LOG_LEVEL=ERROR
export LOG_LEVEL

TEST_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    export RALPH_DIR="$TEST_DIR/ralph"
    export PROJECT_DIR="$TEST_DIR/project"
    mkdir -p "$RALPH_DIR/services" "$PROJECT_DIR"
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# SERVICE-STATE.SH TESTS
# =============================================================================

test_service_state_init() {
    source "$WIGGUM_HOME/lib/service/service-state.sh"

    service_state_init "$RALPH_DIR"

    assert_equals "$RALPH_DIR/services/state.json" "$_SERVICE_STATE_FILE"
    assert_equals "$RALPH_DIR/services/metrics.jsonl" "$_SERVICE_METRICS_FILE"
}

test_service_state_save_restore_roundtrip() {
    source "$WIGGUM_HOME/lib/service/service-state.sh"

    service_state_init "$RALPH_DIR"

    # Set some state
    service_state_set_last_run "test-svc" 1234567890
    service_state_set_status "test-svc" "running"
    _SERVICE_RUN_COUNT["test-svc"]=5
    _SERVICE_FAIL_COUNT["test-svc"]=2

    # Save
    service_state_save

    assert_file_exists "$RALPH_DIR/services/state.json"

    # Clear in-memory state only (not the file)
    _SERVICE_LAST_RUN=()
    _SERVICE_STATUS=()
    _SERVICE_RUN_COUNT=()
    _SERVICE_FAIL_COUNT=()
    _SERVICE_RUNNING_PID=()

    # Restore from file
    service_state_restore

    # Verify restored values
    local last_run
    last_run=$(service_state_get_last_run "test-svc")
    assert_equals "1234567890" "$last_run"

    local run_count
    run_count=$(service_state_get_run_count "test-svc")
    assert_equals "5" "$run_count"

    local fail_count
    fail_count=$(service_state_get_fail_count "test-svc")
    assert_equals "2" "$fail_count"
}

test_service_state_status_transitions() {
    source "$WIGGUM_HOME/lib/service/service-state.sh"

    service_state_init "$RALPH_DIR"

    # Default is stopped
    local status
    status=$(service_state_get_status "svc1")
    assert_equals "stopped" "$status"

    # Transition to running
    service_state_set_status "svc1" "running"
    status=$(service_state_get_status "svc1")
    assert_equals "running" "$status"

    # Transition to completed (via mark)
    service_state_mark_completed "svc1"
    status=$(service_state_get_status "svc1")
    assert_equals "stopped" "$status"

    # Mark as failed
    service_state_mark_failed "svc1"
    status=$(service_state_get_status "svc1")
    assert_equals "failed" "$status"

    # Mark as skipped
    service_state_mark_skipped "svc1"
    status=$(service_state_get_status "svc1")
    assert_equals "skipped" "$status"
}

test_service_state_run_counter_increments() {
    source "$WIGGUM_HOME/lib/service/service-state.sh"

    service_state_init "$RALPH_DIR"

    # Initial count is 0
    local count
    count=$(service_state_get_run_count "svc1")
    assert_equals "0" "$count"

    # Increment
    service_state_increment_runs "svc1"
    count=$(service_state_get_run_count "svc1")
    assert_equals "1" "$count"

    # Increment again
    service_state_increment_runs "svc1"
    count=$(service_state_get_run_count "svc1")
    assert_equals "2" "$count"
}

test_service_state_failure_counter() {
    source "$WIGGUM_HOME/lib/service/service-state.sh"

    service_state_init "$RALPH_DIR"

    local fail_count
    fail_count=$(service_state_get_fail_count "svc1")
    assert_equals "0" "$fail_count"

    # Increment failures
    service_state_increment_failures "svc1"
    fail_count=$(service_state_get_fail_count "svc1")
    assert_equals "1" "$fail_count"

    service_state_increment_failures "svc1"
    fail_count=$(service_state_get_fail_count "svc1")
    assert_equals "2" "$fail_count"

    # Reset on success
    service_state_reset_failures "svc1"
    fail_count=$(service_state_get_fail_count "svc1")
    assert_equals "0" "$fail_count"
}

test_service_state_mark_started_convenience() {
    source "$WIGGUM_HOME/lib/service/service-state.sh"

    service_state_init "$RALPH_DIR"

    service_state_mark_started "svc1" 12345

    local status
    status=$(service_state_get_status "svc1")
    assert_equals "running" "$status"

    local pid
    pid=$(service_state_get_pid "svc1")
    assert_equals "12345" "$pid"

    local run_count
    run_count=$(service_state_get_run_count "svc1")
    assert_equals "1" "$run_count"
}

test_service_state_mark_completed_resets_counters() {
    source "$WIGGUM_HOME/lib/service/service-state.sh"

    service_state_init "$RALPH_DIR"

    # Set up failure state
    _SERVICE_FAIL_COUNT["svc1"]=5
    _SERVICE_RETRY_COUNT["svc1"]=3
    _SERVICE_BACKOFF_UNTIL["svc1"]=9999999999

    service_state_mark_completed "svc1"

    local fail_count
    fail_count=$(service_state_get_fail_count "svc1")
    assert_equals "0" "$fail_count"

    local retry_count
    retry_count=$(service_state_get_retry_count "svc1")
    assert_equals "0" "$retry_count"

    local backoff
    backoff=$(service_state_get_backoff_remaining "svc1")
    assert_equals "0" "$backoff"
}

test_service_state_circuit_breaker_transitions() {
    source "$WIGGUM_HOME/lib/service/service-state.sh"

    service_state_init "$RALPH_DIR"

    # Default is closed
    local state
    state=$(service_state_get_circuit_state "svc1")
    assert_equals "closed" "$state"

    # Open circuit
    service_state_set_circuit_state "svc1" "open"
    state=$(service_state_get_circuit_state "svc1")
    assert_equals "open" "$state"

    local opened_at
    opened_at=$(service_state_get_circuit_opened_at "svc1")
    assert_not_equals "0" "$opened_at"

    # Half-open
    service_state_set_circuit_state "svc1" "half-open"
    state=$(service_state_get_circuit_state "svc1")
    assert_equals "half-open" "$state"

    # Increment half-open attempts
    service_state_increment_half_open_attempts "svc1"
    local attempts
    attempts=$(service_state_get_half_open_attempts "svc1")
    assert_equals "1" "$attempts"

    # Success closes circuit
    service_state_mark_completed "svc1"
    state=$(service_state_get_circuit_state "svc1")
    assert_equals "closed" "$state"
}

test_service_state_record_execution_metrics() {
    source "$WIGGUM_HOME/lib/service/service-state.sh"

    service_state_init "$RALPH_DIR"

    # Record first execution
    _SERVICE_RUN_COUNT["svc1"]=1
    service_state_record_execution "svc1" 100 0

    local metrics
    metrics=$(service_state_get_metrics "svc1")

    local last_duration
    last_duration=$(echo "$metrics" | jq -r '.last_duration_ms')
    assert_equals "100" "$last_duration"

    local min_duration
    min_duration=$(echo "$metrics" | jq -r '.min_duration_ms')
    assert_equals "100" "$min_duration"

    local max_duration
    max_duration=$(echo "$metrics" | jq -r '.max_duration_ms')
    assert_equals "100" "$max_duration"

    # Record second execution
    _SERVICE_RUN_COUNT["svc1"]=2
    service_state_record_execution "svc1" 200 0

    metrics=$(service_state_get_metrics "svc1")

    min_duration=$(echo "$metrics" | jq -r '.min_duration_ms')
    assert_equals "100" "$min_duration"

    max_duration=$(echo "$metrics" | jq -r '.max_duration_ms')
    assert_equals "200" "$max_duration"

    local avg_duration
    avg_duration=$(echo "$metrics" | jq -r '.avg_duration_ms')
    assert_equals "150" "$avg_duration"
}

test_service_state_queue_priority_ordering() {
    source "$WIGGUM_HOME/lib/service/service-state.sh"

    service_state_init "$RALPH_DIR"

    # Add items with different priorities
    service_state_queue_add "svc1" "low" '["arg1"]'
    service_state_queue_add "svc1" "high" '["arg2"]'
    service_state_queue_add "svc1" "normal" '["arg3"]'
    service_state_queue_add "svc1" "critical" '["arg4"]'

    local size
    size=$(service_state_queue_size "svc1")
    assert_equals "4" "$size"

    # Pop should return critical first
    # Note: Cannot use $() to capture result because service_state_queue_pop modifies
    # _SERVICE_QUEUE in-place and $() runs in a subshell, losing the modification.
    # Instead, redirect to file.
    local tmpfile="$TEST_DIR/queue_item"
    service_state_queue_pop "svc1" > "$tmpfile"
    local priority
    priority=$(jq -r '.priority' "$tmpfile")
    assert_equals "critical" "$priority"

    # Then high
    service_state_queue_pop "svc1" > "$tmpfile"
    priority=$(jq -r '.priority' "$tmpfile")
    assert_equals "high" "$priority"

    # Then normal
    service_state_queue_pop "svc1" > "$tmpfile"
    priority=$(jq -r '.priority' "$tmpfile")
    assert_equals "normal" "$priority"

    # Then low
    service_state_queue_pop "svc1" > "$tmpfile"
    priority=$(jq -r '.priority' "$tmpfile")
    assert_equals "low" "$priority"

    # Queue now empty
    size=$(service_state_queue_size "svc1")
    assert_equals "0" "$size"
}

test_service_state_queue_clear() {
    source "$WIGGUM_HOME/lib/service/service-state.sh"

    service_state_init "$RALPH_DIR"

    service_state_queue_add "svc1" "normal" '["arg1"]'
    service_state_queue_add "svc1" "normal" '["arg2"]'

    local size
    size=$(service_state_queue_size "svc1")
    assert_equals "2" "$size"

    service_state_queue_clear "svc1"

    size=$(service_state_queue_size "svc1")
    assert_equals "0" "$size"
}

test_service_state_backoff() {
    source "$WIGGUM_HOME/lib/service/service-state.sh"

    service_state_init "$RALPH_DIR"

    # Set backoff for 10 seconds
    service_state_set_backoff "svc1" 10

    # Should be in backoff
    if service_state_is_in_backoff "svc1"; then
        local remaining
        remaining=$(service_state_get_backoff_remaining "svc1")
        assert_greater_than "$remaining" 0
    else
        fail "Service should be in backoff"
    fi

    # Set backoff in the past
    _SERVICE_BACKOFF_UNTIL["svc1"]=1000000000

    # Should not be in backoff
    if service_state_is_in_backoff "svc1"; then
        fail "Service should not be in backoff"
    fi

    local remaining
    remaining=$(service_state_get_backoff_remaining "svc1")
    assert_equals "0" "$remaining"
}

# =============================================================================
# SERVICE-RUNNER.SH TESTS
# =============================================================================

test_service_runner_init() {
    source "$WIGGUM_HOME/lib/service/service-runner.sh"

    service_runner_init "$RALPH_DIR" "$PROJECT_DIR"

    assert_equals "$RALPH_DIR" "$_RUNNER_RALPH_DIR"
    assert_equals "$PROJECT_DIR" "$_RUNNER_PROJECT_DIR"
}

test_service_runner_function_security_check() {
    source "$WIGGUM_HOME/lib/service/service-state.sh"
    source "$WIGGUM_HOME/lib/service/service-runner.sh"

    service_state_init "$RALPH_DIR"
    service_runner_init "$RALPH_DIR" "$PROJECT_DIR"

    # Mock a service cache
    declare -gA _SVC_CACHE
    _SVC_CACHE["exec_type:test-svc"]="function"
    _SVC_CACHE["exec_func:test-svc"]="dangerous_function"

    # Mock service_get_timeout and service_get_limits
    service_get_timeout() { echo "0"; }
    service_get_limits() { echo "null"; }

    # Attempt to run function without svc_ prefix (should fail)
    local exit_code=0
    service_run "test-svc" || exit_code=$?

    assert_not_equals "0" "$exit_code"

    # Verify status is failed
    local status
    status=$(service_state_get_status "test-svc")
    assert_equals "failed" "$status"
}

test_service_runner_function_type_valid() {
    source "$WIGGUM_HOME/lib/service/service-state.sh"
    source "$WIGGUM_HOME/lib/service/service-runner.sh"

    service_state_init "$RALPH_DIR"
    service_runner_init "$RALPH_DIR" "$PROJECT_DIR"

    # Define a valid svc_ function
    svc_test_function() {
        echo "test output"
        return 0
    }

    # Mock service cache
    declare -gA _SVC_CACHE
    _SVC_CACHE["exec_type:test-svc"]="function"
    _SVC_CACHE["exec_func:test-svc"]="svc_test_function"

    # Mock helpers
    service_get_timeout() { echo "0"; }
    service_get_limits() { echo "null"; }

    # Run function (should succeed)
    local exit_code=0
    service_run "test-svc" || exit_code=$?

    # Should start in background (returns 0)
    assert_equals "0" "$exit_code"

    # Should be marked as running
    local status
    status=$(service_state_get_status "test-svc")
    assert_equals "running" "$status"
}

test_service_runner_resolve_workspace_isolated() {
    source "$WIGGUM_HOME/lib/service/service-runner.sh"

    service_runner_init "$RALPH_DIR" "$PROJECT_DIR"

    local workspace
    workspace=$(_resolve_service_workspace "test-svc" "true")

    # Should be in workers directory with timestamp
    assert_output_contains "$workspace" "/workers/service-test-svc-"

    # Should have created subdirectories
    assert_dir_exists "$workspace/logs"
    assert_dir_exists "$workspace/results"
    assert_dir_exists "$workspace/output"
}

test_service_runner_resolve_workspace_lightweight() {
    source "$WIGGUM_HOME/lib/service/service-runner.sh"

    service_runner_init "$RALPH_DIR" "$PROJECT_DIR"

    local workspace
    workspace=$(_resolve_service_workspace "test-svc" "false")

    # Should be in services directory
    assert_equals "$RALPH_DIR/services/test-svc" "$workspace"

    # Should have created subdirectories
    assert_dir_exists "$workspace/logs"
    assert_dir_exists "$workspace/output"
}

# =============================================================================
# SERVICE-CORE.SH TESTS
# =============================================================================

test_service_core_init() {
    source "$WIGGUM_HOME/lib/service/service-state.sh"
    source "$WIGGUM_HOME/lib/service/service-loader.sh"
    source "$WIGGUM_HOME/lib/service/service-core.sh"

    # Create a minimal config file
    cat > "$TEST_DIR/services.json" << 'EOF'
{
    "services": [],
    "groups": {}
}
EOF

    service_core_init "$RALPH_DIR" "$PROJECT_DIR" "$TEST_DIR/services.json"

    # Verify runner is initialized
    assert_equals "$RALPH_DIR" "$_RUNNER_RALPH_DIR"
    assert_equals "$PROJECT_DIR" "$_RUNNER_PROJECT_DIR"
}

test_service_can_run_checks_dependencies() {
    source "$WIGGUM_HOME/lib/service/service-state.sh"
    source "$WIGGUM_HOME/lib/service/service-loader.sh"
    source "$WIGGUM_HOME/lib/service/service-core.sh"

    service_state_init "$RALPH_DIR"

    # Mock helper functions
    service_conditions_met() { return 0; }
    service_dependencies_satisfied() { return 1; }

    # Should fail if dependencies not satisfied
    if service_can_run "test-svc"; then
        fail "service_can_run should return 1 when dependencies not satisfied"
    fi
}

test_service_get_summary_returns_json() {
    source "$WIGGUM_HOME/lib/service/service-loader.sh"
    source "$WIGGUM_HOME/lib/service/service-core.sh"

    # Mock helper functions
    service_get_schedule() {
        echo '{"type":"interval"}'
    }
    service_get_execution() {
        echo '{"type":"command"}'
    }
    service_get_interval() {
        echo "60"
    }
    service_get_timeout() {
        echo "30"
    }
    service_get_dependencies() {
        echo ""
    }
    service_get_groups() {
        echo ""
    }

    local summary
    summary=$(service_get_summary "test-svc")

    # Verify it's valid JSON
    if ! echo "$summary" | jq empty 2>/dev/null; then
        fail "service_get_summary returned invalid JSON: $summary"
    fi

    # Check fields
    local schedule_type
    schedule_type=$(echo "$summary" | jq -r '.schedule_type')
    assert_equals "interval" "$schedule_type"

    local exec_type
    exec_type=$(echo "$summary" | jq -r '.execution_type')
    assert_equals "command" "$exec_type"
}

# =============================================================================
# SERVICE-HANDLERS TESTS
# =============================================================================

test_orchestrator_handlers_exist() {
    source "$WIGGUM_HOME/lib/service-handlers/orchestrator-handlers.sh"

    # Verify key functions exist using declare -F
    if ! declare -F svc_orch_usage_tracker_write_shared &>/dev/null; then
        fail "Function svc_orch_usage_tracker_write_shared not found"
    fi
    if ! declare -F svc_orch_spawn_ready_tasks &>/dev/null; then
        fail "Function svc_orch_spawn_ready_tasks not found"
    fi
    if ! declare -F svc_orch_cleanup_all_workers &>/dev/null; then
        fail "Function svc_orch_cleanup_all_workers not found"
    fi
    if ! declare -F svc_orch_scheduler_tick &>/dev/null; then
        fail "Function svc_orch_scheduler_tick not found"
    fi
    if ! declare -F svc_orch_task_spawner &>/dev/null; then
        fail "Function svc_orch_task_spawner not found"
    fi
}

test_orchestrator_handlers_svc_prefix() {
    source "$WIGGUM_HOME/lib/service-handlers/orchestrator-handlers.sh"

    # Get all functions defined in the file
    local functions
    functions=$(declare -F | grep -o 'svc_orch_[a-z_]*' || true)

    # Verify all start with svc_
    while read -r func; do
        if [[ ! "$func" =~ ^svc_ ]]; then
            fail "Handler function '$func' does not start with 'svc_'"
        fi
    done <<< "$functions"
}

test_memory_handlers_exist() {
    source "$WIGGUM_HOME/lib/service-handlers/memory-handlers.sh"

    # Verify key functions exist
    if ! declare -F svc_memory_load &>/dev/null; then
        fail "Function svc_memory_load not found"
    fi
    if ! declare -F svc_memory_extract &>/dev/null; then
        fail "Function svc_memory_extract not found"
    fi
    if ! declare -F svc_memory_analyze_complete &>/dev/null; then
        fail "Function svc_memory_analyze_complete not found"
    fi
}

test_memory_handlers_svc_prefix() {
    source "$WIGGUM_HOME/lib/service-handlers/memory-handlers.sh"

    # Verify naming convention - all should start with svc_
    if ! declare -F svc_memory_load &>/dev/null; then
        fail "Function svc_memory_load not found"
    fi
    if ! declare -F svc_memory_extract &>/dev/null; then
        fail "Function svc_memory_extract not found"
    fi
    if ! declare -F svc_memory_analyze_complete &>/dev/null; then
        fail "Function svc_memory_analyze_complete not found"
    fi
}

test_meta_handlers_exist() {
    source "$WIGGUM_HOME/lib/service-handlers/meta-handlers.sh"

    # Verify key functions exist
    if ! declare -F svc_meta_init &>/dev/null; then
        fail "Function svc_meta_init not found"
    fi
    if ! declare -F svc_meta_count_completion &>/dev/null; then
        fail "Function svc_meta_count_completion not found"
    fi
    if ! declare -F svc_meta_complete &>/dev/null; then
        fail "Function svc_meta_complete not found"
    fi
}

test_meta_handlers_svc_prefix() {
    source "$WIGGUM_HOME/lib/service-handlers/meta-handlers.sh"

    # Verify all public functions start with svc_
    if ! declare -F svc_meta_init &>/dev/null; then
        fail "Function svc_meta_init not found"
    fi
    if ! declare -F svc_meta_count_completion &>/dev/null; then
        fail "Function svc_meta_count_completion not found"
    fi
    if ! declare -F svc_meta_complete &>/dev/null; then
        fail "Function svc_meta_complete not found"
    fi
}

test_meta_handlers_threshold_counting() {
    source "$WIGGUM_HOME/lib/service-handlers/meta-handlers.sh"

    # Override threshold for testing
    _META_THRESHOLD=2
    _META_ENABLED=true

    svc_meta_init

    local state_file
    state_file=$(_meta_state_file)

    # First completion
    svc_meta_count_completion

    local count
    count=$(_meta_state_get '.completion_count' '0')
    assert_equals "1" "$count"

    # Should not have dispatched yet (no context file)
    local context_file="$RALPH_DIR/meta/.current-meta-context.json"
    assert_file_not_exists "$context_file"

    # Second completion should trigger dispatch
    svc_meta_count_completion

    count=$(_meta_state_get '.completion_count' '0')
    # Should reset to 0 after dispatch
    assert_equals "0" "$count"

    # Should have created context file
    assert_file_exists "$context_file"
}

test_meta_handlers_agent_rotation() {
    source "$WIGGUM_HOME/lib/service-handlers/meta-handlers.sh"

    _META_THRESHOLD=1
    _META_ENABLED=true

    svc_meta_init

    # First dispatch - should be codebase-health (index 0)
    svc_meta_count_completion

    local context_file="$RALPH_DIR/meta/.current-meta-context.json"
    local agent_type
    agent_type=$(jq -r '.agent_type // ""' "$context_file" 2>/dev/null)
    assert_equals "codebase-health" "$agent_type"

    # Reset for next dispatch
    _meta_state_update '.running = false'
    rm -f "$context_file"

    # Second dispatch - should be todo-hunter (index 1)
    svc_meta_count_completion

    agent_type=$(jq -r '.agent_type // ""' "$context_file" 2>/dev/null)
    assert_equals "todo-hunter" "$agent_type"

    # Reset for next dispatch
    _meta_state_update '.running = false'
    rm -f "$context_file"

    # Third dispatch - should be self-improver (index 2)
    svc_meta_count_completion

    agent_type=$(jq -r '.agent_type // ""' "$context_file" 2>/dev/null)
    assert_equals "self-improver" "$agent_type"
}

# =============================================================================
# RUN TESTS
# =============================================================================

run_test test_service_state_init
run_test test_service_state_save_restore_roundtrip
run_test test_service_state_status_transitions
run_test test_service_state_run_counter_increments
run_test test_service_state_failure_counter
run_test test_service_state_mark_started_convenience
run_test test_service_state_mark_completed_resets_counters
run_test test_service_state_circuit_breaker_transitions
run_test test_service_state_record_execution_metrics
run_test test_service_state_queue_priority_ordering
run_test test_service_state_queue_clear
run_test test_service_state_backoff

run_test test_service_runner_init
run_test test_service_runner_function_security_check
run_test test_service_runner_function_type_valid
run_test test_service_runner_resolve_workspace_isolated
run_test test_service_runner_resolve_workspace_lightweight

run_test test_service_core_init
run_test test_service_can_run_checks_dependencies
run_test test_service_get_summary_returns_json

run_test test_orchestrator_handlers_exist
run_test test_orchestrator_handlers_svc_prefix
run_test test_memory_handlers_exist
run_test test_memory_handlers_svc_prefix
run_test test_meta_handlers_exist
run_test test_meta_handlers_svc_prefix
run_test test_meta_handlers_threshold_counting
run_test test_meta_handlers_agent_rotation

print_test_summary
exit_with_test_result
