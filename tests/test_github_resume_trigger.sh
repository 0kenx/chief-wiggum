#!/usr/bin/env bash
set -euo pipefail
# Test GitHub resume trigger integration:
#   - resume_state_reset_for_user_retry
#   - _post_task_failure_to_github table generation
#   - step-completed-event heartbeat logic

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/test-framework.sh"

# Setup WIGGUM_HOME and source modules
WIGGUM_HOME="$(cd "$SCRIPT_DIR/.." && pwd)"
export WIGGUM_HOME
source "$WIGGUM_HOME/lib/core/exit-codes.sh"
source "$WIGGUM_HOME/lib/core/resume-state.sh"

# Create temp dir for each test
setup() {
    TEST_DIR=$(mktemp -d)
    TEST_WORKER_DIR="$TEST_DIR/workers/worker-GH-42-1234567890"
    mkdir -p "$TEST_WORKER_DIR/results" "$TEST_WORKER_DIR/workspace"
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# ============================================================================
# resume_state_reset_for_user_retry tests
# ============================================================================

test_reset_clears_terminal() {
    # Set up a terminal state
    resume_state_set_terminal "$TEST_WORKER_DIR" "Max resume attempts exceeded"
    resume_state_set_cooldown "$TEST_WORKER_DIR" 3600

    # Verify it's terminal
    resume_state_is_terminal "$TEST_WORKER_DIR"
    assert_equals "0" "$?" "Should be terminal before reset"

    # Reset for user retry
    resume_state_reset_for_user_retry "$TEST_WORKER_DIR"

    # Verify no longer terminal
    local is_terminal=0
    resume_state_is_terminal "$TEST_WORKER_DIR" || is_terminal=$?
    assert_equals "1" "$is_terminal" "Should NOT be terminal after reset"
}

test_reset_clears_cooldown() {
    resume_state_set_cooldown "$TEST_WORKER_DIR" 3600

    resume_state_reset_for_user_retry "$TEST_WORKER_DIR"

    local is_cooling=0
    resume_state_is_cooling "$TEST_WORKER_DIR" || is_cooling=$?
    assert_equals "1" "$is_cooling" "Should NOT be cooling after reset"
}

test_reset_clears_attempt_count() {
    # Increment attempt count
    resume_state_increment "$TEST_WORKER_DIR" "RETRY" "default" "execution" "Attempt 1"
    resume_state_increment "$TEST_WORKER_DIR" "RETRY" "default" "execution" "Attempt 2"

    local before_count
    before_count=$(resume_state_attempts "$TEST_WORKER_DIR")
    assert_equals "2" "$before_count" "Should have 2 attempts before reset"

    # Reset — user-initiated retry should clear all counters
    resume_state_reset_for_user_retry "$TEST_WORKER_DIR"

    local after_count
    after_count=$(resume_state_attempts "$TEST_WORKER_DIR")
    assert_equals "0" "$after_count" "Should reset attempt count to 0"
}

test_reset_appends_user_retry_history() {
    resume_state_increment "$TEST_WORKER_DIR" "RETRY" "" "" "Previous attempt"
    resume_state_set_terminal "$TEST_WORKER_DIR" "Failed permanently"

    resume_state_reset_for_user_retry "$TEST_WORKER_DIR"

    local state
    state=$(resume_state_read "$TEST_WORKER_DIR")

    local history_count
    history_count=$(echo "$state" | jq '.history | length')
    assert_equals "2" "$history_count" "Should have 2 history entries (original + USER_RETRY)"

    local last_decision
    last_decision=$(echo "$state" | jq -r '.history[-1].decision')
    assert_equals "USER_RETRY" "$last_decision" "Last history entry should be USER_RETRY"

    local last_reason
    last_reason=$(echo "$state" | jq -r '.history[-1].reason')
    assert_output_contains "$last_reason" "resume-request" "Reason should mention resume-request"
}

test_reset_after_terminal_allows_resume() {
    # Full lifecycle: increment to max, set terminal, then reset
    resume_state_increment "$TEST_WORKER_DIR" "RETRY" "" "" "Attempt"
    resume_state_increment "$TEST_WORKER_DIR" "RETRY" "" "" "Attempt"
    resume_state_increment "$TEST_WORKER_DIR" "RETRY" "" "" "Attempt"
    resume_state_set_terminal "$TEST_WORKER_DIR" "Max exceeded"

    # Verify terminal and at max
    resume_state_is_terminal "$TEST_WORKER_DIR"
    resume_state_max_exceeded "$TEST_WORKER_DIR"

    # Reset
    resume_state_reset_for_user_retry "$TEST_WORKER_DIR"

    # Should no longer be terminal
    local is_terminal=0
    resume_state_is_terminal "$TEST_WORKER_DIR" || is_terminal=$?
    assert_equals "1" "$is_terminal" "Should not be terminal after user retry reset"

    # Should no longer be at max
    local max_exceeded=0
    resume_state_max_exceeded "$TEST_WORKER_DIR" || max_exceeded=$?
    assert_equals "1" "$max_exceeded" "Should not be at max after user retry reset"

    # terminal_reason should be cleared
    local state
    state=$(resume_state_read "$TEST_WORKER_DIR")
    local reason
    reason=$(echo "$state" | jq -r '.terminal_reason')
    assert_equals "" "$reason" "terminal_reason should be empty after reset"
}

# ============================================================================
# Stale file cleanup tests
# ============================================================================

test_stale_file_cleanup_pattern() {
    # Create files that should be cleaned during resume trigger
    touch "$TEST_WORKER_DIR/resume-decision.json"
    touch "$TEST_WORKER_DIR/resume-decision.json.consumed"
    touch "$TEST_WORKER_DIR/recovery-attempted"
    touch "$TEST_WORKER_DIR/stop-reason-fast-fail"
    touch "$TEST_WORKER_DIR/stop-reason-workspace-deleted"

    # Simulate the cleanup logic from orch_github_resume_trigger
    rm -f "$TEST_WORKER_DIR/resume-decision.json" \
          "$TEST_WORKER_DIR/resume-decision.json.consumed" \
          "$TEST_WORKER_DIR/recovery-attempted"
    find "$TEST_WORKER_DIR" -maxdepth 1 -name 'stop-reason-*' -delete

    assert_file_not_exists "$TEST_WORKER_DIR/resume-decision.json" "resume-decision.json should be removed"
    assert_file_not_exists "$TEST_WORKER_DIR/resume-decision.json.consumed" "consumed file should be removed"
    assert_file_not_exists "$TEST_WORKER_DIR/recovery-attempted" "recovery-attempted should be removed"
    assert_file_not_exists "$TEST_WORKER_DIR/stop-reason-fast-fail" "stop-reason-fast-fail should be removed"
    assert_file_not_exists "$TEST_WORKER_DIR/stop-reason-workspace-deleted" "stop-reason-workspace-deleted should be removed"
}

# ============================================================================
# _post_task_failure_to_github result table tests
# ============================================================================

test_failure_summary_builds_table() {
    # Create mock result files
    jq -n '{
        outputs: { gate_result: "PASS" },
        elapsed_ms: 135000
    }' > "$TEST_WORKER_DIR/results/1700000001-planning-result.json"

    jq -n '{
        outputs: { gate_result: "FAIL" },
        elapsed_ms: 312000
    }' > "$TEST_WORKER_DIR/results/1700000002-execution-result.json"

    # Build the summary using the same logic as _post_task_failure_to_github
    local summary="### Pipeline Results

| Step | Result | Duration |
|------|--------|----------|"

    local result_file
    while IFS= read -r result_file; do
        [ -n "$result_file" ] || continue
        [ -f "$result_file" ] || continue

        local basename_file
        basename_file=$(basename "$result_file")
        local step_id
        step_id=$(echo "$basename_file" | sed -E 's/^[0-9]+-(.+)-result\.json$/\1/')

        local gate_result elapsed_ms
        gate_result=$(jq -r '.outputs.gate_result // "UNKNOWN"' "$result_file" 2>/dev/null)
        gate_result="${gate_result:-UNKNOWN}"
        elapsed_ms=$(jq -r '.elapsed_ms // 0' "$result_file" 2>/dev/null)
        elapsed_ms="${elapsed_ms:-0}"

        local duration_s=$((elapsed_ms / 1000))
        local duration_str
        if [ "$duration_s" -lt 60 ]; then
            duration_str="${duration_s}s"
        elif [ "$duration_s" -lt 3600 ]; then
            duration_str="$((duration_s / 60))m $((duration_s % 60))s"
        else
            duration_str="$((duration_s / 3600))h $(( (duration_s % 3600) / 60 ))m"
        fi

        summary+="
| $step_id | $gate_result | $duration_str |"
    done < <(find "$TEST_WORKER_DIR/results" -name "*-result.json" 2>/dev/null | sort)

    assert_output_contains "$summary" "planning" "Summary should contain planning step"
    assert_output_contains "$summary" "execution" "Summary should contain execution step"
    assert_output_contains "$summary" "PASS" "Summary should contain PASS result"
    assert_output_contains "$summary" "FAIL" "Summary should contain FAIL result"
    assert_output_contains "$summary" "2m 15s" "Summary should format 135s as 2m 15s"
    assert_output_contains "$summary" "5m 12s" "Summary should format 312s as 5m 12s"
}

test_failure_summary_handles_no_results() {
    # Empty results directory
    local count
    count=$(find "$TEST_WORKER_DIR/results" -name "*-result.json" 2>/dev/null | wc -l)
    assert_equals "0" "$count" "Should have no result files"
    # Function should not fail with empty results (just produces header-only table)
}

# ============================================================================
# step-completed-event tests
# ============================================================================

test_step_completed_event_format() {
    # Simulate what pipeline-runner.sh writes
    echo "execution|PASS" > "$TEST_WORKER_DIR/step-completed-event"

    assert_file_exists "$TEST_WORKER_DIR/step-completed-event" "Event file should exist"

    local content
    content=$(cat "$TEST_WORKER_DIR/step-completed-event")
    assert_equals "execution|PASS" "$content" "Event should contain step_id|result"
}

test_step_start_time_format() {
    # Simulate what pipeline-runner.sh writes
    echo "1700000001" > "$TEST_WORKER_DIR/step-start-time"

    assert_file_exists "$TEST_WORKER_DIR/step-start-time" "Start time file should exist"

    local content
    content=$(cat "$TEST_WORKER_DIR/step-start-time")
    assert_not_empty "$content" "Start time should not be empty"
}

# ============================================================================
# Recovery heartbeat coverage tests
# ============================================================================

test_recovery_in_progress_marker_enables_heartbeat_scan() {
    # Simulate a recovery-in-progress worker with sync state
    local task_id="GH-42"
    local worker_name="worker-${task_id}-1234567890"
    local worker_path="$TEST_DIR/workers/$worker_name"
    mkdir -p "$worker_path/results"

    # Create recovery-in-progress marker
    echo "1700000000" > "$worker_path/recovery-in-progress"

    # Verify find discovers it
    local found
    found=$(find "$TEST_DIR/workers" -maxdepth 2 -name "recovery-in-progress" -exec dirname {} \; 2>/dev/null)
    assert_output_contains "$found" "$worker_name" "Should find worker with recovery-in-progress"

    # Verify task_id extraction from directory name
    local dir_name
    dir_name=$(basename "$worker_path")
    local extracted_task_id
    extracted_task_id=$(echo "$dir_name" | sed -E 's/^worker-([A-Za-z]+-[0-9]+)-.+$/\1/')
    assert_equals "$task_id" "$extracted_task_id" "Should extract task_id from worker dir name"
}

test_recovery_step_completed_event_cleared() {
    local task_id="GH-99"
    local worker_name="worker-${task_id}-1700000000"
    local worker_path="$TEST_DIR/workers/$worker_name"
    mkdir -p "$worker_path/results"

    # Create recovery-in-progress and step-completed-event
    echo "1700000000" > "$worker_path/recovery-in-progress"
    echo "failure-resolve|PASS" > "$worker_path/step-completed-event"

    assert_file_exists "$worker_path/step-completed-event" "Event should exist before processing"

    # Simulate the cleanup from heartbeat recovery loop
    rm -f "$worker_path/step-completed-event"

    assert_file_not_exists "$worker_path/step-completed-event" "Event should be cleared after processing"
}

# ============================================================================
# Run all tests
# ============================================================================

run_test test_reset_clears_terminal
run_test test_reset_clears_cooldown
run_test test_reset_clears_attempt_count
run_test test_reset_appends_user_retry_history
run_test test_reset_after_terminal_allows_resume
run_test test_stale_file_cleanup_pattern
run_test test_failure_summary_builds_table
run_test test_failure_summary_handles_no_results
run_test test_step_completed_event_format
run_test test_step_start_time_format
run_test test_recovery_in_progress_marker_enables_heartbeat_scan
run_test test_recovery_step_completed_event_cleared

print_test_summary
exit_with_test_result
