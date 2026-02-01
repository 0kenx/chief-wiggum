#!/usr/bin/env bash
set -euo pipefail
# Integration tests for four-outcome resume decision routing

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/test-framework.sh"

# Setup WIGGUM_HOME and source modules
WIGGUM_HOME="$(cd "$SCRIPT_DIR/.." && pwd)"
export WIGGUM_HOME
source "$WIGGUM_HOME/lib/core/exit-codes.sh"
source "$WIGGUM_HOME/lib/core/resume-state.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"

setup() {
    TEST_WORKER_DIR=$(mktemp -d)
    mkdir -p "$TEST_WORKER_DIR/workspace"
    mkdir -p "$TEST_WORKER_DIR/results"
    mkdir -p "$TEST_WORKER_DIR/conversations"
    echo "# Task PRD" > "$TEST_WORKER_DIR/prd.md"
    echo '{"pipeline":{"name":"default"},"current":{"step_id":"execution","step_idx":1},"steps":[{"id":"planning"},{"id":"execution"},{"id":"test"},{"id":"validation"}]}' > "$TEST_WORKER_DIR/pipeline-config.json"
}

teardown() {
    rm -rf "$TEST_WORKER_DIR"
}

# ============================================================================
# Exit code tests
# ============================================================================

test_exit_codes_defined() {
    assert_equals "65" "$EXIT_RESUME_ABORT" "EXIT_RESUME_ABORT should be 65"
    assert_equals "66" "$EXIT_RESUME_DEFER" "EXIT_RESUME_DEFER should be 66"
    assert_equals "67" "$EXIT_RESUME_COMPLETE" "EXIT_RESUME_COMPLETE should be 67"
}

# ============================================================================
# Resume-decision.json parsing tests
# ============================================================================

test_decision_json_complete() {
    jq -n '{decision: "COMPLETE", pipeline: null, resume_step: null, reason: "All done"}' \
        > "$TEST_WORKER_DIR/resume-decision.json"

    local decision
    decision=$(jq -r '.decision // "ABORT"' "$TEST_WORKER_DIR/resume-decision.json")
    assert_equals "COMPLETE" "$decision" "Should parse COMPLETE from JSON"
}

test_decision_json_retry() {
    jq -n '{decision: "RETRY", pipeline: "default", resume_step: "test", reason: "Tests failed"}' \
        > "$TEST_WORKER_DIR/resume-decision.json"

    local decision pipeline step
    decision=$(jq -r '.decision // "ABORT"' "$TEST_WORKER_DIR/resume-decision.json")
    pipeline=$(jq -r '.pipeline // ""' "$TEST_WORKER_DIR/resume-decision.json")
    step=$(jq -r '.resume_step // ""' "$TEST_WORKER_DIR/resume-decision.json")

    assert_equals "RETRY" "$decision" "Should parse RETRY from JSON"
    assert_equals "default" "$pipeline" "Should parse pipeline from JSON"
    assert_equals "test" "$step" "Should parse step from JSON"
}

test_decision_json_abort() {
    jq -n '{decision: "ABORT", pipeline: null, resume_step: null, reason: "Impossible task"}' \
        > "$TEST_WORKER_DIR/resume-decision.json"

    local decision
    decision=$(jq -r '.decision // "ABORT"' "$TEST_WORKER_DIR/resume-decision.json")
    assert_equals "ABORT" "$decision" "Should parse ABORT from JSON"
}

test_decision_json_defer() {
    jq -n '{decision: "DEFER", pipeline: null, resume_step: null, reason: "OOM"}' \
        > "$TEST_WORKER_DIR/resume-decision.json"

    local decision
    decision=$(jq -r '.decision // "ABORT"' "$TEST_WORKER_DIR/resume-decision.json")
    assert_equals "DEFER" "$decision" "Should parse DEFER from JSON"
}

# ============================================================================
# Backward compatibility: resume-step.txt parsing
# ============================================================================

test_legacy_bare_step_id() {
    # Old format: just a step ID with no decision prefix
    echo "execution" > "$TEST_WORKER_DIR/resume-step.txt"
    rm -f "$TEST_WORKER_DIR/resume-decision.json"

    # Simulate the parsing logic from wiggum-resume
    local raw decision="" resume_pipeline="" resume_step_id=""
    raw=$(cat "$TEST_WORKER_DIR/resume-step.txt" 2>/dev/null || echo "ABORT")
    raw=$(echo "$raw" | tr -d '[:space:]')

    if [[ "$raw" == RETRY:* ]]; then
        decision="RETRY"
        resume_pipeline=$(echo "$raw" | cut -d: -f2)
        resume_step_id=$(echo "$raw" | cut -d: -f3)
    elif [[ "$raw" == "COMPLETE" || "$raw" == "ABORT" || "$raw" == "DEFER" ]]; then
        decision="$raw"
    else
        # Legacy: bare step_id → treat as RETRY
        decision="RETRY"
        resume_step_id="$raw"
    fi

    assert_equals "RETRY" "$decision" "Bare step_id should be treated as RETRY"
    assert_equals "execution" "$resume_step_id" "Step should be the bare ID"
    assert_equals "" "$resume_pipeline" "Pipeline should be empty for legacy format"
}

test_legacy_abort_text() {
    echo "ABORT" > "$TEST_WORKER_DIR/resume-step.txt"
    rm -f "$TEST_WORKER_DIR/resume-decision.json"

    local raw decision=""
    raw=$(cat "$TEST_WORKER_DIR/resume-step.txt" 2>/dev/null || echo "ABORT")
    raw=$(echo "$raw" | tr -d '[:space:]')

    if [[ "$raw" == "COMPLETE" || "$raw" == "ABORT" || "$raw" == "DEFER" ]]; then
        decision="$raw"
    fi

    assert_equals "ABORT" "$decision" "ABORT text should parse correctly"
}

test_legacy_retry_colon_format() {
    echo "RETRY:default:execution" > "$TEST_WORKER_DIR/resume-step.txt"
    rm -f "$TEST_WORKER_DIR/resume-decision.json"

    local raw decision="" resume_pipeline="" resume_step_id=""
    raw=$(cat "$TEST_WORKER_DIR/resume-step.txt" 2>/dev/null || echo "ABORT")
    raw=$(echo "$raw" | tr -d '[:space:]')

    if [[ "$raw" == RETRY:* ]]; then
        decision="RETRY"
        resume_pipeline=$(echo "$raw" | cut -d: -f2)
        resume_step_id=$(echo "$raw" | cut -d: -f3)
    fi

    assert_equals "RETRY" "$decision" "RETRY:pipeline:step should parse as RETRY"
    assert_equals "default" "$resume_pipeline" "Pipeline should be extracted"
    assert_equals "execution" "$resume_step_id" "Step should be extracted"
}

# ============================================================================
# Resume state integration with scheduler filtering
# ============================================================================

test_terminal_worker_filtered() {
    # Mark as terminal
    resume_state_set_terminal "$TEST_WORKER_DIR" "ABORT: impossible task"

    assert_success "Terminal worker should be detected" \
        resume_state_is_terminal "$TEST_WORKER_DIR"
}

test_cooling_worker_filtered() {
    # Initialize state first
    resume_state_write "$TEST_WORKER_DIR" '{"attempt_count":1,"max_attempts":5,"last_attempt_at":0,"cooldown_until":0,"terminal":false,"terminal_reason":"","history":[]}'

    # Set long cooldown
    resume_state_set_cooldown "$TEST_WORKER_DIR" 99999

    assert_success "Cooling worker should be detected" \
        resume_state_is_cooling "$TEST_WORKER_DIR"
}

test_cooldown_expiry() {
    # Set cooldown in the past (already expired)
    local state='{"attempt_count":1,"max_attempts":5,"last_attempt_at":0,"cooldown_until":1,"terminal":false,"terminal_reason":"","history":[]}'
    resume_state_write "$TEST_WORKER_DIR" "$state"

    assert_failure "Expired cooldown should not show as cooling" \
        resume_state_is_cooling "$TEST_WORKER_DIR"
}

test_max_attempts_filtering() {
    # Set attempts to max
    resume_state_write "$TEST_WORKER_DIR" '{"attempt_count":5,"max_attempts":5,"last_attempt_at":0,"cooldown_until":0,"terminal":false,"terminal_reason":"","history":[]}'

    assert_success "Max attempts reached should be detected" \
        resume_state_max_exceeded "$TEST_WORKER_DIR"
}

test_no_state_file_backward_compat() {
    # Worker with no resume-state.json (old worker)
    rm -f "$TEST_WORKER_DIR/resume-state.json"

    assert_failure "No state file should not be terminal" \
        resume_state_is_terminal "$TEST_WORKER_DIR"
    assert_failure "No state file should not be cooling" \
        resume_state_is_cooling "$TEST_WORKER_DIR"
    assert_failure "No state file should not exceed max" \
        resume_state_max_exceeded "$TEST_WORKER_DIR"

    local count
    count=$(resume_state_attempts "$TEST_WORKER_DIR")
    assert_equals "0" "$count" "No state file should report 0 attempts"
}

test_complete_marks_terminal() {
    # Simulate COMPLETE flow
    resume_state_increment "$TEST_WORKER_DIR" "COMPLETE" "" "" "All done"
    resume_state_set_terminal "$TEST_WORKER_DIR" "Work complete, task marked [P]"

    assert_success "COMPLETE should make worker terminal" \
        resume_state_is_terminal "$TEST_WORKER_DIR"

    local reason
    reason=$(jq -r '.terminal_reason' "$TEST_WORKER_DIR/resume-state.json")
    assert_equals "Work complete, task marked [P]" "$reason" "Terminal reason should match"
}

test_abort_marks_terminal() {
    resume_state_increment "$TEST_WORKER_DIR" "ABORT" "" "" "Bad PRD"
    resume_state_set_terminal "$TEST_WORKER_DIR" "Unrecoverable failure"

    assert_success "ABORT should make worker terminal" \
        resume_state_is_terminal "$TEST_WORKER_DIR"
}

test_defer_does_not_mark_terminal() {
    resume_state_increment "$TEST_WORKER_DIR" "DEFER" "" "" "OOM"
    resume_state_set_cooldown "$TEST_WORKER_DIR" 3600

    assert_failure "DEFER should not make worker terminal" \
        resume_state_is_terminal "$TEST_WORKER_DIR"
    assert_success "DEFER should set cooldown" \
        resume_state_is_cooling "$TEST_WORKER_DIR"
}

test_retry_increments_only() {
    resume_state_increment "$TEST_WORKER_DIR" "RETRY" "default" "execution" "Resume"

    assert_failure "RETRY should not make worker terminal" \
        resume_state_is_terminal "$TEST_WORKER_DIR"
    assert_failure "RETRY should not set cooldown" \
        resume_state_is_cooling "$TEST_WORKER_DIR"

    local count
    count=$(resume_state_attempts "$TEST_WORKER_DIR")
    assert_equals "1" "$count" "RETRY should increment attempts"
}

# ============================================================================
# Run tests
# ============================================================================
run_test test_exit_codes_defined
run_test test_decision_json_complete
run_test test_decision_json_retry
run_test test_decision_json_abort
run_test test_decision_json_defer
run_test test_legacy_bare_step_id
run_test test_legacy_abort_text
run_test test_legacy_retry_colon_format
run_test test_terminal_worker_filtered
run_test test_cooling_worker_filtered
run_test test_cooldown_expiry
run_test test_max_attempts_filtering
run_test test_no_state_file_backward_compat
run_test test_complete_marks_terminal
run_test test_abort_marks_terminal
run_test test_defer_does_not_mark_terminal
run_test test_retry_increments_only

print_test_summary
exit_with_test_result
