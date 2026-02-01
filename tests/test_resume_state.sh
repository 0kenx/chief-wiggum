#!/usr/bin/env bash
set -euo pipefail
# Test resume-state module

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/test-framework.sh"

# Setup WIGGUM_HOME and source the module
WIGGUM_HOME="$(cd "$SCRIPT_DIR/.." && pwd)"
export WIGGUM_HOME
source "$WIGGUM_HOME/lib/core/exit-codes.sh"
source "$WIGGUM_HOME/lib/core/resume-state.sh"

# Create temp dir for each test
setup() {
    TEST_WORKER_DIR=$(mktemp -d)
}

teardown() {
    rm -rf "$TEST_WORKER_DIR"
}

# ============================================================================
# Tests
# ============================================================================

test_read_default_state() {
    # Reading from non-existent file should return defaults
    local state
    state=$(resume_state_read "$TEST_WORKER_DIR")

    local attempt_count terminal cooldown_until
    attempt_count=$(echo "$state" | jq -r '.attempt_count')
    terminal=$(echo "$state" | jq -r '.terminal')
    cooldown_until=$(echo "$state" | jq -r '.cooldown_until')

    assert_equals "0" "$attempt_count" "Default attempt_count should be 0"
    assert_equals "false" "$terminal" "Default terminal should be false"
    assert_equals "0" "$cooldown_until" "Default cooldown_until should be 0"
}

test_write_and_read() {
    local json='{"attempt_count":3,"max_attempts":5,"last_attempt_at":1000,"cooldown_until":0,"terminal":false,"terminal_reason":"","history":[]}'
    resume_state_write "$TEST_WORKER_DIR" "$json"

    assert_file_exists "$TEST_WORKER_DIR/resume-state.json" "State file should exist after write"

    local state
    state=$(resume_state_read "$TEST_WORKER_DIR")
    local count
    count=$(echo "$state" | jq -r '.attempt_count')
    assert_equals "3" "$count" "Read should return written attempt_count"
}

test_increment() {
    # Increment from scratch (no existing file)
    resume_state_increment "$TEST_WORKER_DIR" "RETRY" "default" "execution" "First attempt"

    local state
    state=$(resume_state_read "$TEST_WORKER_DIR")
    local count decision
    count=$(echo "$state" | jq -r '.attempt_count')
    decision=$(echo "$state" | jq -r '.history[0].decision')

    assert_equals "1" "$count" "Count should be 1 after first increment"
    assert_equals "RETRY" "$decision" "History should record RETRY decision"

    # Increment again
    resume_state_increment "$TEST_WORKER_DIR" "DEFER" "" "" "OOM error"

    state=$(resume_state_read "$TEST_WORKER_DIR")
    count=$(echo "$state" | jq -r '.attempt_count')
    local second_decision
    second_decision=$(echo "$state" | jq -r '.history[1].decision')

    assert_equals "2" "$count" "Count should be 2 after second increment"
    assert_equals "DEFER" "$second_decision" "Second history entry should be DEFER"
}

test_terminal_detection() {
    # No file → not terminal
    assert_failure "No state file should not be terminal" \
        resume_state_is_terminal "$TEST_WORKER_DIR"

    # Non-terminal state
    resume_state_write "$TEST_WORKER_DIR" '{"attempt_count":1,"max_attempts":5,"last_attempt_at":0,"cooldown_until":0,"terminal":false,"terminal_reason":"","history":[]}'
    assert_failure "Non-terminal state should return 1" \
        resume_state_is_terminal "$TEST_WORKER_DIR"

    # Terminal state
    resume_state_set_terminal "$TEST_WORKER_DIR" "Work complete"
    assert_success "Terminal state should return 0" \
        resume_state_is_terminal "$TEST_WORKER_DIR"

    # Verify reason
    local reason
    reason=$(jq -r '.terminal_reason' "$TEST_WORKER_DIR/resume-state.json")
    assert_equals "Work complete" "$reason" "Terminal reason should be preserved"
}

test_cooldown_logic() {
    # No file → not cooling
    assert_failure "No state file should not be cooling" \
        resume_state_is_cooling "$TEST_WORKER_DIR"

    # Set a long cooldown (far in the future)
    resume_state_write "$TEST_WORKER_DIR" '{"attempt_count":0,"max_attempts":5,"last_attempt_at":0,"cooldown_until":0,"terminal":false,"terminal_reason":"","history":[]}'
    resume_state_set_cooldown "$TEST_WORKER_DIR" 99999

    assert_success "Should be cooling after set_cooldown" \
        resume_state_is_cooling "$TEST_WORKER_DIR"

    # Set cooldown to 0 (expired)
    local state
    state=$(resume_state_read "$TEST_WORKER_DIR")
    state=$(echo "$state" | jq '.cooldown_until = 0')
    resume_state_write "$TEST_WORKER_DIR" "$state"

    assert_failure "Should not be cooling after cooldown expires" \
        resume_state_is_cooling "$TEST_WORKER_DIR"
}

test_attempts_count() {
    # No file → 0
    local count
    count=$(resume_state_attempts "$TEST_WORKER_DIR")
    assert_equals "0" "$count" "No state file should return 0 attempts"

    # After increments
    resume_state_increment "$TEST_WORKER_DIR" "RETRY" "" "execution" ""
    resume_state_increment "$TEST_WORKER_DIR" "RETRY" "" "test" ""

    count=$(resume_state_attempts "$TEST_WORKER_DIR")
    assert_equals "2" "$count" "Should return 2 after two increments"
}

test_max_exceeded() {
    # No file → not exceeded
    assert_failure "No state file should not exceed max" \
        resume_state_max_exceeded "$TEST_WORKER_DIR"

    # Under max
    resume_state_write "$TEST_WORKER_DIR" '{"attempt_count":3,"max_attempts":5,"last_attempt_at":0,"cooldown_until":0,"terminal":false,"terminal_reason":"","history":[]}'
    assert_failure "3 of 5 should not exceed max" \
        resume_state_max_exceeded "$TEST_WORKER_DIR"

    # At max
    local state
    state=$(resume_state_read "$TEST_WORKER_DIR")
    state=$(echo "$state" | jq '.attempt_count = 5')
    resume_state_write "$TEST_WORKER_DIR" "$state"
    assert_success "5 of 5 should exceed max" \
        resume_state_max_exceeded "$TEST_WORKER_DIR"

    # Over max
    state=$(resume_state_read "$TEST_WORKER_DIR")
    state=$(echo "$state" | jq '.attempt_count = 7')
    resume_state_write "$TEST_WORKER_DIR" "$state"
    assert_success "7 of 5 should exceed max" \
        resume_state_max_exceeded "$TEST_WORKER_DIR"
}

test_history_accumulation() {
    resume_state_increment "$TEST_WORKER_DIR" "RETRY" "default" "execution" "first"
    resume_state_increment "$TEST_WORKER_DIR" "DEFER" "" "" "OOM"
    resume_state_increment "$TEST_WORKER_DIR" "COMPLETE" "" "" "done"

    local state
    state=$(resume_state_read "$TEST_WORKER_DIR")
    local history_len
    history_len=$(echo "$state" | jq '.history | length')

    assert_equals "3" "$history_len" "History should have 3 entries"

    # Verify each entry
    local d1 d2 d3
    d1=$(echo "$state" | jq -r '.history[0].decision')
    d2=$(echo "$state" | jq -r '.history[1].decision')
    d3=$(echo "$state" | jq -r '.history[2].decision')

    assert_equals "RETRY" "$d1" "First history entry should be RETRY"
    assert_equals "DEFER" "$d2" "Second history entry should be DEFER"
    assert_equals "COMPLETE" "$d3" "Third history entry should be COMPLETE"

    # Verify RETRY has pipeline/step
    local p1 s1
    p1=$(echo "$state" | jq -r '.history[0].pipeline')
    s1=$(echo "$state" | jq -r '.history[0].step')
    assert_equals "default" "$p1" "RETRY entry should have pipeline"
    assert_equals "execution" "$s1" "RETRY entry should have step"
}

test_atomic_write() {
    # Verify tmp file doesn't linger after write
    resume_state_write "$TEST_WORKER_DIR" '{"attempt_count":0,"max_attempts":5,"last_attempt_at":0,"cooldown_until":0,"terminal":false,"terminal_reason":"","history":[]}'

    assert_file_exists "$TEST_WORKER_DIR/resume-state.json" "State file should exist"
    assert_file_not_exists "$TEST_WORKER_DIR/resume-state.json.tmp" "Tmp file should not exist after write"
}

# ============================================================================
# Run tests
# ============================================================================
run_test test_read_default_state
run_test test_write_and_read
run_test test_increment
run_test test_terminal_detection
run_test test_cooldown_logic
run_test test_attempts_count
run_test test_max_exceeded
run_test test_history_accumulation
run_test test_atomic_write

print_test_summary
exit_with_test_result
