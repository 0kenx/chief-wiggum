#!/usr/bin/env bash
# Test circuit-breaker.sh functionality

set -e

# Get the script directory and project root
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

# Source the test framework
source "$SCRIPT_DIR/test-framework.sh"

# Source the circuit breaker
source "$PROJECT_ROOT/lib/circuit-breaker.sh"

# Create a test directory
TEST_DIR=$(mktemp -d)
trap 'rm -rf "$TEST_DIR"' EXIT

echo "Testing circuit-breaker.sh..."
echo ""

# =============================================================================
# Test cb_init
# =============================================================================

test_cb_init_creates_state_file() {
    local worker_dir="$TEST_DIR/test_init"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"

    assert_file_exists "$worker_dir/circuit-state.json" "State file should be created"
    assert_file_exists "$worker_dir/error-hashes.log" "Error hash log should be created"
    assert_file_exists "$worker_dir/progress-log.json" "Progress log should be created"
}

test_cb_init_state_content() {
    local worker_dir="$TEST_DIR/test_init_content"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"

    local state=$(jq -r '.state' "$worker_dir/circuit-state.json")
    assert_equals "CLOSED" "$state" "Initial state should be CLOSED"

    local iteration=$(jq -r '.iteration' "$worker_dir/circuit-state.json")
    assert_equals "0" "$iteration" "Initial iteration should be 0"

    local no_progress=$(jq -r '.no_progress_count' "$worker_dir/circuit-state.json")
    assert_equals "0" "$no_progress" "Initial no_progress_count should be 0"

    # Check that trip_message is present (from Comment 2706092990 fix)
    local trip_message=$(jq -r '.trip_message' "$worker_dir/circuit-state.json")
    assert_equals "null" "$trip_message" "Initial trip_message should be null"
}

# =============================================================================
# Test cb_get_state and cb_is_open
# =============================================================================

test_cb_get_state_returns_closed_when_no_file() {
    local worker_dir="$TEST_DIR/test_no_state"
    mkdir -p "$worker_dir"

    local state=$(cb_get_state "$worker_dir")
    assert_equals "CLOSED" "$state" "Should return CLOSED when no state file"
}

test_cb_get_state_returns_current_state() {
    local worker_dir="$TEST_DIR/test_current_state"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"

    local state=$(cb_get_state "$worker_dir")
    assert_equals "CLOSED" "$state" "Should return CLOSED after init"
}

test_cb_is_open_returns_false_when_closed() {
    local worker_dir="$TEST_DIR/test_is_open_closed"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"

    if cb_is_open "$worker_dir"; then
        echo -e "  ${RED}✗${NC} Circuit should not be open when CLOSED"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Circuit correctly returns not open when CLOSED"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_cb_is_open_returns_true_when_open() {
    local worker_dir="$TEST_DIR/test_is_open_open"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"
    cb_open "$worker_dir" "TEST" "Test reason"

    if cb_is_open "$worker_dir"; then
        echo -e "  ${GREEN}✓${NC} Circuit correctly returns open when OPEN"
    else
        echo -e "  ${RED}✗${NC} Circuit should be open when state is OPEN"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# Test cb_record_progress
# =============================================================================

test_cb_record_progress_with_progress() {
    local worker_dir="$TEST_DIR/test_progress_with"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"
    cb_record_progress "$worker_dir" "1" "5" "0" "1"

    local no_progress=$(jq -r '.no_progress_count' "$worker_dir/circuit-state.json")
    assert_equals "0" "$no_progress" "no_progress_count should be 0 when progress is made"

    local iteration=$(jq -r '.iteration' "$worker_dir/circuit-state.json")
    assert_equals "1" "$iteration" "iteration should be updated to 1"

    # Check progress log
    local log_count=$(jq 'length' "$worker_dir/progress-log.json")
    assert_equals "1" "$log_count" "Progress log should have 1 entry"
}

test_cb_record_progress_without_progress_increments_counter() {
    local worker_dir="$TEST_DIR/test_progress_without"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"
    cb_record_progress "$worker_dir" "1" "0" "0" "0"

    local no_progress=$(jq -r '.no_progress_count' "$worker_dir/circuit-state.json")
    assert_equals "1" "$no_progress" "no_progress_count should be 1 when no progress"
}

test_cb_record_progress_opens_circuit_after_threshold() {
    local worker_dir="$TEST_DIR/test_progress_threshold"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"

    # Record no progress multiple times (threshold is 3)
    cb_record_progress "$worker_dir" "1" "0" "0" "0"
    cb_record_progress "$worker_dir" "2" "0" "0" "0"
    cb_record_progress "$worker_dir" "3" "0" "0" "0"

    local state=$(cb_get_state "$worker_dir")
    assert_equals "OPEN" "$state" "Circuit should be OPEN after exceeding no-progress threshold"

    local trip_reason=$(jq -r '.trip_reason' "$worker_dir/circuit-state.json")
    assert_equals "NO_PROGRESS" "$trip_reason" "Trip reason should be NO_PROGRESS"
}

# =============================================================================
# Test cb_record_error
# =============================================================================

test_cb_record_error_stores_hash() {
    local worker_dir="$TEST_DIR/test_error_hash"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"
    cb_record_error "$worker_dir" "Test error message"

    local hash_count=$(grep -c -v '^#' "$worker_dir/error-hashes.log" || echo "0")
    assert_equals "1" "$hash_count" "Error hash log should have 1 entry"

    local identical_count=$(jq -r '.identical_error_count' "$worker_dir/circuit-state.json")
    assert_equals "1" "$identical_count" "identical_error_count should be 1 for new error"
}

test_cb_record_error_increments_identical_count() {
    local worker_dir="$TEST_DIR/test_error_identical"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"

    # Record the same error multiple times
    cb_record_error "$worker_dir" "Same error message"
    cb_record_error "$worker_dir" "Same error message"
    cb_record_error "$worker_dir" "Same error message"

    local identical_count=$(jq -r '.identical_error_count' "$worker_dir/circuit-state.json")
    assert_equals "3" "$identical_count" "identical_error_count should be 3 for repeated error"
}

test_cb_record_error_opens_circuit_after_threshold() {
    local worker_dir="$TEST_DIR/test_error_threshold"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"

    # Record the same error multiple times (threshold is 5)
    for i in {1..5}; do
        cb_record_error "$worker_dir" "Repeated error message"
    done

    local state=$(cb_get_state "$worker_dir")
    assert_equals "OPEN" "$state" "Circuit should be OPEN after exceeding identical error threshold"

    local trip_reason=$(jq -r '.trip_reason' "$worker_dir/circuit-state.json")
    assert_equals "IDENTICAL_ERROR" "$trip_reason" "Trip reason should be IDENTICAL_ERROR"
}

# =============================================================================
# Test cb_classify_error
# =============================================================================

test_cb_classify_error_transient() {
    local worker_dir="$TEST_DIR/test_classify_transient"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"
    cb_record_error "$worker_dir" "Test error"

    # Get the hash
    local hash=$(grep -v '^#' "$worker_dir/error-hashes.log" | awk '{print $2}' | head -1)

    local classification=$(cb_classify_error "$worker_dir" "$hash")
    assert_equals "transient" "$classification" "Single occurrence should be transient"
}

test_cb_classify_error_persistent() {
    local worker_dir="$TEST_DIR/test_classify_persistent"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"

    # Record the same error multiple times (threshold is 2)
    cb_record_error "$worker_dir" "Persistent error"
    cb_record_error "$worker_dir" "Persistent error"
    cb_record_error "$worker_dir" "Persistent error"

    # Get the hash
    local hash=$(grep -v '^#' "$worker_dir/error-hashes.log" | awk '{print $2}' | head -1)

    local classification=$(cb_classify_error "$worker_dir" "$hash")
    assert_equals "persistent" "$classification" "Multiple occurrences should be persistent"
}

# =============================================================================
# Test cb_open and cb_reset
# =============================================================================

test_cb_open_sets_state() {
    local worker_dir="$TEST_DIR/test_open"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"
    cb_open "$worker_dir" "TEST_REASON" "Test message"

    local state=$(jq -r '.state' "$worker_dir/circuit-state.json")
    assert_equals "OPEN" "$state" "State should be OPEN"

    local trip_reason=$(jq -r '.trip_reason' "$worker_dir/circuit-state.json")
    assert_equals "TEST_REASON" "$trip_reason" "Trip reason should match"

    local trip_message=$(jq -r '.trip_message' "$worker_dir/circuit-state.json")
    assert_equals "Test message" "$trip_message" "Trip message should match"
}

test_cb_reset_closes_circuit() {
    local worker_dir="$TEST_DIR/test_reset"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"
    cb_open "$worker_dir" "TEST" "Test"
    cb_reset "$worker_dir"

    local state=$(jq -r '.state' "$worker_dir/circuit-state.json")
    assert_equals "CLOSED" "$state" "State should be CLOSED after reset"

    local no_progress=$(jq -r '.no_progress_count' "$worker_dir/circuit-state.json")
    assert_equals "0" "$no_progress" "no_progress_count should be reset to 0"

    local identical_err=$(jq -r '.identical_error_count' "$worker_dir/circuit-state.json")
    assert_equals "0" "$identical_err" "identical_error_count should be reset to 0"
}

# =============================================================================
# Test cb_detect_file_changes (subshell test from Comment 2706093038)
# =============================================================================

test_cb_detect_file_changes_preserves_directory() {
    local worker_dir="$TEST_DIR/test_detect_changes"
    mkdir -p "$worker_dir"

    # Create a git repo for testing
    local test_workspace="$TEST_DIR/test_workspace"
    mkdir -p "$test_workspace"
    (cd "$test_workspace" && git init -q && touch file.txt && git add . && git commit -q -m "init")

    # Record current directory
    local original_dir=$(pwd)

    # Call the function
    cb_detect_file_changes "$test_workspace"

    # Verify we're still in the original directory
    local current_dir=$(pwd)
    assert_equals "$original_dir" "$current_dir" "Working directory should be preserved after cb_detect_file_changes"
}

# =============================================================================
# Test cb_get_status and cb_get_status_line
# =============================================================================

test_cb_get_status_returns_json() {
    local worker_dir="$TEST_DIR/test_status_json"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"

    local status=$(cb_get_status "$worker_dir")

    # Verify it's valid JSON by parsing it
    if echo "$status" | jq -e . >/dev/null 2>&1; then
        echo -e "  ${GREEN}✓${NC} cb_get_status returns valid JSON"
    else
        echo -e "  ${RED}✗${NC} cb_get_status should return valid JSON"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_cb_get_status_line_closed() {
    local worker_dir="$TEST_DIR/test_status_line_closed"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"

    local status_line=$(cb_get_status_line "$worker_dir")

    assert_output_contains "$status_line" "CLOSED" "Status line should contain CLOSED"
}

test_cb_get_status_line_open() {
    local worker_dir="$TEST_DIR/test_status_line_open"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"
    cb_open "$worker_dir" "TEST_REASON" "Test message"

    local status_line=$(cb_get_status_line "$worker_dir")

    assert_output_contains "$status_line" "OPEN" "Status line should contain OPEN"
    assert_output_contains "$status_line" "TEST_REASON" "Status line should contain trip reason"
}

# =============================================================================
# Test cb_get_error_summary (count validation from Comment 2706093024)
# =============================================================================

test_cb_get_error_summary_handles_empty_log() {
    local worker_dir="$TEST_DIR/test_summary_empty"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"

    local summary=$(cb_get_error_summary "$worker_dir")

    local transient=$(echo "$summary" | jq -r '.transient')
    local persistent=$(echo "$summary" | jq -r '.persistent')
    local unique=$(echo "$summary" | jq -r '.unique_errors')

    assert_equals "0" "$transient" "Transient count should be 0 for empty log"
    assert_equals "0" "$persistent" "Persistent count should be 0 for empty log"
    assert_equals "0" "$unique" "Unique count should be 0 for empty log"
}

test_cb_get_error_summary_counts_correctly() {
    local worker_dir="$TEST_DIR/test_summary_counts"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"

    # Add transient error (1 occurrence)
    cb_record_error "$worker_dir" "Transient error"

    # Add persistent error (3 occurrences, threshold is 2)
    cb_record_error "$worker_dir" "Persistent error 1"
    cb_record_error "$worker_dir" "Persistent error 1"
    cb_record_error "$worker_dir" "Persistent error 1"

    local summary=$(cb_get_error_summary "$worker_dir")

    local unique=$(echo "$summary" | jq -r '.unique_errors')
    assert_equals "2" "$unique" "Should have 2 unique errors"
}

# =============================================================================
# Test cb_check_iteration
# =============================================================================

test_cb_check_iteration_returns_success_for_closed() {
    local worker_dir="$TEST_DIR/test_check_iter_closed"
    mkdir -p "$worker_dir"
    mkdir -p "$worker_dir/logs"

    # Create a mock workspace
    local workspace="$TEST_DIR/workspace_check"
    mkdir -p "$workspace"
    (cd "$workspace" && git init -q && touch file.txt && git add . && git commit -q -m "init")

    # Create mock files
    touch "$worker_dir/prd.md"
    touch "$worker_dir/logs/iteration-1.log"

    cb_init "$worker_dir"

    if cb_check_iteration "$worker_dir" "1" "$workspace" "$worker_dir/prd.md" "$worker_dir/logs/iteration-1.log"; then
        echo -e "  ${GREEN}✓${NC} cb_check_iteration returns success when circuit is CLOSED"
    else
        echo -e "  ${RED}✗${NC} cb_check_iteration should return success when circuit is CLOSED"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_cb_check_iteration_returns_failure_for_open() {
    local worker_dir="$TEST_DIR/test_check_iter_open"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"
    cb_open "$worker_dir" "TEST" "Test"

    if cb_check_iteration "$worker_dir" "1" "/tmp" "/tmp/prd.md" "/tmp/log"; then
        echo -e "  ${RED}✗${NC} cb_check_iteration should return failure when circuit is OPEN"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} cb_check_iteration returns failure when circuit is OPEN"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# Test cb_check_errors
# =============================================================================

test_cb_check_errors_returns_success_when_circuit_closed() {
    local worker_dir="$TEST_DIR/test_check_errors_closed"
    mkdir -p "$worker_dir"

    cb_init "$worker_dir"

    # Create a log file with some errors
    local log_file="$worker_dir/test.log"
    echo '{"error": "test error"}' > "$log_file"

    if cb_check_errors "$worker_dir" "$log_file"; then
        echo -e "  ${GREEN}✓${NC} cb_check_errors returns success when circuit stays CLOSED"
    else
        echo -e "  ${RED}✗${NC} cb_check_errors should return success when circuit stays CLOSED"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# Run all tests
# =============================================================================

echo "=== Circuit Breaker Initialization Tests ==="
run_test test_cb_init_creates_state_file
run_test test_cb_init_state_content

echo ""
echo "=== State Query Tests ==="
run_test test_cb_get_state_returns_closed_when_no_file
run_test test_cb_get_state_returns_current_state
run_test test_cb_is_open_returns_false_when_closed
run_test test_cb_is_open_returns_true_when_open

echo ""
echo "=== Progress Recording Tests ==="
run_test test_cb_record_progress_with_progress
run_test test_cb_record_progress_without_progress_increments_counter
run_test test_cb_record_progress_opens_circuit_after_threshold

echo ""
echo "=== Error Recording Tests ==="
run_test test_cb_record_error_stores_hash
run_test test_cb_record_error_increments_identical_count
run_test test_cb_record_error_opens_circuit_after_threshold

echo ""
echo "=== Error Classification Tests ==="
run_test test_cb_classify_error_transient
run_test test_cb_classify_error_persistent

echo ""
echo "=== Circuit Control Tests ==="
run_test test_cb_open_sets_state
run_test test_cb_reset_closes_circuit

echo ""
echo "=== File Detection Tests ==="
run_test test_cb_detect_file_changes_preserves_directory

echo ""
echo "=== Status Reporting Tests ==="
run_test test_cb_get_status_returns_json
run_test test_cb_get_status_line_closed
run_test test_cb_get_status_line_open

echo ""
echo "=== Error Summary Tests ==="
run_test test_cb_get_error_summary_handles_empty_log
run_test test_cb_get_error_summary_counts_correctly

echo ""
echo "=== Integration Tests ==="
run_test test_cb_check_iteration_returns_success_for_closed
run_test test_cb_check_iteration_returns_failure_for_open
run_test test_cb_check_errors_returns_success_when_circuit_closed

echo ""
print_test_summary
exit_with_test_result
