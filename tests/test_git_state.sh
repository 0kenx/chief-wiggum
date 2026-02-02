#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/worker/git-state.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/worker/git-state.sh"

# Create temp dir for test isolation
TEST_DIR=""
WORKER_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    WORKER_DIR="$TEST_DIR/worker-TASK-001-12345"
    mkdir -p "$WORKER_DIR"
}

teardown() {
    rm -rf "$TEST_DIR"
}

# =============================================================================
# git_state_get() Tests
# =============================================================================

test_git_state_get_returns_none_when_no_file() {
    local result
    result=$(git_state_get "$WORKER_DIR")

    assert_equals "none" "$result" "Should return 'none' when no state file exists"
}

test_git_state_get_returns_current_state() {
    echo '{"current_state": "needs_fix"}' > "$WORKER_DIR/git-state.json"

    local result
    result=$(git_state_get "$WORKER_DIR")

    assert_equals "needs_fix" "$result" "Should return current state"
}

test_git_state_get_returns_none_for_null_state() {
    echo '{"current_state": null}' > "$WORKER_DIR/git-state.json"

    local result
    result=$(git_state_get "$WORKER_DIR")

    assert_equals "none" "$result" "Should return 'none' when state is null"
}

# =============================================================================
# git_state_set() Tests
# =============================================================================

test_git_state_set_creates_new_file() {
    git_state_set "$WORKER_DIR" "needs_fix" "test-agent" "Test reason"

    assert_file_exists "$WORKER_DIR/git-state.json" "Should create state file"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "needs_fix" "$state" "Should set correct state"
}

test_git_state_set_initializes_with_transition() {
    git_state_set "$WORKER_DIR" "needs_fix" "test-agent" "Initial state"

    local transitions
    transitions=$(jq -r '.transitions | length' "$WORKER_DIR/git-state.json")

    assert_equals "1" "$transitions" "Should have one transition"

    local first_to
    first_to=$(jq -r '.transitions[0].to' "$WORKER_DIR/git-state.json")
    assert_equals "needs_fix" "$first_to" "First transition should be to needs_fix"

    local first_from
    first_from=$(jq -r '.transitions[0].from' "$WORKER_DIR/git-state.json")
    assert_equals "null" "$first_from" "First transition should be from null"
}

test_git_state_set_updates_existing_state() {
    git_state_set "$WORKER_DIR" "needs_fix" "agent1" "First state"
    git_state_set "$WORKER_DIR" "fixing" "agent2" "Second state"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "fixing" "$state" "Should update to new state"

    local transitions
    transitions=$(jq -r '.transitions | length' "$WORKER_DIR/git-state.json")
    assert_equals "2" "$transitions" "Should have two transitions"
}

test_git_state_set_records_transition_from() {
    git_state_set "$WORKER_DIR" "needs_fix" "agent1" "First"
    git_state_set "$WORKER_DIR" "fixing" "agent2" "Second"

    local last_from
    last_from=$(jq -r '.transitions[-1].from' "$WORKER_DIR/git-state.json")
    assert_equals "needs_fix" "$last_from" "Should record previous state as 'from'"
}

test_git_state_set_records_agent() {
    git_state_set "$WORKER_DIR" "needs_fix" "wiggum-pr.sync" "Test"

    local agent
    agent=$(jq -r '.transitions[0].agent' "$WORKER_DIR/git-state.json")
    assert_equals "wiggum-pr.sync" "$agent" "Should record agent name"
}

test_git_state_set_records_reason() {
    git_state_set "$WORKER_DIR" "needs_fix" "test" "New PR comments detected"

    local reason
    reason=$(jq -r '.transitions[0].reason' "$WORKER_DIR/git-state.json")
    assert_equals "New PR comments detected" "$reason" "Should record reason"
}

test_git_state_set_fails_on_missing_worker_dir() {
    local result=0
    git_state_set "/nonexistent/path" "state" "agent" "reason" 2>/dev/null || result=$?

    assert_equals "1" "$result" "Should fail when worker_dir doesn't exist"
}

# =============================================================================
# git_state_set_pr() Tests
# =============================================================================

test_git_state_set_pr_sets_number() {
    git_state_set "$WORKER_DIR" "needs_fix" "test" "Init"
    git_state_set_pr "$WORKER_DIR" 123

    local pr
    pr=$(jq -r '.pr_number' "$WORKER_DIR/git-state.json")
    assert_equals "123" "$pr" "Should set PR number"
}

test_git_state_set_pr_creates_file_if_missing() {
    # Should create state file with PR number if it doesn't exist
    git_state_set_pr "$WORKER_DIR" 123

    assert_file_exists "$WORKER_DIR/git-state.json" "Should create state file"

    local pr
    pr=$(jq -r '.pr_number' "$WORKER_DIR/git-state.json")
    assert_equals "123" "$pr" "Should set PR number in new file"

    local state
    state=$(jq -r '.current_state' "$WORKER_DIR/git-state.json")
    assert_equals "none" "$state" "Should have 'none' as initial state"
}

# =============================================================================
# git_state_get_pr() Tests
# =============================================================================

test_git_state_get_pr_returns_number() {
    git_state_set "$WORKER_DIR" "needs_fix" "test" "Init"
    git_state_set_pr "$WORKER_DIR" 456

    local pr
    pr=$(git_state_get_pr "$WORKER_DIR")
    assert_equals "456" "$pr" "Should return PR number"
}

test_git_state_get_pr_returns_null_when_not_set() {
    git_state_set "$WORKER_DIR" "needs_fix" "test" "Init"

    local pr
    pr=$(git_state_get_pr "$WORKER_DIR")
    assert_equals "null" "$pr" "Should return 'null' when PR not set"
}

test_git_state_get_pr_returns_null_when_no_file() {
    local pr
    pr=$(git_state_get_pr "$WORKER_DIR")
    assert_equals "null" "$pr" "Should return 'null' when no file exists"
}

# =============================================================================
# git_state_inc_merge_attempts() Tests
# =============================================================================

test_git_state_inc_merge_attempts_increments() {
    git_state_set "$WORKER_DIR" "merging" "test" "Init"

    git_state_inc_merge_attempts "$WORKER_DIR"
    local attempts
    attempts=$(git_state_get_merge_attempts "$WORKER_DIR")
    assert_equals "1" "$attempts" "Should increment to 1"

    git_state_inc_merge_attempts "$WORKER_DIR"
    attempts=$(git_state_get_merge_attempts "$WORKER_DIR")
    assert_equals "2" "$attempts" "Should increment to 2"
}

test_git_state_inc_merge_attempts_fails_without_file() {
    local result=0
    git_state_inc_merge_attempts "$WORKER_DIR" || result=$?

    assert_equals "1" "$result" "Should fail when no state file exists"
}

# =============================================================================
# git_state_get_merge_attempts() Tests
# =============================================================================

test_git_state_get_merge_attempts_returns_zero_initially() {
    git_state_set "$WORKER_DIR" "needs_fix" "test" "Init"

    local attempts
    attempts=$(git_state_get_merge_attempts "$WORKER_DIR")
    assert_equals "0" "$attempts" "Should return 0 initially"
}

test_git_state_get_merge_attempts_returns_zero_no_file() {
    local attempts
    attempts=$(git_state_get_merge_attempts "$WORKER_DIR")
    assert_equals "0" "$attempts" "Should return 0 when no file exists"
}

# =============================================================================
# git_state_set_error() Tests
# =============================================================================

test_git_state_set_error_records_error() {
    git_state_set "$WORKER_DIR" "failed" "test" "Init"
    git_state_set_error "$WORKER_DIR" "Merge conflict detected"

    local error
    error=$(git_state_get_error "$WORKER_DIR")
    assert_equals "Merge conflict detected" "$error" "Should record error message"
}

test_git_state_set_error_fails_without_file() {
    local result=0
    git_state_set_error "$WORKER_DIR" "Error" || result=$?

    assert_equals "1" "$result" "Should fail when no state file exists"
}

# =============================================================================
# git_state_get_error() Tests
# =============================================================================

test_git_state_get_error_returns_null_when_not_set() {
    git_state_set "$WORKER_DIR" "needs_fix" "test" "Init"

    local error
    error=$(git_state_get_error "$WORKER_DIR")
    assert_equals "null" "$error" "Should return 'null' when no error set"
}

test_git_state_get_error_returns_null_no_file() {
    local error
    error=$(git_state_get_error "$WORKER_DIR")
    assert_equals "null" "$error" "Should return 'null' when no file exists"
}

# =============================================================================
# git_state_is() Tests
# =============================================================================

test_git_state_is_returns_true_on_match() {
    git_state_set "$WORKER_DIR" "needs_fix" "test" "Init"

    if git_state_is "$WORKER_DIR" "needs_fix"; then
        echo -e "  ${GREEN}✓${NC} Should return true when state matches"
    else
        echo -e "  ${RED}X${NC} Should return true when state matches"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_git_state_is_returns_false_on_mismatch() {
    git_state_set "$WORKER_DIR" "needs_fix" "test" "Init"

    if git_state_is "$WORKER_DIR" "fixing"; then
        echo -e "  ${RED}X${NC} Should return false when state doesn't match"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Should return false when state doesn't match"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_git_state_is_returns_false_no_file() {
    if git_state_is "$WORKER_DIR" "needs_fix"; then
        echo -e "  ${RED}X${NC} Should return false when no file exists"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Should return false when no file exists"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# git_state_is_any() Tests
# =============================================================================

test_git_state_is_any_returns_true_on_match() {
    git_state_set "$WORKER_DIR" "fixing" "test" "Init"

    if git_state_is_any "$WORKER_DIR" "needs_fix" "fixing" "fix_completed"; then
        echo -e "  ${GREEN}✓${NC} Should return true when state matches any"
    else
        echo -e "  ${RED}X${NC} Should return true when state matches any"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_git_state_is_any_returns_false_on_no_match() {
    git_state_set "$WORKER_DIR" "merged" "test" "Init"

    if git_state_is_any "$WORKER_DIR" "needs_fix" "fixing" "fix_completed"; then
        echo -e "  ${RED}X${NC} Should return false when state matches none"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Should return false when state matches none"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# git_state_dump() Tests
# =============================================================================

test_git_state_dump_returns_full_json() {
    git_state_set "$WORKER_DIR" "needs_fix" "test" "Init"
    git_state_set_pr "$WORKER_DIR" 999

    local dump
    dump=$(git_state_dump "$WORKER_DIR")

    local state
    state=$(echo "$dump" | jq -r '.current_state')
    assert_equals "needs_fix" "$state" "Dump should contain current_state"

    local pr
    pr=$(echo "$dump" | jq -r '.pr_number')
    assert_equals "999" "$pr" "Dump should contain pr_number"
}

test_git_state_dump_returns_empty_object_no_file() {
    local dump
    dump=$(git_state_dump "$WORKER_DIR")

    assert_equals "{}" "$dump" "Should return empty object when no file"
}

# =============================================================================
# git_state_transitions() Tests
# =============================================================================

test_git_state_transitions_returns_array() {
    git_state_set "$WORKER_DIR" "needs_fix" "agent1" "First"
    git_state_set "$WORKER_DIR" "fixing" "agent2" "Second"
    git_state_set "$WORKER_DIR" "fix_completed" "agent3" "Third"

    local transitions
    transitions=$(git_state_transitions "$WORKER_DIR")

    local count
    count=$(echo "$transitions" | jq 'length')
    assert_equals "3" "$count" "Should return all transitions"
}

test_git_state_transitions_returns_empty_array_no_file() {
    local transitions
    transitions=$(git_state_transitions "$WORKER_DIR")

    assert_equals "[]" "$transitions" "Should return empty array when no file"
}

# =============================================================================
# git_state_clear() Tests
# =============================================================================

test_git_state_clear_removes_file() {
    git_state_set "$WORKER_DIR" "needs_fix" "test" "Init"
    assert_file_exists "$WORKER_DIR/git-state.json" "State file should exist before clear"

    git_state_clear "$WORKER_DIR"

    assert_file_not_exists "$WORKER_DIR/git-state.json" "State file should be removed"
}

test_git_state_clear_succeeds_when_no_file() {
    # Should not error when file doesn't exist
    git_state_clear "$WORKER_DIR"

    echo -e "  ${GREEN}✓${NC} Should succeed when no file to clear"
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# State Machine Flow Tests
# =============================================================================

test_full_fix_merge_flow() {
    # Simulate the full workflow
    git_state_set "$WORKER_DIR" "needs_fix" "wiggum-pr.sync" "New PR comments detected"
    git_state_set_pr "$WORKER_DIR" 42

    assert_equals "needs_fix" "$(git_state_get "$WORKER_DIR")" "Initial state"

    git_state_set "$WORKER_DIR" "fixing" "wiggum-run.check_and_spawn_fixes" "Fix worker spawned"
    assert_equals "fixing" "$(git_state_get "$WORKER_DIR")" "After fix spawn"

    git_state_set "$WORKER_DIR" "fix_completed" "engineering.pr-comment-fix" "All comments addressed"
    assert_equals "fix_completed" "$(git_state_get "$WORKER_DIR")" "After fix complete"

    git_state_set "$WORKER_DIR" "needs_merge" "wiggum-run.handle_fix_completion" "Ready for merge"
    assert_equals "needs_merge" "$(git_state_get "$WORKER_DIR")" "Ready for merge"

    git_state_set "$WORKER_DIR" "merging" "wiggum-run.attempt_pr_merge" "Attempting merge"
    git_state_inc_merge_attempts "$WORKER_DIR"
    assert_equals "1" "$(git_state_get_merge_attempts "$WORKER_DIR")" "First attempt"

    git_state_set "$WORKER_DIR" "merged" "wiggum-run.attempt_pr_merge" "PR merged"
    assert_equals "merged" "$(git_state_get "$WORKER_DIR")" "Final state"

    # Verify audit trail
    local transition_count
    transition_count=$(jq '.transitions | length' "$WORKER_DIR/git-state.json")
    assert_equals "6" "$transition_count" "Should have 6 transitions in audit trail"
}

test_conflict_resolution_flow() {
    git_state_set "$WORKER_DIR" "needs_fix" "test" "Init"
    git_state_set "$WORKER_DIR" "fixing" "test" "Fixing"
    git_state_set "$WORKER_DIR" "fix_completed" "test" "Fixed"
    git_state_set "$WORKER_DIR" "needs_merge" "test" "Ready"
    git_state_set "$WORKER_DIR" "merging" "test" "Merging"
    git_state_inc_merge_attempts "$WORKER_DIR"

    # Merge fails with conflict
    git_state_set "$WORKER_DIR" "merge_conflict" "test" "Conflict detected"
    git_state_set_error "$WORKER_DIR" "CONFLICT in file.txt"
    git_state_set "$WORKER_DIR" "needs_resolve" "test" "Resolver required"

    assert_equals "needs_resolve" "$(git_state_get "$WORKER_DIR")" "State after conflict"
    assert_equals "CONFLICT in file.txt" "$(git_state_get_error "$WORKER_DIR")" "Error recorded"

    # Resolver runs
    git_state_set "$WORKER_DIR" "resolving" "test" "Resolver spawned"
    git_state_set "$WORKER_DIR" "resolved" "test" "Conflicts resolved"

    # Retry merge
    git_state_set "$WORKER_DIR" "needs_merge" "test" "Ready for retry"
    git_state_set "$WORKER_DIR" "merging" "test" "Merging again"
    git_state_inc_merge_attempts "$WORKER_DIR"

    assert_equals "2" "$(git_state_get_merge_attempts "$WORKER_DIR")" "Second attempt"

    git_state_set "$WORKER_DIR" "merged" "test" "Success"
    assert_equals "merged" "$(git_state_get "$WORKER_DIR")" "Final state after retry"
}

# =============================================================================
# Run All Tests
# =============================================================================

# git_state_get tests
run_test test_git_state_get_returns_none_when_no_file
run_test test_git_state_get_returns_current_state
run_test test_git_state_get_returns_none_for_null_state

# git_state_set tests
run_test test_git_state_set_creates_new_file
run_test test_git_state_set_initializes_with_transition
run_test test_git_state_set_updates_existing_state
run_test test_git_state_set_records_transition_from
run_test test_git_state_set_records_agent
run_test test_git_state_set_records_reason
run_test test_git_state_set_fails_on_missing_worker_dir

# git_state_set_pr tests
run_test test_git_state_set_pr_sets_number
run_test test_git_state_set_pr_creates_file_if_missing

# git_state_get_pr tests
run_test test_git_state_get_pr_returns_number
run_test test_git_state_get_pr_returns_null_when_not_set
run_test test_git_state_get_pr_returns_null_when_no_file

# git_state_inc_merge_attempts tests
run_test test_git_state_inc_merge_attempts_increments
run_test test_git_state_inc_merge_attempts_fails_without_file

# git_state_get_merge_attempts tests
run_test test_git_state_get_merge_attempts_returns_zero_initially
run_test test_git_state_get_merge_attempts_returns_zero_no_file

# git_state_set_error tests
run_test test_git_state_set_error_records_error
run_test test_git_state_set_error_fails_without_file

# git_state_get_error tests
run_test test_git_state_get_error_returns_null_when_not_set
run_test test_git_state_get_error_returns_null_no_file

# git_state_is tests
run_test test_git_state_is_returns_true_on_match
run_test test_git_state_is_returns_false_on_mismatch
run_test test_git_state_is_returns_false_no_file

# git_state_is_any tests
run_test test_git_state_is_any_returns_true_on_match
run_test test_git_state_is_any_returns_false_on_no_match

# git_state_dump tests
run_test test_git_state_dump_returns_full_json
run_test test_git_state_dump_returns_empty_object_no_file

# git_state_transitions tests
run_test test_git_state_transitions_returns_array
run_test test_git_state_transitions_returns_empty_array_no_file

# git_state_clear tests
run_test test_git_state_clear_removes_file
run_test test_git_state_clear_succeeds_when_no_file

# State machine flow tests
run_test test_full_fix_merge_flow
run_test test_conflict_resolution_flow

print_test_summary
exit_with_test_result
