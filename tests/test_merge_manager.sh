#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/scheduler/merge-manager.sh
# Specifically: _wait_for_mergeable() and "not mergeable" retry handling

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

# We need to source dependencies that merge-manager.sh requires.
# Stub out functions that aren't relevant to our unit tests.
source "$WIGGUM_HOME/lib/worker/git-state.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"

# Stub functions from modules we don't want to fully load
update_kanban_status() { :; }
conflict_queue_add() { :; }
conflict_queue_remove() { :; }
batch_coord_has_worker_context() { return 1; }

source "$WIGGUM_HOME/lib/scheduler/merge-manager.sh"

# Test state
TEST_DIR=""
WORKER_DIR=""
RALPH_DIR=""
MOCK_BIN=""

setup() {
    TEST_DIR=$(mktemp -d)
    RALPH_DIR="$TEST_DIR/.ralph"
    WORKER_DIR="$RALPH_DIR/workers/worker-TASK-001-12345"
    MOCK_BIN="$TEST_DIR/mock-bin"
    mkdir -p "$WORKER_DIR" "$MOCK_BIN" "$WORKER_DIR/workspace"

    # Set short timeouts for tests
    export MERGE_POLL_TIMEOUT=2
    export MERGE_POLL_INTERVAL=0.1
    export MAX_MERGE_ATTEMPTS=3

    # Initialize git state with a PR number
    git_state_set "$WORKER_DIR" "needs_merge" "test" "Init"
    git_state_set_pr "$WORKER_DIR" 42

    # Set up approved review so _check_merge_approved() passes
    export WIGGUM_APPROVED_USER_IDS="12345"
    echo '[{"user_id": 12345, "state": "APPROVED", "submitted_at": "2025-01-01T00:00:00Z"}]' \
        > "$WORKER_DIR/pr-reviews.json"

    # Prepend mock bin to PATH so we can stub gh
    export PATH="$MOCK_BIN:$PATH"
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# Helper: create a mock gh script
# =============================================================================
_mock_gh() {
    local script="$1"
    cat > "$MOCK_BIN/gh" << GHEOF
#!/usr/bin/env bash
$script
GHEOF
    chmod +x "$MOCK_BIN/gh"
}

# =============================================================================
# _wait_for_mergeable() Tests
# =============================================================================

test_wait_for_mergeable_returns_0_when_mergeable() {
    _mock_gh 'echo "MERGEABLE"'

    local result=0
    _wait_for_mergeable 42 "TASK-001" || result=$?

    assert_equals "0" "$result" "Should return 0 when PR is MERGEABLE"
}

test_wait_for_mergeable_returns_1_when_conflicting() {
    _mock_gh 'echo "CONFLICTING"'

    local result=0
    _wait_for_mergeable 42 "TASK-001" || result=$?

    assert_equals "1" "$result" "Should return 1 when PR is CONFLICTING"
}

test_wait_for_mergeable_returns_2_on_timeout() {
    # Always return UNKNOWN - should time out
    _mock_gh 'echo "UNKNOWN"'
    MERGE_POLL_TIMEOUT=1
    MERGE_POLL_INTERVAL=0.1

    local result=0
    _wait_for_mergeable 42 "TASK-001" 2>/dev/null || result=$?

    assert_equals "2" "$result" "Should return 2 on timeout"
}

test_wait_for_mergeable_polls_until_determined() {
    # First call returns UNKNOWN, second returns MERGEABLE
    local counter_file="$TEST_DIR/gh_call_count"
    echo "0" > "$counter_file"

    cat > "$MOCK_BIN/gh" << GHEOF
#!/usr/bin/env bash
count=\$(cat "$counter_file")
count=\$((count + 1))
echo "\$count" > "$counter_file"
if [ "\$count" -le 1 ]; then
    echo "UNKNOWN"
else
    echo "MERGEABLE"
fi
GHEOF
    chmod +x "$MOCK_BIN/gh"

    export MERGE_POLL_TIMEOUT=2
    export MERGE_POLL_INTERVAL=0.1

    local result=0
    _wait_for_mergeable 42 "TASK-001" || result=$?

    assert_equals "0" "$result" "Should succeed after polling through UNKNOWN"

    local calls
    calls=$(cat "$counter_file")
    assert_equals "2" "$calls" "Should have polled twice (UNKNOWN then MERGEABLE)"
}

test_wait_for_mergeable_returns_2_on_unexpected_status() {
    _mock_gh 'echo "WEIRD_STATUS"'

    local result=0
    _wait_for_mergeable 42 "TASK-001" 2>/dev/null || result=$?

    assert_equals "2" "$result" "Should return 2 on unexpected status"
}

test_wait_for_mergeable_returns_2_on_gh_failure() {
    _mock_gh 'exit 1'

    local result=0
    _wait_for_mergeable 42 "TASK-001" 2>/dev/null || result=$?

    # gh failure produces empty string which maps to UNKNOWN, then times out
    assert_equals "2" "$result" "Should return 2 when gh fails"
}

# =============================================================================
# attempt_pr_merge() "not mergeable" retry Tests
# =============================================================================

test_not_mergeable_is_retryable() {
    # Mock gh: pr view returns MERGEABLE, pr merge returns "not mergeable" error
    cat > "$MOCK_BIN/gh" << 'GHEOF'
#!/usr/bin/env bash
if [[ "$*" == *"pr view"* ]]; then
    echo "MERGEABLE"
elif [[ "$*" == *"pr merge"* ]]; then
    echo "GraphQL: Pull Request is not mergeable (mergePullRequest)" >&2
    exit 1
fi
GHEOF
    chmod +x "$MOCK_BIN/gh"

    local result=0
    attempt_pr_merge "$WORKER_DIR" "TASK-001" "$RALPH_DIR" 2>/dev/null || result=$?

    # Should return 1 (retryable) not 2 (permanent failure)
    assert_equals "1" "$result" "not mergeable should be retryable"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "needs_merge" "$state" "State should be needs_merge for retry"
}

test_not_mergeable_fails_permanently_at_max_attempts() {
    # Exhaust all but last attempt
    git_state_inc_merge_attempts "$WORKER_DIR"
    git_state_inc_merge_attempts "$WORKER_DIR"

    # Mock gh: pr view returns MERGEABLE, pr merge returns "not mergeable"
    cat > "$MOCK_BIN/gh" << 'GHEOF'
#!/usr/bin/env bash
if [[ "$*" == *"pr view"* ]]; then
    echo "MERGEABLE"
elif [[ "$*" == *"pr merge"* ]]; then
    echo "GraphQL: Pull Request is not mergeable (mergePullRequest)" >&2
    exit 1
fi
GHEOF
    chmod +x "$MOCK_BIN/gh"

    local result=0
    attempt_pr_merge "$WORKER_DIR" "TASK-001" "$RALPH_DIR" 2>/dev/null || result=$?

    # At max attempts, should be permanent failure
    assert_equals "2" "$result" "Should be permanent failure at max attempts"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "failed" "$state" "State should be failed at max attempts"
}

test_conflict_detected_by_poll_skips_merge_call() {
    # Track whether gh pr merge was called
    local merge_called_file="$TEST_DIR/merge_called"
    echo "no" > "$merge_called_file"

    cat > "$MOCK_BIN/gh" << GHEOF
#!/usr/bin/env bash
if [[ "\$*" == *"pr view"* ]]; then
    echo "CONFLICTING"
elif [[ "\$*" == *"pr merge"* ]]; then
    echo "yes" > "$merge_called_file"
    echo "merged"
fi
GHEOF
    chmod +x "$MOCK_BIN/gh"

    local result=0
    attempt_pr_merge "$WORKER_DIR" "TASK-001" "$RALPH_DIR" || result=$?

    assert_equals "1" "$result" "Should return 1 for conflict"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "needs_resolve" "$state" "State should be needs_resolve"

    local merge_called
    merge_called=$(cat "$merge_called_file")
    assert_equals "no" "$merge_called" "gh pr merge should not have been called"
}

test_successful_merge_after_poll() {
    # Mock gh: pr view returns MERGEABLE, pr merge succeeds
    cat > "$MOCK_BIN/gh" << 'GHEOF'
#!/usr/bin/env bash
if [[ "$*" == *"pr view"* ]]; then
    echo "MERGEABLE"
elif [[ "$*" == *"pr merge"* ]]; then
    echo "merged"
    exit 0
fi
GHEOF
    chmod +x "$MOCK_BIN/gh"

    # Stub git for _cleanup_merged_pr_worktree
    cat > "$MOCK_BIN/git" << 'GHEOF'
#!/usr/bin/env bash
echo ""
exit 0
GHEOF
    chmod +x "$MOCK_BIN/git"

    local result=0
    attempt_pr_merge "$WORKER_DIR" "TASK-001" "$RALPH_DIR" || result=$?

    assert_equals "0" "$result" "Should return 0 on successful merge"

    # Worker directory should be moved to history after successful merge
    local dir_exists="no"
    [ -d "$WORKER_DIR" ] && dir_exists="yes"
    assert_equals "no" "$dir_exists" "Worker directory should be removed from workers/"

    local history_dir
    history_dir="$RALPH_DIR/history/$(basename "$WORKER_DIR")"
    local history_exists="no"
    [ -d "$history_dir" ] && history_exists="yes"
    assert_equals "yes" "$history_exists" "Worker directory should be archived to history/"

    local workspace_in_history="no"
    [ -d "$history_dir/workspace" ] && workspace_in_history="yes"
    assert_equals "no" "$workspace_in_history" "Workspace should not be in archived history"
}

# =============================================================================
# _check_pipeline_results() Tests
# =============================================================================

# Helper: write a mock step result file
_write_step_result() {
    local worker_dir="$1"
    local step_id="$2"
    local gate_result="$3"

    mkdir -p "$worker_dir/results"
    local epoch
    epoch=$(date +%s)
    echo "{\"outputs\":{\"gate_result\":\"$gate_result\"}}" \
        > "$worker_dir/results/${epoch}-${step_id}-result.json"
}

test_pipeline_gate_blocks_test_fix() {
    _write_step_result "$WORKER_DIR" "test" "FIX"

    local result=0
    _check_pipeline_results "$WORKER_DIR" "TASK-001" || result=$?

    assert_equals "1" "$result" "Should block merge when test result is FIX"
}

test_pipeline_gate_blocks_test_fail() {
    _write_step_result "$WORKER_DIR" "test" "FAIL"

    local result=0
    _check_pipeline_results "$WORKER_DIR" "TASK-001" || result=$?

    assert_equals "1" "$result" "Should block merge when test result is FAIL"
}

test_pipeline_gate_blocks_validation_fail() {
    _write_step_result "$WORKER_DIR" "test" "PASS"
    _write_step_result "$WORKER_DIR" "validation" "FAIL"

    local result=0
    _check_pipeline_results "$WORKER_DIR" "TASK-001" || result=$?

    assert_equals "1" "$result" "Should block merge when validation result is FAIL"
}

test_pipeline_gate_allows_test_unknown() {
    # No result files at all — should allow merge
    local result=0
    _check_pipeline_results "$WORKER_DIR" "TASK-001" || result=$?

    assert_equals "0" "$result" "Should allow merge when no test result exists (UNKNOWN)"
}

test_pipeline_gate_allows_all_pass() {
    _write_step_result "$WORKER_DIR" "test" "PASS"
    _write_step_result "$WORKER_DIR" "validation" "PASS"

    local result=0
    _check_pipeline_results "$WORKER_DIR" "TASK-001" || result=$?

    assert_equals "0" "$result" "Should allow merge when all results are PASS"
}

# =============================================================================
# Run All Tests
# =============================================================================

# _wait_for_mergeable tests
run_test test_wait_for_mergeable_returns_0_when_mergeable
run_test test_wait_for_mergeable_returns_1_when_conflicting
run_test test_wait_for_mergeable_returns_2_on_timeout
run_test test_wait_for_mergeable_polls_until_determined
run_test test_wait_for_mergeable_returns_2_on_unexpected_status
run_test test_wait_for_mergeable_returns_2_on_gh_failure

# attempt_pr_merge retry tests
run_test test_not_mergeable_is_retryable
run_test test_not_mergeable_fails_permanently_at_max_attempts
run_test test_conflict_detected_by_poll_skips_merge_call
run_test test_successful_merge_after_poll

# _check_pipeline_results tests
run_test test_pipeline_gate_blocks_test_fix
run_test test_pipeline_gate_blocks_test_fail
run_test test_pipeline_gate_blocks_validation_fail
run_test test_pipeline_gate_allows_test_unknown
run_test test_pipeline_gate_allows_all_pass

print_test_summary
exit_with_test_result
