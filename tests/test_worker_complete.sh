#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/worker/worker-complete.sh — worker self-completion module

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

# Source dependencies
source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"
source "$WIGGUM_HOME/lib/worker/git-state.sh"
source "$WIGGUM_HOME/lib/core/lifecycle-engine.sh"

# Suppress log output during tests
LOG_LEVEL=ERROR
export LOG_LEVEL

# Test isolation
TEST_DIR=""
WORKER_DIR=""
RALPH_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    RALPH_DIR="$TEST_DIR/project/.ralph"
    WORKER_DIR="$RALPH_DIR/workers/worker-TASK-001-12345"
    mkdir -p "$WORKER_DIR/results"
    mkdir -p "$RALPH_DIR"
    export RALPH_DIR

    # Create a minimal kanban for lifecycle effects
    cat > "$RALPH_DIR/kanban.md" << 'KANBAN'
## In Progress
- [=] **[TASK-001]** Test task
  - Description: A test task
  - Priority: HIGH
  - Dependencies: none
KANBAN

    # Reset lifecycle loader state
    _LC_LOADED=0
    _LIFECYCLE_LOADER_LOADED=""
    _LIFECYCLE_ENGINE_LOADED=""
    _LIFECYCLE_GUARDS_LOADED=""
    source "$WIGGUM_HOME/lib/core/lifecycle-loader.sh"
    source "$WIGGUM_HOME/lib/core/lifecycle-engine.sh"
    source "$WIGGUM_HOME/lib/core/lifecycle-guards.sh"
    lifecycle_load

    # Source module under test
    _WORKER_COMPLETE_LOADED=""
    source "$WIGGUM_HOME/lib/worker/worker-complete.sh"
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# worker_complete_fix() — Basic Transitions
# =============================================================================

test_fix_pass_transitions_to_needs_merge() {
    git_state_set "$WORKER_DIR" "fixing" "test" "Setup"

    # Create a pr-fix result with PASS + push_succeeded
    cat > "$WORKER_DIR/results/1000-pr-fix-result.json" << 'JSON'
{"outputs":{"gate_result":"PASS","push_succeeded":"true"}}
JSON

    worker_complete_fix "$WORKER_DIR" "TASK-001"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "needs_merge" "$state" "fix.pass should transition to needs_merge"
}

test_fix_fail_transitions_to_failed() {
    git_state_set "$WORKER_DIR" "fixing" "test" "Setup"

    # Stub effect that would fail in test env
    _check_permanent_failure() { return 0; }

    cat > "$WORKER_DIR/results/1000-pr-fix-result.json" << 'JSON'
{"outputs":{"gate_result":"FAIL","push_succeeded":"false"}}
JSON

    worker_complete_fix "$WORKER_DIR" "TASK-001"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "failed" "$state" "fix.fail should transition to failed"
}

test_fix_skip_transitions_to_needs_merge() {
    git_state_set "$WORKER_DIR" "fixing" "test" "Setup"

    cat > "$WORKER_DIR/results/1000-pr-fix-result.json" << 'JSON'
{"outputs":{"gate_result":"SKIP","push_succeeded":"false"}}
JSON

    worker_complete_fix "$WORKER_DIR" "TASK-001"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "needs_merge" "$state" "fix.skip should transition to needs_merge"
}

test_fix_partial_transitions_to_needs_fix() {
    git_state_set "$WORKER_DIR" "fixing" "test" "Setup"

    cat > "$WORKER_DIR/results/1000-pr-fix-result.json" << 'JSON'
{"outputs":{"gate_result":"FIX","push_succeeded":"true"}}
JSON

    worker_complete_fix "$WORKER_DIR" "TASK-001"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "needs_fix" "$state" "fix.partial should transition to needs_fix"
}

# =============================================================================
# worker_complete_fix() — Guard Behavior
# =============================================================================

test_skips_when_not_fixing() {
    git_state_set "$WORKER_DIR" "needs_merge" "test" "Setup"

    cat > "$WORKER_DIR/results/1000-pr-fix-result.json" << 'JSON'
{"outputs":{"gate_result":"PASS","push_succeeded":"true"}}
JSON

    worker_complete_fix "$WORKER_DIR" "TASK-001"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "needs_merge" "$state" "Should not change state when not in fixing"
}

test_skips_when_no_git_state() {
    # No git-state.json at all
    rm -f "$WORKER_DIR/git-state.json"

    cat > "$WORKER_DIR/results/1000-pr-fix-result.json" << 'JSON'
{"outputs":{"gate_result":"PASS","push_succeeded":"true"}}
JSON

    local result=0
    worker_complete_fix "$WORKER_DIR" "TASK-001" || result=$?
    assert_equals "0" "$result" "Should return 0 even with no git-state"
}

# =============================================================================
# worker_complete_fix() — No Results
# =============================================================================

test_no_results_emits_timeout() {
    git_state_set "$WORKER_DIR" "fixing" "test" "Setup"
    # No result files in results/

    worker_complete_fix "$WORKER_DIR" "TASK-001"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "needs_fix" "$state" "fix.timeout should transition to needs_fix"
}

# =============================================================================
# worker_complete_fix() — Result Priority (task-worker > test-run > pr-fix)
# =============================================================================

test_test_run_fail_overrides_pr_fix_pass() {
    git_state_set "$WORKER_DIR" "fixing" "test" "Setup"

    # Stub effect that would fail in test env
    _check_permanent_failure() { return 0; }

    # pr-fix says PASS (earlier step succeeded)
    cat > "$WORKER_DIR/results/1000-pr-fix-result.json" << 'JSON'
{"outputs":{"gate_result":"PASS","push_succeeded":"true"}}
JSON
    # test-run says FAIL (later step failed — should win)
    cat > "$WORKER_DIR/results/2000-test-run-result.json" << 'JSON'
{"outputs":{"gate_result":"FAIL"}}
JSON

    worker_complete_fix "$WORKER_DIR" "TASK-001"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "failed" "$state" "test-run FAIL should override pr-fix PASS"
}

test_task_worker_result_overrides_all() {
    git_state_set "$WORKER_DIR" "fixing" "test" "Setup"

    # pr-fix says PASS
    cat > "$WORKER_DIR/results/1000-pr-fix-result.json" << 'JSON'
{"outputs":{"gate_result":"PASS","push_succeeded":"true"}}
JSON
    # test-run says FAIL
    cat > "$WORKER_DIR/results/2000-test-run-result.json" << 'JSON'
{"outputs":{"gate_result":"FAIL"}}
JSON
    # task-worker says FIX (pipeline-level outcome — should win over all)
    cat > "$WORKER_DIR/results/3000-system.task-worker-result.json" << 'JSON'
{"outputs":{"gate_result":"FIX"}}
JSON

    worker_complete_fix "$WORKER_DIR" "TASK-001"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "needs_fix" "$state" "task-worker FIX should override test-run FAIL and pr-fix PASS"
}

test_push_succeeded_from_pr_fix_when_task_worker_selected() {
    git_state_set "$WORKER_DIR" "fixing" "test" "Setup"

    # pr-fix has push_succeeded=true
    cat > "$WORKER_DIR/results/1000-pr-fix-result.json" << 'JSON'
{"outputs":{"gate_result":"PASS","push_succeeded":"true"}}
JSON
    # task-worker is selected (no push_succeeded field)
    cat > "$WORKER_DIR/results/3000-system.task-worker-result.json" << 'JSON'
{"outputs":{"gate_result":"PASS"}}
JSON

    worker_complete_fix "$WORKER_DIR" "TASK-001"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "needs_merge" "$state" "Should find push_succeeded from pr-fix even when task-worker is primary"
}

# =============================================================================
# worker_complete_fix() — Generic Result Fallback
# =============================================================================

test_generic_result_file_fallback() {
    git_state_set "$WORKER_DIR" "fixing" "test" "Setup"

    # No pr-fix-result, but a generic result with gate_result
    cat > "$WORKER_DIR/results/1000-generic-result.json" << 'JSON'
{"outputs":{"gate_result":"PASS","push_succeeded":"true"}}
JSON

    worker_complete_fix "$WORKER_DIR" "TASK-001"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "needs_merge" "$state" "Should fallback to generic result file"
}

# =============================================================================
# worker_complete_fix() — Commit-Push Fallback
# =============================================================================

test_push_succeeded_from_commit_push_result() {
    git_state_set "$WORKER_DIR" "fixing" "test" "Setup"

    # pr-fix says PASS but no push_succeeded
    cat > "$WORKER_DIR/results/1000-pr-fix-result.json" << 'JSON'
{"outputs":{"gate_result":"PASS"}}
JSON
    # commit-push result has push_status=success
    cat > "$WORKER_DIR/results/0999-commit-push-result.json" << 'JSON'
{"outputs":{"push_status":"success"}}
JSON

    worker_complete_fix "$WORKER_DIR" "TASK-001"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "needs_merge" "$state" "Should detect push success from commit-push result"
}

# =============================================================================
# _worker_has_completion_results() — scheduler helper
# =============================================================================

test_has_completion_results_with_commit_push() {
    source "$WIGGUM_HOME/lib/scheduler/scheduler.sh" 2>/dev/null || true

    cat > "$WORKER_DIR/results/1000-commit-push-result.json" << 'JSON'
{"outputs":{"push_status":"success"}}
JSON

    assert_success "Should detect commit-push-result.json" \
        _worker_has_completion_results "$WORKER_DIR"
}

test_has_completion_results_with_pr_fix() {
    source "$WIGGUM_HOME/lib/scheduler/scheduler.sh" 2>/dev/null || true

    cat > "$WORKER_DIR/results/1000-pr-fix-result.json" << 'JSON'
{"outputs":{"gate_result":"PASS"}}
JSON

    assert_success "Should detect pr-fix-result.json" \
        _worker_has_completion_results "$WORKER_DIR"
}

test_has_no_completion_results_empty() {
    source "$WIGGUM_HOME/lib/scheduler/scheduler.sh" 2>/dev/null || true

    # Empty results dir
    assert_failure "Should not find completion results in empty dir" \
        _worker_has_completion_results "$WORKER_DIR"
}

test_has_no_completion_results_only_generic() {
    source "$WIGGUM_HOME/lib/scheduler/scheduler.sh" 2>/dev/null || true

    cat > "$WORKER_DIR/results/1000-execution-result.json" << 'JSON'
{"outputs":{"gate_result":"PASS"}}
JSON

    assert_failure "Should not match generic execution-result.json" \
        _worker_has_completion_results "$WORKER_DIR"
}

# =============================================================================
# Run All Tests
# =============================================================================

# Basic transition tests
run_test test_fix_pass_transitions_to_needs_merge
run_test test_fix_fail_transitions_to_failed
run_test test_fix_skip_transitions_to_needs_merge
run_test test_fix_partial_transitions_to_needs_fix

# Guard behavior
run_test test_skips_when_not_fixing
run_test test_skips_when_no_git_state

# No results
run_test test_no_results_emits_timeout

# Result priority
run_test test_test_run_fail_overrides_pr_fix_pass
run_test test_task_worker_result_overrides_all
run_test test_push_succeeded_from_pr_fix_when_task_worker_selected

# Result fallback
run_test test_generic_result_file_fallback
run_test test_push_succeeded_from_commit_push_result

# _worker_has_completion_results
run_test test_has_completion_results_with_commit_push
run_test test_has_completion_results_with_pr_fix
run_test test_has_no_completion_results_empty
run_test test_has_no_completion_results_only_generic

print_test_summary
exit_with_test_result
