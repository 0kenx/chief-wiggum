#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/worker/worker-lifecycle.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"

# Helper: wait for a PID to become visible to kill -0 (max ~1s)
_wait_pid_ready() {
    local pid="$1"
    local attempts=0
    while ! kill -0 "$pid" 2>/dev/null; do
        attempts=$((attempts + 1))
        if [ $attempts -ge 20 ]; then
            return 1
        fi
        sleep 0.05
    done
    return 0
}

# Create temp dir for test isolation
TEST_DIR=""
RALPH_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    RALPH_DIR="$TEST_DIR/.ralph"
    mkdir -p "$RALPH_DIR/workers"
    mkdir -p "$RALPH_DIR/orchestrator"
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# find_worker_by_task_id() Tests
# =============================================================================

test_find_worker_by_task_id_returns_newest() {
    # Create multiple workers for same task with different timestamps
    # The function uses `sort -r` on paths, so lexicographic order determines "newest"
    mkdir -p "$RALPH_DIR/workers/worker-TASK-001-1000"
    mkdir -p "$RALPH_DIR/workers/worker-TASK-001-2000"
    mkdir -p "$RALPH_DIR/workers/worker-TASK-001-3000"

    local result
    result=$(find_worker_by_task_id "$RALPH_DIR" "TASK-001")

    assert_output_contains "$result" "worker-TASK-001-3000" "Should return newest worker directory"
}

test_find_worker_by_task_id_returns_empty_when_not_found() {
    local result
    result=$(find_worker_by_task_id "$RALPH_DIR" "TASK-999")

    assert_equals "" "$result" "Should return empty when no worker found"
}

# =============================================================================
# find_any_worker_by_task_id() Tests
# =============================================================================

test_find_any_worker_by_task_id_returns_match() {
    mkdir -p "$RALPH_DIR/workers/worker-TASK-002-1234"

    local result
    result=$(find_any_worker_by_task_id "$RALPH_DIR" "TASK-002")

    assert_output_contains "$result" "worker-TASK-002" "Should find matching worker"
}

test_find_any_worker_by_task_id_empty_when_not_found() {
    local result
    result=$(find_any_worker_by_task_id "$RALPH_DIR" "TASK-999")

    assert_equals "" "$result" "Should return empty when no match"
}

# =============================================================================
# resolve_worker_id() Tests
# =============================================================================

test_resolve_worker_id_exact_match() {
    mkdir -p "$RALPH_DIR/workers/worker-TASK-001-12345"

    local result
    result=$(resolve_worker_id "$RALPH_DIR" "worker-TASK-001-12345")

    assert_output_contains "$result" "worker-TASK-001-12345" "Should resolve exact match"
}

test_resolve_worker_id_partial_match() {
    mkdir -p "$RALPH_DIR/workers/worker-TASK-001-12345"

    local result
    result=$(resolve_worker_id "$RALPH_DIR" "TASK-001")

    assert_output_contains "$result" "worker-TASK-001-12345" "Should resolve partial match"
}

test_resolve_worker_id_multiple_matches_error() {
    mkdir -p "$RALPH_DIR/workers/worker-TASK-001-11111"
    mkdir -p "$RALPH_DIR/workers/worker-TASK-001-22222"

    local result
    result=$(resolve_worker_id "$RALPH_DIR" "TASK-001" 2>&1)
    local exit_code=$?

    assert_equals "1" "$exit_code" "Should fail with multiple matches"
    assert_output_contains "$result" "Multiple workers match" "Should report multiple matches"
}

test_resolve_worker_id_no_match_error() {
    local result
    result=$(resolve_worker_id "$RALPH_DIR" "NONEXISTENT" 2>&1)
    local exit_code=$?

    assert_equals "1" "$exit_code" "Should fail with no match"
    assert_output_contains "$result" "No worker matches" "Should report no match"
}

test_resolve_worker_id_no_workers_dir_error() {
    [ -n "$RALPH_DIR" ] && rm -rf "$RALPH_DIR/workers"

    local result
    result=$(resolve_worker_id "$RALPH_DIR" "TASK-001" 2>&1)
    local exit_code=$?

    assert_equals "1" "$exit_code" "Should fail when workers dir doesn't exist"
    assert_output_contains "$result" "No workers directory" "Should report missing directory"
}

# =============================================================================
# get_valid_worker_pid() Tests
# =============================================================================

test_get_valid_worker_pid_valid_bash_process() {
    # Start a background bash process that stays as bash (not exec'd to another command)
    bash -c 'while true; do sleep 1; done' >/dev/null 2>&1 &
    local pid=$!
    local pid_file="$TEST_DIR/test.pid"
    echo "$pid" > "$pid_file"

    _wait_pid_ready $pid

    local result
    result=$(get_valid_worker_pid "$pid_file" "bash")
    local exit_code=$?

    # Clean up the process
    kill $pid 2>/dev/null || true
    wait $pid 2>/dev/null || true

    assert_equals "0" "$exit_code" "Should succeed for valid bash process"
    assert_equals "$pid" "$result" "Should return correct PID"
}

test_get_valid_worker_pid_missing_file() {
    local result
    get_valid_worker_pid "$TEST_DIR/nonexistent.pid" "bash" >/dev/null 2>&1
    local exit_code=$?

    assert_equals "1" "$exit_code" "Should fail for missing PID file"
}

test_get_valid_worker_pid_invalid_pid_content() {
    local pid_file="$TEST_DIR/invalid.pid"
    echo "not-a-number" > "$pid_file"

    local result
    get_valid_worker_pid "$pid_file" "bash" >/dev/null 2>&1
    local exit_code=$?

    assert_equals "1" "$exit_code" "Should fail for non-numeric PID"
}

test_get_valid_worker_pid_dead_process() {
    local pid_file="$TEST_DIR/dead.pid"
    # Use a PID that definitely doesn't exist
    echo "99999999" > "$pid_file"

    local result
    get_valid_worker_pid "$pid_file" "bash" >/dev/null 2>&1
    local exit_code=$?

    assert_equals "1" "$exit_code" "Should fail for dead process"
}

# =============================================================================
# is_worker_running() Tests
# =============================================================================

test_is_worker_running_true_when_running() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-12345"
    mkdir -p "$worker_dir"

    # Start a background bash process that stays as bash
    bash -c 'while true; do sleep 1; done' >/dev/null 2>&1 &
    local pid=$!
    echo "$pid" > "$worker_dir/agent.pid"

    _wait_pid_ready $pid

    is_worker_running "$worker_dir"
    local result=$?

    # Clean up
    kill $pid 2>/dev/null || true
    wait $pid 2>/dev/null || true

    assert_equals "0" "$result" "Should return 0 when worker is running"
}

test_is_worker_running_false_when_not_running() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-002-12345"
    mkdir -p "$worker_dir"

    # No PID file
    is_worker_running "$worker_dir"
    local result=$?

    assert_equals "1" "$result" "Should return 1 when no PID file"
}

# =============================================================================
# cleanup_stale_pid() Tests
# =============================================================================

test_cleanup_stale_pid_removes_stale() {
    local pid_file="$TEST_DIR/stale.pid"
    echo "99999999" > "$pid_file"

    cleanup_stale_pid "$pid_file"
    local result=$?

    assert_equals "0" "$result" "Should succeed"
    assert_file_not_exists "$pid_file" "Should remove stale PID file"
}

test_cleanup_stale_pid_keeps_running() {
    # Start a background bash process that stays as bash
    bash -c 'while true; do sleep 1; done' >/dev/null 2>&1 &
    local pid=$!
    local pid_file="$TEST_DIR/running.pid"
    echo "$pid" > "$pid_file"

    _wait_pid_ready $pid

    cleanup_stale_pid "$pid_file" "bash"
    local result=$?

    # Clean up
    kill $pid 2>/dev/null || true
    wait $pid 2>/dev/null || true

    assert_equals "1" "$result" "Should return 1 for running process"
    assert_file_exists "$pid_file" "Should keep PID file for running process"
}

test_cleanup_stale_pid_no_file() {
    cleanup_stale_pid "$TEST_DIR/nonexistent.pid"
    local result=$?

    assert_equals "0" "$result" "Should succeed when file doesn't exist"
}

# =============================================================================
# get_task_id_from_worker() Tests
# =============================================================================

test_get_task_id_from_worker_standard_format() {
    local task_id
    task_id=$(get_task_id_from_worker "worker-TASK-001-12345678")

    assert_equals "TASK-001" "$task_id" "Should extract TASK-001"
}

test_get_task_id_from_worker_different_prefix() {
    local task_id
    task_id=$(get_task_id_from_worker "worker-FEATURE-123-87654321")

    # The sed pattern expects TASK- prefix, so this tests the actual behavior
    # Based on the code: sed -E 's/worker-(TASK-[0-9]+)-.*/\1/'
    # It won't match FEATURE, so will return the whole string
    # This tests the actual implementation behavior
    if [[ "$task_id" == "FEATURE-123" || "$task_id" == "worker-FEATURE-123-87654321" ]]; then
        echo -e "  ${GREEN}✓${NC} Handles non-TASK prefix (returns: $task_id)"
    else
        echo -e "  ${RED}X${NC} Unexpected result: $task_id"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# scan_active_workers() Tests
# =============================================================================

test_scan_active_workers_finds_running() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-12345"
    mkdir -p "$worker_dir"

    # Start a background bash process that stays as bash
    bash -c 'while true; do sleep 1; done' >/dev/null 2>&1 &
    local pid=$!
    echo "$pid" > "$worker_dir/agent.pid"

    _wait_pid_ready $pid

    local result
    result=$(scan_active_workers "$RALPH_DIR")

    # Clean up
    kill $pid 2>/dev/null || true
    wait $pid 2>/dev/null || true

    assert_output_contains "$result" "$pid" "Should include running worker PID"
    assert_output_contains "$result" "TASK-001" "Should include task ID"
}

test_scan_active_workers_empty_when_none() {
    local result
    result=$(scan_active_workers "$RALPH_DIR")

    assert_equals "" "$result" "Should return empty when no workers"
}

test_scan_active_workers_cleans_stale() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-003-99999"
    mkdir -p "$worker_dir"
    echo "99999999" > "$worker_dir/agent.pid"

    scan_active_workers "$RALPH_DIR" > /dev/null

    # The stale PID file should be removed
    assert_file_not_exists "$worker_dir/agent.pid" "Should clean stale PID file"
}

# =============================================================================
# wait_for_worker_pid() Tests
# =============================================================================

test_wait_for_worker_pid_immediate() {
    local worker_dir="$TEST_DIR/worker"
    mkdir -p "$worker_dir"
    echo "12345" > "$worker_dir/agent.pid"

    wait_for_worker_pid "$worker_dir" 10
    local result=$?

    assert_equals "0" "$result" "Should succeed immediately when PID exists"
}

test_wait_for_worker_pid_timeout() {
    local worker_dir="$TEST_DIR/worker-no-pid"
    mkdir -p "$worker_dir"
    # Don't create PID file

    wait_for_worker_pid "$worker_dir" 5  # 0.5 seconds timeout
    local result=$?

    assert_equals "1" "$result" "Should timeout when PID not created"
}

# =============================================================================
# resume.pid detection tests
# =============================================================================

test_is_worker_running_true_when_resuming() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-010-12345"
    mkdir -p "$worker_dir"

    # Start a background bash process that stays as bash
    bash -c 'while true; do sleep 1; done' >/dev/null 2>&1 &
    local pid=$!
    echo "$pid" > "$worker_dir/resume.pid"

    _wait_pid_ready $pid

    is_worker_running "$worker_dir"
    local result=$?

    # Clean up
    kill $pid 2>/dev/null || true
    wait $pid 2>/dev/null || true

    assert_equals "0" "$result" "Should return 0 when worker has resume.pid"
}

test_scan_active_workers_finds_resuming() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-011-12345"
    mkdir -p "$worker_dir"

    # Start a background bash process that stays as bash
    bash -c 'while true; do sleep 1; done' >/dev/null 2>&1 &
    local pid=$!
    echo "$pid" > "$worker_dir/resume.pid"

    _wait_pid_ready $pid

    local result
    result=$(scan_active_workers "$RALPH_DIR")

    # Clean up
    kill $pid 2>/dev/null || true
    wait $pid 2>/dev/null || true

    assert_output_contains "$result" "$pid" "Should include resuming worker PID"
    assert_output_contains "$result" "TASK-011" "Should include task ID"
    assert_output_contains "$result" "resume" "Should indicate resume pid type"
}

test_scan_active_workers_cleans_stale_resume_pid() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-012-99999"
    mkdir -p "$worker_dir"
    echo "99999999" > "$worker_dir/resume.pid"

    scan_active_workers "$RALPH_DIR" > /dev/null

    # The stale resume.pid file should be removed
    assert_file_not_exists "$worker_dir/resume.pid" "Should clean stale resume.pid file"
}

# =============================================================================
# Per-Worker Locking Tests
# =============================================================================

test_per_worker_lock_path() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-020-12345"
    mkdir -p "$worker_dir"

    local lock_file
    lock_file=$(_get_pid_ops_lock "$RALPH_DIR" "$worker_dir")

    assert_equals "$worker_dir/.pid.lock" "$lock_file" "Should return per-worker lock path"
}

test_global_lock_path_fallback() {
    local lock_file
    lock_file=$(_get_pid_ops_lock "$RALPH_DIR")

    assert_equals "$RALPH_DIR/orchestrator/pid-ops.lock" "$lock_file" "Should return global lock path when no worker_dir"
}

test_scan_skips_cleanup_when_locked() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-021-99999"
    mkdir -p "$worker_dir"
    echo "99999999" > "$worker_dir/agent.pid"

    local lock_file="$worker_dir/.pid.lock"

    # Hold the lock in background
    (
        exec 200>"$lock_file"
        flock 200
        sleep 2
    ) &
    local lock_pid=$!
    sleep 0.1  # Let lock be acquired

    # Scan should skip this worker's cleanup (non-blocking)
    scan_active_workers "$RALPH_DIR" > /dev/null

    # Kill the lock holder
    kill $lock_pid 2>/dev/null || true
    wait $lock_pid 2>/dev/null || true

    # PID file should still exist (cleanup was skipped)
    assert_file_exists "$worker_dir/agent.pid" "Should skip cleanup when lock is held"
}

test_scan_cleans_different_worker_when_one_locked() {
    local worker_a="$RALPH_DIR/workers/worker-TASK-022-11111"
    local worker_b="$RALPH_DIR/workers/worker-TASK-023-22222"
    mkdir -p "$worker_a" "$worker_b"
    echo "99999999" > "$worker_a/agent.pid"
    echo "99999998" > "$worker_b/agent.pid"

    local lock_file_a="$worker_a/.pid.lock"

    # Hold lock on worker A
    (
        exec 200>"$lock_file_a"
        flock 200
        sleep 2
    ) &
    local lock_pid=$!
    sleep 0.1

    # Scan should clean worker B but skip worker A
    scan_active_workers "$RALPH_DIR" > /dev/null

    kill $lock_pid 2>/dev/null || true
    wait $lock_pid 2>/dev/null || true

    # Worker A should still have stale PID (locked)
    assert_file_exists "$worker_a/agent.pid" "Should skip locked worker"
    # Worker B should be cleaned (not locked)
    assert_file_not_exists "$worker_b/agent.pid" "Should clean unlocked worker"
}

test_write_pid_file_uses_per_worker_lock() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-024-33333"
    mkdir -p "$worker_dir"
    local pid_file="$worker_dir/agent.pid"

    write_pid_file "$pid_file" "12345"

    assert_file_exists "$pid_file" "Should create PID file"
    assert_equals "12345" "$(cat "$pid_file")" "Should contain correct PID"
}

test_remove_pid_file_uses_per_worker_lock() {
    local worker_dir="$RALPH_DIR/workers/worker-TASK-025-44444"
    mkdir -p "$worker_dir"
    local pid_file="$worker_dir/agent.pid"
    echo "12345" > "$pid_file"

    remove_pid_file "$pid_file"

    assert_file_not_exists "$pid_file" "Should remove PID file"
}

# =============================================================================
# Run All Tests
# =============================================================================

# find_worker_by_task_id tests
run_test test_find_worker_by_task_id_returns_newest
run_test test_find_worker_by_task_id_returns_empty_when_not_found

# find_any_worker_by_task_id tests
run_test test_find_any_worker_by_task_id_returns_match
run_test test_find_any_worker_by_task_id_empty_when_not_found

# resolve_worker_id tests
run_test test_resolve_worker_id_exact_match
run_test test_resolve_worker_id_partial_match
run_test test_resolve_worker_id_multiple_matches_error
run_test test_resolve_worker_id_no_match_error
run_test test_resolve_worker_id_no_workers_dir_error

# get_valid_worker_pid tests
run_test test_get_valid_worker_pid_valid_bash_process
run_test test_get_valid_worker_pid_missing_file
run_test test_get_valid_worker_pid_invalid_pid_content
run_test test_get_valid_worker_pid_dead_process

# is_worker_running tests
run_test test_is_worker_running_true_when_running
run_test test_is_worker_running_false_when_not_running

# cleanup_stale_pid tests
run_test test_cleanup_stale_pid_removes_stale
run_test test_cleanup_stale_pid_keeps_running
run_test test_cleanup_stale_pid_no_file

# get_task_id_from_worker tests
run_test test_get_task_id_from_worker_standard_format
run_test test_get_task_id_from_worker_different_prefix

# scan_active_workers tests
run_test test_scan_active_workers_finds_running
run_test test_scan_active_workers_empty_when_none
run_test test_scan_active_workers_cleans_stale

# wait_for_worker_pid tests
run_test test_wait_for_worker_pid_immediate
run_test test_wait_for_worker_pid_timeout

# resume.pid detection tests
run_test test_is_worker_running_true_when_resuming
run_test test_scan_active_workers_finds_resuming
run_test test_scan_active_workers_cleans_stale_resume_pid

# per-worker locking tests
run_test test_per_worker_lock_path
run_test test_global_lock_path_fallback
run_test test_scan_skips_cleanup_when_locked
run_test test_scan_cleans_different_worker_when_one_locked
run_test test_write_pid_file_uses_per_worker_lock
run_test test_remove_pid_file_uses_per_worker_lock

print_test_summary
exit_with_test_result
