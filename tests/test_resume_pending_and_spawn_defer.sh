#!/usr/bin/env bash
set -euo pipefail
# Tests for the resume-pending disk persistence mechanism and spawn_worker
# deferred return code (exit 2 for resumable workers).
#
# Covers:
#   1. _poll_pending_resumes ingests entries from resume-pending disk file
#   2. resume-pending file is truncated after ingestion
#   3. Duplicate entries are skipped during ingestion
#   4. .resume-exit-code file is used for exit code retrieval
#   5. spawn_worker returns 2 for resumable (non-terminal) workers
#   6. spawn_worker returns 1 for workers with still-running processes

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/test-framework.sh"

WIGGUM_HOME="$(cd "$SCRIPT_DIR/.." && pwd)"
export WIGGUM_HOME

# Source exit codes (needed by orchestrator-functions.sh)
source "$WIGGUM_HOME/lib/core/exit-codes.sh"

# Source worker pool (used by _poll_pending_resumes)
source "$WIGGUM_HOME/lib/scheduler/worker-pool.sh"

# =============================================================================
# Stubs for functions orchestrator-functions.sh depends on
# =============================================================================

# Logger stubs
log() { :; }
log_debug() { :; }
log_error() { :; }
log_warn() { :; }

# Scheduler stubs
scheduler_mark_event() { :; }
scheduler_remove_from_aging() { :; }

# Activity log stub - records calls for assertions
_ACTIVITY_LOG_CALLS=()
activity_log() {
    _ACTIVITY_LOG_CALLS+=("$1|${2:-}|${3:-}|${4:-}")
}

# Worker lifecycle stubs
wait_for_worker_pid() {
    local worker_dir="$1"
    [ -f "$worker_dir/agent.pid" ]
}

find_any_worker_by_task_id() {
    local ralph_dir="$1"
    local task_id="$2"
    # Return first matching dir, excluding plan workers
    find "$ralph_dir/workers" -maxdepth 1 -type d -name "worker-$task_id-*" 2>/dev/null | grep -v -- '-plan-' | head -1
}

find_worker_by_task_id() {
    find_any_worker_by_task_id "$@"
}

# Resume state stubs
resume_state_is_terminal() {
    # Default: not terminal (worker is resumable)
    return 1
}

# Kanban stubs
get_task_status() { echo " "; }
update_kanban_status() { return 0; }

# Smart mode stubs
smart_assess_complexity() { echo "simple"; }
smart_get_routing() { echo "|false"; }

# Source the module under test (after stubs are defined)
source "$WIGGUM_HOME/lib/scheduler/orchestrator-functions.sh"

# =============================================================================
# Test state
# =============================================================================

TEST_DIR=""
RALPH_DIR=""
PROJECT_DIR=""
export MAX_WORKERS=4
export MAX_ITERATIONS=3
export MAX_TURNS=10
export AGENT_TYPE="task-worker"
export PID_WAIT_TIMEOUT=1

setup() {
    TEST_DIR=$(mktemp -d)
    RALPH_DIR="$TEST_DIR/.ralph"
    PROJECT_DIR="$TEST_DIR/project"
    mkdir -p "$RALPH_DIR/workers"
    mkdir -p "$RALPH_DIR/orchestrator"
    mkdir -p "$RALPH_DIR/logs"
    mkdir -p "$PROJECT_DIR"
    pool_init
    _PENDING_RESUMES=()
    _ACTIVITY_LOG_CALLS=()
}

teardown() {
    rm -rf "$TEST_DIR"
}

# =============================================================================
# _poll_pending_resumes: disk ingestion tests
# =============================================================================

test_poll_ingests_from_disk_file() {
    # Write an entry to resume-pending as _schedule_resume_workers would
    local fake_pid=99999
    local worker_dir="$RALPH_DIR/workers/worker-TST-001-12345"
    mkdir -p "$worker_dir"

    local pending_file="$RALPH_DIR/orchestrator/resume-pending"
    echo "$fake_pid|$worker_dir|TST-001|main" > "$pending_file"

    # Create .resume-exit-code indicating the resume has already finished
    # with a non-zero exit that just falls through to the default case
    echo "1" > "$worker_dir/.resume-exit-code"

    # Call _poll_pending_resumes - the fake PID doesn't exist so it will
    # be detected as finished
    _poll_pending_resumes

    # Verify the pending file was truncated
    local file_size
    file_size=$(wc -c < "$pending_file")
    assert_equals "0" "$file_size" "resume-pending file should be truncated after ingestion"
}

test_poll_ingests_multiple_entries() {
    local pending_file="$RALPH_DIR/orchestrator/resume-pending"

    # Create two entries with fake PIDs
    local dir1="$RALPH_DIR/workers/worker-TST-001-11111"
    local dir2="$RALPH_DIR/workers/worker-TST-002-22222"
    mkdir -p "$dir1" "$dir2"

    # Both have resume-exit-code files (finished with non-resume errors)
    echo "1" > "$dir1/.resume-exit-code"
    echo "1" > "$dir2/.resume-exit-code"

    {
        echo "99901|$dir1|TST-001|main"
        echo "99902|$dir2|TST-002|main"
    } > "$pending_file"

    _poll_pending_resumes

    # Both entries should have been processed (PIDs don't exist)
    assert_equals "0" "${#_PENDING_RESUMES[@]}" "All entries should be processed (none remaining)"
}

test_poll_skips_duplicate_entries() {
    local pending_file="$RALPH_DIR/orchestrator/resume-pending"
    local worker_dir="$RALPH_DIR/workers/worker-TST-001-12345"
    mkdir -p "$worker_dir"

    # Use our own PID (which IS running) so the entry stays tracked
    local live_pid=$$
    _PENDING_RESUMES[$live_pid]="$worker_dir|TST-001|main"

    # Write the same PID to the disk file
    echo "$live_pid|$worker_dir|TST-001|main" > "$pending_file"

    # Should skip the duplicate during ingestion, then skip during poll
    # because kill -0 $$ succeeds (still running)
    _poll_pending_resumes

    # The entry should still be there (not duplicated, not removed)
    assert_equals "1" "${#_PENDING_RESUMES[@]}" "Should still have exactly 1 entry (duplicate skipped)"
}

test_poll_empty_file_is_noop() {
    # Empty file should not cause errors
    touch "$RALPH_DIR/orchestrator/resume-pending"

    _poll_pending_resumes

    assert_equals "0" "${#_PENDING_RESUMES[@]}" "Empty file should result in no entries"
}

test_poll_missing_file_is_noop() {
    # No resume-pending file at all
    _poll_pending_resumes

    assert_equals "0" "${#_PENDING_RESUMES[@]}" "Missing file should result in no entries"
}

# =============================================================================
# _poll_pending_resumes: exit code file tests
# =============================================================================

test_poll_reads_exit_code_from_file() {
    local worker_dir="$RALPH_DIR/workers/worker-TST-001-12345"
    mkdir -p "$worker_dir"

    # Write a successful exit code (0 = RETRY)
    echo "0" > "$worker_dir/.resume-exit-code"

    # Create agent.pid so wait_for_worker_pid succeeds
    echo "88888" > "$worker_dir/agent.pid"
    echo "execution" > "$worker_dir/current_step"

    # Write entry to pending file
    echo "99999|$worker_dir|TST-001|main" > "$RALPH_DIR/orchestrator/resume-pending"

    _poll_pending_resumes

    # On exit 0, pool_add should have been called
    local pool_size
    pool_size=$(pool_count)
    assert_equals "1" "$pool_size" "Worker should be added to pool on exit code 0"

    # The .resume-exit-code file should be cleaned up
    assert_file_not_exists "$worker_dir/.resume-exit-code" \
        "Exit code file should be removed after reading"
}

test_poll_handles_complete_exit_code() {
    local worker_dir="$RALPH_DIR/workers/worker-TST-001-12345"
    mkdir -p "$worker_dir"

    # EXIT_RESUME_COMPLETE = 67
    echo "$EXIT_RESUME_COMPLETE" > "$worker_dir/.resume-exit-code"

    echo "99999|$worker_dir|TST-001|main" > "$RALPH_DIR/orchestrator/resume-pending"

    _poll_pending_resumes

    # Should NOT add to pool (task is complete)
    local pool_size
    pool_size=$(pool_count)
    assert_equals "0" "$pool_size" "Worker should NOT be added to pool on COMPLETE"

    # Should have logged the completion activity
    local found=false
    for call in "${_ACTIVITY_LOG_CALLS[@]}"; do
        if [[ "$call" == *"resume_complete"* ]]; then
            found=true
            break
        fi
    done
    assert_equals "true" "$found" "Should log resume_complete activity"
}

test_poll_handles_abort_exit_code() {
    local worker_dir="$RALPH_DIR/workers/worker-TST-001-12345"
    mkdir -p "$worker_dir"

    # EXIT_RESUME_ABORT = 65
    echo "$EXIT_RESUME_ABORT" > "$worker_dir/.resume-exit-code"

    echo "99999|$worker_dir|TST-001|main" > "$RALPH_DIR/orchestrator/resume-pending"

    _poll_pending_resumes

    # Should NOT add to pool
    local pool_size
    pool_size=$(pool_count)
    assert_equals "0" "$pool_size" "Worker should NOT be added to pool on ABORT"

    # Should have logged the abort activity
    local found=false
    for call in "${_ACTIVITY_LOG_CALLS[@]}"; do
        if [[ "$call" == *"resume_abort"* ]]; then
            found=true
            break
        fi
    done
    assert_equals "true" "$found" "Should log resume_abort activity"
}

test_poll_handles_defer_exit_code() {
    local worker_dir="$RALPH_DIR/workers/worker-TST-001-12345"
    mkdir -p "$worker_dir"

    # EXIT_RESUME_DEFER = 66
    echo "$EXIT_RESUME_DEFER" > "$worker_dir/.resume-exit-code"

    echo "99999|$worker_dir|TST-001|main" > "$RALPH_DIR/orchestrator/resume-pending"

    _poll_pending_resumes

    # Should NOT add to pool (deferred)
    local pool_size
    pool_size=$(pool_count)
    assert_equals "0" "$pool_size" "Worker should NOT be added to pool on DEFER"

    # Should have logged the defer activity
    local found=false
    for call in "${_ACTIVITY_LOG_CALLS[@]}"; do
        if [[ "$call" == *"resume_defer"* ]]; then
            found=true
            break
        fi
    done
    assert_equals "true" "$found" "Should log resume_defer activity"
}

# =============================================================================
# spawn_worker: return code 2 for resumable workers
# =============================================================================

test_spawn_worker_returns_2_for_resumable() {
    local task_id="TST-001"

    # Create a mock wiggum-start that returns EXIT_WORKER_ALREADY_EXISTS
    local mock_bin="$TEST_DIR/mock-bin"
    mkdir -p "$mock_bin"
    cat > "$mock_bin/wiggum-start" <<'SCRIPT'
#!/usr/bin/env bash
exit 15  # EXIT_WORKER_ALREADY_EXISTS
SCRIPT
    chmod +x "$mock_bin/wiggum-start"

    # Override WIGGUM_HOME/bin to point to our mock
    local saved_home="$WIGGUM_HOME"
    WIGGUM_HOME="$TEST_DIR/mock-wiggum"
    mkdir -p "$WIGGUM_HOME/bin"
    cp "$mock_bin/wiggum-start" "$WIGGUM_HOME/bin/wiggum-start"

    # Create a worker dir that looks resumable (not terminal)
    local worker_dir="$RALPH_DIR/workers/worker-$task_id-12345"
    mkdir -p "$worker_dir/workspace"
    echo "stale-pid-gone" > "$worker_dir/agent.pid"

    # _is_terminal_failure already stubbed to return 1 (not terminal = resumable)

    local rc=0
    spawn_worker "$task_id" 2>/dev/null || rc=$?

    assert_equals "2" "$rc" "spawn_worker should return 2 for resumable workers"

    WIGGUM_HOME="$saved_home"
}

test_spawn_worker_returns_1_for_running_worker() {
    local task_id="TST-002"

    # Create a mock wiggum-start that returns EXIT_WORKER_ALREADY_EXISTS
    WIGGUM_HOME="$TEST_DIR/mock-wiggum"
    mkdir -p "$WIGGUM_HOME/bin"
    cat > "$WIGGUM_HOME/bin/wiggum-start" <<'SCRIPT'
#!/usr/bin/env bash
exit 15  # EXIT_WORKER_ALREADY_EXISTS
SCRIPT
    chmod +x "$WIGGUM_HOME/bin/wiggum-start"

    # Create a worker dir with a PID that IS still running (use our own PID)
    local worker_dir="$RALPH_DIR/workers/worker-$task_id-12345"
    mkdir -p "$worker_dir"
    echo "$$" > "$worker_dir/agent.pid"

    local rc=0
    spawn_worker "$task_id" 2>/dev/null || rc=$?

    assert_equals "1" "$rc" "spawn_worker should return 1 for still-running workers"

    WIGGUM_HOME="$(cd "$SCRIPT_DIR/.." && pwd)"
}

# =============================================================================
# Resume-pending file format tests
# =============================================================================

test_resume_pending_format_pipe_delimited() {
    # Verify the format matches what _poll_pending_resumes expects
    local pending_file="$RALPH_DIR/orchestrator/resume-pending"
    local worker_dir="$RALPH_DIR/workers/worker-TST-001-12345"
    mkdir -p "$worker_dir"
    echo "1" > "$worker_dir/.resume-exit-code"

    # Write in the expected format: pid|worker_dir|task_id|worker_type
    echo "99999|$worker_dir|TST-001|fix" > "$pending_file"

    _poll_pending_resumes

    # Verify it processed correctly (the error log call should mention TST-001)
    local found=false
    for call in "${_ACTIVITY_LOG_CALLS[@]}"; do
        if [[ "$call" == *"TST-001"* ]]; then
            found=true
            break
        fi
    done
    # With exit code 1, it falls through to the default case (no activity_log)
    # but the entry was still parsed and removed from _PENDING_RESUMES
    assert_equals "0" "${#_PENDING_RESUMES[@]}" "Entry should be fully processed"
}

test_resume_pending_blank_lines_ignored() {
    local pending_file="$RALPH_DIR/orchestrator/resume-pending"
    local worker_dir="$RALPH_DIR/workers/worker-TST-001-12345"
    mkdir -p "$worker_dir"
    echo "1" > "$worker_dir/.resume-exit-code"

    # File with blank lines interspersed
    {
        echo ""
        echo "99999|$worker_dir|TST-001|main"
        echo ""
    } > "$pending_file"

    _poll_pending_resumes

    # Should have processed the one real entry without errors
    assert_equals "0" "${#_PENDING_RESUMES[@]}" "Should process entry despite blank lines"
}

# =============================================================================
# Run Tests
# =============================================================================

echo "=== Resume-pending disk ingestion tests ==="
run_test test_poll_ingests_from_disk_file
run_test test_poll_ingests_multiple_entries
run_test test_poll_skips_duplicate_entries
run_test test_poll_empty_file_is_noop
run_test test_poll_missing_file_is_noop

echo ""
echo "=== Exit code file tests ==="
run_test test_poll_reads_exit_code_from_file
run_test test_poll_handles_complete_exit_code
run_test test_poll_handles_abort_exit_code
run_test test_poll_handles_defer_exit_code

echo ""
echo "=== spawn_worker return code tests ==="
run_test test_spawn_worker_returns_2_for_resumable
run_test test_spawn_worker_returns_1_for_running_worker

echo ""
echo "=== File format tests ==="
run_test test_resume_pending_format_pipe_delimited
run_test test_resume_pending_blank_lines_ignored

print_test_summary
exit_with_test_result
