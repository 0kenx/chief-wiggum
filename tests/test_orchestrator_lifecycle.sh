#!/usr/bin/env bash
# Test suite for orchestrator lifecycle modules
# Tests: arg-parser.sh, migration.sh, lifecycle.sh

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
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# Test: arg-parser.sh - Default Values
# =============================================================================

test_parse_args_defaults() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    # Set defaults that would normally be set in wiggum-run
    MAX_WORKERS=3
    MAX_ITERATIONS=30
    MAX_TURNS=100
    WIGGUM_RUN_MODE="default"
    WIGGUM_PLAN_MODE=false
    WIGGUM_SMART_MODE=true
    WIGGUM_USE_PYTHON=true
    WIGGUM_NO_RESUME=false
    WIGGUM_NO_FIX=false
    WIGGUM_NO_MERGE=false
    WIGGUM_NO_SYNC=false
    FORCE_LOCK=false
    FIX_WORKER_LIMIT=1
    export WIGGUM_TASK_SOURCE_MODE="hybrid"

    # Parse no args - should keep defaults
    _parse_run_args

    assert_equals "3" "$MAX_WORKERS" "MAX_WORKERS default should be 3"
    assert_equals "30" "$MAX_ITERATIONS" "MAX_ITERATIONS default should be 30"
    assert_equals "100" "$MAX_TURNS" "MAX_TURNS default should be 100"
    assert_equals "true" "$WIGGUM_SMART_MODE" "WIGGUM_SMART_MODE default should be true"
    assert_equals "true" "$WIGGUM_USE_PYTHON" "WIGGUM_USE_PYTHON default should be true"
    assert_equals "default" "$WIGGUM_RUN_MODE" "WIGGUM_RUN_MODE default should be default"
    assert_equals "false" "$WIGGUM_PLAN_MODE" "WIGGUM_PLAN_MODE default should be false"
    assert_equals "hybrid" "$WIGGUM_TASK_SOURCE_MODE" "WIGGUM_TASK_SOURCE_MODE default should be hybrid"
}

# =============================================================================
# Test: arg-parser.sh - Plan Mode
# =============================================================================

test_parse_args_plan_mode() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    WIGGUM_RUN_MODE="default"
    WIGGUM_PLAN_MODE=false
    WIGGUM_SMART_MODE=true

    _parse_run_args plan

    assert_equals "true" "$WIGGUM_PLAN_MODE" "plan argument should set WIGGUM_PLAN_MODE=true"
    assert_equals "false" "$WIGGUM_SMART_MODE" "plan mode should disable smart mode"
}

test_parse_args_plan_flag() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    WIGGUM_RUN_MODE="default"
    WIGGUM_PLAN_MODE=false
    WIGGUM_SMART_MODE=true

    _parse_run_args --plan

    assert_equals "true" "$WIGGUM_PLAN_MODE" "--plan flag should set WIGGUM_PLAN_MODE=true"
    assert_equals "false" "$WIGGUM_SMART_MODE" "--plan should disable smart mode"
}

# =============================================================================
# Test: arg-parser.sh - Max Workers
# =============================================================================

test_parse_args_max_workers() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    MAX_WORKERS=3

    _parse_run_args --max-workers 5

    assert_equals "5" "$MAX_WORKERS" "--max-workers should set MAX_WORKERS"
}

# =============================================================================
# Test: arg-parser.sh - Max Iterations
# =============================================================================

test_parse_args_max_iters() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    MAX_ITERATIONS=30

    _parse_run_args --max-iters 10

    assert_equals "10" "$MAX_ITERATIONS" "--max-iters should set MAX_ITERATIONS"
}

# =============================================================================
# Test: arg-parser.sh - Max Turns
# =============================================================================

test_parse_args_max_turns() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    MAX_TURNS=100

    _parse_run_args --max-turns 20

    assert_equals "20" "$MAX_TURNS" "--max-turns should set MAX_TURNS"
}

# =============================================================================
# Test: arg-parser.sh - Pipeline
# =============================================================================

test_parse_args_pipeline() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    WIGGUM_SMART_MODE=true
    unset WIGGUM_PIPELINE

    _parse_run_args --pipeline fix

    assert_equals "fix" "$WIGGUM_PIPELINE" "--pipeline should export WIGGUM_PIPELINE"
    assert_equals "false" "$WIGGUM_SMART_MODE" "--pipeline should disable smart mode"
}

# =============================================================================
# Test: arg-parser.sh - Run Modes
# =============================================================================

test_parse_args_fix_only() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    WIGGUM_RUN_MODE="default"
    WIGGUM_PLAN_MODE=false
    WIGGUM_SMART_MODE=true

    _parse_run_args --fix-only

    assert_equals "fix-only" "$WIGGUM_RUN_MODE" "--fix-only should set WIGGUM_RUN_MODE"
    assert_equals "false" "$WIGGUM_SMART_MODE" "--fix-only should disable smart mode"
}

test_parse_args_merge_only() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    WIGGUM_RUN_MODE="default"
    WIGGUM_PLAN_MODE=false
    WIGGUM_SMART_MODE=true

    _parse_run_args --merge-only

    assert_equals "merge-only" "$WIGGUM_RUN_MODE" "--merge-only should set WIGGUM_RUN_MODE"
}

test_parse_args_resume_only() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    WIGGUM_RUN_MODE="default"
    WIGGUM_PLAN_MODE=false
    WIGGUM_SMART_MODE=true

    _parse_run_args --resume-only

    assert_equals "resume-only" "$WIGGUM_RUN_MODE" "--resume-only should set WIGGUM_RUN_MODE"
}

# =============================================================================
# Test: arg-parser.sh - No Flags
# =============================================================================

test_parse_args_no_resume() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    WIGGUM_NO_RESUME=false
    WIGGUM_RUN_MODE="default"
    WIGGUM_PLAN_MODE=false

    _parse_run_args --no-resume

    assert_equals "true" "$WIGGUM_NO_RESUME" "--no-resume should set WIGGUM_NO_RESUME=true"
}

test_parse_args_no_fix() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    WIGGUM_NO_FIX=false
    WIGGUM_RUN_MODE="default"
    WIGGUM_PLAN_MODE=false

    _parse_run_args --no-fix

    assert_equals "true" "$WIGGUM_NO_FIX" "--no-fix should set WIGGUM_NO_FIX=true"
}

test_parse_args_no_merge() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    WIGGUM_NO_MERGE=false
    WIGGUM_RUN_MODE="default"
    WIGGUM_PLAN_MODE=false

    _parse_run_args --no-merge

    assert_equals "true" "$WIGGUM_NO_MERGE" "--no-merge should set WIGGUM_NO_MERGE=true"
}

test_parse_args_no_sync() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    WIGGUM_NO_SYNC=false
    WIGGUM_RUN_MODE="default"
    WIGGUM_PLAN_MODE=false

    _parse_run_args --no-sync

    assert_equals "true" "$WIGGUM_NO_SYNC" "--no-sync should set WIGGUM_NO_SYNC=true"
}

test_parse_args_no_python() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    WIGGUM_USE_PYTHON=true
    WIGGUM_RUN_MODE="default"
    WIGGUM_PLAN_MODE=false

    _parse_run_args --no-python

    assert_equals "false" "$WIGGUM_USE_PYTHON" "--no-python should set WIGGUM_USE_PYTHON=false"
}

# =============================================================================
# Test: arg-parser.sh - Force Lock
# =============================================================================

test_parse_args_force() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    FORCE_LOCK=false
    WIGGUM_RUN_MODE="default"
    WIGGUM_PLAN_MODE=false

    _parse_run_args --force

    assert_equals "true" "$FORCE_LOCK" "--force should set FORCE_LOCK=true"
}

# =============================================================================
# Test: arg-parser.sh - Task Source Mode
# =============================================================================

test_parse_args_mode_github() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    export WIGGUM_TASK_SOURCE_MODE="hybrid"

    _parse_run_args --mode github

    assert_equals "github" "$WIGGUM_TASK_SOURCE_MODE" "--mode github should set WIGGUM_TASK_SOURCE_MODE"
}

test_parse_args_mode_local() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    export WIGGUM_TASK_SOURCE_MODE="hybrid"

    _parse_run_args --mode local

    assert_equals "local" "$WIGGUM_TASK_SOURCE_MODE" "--mode local should set WIGGUM_TASK_SOURCE_MODE"
}

test_parse_args_mode_hybrid() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    export WIGGUM_TASK_SOURCE_MODE="local"

    _parse_run_args --mode hybrid

    assert_equals "hybrid" "$WIGGUM_TASK_SOURCE_MODE" "--mode hybrid should set WIGGUM_TASK_SOURCE_MODE"
}

# =============================================================================
# Test: arg-parser.sh - Server ID
# =============================================================================

test_parse_args_server_id() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    unset WIGGUM_SERVER_ID

    _parse_run_args --server-id myhost

    assert_equals "myhost" "$WIGGUM_SERVER_ID" "--server-id should export WIGGUM_SERVER_ID"
}

# =============================================================================
# Test: arg-parser.sh - Fix Agents Limit
# =============================================================================

test_parse_args_fix_agents() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    FIX_WORKER_LIMIT=1

    _parse_run_args --fix-agents 3

    assert_equals "3" "$FIX_WORKER_LIMIT" "--fix-agents should set FIX_WORKER_LIMIT"
}

# =============================================================================
# Test: arg-parser.sh - Smart Mode Disabling
# =============================================================================

test_parse_args_smart_disabled_by_pipeline() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    WIGGUM_SMART_MODE=true
    WIGGUM_RUN_MODE="default"
    WIGGUM_PLAN_MODE=false

    _parse_run_args --pipeline custom

    assert_equals "false" "$WIGGUM_SMART_MODE" "Smart mode should be disabled when pipeline is set"
}

test_parse_args_smart_disabled_by_run_mode() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/arg-parser.sh"

    WIGGUM_SMART_MODE=true
    WIGGUM_RUN_MODE="default"
    WIGGUM_PLAN_MODE=false
    WIGGUM_NO_FIX=false
    WIGGUM_NO_RESUME=false
    WIGGUM_NO_MERGE=false

    _parse_run_args --fix-only

    assert_equals "false" "$WIGGUM_SMART_MODE" "Smart mode should be disabled when run mode is not default"
}

# =============================================================================
# Test: migration.sh - Ensure Directories
# =============================================================================

test_ensure_orchestrator_dirs() {
    source "$WIGGUM_HOME/lib/orchestrator/migration.sh"

    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir"

    _ensure_orchestrator_dirs "$ralph_dir"

    assert_dir_exists "$ralph_dir/orchestrator" "Should create orchestrator directory"
    assert_dir_exists "$ralph_dir/services" "Should create services directory"
}

test_ensure_orchestrator_dirs_idempotent() {
    source "$WIGGUM_HOME/lib/orchestrator/migration.sh"

    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir/orchestrator"
    mkdir -p "$ralph_dir/services"

    # Call again - should succeed without errors
    _ensure_orchestrator_dirs "$ralph_dir"

    assert_dir_exists "$ralph_dir/orchestrator" "orchestrator directory should still exist"
    assert_dir_exists "$ralph_dir/services" "services directory should still exist"
}

# =============================================================================
# Test: migration.sh - Migrate Files
# =============================================================================

test_migrate_orchestrator_pid() {
    source "$WIGGUM_HOME/lib/orchestrator/migration.sh"

    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir"

    echo "12345" > "$ralph_dir/.orchestrator.pid"

    _migrate_ralph_layout "$ralph_dir"

    assert_file_exists "$ralph_dir/orchestrator/orchestrator.pid" "PID file should be migrated"
    assert_file_not_exists "$ralph_dir/.orchestrator.pid" "Old PID file should be removed"
    assert_file_contains "$ralph_dir/orchestrator/orchestrator.pid" "12345" "PID content should be preserved"
}

test_migrate_pool_pending() {
    source "$WIGGUM_HOME/lib/orchestrator/migration.sh"

    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir"

    echo "TASK-001" > "$ralph_dir/.pool-pending"

    _migrate_ralph_layout "$ralph_dir"

    assert_file_exists "$ralph_dir/orchestrator/pool-pending" "pool-pending should be migrated"
    assert_file_not_exists "$ralph_dir/.pool-pending" "Old pool-pending should be removed"
}

test_migrate_service_state() {
    source "$WIGGUM_HOME/lib/orchestrator/migration.sh"

    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir"

    echo '{"version": 1}' > "$ralph_dir/.service-state.json"

    _migrate_ralph_layout "$ralph_dir"

    assert_file_exists "$ralph_dir/services/state.json" "Service state should be migrated"
    assert_file_not_exists "$ralph_dir/.service-state.json" "Old service state should be removed"
    assert_file_contains "$ralph_dir/services/state.json" '"version": 1' "Service state content should be preserved"
}

test_migrate_heartbeat() {
    source "$WIGGUM_HOME/lib/orchestrator/migration.sh"

    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir"

    echo "1234567890" > "$ralph_dir/.heartbeat"

    _migrate_ralph_layout "$ralph_dir"

    assert_file_exists "$ralph_dir/services/heartbeat" "Heartbeat should be migrated"
    assert_file_not_exists "$ralph_dir/.heartbeat" "Old heartbeat should be removed"
}

test_migrate_idempotent_when_new_exists() {
    source "$WIGGUM_HOME/lib/orchestrator/migration.sh"

    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir/orchestrator"

    echo "old" > "$ralph_dir/.orchestrator.pid"
    echo "new" > "$ralph_dir/orchestrator/orchestrator.pid"

    _migrate_ralph_layout "$ralph_dir"

    assert_file_contains "$ralph_dir/orchestrator/orchestrator.pid" "new" "Should keep new file when both exist"
    assert_file_exists "$ralph_dir/.orchestrator.pid" "Should not remove old file if new exists"
}

test_migrate_noop_when_old_missing() {
    source "$WIGGUM_HOME/lib/orchestrator/migration.sh"

    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir"

    _migrate_ralph_layout "$ralph_dir"

    # Should succeed without errors even when no old files exist
    assert_dir_exists "$ralph_dir/orchestrator" "Should create orchestrator directory"
    assert_dir_exists "$ralph_dir/services" "Should create services directory"
}

# =============================================================================
# Test: lifecycle.sh - Validate Project
# =============================================================================

test_validate_project_success() {
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/lifecycle.sh"

    local ralph_dir="$TEST_DIR/.ralph"
    export RALPH_DIR="$ralph_dir"

    mkdir -p "$ralph_dir"
    touch "$ralph_dir/kanban.md"

    _validate_project
    local exit_code=$?

    assert_equals "0" "$exit_code" "Should return 0 when .ralph/ and kanban.md exist"
}

test_validate_project_missing_ralph() {
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/lifecycle.sh"

    local ralph_dir="$TEST_DIR/.ralph-missing"
    export RALPH_DIR="$ralph_dir"

    # Run in subshell to catch exit
    ( _validate_project ) 2>/dev/null
    local exit_code=$?

    assert_equals "$EXIT_RUN_NO_RALPH_DIR" "$exit_code" "Should exit with EXIT_RUN_NO_RALPH_DIR when .ralph/ missing"
}

test_validate_project_missing_kanban() {
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/lifecycle.sh"

    local ralph_dir="$TEST_DIR/.ralph"
    export RALPH_DIR="$ralph_dir"

    mkdir -p "$ralph_dir"
    # kanban.md deliberately missing

    # Run in subshell to catch exit
    ( _validate_project ) 2>/dev/null
    local exit_code=$?

    assert_equals "$EXIT_RUN_NO_KANBAN" "$exit_code" "Should exit with EXIT_RUN_NO_KANBAN when kanban.md missing"
}

# =============================================================================
# Test: lifecycle.sh - Lock Acquisition
# =============================================================================

test_acquire_lock_creates_pidfile() {
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/lifecycle.sh"

    local ralph_dir="$TEST_DIR/.ralph"
    export RALPH_DIR="$ralph_dir"

    mkdir -p "$ralph_dir/orchestrator"

    FORCE_LOCK=false
    _acquire_lock

    assert_file_exists "$ralph_dir/orchestrator/orchestrator.pid" "Should create PID file"
    assert_file_contains "$ralph_dir/orchestrator/orchestrator.pid" "$$" "PID file should contain current PID"
}

test_acquire_lock_cleans_stale_lock() {
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/lifecycle.sh"

    local ralph_dir="$TEST_DIR/.ralph"
    export RALPH_DIR="$ralph_dir"

    mkdir -p "$ralph_dir/orchestrator"

    # Create stale lock with non-existent PID
    echo "999999" > "$ralph_dir/orchestrator/orchestrator.pid"

    FORCE_LOCK=false
    _acquire_lock

    assert_file_exists "$ralph_dir/orchestrator/orchestrator.pid" "Should create new PID file"
    assert_file_contains "$ralph_dir/orchestrator/orchestrator.pid" "$$" "Should replace stale PID with current PID"
}

test_acquire_lock_with_force() {
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/lifecycle.sh"

    local ralph_dir="$TEST_DIR/.ralph"
    export RALPH_DIR="$ralph_dir"

    mkdir -p "$ralph_dir/orchestrator"

    # Create lock with current PID (simulating existing lock)
    echo "$$" > "$ralph_dir/orchestrator/orchestrator.pid"

    FORCE_LOCK=true
    _acquire_lock

    assert_file_exists "$ralph_dir/orchestrator/orchestrator.pid" "Should still have PID file after force"
    assert_file_contains "$ralph_dir/orchestrator/orchestrator.pid" "$$" "Should overwrite with current PID"
}

# =============================================================================
# Test: lifecycle.sh - Lock Release
# =============================================================================

test_release_lock() {
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"
    source "$WIGGUM_HOME/lib/orchestrator/lifecycle.sh"

    local ralph_dir="$TEST_DIR/.ralph"
    export RALPH_DIR="$ralph_dir"

    mkdir -p "$ralph_dir/orchestrator"
    echo "$$" > "$ralph_dir/orchestrator/orchestrator.pid"

    _release_lock

    assert_file_not_exists "$ralph_dir/orchestrator/orchestrator.pid" "Should remove PID file"
}

# =============================================================================
# Run All Tests
# =============================================================================

run_test test_parse_args_defaults
run_test test_parse_args_plan_mode
run_test test_parse_args_plan_flag
run_test test_parse_args_max_workers
run_test test_parse_args_max_iters
run_test test_parse_args_max_turns
run_test test_parse_args_pipeline
run_test test_parse_args_fix_only
run_test test_parse_args_merge_only
run_test test_parse_args_resume_only
run_test test_parse_args_no_resume
run_test test_parse_args_no_fix
run_test test_parse_args_no_merge
run_test test_parse_args_no_sync
run_test test_parse_args_no_python
run_test test_parse_args_force
run_test test_parse_args_mode_github
run_test test_parse_args_mode_local
run_test test_parse_args_mode_hybrid
run_test test_parse_args_server_id
run_test test_parse_args_fix_agents
run_test test_parse_args_smart_disabled_by_pipeline
run_test test_parse_args_smart_disabled_by_run_mode
run_test test_ensure_orchestrator_dirs
run_test test_ensure_orchestrator_dirs_idempotent
run_test test_migrate_orchestrator_pid
run_test test_migrate_pool_pending
run_test test_migrate_service_state
run_test test_migrate_heartbeat
run_test test_migrate_idempotent_when_new_exists
run_test test_migrate_noop_when_old_missing
run_test test_validate_project_success
run_test test_validate_project_missing_ralph
run_test test_validate_project_missing_kanban
run_test test_acquire_lock_creates_pidfile
run_test test_acquire_lock_cleans_stale_lock
run_test test_acquire_lock_with_force
run_test test_release_lock

print_test_summary
exit_with_test_result
