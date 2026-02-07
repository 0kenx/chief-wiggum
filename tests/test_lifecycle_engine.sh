#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/core/lifecycle-loader.sh and lib/core/lifecycle-engine.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

# Source dependencies before lifecycle modules
source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"
source "$WIGGUM_HOME/lib/worker/git-state.sh"

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
    mkdir -p "$WORKER_DIR"
    mkdir -p "$RALPH_DIR"
    export RALPH_DIR

    # Create a minimal kanban for update_kanban_status tests
    cat > "$RALPH_DIR/kanban.md" << 'KANBAN'
## In Progress
- [=] **[TASK-001]** Test task
  - Description: A test task
  - Priority: HIGH
  - Dependencies: none
KANBAN

    # Initialize git-state for the worker
    git_state_set "$WORKER_DIR" "none" "test" "Initial state"

    # Reset loader state for each test
    _LC_LOADED=0

    # Source lifecycle modules fresh
    _LIFECYCLE_LOADER_LOADED=""
    _LIFECYCLE_ENGINE_LOADED=""
    _LIFECYCLE_GUARDS_LOADED=""
    source "$WIGGUM_HOME/lib/core/lifecycle-loader.sh"
    source "$WIGGUM_HOME/lib/core/lifecycle-engine.sh"
    source "$WIGGUM_HOME/lib/core/lifecycle-guards.sh"
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# Loader Tests
# =============================================================================

test_loader_reads_all_states() {
    lifecycle_load

    assert_equals "1" "${_LC_VALID_STATES[none]:-0}" "State 'none' should be valid"
    assert_equals "1" "${_LC_VALID_STATES[merged]:-0}" "State 'merged' should be valid"
    assert_equals "1" "${_LC_VALID_STATES[failed]:-0}" "State 'failed' should be valid"
    assert_equals "1" "${_LC_VALID_STATES[needs_fix]:-0}" "State 'needs_fix' should be valid"
    assert_equals "1" "${_LC_VALID_STATES[fixing]:-0}" "State 'fixing' should be valid"
    assert_equals "1" "${_LC_VALID_STATES[needs_merge]:-0}" "State 'needs_merge' should be valid"
    assert_equals "1" "${_LC_VALID_STATES[merging]:-0}" "State 'merging' should be valid"
    assert_equals "1" "${_LC_VALID_STATES[resolving]:-0}" "State 'resolving' should be valid"
}

test_loader_reads_state_types() {
    lifecycle_load

    assert_equals "initial" "$(lifecycle_state_type "none")" "none should be initial"
    assert_equals "terminal" "$(lifecycle_state_type "merged")" "merged should be terminal"
    assert_equals "terminal_recoverable" "$(lifecycle_state_type "failed")" "failed should be terminal_recoverable"
    assert_equals "waiting" "$(lifecycle_state_type "needs_fix")" "needs_fix should be waiting"
    assert_equals "running" "$(lifecycle_state_type "fixing")" "fixing should be running"
    assert_equals "transient" "$(lifecycle_state_type "fix_completed")" "fix_completed should be transient"
}

test_loader_reads_transitions() {
    lifecycle_load

    local count
    count=$(lifecycle_transition_count)
    assert_greater_than "$count" 30 "Should have >30 transitions"
}

test_loader_reads_guards() {
    lifecycle_load

    assert_not_empty "${_LC_GUARD_FN[merge_attempts_lt_max]:-}" "Should have merge_attempts_lt_max guard"
    assert_not_empty "${_LC_GUARD_FN[recovery_attempts_lt_max]:-}" "Should have recovery_attempts_lt_max guard"
    assert_not_empty "${_LC_GUARD_FN[rebase_succeeded]:-}" "Should have rebase_succeeded guard"
}

test_loader_reads_effects() {
    lifecycle_load

    assert_not_empty "${_LC_EFFECT_FN[set_error]:-}" "Should have set_error effect"
    assert_not_empty "${_LC_EFFECT_FN[inc_merge_attempts]:-}" "Should have inc_merge_attempts effect"
    assert_not_empty "${_LC_EFFECT_FN[sync_github]:-}" "Should have sync_github effect"
}

test_loader_fails_on_missing_file() {
    local result=0
    lifecycle_load "/nonexistent/file.json" 2>/dev/null || result=$?
    assert_equals "1" "$result" "Should fail when spec file is missing"
}

test_loader_is_loaded_flag() {
    assert_equals "0" "$_LC_LOADED" "Should not be loaded initially"

    lifecycle_load
    assert_equals "1" "$_LC_LOADED" "Should be loaded after lifecycle_load"
}

test_loader_is_valid_state() {
    lifecycle_load

    if lifecycle_is_valid_state "none"; then
        echo -e "  ${GREEN}✓${NC} 'none' is a valid state"
    else
        echo -e "  ${RED}✗${NC} 'none' should be a valid state"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    if lifecycle_is_valid_state "bogus_state"; then
        echo -e "  ${RED}✗${NC} 'bogus_state' should not be valid"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} 'bogus_state' is not a valid state"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# emit_event() - Basic Transitions
# =============================================================================

test_emit_event_basic_transition() {
    lifecycle_load

    # none -> needs_fix via fix.detected
    local result=0
    emit_event "$WORKER_DIR" "fix.detected" "test" '{}' || result=$?
    assert_equals "0" "$result" "fix.detected from none should succeed"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "needs_fix" "$state" "State should be needs_fix after fix.detected"
}

test_emit_event_chain_transition() {
    lifecycle_load

    # Set up: none -> needs_fix -> fixing
    git_state_set "$WORKER_DIR" "fixing" "test" "Setup"

    # Mock inc_merge_attempts as a side effect (it's real, tests against git-state.json)
    local result=0
    emit_event "$WORKER_DIR" "fix.pass" "test" '{}' || result=$?
    assert_equals "0" "$result" "fix.pass from fixing should succeed"

    # Should land on needs_merge (via chain through fix_completed)
    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "needs_merge" "$state" "State should be needs_merge after fix.pass (via chain)"

    # Verify chain state was recorded in transitions
    local chain_recorded
    chain_recorded=$(jq '[.transitions[] | select(.to == "fix_completed")] | length' "$WORKER_DIR/git-state.json")
    assert_greater_than "$chain_recorded" 0 "fix_completed chain state should appear in transitions"
}

test_emit_event_no_matching_transition() {
    lifecycle_load

    # Try an event that doesn't match the current state
    git_state_set "$WORKER_DIR" "merged" "test" "Setup"

    local result=0
    emit_event "$WORKER_DIR" "fix.detected" "test" '{}' 2>/dev/null || result=$?
    assert_equals "1" "$result" "Should return 1 when no matching transition"
}

test_emit_event_wildcard_transition() {
    lifecycle_load

    # resume.abort has from: "*" - should work from any state
    git_state_set "$WORKER_DIR" "fixing" "test" "Setup"

    local result=0
    emit_event "$WORKER_DIR" "resume.abort" "test" '{}' || result=$?
    assert_equals "0" "$result" "resume.abort with wildcard should match from any state"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "failed" "$state" "State should be failed after resume.abort"
}

test_emit_event_null_target() {
    lifecycle_load

    # resume.retry has to: null - should only update kanban, not git-state
    git_state_set "$WORKER_DIR" "failed" "test" "Setup"

    local result=0
    emit_event "$WORKER_DIR" "resume.retry" "test" '{}' || result=$?
    assert_equals "0" "$result" "resume.retry should succeed"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "failed" "$state" "State should remain failed (null target)"

    # Kanban should be updated to [=]
    local kanban_status
    kanban_status=$(grep -o '\[.\]' "$RALPH_DIR/kanban.md" | head -1 | tr -d '[]')
    assert_equals "=" "$kanban_status" "Kanban should be [=] after resume.retry"
}

# =============================================================================
# emit_event() - Guard Tests
# =============================================================================

test_emit_event_guard_passes() {
    lifecycle_load

    # merge.start from needs_merge with guard merge_attempts_lt_max
    git_state_set "$WORKER_DIR" "needs_merge" "test" "Setup"
    # merge_attempts = 0 (default) which is < 3 (MAX_MERGE_ATTEMPTS)

    local result=0
    emit_event "$WORKER_DIR" "merge.start" "test" '{}' || result=$?
    assert_equals "0" "$result" "merge.start should succeed when attempts < max"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "merging" "$state" "State should be merging when guard passes"
}

test_emit_event_guard_fails_uses_fallback() {
    lifecycle_load

    # Set merge_attempts >= MAX_MERGE_ATTEMPTS so guard fails
    git_state_set "$WORKER_DIR" "needs_merge" "test" "Setup"
    MAX_MERGE_ATTEMPTS=2
    git_state_inc_merge_attempts "$WORKER_DIR"
    git_state_inc_merge_attempts "$WORKER_DIR"

    # Stub _check_permanent_failure to prevent it from trying real kanban ops
    _check_permanent_failure() { return 0; }

    local result=0
    emit_event "$WORKER_DIR" "merge.start" "test" '{"kanban_file":"'"$RALPH_DIR/kanban.md"'"}' || result=$?
    assert_equals "0" "$result" "merge.start should still succeed via fallback"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "failed" "$state" "State should be failed when guard fails (fallback transition)"

    # Restore
    export MAX_MERGE_ATTEMPTS=3
}

# =============================================================================
# emit_event() - Kanban Update Tests
# =============================================================================

test_emit_event_kanban_complete() {
    lifecycle_load

    git_state_set "$WORKER_DIR" "merging" "test" "Setup"

    # Stub effects that would fail in test env
    github_issue_sync_task_status() { return 0; }
    _cleanup_batch_state() { return 0; }
    _cleanup_merged_pr_worktree() { return 0; }
    scheduler_release_task() { return 0; }

    local result=0
    emit_event "$WORKER_DIR" "merge.succeeded" "test" '{}' || result=$?
    assert_equals "0" "$result" "merge.succeeded should succeed"

    local state
    state=$(git_state_get "$WORKER_DIR")
    assert_equals "merged" "$state" "State should be merged"

    local kanban_status
    kanban_status=$(grep -o '\[.\]' "$RALPH_DIR/kanban.md" | head -1 | tr -d '[]')
    assert_equals "x" "$kanban_status" "Kanban should be [x] after merge.succeeded"
}

test_emit_event_kanban_failed() {
    lifecycle_load

    git_state_set "$WORKER_DIR" "fixing" "test" "Setup"

    # Stub check_permanent
    _check_permanent_failure() { return 0; }

    local result=0
    emit_event "$WORKER_DIR" "resume.abort" "test" '{}' || result=$?
    assert_equals "0" "$result" "resume.abort should succeed"

    local kanban_status
    kanban_status=$(grep -o '\[.\]' "$RALPH_DIR/kanban.md" | head -1 | tr -d '[]')
    assert_equals "*" "$kanban_status" "Kanban should be [*] after resume.abort"
}

# =============================================================================
# emit_event() - Effects Tests
# =============================================================================

test_emit_event_inc_merge_attempts_effect() {
    lifecycle_load

    git_state_set "$WORKER_DIR" "needs_merge" "test" "Setup"

    local before
    before=$(git_state_get_merge_attempts "$WORKER_DIR")
    assert_equals "0" "$before" "Merge attempts should start at 0"

    local result=0
    emit_event "$WORKER_DIR" "merge.start" "test" '{}' || result=$?
    assert_equals "0" "$result" "merge.start should succeed"

    local after
    after=$(git_state_get_merge_attempts "$WORKER_DIR")
    assert_equals "1" "$after" "Merge attempts should be 1 after merge.start effect"
}

test_emit_event_set_error_effect() {
    lifecycle_load

    git_state_set "$WORKER_DIR" "merging" "test" "Setup"

    # Stub conflict queue
    conflict_queue_add() { return 0; }

    local result=0
    emit_event "$WORKER_DIR" "merge.conflict" "test" '{"error":"CONFLICT in file.txt","pr_number":42,"affected_files":[]}' || result=$?
    assert_equals "0" "$result" "merge.conflict should succeed"

    local error
    error=$(git_state_get_error "$WORKER_DIR")
    assert_equals "CONFLICT in file.txt" "$error" "Error should be set by set_error effect"
}

# =============================================================================
# emit_event() - Event Log Tests
# =============================================================================

test_emit_event_writes_events_jsonl() {
    lifecycle_load

    emit_event "$WORKER_DIR" "fix.detected" "test-source" '{}' || true

    assert_file_exists "$WORKER_DIR/events.jsonl" "events.jsonl should be created"

    local event_name
    event_name=$(jq -r '.event' "$WORKER_DIR/events.jsonl" | head -1)
    assert_equals "fix.detected" "$event_name" "Event name should be recorded"

    local event_source
    event_source=$(jq -r '.source' "$WORKER_DIR/events.jsonl" | head -1)
    assert_equals "test-source" "$event_source" "Event source should be recorded"
}

# =============================================================================
# emit_event() - Full Flow Tests
# =============================================================================

test_full_fix_merge_flow() {
    lifecycle_load

    # Stub effects
    github_issue_sync_task_status() { return 0; }
    _cleanup_batch_state() { return 0; }
    _cleanup_merged_pr_worktree() { return 0; }
    scheduler_release_task() { return 0; }

    # none -> needs_fix
    emit_event "$WORKER_DIR" "fix.detected" "test" '{}' || true
    assert_equals "needs_fix" "$(git_state_get "$WORKER_DIR")" "Step 1: needs_fix"

    # needs_fix -> fixing
    emit_event "$WORKER_DIR" "fix.started" "test" '{}' || true
    assert_equals "fixing" "$(git_state_get "$WORKER_DIR")" "Step 2: fixing"

    # fixing -> needs_merge (via fix_completed chain)
    emit_event "$WORKER_DIR" "fix.pass" "test" '{}' || true
    assert_equals "needs_merge" "$(git_state_get "$WORKER_DIR")" "Step 3: needs_merge"

    # needs_merge -> merging
    emit_event "$WORKER_DIR" "merge.start" "test" '{}' || true
    assert_equals "merging" "$(git_state_get "$WORKER_DIR")" "Step 4: merging"

    # merging -> merged
    emit_event "$WORKER_DIR" "merge.succeeded" "test" '{}' || true
    assert_equals "merged" "$(git_state_get "$WORKER_DIR")" "Step 5: merged"
}

test_full_conflict_resolution_flow() {
    lifecycle_load

    # Stub effects
    conflict_queue_add() { return 0; }
    conflict_queue_remove() { return 0; }
    _check_permanent_failure() { return 0; }
    github_issue_sync_task_status() { return 0; }
    _cleanup_batch_state() { return 0; }
    _cleanup_merged_pr_worktree() { return 0; }
    scheduler_release_task() { return 0; }

    git_state_set "$WORKER_DIR" "merging" "test" "Setup"

    # merging -> merge_conflict
    emit_event "$WORKER_DIR" "merge.conflict" "test" '{"error":"conflict","pr_number":1,"affected_files":[]}' || true
    assert_equals "merge_conflict" "$(git_state_get "$WORKER_DIR")" "Step 1: merge_conflict"

    # merge_conflict -> needs_resolve (guard passes - attempts=0 < max=3)
    emit_event "$WORKER_DIR" "conflict.needs_resolve" "test" '{}' || true
    assert_equals "needs_resolve" "$(git_state_get "$WORKER_DIR")" "Step 2: needs_resolve"

    # needs_resolve -> resolving
    emit_event "$WORKER_DIR" "resolve.started" "test" '{}' || true
    assert_equals "resolving" "$(git_state_get "$WORKER_DIR")" "Step 3: resolving"

    # resolving -> needs_merge (via resolved chain)
    emit_event "$WORKER_DIR" "resolve.succeeded" "test" '{}' || true
    assert_equals "needs_merge" "$(git_state_get "$WORKER_DIR")" "Step 4: needs_merge"

    # needs_merge -> merging
    emit_event "$WORKER_DIR" "merge.start" "test" '{}' || true
    assert_equals "merging" "$(git_state_get "$WORKER_DIR")" "Step 5: merging"

    # merging -> merged
    emit_event "$WORKER_DIR" "merge.succeeded" "test" '{}' || true
    assert_equals "merged" "$(git_state_get "$WORKER_DIR")" "Step 6: merged"
}

test_recovery_flow() {
    lifecycle_load

    # Stub effects
    _check_permanent_failure() { return 0; }

    git_state_set "$WORKER_DIR" "failed" "test" "Setup"

    # failed -> needs_resolve (guard passes - recovery_attempts=0 < max=2)
    emit_event "$WORKER_DIR" "recovery.to_resolve" "test" '{}' || true
    assert_equals "needs_resolve" "$(git_state_get "$WORKER_DIR")" "Should recover to needs_resolve"

    local recovery
    recovery=$(git_state_get_recovery_attempts "$WORKER_DIR")
    assert_equals "1" "$recovery" "Recovery attempts should be incremented"
}

# =============================================================================
# Resolve Task ID Tests
# =============================================================================

test_resolve_task_id_from_worker_dir() {
    lifecycle_load

    local task_id
    task_id=$(_lifecycle_resolve_task_id "$WORKER_DIR" '{}')
    assert_equals "TASK-001" "$task_id" "Should parse task ID from worker dir name"
}

test_resolve_task_id_from_data_json() {
    lifecycle_load

    local task_id
    task_id=$(_lifecycle_resolve_task_id "$WORKER_DIR" '{"task_id":"FEAT-042"}')
    assert_equals "FEAT-042" "$task_id" "Should use task_id from data_json"
}

test_resolve_task_id_from_env() {
    lifecycle_load

    export WIGGUM_TASK_ID="ENV-099"
    local task_id
    task_id=$(_lifecycle_resolve_task_id "/tmp/some/random/path" '{}')
    assert_equals "ENV-099" "$task_id" "Should use WIGGUM_TASK_ID env var"
    unset WIGGUM_TASK_ID
}

# =============================================================================
# Resolve Ralph Dir Tests
# =============================================================================

test_resolve_ralph_dir_from_worker_dir() {
    lifecycle_load

    local ralph_dir
    ralph_dir=$(_lifecycle_resolve_ralph_dir "$WORKER_DIR" '{}')
    assert_equals "$RALPH_DIR" "$ralph_dir" "Should derive ralph_dir from worker_dir"
}

test_resolve_ralph_dir_from_env() {
    lifecycle_load

    # RALPH_DIR is already exported in setup()
    local ralph_dir
    ralph_dir=$(_lifecycle_resolve_ralph_dir "/tmp/some/random/dir" '{}')
    assert_equals "$RALPH_DIR" "$ralph_dir" "Should use RALPH_DIR env var"
}

# =============================================================================
# Run All Tests
# =============================================================================

# Loader tests
run_test test_loader_reads_all_states
run_test test_loader_reads_state_types
run_test test_loader_reads_transitions
run_test test_loader_reads_guards
run_test test_loader_reads_effects
run_test test_loader_fails_on_missing_file
run_test test_loader_is_loaded_flag
run_test test_loader_is_valid_state

# Basic transition tests
run_test test_emit_event_basic_transition
run_test test_emit_event_chain_transition
run_test test_emit_event_no_matching_transition
run_test test_emit_event_wildcard_transition
run_test test_emit_event_null_target

# Guard tests
run_test test_emit_event_guard_passes
run_test test_emit_event_guard_fails_uses_fallback

# Kanban tests
run_test test_emit_event_kanban_complete
run_test test_emit_event_kanban_failed

# Effect tests
run_test test_emit_event_inc_merge_attempts_effect
run_test test_emit_event_set_error_effect

# Event log tests
run_test test_emit_event_writes_events_jsonl

# Full flow tests
run_test test_full_fix_merge_flow
run_test test_full_conflict_resolution_flow
run_test test_recovery_flow

# Resolution tests
run_test test_resolve_task_id_from_worker_dir
run_test test_resolve_task_id_from_data_json
run_test test_resolve_task_id_from_env
run_test test_resolve_ralph_dir_from_worker_dir
run_test test_resolve_ralph_dir_from_env

print_test_summary
exit_with_test_result
