#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/scheduler/scheduler.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

# Source dependencies first
source "$WIGGUM_HOME/lib/core/exit-codes.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"
source "$WIGGUM_HOME/lib/scheduler/scheduler.sh"

# Create temp dir for test isolation
TEST_DIR=""
RALPH_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    RALPH_DIR="$TEST_DIR/.ralph"
    mkdir -p "$RALPH_DIR/workers"
    mkdir -p "$RALPH_DIR/logs"
    mkdir -p "$RALPH_DIR/plans"
    mkdir -p "$RALPH_DIR/orchestrator"

    # Create minimal kanban file
    cat > "$RALPH_DIR/kanban.md" << 'EOF'
# Tasks

## Todo

- [ ] **[TASK-001]** First task
  - Description: Test task 1
  - Priority: HIGH
  - Dependencies: none

- [ ] **[TASK-002]** Second task
  - Description: Test task 2
  - Priority: MEDIUM
  - Dependencies: none

- [ ] **[TASK-003]** Third task
  - Description: Depends on first
  - Priority: LOW
  - Dependencies: TASK-001

## Done
EOF

    scheduler_init "$RALPH_DIR" "$TEST_DIR" 7 20000 15000 7000
}

teardown() {
    rm -rf "$TEST_DIR"
}

# =============================================================================
# scheduler_init() Tests
# =============================================================================

test_scheduler_init_sets_ralph_dir() {
    local ralph_dir
    ralph_dir=$(scheduler_get_ralph_dir)
    assert_equals "$RALPH_DIR" "$ralph_dir" "Ralph dir should be set correctly"
}

test_scheduler_init_creates_ready_since_file() {
    local ready_since
    ready_since=$(scheduler_get_ready_since_file)
    assert_file_exists "$ready_since" "Ready since file should exist"
}

test_scheduler_init_clears_pool() {
    # Add something to pool before init
    pool_add "9999" "main" "OLD-TASK"
    scheduler_init "$RALPH_DIR" "$TEST_DIR"

    local count
    count=$(pool_count)
    assert_equals "0" "$count" "Pool should be empty after init"
}

# =============================================================================
# scheduler_tick() Tests
# =============================================================================

test_scheduler_tick_populates_ready_tasks() {
    scheduler_tick

    assert_not_empty "$SCHED_READY_TASKS" "Ready tasks should not be empty"
}

test_scheduler_tick_finds_blocked_tasks() {
    scheduler_tick

    # TASK-003 depends on TASK-001 (not done), so should be blocked
    assert_output_contains "$SCHED_BLOCKED_TASKS" "TASK-003" "TASK-003 should be blocked"
}

test_scheduler_tick_initializes_event_flag() {
    # First tick populates task lists (triggers event due to list change)
    scheduler_tick

    # Second tick with no changes — flag should stay false
    SCHED_SCHEDULING_EVENT=true
    scheduler_tick

    assert_equals "false" "$SCHED_SCHEDULING_EVENT" "Event flag should be reset"
}

# =============================================================================
# scheduler_can_spawn_task() Tests
# =============================================================================

test_scheduler_can_spawn_when_empty() {
    scheduler_tick

    assert_success "Should be able to spawn with empty pool" \
        scheduler_can_spawn_task "TASK-001" 4
}

test_scheduler_cannot_spawn_at_capacity() {
    pool_add "1000" "main" "TASK-A"
    pool_add "1001" "main" "TASK-B"
    scheduler_tick

    assert_failure "Should fail at capacity" \
        scheduler_can_spawn_task "TASK-001" 2

    assert_equals "at_capacity" "$SCHED_SKIP_REASON" "Reason should be at_capacity"
}

# =============================================================================
# scheduler_detect_cycles() Tests
# =============================================================================

test_scheduler_detect_cycles_no_cycles() {
    # Our test kanban has no cycles
    assert_success "Should detect no cycles" scheduler_detect_cycles
}

test_scheduler_detect_cycles_self_dependency() {
    # Create kanban with self-dependency
    cat > "$RALPH_DIR/kanban.md" << 'EOF'
# Tasks

## Todo

- [ ] **[TASK-001]** Self-referencing task
  - Description: Bad task
  - Priority: HIGH
  - Dependencies: TASK-001

## Done
EOF

    scheduler_init "$RALPH_DIR" "$TEST_DIR"
    local result=0
    scheduler_detect_cycles 2>/dev/null || result=$?

    assert_equals "1" "$result" "Should detect self-dependency"
}

# =============================================================================
# scheduler_mark_event() Tests
# =============================================================================

test_scheduler_mark_event() {
    SCHED_SCHEDULING_EVENT=false
    scheduler_mark_event

    assert_equals "true" "$SCHED_SCHEDULING_EVENT" "Event flag should be set"
}

# =============================================================================
# scheduler_increment_skip() / scheduler_get_skip_count() Tests
# =============================================================================

test_scheduler_skip_count_starts_at_zero() {
    local count
    count=$(scheduler_get_skip_count "TASK-001")
    assert_equals "0" "$count" "Skip count should start at 0"
}

test_scheduler_increment_skip() {
    scheduler_increment_skip "TASK-001"

    local count
    count=$(scheduler_get_skip_count "TASK-001")
    assert_equals "1" "$count" "First skip should set count to 1"

    scheduler_increment_skip "TASK-001"
    count=$(scheduler_get_skip_count "TASK-001")
    assert_equals "2" "$count" "Second skip should double to 2"
}

# =============================================================================
# Skip cooldown self-decrement Tests
# =============================================================================

test_scheduler_skip_cooldown_decrements() {
    # Set skip count to 2 via two increments (1 -> 2)
    scheduler_increment_skip "TASK-001"
    scheduler_increment_skip "TASK-001"

    # scheduler_can_spawn_task should skip and decrement
    SCHED_SKIP_REASON=""
    scheduler_can_spawn_task "TASK-001" 10 || true

    local count
    count=$(scheduler_get_skip_count "TASK-001")
    assert_equals "1" "$count" "Skip count should decrement to 1 after check"
}

test_scheduler_skip_cooldown_removes_at_zero() {
    scheduler_increment_skip "TASK-001"

    # First check: decrements 1 -> 0, removes entry
    scheduler_can_spawn_task "TASK-001" 10 || true

    local count
    count=$(scheduler_get_skip_count "TASK-001")
    assert_equals "0" "$count" "Skip count should be 0 after decrementing from 1"
}

# =============================================================================
# scheduler_is_complete() Tests
# =============================================================================

test_scheduler_is_complete_false_with_pending() {
    scheduler_tick

    assert_failure "Should not be complete with pending tasks" scheduler_is_complete
}

test_scheduler_is_complete_false_with_workers() {
    # Mark all tasks as done
    cat > "$RALPH_DIR/kanban.md" << 'EOF'
# Tasks

## Done

- [x] **[TASK-001]** Done task
  - Description: Completed
  - Priority: HIGH
  - Dependencies: none
EOF

    scheduler_init "$RALPH_DIR" "$TEST_DIR"
    scheduler_tick
    pool_add "1234" "main" "TASK-002"

    assert_failure "Should not be complete with active workers" scheduler_is_complete
}

test_scheduler_is_complete_true() {
    # Mark all tasks as done
    cat > "$RALPH_DIR/kanban.md" << 'EOF'
# Tasks

## Done

- [x] **[TASK-001]** Done task
  - Description: Completed
  - Priority: HIGH
  - Dependencies: none
EOF

    scheduler_init "$RALPH_DIR" "$TEST_DIR"
    scheduler_tick

    assert_success "Should be complete with no pending and no workers" scheduler_is_complete
}

# =============================================================================
# scheduler_remove_from_aging() Tests
# =============================================================================

test_scheduler_remove_from_aging() {
    local ready_since
    ready_since=$(scheduler_get_ready_since_file)

    # Add task to ready-since file
    echo "TASK-001|5" >> "$ready_since"

    scheduler_remove_from_aging "TASK-001"

    if grep -q "TASK-001" "$ready_since" 2>/dev/null; then
        assert_failure "TASK-001 should be removed" false
    else
        assert_success "TASK-001 removed from aging file" true
    fi
}

# =============================================================================
# scheduler_get_*() Accessor Tests
# =============================================================================

test_scheduler_get_aging_factor() {
    local factor
    factor=$(scheduler_get_aging_factor)
    assert_equals "7" "$factor" "Aging factor should be 7"
}

test_scheduler_get_plan_bonus() {
    local bonus
    bonus=$(scheduler_get_plan_bonus)
    assert_equals "15000" "$bonus" "Plan bonus should be 15000"
}

test_scheduler_get_dep_bonus_per_task() {
    local bonus
    bonus=$(scheduler_get_dep_bonus_per_task)
    assert_equals "7000" "$bonus" "Dep bonus should be 7000"
}

# =============================================================================
# get_resumable_workers() Tests
# =============================================================================

# Helper: create a minimal resumable worker directory
# Args: worker_name (e.g., "worker-TASK-001-1234567890")
_create_resumable_worker() {
    local name="$1"
    local dir="$RALPH_DIR/workers/$name"
    mkdir -p "$dir/workspace"
    echo "test" > "$dir/prd.md"
}

test_get_resumable_workers_main_type() {
    _create_resumable_worker "worker-TASK-001-1234567890"

    local output
    output=$(get_resumable_workers "$RALPH_DIR")

    assert_output_contains "$output" "TASK-001" "Should find TASK-001"
    assert_output_contains "$output" "main" "Main worker should have type 'main'"
}

test_get_resumable_workers_fix_type_from_dirname() {
    _create_resumable_worker "worker-TASK-001-fix-1234567890"

    local output
    output=$(get_resumable_workers "$RALPH_DIR")

    assert_output_contains "$output" "TASK-001" "Should find TASK-001"
    assert_output_contains "$output" "fix" "Fix worker should have type 'fix'"
    # Must not contain 'main'
    local worker_type
    worker_type=$(echo "$output" | awk '{print $4}')
    assert_equals "fix" "$worker_type" "Worker type field should be 'fix'"
}

test_get_resumable_workers_resolve_type_from_dirname() {
    _create_resumable_worker "worker-TASK-002-resolve-1234567890"

    local output
    output=$(get_resumable_workers "$RALPH_DIR")

    assert_output_contains "$output" "TASK-002" "Should find TASK-002"
    local worker_type
    worker_type=$(echo "$output" | awk '{print $4}')
    assert_equals "resolve" "$worker_type" "Worker type field should be 'resolve'"
}

test_get_resumable_workers_fix_type_from_git_state() {
    _create_resumable_worker "worker-TASK-001-1234567890"
    echo '{"current_state": "needs_fix"}' > "$RALPH_DIR/workers/worker-TASK-001-1234567890/git-state.json"

    local output
    output=$(get_resumable_workers "$RALPH_DIR")

    local worker_type
    worker_type=$(echo "$output" | awk '{print $4}')
    assert_equals "fix" "$worker_type" "Worker with needs_fix git-state should be type 'fix'"
}

test_get_resumable_workers_resolve_type_from_git_state() {
    _create_resumable_worker "worker-TASK-001-1234567890"
    echo '{"current_state": "resolving"}' > "$RALPH_DIR/workers/worker-TASK-001-1234567890/git-state.json"

    local output
    output=$(get_resumable_workers "$RALPH_DIR")

    local worker_type
    worker_type=$(echo "$output" | awk '{print $4}')
    assert_equals "resolve" "$worker_type" "Worker with resolving git-state should be type 'resolve'"
}

test_get_resumable_workers_fix_type_from_pipeline_config() {
    _create_resumable_worker "worker-TASK-003-1234567890"
    echo '{"pipeline":{"name":"fix","source":"config/pipelines/fix.json"},"current":{"step_idx":0,"step_id":"pr-fix"},"steps":{}}' \
        > "$RALPH_DIR/workers/worker-TASK-003-1234567890/pipeline-config.json"

    local output
    output=$(get_resumable_workers "$RALPH_DIR")

    local worker_type
    worker_type=$(echo "$output" | awk '{print $4}')
    assert_equals "fix" "$worker_type" "Worker with fix pipeline config should be type 'fix'"
}

test_get_resumable_workers_resolve_type_from_pipeline_config() {
    _create_resumable_worker "worker-TASK-004-1234567890"
    echo '{"pipeline":{"name":"multi-pr-resolve","source":"config/pipelines/multi-pr-resolve.json"},"current":{"step_idx":0,"step_id":"resolve"},"steps":{}}' \
        > "$RALPH_DIR/workers/worker-TASK-004-1234567890/pipeline-config.json"

    local output
    output=$(get_resumable_workers "$RALPH_DIR")

    local worker_type
    worker_type=$(echo "$output" | awk '{print $4}')
    assert_equals "resolve" "$worker_type" "Worker with resolve pipeline config should be type 'resolve'"
}

test_get_resumable_workers_output_has_four_fields() {
    _create_resumable_worker "worker-TASK-001-1234567890"

    local output
    output=$(get_resumable_workers "$RALPH_DIR")

    local field_count
    field_count=$(echo "$output" | awk '{print NF}')
    assert_equals "4" "$field_count" "Output should have 4 fields (worker_dir task_id step type)"
}

# =============================================================================
# Run Tests
# =============================================================================

run_test test_scheduler_init_sets_ralph_dir
run_test test_scheduler_init_creates_ready_since_file
run_test test_scheduler_init_clears_pool
run_test test_scheduler_tick_populates_ready_tasks
run_test test_scheduler_tick_finds_blocked_tasks
run_test test_scheduler_tick_initializes_event_flag
run_test test_scheduler_can_spawn_when_empty
run_test test_scheduler_cannot_spawn_at_capacity
run_test test_scheduler_detect_cycles_no_cycles
run_test test_scheduler_detect_cycles_self_dependency
run_test test_scheduler_mark_event
run_test test_scheduler_skip_count_starts_at_zero
run_test test_scheduler_increment_skip
run_test test_scheduler_skip_cooldown_decrements
run_test test_scheduler_skip_cooldown_removes_at_zero
run_test test_scheduler_is_complete_false_with_pending
run_test test_scheduler_is_complete_false_with_workers
run_test test_scheduler_is_complete_true
run_test test_scheduler_remove_from_aging
run_test test_scheduler_get_aging_factor
run_test test_scheduler_get_plan_bonus
run_test test_scheduler_get_dep_bonus_per_task
run_test test_get_resumable_workers_main_type
run_test test_get_resumable_workers_fix_type_from_dirname
run_test test_get_resumable_workers_resolve_type_from_dirname
run_test test_get_resumable_workers_fix_type_from_git_state
run_test test_get_resumable_workers_resolve_type_from_git_state
run_test test_get_resumable_workers_fix_type_from_pipeline_config
run_test test_get_resumable_workers_resolve_type_from_pipeline_config
run_test test_get_resumable_workers_output_has_four_fields

print_test_summary
exit_with_test_result
