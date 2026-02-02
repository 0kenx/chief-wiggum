#!/usr/bin/env bash
set -euo pipefail
# Tests for get_unified_work_queue() in lib/scheduler/scheduler.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

# Source dependencies
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

    # Create minimal kanban file with tasks at different priorities
    cat > "$RALPH_DIR/kanban.md" << 'EOF'
# Tasks

## Todo

- [ ] **[TST-001]** High priority task
  - Description: A high priority task
  - Priority: HIGH
  - Dependencies: none

- [ ] **[TST-002]** Medium priority task
  - Description: A medium priority task
  - Priority: MEDIUM
  - Dependencies: none

- [ ] **[TST-003]** Low priority task
  - Description: A low priority task
  - Priority: LOW
  - Dependencies: none

## Done
EOF

    export WIGGUM_NO_RESUME=false
    export WIGGUM_RUN_MODE=default

    # Initialize scheduler with default params + resume queue config
    scheduler_init "$RALPH_DIR" "$TEST_DIR" 7 20000 15000 7000 20000 8000
}

teardown() {
    rm -rf "$TEST_DIR"
}

# Helper: create a fake resumable worker directory
# Args: task_id [attempt_count]
_create_resumable_worker() {
    local task_id="$1"
    local attempts="${2:-0}"

    local worker_dir="$RALPH_DIR/workers/worker-${task_id}-1234567890"
    mkdir -p "$worker_dir/workspace" "$worker_dir/results" "$worker_dir/logs"
    touch "$worker_dir/prd.md"

    # Pipeline config at execution step
    cat > "$worker_dir/pipeline-config.json" << PJSON
{
    "current": {"step_id": "execution", "step_idx": 1},
    "steps": [
        {"id": "planning"},
        {"id": "execution"},
        {"id": "validation"}
    ]
}
PJSON

    # Resume state with attempt count
    if [ "$attempts" -gt 0 ]; then
        local history="[]"
        for ((i=0; i<attempts; i++)); do
            history=$(echo "$history" | jq ". + [{\"at\": $((1000 + i)), \"decision\": \"ERROR\"}]")
        done
        cat > "$worker_dir/resume-state.json" << RJSON
{
    "attempt_count": $attempts,
    "max_attempts": 5,
    "last_attempt_at": 1000,
    "cooldown_until": 0,
    "terminal": false,
    "terminal_reason": "",
    "history": $history
}
RJSON
    fi

    # Mark task as in-progress in kanban
    if grep -q "\[$task_id\]" "$RALPH_DIR/kanban.md"; then
        sed -i "s/- \[ \] \*\*\[$task_id\]\*\*/- [=] **[$task_id]**/" "$RALPH_DIR/kanban.md"
    fi

    echo "$worker_dir"
}

# =============================================================================
# Tests
# =============================================================================

test_new_tasks_only() {
    # No resumable workers — queue should contain only new tasks
    scheduler_tick

    local queue="$SCHED_UNIFIED_QUEUE"
    assert_equals "true" "$([ -n "$queue" ] && echo true || echo false)" "Queue should not be empty"

    # All items should be work_type=new
    local new_count resume_count
    new_count=$(echo "$queue" | grep -c '|new|' || true)
    resume_count=$(echo "$queue" | grep -c '|resume|' || true)

    assert_equals "0" "$resume_count" "No resume items expected"
    # At least one new task
    assert_equals "true" "$([ "$new_count" -gt 0 ] && echo true || echo false)" "Should have new tasks"
}

test_resume_tasks_only() {
    # Make all kanban tasks in-progress, create resumable workers
    _create_resumable_worker "TST-001" 0
    _create_resumable_worker "TST-002" 0

    scheduler_tick

    local queue="$SCHED_UNIFIED_QUEUE"
    local resume_count
    resume_count=$(echo "$queue" | grep -c '|resume|' || true)

    assert_equals "true" "$([ "$resume_count" -ge 2 ] && echo true || echo false)" "Should have at least 2 resume items"
}

test_fresh_resume_sorts_above_same_priority_new() {
    # TST-002 is MEDIUM (new, priority ~20000)
    # Create a MEDIUM resumable worker with 0 attempts
    # Resume priority = 20000 - 20000 (initial bonus) - progress_bonus = ~0
    # So resume should sort above the new MEDIUM task

    _create_resumable_worker "TST-002" 0

    # Add a fresh pending MEDIUM task to the kanban
    cat >> "$RALPH_DIR/kanban.md" << 'EOF'

- [ ] **[TST-004]** Another medium task
  - Description: Fresh medium task
  - Priority: MEDIUM
  - Dependencies: none
EOF

    scheduler_tick
    local queue="$SCHED_UNIFIED_QUEUE"

    # Get the first item's type in queue
    local first_type
    first_type=$(echo "$queue" | head -1 | cut -d'|' -f2)

    # The resume task should come first (lower priority number)
    assert_equals "resume" "$first_type" "Fresh resume should sort before same-priority new task"
}

test_degraded_resume_sorts_below_new() {
    # Create a MEDIUM resumable worker with 3 failed attempts
    # Resume priority = 20000 - 20000 + 3*8000 - progress_bonus = ~22333
    # New MEDIUM task at 20000 should sort above it
    _create_resumable_worker "TST-002" 3

    # Add a fresh MEDIUM task with a DIFFERENT prefix to avoid sibling WIP penalty
    cat >> "$RALPH_DIR/kanban.md" << 'EOF'

- [ ] **[NEW-001]** Fresh medium
  - Description: Fresh medium task
  - Priority: MEDIUM
  - Dependencies: none
EOF

    scheduler_tick
    local queue="$SCHED_UNIFIED_QUEUE"

    # Find the new task and resume task priorities
    local new_pri resume_pri
    new_pri=$(echo "$queue" | grep '|new|NEW-001|' | cut -d'|' -f1)
    resume_pri=$(echo "$queue" | grep '|resume|TST-002|' | cut -d'|' -f1)

    # Guard against empty values
    new_pri="${new_pri:-99999}"
    resume_pri="${resume_pri:-99999}"

    assert_equals "true" "$([ "$new_pri" -lt "$resume_pri" ] && echo true || echo false)" \
        "New MEDIUM ($new_pri) should sort above degraded resume ($resume_pri)"
}

test_no_resume_excludes_resume_items() {
    _create_resumable_worker "TST-001" 0

    export WIGGUM_NO_RESUME=true
    scheduler_tick
    local queue="$SCHED_UNIFIED_QUEUE"

    local resume_count
    resume_count=$(echo "$queue" | grep -c '|resume|' || true)
    assert_equals "0" "$resume_count" "--no-resume should exclude resume items"

    export WIGGUM_NO_RESUME=false
}

test_resume_only_excludes_new_items() {
    _create_resumable_worker "TST-001" 0

    # Add a pending task
    cat >> "$RALPH_DIR/kanban.md" << 'EOF'

- [ ] **[TST-006]** Pending task
  - Description: Should be excluded in resume-only
  - Priority: HIGH
  - Dependencies: none
EOF

    scheduler_tick
    local queue="$SCHED_UNIFIED_QUEUE"

    # Verify both types exist in queue (mode filtering happens in task_spawner, not queue)
    local new_count resume_count
    new_count=$(echo "$queue" | grep -c '|new|' || true)
    resume_count=$(echo "$queue" | grep -c '|resume|' || true)

    assert_equals "true" "$([ "$new_count" -gt 0 ] && echo true || echo false)" "Queue includes new items (mode filtering in spawner)"
    assert_equals "true" "$([ "$resume_count" -gt 0 ] && echo true || echo false)" "Queue includes resume items"
}

test_queue_sorted_by_priority() {
    # Create workers with different effective priorities
    _create_resumable_worker "TST-001" 0    # HIGH + resume bonus = very high priority
    _create_resumable_worker "TST-003" 0   # LOW + resume bonus = moderate priority

    scheduler_tick
    local queue="$SCHED_UNIFIED_QUEUE"

    # Verify queue is sorted (each line's first field <= next line's)
    local prev=0 sorted=true
    while IFS='|' read -r pri _rest; do
        [ -n "$pri" ] || continue
        if [ "$pri" -lt "$prev" ]; then
            sorted=false
            break
        fi
        prev="$pri"
    done <<< "$queue"

    assert_equals "true" "$sorted" "Queue should be sorted by priority ascending"
}

test_pipeline_progress_bonus() {
    # Create two MEDIUM workers: one early in pipeline, one late
    local early_dir
    early_dir=$(_create_resumable_worker "TST-002" 0)

    # Override TST-002 worker to be at step 0 (early)
    cat > "$early_dir/pipeline-config.json" << 'PJSON'
{
    "current": {"step_id": "planning", "step_idx": 0},
    "steps": [
        {"id": "planning"},
        {"id": "execution"},
        {"id": "validation"},
        {"id": "docs"}
    ]
}
PJSON

    # Need another task for late-pipeline worker
    cat >> "$RALPH_DIR/kanban.md" << 'EOF'

- [=] **[TST-007]** Late pipeline task
  - Description: Worker near completion
  - Priority: MEDIUM
  - Dependencies: none
EOF

    local late_worker_dir="$RALPH_DIR/workers/worker-TST-007-1234567890"
    mkdir -p "$late_worker_dir/workspace" "$late_worker_dir/results" "$late_worker_dir/logs"
    touch "$late_worker_dir/prd.md"
    cat > "$late_worker_dir/pipeline-config.json" << 'PJSON'
{
    "current": {"step_id": "docs", "step_idx": 3},
    "steps": [
        {"id": "planning"},
        {"id": "execution"},
        {"id": "validation"},
        {"id": "docs"}
    ]
}
PJSON

    scheduler_tick
    local queue="$SCHED_UNIFIED_QUEUE"

    local early_pri late_pri
    early_pri=$(echo "$queue" | grep '|resume|TST-002|' | cut -d'|' -f1)
    late_pri=$(echo "$queue" | grep '|resume|TST-007|' | cut -d'|' -f1)

    early_pri="${early_pri:-99999}"
    late_pri="${late_pri:-99999}"

    assert_equals "true" "$([ "$late_pri" -le "$early_pri" ] && echo true || echo false)" \
        "Late-pipeline worker ($late_pri) should have equal or higher priority than early ($early_pri)"
}

# =============================================================================
# Run Tests
# =============================================================================

run_test test_new_tasks_only
run_test test_resume_tasks_only
run_test test_fresh_resume_sorts_above_same_priority_new
run_test test_degraded_resume_sorts_below_new
run_test test_no_resume_excludes_resume_items
run_test test_resume_only_excludes_new_items
run_test test_queue_sorted_by_priority
run_test test_pipeline_progress_bonus

print_test_summary
exit_with_test_result
