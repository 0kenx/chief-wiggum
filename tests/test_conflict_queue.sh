#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/scheduler/conflict-queue.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/scheduler/conflict-queue.sh"

# Create temp dir for test isolation
TEST_DIR=""
RALPH_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    RALPH_DIR="$TEST_DIR/.ralph"
    mkdir -p "$RALPH_DIR/workers"
}

teardown() {
    rm -rf "$TEST_DIR"
}

# =============================================================================
# conflict_queue_init() Tests
# =============================================================================

test_conflict_queue_init_creates_file() {
    conflict_queue_init "$RALPH_DIR"

    assert_file_exists "$RALPH_DIR/conflict-queue.json" "Queue file should exist"
}

test_conflict_queue_init_creates_valid_json() {
    conflict_queue_init "$RALPH_DIR"

    local content
    content=$(cat "$RALPH_DIR/conflict-queue.json")
    assert_output_contains "$content" '"queue":[]' "Should have empty queue"
    assert_output_contains "$content" '"batches":{}' "Should have empty batches"
}

test_conflict_queue_init_idempotent() {
    conflict_queue_init "$RALPH_DIR"
    conflict_queue_add "$RALPH_DIR" "TASK-001" "$RALPH_DIR/workers/worker-TASK-001" "42" '["src/api.ts"]'
    conflict_queue_init "$RALPH_DIR"

    # Should not overwrite existing data
    local content
    content=$(cat "$RALPH_DIR/conflict-queue.json")
    assert_output_contains "$content" "TASK-001" "Data should be preserved"
}

# =============================================================================
# conflict_queue_add() Tests
# =============================================================================

test_conflict_queue_add_success() {
    conflict_queue_init "$RALPH_DIR"
    conflict_queue_add "$RALPH_DIR" "TASK-001" "$RALPH_DIR/workers/worker-TASK-001" "42" '["src/api.ts"]'

    local content
    content=$(cat "$RALPH_DIR/conflict-queue.json")
    assert_output_contains "$content" "TASK-001" "Should contain task_id"
    assert_output_contains "$content" "42" "Should contain PR number"
}

test_conflict_queue_add_multiple_files() {
    conflict_queue_init "$RALPH_DIR"
    conflict_queue_add "$RALPH_DIR" "TASK-001" "$RALPH_DIR/workers/worker-TASK-001" "42" '["src/api.ts","src/types.ts"]'

    local count
    count=$(jq '.queue | length' "$RALPH_DIR/conflict-queue.json")
    assert_equals "1" "$count" "Queue should have 1 entry"
}

test_conflict_queue_add_prevents_duplicates() {
    conflict_queue_init "$RALPH_DIR"
    conflict_queue_add "$RALPH_DIR" "TASK-001" "$RALPH_DIR/workers/worker-TASK-001" "42" '["src/api.ts"]'
    conflict_queue_add "$RALPH_DIR" "TASK-001" "$RALPH_DIR/workers/worker-TASK-001" "42" '["src/api.ts"]'

    local count
    count=$(jq '.queue | length' "$RALPH_DIR/conflict-queue.json")
    assert_equals "1" "$count" "Should not add duplicates"
}

test_conflict_queue_add_multiple_tasks() {
    conflict_queue_init "$RALPH_DIR"
    conflict_queue_add "$RALPH_DIR" "TASK-001" "$RALPH_DIR/workers/worker-TASK-001" "42" '["src/api.ts"]'
    conflict_queue_add "$RALPH_DIR" "TASK-002" "$RALPH_DIR/workers/worker-TASK-002" "43" '["src/api.ts"]'

    local count
    count=$(jq '.queue | length' "$RALPH_DIR/conflict-queue.json")
    assert_equals "2" "$count" "Should have 2 entries"
}

# =============================================================================
# conflict_queue_remove() Tests
# =============================================================================

test_conflict_queue_remove_success() {
    conflict_queue_init "$RALPH_DIR"
    conflict_queue_add "$RALPH_DIR" "TASK-001" "$RALPH_DIR/workers/worker-TASK-001" "42" '["src/api.ts"]'
    conflict_queue_remove "$RALPH_DIR" "TASK-001"

    local count
    count=$(jq '.queue | length' "$RALPH_DIR/conflict-queue.json")
    assert_equals "0" "$count" "Queue should be empty after remove"
}

test_conflict_queue_remove_nonexistent_noop() {
    conflict_queue_init "$RALPH_DIR"
    conflict_queue_remove "$RALPH_DIR" "TASK-999"

    # Should not fail
    assert_success "Remove should succeed" true
}

# =============================================================================
# conflict_queue_group_related() Tests
# =============================================================================

test_conflict_queue_group_related_no_overlap() {
    conflict_queue_init "$RALPH_DIR"
    conflict_queue_add "$RALPH_DIR" "TASK-001" "$RALPH_DIR/workers/worker-TASK-001" "42" '["src/api.ts"]'
    conflict_queue_add "$RALPH_DIR" "TASK-002" "$RALPH_DIR/workers/worker-TASK-002" "43" '["src/utils.ts"]'

    local groups
    groups=$(conflict_queue_group_related "$RALPH_DIR")

    local count
    count=$(echo "$groups" | jq 'length')
    assert_equals "0" "$count" "No groups for non-overlapping files"
}

test_conflict_queue_group_related_with_overlap() {
    conflict_queue_init "$RALPH_DIR"
    conflict_queue_add "$RALPH_DIR" "TASK-001" "$RALPH_DIR/workers/worker-TASK-001" "42" '["src/api.ts"]'
    conflict_queue_add "$RALPH_DIR" "TASK-002" "$RALPH_DIR/workers/worker-TASK-002" "43" '["src/api.ts"]'

    local groups
    groups=$(conflict_queue_group_related "$RALPH_DIR")

    local count
    count=$(echo "$groups" | jq 'length')
    assert_equals "1" "$count" "Should have 1 group"

    local task_count
    task_count=$(echo "$groups" | jq '.[0].task_ids | length')
    assert_equals "2" "$task_count" "Group should have 2 tasks"
}

test_conflict_queue_group_related_single_task() {
    conflict_queue_init "$RALPH_DIR"
    conflict_queue_add "$RALPH_DIR" "TASK-001" "$RALPH_DIR/workers/worker-TASK-001" "42" '["src/api.ts"]'

    local groups
    groups=$(conflict_queue_group_related "$RALPH_DIR")

    local count
    count=$(echo "$groups" | jq 'length')
    assert_equals "0" "$count" "Single task should not form a group"
}

# =============================================================================
# conflict_queue_batch_ready() Tests
# =============================================================================

test_conflict_queue_batch_ready_false() {
    conflict_queue_init "$RALPH_DIR"
    conflict_queue_add "$RALPH_DIR" "TASK-001" "$RALPH_DIR/workers/worker-TASK-001" "42" '["src/api.ts"]'

    assert_failure "Should not be ready with single task" conflict_queue_batch_ready "$RALPH_DIR"
}

test_conflict_queue_batch_ready_true() {
    conflict_queue_init "$RALPH_DIR"
    conflict_queue_add "$RALPH_DIR" "TASK-001" "$RALPH_DIR/workers/worker-TASK-001" "42" '["src/api.ts"]'
    conflict_queue_add "$RALPH_DIR" "TASK-002" "$RALPH_DIR/workers/worker-TASK-002" "43" '["src/api.ts"]'

    assert_success "Should be ready with overlapping tasks" conflict_queue_batch_ready "$RALPH_DIR"
}

# =============================================================================
# conflict_queue_create_batch() Tests
# =============================================================================

test_conflict_queue_create_batch_creates_batch() {
    conflict_queue_init "$RALPH_DIR"
    conflict_queue_add "$RALPH_DIR" "TASK-001" "$RALPH_DIR/workers/worker-TASK-001" "42" '["src/api.ts"]'
    conflict_queue_add "$RALPH_DIR" "TASK-002" "$RALPH_DIR/workers/worker-TASK-002" "43" '["src/api.ts"]'

    local batch_id
    batch_id=$(conflict_queue_create_batch "$RALPH_DIR" '["TASK-001","TASK-002"]' | head -1)

    assert_not_empty "$batch_id" "Should return batch_id"
    assert_output_contains "$batch_id" "batch-" "Batch ID should have prefix"
}

test_conflict_queue_create_batch_marks_tasks() {
    conflict_queue_init "$RALPH_DIR"
    conflict_queue_add "$RALPH_DIR" "TASK-001" "$RALPH_DIR/workers/worker-TASK-001" "42" '["src/api.ts"]' 2>/dev/null
    conflict_queue_add "$RALPH_DIR" "TASK-002" "$RALPH_DIR/workers/worker-TASK-002" "43" '["src/api.ts"]' 2>/dev/null

    local batch_id
    # Use head -1 to capture only the batch_id, ignoring log output
    batch_id=$(conflict_queue_create_batch "$RALPH_DIR" '["TASK-001","TASK-002"]' 2>/dev/null | head -1)

    local task1_batch
    task1_batch=$(jq -r '.queue[] | select(.task_id == "TASK-001") | .batch_id' "$RALPH_DIR/conflict-queue.json")
    assert_equals "$batch_id" "$task1_batch" "Task 1 should be marked with batch_id"
}

# =============================================================================
# conflict_queue_update_batch_status() Tests
# =============================================================================

test_conflict_queue_update_batch_status() {
    conflict_queue_init "$RALPH_DIR"
    conflict_queue_add "$RALPH_DIR" "TASK-001" "$RALPH_DIR/workers/worker-TASK-001" "42" '["src/api.ts"]'
    conflict_queue_add "$RALPH_DIR" "TASK-002" "$RALPH_DIR/workers/worker-TASK-002" "43" '["src/api.ts"]'

    local batch_id
    batch_id=$(conflict_queue_create_batch "$RALPH_DIR" '["TASK-001","TASK-002"]' | head -1)
    conflict_queue_update_batch_status "$RALPH_DIR" "$batch_id" "planning"

    local status
    status=$(jq -r ".batches.\"$batch_id\".status" "$RALPH_DIR/conflict-queue.json")
    assert_equals "planning" "$status" "Status should be updated"
}

# =============================================================================
# conflict_queue_get_batch() Tests
# =============================================================================

test_conflict_queue_get_batch_success() {
    conflict_queue_init "$RALPH_DIR"
    conflict_queue_add "$RALPH_DIR" "TASK-001" "$RALPH_DIR/workers/worker-TASK-001" "42" '["src/api.ts"]'
    conflict_queue_add "$RALPH_DIR" "TASK-002" "$RALPH_DIR/workers/worker-TASK-002" "43" '["src/api.ts"]'

    local batch_id
    batch_id=$(conflict_queue_create_batch "$RALPH_DIR" '["TASK-001","TASK-002"]' | head -1)

    local batch
    batch=$(conflict_queue_get_batch "$RALPH_DIR" "$batch_id")

    assert_not_equals "null" "$batch" "Should return batch info"
    assert_output_contains "$batch" "TASK-001" "Should contain first task"
}

test_conflict_queue_get_batch_nonexistent() {
    conflict_queue_init "$RALPH_DIR"

    local batch
    batch=$(conflict_queue_get_batch "$RALPH_DIR" "batch-nonexistent")
    assert_equals "null" "$batch" "Should return null for nonexistent batch"
}

# =============================================================================
# conflict_queue_stats() Tests
# =============================================================================

test_conflict_queue_stats_empty() {
    conflict_queue_init "$RALPH_DIR"

    local stats
    stats=$(conflict_queue_stats "$RALPH_DIR")

    local queued
    queued=$(echo "$stats" | jq '.queued')
    assert_equals "0" "$queued" "Queued should be 0"
}

test_conflict_queue_stats_with_data() {
    conflict_queue_init "$RALPH_DIR"
    conflict_queue_add "$RALPH_DIR" "TASK-001" "$RALPH_DIR/workers/worker-TASK-001" "42" '["src/api.ts"]'
    conflict_queue_add "$RALPH_DIR" "TASK-002" "$RALPH_DIR/workers/worker-TASK-002" "43" '["src/api.ts"]'

    local batch_id
    batch_id=$(conflict_queue_create_batch "$RALPH_DIR" '["TASK-001","TASK-002"]' | head -1)

    local stats
    stats=$(conflict_queue_stats "$RALPH_DIR")

    local batched
    batched=$(echo "$stats" | jq '.batched')
    assert_equals "2" "$batched" "Batched should be 2"

    local batches
    batches=$(echo "$stats" | jq '.batches')
    assert_equals "1" "$batches" "Batches should be 1"
}

# =============================================================================
# conflict_queue_cleanup_batch() Tests
# =============================================================================

test_conflict_queue_cleanup_batch() {
    conflict_queue_init "$RALPH_DIR"
    conflict_queue_add "$RALPH_DIR" "TASK-001" "$RALPH_DIR/workers/worker-TASK-001" "42" '["src/api.ts"]'
    conflict_queue_add "$RALPH_DIR" "TASK-002" "$RALPH_DIR/workers/worker-TASK-002" "43" '["src/api.ts"]'

    local batch_id
    batch_id=$(conflict_queue_create_batch "$RALPH_DIR" '["TASK-001","TASK-002"]' | head -1)
    conflict_queue_cleanup_batch "$RALPH_DIR" "$batch_id"

    local queue_count batch_count
    queue_count=$(jq '.queue | length' "$RALPH_DIR/conflict-queue.json")
    batch_count=$(jq '.batches | length' "$RALPH_DIR/conflict-queue.json")

    assert_equals "0" "$queue_count" "Queue should be empty"
    assert_equals "0" "$batch_count" "Batches should be empty"
}

# =============================================================================
# Run Tests
# =============================================================================

run_test test_conflict_queue_init_creates_file
run_test test_conflict_queue_init_creates_valid_json
run_test test_conflict_queue_init_idempotent
run_test test_conflict_queue_add_success
run_test test_conflict_queue_add_multiple_files
run_test test_conflict_queue_add_prevents_duplicates
run_test test_conflict_queue_add_multiple_tasks
run_test test_conflict_queue_remove_success
run_test test_conflict_queue_remove_nonexistent_noop
run_test test_conflict_queue_group_related_no_overlap
run_test test_conflict_queue_group_related_with_overlap
run_test test_conflict_queue_group_related_single_task
run_test test_conflict_queue_batch_ready_false
run_test test_conflict_queue_batch_ready_true
run_test test_conflict_queue_create_batch_creates_batch
run_test test_conflict_queue_create_batch_marks_tasks
run_test test_conflict_queue_update_batch_status
run_test test_conflict_queue_get_batch_success
run_test test_conflict_queue_get_batch_nonexistent
run_test test_conflict_queue_stats_empty
run_test test_conflict_queue_stats_with_data
run_test test_conflict_queue_cleanup_batch

print_test_summary
exit_with_test_result
