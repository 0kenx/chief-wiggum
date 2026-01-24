#!/usr/bin/env bash
# Tests for lib/core/checkpoint.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/checkpoint.sh"

# Test isolation
TEST_DIR=""
setup() {
    TEST_DIR=$(mktemp -d)
    export LOG_FILE="$TEST_DIR/test.log"
    export RALPH_RUN_ID="test"
}
teardown() {
    rm -rf "$TEST_DIR"
}

# =============================================================================
# checkpoint_get_dir() Tests
# =============================================================================

test_get_dir_returns_checkpoints_subdir() {
    local result
    result=$(checkpoint_get_dir "$TEST_DIR/worker-TASK-123-abc")
    assert_equals "$TEST_DIR/worker-TASK-123-abc/checkpoints/test" "$result" \
        "checkpoint_get_dir should return worker_dir/checkpoints/run_id"
}

test_get_dir_with_trailing_slash() {
    local result
    result=$(checkpoint_get_dir "$TEST_DIR/worker-dir")
    assert_equals "$TEST_DIR/worker-dir/checkpoints/test" "$result" \
        "checkpoint_get_dir should work without trailing slash"
}

# =============================================================================
# checkpoint_get_path() Tests
# =============================================================================

test_get_path_returns_correct_filename() {
    local result
    result=$(checkpoint_get_path "$TEST_DIR/worker-TASK-42-xyz" "3")
    assert_equals "$TEST_DIR/worker-TASK-42-xyz/checkpoints/test/checkpoint-3.json" "$result" \
        "checkpoint_get_path should return checkpoint-N.json in checkpoints dir"
}

test_get_path_iteration_zero() {
    local result
    result=$(checkpoint_get_path "$TEST_DIR/myworker" "0")
    assert_equals "$TEST_DIR/myworker/checkpoints/test/checkpoint-0.json" "$result" \
        "checkpoint_get_path should handle iteration 0"
}

test_get_path_large_iteration() {
    local result
    result=$(checkpoint_get_path "$TEST_DIR/myworker" "99")
    assert_equals "$TEST_DIR/myworker/checkpoints/test/checkpoint-99.json" "$result" \
        "checkpoint_get_path should handle large iteration numbers"
}

# =============================================================================
# checkpoint_init() Tests
# =============================================================================

test_init_creates_checkpoint_dir() {
    local worker_dir="$TEST_DIR/worker-INIT-1-test"
    mkdir -p "$worker_dir"

    checkpoint_init "$worker_dir"

    assert_dir_exists "$worker_dir/checkpoints" \
        "checkpoint_init should create checkpoints directory"
}

test_init_idempotent() {
    local worker_dir="$TEST_DIR/worker-INIT-2-test"
    mkdir -p "$worker_dir"

    checkpoint_init "$worker_dir"
    checkpoint_init "$worker_dir"

    assert_dir_exists "$worker_dir/checkpoints" \
        "checkpoint_init should be idempotent"
}

test_init_creates_parent_dirs() {
    local worker_dir="$TEST_DIR/deep/nested/worker-INIT-3-test"

    checkpoint_init "$worker_dir"

    assert_dir_exists "$worker_dir/checkpoints" \
        "checkpoint_init should create parent dirs with mkdir -p"
}

# =============================================================================
# checkpoint_write() Tests
# =============================================================================

test_write_creates_checkpoint_file() {
    local worker_dir="$TEST_DIR/worker-WRITE-1-abc"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "session-abc123" "in_progress" \
        '["file1.sh","file2.sh"]' '["task1"]' '["step1"]' "Test summary"

    local checkpoint_file="$worker_dir/checkpoints/test/checkpoint-1.json"
    assert_file_exists "$checkpoint_file" \
        "checkpoint_write should create checkpoint file"
}

test_write_produces_valid_json() {
    local worker_dir="$TEST_DIR/worker-WRITE-2-def"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "session-def456" "completed" \
        '["a.sh"]' '["done"]' '["next"]' "Summary text"

    local checkpoint_file="$worker_dir/checkpoints/test/checkpoint-1.json"
    local valid
    valid=$(jq empty "$checkpoint_file" 2>&1 && echo "valid" || echo "invalid")
    assert_equals "valid" "$valid" \
        "checkpoint_write should produce valid JSON"
}

test_write_stores_correct_version() {
    local worker_dir="$TEST_DIR/worker-WRITE-3-ghi"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "2" "sess-001" "in_progress"

    local checkpoint_file="$worker_dir/checkpoints/test/checkpoint-2.json"
    local version
    version=$(jq -r '.version' "$checkpoint_file")
    assert_equals "1.0" "$version" \
        "checkpoint_write should store version 1.0"
}

test_write_stores_iteration() {
    local worker_dir="$TEST_DIR/worker-WRITE-4-jkl"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "5" "sess-002" "in_progress"

    local checkpoint_file="$worker_dir/checkpoints/test/checkpoint-5.json"
    local iteration
    iteration=$(jq -r '.iteration' "$checkpoint_file")
    assert_equals "5" "$iteration" \
        "checkpoint_write should store correct iteration number"
}

test_write_stores_session_id() {
    local worker_dir="$TEST_DIR/worker-WRITE-5-mno"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "my-session-xyz" "in_progress"

    local checkpoint_file="$worker_dir/checkpoints/test/checkpoint-1.json"
    local session_id
    session_id=$(jq -r '.session_id' "$checkpoint_file")
    assert_equals "my-session-xyz" "$session_id" \
        "checkpoint_write should store session_id"
}

test_write_stores_status() {
    local worker_dir="$TEST_DIR/worker-WRITE-6-pqr"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-003" "completed"

    local checkpoint_file="$worker_dir/checkpoints/test/checkpoint-1.json"
    local status
    status=$(jq -r '.status' "$checkpoint_file")
    assert_equals "completed" "$status" \
        "checkpoint_write should store correct status"
}

test_write_stores_files_modified() {
    local worker_dir="$TEST_DIR/worker-WRITE-7-stu"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-004" "in_progress" \
        '["src/main.sh","lib/util.sh"]'

    local checkpoint_file="$worker_dir/checkpoints/test/checkpoint-1.json"
    local count
    count=$(jq '.files_modified | length' "$checkpoint_file")
    assert_equals "2" "$count" \
        "checkpoint_write should store files_modified array"

    local first_file
    first_file=$(jq -r '.files_modified[0]' "$checkpoint_file")
    assert_equals "src/main.sh" "$first_file" \
        "checkpoint_write should store correct file paths"
}

test_write_stores_completed_tasks() {
    local worker_dir="$TEST_DIR/worker-WRITE-8-vwx"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-005" "in_progress" \
        '[]' '["Implemented feature X","Fixed bug Y"]'

    local checkpoint_file="$worker_dir/checkpoints/test/checkpoint-1.json"
    local count
    count=$(jq '.completed_tasks | length' "$checkpoint_file")
    assert_equals "2" "$count" \
        "checkpoint_write should store completed_tasks array"
}

test_write_stores_next_steps() {
    local worker_dir="$TEST_DIR/worker-WRITE-9-yza"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-006" "in_progress" \
        '[]' '[]' '["Add tests","Update docs"]'

    local checkpoint_file="$worker_dir/checkpoints/test/checkpoint-1.json"
    local count
    count=$(jq '.next_steps | length' "$checkpoint_file")
    assert_equals "2" "$count" \
        "checkpoint_write should store next_steps array"
}

test_write_stores_prose_summary() {
    local worker_dir="$TEST_DIR/worker-WRITE-10-bcd"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-007" "in_progress" \
        '[]' '[]' '[]' "This is a detailed prose summary of the work done."

    local checkpoint_file="$worker_dir/checkpoints/test/checkpoint-1.json"
    local summary
    summary=$(jq -r '.prose_summary' "$checkpoint_file")
    assert_equals "This is a detailed prose summary of the work done." "$summary" \
        "checkpoint_write should store prose_summary"
}

test_write_defaults_empty_arrays() {
    local worker_dir="$TEST_DIR/worker-WRITE-11-efg"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-008" "in_progress"

    local checkpoint_file="$worker_dir/checkpoints/test/checkpoint-1.json"
    local files_count
    files_count=$(jq '.files_modified | length' "$checkpoint_file")
    assert_equals "0" "$files_count" \
        "checkpoint_write should default files_modified to empty array"

    local tasks_count
    tasks_count=$(jq '.completed_tasks | length' "$checkpoint_file")
    assert_equals "0" "$tasks_count" \
        "checkpoint_write should default completed_tasks to empty array"

    local steps_count
    steps_count=$(jq '.next_steps | length' "$checkpoint_file")
    assert_equals "0" "$steps_count" \
        "checkpoint_write should default next_steps to empty array"
}

test_write_extracts_task_id_from_worker_dir() {
    local worker_dir="$TEST_DIR/worker-PROJ-789-somehash"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-009" "in_progress"

    local checkpoint_file="$worker_dir/checkpoints/test/checkpoint-1.json"
    local task_id
    task_id=$(jq -r '.task_id' "$checkpoint_file")
    assert_equals "PROJ-789" "$task_id" \
        "checkpoint_write should extract task_id from worker directory name"
}

test_write_stores_worker_id() {
    local worker_dir="$TEST_DIR/worker-ABC-100-hashval"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-010" "in_progress"

    local checkpoint_file="$worker_dir/checkpoints/test/checkpoint-1.json"
    local worker_id
    worker_id=$(jq -r '.worker_id' "$checkpoint_file")
    assert_equals "worker-ABC-100-hashval" "$worker_id" \
        "checkpoint_write should store worker_id from basename"
}

test_write_stores_timestamp() {
    local worker_dir="$TEST_DIR/worker-TS-1-abc"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-011" "in_progress"

    local checkpoint_file="$worker_dir/checkpoints/test/checkpoint-1.json"
    local timestamp
    timestamp=$(jq -r '.timestamp' "$checkpoint_file")
    assert_not_equals "" "$timestamp" \
        "checkpoint_write should store a non-empty timestamp"
}

# =============================================================================
# checkpoint_read() Tests
# =============================================================================

test_read_returns_full_json() {
    local worker_dir="$TEST_DIR/worker-READ-1-abc"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-r01" "completed" \
        '["x.sh"]' '["task done"]' '["next thing"]' "Read test summary"

    local output
    output=$(checkpoint_read "$worker_dir" "1")
    local valid
    valid=$(echo "$output" | jq empty 2>&1 && echo "valid" || echo "invalid")
    assert_equals "valid" "$valid" \
        "checkpoint_read should return valid JSON"
}

test_read_specific_field_status() {
    local worker_dir="$TEST_DIR/worker-READ-2-def"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-r02" "failed"

    local status
    status=$(checkpoint_read "$worker_dir" "1" ".status")
    assert_equals "failed" "$status" \
        "checkpoint_read with field should return specific value"
}

test_read_specific_field_session_id() {
    local worker_dir="$TEST_DIR/worker-READ-3-ghi"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "2" "sess-unique-id" "in_progress"

    local session_id
    session_id=$(checkpoint_read "$worker_dir" "2" ".session_id")
    assert_equals "sess-unique-id" "$session_id" \
        "checkpoint_read should extract session_id field"
}

test_read_specific_field_iteration() {
    local worker_dir="$TEST_DIR/worker-READ-4-jkl"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "7" "sess-r04" "in_progress"

    local iteration
    iteration=$(checkpoint_read "$worker_dir" "7" ".iteration")
    assert_equals "7" "$iteration" \
        "checkpoint_read should extract iteration field"
}

test_read_nested_field() {
    local worker_dir="$TEST_DIR/worker-READ-5-mno"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-r05" "in_progress" \
        '["file_a.sh","file_b.sh"]'

    local first_file
    first_file=$(checkpoint_read "$worker_dir" "1" ".files_modified[0]")
    assert_equals "file_a.sh" "$first_file" \
        "checkpoint_read should handle jq array access"
}

test_read_nonexistent_checkpoint_fails() {
    local worker_dir="$TEST_DIR/worker-READ-6-pqr"
    mkdir -p "$worker_dir/checkpoints/test"

    local result
    result=$(checkpoint_read "$worker_dir" "999" 2>/dev/null) || true
    assert_equals "" "$result" \
        "checkpoint_read should return empty for nonexistent checkpoint"
}

test_read_latest_when_no_iteration_specified() {
    local worker_dir="$TEST_DIR/worker-READ-7-stu"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-old" "completed"
    checkpoint_write "$worker_dir" "2" "sess-mid" "completed"
    checkpoint_write "$worker_dir" "3" "sess-new" "in_progress"

    local session_id
    session_id=$(checkpoint_read "$worker_dir" "" ".session_id")
    assert_equals "sess-new" "$session_id" \
        "checkpoint_read without iteration should read latest"
}

# =============================================================================
# checkpoint_get_latest() Tests
# =============================================================================

test_get_latest_single_checkpoint() {
    local worker_dir="$TEST_DIR/worker-LAT-1-abc"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-l01" "in_progress"

    local latest
    latest=$(checkpoint_get_latest "$worker_dir")
    assert_equals "$worker_dir/checkpoints/test/checkpoint-1.json" "$latest" \
        "checkpoint_get_latest should return only checkpoint"
}

test_get_latest_multiple_checkpoints() {
    local worker_dir="$TEST_DIR/worker-LAT-2-def"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-l02a" "completed"
    checkpoint_write "$worker_dir" "2" "sess-l02b" "completed"
    checkpoint_write "$worker_dir" "3" "sess-l02c" "in_progress"

    local latest
    latest=$(checkpoint_get_latest "$worker_dir")
    assert_equals "$worker_dir/checkpoints/test/checkpoint-3.json" "$latest" \
        "checkpoint_get_latest should return highest iteration"
}

test_get_latest_nonsequential_iterations() {
    local worker_dir="$TEST_DIR/worker-LAT-3-ghi"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "2" "sess-l03a" "completed"
    checkpoint_write "$worker_dir" "5" "sess-l03b" "completed"
    checkpoint_write "$worker_dir" "10" "sess-l03c" "in_progress"

    local latest
    latest=$(checkpoint_get_latest "$worker_dir")
    assert_equals "$worker_dir/checkpoints/test/checkpoint-10.json" "$latest" \
        "checkpoint_get_latest should handle nonsequential iterations"
}

test_get_latest_no_checkpoints_fails() {
    local worker_dir="$TEST_DIR/worker-LAT-4-jkl"
    mkdir -p "$worker_dir/checkpoints/test"

    local latest
    latest=$(checkpoint_get_latest "$worker_dir" 2>/dev/null) || true
    assert_equals "" "$latest" \
        "checkpoint_get_latest should return empty when no checkpoints"
}

test_get_latest_no_checkpoint_dir_fails() {
    local worker_dir="$TEST_DIR/worker-LAT-5-mno"
    mkdir -p "$worker_dir"

    local result=0
    checkpoint_get_latest "$worker_dir" 2>/dev/null || result=$?
    assert_equals "1" "$result" \
        "checkpoint_get_latest should fail when dir does not exist"
}

# =============================================================================
# checkpoint_get_latest_iteration() Tests
# =============================================================================

test_get_latest_iteration_returns_number() {
    local worker_dir="$TEST_DIR/worker-ITER-1-abc"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-i01" "completed"
    checkpoint_write "$worker_dir" "2" "sess-i02" "completed"
    checkpoint_write "$worker_dir" "3" "sess-i03" "in_progress"

    local iteration
    iteration=$(checkpoint_get_latest_iteration "$worker_dir")
    assert_equals "3" "$iteration" \
        "checkpoint_get_latest_iteration should return highest iteration"
}

test_get_latest_iteration_no_checkpoints() {
    local worker_dir="$TEST_DIR/worker-ITER-2-def"
    mkdir -p "$worker_dir/checkpoints/test"

    local iteration
    iteration=$(checkpoint_get_latest_iteration "$worker_dir")
    assert_equals "-1" "$iteration" \
        "checkpoint_get_latest_iteration should return -1 when no checkpoints"
}

test_get_latest_iteration_no_dir() {
    local worker_dir="$TEST_DIR/worker-ITER-3-ghi"
    mkdir -p "$worker_dir"

    local iteration
    iteration=$(checkpoint_get_latest_iteration "$worker_dir")
    assert_equals "-1" "$iteration" \
        "checkpoint_get_latest_iteration should return -1 when dir missing"
}

test_get_latest_iteration_single() {
    local worker_dir="$TEST_DIR/worker-ITER-4-jkl"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "7" "sess-i04" "in_progress"

    local iteration
    iteration=$(checkpoint_get_latest_iteration "$worker_dir")
    assert_equals "7" "$iteration" \
        "checkpoint_get_latest_iteration should work with single checkpoint"
}

# =============================================================================
# checkpoint_list() Tests
# =============================================================================

test_list_multiple_checkpoints() {
    local worker_dir="$TEST_DIR/worker-LIST-1-abc"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-ls01" "completed"
    checkpoint_write "$worker_dir" "2" "sess-ls02" "completed"
    checkpoint_write "$worker_dir" "3" "sess-ls03" "in_progress"

    local output
    output=$(checkpoint_list "$worker_dir")
    assert_output_contains "$output" "1 completed" \
        "checkpoint_list should show iteration 1 as completed"
    assert_output_contains "$output" "2 completed" \
        "checkpoint_list should show iteration 2 as completed"
    assert_output_contains "$output" "3 in_progress" \
        "checkpoint_list should show iteration 3 as in_progress"
}

test_list_sorted_output() {
    local worker_dir="$TEST_DIR/worker-LIST-2-def"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "3" "sess-ls04" "in_progress"
    checkpoint_write "$worker_dir" "1" "sess-ls05" "completed"
    checkpoint_write "$worker_dir" "2" "sess-ls06" "completed"

    local output
    output=$(checkpoint_list "$worker_dir")
    local first_line
    first_line=$(echo "$output" | head -1)
    assert_output_contains "$first_line" "1 completed" \
        "checkpoint_list should sort by iteration number"
}

test_list_empty_when_no_checkpoints() {
    local worker_dir="$TEST_DIR/worker-LIST-3-ghi"
    mkdir -p "$worker_dir/checkpoints/test"

    local output
    output=$(checkpoint_list "$worker_dir")
    assert_equals "" "$output" \
        "checkpoint_list should return empty when no checkpoints"
}

test_list_no_dir_returns_empty() {
    local worker_dir="$TEST_DIR/worker-LIST-4-jkl"
    mkdir -p "$worker_dir"

    local output
    output=$(checkpoint_list "$worker_dir")
    assert_equals "" "$output" \
        "checkpoint_list should return empty when checkpoint dir missing"
}

# =============================================================================
# checkpoint_update_status() Tests
# =============================================================================

test_update_status_changes_value() {
    local worker_dir="$TEST_DIR/worker-STAT-1-abc"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-s01" "in_progress"
    checkpoint_update_status "$worker_dir" "1" "completed"

    local status
    status=$(checkpoint_read "$worker_dir" "1" ".status")
    assert_equals "completed" "$status" \
        "checkpoint_update_status should change the status field"
}

test_update_status_to_failed() {
    local worker_dir="$TEST_DIR/worker-STAT-2-def"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "2" "sess-s02" "in_progress"
    checkpoint_update_status "$worker_dir" "2" "failed"

    local status
    status=$(checkpoint_read "$worker_dir" "2" ".status")
    assert_equals "failed" "$status" \
        "checkpoint_update_status should set status to failed"
}

test_update_status_to_interrupted() {
    local worker_dir="$TEST_DIR/worker-STAT-3-ghi"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-s03" "in_progress"
    checkpoint_update_status "$worker_dir" "1" "interrupted"

    local status
    status=$(checkpoint_read "$worker_dir" "1" ".status")
    assert_equals "interrupted" "$status" \
        "checkpoint_update_status should set status to interrupted"
}

test_update_status_nonexistent_fails() {
    local worker_dir="$TEST_DIR/worker-STAT-4-jkl"
    mkdir -p "$worker_dir/checkpoints/test"

    local result=0
    checkpoint_update_status "$worker_dir" "99" "completed" 2>/dev/null || result=$?
    assert_equals "1" "$result" \
        "checkpoint_update_status should fail for nonexistent checkpoint"
}

test_update_status_preserves_other_fields() {
    local worker_dir="$TEST_DIR/worker-STAT-5-mno"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-s05" "in_progress" \
        '["myfile.sh"]' '["task1"]' '["step1"]' "Keep this summary"
    checkpoint_update_status "$worker_dir" "1" "completed"

    local session_id
    session_id=$(checkpoint_read "$worker_dir" "1" ".session_id")
    assert_equals "sess-s05" "$session_id" \
        "checkpoint_update_status should preserve session_id"

    local files_count
    files_count=$(checkpoint_read "$worker_dir" "1" ".files_modified | length")
    assert_equals "1" "$files_count" \
        "checkpoint_update_status should preserve files_modified"

    local summary
    summary=$(checkpoint_read "$worker_dir" "1" ".prose_summary")
    assert_equals "Keep this summary" "$summary" \
        "checkpoint_update_status should preserve prose_summary"
}

# =============================================================================
# checkpoint_update_summary() Tests
# =============================================================================

test_update_summary_from_file() {
    local worker_dir="$TEST_DIR/worker-SUM-1-abc"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-sum01" "in_progress"

    local summary_file="$TEST_DIR/summary.txt"
    echo "This is the updated summary from the file." > "$summary_file"

    checkpoint_update_summary "$worker_dir" "1" "$summary_file"

    local summary
    summary=$(checkpoint_read "$worker_dir" "1" ".prose_summary")
    assert_equals "This is the updated summary from the file." "$summary" \
        "checkpoint_update_summary should update prose_summary from file"
}

test_update_summary_multiline() {
    local worker_dir="$TEST_DIR/worker-SUM-2-def"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-sum02" "in_progress"

    local summary_file="$TEST_DIR/multiline_summary.txt"
    printf "Line one.\nLine two.\nLine three." > "$summary_file"

    checkpoint_update_summary "$worker_dir" "1" "$summary_file"

    local summary
    summary=$(checkpoint_read "$worker_dir" "1" ".prose_summary")
    assert_output_contains "$summary" "Line one." \
        "checkpoint_update_summary should handle multiline content (line 1)"
    assert_output_contains "$summary" "Line three." \
        "checkpoint_update_summary should handle multiline content (line 3)"
}

test_update_summary_nonexistent_checkpoint_fails() {
    local worker_dir="$TEST_DIR/worker-SUM-3-ghi"
    mkdir -p "$worker_dir/checkpoints/test"

    local summary_file="$TEST_DIR/summary_no_cp.txt"
    echo "orphan summary" > "$summary_file"

    local result=0
    checkpoint_update_summary "$worker_dir" "99" "$summary_file" 2>/dev/null || result=$?
    assert_equals "1" "$result" \
        "checkpoint_update_summary should fail for nonexistent checkpoint"
}

test_update_summary_missing_file_sets_empty() {
    local worker_dir="$TEST_DIR/worker-SUM-4-jkl"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-sum04" "in_progress" \
        '[]' '[]' '[]' "Original summary"

    checkpoint_update_summary "$worker_dir" "1" "$TEST_DIR/nonexistent_summary.txt"

    local summary
    summary=$(checkpoint_read "$worker_dir" "1" ".prose_summary")
    assert_equals "" "$summary" \
        "checkpoint_update_summary with missing file should set empty summary"
}

# =============================================================================
# checkpoint_update_supervisor() Tests
# =============================================================================

test_update_supervisor_continue() {
    local worker_dir="$TEST_DIR/worker-SUP-1-abc"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-sup01" "completed"
    checkpoint_update_supervisor "$worker_dir" "1" "CONTINUE" "Keep going with tests"

    local decision
    decision=$(checkpoint_read "$worker_dir" "1" ".supervisor_decision")
    assert_equals "CONTINUE" "$decision" \
        "checkpoint_update_supervisor should store CONTINUE decision"

    local guidance
    guidance=$(checkpoint_read "$worker_dir" "1" ".supervisor_guidance")
    assert_equals "Keep going with tests" "$guidance" \
        "checkpoint_update_supervisor should store guidance text"
}

test_update_supervisor_stop() {
    local worker_dir="$TEST_DIR/worker-SUP-2-def"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-sup02" "completed"
    checkpoint_update_supervisor "$worker_dir" "1" "STOP" "Task is done"

    local decision
    decision=$(checkpoint_read "$worker_dir" "1" ".supervisor_decision")
    assert_equals "STOP" "$decision" \
        "checkpoint_update_supervisor should store STOP decision"
}

test_update_supervisor_restart() {
    local worker_dir="$TEST_DIR/worker-SUP-3-ghi"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-sup03" "failed"
    checkpoint_update_supervisor "$worker_dir" "1" "RESTART" "Try a different approach"

    local decision
    decision=$(checkpoint_read "$worker_dir" "1" ".supervisor_decision")
    assert_equals "RESTART" "$decision" \
        "checkpoint_update_supervisor should store RESTART decision"

    local guidance
    guidance=$(checkpoint_read "$worker_dir" "1" ".supervisor_guidance")
    assert_equals "Try a different approach" "$guidance" \
        "checkpoint_update_supervisor should store restart guidance"
}

test_update_supervisor_empty_guidance() {
    local worker_dir="$TEST_DIR/worker-SUP-4-jkl"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-sup04" "completed"
    checkpoint_update_supervisor "$worker_dir" "1" "CONTINUE"

    local guidance
    guidance=$(checkpoint_read "$worker_dir" "1" ".supervisor_guidance")
    assert_equals "" "$guidance" \
        "checkpoint_update_supervisor should handle empty guidance"
}

test_update_supervisor_nonexistent_fails() {
    local worker_dir="$TEST_DIR/worker-SUP-5-mno"
    mkdir -p "$worker_dir/checkpoints/test"

    local result=0
    checkpoint_update_supervisor "$worker_dir" "99" "STOP" "no checkpoint" 2>/dev/null || result=$?
    assert_equals "1" "$result" \
        "checkpoint_update_supervisor should fail for nonexistent checkpoint"
}

test_update_supervisor_preserves_other_fields() {
    local worker_dir="$TEST_DIR/worker-SUP-6-pqr"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-sup06" "completed" \
        '["important.sh"]' '["did stuff"]' '[]' "Keep me"
    checkpoint_update_supervisor "$worker_dir" "1" "CONTINUE" "Guidance here"

    local status
    status=$(checkpoint_read "$worker_dir" "1" ".status")
    assert_equals "completed" "$status" \
        "checkpoint_update_supervisor should preserve status"

    local summary
    summary=$(checkpoint_read "$worker_dir" "1" ".prose_summary")
    assert_equals "Keep me" "$summary" \
        "checkpoint_update_supervisor should preserve prose_summary"
}

# =============================================================================
# checkpoint_extract_files_modified() Tests
# =============================================================================

test_extract_files_from_log() {
    local log_file="$TEST_DIR/iteration.log"
    cat > "$log_file" << 'LOGEOF'
{"type":"tool_call","name":"Edit","input":{"file_path":"/src/main.sh","old_text":"foo","new_text":"bar"}}
{"type":"tool_call","name":"Write","input":{"file_path":"/src/new_file.sh","content":"hello"}}
{"type":"tool_call","name":"Edit","input":{"file_path":"/lib/util.sh","old_text":"a","new_text":"b"}}
LOGEOF

    local result
    result=$(checkpoint_extract_files_modified "$log_file")

    local valid
    valid=$(echo "$result" | jq empty 2>&1 && echo "valid" || echo "invalid")
    assert_equals "valid" "$valid" \
        "checkpoint_extract_files_modified should return valid JSON array"

    local count
    count=$(echo "$result" | jq 'length')
    assert_equals "3" "$count" \
        "checkpoint_extract_files_modified should find 3 unique files"

    assert_output_contains "$result" "/src/main.sh" \
        "checkpoint_extract_files_modified should contain main.sh"
    assert_output_contains "$result" "/src/new_file.sh" \
        "checkpoint_extract_files_modified should contain new_file.sh"
    assert_output_contains "$result" "/lib/util.sh" \
        "checkpoint_extract_files_modified should contain util.sh"
}

test_extract_files_deduplicates() {
    local log_file="$TEST_DIR/dup_iteration.log"
    cat > "$log_file" << 'LOGEOF'
{"type":"tool_call","name":"Edit","input":{"file_path":"/src/same.sh","old_text":"a","new_text":"b"}}
{"type":"tool_call","name":"Edit","input":{"file_path":"/src/same.sh","old_text":"c","new_text":"d"}}
{"type":"tool_call","name":"Write","input":{"file_path":"/src/same.sh","content":"final"}}
LOGEOF

    local result
    result=$(checkpoint_extract_files_modified "$log_file")
    local count
    count=$(echo "$result" | jq 'length')
    assert_equals "1" "$count" \
        "checkpoint_extract_files_modified should deduplicate repeated files"
}

test_extract_files_nonexistent_log() {
    local result
    result=$(checkpoint_extract_files_modified "$TEST_DIR/no_such_log.txt")
    assert_equals "[]" "$result" \
        "checkpoint_extract_files_modified should return [] for missing log"
}

test_extract_files_empty_log() {
    local log_file="$TEST_DIR/empty.log"
    touch "$log_file"

    local result
    result=$(checkpoint_extract_files_modified "$log_file")
    assert_equals "[]" "$result" \
        "checkpoint_extract_files_modified should return [] for empty log"
}

test_extract_files_no_edits_in_log() {
    local log_file="$TEST_DIR/no_edits.log"
    cat > "$log_file" << 'LOGEOF'
{"type":"tool_call","name":"Read","input":{"file_path":"/src/read_only.sh"}}
{"type":"tool_call","name":"Bash","input":{"command":"ls"}}
LOGEOF

    local result
    result=$(checkpoint_extract_files_modified "$log_file")
    assert_equals "[]" "$result" \
        "checkpoint_extract_files_modified should return [] when no Edit/Write calls"
}

# =============================================================================
# checkpoint_from_summary() Tests
# =============================================================================

test_from_summary_basic() {
    local worker_dir="$TEST_DIR/worker-FROM-1-abc"
    mkdir -p "$worker_dir"

    checkpoint_from_summary "$worker_dir" "1" "sess-from01" "completed"

    local checkpoint_file="$worker_dir/checkpoints/test/checkpoint-1.json"
    assert_file_exists "$checkpoint_file" \
        "checkpoint_from_summary should create checkpoint file"

    local status
    status=$(checkpoint_read "$worker_dir" "1" ".status")
    assert_equals "completed" "$status" \
        "checkpoint_from_summary should set correct status"
}

test_from_summary_with_log_file() {
    local worker_dir="$TEST_DIR/worker-FROM-2-def"
    mkdir -p "$worker_dir"

    local log_file="$TEST_DIR/from_log.txt"
    cat > "$log_file" << 'LOGEOF'
{"type":"tool_call","name":"Edit","input":{"file_path":"/extracted/file.sh","old_text":"x","new_text":"y"}}
LOGEOF

    checkpoint_from_summary "$worker_dir" "1" "sess-from02" "completed" "$log_file"

    local files
    files=$(checkpoint_read "$worker_dir" "1" ".files_modified[0]")
    assert_equals "/extracted/file.sh" "$files" \
        "checkpoint_from_summary should extract files_modified from log"
}

test_from_summary_with_summary_file() {
    local worker_dir="$TEST_DIR/worker-FROM-3-ghi"
    mkdir -p "$worker_dir"

    local summary_file="$TEST_DIR/from_summary.txt"
    echo "Work completed successfully with all tests passing." > "$summary_file"

    checkpoint_from_summary "$worker_dir" "1" "sess-from03" "completed" "" "$summary_file"

    local summary
    summary=$(checkpoint_read "$worker_dir" "1" ".prose_summary")
    assert_equals "Work completed successfully with all tests passing." "$summary" \
        "checkpoint_from_summary should read prose_summary from file"
}

test_from_summary_with_both_log_and_summary() {
    local worker_dir="$TEST_DIR/worker-FROM-4-jkl"
    mkdir -p "$worker_dir"

    local log_file="$TEST_DIR/both_log.txt"
    cat > "$log_file" << 'LOGEOF'
{"type":"tool_call","name":"Write","input":{"file_path":"/both/new.sh","content":"code"}}
LOGEOF

    local summary_file="$TEST_DIR/both_summary.txt"
    echo "Combined test summary." > "$summary_file"

    checkpoint_from_summary "$worker_dir" "1" "sess-from04" "in_progress" \
        "$log_file" "$summary_file"

    local files
    files=$(checkpoint_read "$worker_dir" "1" ".files_modified[0]")
    assert_equals "/both/new.sh" "$files" \
        "checkpoint_from_summary should extract files from log"

    local summary
    summary=$(checkpoint_read "$worker_dir" "1" ".prose_summary")
    assert_equals "Combined test summary." "$summary" \
        "checkpoint_from_summary should set prose_summary from file"
}

test_from_summary_missing_log_uses_empty_array() {
    local worker_dir="$TEST_DIR/worker-FROM-5-mno"
    mkdir -p "$worker_dir"

    checkpoint_from_summary "$worker_dir" "1" "sess-from05" "completed" \
        "$TEST_DIR/no_such_log.txt"

    local files_count
    files_count=$(checkpoint_read "$worker_dir" "1" ".files_modified | length")
    assert_equals "0" "$files_count" \
        "checkpoint_from_summary should use empty array for missing log"
}

test_from_summary_missing_summary_uses_empty_string() {
    local worker_dir="$TEST_DIR/worker-FROM-6-pqr"
    mkdir -p "$worker_dir"

    checkpoint_from_summary "$worker_dir" "1" "sess-from06" "completed" \
        "" "$TEST_DIR/no_such_summary.txt"

    local summary
    summary=$(checkpoint_read "$worker_dir" "1" ".prose_summary")
    assert_equals "" "$summary" \
        "checkpoint_from_summary should use empty string for missing summary"
}

# =============================================================================
# checkpoint_exists() Tests
# =============================================================================

test_exists_returns_true_when_present() {
    local worker_dir="$TEST_DIR/worker-EXIST-1-abc"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-ex01" "in_progress"

    local result=0
    checkpoint_exists "$worker_dir" "1" || result=$?
    assert_equals "0" "$result" \
        "checkpoint_exists should return 0 when checkpoint exists"
}

test_exists_returns_false_when_missing() {
    local worker_dir="$TEST_DIR/worker-EXIST-2-def"
    mkdir -p "$worker_dir/checkpoints/test"

    local result=0
    checkpoint_exists "$worker_dir" "42" || result=$?
    assert_equals "1" "$result" \
        "checkpoint_exists should return 1 when checkpoint does not exist"
}

test_exists_returns_false_no_dir() {
    local worker_dir="$TEST_DIR/worker-EXIST-3-ghi"
    mkdir -p "$worker_dir"

    local result=0
    checkpoint_exists "$worker_dir" "1" || result=$?
    assert_equals "1" "$result" \
        "checkpoint_exists should return 1 when checkpoints dir missing"
}

test_exists_specific_iteration() {
    local worker_dir="$TEST_DIR/worker-EXIST-4-jkl"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-ex04a" "completed"
    checkpoint_write "$worker_dir" "3" "sess-ex04b" "in_progress"

    local result_1=0
    checkpoint_exists "$worker_dir" "1" || result_1=$?
    assert_equals "0" "$result_1" \
        "checkpoint_exists should find iteration 1"

    local result_2=0
    checkpoint_exists "$worker_dir" "2" || result_2=$?
    assert_equals "1" "$result_2" \
        "checkpoint_exists should not find iteration 2"

    local result_3=0
    checkpoint_exists "$worker_dir" "3" || result_3=$?
    assert_equals "0" "$result_3" \
        "checkpoint_exists should find iteration 3"
}

# =============================================================================
# Error Cases Tests
# =============================================================================

test_write_invalid_json_arrays_still_writes() {
    local worker_dir="$TEST_DIR/worker-ERR-1-abc"
    mkdir -p "$worker_dir"

    # Even with invalid JSON in arrays, the file should be created
    # (the function does not validate input JSON)
    checkpoint_write "$worker_dir" "1" "sess-err01" "in_progress" \
        '["valid"]' '["also valid"]' '["fine"]'

    local checkpoint_file="$worker_dir/checkpoints/test/checkpoint-1.json"
    assert_file_exists "$checkpoint_file" \
        "checkpoint_write should create file with valid array arguments"
}

test_read_from_completely_nonexistent_dir() {
    local result=0
    checkpoint_read "$TEST_DIR/totally/fake/path" "1" 2>/dev/null || result=$?
    assert_equals "1" "$result" \
        "checkpoint_read should fail for completely nonexistent directory"
}

test_update_status_after_supervisor_preserves_supervisor_fields() {
    local worker_dir="$TEST_DIR/worker-ERR-2-def"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-err02" "in_progress"
    checkpoint_update_supervisor "$worker_dir" "1" "CONTINUE" "Go on"
    checkpoint_update_status "$worker_dir" "1" "completed"

    local decision
    decision=$(checkpoint_read "$worker_dir" "1" ".supervisor_decision")
    assert_equals "CONTINUE" "$decision" \
        "Updating status should preserve supervisor_decision"

    local guidance
    guidance=$(checkpoint_read "$worker_dir" "1" ".supervisor_guidance")
    assert_equals "Go on" "$guidance" \
        "Updating status should preserve supervisor_guidance"
}

test_multiple_writes_overwrite_same_iteration() {
    local worker_dir="$TEST_DIR/worker-ERR-3-ghi"
    mkdir -p "$worker_dir"

    checkpoint_write "$worker_dir" "1" "sess-first" "in_progress" \
        '[]' '[]' '[]' "First write"
    checkpoint_write "$worker_dir" "1" "sess-second" "completed" \
        '["new.sh"]' '["done"]' '[]' "Second write"

    local session_id
    session_id=$(checkpoint_read "$worker_dir" "1" ".session_id")
    assert_equals "sess-second" "$session_id" \
        "Writing same iteration should overwrite with new data"

    local summary
    summary=$(checkpoint_read "$worker_dir" "1" ".prose_summary")
    assert_equals "Second write" "$summary" \
        "Overwritten checkpoint should have new summary"
}

# =============================================================================
# Run All Tests
# =============================================================================

# checkpoint_get_dir tests
run_test test_get_dir_returns_checkpoints_subdir
run_test test_get_dir_with_trailing_slash

# checkpoint_get_path tests
run_test test_get_path_returns_correct_filename
run_test test_get_path_iteration_zero
run_test test_get_path_large_iteration

# checkpoint_init tests
run_test test_init_creates_checkpoint_dir
run_test test_init_idempotent
run_test test_init_creates_parent_dirs

# checkpoint_write tests
run_test test_write_creates_checkpoint_file
run_test test_write_produces_valid_json
run_test test_write_stores_correct_version
run_test test_write_stores_iteration
run_test test_write_stores_session_id
run_test test_write_stores_status
run_test test_write_stores_files_modified
run_test test_write_stores_completed_tasks
run_test test_write_stores_next_steps
run_test test_write_stores_prose_summary
run_test test_write_defaults_empty_arrays
run_test test_write_extracts_task_id_from_worker_dir
run_test test_write_stores_worker_id
run_test test_write_stores_timestamp

# checkpoint_read tests
run_test test_read_returns_full_json
run_test test_read_specific_field_status
run_test test_read_specific_field_session_id
run_test test_read_specific_field_iteration
run_test test_read_nested_field
run_test test_read_nonexistent_checkpoint_fails
run_test test_read_latest_when_no_iteration_specified

# checkpoint_get_latest tests
run_test test_get_latest_single_checkpoint
run_test test_get_latest_multiple_checkpoints
run_test test_get_latest_nonsequential_iterations
run_test test_get_latest_no_checkpoints_fails
run_test test_get_latest_no_checkpoint_dir_fails

# checkpoint_get_latest_iteration tests
run_test test_get_latest_iteration_returns_number
run_test test_get_latest_iteration_no_checkpoints
run_test test_get_latest_iteration_no_dir
run_test test_get_latest_iteration_single

# checkpoint_list tests
run_test test_list_multiple_checkpoints
run_test test_list_sorted_output
run_test test_list_empty_when_no_checkpoints
run_test test_list_no_dir_returns_empty

# checkpoint_update_status tests
run_test test_update_status_changes_value
run_test test_update_status_to_failed
run_test test_update_status_to_interrupted
run_test test_update_status_nonexistent_fails
run_test test_update_status_preserves_other_fields

# checkpoint_update_summary tests
run_test test_update_summary_from_file
run_test test_update_summary_multiline
run_test test_update_summary_nonexistent_checkpoint_fails
run_test test_update_summary_missing_file_sets_empty

# checkpoint_update_supervisor tests
run_test test_update_supervisor_continue
run_test test_update_supervisor_stop
run_test test_update_supervisor_restart
run_test test_update_supervisor_empty_guidance
run_test test_update_supervisor_nonexistent_fails
run_test test_update_supervisor_preserves_other_fields

# checkpoint_extract_files_modified tests
run_test test_extract_files_from_log
run_test test_extract_files_deduplicates
run_test test_extract_files_nonexistent_log
run_test test_extract_files_empty_log
run_test test_extract_files_no_edits_in_log

# checkpoint_from_summary tests
run_test test_from_summary_basic
run_test test_from_summary_with_log_file
run_test test_from_summary_with_summary_file
run_test test_from_summary_with_both_log_and_summary
run_test test_from_summary_missing_log_uses_empty_array
run_test test_from_summary_missing_summary_uses_empty_string

# checkpoint_exists tests
run_test test_exists_returns_true_when_present
run_test test_exists_returns_false_when_missing
run_test test_exists_returns_false_no_dir
run_test test_exists_specific_iteration

# Error case tests
run_test test_write_invalid_json_arrays_still_writes
run_test test_read_from_completely_nonexistent_dir
run_test test_update_status_after_supervisor_preserves_supervisor_fields
run_test test_multiple_writes_overwrite_same_iteration

print_test_summary
exit_with_test_result
