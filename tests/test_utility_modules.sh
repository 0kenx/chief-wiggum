#!/usr/bin/env bash
# =============================================================================
# test_utility_modules.sh - Tests for low-priority utility modules
#
# Tests coverage for:
#   - lib/utils/activity-log.sh
#   - lib/utils/work-log.sh
#   - lib/core/gh-error.sh
# =============================================================================

set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

LOG_LEVEL=ERROR
export LOG_LEVEL

# Source modules under test
source "$WIGGUM_HOME/lib/utils/activity-log.sh"
source "$WIGGUM_HOME/lib/utils/work-log.sh"
source "$WIGGUM_HOME/lib/core/gh-error.sh"

TEST_DIR=""
RALPH_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    RALPH_DIR="$TEST_DIR/ralph"
    export RALPH_DIR
    # Reset activity log for each test
    _ACTIVITY_LOG_FILE=""
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# Tests for lib/utils/activity-log.sh
# =============================================================================

test_activity_log_init_creates_directory() {
    setup

    activity_init "$TEST_DIR"

    assert_file_exists "$RALPH_DIR/logs/activity.jsonl" "activity.jsonl created"
    assert_not_empty "$_ACTIVITY_LOG_FILE" "Global log file path set"

    teardown
}

test_activity_log_writes_valid_json() {
    setup

    activity_init "$TEST_DIR"

    activity_log "test.event" "worker-001" "TASK-123"

    assert_file_exists "$RALPH_DIR/logs/activity.jsonl" "Log file exists"

    # Verify JSON is valid
    local json_valid=0
    jq empty "$RALPH_DIR/logs/activity.jsonl" 2>/dev/null || json_valid=$?
    assert_equals 0 "$json_valid" "Log contains valid JSON"

    # Verify required fields
    local event
    event=$(jq -r '.event' "$RALPH_DIR/logs/activity.jsonl")
    assert_equals "test.event" "$event" "Event field correct"

    local worker_id
    worker_id=$(jq -r '.worker_id' "$RALPH_DIR/logs/activity.jsonl")
    assert_equals "worker-001" "$worker_id" "Worker ID field correct"

    local task_id
    task_id=$(jq -r '.task_id' "$RALPH_DIR/logs/activity.jsonl")
    assert_equals "TASK-123" "$task_id" "Task ID field correct"

    # Verify timestamp exists and is not empty
    local ts
    ts=$(jq -r '.ts' "$RALPH_DIR/logs/activity.jsonl")
    assert_not_empty "$ts" "Timestamp field exists"

    teardown
}

test_activity_log_extra_fields() {
    setup

    activity_init "$TEST_DIR"

    activity_log "agent.completed" "worker-002" "TASK-456" "step_id=planning" "agent=product.plan-mode" "exit_code=0"

    local step_id
    step_id=$(jq -r '.step_id' "$RALPH_DIR/logs/activity.jsonl")
    assert_equals "planning" "$step_id" "Extra field: step_id"

    local agent
    agent=$(jq -r '.agent' "$RALPH_DIR/logs/activity.jsonl")
    assert_equals "product.plan-mode" "$agent" "Extra field: agent"

    local exit_code
    exit_code=$(jq -r '.exit_code' "$RALPH_DIR/logs/activity.jsonl")
    assert_equals "0" "$exit_code" "Extra field: exit_code"

    teardown
}

test_activity_log_invalid_task_id_sanitized() {
    setup

    activity_init "$TEST_DIR"

    # Test various invalid formats
    activity_log "test.event" "worker-001" "INVALID_ID_NO_DASH"
    activity_log "test.event" "worker-002" "X-99999"
    activity_log "test.event" "worker-003" "TOOLONGPREFIX-123"
    activity_log "test.event" "worker-004" "AB-"

    local line_count
    line_count=$(wc -l < "$RALPH_DIR/logs/activity.jsonl")
    assert_equals "4" "$line_count" "Four log lines written"

    # All should be sanitized to INVALID_TASK_ID
    local sanitized_count
    sanitized_count=$(grep -c '"task_id":"INVALID_TASK_ID"' "$RALPH_DIR/logs/activity.jsonl")
    assert_equals "4" "$sanitized_count" "All invalid task IDs sanitized"

    teardown
}

test_activity_log_valid_task_id_formats() {
    setup

    activity_init "$TEST_DIR"

    # Test valid formats (prefix 2-10 letters, number 1-4 digits)
    activity_log "test.event" "worker-001" "TASK-001"
    activity_log "test.event" "worker-002" "AB-1"
    activity_log "test.event" "worker-003" "LONGPREFIX-9999"
    activity_log "test.event" "worker-004" "Aa-123"

    # Verify all are accepted as-is
    local task_ids
    task_ids=$(jq -r '.task_id' "$RALPH_DIR/logs/activity.jsonl" | paste -sd ',' -)
    assert_equals "TASK-001,AB-1,LONGPREFIX-9999,Aa-123" "$task_ids" "Valid task IDs preserved"

    teardown
}

test_activity_log_empty_worker_and_task() {
    setup

    activity_init "$TEST_DIR"

    activity_log "system.startup" "" ""

    local worker_id
    worker_id=$(jq -r '.worker_id' "$RALPH_DIR/logs/activity.jsonl")
    assert_equals "" "$worker_id" "Empty worker_id accepted"

    local task_id
    task_id=$(jq -r '.task_id' "$RALPH_DIR/logs/activity.jsonl")
    assert_equals "" "$task_id" "Empty task_id accepted"

    teardown
}

test_activity_log_multiple_lines() {
    setup

    activity_init "$TEST_DIR"

    activity_log "event.one" "worker-001" "TASK-001"
    activity_log "event.two" "worker-002" "TASK-002"
    activity_log "event.three" "worker-003" "TASK-003"

    local line_count
    line_count=$(wc -l < "$RALPH_DIR/logs/activity.jsonl")
    assert_equals "3" "$line_count" "Three log lines written"

    # Verify all lines are valid JSON
    local json_valid=0
    while IFS= read -r line; do
        echo "$line" | jq empty 2>/dev/null || json_valid=$?
    done < "$RALPH_DIR/logs/activity.jsonl"
    assert_equals 0 "$json_valid" "All lines are valid JSON"

    teardown
}

test_activity_log_context_update() {
    setup

    activity_init "$TEST_DIR"

    activity_log_context_update "worker-001" "TASK-123" "description" "github_issue_sync" "abc123" "def456"

    local event
    event=$(jq -r '.event' "$RALPH_DIR/logs/activity.jsonl")
    assert_equals "context.updated" "$event" "Event is context.updated"

    local field
    field=$(jq -r '.field' "$RALPH_DIR/logs/activity.jsonl")
    assert_equals "description" "$field" "Field is description"

    local source
    source=$(jq -r '.source' "$RALPH_DIR/logs/activity.jsonl")
    assert_equals "github_issue_sync" "$source" "Source is github_issue_sync"

    local old_hash
    old_hash=$(jq -r '.old_hash' "$RALPH_DIR/logs/activity.jsonl")
    assert_equals "abc123" "$old_hash" "Old hash correct"

    local new_hash
    new_hash=$(jq -r '.new_hash' "$RALPH_DIR/logs/activity.jsonl")
    assert_equals "def456" "$new_hash" "New hash correct"

    teardown
}

test_activity_log_not_initialized() {
    setup

    # Don't call activity_init

    # Should not error if not initialized
    activity_log "test.event" "worker-001" "TASK-123"

    # Log file should not be created
    assert_file_not_exists "$RALPH_DIR/logs/activity.jsonl" "No log file created without init"

    teardown
}

# =============================================================================
# Tests for lib/utils/work-log.sh
# =============================================================================

test_work_log_init_creates_structure() {
    setup

    local output_dir="$TEST_DIR/output"
    mkdir -p "$output_dir"

    work_log_init "$output_dir"

    assert_dir_exists "$output_dir/work-log/default" "Work log directory created"
    assert_file_exists "$output_dir/work-log/default/index.md" "Index file created"

    # Verify index.md has markdown table header
    assert_file_contains "$output_dir/work-log/default/index.md" "| Iteration | Timestamp | Exit Code | Summary |" "Index has table header"

    teardown
}

test_work_log_init_respects_ralph_run_id() {
    setup

    local output_dir="$TEST_DIR/output"
    mkdir -p "$output_dir"

    export RALPH_RUN_ID="test-run-123"

    work_log_init "$output_dir"

    assert_dir_exists "$output_dir/work-log/test-run-123" "Run-specific directory created"
    assert_file_exists "$output_dir/work-log/test-run-123/index.md" "Run-specific index created"

    unset RALPH_RUN_ID
    teardown
}

test_work_log_write_iteration_success() {
    setup

    local output_dir="$TEST_DIR/output"
    mkdir -p "$output_dir"

    work_log_init "$output_dir"

    local summary_text="## Primary Request
Test request summary
## Problem Solving
Made some decisions
## Current Work
Working on feature X
## Pending Tasks
- Task 1
- Task 2"

    work_log_write_iteration "$output_dir" 0 "session-abc" 0 "$summary_text" ""

    assert_file_exists "$output_dir/work-log/default/iteration-0.md" "Iteration file created"

    # Verify content
    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "# Iteration 0" "Iteration header"
    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "**Session:** session-abc" "Session ID"
    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "**Exit Code:** 0" "Exit code"
    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "Completed successfully" "Success outcome"

    # Verify sections extracted
    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "## Context" "Context section"
    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "Test request summary" "Context content"
    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "Made some decisions" "Decisions content"
    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "Working on feature X" "Current work"

    # Verify index updated
    assert_file_contains "$output_dir/work-log/default/index.md" "[0](iteration-0.md)" "Index has link to iteration"

    teardown
}

test_work_log_write_iteration_interrupted() {
    setup

    local output_dir="$TEST_DIR/output"
    mkdir -p "$output_dir"

    work_log_init "$output_dir"

    work_log_write_iteration "$output_dir" 0 "session-def" 130 "Summary text" ""

    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "Interrupted by signal (exit code: 130)" "Interrupted outcome"
    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "Interrupted by signal" "Error section shows interrupted"

    teardown
}

test_work_log_write_iteration_error() {
    setup

    local output_dir="$TEST_DIR/output"
    mkdir -p "$output_dir"

    work_log_init "$output_dir"

    work_log_write_iteration "$output_dir" 0 "session-ghi" 1 "Summary text" ""

    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "Completed with errors (exit code: 1)" "Error outcome"
    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "Exit code: 1" "Error section shows exit code"

    teardown
}

test_work_log_write_iteration_with_file_changes() {
    setup

    local output_dir="$TEST_DIR/output"
    mkdir -p "$output_dir"

    # Create a mock log file with file_path entries
    local log_file="$TEST_DIR/mock-log.jsonl"
    cat > "$log_file" << 'EOF'
{"file_path": "src/main.py", "action": "edit"}
{"file_path": "tests/test_main.py", "action": "edit"}
{"file_path": "README.md", "action": "edit"}
EOF

    work_log_init "$output_dir"

    work_log_write_iteration "$output_dir" 0 "session-jkl" 0 "Summary" "$log_file"

    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "## Files Changed" "Files changed section"
    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "src/main.py" "First file listed"
    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "tests/test_main.py" "Second file listed"
    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "README.md" "Third file listed"

    teardown
}

test_work_log_write_iteration_no_summary() {
    setup

    local output_dir="$TEST_DIR/output"
    mkdir -p "$output_dir"

    work_log_init "$output_dir"

    work_log_write_iteration "$output_dir" 0 "session-mno" 0 "" ""

    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "_No context extracted_" "Empty context placeholder"
    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "_No decisions recorded_" "Empty decisions placeholder"
    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "_No file changes detected_" "Empty files placeholder"

    teardown
}

test_work_log_write_multiple_iterations() {
    setup

    local output_dir="$TEST_DIR/output"
    mkdir -p "$output_dir"

    work_log_init "$output_dir"

    work_log_write_iteration "$output_dir" 0 "session-1" 0 "Iteration 0" ""
    work_log_write_iteration "$output_dir" 1 "session-2" 0 "Iteration 1" ""
    work_log_write_iteration "$output_dir" 2 "session-3" 0 "Iteration 2" ""

    assert_file_exists "$output_dir/work-log/default/iteration-0.md" "Iteration 0 exists"
    assert_file_exists "$output_dir/work-log/default/iteration-1.md" "Iteration 1 exists"
    assert_file_exists "$output_dir/work-log/default/iteration-2.md" "Iteration 2 exists"

    # Verify navigation links
    assert_file_contains "$output_dir/work-log/default/iteration-0.md" "[Next](iteration-1.md)" "Iteration 0 has next link"
    assert_file_contains "$output_dir/work-log/default/iteration-1.md" "[Previous](iteration-0.md)" "Iteration 1 has previous link"
    assert_file_contains "$output_dir/work-log/default/iteration-1.md" "[Next](iteration-2.md)" "Iteration 1 has next link"

    # Verify index has all entries
    local index_count
    index_count=$(grep -c '\[0\](iteration-0.md)' "$output_dir/work-log/default/index.md")
    assert_equals "1" "$index_count" "Index has iteration 0"

    teardown
}

# =============================================================================
# Tests for lib/core/gh-error.sh
# =============================================================================

test_gh_is_network_error_timeout() {
    setup

    local result=0
    gh_is_network_error "124" "" || result=$?
    assert_equals 0 "$result" "Exit 124 is network error"

    teardown
}

test_gh_is_network_error_network_unreachable() {
    setup

    local result=0
    gh_is_network_error "" "Network is unreachable" || result=$?
    assert_equals 0 "$result" "Network is unreachable detected"

    gh_is_network_error "" "network is unreachable" || result=$?
    assert_equals 0 "$result" "Lowercase variant detected"

    teardown
}

test_gh_is_network_error_connection_refused() {
    setup

    local result=0
    gh_is_network_error "" "Connection refused" || result=$?
    assert_equals 0 "$result" "Connection refused detected"

    teardown
}

test_gh_is_network_error_could_not_resolve() {
    setup

    local result=0
    gh_is_network_error "" "Could not resolve host github.com" || result=$?
    assert_equals 0 "$result" "Could not resolve host detected"

    teardown
}

test_gh_is_network_error_502_503() {
    setup

    local result=0
    gh_is_network_error "" "HTTP 502 Bad Gateway" || result=$?
    assert_equals 0 "$result" "HTTP 502 detected"

    gh_is_network_error "" "503 Service Unavailable" || result=$?
    assert_equals 0 "$result" "HTTP 503 detected"

    gh_is_network_error "" "HTTP 504" || result=$?
    assert_equals 0 "$result" "HTTP 504 detected"

    teardown
}

test_gh_is_network_error_ssh_errors() {
    setup

    local result=0
    gh_is_network_error "" "ssh: connect to host github.com port 22: Connection timed out" || result=$?
    assert_equals 0 "$result" "SSH connection error detected"

    gh_is_network_error "" "ssh_exchange_identification: read: Connection reset by peer" || result=$?
    assert_equals 0 "$result" "SSH exchange identification error detected"

    teardown
}

test_gh_is_network_error_not_network_error() {
    setup

    local result=0
    gh_is_network_error "1" "permission denied" || result=$?
    assert_equals 1 "$result" "Permission denied is NOT network error"

    gh_is_network_error "1" "not found" || result=$?
    assert_equals 1 "$result" "Not found is NOT network error"

    gh_is_network_error "0" "" || result=$?
    assert_equals 1 "$result" "Exit 0 is NOT network error"

    teardown
}

test_gh_format_error_network() {
    setup

    local msg
    msg=$(gh_format_error "124" "" "fetching issues")
    assert_output_contains "$msg" "Network timeout" "Timeout message formatted"
    assert_output_contains "$msg" "fetching issues" "Operation included in message"

    msg=$(gh_format_error "1" "Connection refused" "creating PR")
    assert_output_contains "$msg" "Network error" "Network error message formatted"
    assert_output_contains "$msg" "creating PR" "Operation included in message"

    teardown
}

test_gh_format_error_non_network() {
    setup

    local msg
    msg=$(gh_format_error "1" "permission denied" "pushing code")
    assert_output_contains "$msg" "GitHub API error" "API error message formatted"
    assert_output_contains "$msg" "pushing code" "Operation included in message"
    assert_output_contains "$msg" "exit: 1" "Exit code included"

    teardown
}

test_gh_with_network_detection_success() {
    setup

    local output
    output=$(gh_with_network_detection echo "test output")

    assert_equals "test output" "$output" "Command output captured"
    assert_equals "false" "$GH_LAST_WAS_NETWORK_ERROR" "Network error flag is false"

    teardown
}

test_gh_with_network_detection_network_error() {
    setup

    # Use a command that will fail with network-like error
    local exit_code=0
    gh_with_network_detection bash -c 'echo "Network is unreachable" >&2; exit 1' > /dev/null 2>&1 || exit_code=$?

    assert_equals "1" "$exit_code" "Command failed as expected"
    assert_equals "true" "$GH_LAST_WAS_NETWORK_ERROR" "Network error flag is true"

    teardown
}

test_gh_with_network_detection_non_network_error() {
    setup

    local exit_code=0
    gh_with_network_detection bash -c 'echo "permission denied" >&2; exit 1' > /dev/null 2>&1 || exit_code=$?

    assert_equals "1" "$exit_code" "Command failed as expected"
    assert_equals "false" "$GH_LAST_WAS_NETWORK_ERROR" "Network error flag is false"

    teardown
}

test_gh_with_network_detection_flag_cleared() {
    setup

    # Set flag to true
    GH_LAST_WAS_NETWORK_ERROR=true

    # Run successful command
    gh_with_network_detection echo "success" > /dev/null

    assert_equals "false" "$GH_LAST_WAS_NETWORK_ERROR" "Network error flag cleared on success"

    teardown
}

# =============================================================================
# Run all tests
# =============================================================================

run_test test_activity_log_init_creates_directory
run_test test_activity_log_writes_valid_json
run_test test_activity_log_extra_fields
run_test test_activity_log_invalid_task_id_sanitized
run_test test_activity_log_valid_task_id_formats
run_test test_activity_log_empty_worker_and_task
run_test test_activity_log_multiple_lines
run_test test_activity_log_context_update
run_test test_activity_log_not_initialized

run_test test_work_log_init_creates_structure
run_test test_work_log_init_respects_ralph_run_id
run_test test_work_log_write_iteration_success
run_test test_work_log_write_iteration_interrupted
run_test test_work_log_write_iteration_error
run_test test_work_log_write_iteration_with_file_changes
run_test test_work_log_write_iteration_no_summary
run_test test_work_log_write_multiple_iterations

run_test test_gh_is_network_error_timeout
run_test test_gh_is_network_error_network_unreachable
run_test test_gh_is_network_error_connection_refused
run_test test_gh_is_network_error_could_not_resolve
run_test test_gh_is_network_error_502_503
run_test test_gh_is_network_error_ssh_errors
run_test test_gh_is_network_error_not_network_error
run_test test_gh_format_error_network
run_test test_gh_format_error_non_network
run_test test_gh_with_network_detection_success
run_test test_gh_with_network_detection_network_error
run_test test_gh_with_network_detection_non_network_error
run_test test_gh_with_network_detection_flag_cleared

print_test_summary
exit_with_test_result
