#!/usr/bin/env bash
# Tests for wiggum validate command

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

# =============================================================================
# Valid Kanban Tests
# =============================================================================

test_valid_simple_kanban() {
    assert_success \
        "$WIGGUM_HOME/bin/wiggum-validate -f $WIGGUM_HOME/config/examples/simple-kanban.md" \
        "Simple kanban file should be valid"
}

test_valid_webapp_kanban() {
    assert_success \
        "$WIGGUM_HOME/bin/wiggum-validate -f $WIGGUM_HOME/config/examples/web-app-kanban.md" \
        "Web app kanban file should be valid"
}

# =============================================================================
# Missing Required Fields Tests
# =============================================================================

test_missing_description() {
    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" -f "$FIXTURES_DIR/invalid-kanban-missing-fields.md" 2>&1)
    local exit_code=$?

    assert_equals "1" "$exit_code" "Should fail with exit code 1 for missing fields"
    assert_output_contains "$output" "missing required field: Description" "Should report missing Description"
    assert_output_contains "$output" "missing required field: Priority" "Should report missing Priority"
}

# =============================================================================
# Malformed Task ID Tests
# =============================================================================

test_malformed_task_ids() {
    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" -f "$FIXTURES_DIR/invalid-kanban-bad-ids.md" 2>&1)
    local exit_code=$?

    assert_equals "1" "$exit_code" "Should fail with exit code 1 for malformed IDs"
    assert_output_contains "$output" "Malformed task ID 'T-001'" "Should detect prefix too short"
    assert_output_contains "$output" "Malformed task ID 'VERYLONGPREFIX-001'" "Should detect prefix too long"
    assert_output_contains "$output" "Malformed task ID 'TASK-abc'" "Should detect non-numeric ID"
}

# =============================================================================
# Duplicate Task ID Tests
# =============================================================================

test_duplicate_task_ids() {
    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" -f "$FIXTURES_DIR/invalid-kanban-duplicate-ids.md" 2>&1)
    local exit_code=$?

    assert_equals "1" "$exit_code" "Should fail with exit code 1 for duplicate IDs"
    assert_output_contains "$output" "Duplicate task ID 'TASK-001'" "Should detect duplicate task ID"
    assert_output_contains "$output" "first occurrence at line" "Should include line number of first occurrence"
}

# =============================================================================
# Invalid Priority Tests
# =============================================================================

test_invalid_priority() {
    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" -f "$FIXTURES_DIR/invalid-kanban-bad-priority.md" 2>&1)
    local exit_code=$?

    assert_equals "1" "$exit_code" "Should fail with exit code 1 for invalid priority"
    assert_output_contains "$output" "Invalid priority 'CRITICAL'" "Should detect invalid priority value"
    assert_output_contains "$output" "Invalid priority 'high'" "Should detect lowercase priority"
    assert_output_contains "$output" "must be HIGH, MEDIUM, or LOW" "Should include valid values in error"
}

# =============================================================================
# Dependency Validation Tests
# =============================================================================

test_non_existent_dependencies() {
    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" -f "$FIXTURES_DIR/invalid-kanban-bad-deps.md" 2>&1)
    local exit_code=$?

    assert_equals "1" "$exit_code" "Should fail with exit code 1 for bad dependencies"
    assert_output_contains "$output" "references non-existent dependency 'TASK-999'" "Should detect single missing dependency"
    assert_output_contains "$output" "references non-existent dependency 'TASK-100'" "Should detect first missing dependency in list"
    assert_output_contains "$output" "references non-existent dependency 'TASK-200'" "Should detect second missing dependency in list"
}

# =============================================================================
# Missing TASKS Section Tests
# =============================================================================

test_missing_tasks_section() {
    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" -f "$FIXTURES_DIR/invalid-kanban-no-section.md" 2>&1)
    local exit_code=$?

    assert_equals "1" "$exit_code" "Should fail with exit code 1 for missing TASKS section"
    assert_output_contains "$output" "Missing required '## TASKS' section header" "Should report missing TASKS section"
}

# =============================================================================
# Line Number Reporting Tests
# =============================================================================

test_line_numbers_in_errors() {
    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" -f "$FIXTURES_DIR/invalid-kanban-missing-fields.md" 2>&1)

    assert_output_contains "$output" "Line 5:" "Should include line number for first task error"
    assert_output_contains "$output" "Line 9:" "Should include line number for second task error"
}

# =============================================================================
# Exit Code Tests
# =============================================================================

test_exit_code_zero_on_valid() {
    "$WIGGUM_HOME/bin/wiggum-validate" -f "$WIGGUM_HOME/config/examples/simple-kanban.md" >/dev/null 2>&1
    local exit_code=$?
    assert_equals "0" "$exit_code" "Should exit 0 on valid kanban"
}

test_exit_code_one_on_invalid() {
    "$WIGGUM_HOME/bin/wiggum-validate" -f "$FIXTURES_DIR/invalid-kanban-missing-fields.md" >/dev/null 2>&1
    local exit_code=$?
    assert_equals "1" "$exit_code" "Should exit 1 on invalid kanban"
}

test_exit_code_two_on_missing_file() {
    "$WIGGUM_HOME/bin/wiggum-validate" -f "$FIXTURES_DIR/nonexistent.md" >/dev/null 2>&1
    local exit_code=$?
    assert_equals "2" "$exit_code" "Should exit 2 on missing file"
}

# =============================================================================
# Quiet Mode Tests
# =============================================================================

test_quiet_mode_no_success_message() {
    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" -q -f "$WIGGUM_HOME/config/examples/simple-kanban.md" 2>&1)

    assert_equals "" "$output" "Quiet mode should produce no output on success"
}

test_quiet_mode_shows_errors() {
    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" -q -f "$FIXTURES_DIR/invalid-kanban-missing-fields.md" 2>&1)

    assert_output_contains "$output" "Validation failed" "Quiet mode should still show errors"
}

# =============================================================================
# Help Option Tests
# =============================================================================

test_help_option() {
    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" --help 2>&1)
    local exit_code=$?

    assert_equals "0" "$exit_code" "Help should exit 0"
    assert_output_contains "$output" "wiggum validate" "Help should show command name"
    assert_output_contains "$output" "Validates:" "Help should list what is validated"
}

# =============================================================================
# Run All Tests
# =============================================================================

run_test test_valid_simple_kanban
run_test test_valid_webapp_kanban
run_test test_missing_description
run_test test_malformed_task_ids
run_test test_duplicate_task_ids
run_test test_invalid_priority
run_test test_non_existent_dependencies
run_test test_missing_tasks_section
run_test test_line_numbers_in_errors
run_test test_exit_code_zero_on_valid
run_test test_exit_code_one_on_invalid
run_test test_exit_code_two_on_missing_file
run_test test_quiet_mode_no_success_message
run_test test_quiet_mode_shows_errors
run_test test_help_option

print_test_summary
exit_with_test_result
