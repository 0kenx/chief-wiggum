#!/usr/bin/env bash
set -euo pipefail
# Tests for wiggum validate command

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/core/exit-codes.sh"

# =============================================================================
# Valid Kanban Tests
# =============================================================================

test_valid_simple_kanban() {
    assert_success "Simple kanban file should be valid" \
        "$WIGGUM_HOME/bin/wiggum-validate" -f "$WIGGUM_HOME/config/examples/simple-kanban.md"
}

test_valid_webapp_kanban() {
    assert_success "Web app kanban file should be valid" \
        "$WIGGUM_HOME/bin/wiggum-validate" -f "$WIGGUM_HOME/config/examples/web-app-kanban.md"
}

# =============================================================================
# Missing Required Fields Tests
# =============================================================================

test_missing_description() {
    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" -f "$FIXTURES_DIR/invalid-kanban-missing-fields.md" 2>&1)
    local exit_code=$?

    assert_equals "$EXIT_VALIDATE_ERRORS_FOUND" "$exit_code" "Should fail with exit code $EXIT_VALIDATE_ERRORS_FOUND for missing fields"
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

    assert_equals "$EXIT_VALIDATE_ERRORS_FOUND" "$exit_code" "Should fail with exit code $EXIT_VALIDATE_ERRORS_FOUND for malformed IDs"
    assert_output_contains "$output" "Malformed task ID 'T-001'" "Should detect prefix too short"
    assert_output_contains "$output" "Malformed task ID 'VERYLONGPREFIX-001'" "Should detect prefix too long"
    assert_output_contains "$output" "Malformed task ID 'TASK-abc'" "Should detect non-numeric ID"
    assert_output_contains "$output" "Malformed task ID 'TASK-12345'" "Should detect number too long"
}

# =============================================================================
# Duplicate Task ID Tests
# =============================================================================

test_duplicate_task_ids() {
    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" -f "$FIXTURES_DIR/invalid-kanban-duplicate-ids.md" 2>&1)
    local exit_code=$?

    assert_equals "$EXIT_VALIDATE_ERRORS_FOUND" "$exit_code" "Should fail with exit code $EXIT_VALIDATE_ERRORS_FOUND for duplicate IDs"
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

    assert_equals "$EXIT_VALIDATE_ERRORS_FOUND" "$exit_code" "Should fail with exit code $EXIT_VALIDATE_ERRORS_FOUND for invalid priority"
    # Note: CRITICAL is now a valid priority, so test fixture may need adjustment
    # Test that lowercase priorities are detected as invalid
    assert_output_contains "$output" "Invalid priority 'high'" "Should detect lowercase priority"
    assert_output_contains "$output" "must be" "Should include valid values hint in error"
}

# =============================================================================
# Dependency Validation Tests
# =============================================================================

test_non_existent_dependencies() {
    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" -f "$FIXTURES_DIR/invalid-kanban-bad-deps.md" 2>&1)
    local exit_code=$?

    assert_equals "$EXIT_VALIDATE_ERRORS_FOUND" "$exit_code" "Should fail with exit code $EXIT_VALIDATE_ERRORS_FOUND for bad dependencies"
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

    assert_equals "$EXIT_VALIDATE_ERRORS_FOUND" "$exit_code" "Should fail with exit code $EXIT_VALIDATE_ERRORS_FOUND for missing TASKS section"
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

test_exit_code_on_invalid() {
    "$WIGGUM_HOME/bin/wiggum-validate" -f "$FIXTURES_DIR/invalid-kanban-missing-fields.md" >/dev/null 2>&1
    local exit_code=$?
    assert_equals "$EXIT_VALIDATE_ERRORS_FOUND" "$exit_code" "Should exit $EXIT_VALIDATE_ERRORS_FOUND on invalid kanban"
}

test_exit_code_on_missing_file() {
    "$WIGGUM_HOME/bin/wiggum-validate" -f "$FIXTURES_DIR/nonexistent.md" >/dev/null 2>&1
    local exit_code=$?
    assert_equals "$EXIT_VALIDATE_FILE_NOT_FOUND" "$exit_code" "Should exit $EXIT_VALIDATE_FILE_NOT_FOUND on missing file"
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
# Cleanup Subcommand Tests
# =============================================================================

test_cleanup_collapses_completed() {
    local tmp_dir
    tmp_dir=$(create_test_dir)
    cp "$FIXTURES_DIR/kanban-cleanup-mixed.md" "$tmp_dir/kanban.md"

    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" cleanup -f "$tmp_dir/kanban.md" 2>&1)
    local exit_code=$?

    assert_equals "0" "$exit_code" "Cleanup should exit 0"
    # Completed task blocks should be gone
    assert_file_not_contains "$tmp_dir/kanban.md" "- [x] **[TASK-001]**" "TASK-001 block should be collapsed"
    assert_file_not_contains "$tmp_dir/kanban.md" "- [x] **[TASK-004]**" "TASK-004 block should be collapsed"
    # IDs preserved in done comment
    assert_file_contains "$tmp_dir/kanban.md" "<!-- done: TASK-001, TASK-004 -->" "Done comment should list collapsed IDs"

    rm -rf "$tmp_dir"
}

test_cleanup_keeps_non_completed() {
    local tmp_dir
    tmp_dir=$(create_test_dir)
    cp "$FIXTURES_DIR/kanban-cleanup-mixed.md" "$tmp_dir/kanban.md"

    "$WIGGUM_HOME/bin/wiggum-validate" cleanup -f "$tmp_dir/kanban.md" >/dev/null 2>&1

    assert_file_contains "$tmp_dir/kanban.md" "**[TASK-002]**" "TASK-002 (failed) should remain"
    assert_file_contains "$tmp_dir/kanban.md" "**[TASK-003]**" "TASK-003 (pending) should remain"
    assert_file_contains "$tmp_dir/kanban.md" "**[TASK-005]**" "TASK-005 (in-progress) should remain"

    rm -rf "$tmp_dir"
}

test_cleanup_all_completed() {
    local tmp_dir
    tmp_dir=$(create_test_dir)
    cp "$FIXTURES_DIR/kanban-all-complete.md" "$tmp_dir/kanban.md"

    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" cleanup -f "$tmp_dir/kanban.md" 2>&1)
    local exit_code=$?

    assert_equals "0" "$exit_code" "Cleanup should exit 0 when all tasks collapsed"
    assert_file_contains "$tmp_dir/kanban.md" "## TASKS" "TASKS section header should be preserved"
    assert_file_contains "$tmp_dir/kanban.md" "<!-- done: TASK-001, TASK-002 -->" "Done comment should list all IDs"
    assert_file_not_contains "$tmp_dir/kanban.md" "- [x]" "No [x] task blocks should remain"

    rm -rf "$tmp_dir"
}

test_cleanup_no_completed() {
    local tmp_dir
    tmp_dir=$(create_test_dir)
    # Create a kanban with no completed tasks
    cat > "$tmp_dir/kanban.md" << 'EOF'
# Kanban Board

## TASKS

- [ ] **[TASK-001]** Pending task
  - Description: Not done yet
  - Priority: HIGH
  - Dependencies: none
EOF

    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" cleanup -f "$tmp_dir/kanban.md" 2>&1)
    local exit_code=$?

    assert_equals "0" "$exit_code" "Cleanup should exit 0 when no completed tasks"
    assert_output_contains "$output" "No completed tasks to clean up" "Should report no completed tasks"

    rm -rf "$tmp_dir"
}

test_cleanup_quiet_mode() {
    local tmp_dir
    tmp_dir=$(create_test_dir)
    cp "$FIXTURES_DIR/kanban-cleanup-mixed.md" "$tmp_dir/kanban.md"

    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" cleanup -q -f "$tmp_dir/kanban.md" 2>&1)

    assert_equals "" "$output" "Quiet mode should produce no output on success"

    rm -rf "$tmp_dir"
}

test_cleanup_file_not_found() {
    "$WIGGUM_HOME/bin/wiggum-validate" cleanup -f "$FIXTURES_DIR/nonexistent.md" >/dev/null 2>&1
    local exit_code=$?
    assert_equals "$EXIT_VALIDATE_FILE_NOT_FOUND" "$exit_code" "Should exit $EXIT_VALIDATE_FILE_NOT_FOUND for missing file"
}

test_cleanup_reports_collapsed_ids() {
    local tmp_dir
    tmp_dir=$(create_test_dir)
    cp "$FIXTURES_DIR/kanban-cleanup-mixed.md" "$tmp_dir/kanban.md"

    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" cleanup -f "$tmp_dir/kanban.md" 2>&1)

    assert_output_contains "$output" "Collapsed 2 completed task(s)" "Should report number of collapsed tasks"
    assert_output_contains "$output" "TASK-001" "Should list collapsed TASK-001"
    assert_output_contains "$output" "TASK-004" "Should list collapsed TASK-004"

    rm -rf "$tmp_dir"
}

# =============================================================================
# Cleanup with Sub-headings Tests
# =============================================================================

test_cleanup_sections_collapses_per_section() {
    local tmp_dir
    tmp_dir=$(create_test_dir)
    cp "$FIXTURES_DIR/kanban-cleanup-sections.md" "$tmp_dir/kanban.md"

    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" cleanup -f "$tmp_dir/kanban.md" 2>&1)
    local exit_code=$?

    assert_equals "0" "$exit_code" "Cleanup should exit 0"
    # Completed blocks should be gone
    assert_file_not_contains "$tmp_dir/kanban.md" "- [x] **[TASK-001]**" "TASK-001 block should be collapsed"
    assert_file_not_contains "$tmp_dir/kanban.md" "- [x] **[TASK-003]**" "TASK-003 block should be collapsed"
    assert_file_not_contains "$tmp_dir/kanban.md" "- [x] **[TASK-004]**" "TASK-004 block should be collapsed"
    # Section headings preserved
    assert_file_contains "$tmp_dir/kanban.md" "### Critical" "Critical section heading should be preserved"
    assert_file_contains "$tmp_dir/kanban.md" "### High" "High section heading should be preserved"
    assert_file_contains "$tmp_dir/kanban.md" "### Medium" "Medium section heading should be preserved"
    # Single done comment at top with all collapsed IDs
    assert_file_contains "$tmp_dir/kanban.md" "<!-- done: TASK-001, TASK-003, TASK-004 -->" "Done comment should list all collapsed IDs at top"
    # Non-completed tasks remain
    assert_file_contains "$tmp_dir/kanban.md" "**[TASK-002]**" "TASK-002 (pending) should remain"
    assert_file_contains "$tmp_dir/kanban.md" "**[TASK-005]**" "TASK-005 (pending) should remain"
    assert_file_contains "$tmp_dir/kanban.md" "**[TASK-006]**" "TASK-006 (pending) should remain"

    rm -rf "$tmp_dir"
}

test_cleanup_sections_all_completed_in_section() {
    local tmp_dir
    tmp_dir=$(create_test_dir)
    # Create kanban where one section has all tasks completed
    cat > "$tmp_dir/kanban.md" << 'EOF'
# Kanban Board

## TASKS

### Phase 1

- [x] **[TASK-001]** Done task
  - Description: Completed
  - Priority: HIGH
  - Dependencies: none

- [x] **[TASK-002]** Also done
  - Description: Completed too
  - Priority: HIGH
  - Dependencies: none

### Phase 2

- [ ] **[TASK-003]** Pending task
  - Description: Not started
  - Priority: MEDIUM
  - Dependencies: none
EOF

    "$WIGGUM_HOME/bin/wiggum-validate" cleanup -f "$tmp_dir/kanban.md" >/dev/null 2>&1

    # Phase 1 heading should be deleted (no remaining tasks)
    assert_file_not_contains "$tmp_dir/kanban.md" "### Phase 1" "Empty section heading should be deleted"
    assert_file_contains "$tmp_dir/kanban.md" "<!-- done: TASK-001, TASK-002 -->" "Done comment should list all IDs at top"
    # Phase 2 should be untouched
    assert_file_contains "$tmp_dir/kanban.md" "### Phase 2" "Phase 2 heading should remain"
    assert_file_contains "$tmp_dir/kanban.md" "**[TASK-003]**" "Pending task should remain"

    rm -rf "$tmp_dir"
}

test_cleanup_sections_no_headings_still_works() {
    local tmp_dir
    tmp_dir=$(create_test_dir)
    cp "$FIXTURES_DIR/kanban-cleanup-mixed.md" "$tmp_dir/kanban.md"

    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" cleanup -f "$tmp_dir/kanban.md" 2>&1)
    local exit_code=$?

    assert_equals "0" "$exit_code" "Cleanup should still work without sub-headings"
    assert_file_contains "$tmp_dir/kanban.md" "<!-- done: TASK-001, TASK-004 -->" "Done comment should list collapsed IDs"
    assert_file_contains "$tmp_dir/kanban.md" "**[TASK-002]**" "Non-completed tasks should remain"

    rm -rf "$tmp_dir"
}

test_cleanup_sections_reports_all_collapsed() {
    local tmp_dir
    tmp_dir=$(create_test_dir)
    cp "$FIXTURES_DIR/kanban-cleanup-sections.md" "$tmp_dir/kanban.md"

    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" cleanup -f "$tmp_dir/kanban.md" 2>&1)

    assert_output_contains "$output" "Collapsed 3 completed task(s)" "Should report total collapsed count across sections"
    assert_output_contains "$output" "TASK-001" "Should list TASK-001"
    assert_output_contains "$output" "TASK-003" "Should list TASK-003"
    assert_output_contains "$output" "TASK-004" "Should list TASK-004"

    rm -rf "$tmp_dir"
}

# =============================================================================
# Cleanup with ## Level Headings Tests
# =============================================================================

test_cleanup_h2_sections_collapses_across_sections() {
    local tmp_dir
    tmp_dir=$(create_test_dir)
    cat > "$tmp_dir/kanban.md" << 'EOF'
# Kanban Board

## TASKS

- [P] **[TASK-001]** Pending approval task
  - Description: Awaiting review
  - Priority: HIGH
  - Dependencies: none

## Feature Work

- [x] **[TASK-002]** Completed feature
  - Description: Feature is done
  - Priority: HIGH
  - Dependencies: none

- [ ] **[TASK-003]** Pending feature
  - Description: Not started
  - Priority: MEDIUM
  - Dependencies: TASK-002

## Bug Fixes

- [x] **[TASK-004]** Fixed bug
  - Description: Bug resolved
  - Priority: CRITICAL
  - Dependencies: none

- [x] **[TASK-005]** Another fixed bug
  - Description: Also resolved
  - Priority: HIGH
  - Dependencies: none
EOF

    local output
    output=$("$WIGGUM_HOME/bin/wiggum-validate" cleanup -f "$tmp_dir/kanban.md" 2>&1)
    local exit_code=$?

    assert_equals "0" "$exit_code" "Cleanup should exit 0 with ## sections"
    # Completed blocks should be gone
    assert_file_not_contains "$tmp_dir/kanban.md" "- [x] **[TASK-002]**" "TASK-002 block should be collapsed"
    assert_file_not_contains "$tmp_dir/kanban.md" "- [x] **[TASK-004]**" "TASK-004 block should be collapsed"
    assert_file_not_contains "$tmp_dir/kanban.md" "- [x] **[TASK-005]**" "TASK-005 block should be collapsed"
    # Feature Work kept (has pending task), Bug Fixes deleted (all completed)
    assert_file_contains "$tmp_dir/kanban.md" "## Feature Work" "Feature Work heading should be preserved"
    assert_file_not_contains "$tmp_dir/kanban.md" "## Bug Fixes" "Bug Fixes heading should be deleted (all tasks completed)"
    # Single done comment at top
    assert_file_contains "$tmp_dir/kanban.md" "<!-- done: TASK-002, TASK-004, TASK-005 -->" "Done comment should list all collapsed IDs at top"
    # Non-completed tasks remain
    assert_file_contains "$tmp_dir/kanban.md" "**[TASK-001]**" "TASK-001 (pending approval) should remain"
    assert_file_contains "$tmp_dir/kanban.md" "**[TASK-003]**" "TASK-003 (pending) should remain"
    # Report collapsed count
    assert_output_contains "$output" "Collapsed 3 completed task(s)" "Should report 3 collapsed tasks"

    rm -rf "$tmp_dir"
}

test_cleanup_mixed_h2_h3_sections() {
    local tmp_dir
    tmp_dir=$(create_test_dir)
    cat > "$tmp_dir/kanban.md" << 'EOF'
# Kanban Board

## TASKS

- [ ] **[TASK-001]** Top-level task
  - Description: Before any sub-section
  - Priority: HIGH
  - Dependencies: none

## Spec Compliance

### Critical

- [x] **[TASK-002]** Critical spec task
  - Description: Spec compliance work
  - Priority: CRITICAL
  - Dependencies: none

### Medium

- [x] **[TASK-003]** Medium spec task
  - Description: Less urgent spec work
  - Priority: MEDIUM
  - Dependencies: TASK-002

- [ ] **[TASK-004]** Pending spec task
  - Description: Not started
  - Priority: MEDIUM
  - Dependencies: TASK-002
EOF

    "$WIGGUM_HOME/bin/wiggum-validate" cleanup -f "$tmp_dir/kanban.md" >/dev/null 2>&1

    # ## Spec Compliance kept (has child ### Medium with tasks), ### Critical deleted (all completed)
    assert_file_contains "$tmp_dir/kanban.md" "## Spec Compliance" "## heading preserved (has child sections with tasks)"
    assert_file_not_contains "$tmp_dir/kanban.md" "### Critical" "### Critical deleted (all tasks completed)"
    assert_file_contains "$tmp_dir/kanban.md" "### Medium" "### heading should be preserved"
    # Tasks collapsed per section
    assert_file_not_contains "$tmp_dir/kanban.md" "- [x] **[TASK-002]**" "TASK-002 should be collapsed"
    assert_file_not_contains "$tmp_dir/kanban.md" "- [x] **[TASK-003]**" "TASK-003 should be collapsed"
    # Non-completed preserved
    assert_file_contains "$tmp_dir/kanban.md" "**[TASK-001]**" "TASK-001 (pending) should remain"
    assert_file_contains "$tmp_dir/kanban.md" "**[TASK-004]**" "TASK-004 (pending) should remain"

    rm -rf "$tmp_dir"
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
run_test test_exit_code_on_invalid
run_test test_exit_code_on_missing_file
run_test test_quiet_mode_no_success_message
run_test test_quiet_mode_shows_errors
run_test test_help_option
run_test test_cleanup_collapses_completed
run_test test_cleanup_keeps_non_completed
run_test test_cleanup_all_completed
run_test test_cleanup_no_completed
run_test test_cleanup_quiet_mode
run_test test_cleanup_file_not_found
run_test test_cleanup_reports_collapsed_ids
run_test test_cleanup_sections_collapses_per_section
run_test test_cleanup_sections_all_completed_in_section
run_test test_cleanup_sections_no_headings_still_works
run_test test_cleanup_sections_reports_all_collapsed
run_test test_cleanup_h2_sections_collapses_across_sections
run_test test_cleanup_mixed_h2_h3_sections

print_test_summary
exit_with_test_result
