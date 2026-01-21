#!/usr/bin/env bash
# Test the test framework itself

set -e

# Get the script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/test-framework.sh"

# Test: Fixture loading
test_fixture_loading() {
    local fixture_content
    fixture_content=$(load_fixture "simple-kanban.md")
    assert_output_contains "$fixture_content" "TASK-001" "Fixture should contain TASK-001"
    assert_output_contains "$fixture_content" "Create README file" "Fixture should contain task description"
}

# Test: Assertion functions work correctly
test_assertions() {
    # Test assert_equals
    assert_equals "hello" "hello" "Equal strings should pass"

    # Test assert_not_equals
    assert_not_equals "hello" "world" "Different strings should pass"

    # Test assert_success
    assert_success "true" "True command should succeed"

    # Test assert_failure
    assert_failure "false" "False command should fail"
}

# Test: File operations
test_file_operations() {
    local test_file="$TEST_TEMP_DIR/test.txt"
    echo "test content" > "$test_file"

    assert_file_exists "$test_file" "Test file should exist"
    assert_file_contains "$test_file" "test content" "File should contain expected content"

    rm "$test_file"
    assert_file_not_exists "$test_file" "Test file should be removed"
}

# Test: Directory operations
test_directory_operations() {
    local test_dir="$TEST_TEMP_DIR/testdir"
    mkdir -p "$test_dir"

    assert_dir_exists "$test_dir" "Test directory should exist"

    rmdir "$test_dir"
}

# Test: Copy fixture
test_copy_fixture() {
    local dest_file="$TEST_TEMP_DIR/copied-kanban.md"
    copy_fixture "simple-kanban.md" "$dest_file"

    assert_file_exists "$dest_file" "Copied fixture should exist"
    assert_file_contains "$dest_file" "TASK-001" "Copied fixture should contain content"
}

# Test: Numeric comparisons
test_numeric_comparisons() {
    assert_greater_than 10 5 "10 should be greater than 5"
    assert_greater_than 100 0 "100 should be greater than 0"
}

# Run all tests
run_test test_fixture_loading
run_test test_assertions
run_test test_file_operations
run_test test_directory_operations
run_test test_copy_fixture
run_test test_numeric_comparisons

# Print summary and exit
print_test_summary
exit_with_test_result
