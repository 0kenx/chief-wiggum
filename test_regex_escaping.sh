#!/usr/bin/env bash
# Test script for regex escaping in task IDs
# Tests edge cases: dots, brackets, slashes, asterisks, etc.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/lib/string-utils.sh"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Test counter
TESTS_PASSED=0
TESTS_FAILED=0

# Test sed pattern matching with escaped task IDs
test_sed_pattern() {
    local task_id="$1"
    local test_name="$2"

    # Create a temporary test file
    local temp_file=$(mktemp)
    echo "- [ ] **[$task_id]** Test task description" > "$temp_file"

    # Try to match and replace using escaped task_id
    local escaped_task_id=$(escape_regex_chars "$task_id")

    # Use | as delimiter for sed to avoid issues with forward slashes in task IDs
    if sed -i "s|- \[[^\]]*\] \*\*\[$escaped_task_id\]\*\*|- [x] **[$task_id]**|" "$temp_file" 2>/dev/null; then
        # Check if the replacement worked (use literal string matching)
        local result=$(cat "$temp_file")
        if [[ "$result" == "- [x] **[$task_id]** Test task description" ]]; then
            echo -e "${GREEN}✓${NC} PASS: sed pattern with task_id '$task_id' ($test_name)"
            ((TESTS_PASSED++))
        else
            echo -e "${RED}✗${NC} FAIL: sed replacement didn't work for task_id '$task_id' ($test_name)"
            echo "  Expected escaped: $escaped_task_id"
            echo "  File contents: $result"
            ((TESTS_FAILED++))
        fi
    else
        echo -e "${RED}✗${NC} FAIL: sed command failed for task_id '$task_id' ($test_name)"
        echo "  Escaped task_id: $escaped_task_id"
        ((TESTS_FAILED++))
    fi

    rm -f "$temp_file"
}

echo "========================================"
echo "Testing sed pattern matching"
echo "========================================"
echo

# Test sed patterns with various task IDs (focusing on the actual edge cases from the PRD)
test_sed_pattern "TASK-001" "simple task ID"
test_sed_pattern "TASK.001" "task ID with dot"
test_sed_pattern "TASK[001]" "task ID with brackets"
test_sed_pattern "TASK*001" "task ID with asterisk"
test_sed_pattern "TASK/001" "task ID with slash"
test_sed_pattern "TASK^001" "task ID with caret"
test_sed_pattern "TASK\$001" "task ID with dollar sign"
test_sed_pattern "TASK-[1.0]" "complex task ID with brackets and dots"
test_sed_pattern "v1.2.3-rc.1" "version-like task ID"

# Test the actual functions used in file-lock.sh and worker.sh
echo
echo "========================================"
echo "Testing actual usage patterns"
echo "========================================"
echo

# Test kanban update pattern (from file-lock.sh)
test_kanban_update() {
    local task_id="$1"
    local test_name="$2"

    local temp_file=$(mktemp)
    echo "- [ ] **[$task_id]** Test task" > "$temp_file"

    local escaped_task_id=$(escape_regex_chars "$task_id")
    local new_status="x"

    # Use | as delimiter for sed to avoid issues with forward slashes
    if sed -i "s|- \[[^\]]*\] \*\*\[$escaped_task_id\]\*\*|- [$new_status] **[$task_id]**|" "$temp_file" 2>/dev/null; then
        local result=$(cat "$temp_file")
        if [[ "$result" == "- [x] **[$task_id]** Test task" ]]; then
            echo -e "${GREEN}✓${NC} PASS: kanban update for '$task_id' ($test_name)"
            ((TESTS_PASSED++))
        else
            echo -e "${RED}✗${NC} FAIL: kanban update failed for '$task_id' ($test_name)"
            echo "  File contents: $result"
            ((TESTS_FAILED++))
        fi
    else
        echo -e "${RED}✗${NC} FAIL: sed failed for '$task_id' ($test_name)"
        ((TESTS_FAILED++))
    fi

    rm -f "$temp_file"
}

test_kanban_update "TASK.001" "kanban with dot"
test_kanban_update "TASK[001]" "kanban with brackets"
test_kanban_update "TASK/001" "kanban with slash"

# Test task description extraction pattern (from worker.sh)
test_desc_extraction() {
    local task_id="$1"
    local test_name="$2"

    local temp_file=$(mktemp)
    echo "- [ ] **[$task_id]** This is the task description" > "$temp_file"

    local escaped_task_id=$(escape_regex_chars "$task_id")
    # Use | as delimiter for sed to avoid issues with forward slashes
    local result=$(sed "s|.*\*\*\[$escaped_task_id\]\*\* ||" "$temp_file")

    if [ "$result" = "This is the task description" ]; then
        echo -e "${GREEN}✓${NC} PASS: description extraction for '$task_id' ($test_name)"
        ((TESTS_PASSED++))
    else
        echo -e "${RED}✗${NC} FAIL: description extraction failed for '$task_id' ($test_name)"
        echo "  Expected: 'This is the task description'"
        echo "  Got: '$result'"
        ((TESTS_FAILED++))
    fi

    rm -f "$temp_file"
}

test_desc_extraction "TASK.001" "description with dot"
test_desc_extraction "TASK[001]" "description with brackets"
test_desc_extraction "TASK/001" "description with slash"

echo
echo "========================================"
echo "Test Summary"
echo "========================================"
echo -e "${GREEN}Passed: $TESTS_PASSED${NC}"
echo -e "${RED}Failed: $TESTS_FAILED${NC}"
echo

if [ $TESTS_FAILED -eq 0 ]; then
    echo -e "${GREEN}All tests passed!${NC}"
    exit 0
else
    echo -e "${RED}Some tests failed!${NC}"
    exit 1
fi
