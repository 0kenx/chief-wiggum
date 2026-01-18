#!/usr/bin/env bash
# Test script for regex escaping functionality

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/lib/task-parser.sh"
source "$SCRIPT_DIR/lib/file-lock.sh"

# Colors for output
GREEN='\033[0;32m'
RED='\033[0;31m'
NC='\033[0m' # No Color

test_count=0
pass_count=0
fail_count=0

run_test() {
    local test_name="$1"
    local task_id="$2"
    local expected_pattern="$3"

    ((test_count++))
    echo "----------------------------------------"
    echo "Test $test_count: $test_name"
    echo "Task ID: $task_id"

    # Test escape_regex_chars (BRE)
    local escaped=$(escape_regex_chars "$task_id")
    echo "Escaped (BRE): $escaped"
    echo "Expected: $expected_pattern"

    if [ "$escaped" = "$expected_pattern" ]; then
        echo -e "${GREEN}✓ PASS${NC}: Escaping correct"
        ((pass_count++))
    else
        echo -e "${RED}✗ FAIL${NC}: Escaping incorrect"
        ((fail_count++))
        return
    fi

    # Test in actual sed pattern matching
    local test_file=$(mktemp)
    echo "- [ ] **[$task_id]** Test task description" > "$test_file"

    # Try to match with escaped pattern
    if sed -n "s/- \[[^\]]*\] \*\*\[$escaped\]\*\*/MATCHED/p" "$test_file" | grep -q "MATCHED"; then
        echo -e "${GREEN}✓ PASS${NC}: sed pattern matching works"
        ((pass_count++))
    else
        echo -e "${RED}✗ FAIL${NC}: sed pattern matching failed"
        ((fail_count++))
        rm "$test_file"
        return
    fi

    # Test replacement with escaped pattern
    sed -i "s/- \[[^\]]*\] \*\*\[$escaped\]\*\*/- [x] **[$task_id]**/" "$test_file"

    if grep -q "- \[x\] \*\*\[$task_id\]\*\*" "$test_file"; then
        echo -e "${GREEN}✓ PASS${NC}: sed replacement works"
        ((pass_count++))
    else
        echo -e "${RED}✗ FAIL${NC}: sed replacement failed"
        echo "File contents: $(cat $test_file)"
        ((fail_count++))
        rm "$test_file"
        return
    fi

    rm "$test_file"
    echo -e "${GREEN}✓ All checks passed for this test${NC}"
}

run_ere_test() {
    local test_name="$1"
    local task_id="$2"
    local expected_pattern="$3"

    ((test_count++))
    echo "----------------------------------------"
    echo "Test $test_count: $test_name (ERE)"
    echo "Task ID: $task_id"

    # Test escape_regex_chars_ere (ERE)
    local escaped=$(escape_regex_chars_ere "$task_id")
    echo "Escaped (ERE): $escaped"
    echo "Expected: $expected_pattern"

    if [ "$escaped" = "$expected_pattern" ]; then
        echo -e "${GREEN}✓ PASS${NC}: ERE escaping correct"
        ((pass_count++))
    else
        echo -e "${RED}✗ FAIL${NC}: ERE escaping incorrect"
        ((fail_count++))
        return
    fi

    # Test in awk pattern matching
    local test_file=$(mktemp)
    echo "**[$task_id]** Test task description" > "$test_file"

    if awk "/\*\*\[$escaped\]\*\*/ {print \"MATCHED\"}" "$test_file" | grep -q "MATCHED"; then
        echo -e "${GREEN}✓ PASS${NC}: awk pattern matching works"
        ((pass_count++))
    else
        echo -e "${RED}✗ FAIL${NC}: awk pattern matching failed"
        ((fail_count++))
        rm "$test_file"
        return
    fi

    rm "$test_file"
    echo -e "${GREEN}✓ All checks passed for this ERE test${NC}"
}

echo "========================================"
echo "REGEX ESCAPING TEST SUITE"
echo "========================================"
echo ""

# Test 1: Normal task ID (no special chars)
run_test "Normal task ID" "TASK-012" "TASK-012"

# Test 2: Task ID with dots
run_test "Task ID with dots" "TASK-012.foo" "TASK-012\\.foo"

# Test 3: Task ID with brackets
run_test "Task ID with brackets" "TASK-012[bar]" "TASK-012\\[bar\\]"

# Test 4: Task ID with dots and brackets
run_test "Task ID with dots and brackets" "TASK-012.foo[bar]" "TASK-012\\.foo\\[bar\\]"

# Test 5: Task ID with asterisk
run_test "Task ID with asterisk" "TASK-012*baz" "TASK-012\\*baz"

# Test 6: Task ID with caret
run_test "Task ID with caret" "TASK-012^test" "TASK-012\\^test"

# Test 7: Task ID with dollar sign
run_test "Task ID with dollar sign" "TASK-012$" "TASK-012\\$"

# Test 8: Task ID with backslash
run_test "Task ID with backslash" "TASK-012\\test" "TASK-012\\\\test"

# Test 9: Task ID with forward slash
run_test "Task ID with forward slash" "TASK-012/test" "TASK-012\\/test"

# Test 10: Complex task ID with multiple special chars
run_test "Complex task ID" "TASK-012.foo[bar]*baz^" "TASK-012\\.foo\\[bar\\]\\*baz\\^"

echo ""
echo "========================================"
echo "ERE (AWK) TESTS"
echo "========================================"
echo ""

# Test ERE escaping for awk patterns
run_ere_test "Normal task ID (ERE)" "TASK-012" "TASK-012"
run_ere_test "Task ID with dots (ERE)" "TASK-012.foo" "TASK-012\\.foo"
run_ere_test "Task ID with brackets (ERE)" "TASK-012[bar]" "TASK-012\\[bar\\]"
run_ere_test "Task ID with parentheses (ERE)" "TASK-012(test)" "TASK-012\\(test\\)"
run_ere_test "Task ID with curly braces (ERE)" "TASK-012{test}" "TASK-012\\{test\\}"
run_ere_test "Task ID with plus (ERE)" "TASK-012+test" "TASK-012\\+test"
run_ere_test "Task ID with question mark (ERE)" "TASK-012?test" "TASK-012\\?test"
run_ere_test "Task ID with pipe (ERE)" "TASK-012|test" "TASK-012\\|test"

echo ""
echo "========================================"
echo "FUNCTIONAL INTEGRATION TESTS"
echo "========================================"
echo ""

# Test the actual functions used in file-lock.sh and worker.sh
((test_count++))
echo "Test $test_count: update_kanban_status with special chars"
temp_kanban=$(mktemp)
cat > "$temp_kanban" <<EOF
## TASKS

- [ ] **[TASK-012.foo[bar]]** Test task with special chars
  - Description: A test task
  - Priority: HIGH
EOF

echo "Testing update_kanban_status with TASK-012.foo[bar]..."
if update_kanban_status "$temp_kanban" "TASK-012.foo[bar]" "x"; then
    if grep -q "- \[x\] \*\*\[TASK-012.foo\[bar\]\]\*\*" "$temp_kanban"; then
        echo -e "${GREEN}✓ PASS${NC}: update_kanban_status works with special chars"
        ((pass_count++))
    else
        echo -e "${RED}✗ FAIL${NC}: Status not updated correctly"
        echo "File contents:"
        cat "$temp_kanban"
        ((fail_count++))
    fi
else
    echo -e "${RED}✗ FAIL${NC}: update_kanban_status failed"
    ((fail_count++))
fi
rm -f "$temp_kanban" "${temp_kanban}.lock"

# Test worker.sh grep pattern
((test_count++))
echo "----------------------------------------"
echo "Test $test_count: Worker grep pattern with special chars"
temp_kanban2=$(mktemp)
cat > "$temp_kanban2" <<EOF
## TASKS

- [ ] **[TASK-012.foo[bar]]** Extract this description
  - Description: A test task
  - Priority: HIGH
EOF

task_id_special="TASK-012.foo[bar]"
escaped_task_id=$(escape_regex_chars "$task_id_special")
task_desc=$(grep "**\[$escaped_task_id\]**" "$temp_kanban2" | sed 's/.*\*\*\[.*\]\*\* //' | head -1)

if [ "$task_desc" = "Extract this description" ]; then
    echo -e "${GREEN}✓ PASS${NC}: Task description extracted correctly with special chars"
    ((pass_count++))
else
    echo -e "${RED}✗ FAIL${NC}: Task description extraction failed"
    echo "Expected: 'Extract this description'"
    echo "Got: '$task_desc'"
    ((fail_count++))
fi
rm -f "$temp_kanban2"

echo ""
echo "========================================"
echo "TEST SUMMARY"
echo "========================================"
echo "Total tests: $test_count"
echo -e "${GREEN}Passed: $pass_count${NC}"
echo -e "${RED}Failed: $fail_count${NC}"
echo ""

if [ $fail_count -eq 0 ]; then
    echo -e "${GREEN}✓ ALL TESTS PASSED${NC}"
    exit 0
else
    echo -e "${RED}✗ SOME TESTS FAILED${NC}"
    exit 1
fi
