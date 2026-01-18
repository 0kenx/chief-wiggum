#!/usr/bin/env bash
source lib/task-parser.sh
source lib/file-lock.sh

GREEN='\033[0;32m'
RED='\033[0;31m'
NC='\033[0m'

pass=0
fail=0

echo "========================================"
echo "REGEX ESCAPING FUNCTIONALITY TESTS"
echo "========================================"
echo ""

# Test 1: update_kanban_status with normal task ID
echo "Test 1: Normal task ID"
temp1=$(mktemp)
cat > "$temp1" << 'KANBAN'
- [ ] **[TASK-012]** Normal task
KANBAN
update_kanban_status "$temp1" "TASK-012" "x"
if grep -F -- '- [x] **[TASK-012]**' "$temp1" > /dev/null 2>&1; then
    echo -e "${GREEN}✓ PASS${NC}: Normal task ID works"
    ((pass++))
else
    echo -e "${RED}✗ FAIL${NC}: Normal task ID failed"
    echo "Content: $(cat $temp1)"
    ((fail++))
fi
rm -f "$temp1" "${temp1}.lock"

# Test 2: Task ID with dots
echo ""
echo "Test 2: Task ID with dots"
temp2=$(mktemp)
cat > "$temp2" << 'KANBAN'
- [ ] **[TASK-012.foo]** Task with dots
KANBAN
update_kanban_status "$temp2" "TASK-012.foo" "x"
if grep -F -- '- [x] **[TASK-012.foo]**' "$temp2" > /dev/null 2>&1; then
    echo -e "${GREEN}✓ PASS${NC}: Task ID with dots works"
    ((pass++))
else
    echo -e "${RED}✗ FAIL${NC}: Task ID with dots failed"
    echo "Content: $(cat $temp2)"
    ((fail++))
fi
rm -f "$temp2" "${temp2}.lock"

# Test 3: Task ID with brackets
echo ""
echo "Test 3: Task ID with brackets"
temp3=$(mktemp)
cat > "$temp3" << 'KANBAN'
- [ ] **[TASK-012[bar]]** Task with brackets
KANBAN
update_kanban_status "$temp3" "TASK-012[bar]" "x"
if grep -F -- '- [x] **[TASK-012[bar]]**' "$temp3" > /dev/null 2>&1; then
    echo -e "${GREEN}✓ PASS${NC}: Task ID with brackets works"
    ((pass++))
else
    echo -e "${RED}✗ FAIL${NC}: Task ID with brackets failed"
    echo "Content: $(cat $temp3)"
    ((fail++))
fi
rm -f "$temp3" "${temp3}.lock"

# Test 4: Task ID with dots and brackets
echo ""
echo "Test 4: Task ID with dots and brackets"
temp4=$(mktemp)
cat > "$temp4" << 'KANBAN'
- [ ] **[TASK-012.foo[bar]]** Task with dots and brackets
KANBAN
update_kanban_status "$temp4" "TASK-012.foo[bar]" "x"
if grep -F -- '- [x] **[TASK-012.foo[bar]]**' "$temp4" > /dev/null 2>&1; then
    echo -e "${GREEN}✓ PASS${NC}: Task ID with dots and brackets works"
    ((pass++))
else
    echo -e "${RED}✗ FAIL${NC}: Task ID with dots and brackets failed"
    echo "Content: $(cat $temp4)"
    ((fail++))
fi
rm -f "$temp4" "${temp4}.lock"

# Test 5: Task ID with asterisk
echo ""
echo "Test 5: Task ID with asterisk"
temp5=$(mktemp)
cat > "$temp5" << 'KANBAN'
- [ ] **[TASK-012*baz]** Task with asterisk
KANBAN
update_kanban_status "$temp5" "TASK-012*baz" "x"
if grep -F -- '- [x] **[TASK-012*baz]**' "$temp5" > /dev/null 2>&1; then
    echo -e "${GREEN}✓ PASS${NC}: Task ID with asterisk works"
    ((pass++))
else
    echo -e "${RED}✗ FAIL${NC}: Task ID with asterisk failed"
    echo "Content: $(cat $temp5)"
    ((fail++))
fi
rm -f "$temp5" "${temp5}.lock"

# Test 6: Task ID with forward slash
echo ""
echo "Test 6: Task ID with forward slash"
temp6=$(mktemp)
cat > "$temp6" << 'KANBAN'
- [ ] **[TASK-012/test]** Task with slash
KANBAN
update_kanban_status "$temp6" "TASK-012/test" "x"
if grep -F -- '- [x] **[TASK-012/test]**' "$temp6" > /dev/null 2>&1; then
    echo -e "${GREEN}✓ PASS${NC}: Task ID with slash works"
    ((pass++))
else
    echo -e "${RED}✗ FAIL${NC}: Task ID with slash failed"
    echo "Content: $(cat $temp6)"
    ((fail++))
fi
rm -f "$temp6" "${temp6}.lock"

# Test 7: Complex task ID with multiple special chars
echo ""
echo "Test 7: Complex task ID"
temp7=$(mktemp)
cat > "$temp7" << 'KANBAN'
- [ ] **[TASK-012.foo[bar]*baz]** Complex task
KANBAN
update_kanban_status "$temp7" "TASK-012.foo[bar]*baz" "x"
if grep -F -- '- [x] **[TASK-012.foo[bar]*baz]**' "$temp7" > /dev/null 2>&1; then
    echo -e "${GREEN}✓ PASS${NC}: Complex task ID works"
    ((pass++))
else
    echo -e "${RED}✗ FAIL${NC}: Complex task ID failed"
    echo "Content: $(cat $temp7)"
    ((fail++))
fi
rm -f "$temp7" "${temp7}.lock"

# Test 8: Task description extraction (worker.sh pattern)
echo ""
echo "Test 8: Task description extraction with special chars"
temp8=$(mktemp)
cat > "$temp8" << 'KANBAN'
- [ ] **[TASK-012.foo[bar]]** Extract this description
  - Description: Full description
KANBAN
escaped_task_id=$(escape_regex_chars "TASK-012.foo[bar]")
task_desc=$(grep -- "**\[$escaped_task_id\]**" "$temp8" | sed 's/.*\*\*\[.*\]\*\* //' | head -1)
if [ "$task_desc" = "Extract this description" ]; then
    echo -e "${GREEN}✓ PASS${NC}: Task description extraction works"
    ((pass++))
else
    echo -e "${RED}✗ FAIL${NC}: Expected 'Extract this description', got '$task_desc'"
    ((fail++))
fi
rm "$temp8"

# Test 9: ERE escaping for awk patterns
echo ""
echo "Test 9: ERE escaping for awk patterns"
temp9=$(mktemp)
echo "**[TASK-012.foo[bar](test)]** Description" > "$temp9"
escaped_ere=$(escape_regex_chars_ere "TASK-012.foo[bar](test)")
result=$(awk "/\*\*\[$escaped_ere\]\*\*/ {print \"FOUND\"}" "$temp9")
if [ "$result" = "FOUND" ]; then
    echo -e "${GREEN}✓ PASS${NC}: ERE escaping for awk works"
    ((pass++))
else
    echo -e "${RED}✗ FAIL${NC}: ERE escaping for awk failed"
    ((fail++))
fi
rm "$temp9"

# Test 10: Status change to failed (*)
echo ""
echo "Test 10: Marking task as failed"
temp10=$(mktemp)
cat > "$temp10" << 'KANBAN'
- [=] **[TASK-012.foo[bar]]** Task to mark failed
KANBAN
update_kanban_status "$temp10" "TASK-012.foo[bar]" "*"
if grep -F -- '- [*] **[TASK-012.foo[bar]]**' "$temp10" > /dev/null 2>&1; then
    echo -e "${GREEN}✓ PASS${NC}: Marking task as failed works"
    ((pass++))
else
    echo -e "${RED}✗ FAIL${NC}: Marking task as failed failed"
    echo "Content: $(cat $temp10)"
    ((fail++))
fi
rm -f "$temp10" "${temp10}.lock"

echo ""
echo "========================================"
echo "TEST SUMMARY"
echo "========================================"
echo "Total tests: $((pass + fail))"
echo -e "${GREEN}Passed: $pass${NC}"
echo -e "${RED}Failed: $fail${NC}"
echo ""

if [ $fail -eq 0 ]; then
    echo -e "${GREEN}✓ ALL TESTS PASSED${NC}"
    exit 0
else
    echo -e "${RED}✗ SOME TESTS FAILED${NC}"
    exit 1
fi
