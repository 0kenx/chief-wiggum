#!/usr/bin/env bash
source lib/task-parser.sh
source lib/file-lock.sh

# Test 1: Simple test with brackets
echo "=== Test 1: Task ID with brackets ==="
temp=$(mktemp)
echo '- [ ] **[TASK-012[bar]]** Test task' > "$temp"
echo "Before: $(cat $temp)"

escaped=$(escape_regex_chars "TASK-012[bar]")
echo "Escaped: $escaped"

sed -i "s/- \[[^\]]*\] \*\*\[$escaped\]\*\*/- [x] **[TASK-012[bar]]**/" "$temp"
echo "After: $(cat $temp)"

# Check if the status was changed from [ ] to [x]
if echo "$(cat $temp)" | grep -F '- [x]' > /dev/null; then
    echo "✓ PASS: Status changed successfully"
else
    echo "✗ FAIL: Status not changed"
fi

rm "$temp"

# Test 2: Test update_kanban_status function directly
echo ""
echo "=== Test 2: update_kanban_status function ==="
temp2=$(mktemp)
cat > "$temp2" << 'KANBAN'
## TASKS

- [ ] **[TASK-012.foo[bar]]** Test task with special chars
  - Description: A test task
KANBAN

echo "Before: $(grep TASK-012 $temp2)"
update_kanban_status "$temp2" "TASK-012.foo[bar]" "x"
echo "After: $(grep TASK-012 $temp2)"

if grep -F '- [x]' "$temp2" > /dev/null; then
    echo "✓ PASS: update_kanban_status works"
else
    echo "✗ FAIL: update_kanban_status failed"
fi

rm -f "$temp2" "${temp2}.lock"

# Test 3: Test task description extraction (from worker.sh)
echo ""
echo "=== Test 3: Task description extraction ==="
temp3=$(mktemp)
cat > "$temp3" << 'KANBAN'
## TASKS

- [ ] **[TASK-012.foo[bar]]** Extract this description
  - Description: A test task
KANBAN

escaped_task_id=$(escape_regex_chars "TASK-012.foo[bar]")
echo "Looking for pattern: **\[$escaped_task_id\]**"
task_desc=$(grep "**\[$escaped_task_id\]**" "$temp3" | sed 's/.*\*\*\[.*\]\*\* //' | head -1)
echo "Extracted: '$task_desc'"

if [ "$task_desc" = "Extract this description" ]; then
    echo "✓ PASS: Description extracted correctly"
else
    echo "✗ FAIL: Expected 'Extract this description', got '$task_desc'"
fi

rm "$temp3"

echo ""
echo "=== All critical functionality tests complete ==="
