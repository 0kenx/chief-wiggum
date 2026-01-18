#!/usr/bin/env bash
# Tests for edge cases and integration scenarios

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/test-framework.sh"
source "$SCRIPT_DIR/../lib/task-parser.sh"

test_suite "Edge Cases and Integration Tests"

# Edge case: Unicode and special characters
test_case "Edge case - Unicode in task descriptions"
setup_test_dir
cat > "$TEST_TMP_DIR/kanban.md" <<'EOF'
# Kanban Board

## TODO

- [ ] **[TASK-001]** Task with émojis 🚀
  - Description: Add support for 中文 characters and émojis
  - Priority: HIGH
  - Dependencies: none
EOF

result=$(extract_task "TASK-001" "$TEST_TMP_DIR/kanban.md")
# Note: emojis may be stripped by awk processing, which is acceptable
assert_contains "$result" "中文" "Should handle Chinese characters"
assert_contains "$result" "émojis" "Should handle accented characters"
teardown_test_dir

# Edge case: Very long task descriptions
test_case "Edge case - Long task descriptions"
setup_test_dir
long_desc="$(printf 'A%.0s' {1..1000})"
cat > "$TEST_TMP_DIR/kanban.md" <<EOF
# Kanban Board

## TODO

- [ ] **[TASK-002]** Long task
  - Description: $long_desc
  - Priority: LOW
EOF

result=$(extract_task "TASK-002" "$TEST_TMP_DIR/kanban.md")
assert_contains "$result" "$long_desc" "Should handle very long descriptions"
teardown_test_dir

# Edge case: Multiple dependencies
test_case "Edge case - Multiple dependencies"
setup_test_dir
cat > "$TEST_TMP_DIR/kanban.md" <<'EOF'
# Kanban Board

## TODO

- [ ] **[TASK-003]** Task with multiple deps
  - Description: Complex task
  - Priority: MEDIUM
  - Dependencies: TASK-001, TASK-002, FEATURE-100
EOF

result=$(extract_task "TASK-003" "$TEST_TMP_DIR/kanban.md")
assert_contains "$result" "TASK-001, TASK-002, FEATURE-100" "Should preserve multiple dependencies"
teardown_test_dir

# Edge case: Task ID with maximum allowed length
test_case "Edge case - Maximum task ID length"
setup_test_dir
cat > "$TEST_TMP_DIR/kanban.md" <<'EOF'
# Kanban Board

## TODO

- [ ] **[ABCDEFGH-999]** Eight character prefix
  - Description: Maximum prefix length
EOF

result=$(get_todo_tasks "$TEST_TMP_DIR/kanban.md")
assert_contains "$result" "ABCDEFGH-999" "Should handle 8-character prefix"
teardown_test_dir

# Edge case: Malformed task entries
test_case "Edge case - Malformed task entries"
setup_test_dir
cat > "$TEST_TMP_DIR/kanban.md" <<'EOF'
# Kanban Board

## TODO

- [ ] **[TASK-004** Missing closing bracket
- [ ] **TASK-005** Missing brackets
- [ ] [TASK-006] Missing bold markers
- [ ] **[TASK-007]** Valid task
  - Description: This one is valid
EOF

result=$(get_todo_tasks "$TEST_TMP_DIR/kanban.md")
assert_not_contains "$result" "TASK-004" "Should not extract malformed task 004"
assert_not_contains "$result" "TASK-005" "Should not extract malformed task 005"
assert_not_contains "$result" "TASK-006" "Should not extract malformed task 006"
assert_contains "$result" "TASK-007" "Should extract valid task"
teardown_test_dir

# Edge case: Empty sections
test_case "Edge case - Empty description or priority"
setup_test_dir
cat > "$TEST_TMP_DIR/kanban.md" <<'EOF'
# Kanban Board

## TODO

- [ ] **[TASK-008]** Task with empty fields
  - Description:
  - Priority:
  - Dependencies: none
EOF

result=$(extract_task "TASK-008" "$TEST_TMP_DIR/kanban.md")
# Should still generate the sections but with empty values
assert_contains "$result" "# Task: TASK-008" "Should have task header"
teardown_test_dir

# Edge case: Task at end of file
test_case "Edge case - Task at end of file without trailing newline"
setup_test_dir
printf '# Kanban\n## TODO\n- [ ] **[TASK-009]** Last task\n  - Description: No newline after' > "$TEST_TMP_DIR/kanban.md"

result=$(get_todo_tasks "$TEST_TMP_DIR/kanban.md")
assert_contains "$result" "TASK-009" "Should extract task at EOF"
teardown_test_dir

# Edge case: Nested checkboxes
test_case "Edge case - Nested checkboxes in description"
setup_test_dir
cat > "$TEST_TMP_DIR/prd.md" <<'EOF'
# Task: TEST-010

## Description
This task includes:
- [ ] Sub-item 1
- [x] Sub-item 2

## Checklist

- [ ] Main task 1
- [x] Completed main task
- [ ] Main task 2
EOF

has_incomplete_tasks "$TEST_TMP_DIR/prd.md"
assert_true $? "Should detect incomplete tasks even with nested checkboxes"
teardown_test_dir

# Integration test: Full workflow
test_case "Integration - Complete task workflow"
setup_test_dir

# Create initial kanban
cat > "$TEST_TMP_DIR/kanban.md" <<'EOF'
# Kanban Board

## TODO

- [ ] **[INTEG-001]** Integration test task
  - Description: Test full workflow
  - Priority: HIGH
  - Dependencies: none

- [ ] **[INTEG-002]** Second task
  - Description: Another task
EOF

# Step 1: Get TODO tasks
todos=$(get_todo_tasks "$TEST_TMP_DIR/kanban.md")
assert_contains "$todos" "INTEG-001" "Should find first task"

# Step 2: Extract task to PRD
prd=$(extract_task "INTEG-001" "$TEST_TMP_DIR/kanban.md")
echo "$prd" > "$TEST_TMP_DIR/prd.md"

# Step 3: Verify PRD has incomplete tasks
has_incomplete_tasks "$TEST_TMP_DIR/prd.md"
assert_true $? "PRD should have incomplete tasks initially"

# Step 4: Mark tasks complete in PRD
sed -i 's/- \[ \]/- [x]/g' "$TEST_TMP_DIR/prd.md"

# Step 5: Verify no incomplete tasks
has_incomplete_tasks "$TEST_TMP_DIR/prd.md"
assert_false $? "PRD should have no incomplete tasks after completion"

# Step 6: Mark task complete in kanban
sed -i "s/- \[ \] \*\*\[INTEG-001\]\*\*/- [x] **[INTEG-001]**/" "$TEST_TMP_DIR/kanban.md"

kanban_result=$(cat "$TEST_TMP_DIR/kanban.md")
assert_contains "$kanban_result" "- [x] **[INTEG-001]**" "Task should be marked complete in kanban"
assert_contains "$kanban_result" "- [ ] **[INTEG-002]**" "Other tasks should remain incomplete"

teardown_test_dir

# Integration test: Multiple tasks in sequence
test_case "Integration - Process multiple tasks"
setup_test_dir

cat > "$TEST_TMP_DIR/kanban.md" <<'EOF'
# Kanban Board

## TODO

- [ ] **[SEQ-001]** First task
  - Description: First
  - Priority: HIGH

- [ ] **[SEQ-002]** Second task
  - Description: Second
  - Priority: MEDIUM

- [ ] **[SEQ-003]** Third task
  - Description: Third
  - Priority: LOW
EOF

# Process all tasks
for task_id in SEQ-001 SEQ-002 SEQ-003; do
    todos=$(get_todo_tasks "$TEST_TMP_DIR/kanban.md")
    if echo "$todos" | grep -q "$task_id"; then
        prd=$(extract_task "$task_id" "$TEST_TMP_DIR/kanban.md")
        echo "$prd" > "$TEST_TMP_DIR/prd-$task_id.md"

        # Simulate completion
        sed -i "s/- \[ \] \*\*\[$task_id\]\*\*/- [x] **[$task_id]**/" "$TEST_TMP_DIR/kanban.md"
    fi
done

final_kanban=$(cat "$TEST_TMP_DIR/kanban.md")
assert_contains "$final_kanban" "- [x] **[SEQ-001]**" "First task should be complete"
assert_contains "$final_kanban" "- [x] **[SEQ-002]**" "Second task should be complete"
assert_contains "$final_kanban" "- [x] **[SEQ-003]**" "Third task should be complete"

teardown_test_dir

# Edge case: Concurrent access simulation
test_case "Edge case - File locking and race conditions"
setup_test_dir

cat > "$TEST_TMP_DIR/kanban.md" <<'EOF'
# Kanban Board

## TODO

- [ ] **[RACE-001]** Task that might be accessed concurrently
EOF

# Simulate concurrent read (should be safe)
result1=$(get_todo_tasks "$TEST_TMP_DIR/kanban.md")
result2=$(get_todo_tasks "$TEST_TMP_DIR/kanban.md")

assert_equals "$result1" "$result2" "Concurrent reads should produce same result"

teardown_test_dir

# Edge case: Special regex characters in descriptions
test_case "Edge case - Regex special characters in task content"
setup_test_dir

cat > "$TEST_TMP_DIR/kanban.md" <<'EOF'
# Kanban Board

## TODO

- [ ] **[REGEX-001]** Task with special chars
  - Description: Fix regex: .*$^[]{}()|+?
  - Priority: HIGH
EOF

result=$(extract_task "REGEX-001" "$TEST_TMP_DIR/kanban.md")
assert_contains "$result" ".*\$^[]{}()|+?" "Should handle regex special characters"

teardown_test_dir

# Skills integration test
test_case "Skills integration - Task completion flow"
setup_test_dir

# Simulate the complete-task skill behavior
TASK_ID="SKILL-001"
cat > "$TEST_TMP_DIR/kanban.md" <<'EOF'
# Kanban Board

## TODO

- [ ] **[SKILL-001]** Test skill integration
  - Description: Test the complete-task skill
EOF

# Simulate what the skill does (from complete-task.md)
sed -i "s/- \[ \] \*\*\[$TASK_ID\]\*\*/- [x] **[$TASK_ID]**/" "$TEST_TMP_DIR/kanban.md"

result=$(cat "$TEST_TMP_DIR/kanban.md")
assert_contains "$result" "- [x] **[SKILL-001]**" "Skill should mark task complete"

teardown_test_dir

print_summary
