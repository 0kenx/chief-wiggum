#!/usr/bin/env bash
# Tests for lib/task-parser.sh

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/test-framework.sh"
source "$SCRIPT_DIR/../lib/task-parser.sh"

test_suite "task-parser.sh"

# Test has_incomplete_tasks
test_case "has_incomplete_tasks - detects incomplete tasks"
setup_test_dir
cat > "$TEST_TMP_DIR/test.md" <<'EOF'
# Test PRD

## Checklist

- [ ] Incomplete task 1
- [x] Complete task
- [ ] Incomplete task 2
EOF

has_incomplete_tasks "$TEST_TMP_DIR/test.md"
assert_true $? "Should detect incomplete tasks"
teardown_test_dir

test_case "has_incomplete_tasks - no incomplete tasks"
setup_test_dir
cat > "$TEST_TMP_DIR/test.md" <<'EOF'
# Test PRD

## Checklist

- [x] Complete task 1
- [x] Complete task 2
EOF

has_incomplete_tasks "$TEST_TMP_DIR/test.md"
assert_false $? "Should not detect incomplete tasks when all are complete"
teardown_test_dir

test_case "has_incomplete_tasks - empty file"
setup_test_dir
touch "$TEST_TMP_DIR/empty.md"
has_incomplete_tasks "$TEST_TMP_DIR/empty.md"
assert_false $? "Should handle empty file"
teardown_test_dir

test_case "has_incomplete_tasks - edge case with similar patterns"
setup_test_dir
cat > "$TEST_TMP_DIR/test.md" <<'EOF'
# Test PRD

Some text with - [ ] in it but not a task
- [x] Complete task
  - [ ] This is a sub-item, should still be detected
EOF

has_incomplete_tasks "$TEST_TMP_DIR/test.md"
assert_true $? "Should detect incomplete tasks even with false positives in text"
teardown_test_dir

# Test get_todo_tasks
test_case "get_todo_tasks - extracts tasks from TODO section"
setup_test_dir
cat > "$TEST_TMP_DIR/kanban.md" <<'EOF'
# Kanban Board

## TODO

- [ ] **[TASK-001]** First task
  - Description: Do something
  - Priority: HIGH
  - Dependencies: none

- [ ] **[TASK-002]** Second task
  - Description: Do another thing
  - Priority: LOW

## IN PROGRESS

- [ ] **[PROG-001]** In progress task

## DONE

- [x] **[DONE-001]** Completed task
EOF

result=$(get_todo_tasks "$TEST_TMP_DIR/kanban.md")
assert_contains "$result" "TASK-001" "Should extract TASK-001"
assert_contains "$result" "TASK-002" "Should extract TASK-002"
assert_not_contains "$result" "PROG-001" "Should not extract tasks from other sections"
assert_not_contains "$result" "DONE-001" "Should not extract completed tasks"
teardown_test_dir

test_case "get_todo_tasks - handles different task ID formats"
setup_test_dir
cat > "$TEST_TMP_DIR/kanban.md" <<'EOF'
# Kanban Board

## TODO

- [ ] **[AB-123]** Two letter prefix
- [ ] **[FEATURE-456]** Seven letter prefix
- [ ] **[LONGTASK-789]** Eight letter prefix
- [ ] **[VERYLONGG-999]** Nine letter prefix (should not match)
- [ ] **[X-111]** One letter prefix (should not match)
EOF

result=$(get_todo_tasks "$TEST_TMP_DIR/kanban.md")
assert_contains "$result" "AB-123" "Should extract 2-letter prefix"
assert_contains "$result" "FEATURE-456" "Should extract 7-letter prefix"
assert_contains "$result" "LONGTASK-789" "Should extract 8-letter prefix"
assert_not_contains "$result" "VERYLONGG-999" "Should not extract 9-letter prefix"
assert_not_contains "$result" "X-111" "Should not extract 1-letter prefix"
teardown_test_dir

test_case "get_todo_tasks - empty TODO section"
setup_test_dir
cat > "$TEST_TMP_DIR/kanban.md" <<'EOF'
# Kanban Board

## TODO

## IN PROGRESS
EOF

result=$(get_todo_tasks "$TEST_TMP_DIR/kanban.md")
assert_equals "" "$result" "Should return empty for empty TODO section"
teardown_test_dir

# Test extract_task
test_case "extract_task - extracts full task details"
setup_test_dir
cat > "$TEST_TMP_DIR/kanban.md" <<'EOF'
# Kanban Board

## TODO

- [ ] **[TASK-001]** First task
  - Description: Implement user authentication
  - Priority: HIGH
  - Dependencies: TASK-000

- [ ] **[TASK-002]** Second task
  - Description: Add logging
  - Priority: LOW
  - Dependencies: none
EOF

result=$(extract_task "TASK-001" "$TEST_TMP_DIR/kanban.md")
assert_contains "$result" "# Task: TASK-001" "Should have task header"
assert_contains "$result" "## Description" "Should have description section"
assert_contains "$result" "Implement user authentication" "Should have description text"
assert_contains "$result" "## Priority" "Should have priority section"
assert_contains "$result" "HIGH" "Should have priority value"
assert_contains "$result" "## Dependencies" "Should have dependencies section"
assert_contains "$result" "TASK-000" "Should have dependency value"
assert_contains "$result" "## Checklist" "Should have checklist section"
assert_contains "$result" "- [ ] Complete the task as described" "Should have checklist items"
teardown_test_dir

test_case "extract_task - handles task with no dependencies"
setup_test_dir
cat > "$TEST_TMP_DIR/kanban.md" <<'EOF'
# Kanban Board

## TODO

- [ ] **[TASK-999]** Task without deps
  - Description: Simple task
  - Priority: MEDIUM
  - Dependencies: none
EOF

result=$(extract_task "TASK-999" "$TEST_TMP_DIR/kanban.md")
assert_contains "$result" "# Task: TASK-999" "Should have task header"
assert_contains "$result" "Simple task" "Should have description"
assert_not_contains "$result" "## Dependencies" "Should not include dependencies section for 'none'"
teardown_test_dir

test_case "extract_task - handles task without priority"
setup_test_dir
cat > "$TEST_TMP_DIR/kanban.md" <<'EOF'
# Kanban Board

## TODO

- [ ] **[TASK-888]** Task without priority
  - Description: Another task
  - Dependencies: none
EOF

result=$(extract_task "TASK-888" "$TEST_TMP_DIR/kanban.md")
assert_contains "$result" "# Task: TASK-888" "Should have task header"
assert_contains "$result" "Another task" "Should have description"
assert_not_contains "$result" "## Priority" "Should not include priority section if missing"
teardown_test_dir

test_case "extract_task - handles multiple tasks correctly"
setup_test_dir
cat > "$TEST_TMP_DIR/kanban.md" <<'EOF'
# Kanban Board

## TODO

- [ ] **[TASK-100]** First task
  - Description: First description
  - Priority: HIGH

- [ ] **[TASK-200]** Second task
  - Description: Second description
  - Priority: LOW
EOF

result=$(extract_task "TASK-200" "$TEST_TMP_DIR/kanban.md")
assert_contains "$result" "# Task: TASK-200" "Should extract correct task"
assert_contains "$result" "Second description" "Should have correct description"
assert_not_contains "$result" "First description" "Should not include other task's description"
teardown_test_dir

print_summary
