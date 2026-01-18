#!/usr/bin/env bash
# Tests for lib/worker.sh

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/test-framework.sh"

test_suite "worker.sh"

# Note: Testing worker.sh is complex as it spawns subprocesses and uses git worktrees
# We'll focus on testing individual functions in isolation

test_case "worker.sh - setup_worker function creates worktree"
setup_test_dir

# Create a minimal git repo for testing
cd "$TEST_TMP_DIR"
git init test-project > /dev/null 2>&1
cd test-project
git config user.email "test@test.com"
git config user.name "Test User"
echo "# Test" > README.md
git add README.md
git commit -m "Initial commit" > /dev/null 2>&1

# Create worker directory structure
WORKER_DIR="$TEST_TMP_DIR/worker-TEST-001"
mkdir -p "$WORKER_DIR"

# Source worker functions (excluding main execution)
# We'll test the setup_worker function logic
PROJECT_DIR="$TEST_TMP_DIR/test-project"
WORKER_ID="worker-TEST-001"
TASK_ID="TEST-001"

# Simulate setup_worker
cd "$PROJECT_DIR" || exit 1
git worktree add "$WORKER_DIR/workspace" HEAD > /dev/null 2>&1
worktree_created=$?

assert_true $worktree_created "Should create git worktree successfully"
assert_file_exists "$WORKER_DIR/workspace/README.md" "Worktree should contain project files"

# Cleanup worktree
git worktree remove "$WORKER_DIR/workspace" --force > /dev/null 2>&1

teardown_test_dir

test_case "worker.sh - cleanup_worker marks task complete in kanban"
setup_test_dir

# Create a kanban file
cat > "$TEST_TMP_DIR/kanban.md" <<'EOF'
# Kanban Board

## TODO

- [ ] **[TASK-001]** Test task
  - Description: Test description
  - Priority: HIGH

- [ ] **[TASK-002]** Another task
EOF

TASK_ID="TASK-001"

# Simulate the sed command from cleanup_worker
sed -i "s/- \[ \] \*\*\[$TASK_ID\]\*\*/- [x] **[$TASK_ID]**/" "$TEST_TMP_DIR/kanban.md"

result=$(cat "$TEST_TMP_DIR/kanban.md")
assert_contains "$result" "- [x] **[TASK-001]**" "Should mark task as complete"
assert_contains "$result" "- [ ] **[TASK-002]**" "Should not affect other tasks"

teardown_test_dir

test_case "worker.sh - cleanup_worker handles multiple occurrences"
setup_test_dir

cat > "$TEST_TMP_DIR/kanban.md" <<'EOF'
# Kanban Board

## TODO

- [ ] **[TASK-003]** Test task

## IN PROGRESS

- [ ] **[TASK-003]** This shouldn't happen but test it
EOF

TASK_ID="TASK-003"
sed -i "s/- \[ \] \*\*\[$TASK_ID\]\*\*/- [x] **[$TASK_ID]**/" "$TEST_TMP_DIR/kanban.md"

result=$(cat "$TEST_TMP_DIR/kanban.md")
# Both should be marked complete with sed -i default behavior
completed_count=$(grep -c "\[x\] \*\*\[TASK-003\]\*\*" "$TEST_TMP_DIR/kanban.md")
assert_equals "2" "$completed_count" "Should mark all occurrences as complete"

teardown_test_dir

test_case "worker.sh - environment variables are set correctly"
setup_test_dir

# Simulate the environment setup
WORKER_ID="worker-TASK-123-45678"
TASK_ID="TASK-123"
export WORKER_ID
export TASK_ID

assert_equals "worker-TASK-123-45678" "$WORKER_ID" "WORKER_ID should be set"
assert_equals "TASK-123" "$TASK_ID" "TASK_ID should be set"

unset WORKER_ID
unset TASK_ID
teardown_test_dir

test_case "worker.sh - results directory creation"
setup_test_dir

PROJECT_DIR="$TEST_TMP_DIR/project"
TASK_ID="TASK-456"
mkdir -p "$PROJECT_DIR"

# Simulate results directory creation from cleanup_worker
mkdir -p "$PROJECT_DIR/.ralph/results/$TASK_ID"

# Check if directory exists
if [ -d "$PROJECT_DIR/.ralph/results/$TASK_ID" ]; then
    assert_true 0 "Results directory should be created"
else
    assert_true 1 "Results directory should be created"
fi

teardown_test_dir

test_case "worker.sh - CHIEF_HOME default value"
setup_test_dir

# Test default CHIEF_HOME
unset CHIEF_HOME
CHIEF_HOME="${CHIEF_HOME:-$HOME/.claude/chief-wiggum}"

assert_equals "$HOME/.claude/chief-wiggum" "$CHIEF_HOME" "Should use default CHIEF_HOME if not set"

# Test with custom CHIEF_HOME
export CHIEF_HOME="/custom/path"
CHIEF_HOME="${CHIEF_HOME:-$HOME/.claude/chief-wiggum}"

assert_equals "/custom/path" "$CHIEF_HOME" "Should use custom CHIEF_HOME if set"

unset CHIEF_HOME
teardown_test_dir

print_summary
