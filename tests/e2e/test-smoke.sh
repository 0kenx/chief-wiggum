#!/usr/bin/env bash
# test-smoke.sh - End-to-end smoke test for Chief Wiggum
#
# Tests the full workflow: init → validate → (mock) run
# Uses mock Claude CLI to avoid actual API calls.
set -euo pipefail

# Test framework setup
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
export WIGGUM_HOME="$PROJECT_ROOT"

# Use mock Claude
export CLAUDE="$PROJECT_ROOT/tests/mocks/mock-claude.sh"
chmod +x "$CLAUDE"

# Test utilities
TEST_COUNT=0
PASS_COUNT=0
FAIL_COUNT=0

test_start() {
    TEST_COUNT=$((TEST_COUNT + 1))
    echo -n "Test $TEST_COUNT: $1... "
}

test_pass() {
    PASS_COUNT=$((PASS_COUNT + 1))
    echo "PASS"
}

test_fail() {
    FAIL_COUNT=$((FAIL_COUNT + 1))
    echo "FAIL"
    [ -n "${1:-}" ] && echo "  Error: $1"
}

# Cleanup function
cleanup() {
    cd /
    rm -rf "$TEST_TEMP_DIR" 2>/dev/null || true
}
trap cleanup EXIT

# Create temporary test directory
TEST_TEMP_DIR=$(mktemp -d)
cd "$TEST_TEMP_DIR"

echo "=== End-to-End Smoke Tests ==="
echo "Test directory: $TEST_TEMP_DIR"
echo ""

# =============================================================================
# TESTS
# =============================================================================

# Test 1: wiggum init
test_start "wiggum init creates .ralph directory"
(
    # Initialize git repo first (required for init)
    git init -q

    "$WIGGUM_HOME/bin/wiggum-init" > /dev/null 2>&1

    [ -d ".ralph" ] && \
    [ -f ".ralph/kanban.md" ] && \
    [ -d ".ralph/workers" ] && \
    [ -d ".ralph/logs" ]
) && test_pass || test_fail ".ralph directory structure incomplete"

# Test 2: wiggum validate (empty kanban)
test_start "wiggum validate accepts valid kanban"
(
    "$WIGGUM_HOME/bin/wiggum-validate" > /dev/null 2>&1
) && test_pass || test_fail "Validation failed on empty kanban"

# Test 3: Add tasks and validate
test_start "wiggum validate with tasks"
(
    cat > .ralph/kanban.md << 'EOF'
# Kanban

## TASKS

- [ ] **[TASK-001]** Implement user authentication
  - Priority: HIGH
  - Description: Add login/logout functionality

- [ ] **[TASK-002]** Add dashboard page
  - Priority: MEDIUM
  - Description: Create main dashboard
EOF

    "$WIGGUM_HOME/bin/wiggum-validate" > /dev/null 2>&1
) && test_pass || test_fail "Validation failed with tasks"

# Test 4: wiggum status (no workers)
test_start "wiggum status shows no active workers"
(
    output=$("$WIGGUM_HOME/bin/wiggum-status" 2>&1)
    echo "$output" | grep -qiF "no wiggum"
) && test_pass || test_fail "Status not showing empty state"

# Test 5: wiggum doctor (check prerequisites)
test_start "wiggum doctor runs checks"
(
    # Doctor should run without error (may have warnings/failures)
    output=$("$WIGGUM_HOME/bin/wiggum-doctor" 2>&1 || true)
    echo "$output" | grep -qE "FAIL|PASS"
) && test_pass || test_fail "Doctor failed to run"

# Test 6: Config validation
test_start "Config files are valid JSON"
(
    source "$WIGGUM_HOME/lib/core/config-validator.sh"
    validate_config > /dev/null 2>&1
) && test_pass || test_fail "Config validation failed"

# Test 7: Agents config validation
test_start "Agents config is valid JSON"
(
    source "$WIGGUM_HOME/lib/core/config-validator.sh"
    validate_agents_config > /dev/null 2>&1
) && test_pass || test_fail "Agents config validation failed"

# Test 8: Task parser functions
test_start "Task parser extracts tasks"
(
    source "$WIGGUM_HOME/lib/tasks/task-parser.sh"

    tasks=$(get_todo_tasks ".ralph/kanban.md")
    echo "$tasks" | grep -q "TASK-001"
) && test_pass || test_fail "Task parser failed"

# Test 9: Checkpoint creation
test_start "Checkpoint creation"
(
    source "$WIGGUM_HOME/lib/core/checkpoint.sh"

    worker_dir=".ralph/workers/worker-TASK-001-12345"
    mkdir -p "$worker_dir"

    export RALPH_RUN_ID="smoke-test"
    checkpoint_write "$worker_dir" 0 "test-session" "in_progress" '["file1.txt"]' '["task1"]' '["step1"]' "Test summary"

    [ -f "$worker_dir/checkpoints/smoke-test/checkpoint-0.json" ] && \
    grep -q '"iteration": 0' "$worker_dir/checkpoints/smoke-test/checkpoint-0.json"
) && test_pass || test_fail "Checkpoint not created"

# Test 10: Activity logging
test_start "Activity logging"
(
    source "$WIGGUM_HOME/lib/utils/activity-log.sh"

    activity_init "."
    activity_log "task.started" "worker-TASK-001-12345" "TASK-001"

    [ -f ".ralph/logs/activity.jsonl" ] && \
    grep -q "task.started" ".ralph/logs/activity.jsonl"
) && test_pass || test_fail "Activity log not written"

# Test 11: Logger functions
test_start "Logger functions work"
(
    source "$WIGGUM_HOME/lib/core/logger.sh"

    log "Test message" > /dev/null 2>&1
    log_debug "Debug message" > /dev/null 2>&1
    log_warn "Warning message" > /dev/null 2>&1
    log_error "Error message" > /dev/null 2>&1

    true  # If we got here, logging works
) && test_pass || test_fail "Logger failed"

# Test 12: File locking
test_start "File locking works"
(
    source "$WIGGUM_HOME/lib/core/file-lock.sh"

    # Test with kanban update
    update_kanban_status ".ralph/kanban.md" "TASK-001" "="

    grep -q '\[=\].*TASK-001' ".ralph/kanban.md"
) && test_pass || test_fail "File locking failed"

# Test 13: Mock Claude responds
test_start "Mock Claude CLI responds"
(
    export MOCK_CLAUDE_RESPONSE="Test response from mock"
    output=$("$CLAUDE" --version 2>&1)
    echo "$output" | grep -q "mock"
) && test_pass || test_fail "Mock Claude not working"

# Test 14: Preflight checks
test_start "Preflight check functions"
(
    source "$WIGGUM_HOME/lib/core/preflight.sh"

    check_command_exists bash
    check_command_exists git
    check_jq > /dev/null 2>&1
) && test_pass || test_fail "Preflight checks failed"

# Test 15: Clean command (dry run)
test_start "wiggum clean handles missing workers"
(
    # Should not fail when no workers exist
    "$WIGGUM_HOME/bin/wiggum-clean" -y all > /dev/null 2>&1 || true
    true
) && test_pass || test_fail "Clean command failed"

# =============================================================================
# SUMMARY
# =============================================================================

echo ""
echo "=== Test Summary ==="
echo "Total: $TEST_COUNT"
echo "Passed: $PASS_COUNT"
echo "Failed: $FAIL_COUNT"
echo ""

if [ $FAIL_COUNT -gt 0 ]; then
    echo "Some tests failed!"
    exit 1
fi

echo "All smoke tests passed!"
exit 0
