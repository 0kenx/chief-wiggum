#!/usr/bin/env bash
# test-worker-coordination.sh - Integration tests for worker coordination
set -euo pipefail

# Test framework setup
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
export WIGGUM_HOME="$PROJECT_ROOT"
export PATH="$PROJECT_ROOT/tests/mocks:$PATH"

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
    rm -rf "$TEST_TEMP_DIR" 2>/dev/null || true
}
trap cleanup EXIT

# Create temporary test directory
TEST_TEMP_DIR=$(mktemp -d)
export PROJECT_DIR="$TEST_TEMP_DIR"
export RALPH_DIR="$TEST_TEMP_DIR/.ralph"

# Setup test environment
setup_test_env() {
    mkdir -p "$RALPH_DIR/workers"
    mkdir -p "$RALPH_DIR/logs"

    # Create minimal kanban.md
    cat > "$RALPH_DIR/kanban.md" << 'EOF'
# Kanban

## TODO
- [ ] **[TASK-001]** First test task
- [ ] **[TASK-002]** Second test task
EOF
}

# =============================================================================
# TESTS
# =============================================================================

echo "=== Worker Coordination Integration Tests ==="
echo ""

# Test 1: Find worker by task ID
test_start "Find worker by task ID"
(
    setup_test_env
    source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"

    # Create test worker directory
    mkdir -p "$RALPH_DIR/workers/worker-TASK-001-12345678"

    local result
    result=$(find_worker_by_task_id "$RALPH_DIR" "TASK-001")
    [ -n "$result" ] && [[ "$result" == *"worker-TASK-001-12345678"* ]]
) && test_pass || test_fail "Worker not found"

# Test 2: Find any worker by task ID
test_start "Find any worker by task ID"
(
    setup_test_env
    source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"

    mkdir -p "$RALPH_DIR/workers/worker-TASK-002-11111111"
    mkdir -p "$RALPH_DIR/workers/worker-TASK-002-22222222"

    local result
    result=$(find_any_worker_by_task_id "$RALPH_DIR" "TASK-002")
    [ -n "$result" ] && [[ "$result" == *"TASK-002"* ]]
) && test_pass || test_fail "Worker not found"

# Test 3: Resolve worker ID (exact match)
test_start "Resolve worker ID - exact match"
(
    setup_test_env
    source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"

    mkdir -p "$RALPH_DIR/workers/worker-TASK-001-12345678"

    local result
    result=$(resolve_worker_id "$RALPH_DIR" "12345678")
    [ -n "$result" ] && [[ "$result" == *"12345678"* ]]
) && test_pass || test_fail "Worker not resolved"

# Test 4: Get task ID from worker
test_start "Get task ID from worker"
(
    source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"

    local task_id
    task_id=$(get_task_id_from_worker "worker-TASK-001-12345678")
    [ "$task_id" = "TASK-001" ]
) && test_pass || test_fail "Task ID not extracted"

# Test 5: Valid worker PID check (not running)
test_start "Valid worker PID check - not running"
(
    setup_test_env
    source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"

    mkdir -p "$RALPH_DIR/workers/worker-TASK-001-12345"
    echo "99999999" > "$RALPH_DIR/workers/worker-TASK-001-12345/agent.pid"

    # Should fail because PID doesn't exist
    ! get_valid_worker_pid "$RALPH_DIR/workers/worker-TASK-001-12345/agent.pid" "bash" > /dev/null
) && test_pass || test_fail "Should not find invalid PID"

# Test 6: Cleanup stale PID
test_start "Cleanup stale PID file"
(
    setup_test_env
    source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"

    mkdir -p "$RALPH_DIR/workers/worker-TASK-001-12345"
    echo "99999999" > "$RALPH_DIR/workers/worker-TASK-001-12345/agent.pid"

    cleanup_stale_pid "$RALPH_DIR/workers/worker-TASK-001-12345/agent.pid"

    # PID file should be removed
    [ ! -f "$RALPH_DIR/workers/worker-TASK-001-12345/agent.pid" ]
) && test_pass || test_fail "Stale PID not cleaned"

# Test 7: Is worker running (not running)
test_start "Is worker running - not running"
(
    setup_test_env
    source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"

    mkdir -p "$RALPH_DIR/workers/worker-TASK-001-12345"

    # No PID file means not running
    ! is_worker_running "$RALPH_DIR/workers/worker-TASK-001-12345"
) && test_pass || test_fail "Should report not running"

# Test 8: Scan active workers (empty)
test_start "Scan active workers - empty"
(
    setup_test_env
    source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"

    local result
    result=$(scan_active_workers "$RALPH_DIR")
    [ -z "$result" ]
) && test_pass || test_fail "Should find no active workers"

# Test 9: Wait for worker PID (timeout)
test_start "Wait for worker PID - timeout"
(
    setup_test_env
    source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"

    mkdir -p "$RALPH_DIR/workers/worker-TASK-001-12345"

    # Should timeout quickly (1 decisecond = 0.1 second)
    ! wait_for_worker_pid "$RALPH_DIR/workers/worker-TASK-001-12345" 1
) && test_pass || test_fail "Should timeout"

# Test 10: Write and remove PID file with locking
test_start "Write and remove PID file with locking"
(
    setup_test_env
    source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"

    mkdir -p "$RALPH_DIR/workers/worker-TASK-001-12345"
    local pid_file="$RALPH_DIR/workers/worker-TASK-001-12345/agent.pid"

    # Write PID
    write_pid_file "$pid_file" "12345"
    [ -f "$pid_file" ] && [ "$(cat "$pid_file")" = "12345" ]

    # Remove PID
    remove_pid_file "$pid_file"
    [ ! -f "$pid_file" ]
) && test_pass || test_fail "PID file operations failed"

# Test 11: File lock for kanban update
test_start "File lock for kanban update"
(
    setup_test_env
    source "$WIGGUM_HOME/lib/core/file-lock.sh"

    update_kanban_status "$RALPH_DIR/kanban.md" "TASK-001" "="

    grep -q '\[=\].*TASK-001' "$RALPH_DIR/kanban.md"
) && test_pass || test_fail "Kanban not updated"

# Test 12: Config validation
test_start "Config validation - valid JSON"
(
    source "$WIGGUM_HOME/lib/core/config-validator.sh"

    # Validate existing config files
    validate_json_file "$WIGGUM_HOME/config/config.json"
) && test_pass || test_fail "Config validation failed"

# =============================================================================
# SUMMARY
# =============================================================================

echo ""
echo "=== Test Summary ==="
echo "Total: $TEST_COUNT"
echo "Passed: $PASS_COUNT"
echo "Failed: $FAIL_COUNT"

if [ $FAIL_COUNT -gt 0 ]; then
    exit 1
fi
exit 0
