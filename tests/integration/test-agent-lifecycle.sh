#!/usr/bin/env bash
# test-agent-lifecycle.sh - Integration tests for agent lifecycle hooks
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
- [ ] **[TASK-001]** Test task
EOF
}

# =============================================================================
# TESTS
# =============================================================================

echo "=== Agent Lifecycle Integration Tests ==="
echo ""

# Test 1: Agent metadata initialization
test_start "Agent metadata initialization"
(
    source "$WIGGUM_HOME/lib/core/agent-base.sh"
    agent_init_metadata "test-agent" "Test agent description"
    [ "$AGENT_TYPE" = "test-agent" ] && [ "$AGENT_DESCRIPTION" = "Test agent description" ]
) && test_pass || test_fail "Metadata not set correctly"

# Test 2: Agent context setup
test_start "Agent context setup"
(
    source "$WIGGUM_HOME/lib/core/agent-base.sh"
    agent_setup_context "/worker/dir" "/workspace" "/project" "TASK-001"
    [ "$(agent_get_worker_dir)" = "/worker/dir" ] && \
    [ "$(agent_get_workspace)" = "/workspace" ] && \
    [ "$(agent_get_project_dir)" = "/project" ] && \
    [ "$(agent_get_task_id)" = "TASK-001" ]
) && test_pass || test_fail "Context not set correctly"

# Test 3: Agent config loading
test_start "Agent config loading"
(
    source "$WIGGUM_HOME/lib/core/agent-base.sh"
    load_agent_config "task-worker"
    [ -n "$AGENT_CONFIG_MAX_ITERATIONS" ] && [ -n "$AGENT_CONFIG_MAX_TURNS" ]
) && test_pass || test_fail "Config not loaded"

# Test 4: Agent result writing
test_start "Agent result writing"
(
    setup_test_env
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-12345"
    mkdir -p "$worker_dir"

    # Initialize task ID context
    _AGENT_TASK_ID="TASK-001"

    agent_write_result "$worker_dir" "success" 0 '{"pr_url":"https://github.com/test"}' '[]' '{}'

    [ -f "$worker_dir/agent-result.json" ] && \
    grep -q '"status": "success"' "$worker_dir/agent-result.json"
) && test_pass || test_fail "Result file not created or invalid"

# Test 5: Agent result reading
test_start "Agent result reading"
(
    setup_test_env
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-12345"
    mkdir -p "$worker_dir"
    _AGENT_TASK_ID="TASK-001"

    agent_write_result "$worker_dir" "success" 0 '{"validation_result":"PASS"}' '[]' '{}'

    local status
    status=$(agent_read_result "$worker_dir" ".status")
    [ "$status" = "success" ]
) && test_pass || test_fail "Could not read result"

# Test 6: Agent output get/set
test_start "Agent output get/set"
(
    setup_test_env
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-12345"
    mkdir -p "$worker_dir"
    _AGENT_TASK_ID="TASK-001"

    agent_write_result "$worker_dir" "success" 0 '{}' '[]' '{}'
    agent_set_output "$worker_dir" "test_key" "test_value"

    local value
    value=$(agent_get_output "$worker_dir" "test_key")
    [ "$value" = "test_value" ]
) && test_pass || test_fail "Output get/set failed"

# Test 7: Agent error adding
test_start "Agent error adding"
(
    setup_test_env
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-12345"
    mkdir -p "$worker_dir"
    _AGENT_TASK_ID="TASK-001"

    agent_write_result "$worker_dir" "failure" 1 '{}' '[]' '{}'
    agent_add_error "$worker_dir" "Test error message"

    grep -q "Test error message" "$worker_dir/agent-result.json"
) && test_pass || test_fail "Error not added"

# Test 8: Communication path generation
test_start "Communication path generation"
(
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local worker_dir="/test/worker"
    [ "$(agent_comm_path "$worker_dir" "result")" = "/test/worker/agent-result.json" ] && \
    [ "$(agent_comm_path "$worker_dir" "validation")" = "/test/worker/validation-result.txt" ] && \
    [ "$(agent_comm_path "$worker_dir" "workspace")" = "/test/worker/workspace" ]
) && test_pass || test_fail "Paths not generated correctly"

# Test 9: Directory creation
test_start "Agent directory creation"
(
    setup_test_env
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local worker_dir="$RALPH_DIR/workers/worker-TASK-002-12345"
    agent_create_directories "$worker_dir"

    [ -d "$worker_dir/logs" ] && [ -d "$worker_dir/summaries" ]
) && test_pass || test_fail "Directories not created"

# Test 10: Subagent result reading
test_start "Subagent result reading"
(
    setup_test_env
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local worker_dir="$RALPH_DIR/workers/worker-TASK-001-12345"
    mkdir -p "$worker_dir"
    _AGENT_TASK_ID="TASK-001"

    # Create with output
    agent_write_result "$worker_dir" "success" 0 '{"VALIDATION_result":"PASS"}' '[]' '{}'

    local result
    result=$(agent_read_subagent_result "$worker_dir" "VALIDATION_result" "validation-result.txt")
    [ "$result" = "PASS" ]
) && test_pass || test_fail "Subagent result not read"

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
