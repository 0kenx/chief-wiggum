#!/usr/bin/env bash
# =============================================================================
# Signal Handling Integration Test
#
# Tests graceful shutdown when receiving SIGTERM/SIGINT:
# - PID file removed on signal
# - Cleanup hooks fired
# - Child process (mock claude) terminated
# - No zombie processes
# =============================================================================

set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$TESTS_DIR/mocks/mock-helpers.sh"

TEST_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    mock_setup
    export CLAUDE="$TESTS_DIR/mocks/mock-claude.sh"
    export LOG_FILE="$TEST_DIR/test.log"
}

teardown() {
    mock_teardown
    # Kill any leftover background processes
    jobs -p 2>/dev/null | xargs -r kill 2>/dev/null || true
    wait 2>/dev/null || true
    rm -rf "$TEST_DIR"
}

# =============================================================================
# Test: Agent runner creates and removes PID file
# =============================================================================
test_pid_file_lifecycle() {
    source "$WIGGUM_HOME/lib/worker/agent-runner.sh"

    local agent_dir="$TEST_DIR/agent-pid"
    local project_dir="$TEST_DIR/project"
    mkdir -p "$project_dir"

    # Init creates PID file
    agent_runner_init "$agent_dir" "$project_dir" 0
    assert_file_exists "$agent_dir/agent.pid" "PID file should exist after init"

    local pid_content
    pid_content=$(cat "$agent_dir/agent.pid")
    assert_not_equals "" "$pid_content" "PID file should contain a PID"

    # Cleanup removes PID file
    agent_runner_cleanup
    assert_file_not_exists "$agent_dir/agent.pid" "PID file should be removed after cleanup"
}

# =============================================================================
# Test: Signal sets interrupted flag
# =============================================================================
test_signal_sets_interrupted_flag() {
    source "$WIGGUM_HOME/lib/worker/agent-runner.sh"

    local agent_dir="$TEST_DIR/agent-signal"
    local project_dir="$TEST_DIR/project"
    mkdir -p "$project_dir"

    agent_runner_init "$agent_dir" "$project_dir" 0

    # Initially not interrupted
    assert_failure "Should not be interrupted initially" agent_runner_interrupted

    # Simulate signal handler
    _AGENT_RUNNER_INTERRUPTED=true

    # Now should be interrupted
    assert_success "Should be interrupted after signal" agent_runner_interrupted

    agent_runner_cleanup
}

# =============================================================================
# Test: Child process is terminated on signal
# =============================================================================
test_child_process_termination() {
    source "$WIGGUM_HOME/lib/worker/agent-runner.sh"

    local agent_dir="$TEST_DIR/agent-child-term"
    local project_dir="$TEST_DIR/project"
    mkdir -p "$project_dir"

    agent_runner_init "$agent_dir" "$project_dir" 0

    # Start a background child process (sleep simulating claude)
    sleep 300 &
    local child_pid=$!
    agent_runner_register_child "$child_pid"

    # Verify child is running
    assert_success "Child process should be running" kill -0 "$child_pid"

    # Simulate signal handler (which kills child)
    _agent_runner_signal_handler

    # Give child a moment to die
    sleep 0.1

    # Child should be terminated
    assert_failure "Child process should be terminated" kill -0 "$child_pid"

    agent_runner_cleanup
}

# =============================================================================
# Test: SIGTERM to ralph loop sets shutdown flag
# =============================================================================
test_ralph_loop_sigterm_shutdown() {
    source "$WIGGUM_HOME/lib/claude/run-claude-ralph-loop.sh"

    # Use a slow mock so we can signal during execution
    export MOCK_CLAUDE_DELAY="2"
    export MOCK_CLAUDE_RESPONSE="Working..."

    local workspace="$TEST_DIR/workspace"
    local output_dir="$TEST_DIR/output"
    mkdir -p "$workspace" "$output_dir"

    _test_prompt() { echo "Continue"; }
    _test_never_done() { return 1; }

    # Run ralph loop in background
    run_ralph_loop "$workspace" "System" \
        "_test_prompt" "_test_never_done" \
        10 5 "$output_dir" "test" &
    local loop_pid=$!

    # Wait for it to start
    sleep 0.5

    # Send SIGTERM
    kill -TERM "$loop_pid" 2>/dev/null || true

    # Wait for it to finish
    wait "$loop_pid" 2>/dev/null || true

    # Should have only 1-2 invocations (not 10)
    local invocation_count
    invocation_count=$(mock_get_invocation_count)
    assert_greater_than 10 "$invocation_count" \
        "Should have fewer than 10 invocations after SIGTERM"
}

# =============================================================================
# Test: No zombie processes after cleanup
# =============================================================================
test_no_zombie_processes() {
    source "$WIGGUM_HOME/lib/worker/agent-runner.sh"

    local agent_dir="$TEST_DIR/agent-zombie"
    local project_dir="$TEST_DIR/project"
    mkdir -p "$project_dir"

    agent_runner_init "$agent_dir" "$project_dir" 0

    # Start and immediately end a child
    sleep 0 &
    local child_pid=$!
    agent_runner_register_child "$child_pid"
    wait "$child_pid" 2>/dev/null || true

    # Run cleanup
    agent_runner_cleanup

    # Check no zombies from our test
    local zombies
    zombies=$(ps -eo state,ppid 2>/dev/null | grep "^Z.*$$" | wc -l)
    assert_equals "0" "$zombies" "Should have no zombie processes"
}

# =============================================================================
# Test: EXIT trap fires after signal
# =============================================================================
test_exit_trap_fires() {
    local marker_file="$TEST_DIR/exit-trap-marker"

    # Run a subshell that sets an EXIT trap then receives SIGTERM
    (
        trap 'touch "$marker_file"' EXIT
        sleep 300
    ) &
    local subshell_pid=$!

    sleep 0.2
    kill -TERM "$subshell_pid" 2>/dev/null || true
    wait "$subshell_pid" 2>/dev/null || true

    # The EXIT trap in bash fires on SIGTERM
    # (This tests the general behavior, not wiggum-specific)
    # Note: This test validates that our trap EXIT approach works
    assert_file_exists "$marker_file" "Exit trap should have created marker file on SIGTERM"
}

# =============================================================================
# Run all tests
# =============================================================================
run_test test_pid_file_lifecycle
run_test test_signal_sets_interrupted_flag
run_test test_child_process_termination
run_test test_ralph_loop_sigterm_shutdown
run_test test_no_zombie_processes
run_test test_exit_trap_fires

print_test_summary
exit_with_test_result
