#!/usr/bin/env bash
# agent-runner.sh - Generic agent lifecycle management
#
# Provides common functionality for all agent types:
# - PID recording in agent.pid
# - Signal handling for graceful shutdown
# - Workspace violation flag detection
# - Logging setup
#
# Usage:
#   source "$WIGGUM_HOME/lib/worker/agent-runner.sh"
#   agent_runner_init "$agent_dir" "$project_dir"
#   # ... run your agent logic ...
#   agent_runner_cleanup
set -euo pipefail

source "$WIGGUM_HOME/lib/core/defaults.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"

# Global state for agent runner
_AGENT_RUNNER_DIR=""
_AGENT_RUNNER_PROJECT_DIR=""
_AGENT_RUNNER_INTERRUPTED=false
_AGENT_RUNNER_CHILD_PID=""

# Initialize agent runner
#
# Sets up:
# - PID file (agent.pid)
# - Log file reference
# - Violation monitoring
# - Signal handlers
#
# Args:
#   agent_dir    - Directory for this agent instance (e.g., .ralph/workers/worker-TASK-001-xxx)
#   project_dir  - Project root directory
#   monitor_interval - Violation monitor interval in seconds (default: 30, 0 to disable)
#
# Returns: 0 on success, 1 on failure
agent_runner_init() {
    local agent_dir="$1"
    local project_dir="$2"
    local monitor_interval="${3:-30}"
    export monitor_interval  # Available to subclasses

    if [ -z "$agent_dir" ] || [ -z "$project_dir" ]; then
        log_error "agent_runner_init: agent_dir and project_dir are required"
        return 1
    fi

    _AGENT_RUNNER_DIR="$agent_dir"
    _AGENT_RUNNER_PROJECT_DIR="$project_dir"
    _AGENT_RUNNER_INTERRUPTED=false

    # Ensure agent directory exists
    mkdir -p "$agent_dir"

    # Record PID - use BASHPID to get actual process ID (not parent's $$ in subshells)
    # Security: Atomic write with restricted permissions (write-then-rename)
    (umask 077; echo "$BASHPID" > "$agent_dir/agent.pid.tmp" && mv "$agent_dir/agent.pid.tmp" "$agent_dir/agent.pid")
    log_debug "Agent PID $BASHPID recorded in $agent_dir/agent.pid"

    # Setup signal handlers
    trap '_agent_runner_signal_handler' INT TERM

    # NOTE: Violation monitoring is now handled by each agent individually
    # (e.g., system.task-worker starts its own log-based monitor)
    # The generic git-status-based monitor was removed because it caused
    # false positives when multiple workers run concurrently.

    return 0
}

# Internal signal handler
_agent_runner_signal_handler() {
    log "Agent received shutdown signal"
    _AGENT_RUNNER_INTERRUPTED=true

    # Kill child process if running
    if [ -n "$_AGENT_RUNNER_CHILD_PID" ] && kill -0 "$_AGENT_RUNNER_CHILD_PID" 2>/dev/null; then
        log "Terminating child process (PID: $_AGENT_RUNNER_CHILD_PID)"
        kill -TERM "$_AGENT_RUNNER_CHILD_PID" 2>/dev/null || true
        wait "$_AGENT_RUNNER_CHILD_PID" 2>/dev/null || true
    fi
}

# Register a child process for signal handling
#
# Args:
#   child_pid - PID of the child process to track
agent_runner_register_child() {
    _AGENT_RUNNER_CHILD_PID="$1"
}

# Check if shutdown was requested
#
# Returns: 0 if interrupted, 1 if not
agent_runner_interrupted() {
    [ "$_AGENT_RUNNER_INTERRUPTED" = true ]
}

# Detect workspace violations
#
# Checks if a violation was detected by the log-based violation monitor.
# The monitor parses iteration logs for Edit/Write/Bash tool calls outside workspace.
#
# NOTE: Previously this function checked git status in the main repo, which caused
# false positives when multiple workers ran concurrently (one worker's violation
# would flag all workers). Now it only checks the worker-specific violation flag.
#
# Args:
#   workspace   - The workspace directory (unused, kept for API compatibility)
#   project_dir - The project root directory (optional, uses init value)
#
# Returns: 0 if no violations, 1 if violations detected
agent_runner_detect_violations() {
    local workspace="$1"
    local project_dir="${2:-$_AGENT_RUNNER_PROJECT_DIR}"

    log_debug "Checking for workspace boundary violations"

    # Check if the log-based violation monitor flagged this worker
    if [[ -f "$_AGENT_RUNNER_DIR/violation_flag.txt" ]]; then
        log_error "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        log_error "⚠️  CRITICAL: Workspace boundary violation detected!"
        log_error "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        log_error ""
        log_error "Violation details:"
        cat "$_AGENT_RUNNER_DIR/violation_flag.txt" | while read -r line; do
            log_error "  $line"
        done
        log_error ""
        log_error "Expected workspace: $workspace"
        log_error ""

        # Log violation with timestamp
        mkdir -p "${RALPH_DIR:-$project_dir/.ralph}/logs"
        {
            echo "================================================================================"
            echo "VIOLATION: Workspace Escape"
            echo "Timestamp: $(iso_now)"
            echo "Agent Dir: $_AGENT_RUNNER_DIR"
            cat "$_AGENT_RUNNER_DIR/violation_flag.txt"
            echo "================================================================================"
            echo ""
        } >> "${RALPH_DIR:-$project_dir/.ralph}/logs/violations.log"

        return 1
    fi

    log_debug "No workspace violations detected"
    return 0
}

# Check if violation flag was set by monitor
#
# Returns: 0 if violation detected, 1 otherwise
agent_runner_has_violation_flag() {
    [[ -f "$_AGENT_RUNNER_DIR/violation_flag.txt" ]]
}

# Cleanup agent runner
#
# Removes PID file and clears state.
# Should be called when agent completes or on exit.
agent_runner_cleanup() {
    log_debug "Agent runner cleanup"

    # Remove PID file
    if [ -n "$_AGENT_RUNNER_DIR" ] && [ -f "$_AGENT_RUNNER_DIR/agent.pid" ]; then
        rm -f "$_AGENT_RUNNER_DIR/agent.pid"
        log_debug "Removed agent PID file"
    fi

    # Clear state
    _AGENT_RUNNER_DIR=""
    _AGENT_RUNNER_PROJECT_DIR=""
    _AGENT_RUNNER_CHILD_PID=""
}

# Get the agent directory
agent_runner_get_dir() {
    echo "$_AGENT_RUNNER_DIR"
}

# Get the project directory
agent_runner_get_project_dir() {
    echo "$_AGENT_RUNNER_PROJECT_DIR"
}
