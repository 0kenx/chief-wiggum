#!/usr/bin/env bash
# =============================================================================
# lifecycle.sh - Orchestrator lifecycle management
#
# Extracted from wiggum-run main() to keep the orchestrator script lean.
# Handles project validation, lock acquisition, signal setup, rate limiting,
# and final summary display.
#
# Provides:
#   _validate_project()          - Check .ralph/ exists, kanban exists
#   _acquire_lock()              - Write orchestrator.pid, check for existing
#   _release_lock()              - Remove orchestrator.pid
#   _setup_signals()             - Trap EXIT/INT/TERM/WINCH
#   _check_rate_limit_pause()    - Check/wait for rate-limit-pause file
#   _display_final_summary()     - Final output on exit
# =============================================================================
set -euo pipefail

[ -n "${_ORCHESTRATOR_LIFECYCLE_LOADED:-}" ] && return 0
_ORCHESTRATOR_LIFECYCLE_LOADED=1

# Source platform helpers for portable time functions
source "$WIGGUM_HOME/lib/core/platform.sh"

# Validate that the project is properly initialized
#
# Checks:
#   - .ralph/ directory exists
#   - .ralph/kanban.md exists
#
# Exits with appropriate error code if validation fails
_validate_project() {
    if [ ! -d "$RALPH_DIR" ]; then
        log_error ".ralph/ directory not found. Run 'wiggum init' first."
        exit $EXIT_RUN_NO_RALPH_DIR
    fi

    if [ ! -f "$RALPH_DIR/kanban.md" ]; then
        log_error ".ralph/kanban.md not found. Create a kanban file first."
        exit $EXIT_RUN_NO_KANBAN
    fi
}

# Acquire orchestrator lock (PID file)
#
# Ensures only one orchestrator runs at a time. Checks for existing lock
# and handles stale/reused PIDs.
#
# Uses globals:
#   RALPH_DIR    - Ralph directory path
#   FORCE_LOCK   - If true, override existing lock
#
# Sets globals:
#   orchestrator_lock - Path to lock file (needed by trap handler)
_acquire_lock() {
    orchestrator_lock="$RALPH_DIR/orchestrator/orchestrator.pid"

    if [ -f "$orchestrator_lock" ]; then
        local existing_pid
        existing_pid=$(cat "$orchestrator_lock" 2>/dev/null)

        # Validate PID is a number
        if [[ "$existing_pid" =~ ^[0-9]+$ ]]; then
            if kill -0 "$existing_pid" 2>/dev/null; then
                if ps -p "$existing_pid" -o args= 2>/dev/null | grep -q "wiggum-run"; then
                    if [ "$FORCE_LOCK" = true ]; then
                        log "WARNING: Overriding lock held by running orchestrator (PID: $existing_pid) due to --force"
                        rm -f "$orchestrator_lock"
                    else
                        log_error "Another wiggum-run orchestrator is already running (PID: $existing_pid)"
                        echo ""
                        echo "Only one orchestrator can run at a time to prevent conflicts."
                        echo "If you're sure no orchestrator is running, remove: $orchestrator_lock"
                        echo "Or use --force to override the lock."
                        exit $EXIT_RUN_ORCHESTRATOR_RUNNING
                    fi
                else
                    log "Cleaning stale orchestrator lock (PID reused)"
                    rm -f "$orchestrator_lock"
                fi
            else
                log "Cleaning stale orchestrator lock"
                rm -f "$orchestrator_lock"
            fi
        else
            log "Cleaning invalid orchestrator lock"
            rm -f "$orchestrator_lock"
        fi
    fi

    echo "$$" > "$orchestrator_lock"
    log "Created orchestrator lock (PID: $$)"
}

# Release orchestrator lock
_release_lock() {
    local lock_file="$RALPH_DIR/orchestrator/orchestrator.pid"
    rm -f "$lock_file"
}

# Set up signal handlers for graceful shutdown
#
# Uses globals:
#   _ORCH_SHUTDOWN_REQUESTED - Tracks shutdown state
_setup_signals() {
    _ORCH_SHUTDOWN_REQUESTED=false

    cleanup_orchestrator() {
        if [ "${_ORCH_SHUTDOWN_REQUESTED:-false}" = false ]; then
            log "Cleaning up orchestrator lock"
            _ORCH_SHUTDOWN_REQUESTED=true
            _release_lock
        fi
    }
    trap cleanup_orchestrator EXIT

    handle_shutdown_signal() {
        log ""
        log "Shutdown signal received - stopping orchestrator"
        log "Active workers will continue running to completion"
        log "Use 'wiggum status' to monitor worker progress"
        cleanup_orchestrator
        exit $EXIT_SIGINT
    }
    trap handle_shutdown_signal INT TERM
}

# Check for rate limit pause file and wait if needed
#
# Reads .ralph/orchestrator/rate-limit-pause for resume timestamp.
# If present and not expired, waits until the specified time.
_check_rate_limit_pause() {
    local pause_file="$RALPH_DIR/orchestrator/rate-limit-pause"
    [ -f "$pause_file" ] || return 0

    local resume_at
    resume_at=$(cat "$pause_file" 2>/dev/null)
    [ -n "$resume_at" ] || return 0

    local now
    now=$(epoch_now)

    if [ "$now" -lt "$resume_at" ]; then
        local wait_seconds=$((resume_at - now))
        log "Rate limit pause: waiting ${wait_seconds}s"
        sleep "$wait_seconds"
    fi

    rm -f "$pause_file"
}

# Display final summary when orchestrator exits
#
# Shows completion status, worker results, and any errors.
_display_final_summary() {
    display_final_summary "$RALPH_DIR"
}
