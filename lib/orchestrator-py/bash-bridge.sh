#!/usr/bin/env bash
# =============================================================================
# bash-bridge.sh - Bridge between Python orchestrator and bash svc_* functions
#
# Sources all required libraries (same as wiggum-run) then dispatches calls
# to svc_* functions. Called by the Python service executor in two modes:
#
#   phase <phase-name> <func1> <func2> ...
#     Run all listed functions sequentially in one process (shared state).
#
#   function <func-name> [args...]
#     Run a single function with optional arguments.
#
# Security: Only svc_* prefixed functions are allowed.
# =============================================================================
set -euo pipefail

WIGGUM_HOME="${WIGGUM_HOME:?WIGGUM_HOME not set}"
PROJECT_DIR="${PROJECT_DIR:?PROJECT_DIR not set}"
RALPH_DIR="${RALPH_DIR:?RALPH_DIR not set}"

# Source shared libraries (same list as wiggum-run)
source "$WIGGUM_HOME/lib/core/exit-codes.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"
source "$WIGGUM_HOME/lib/core/verbose-flags.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"
source "$WIGGUM_HOME/lib/utils/audit-logger.sh"
source "$WIGGUM_HOME/lib/utils/activity-log.sh"
source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"
source "$WIGGUM_HOME/lib/worker/git-state.sh"
source "$WIGGUM_HOME/lib/runtime/runtime.sh"
source "$WIGGUM_HOME/lib/backend/claude/usage-tracker.sh"
source "$WIGGUM_HOME/lib/git/worktree-helpers.sh"
source "$WIGGUM_HOME/lib/tasks/task-parser.sh"
source "$WIGGUM_HOME/lib/tasks/plan-parser.sh"
source "$WIGGUM_HOME/lib/tasks/conflict-detection.sh"

# Source scheduler module
source "$WIGGUM_HOME/lib/scheduler/scheduler.sh"
source "$WIGGUM_HOME/lib/scheduler/conflict-queue.sh"
source "$WIGGUM_HOME/lib/scheduler/conflict-registry.sh"
source "$WIGGUM_HOME/lib/scheduler/pr-merge-optimizer.sh"
source "$WIGGUM_HOME/lib/scheduler/orchestrator-functions.sh"
source "$WIGGUM_HOME/lib/scheduler/smart-routing.sh"

# Service-based scheduler (for state functions)
source "$WIGGUM_HOME/lib/service/service-scheduler.sh"
# Service handlers (svc_* functions)
source "$WIGGUM_HOME/lib/services/orchestrator-handlers.sh"
# Orchestrator directory migration
source "$WIGGUM_HOME/lib/orchestrator/migration.sh"
# Orchestrator lifecycle
source "$WIGGUM_HOME/lib/orchestrator/lifecycle.sh"

# Log rotation
source "$WIGGUM_HOME/lib/core/log-rotation.sh"

# Initialize activity log
activity_init "$PROJECT_DIR"

# Initialize service state for handler functions that use it
service_state_init "$RALPH_DIR"

# Try to restore state for continuity
service_state_restore 2>/dev/null || true

# Initialize scheduler state (needed by scheduler_tick, etc.)
# Only initialize if not already done — some functions depend on this
if [[ "${_SCHED_INITIALIZED:-false}" != "true" ]]; then
    service_scheduler_init "$RALPH_DIR" "$PROJECT_DIR"
fi

# Load log rotation config
load_log_rotation_config 2>/dev/null || true
log_rotation_init "$RALPH_DIR/logs" 2>/dev/null || true

# Load rate limit config
load_rate_limit_config 2>/dev/null || true

# Load workers config
load_workers_config 2>/dev/null || true
FIX_WORKER_LIMIT="${FIX_WORKER_LIMIT:-${WIGGUM_FIX_WORKER_LIMIT:-2}}"

# Load resume configs
load_resume_queue_config 2>/dev/null || true
load_resume_config 2>/dev/null || true

# Default variables that handlers expect
MAX_SKIP_RETRIES="${MAX_SKIP_RETRIES:-3}"
PID_WAIT_TIMEOUT="${PID_WAIT_TIMEOUT:-300}"
AGING_FACTOR="${AGING_FACTOR:-7}"
SIBLING_WIP_PENALTY="${SIBLING_WIP_PENALTY:-20000}"
PLAN_BONUS="${PLAN_BONUS:-15000}"
DEP_BONUS_PER_TASK="${DEP_BONUS_PER_TASK:-7000}"
RESUME_INITIAL_BONUS="${RESUME_INITIAL_BONUS:-20000}"
RESUME_FAIL_PENALTY="${RESUME_FAIL_PENALTY:-8000}"
RESUME_MIN_RETRY_INTERVAL="${RESUME_MIN_RETRY_INTERVAL:-30}"
WIGGUM_RUN_MODE="${WIGGUM_RUN_MODE:-default}"
_ORCH_ITERATION="${_ORCH_ITERATION:-0}"
_ORCH_TICK_EPOCH="${_ORCH_TICK_EPOCH:-$(date +%s)}"

# Validate function name (security: only svc_* allowed)
_validate_func() {
    local func="$1"
    if [[ "$func" != svc_* ]]; then
        echo "ERROR: Only svc_* functions allowed, got: $func" >&2
        return 1
    fi
    if ! declare -F "$func" &>/dev/null; then
        echo "ERROR: Function not found: $func" >&2
        return 1
    fi
    return 0
}

# Main dispatch
mode="${1:?Usage: bash-bridge.sh <phase|function> ...}"
shift

case "$mode" in
    phase)
        # shellcheck disable=SC2034  # phase consumed for validation
        phase="${1:?Missing phase name}"
        shift
        for func in "$@"; do
            _validate_func "$func" || exit 1
            "$func" || true
        done
        ;;
    function)
        func="${1:?Missing function name}"
        shift
        _validate_func "$func" || exit 1
        "$func" "$@"
        ;;
    *)
        echo "ERROR: Unknown mode: $mode (expected: phase|function)" >&2
        exit 1
        ;;
esac
