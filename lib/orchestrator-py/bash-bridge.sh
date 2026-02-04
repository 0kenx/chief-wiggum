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

# =============================================================================
# Directory validation — refuse to run with empty/missing paths.
# Every variable that participates in path construction is validated here
# so that a missing value produces "not set" instead of bare /foo paths.
# =============================================================================
WIGGUM_HOME="${WIGGUM_HOME:?WIGGUM_HOME not set}"
PROJECT_DIR="${PROJECT_DIR:?PROJECT_DIR not set}"
RALPH_DIR="${RALPH_DIR:?RALPH_DIR not set}"

# Belt-and-suspenders: verify the :? guard caught both unset AND empty
_assert_dir() {
    if [[ -z "$2" ]]; then
        echo "FATAL: $1 is empty — refusing to run (would produce /$3 paths)" >&2
        exit 1
    fi
}
_assert_dir "WIGGUM_HOME" "$WIGGUM_HOME" "lib/..."
_assert_dir "PROJECT_DIR" "$PROJECT_DIR" ".ralph/..."
_assert_dir "RALPH_DIR"   "$RALPH_DIR"   "kanban.md"

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

# =============================================================================
# Minimal init for bridge mode.
#
# Python manages service scheduling and state persistence. The bridge only
# needs library functions sourced so svc_* handlers can call them. We
# deliberately skip:
#   - service_state_init/restore  (would load state.json via jq on every call)
#   - service_scheduler_init      (would load services.json + state via jq)
#
# We DO call scheduler_init (lib/scheduler/scheduler.sh) — it's cheap (just
# variable assignments + pool_init + touch) and sets _SCHED_RALPH_DIR which
# all scheduler module functions use instead of $RALPH_DIR.
#
# _SERVICE_STATE_FILE stays empty (""), so bash service_state_save() returns
# early at its [ -n "$_SERVICE_STATE_FILE" ] guard — no risk of overwriting
# the state file that Python manages.
# =============================================================================

# Default handler variables (set before scheduler_init which may read them)
AGING_FACTOR="${AGING_FACTOR:-7}"
SIBLING_WIP_PENALTY="${SIBLING_WIP_PENALTY:-20000}"
PLAN_BONUS="${PLAN_BONUS:-15000}"
DEP_BONUS_PER_TASK="${DEP_BONUS_PER_TASK:-7000}"
RESUME_INITIAL_BONUS="${RESUME_INITIAL_BONUS:-20000}"
RESUME_FAIL_PENALTY="${RESUME_FAIL_PENALTY:-8000}"
RESUME_MIN_RETRY_INTERVAL="${RESUME_MIN_RETRY_INTERVAL:-30}"
MAX_SKIP_RETRIES="${MAX_SKIP_RETRIES:-3}"
PID_WAIT_TIMEOUT="${PID_WAIT_TIMEOUT:-300}"
MAX_WORKERS="${MAX_WORKERS:-4}"
MAX_ITERATIONS="${MAX_ITERATIONS:-20}"
MAX_TURNS="${MAX_TURNS:-50}"
FIX_WORKER_TIMEOUT="${FIX_WORKER_TIMEOUT:-7200}"
RESOLVE_WORKER_TIMEOUT="${RESOLVE_WORKER_TIMEOUT:-7200}"
WIGGUM_RUN_MODE="${WIGGUM_RUN_MODE:-default}"
WIGGUM_NO_RESUME="${WIGGUM_NO_RESUME:-false}"
WIGGUM_NO_FIX="${WIGGUM_NO_FIX:-false}"
WIGGUM_NO_MERGE="${WIGGUM_NO_MERGE:-false}"
WIGGUM_NO_SYNC="${WIGGUM_NO_SYNC:-false}"
_ORCH_ITERATION="${_ORCH_ITERATION:-0}"
_ORCH_TICK_EPOCH="${_ORCH_TICK_EPOCH:-$(date +%s)}"

# Initialize the scheduler module (sets _SCHED_RALPH_DIR, pool state, etc.)
# This is cheap — just variable assignments, no jq/subprocess calls.
scheduler_init "$RALPH_DIR" "$PROJECT_DIR" \
    "$AGING_FACTOR" "$SIBLING_WIP_PENALTY" "$PLAN_BONUS" "$DEP_BONUS_PER_TASK" \
    "$RESUME_INITIAL_BONUS" "$RESUME_FAIL_PENALTY"

# Verify scheduler_init actually set _SCHED_RALPH_DIR
_assert_dir "_SCHED_RALPH_DIR" "${_SCHED_RALPH_DIR:-}" "kanban.md"

# Restore pool state from live worker directories.
# Each bridge invocation is a fresh process — scheduler_init clears the pool.
# Without this, pool_count() always returns 0 and worker limits are never enforced.
pool_restore_from_workers "$RALPH_DIR"
pool_ingest_pending "$RALPH_DIR"

# Load configs that handler functions depend on at call time
load_log_rotation_config 2>/dev/null || true
log_rotation_init "$RALPH_DIR/logs" 2>/dev/null || true
load_rate_limit_config 2>/dev/null || true
load_workers_config 2>/dev/null || true
FIX_WORKER_LIMIT="${FIX_WORKER_LIMIT:-${WIGGUM_FIX_WORKER_LIMIT:-2}}"
load_resume_queue_config 2>/dev/null || true
load_resume_config 2>/dev/null || true

# =============================================================================
# Dispatch
# =============================================================================

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
