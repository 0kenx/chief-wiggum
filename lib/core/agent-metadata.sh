#!/usr/bin/env bash
# =============================================================================
# agent-metadata.sh - Agent metadata, context, and initialization
#
# Provides:
#   - Metadata setup (agent_init_metadata)
#   - Callback context management (agent_setup_context)
#   - Common dependency sourcing (agent_source_*)
#   - Default lifecycle hook implementations
#   - Logging helpers
#
# Split from agent-base.sh for maintainability.
# =============================================================================
set -euo pipefail

[ -n "${_AGENT_METADATA_LOADED:-}" ] && return 0
_AGENT_METADATA_LOADED=1

# Source platform.sh at top level for portable helper functions (find_newest, grep_pcre_*, etc.)
source "$WIGGUM_HOME/lib/core/platform.sh"

# =============================================================================
# METADATA SETUP
# =============================================================================

# Initialize agent metadata
#
# Args:
#   type        - Agent type identifier (e.g., "system.task-worker")
#   description - Human-readable description
#
# Sets and exports: AGENT_TYPE, AGENT_DESCRIPTION
agent_init_metadata() {
    local type="$1"
    local description="$2"

    AGENT_TYPE="$type"
    AGENT_DESCRIPTION="$description"
    export AGENT_TYPE AGENT_DESCRIPTION
}

# =============================================================================
# CALLBACK CONTEXT SETUP
# =============================================================================

# Agent context variables (set by agent_setup_context)
_AGENT_WORKER_DIR=""
_AGENT_WORKSPACE=""
_AGENT_PROJECT_DIR=""
_AGENT_TASK_ID=""
_AGENT_START_EPOCH=""

# Setup standard callback context for ralph loop
#
# Args:
#   worker_dir  - Worker directory path
#   workspace   - Workspace directory path (where code lives)
#   project_dir - Project root directory (optional)
#   task_id     - Task identifier (optional)
agent_setup_context() {
    _AGENT_WORKER_DIR="${1:-}"
    _AGENT_WORKSPACE="${2:-}"
    _AGENT_PROJECT_DIR="${3:-}"
    _AGENT_TASK_ID="${4:-}"
    _AGENT_START_EPOCH=$(date +%s)
}

# Get context values (for use in callbacks)
agent_get_worker_dir() { echo "$_AGENT_WORKER_DIR"; }
agent_get_workspace() { echo "$_AGENT_WORKSPACE"; }
agent_get_project_dir() { echo "$_AGENT_PROJECT_DIR"; }
agent_get_task_id() { echo "$_AGENT_TASK_ID"; }

# =============================================================================
# DEPENDENCY SOURCING
# =============================================================================

# Source core dependencies (logger, defaults)
agent_source_core() {
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/defaults.sh"
}

# Source ralph loop (unified execution pattern with optional supervision)
# Supervision is enabled by passing supervisor_interval > 0 to run_ralph_loop
agent_source_ralph() {
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
    source "$WIGGUM_HOME/lib/runtime/runtime-loop.sh"
}

# Alias for backward compatibility - sources the same unified ralph loop
# The run_ralph_loop_supervised function is defined in the unified file
agent_source_ralph_supervised() {
    agent_source_ralph
}

# Source one-shot agent execution (no iteration loop)
agent_source_once() {
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
}

# Source git operations
agent_source_git() {
    source "$WIGGUM_HOME/lib/git/worktree-helpers.sh"
    source "$WIGGUM_HOME/lib/git/git-operations.sh"
}

# Source task parsing utilities
agent_source_tasks() {
    source "$WIGGUM_HOME/lib/tasks/task-parser.sh"
}

# Source metrics and audit logging
agent_source_metrics() {
    source "$WIGGUM_HOME/lib/utils/audit-logger.sh"
    source "$WIGGUM_HOME/lib/utils/metrics-export.sh"
}

# Source agent registry (for sub-agent spawning)
agent_source_registry() {
    source "$WIGGUM_HOME/lib/worker/agent-registry.sh"
}

# Source file locking utilities
agent_source_lock() {
    source "$WIGGUM_HOME/lib/core/file-lock.sh"
}

# Source resume capabilities
agent_source_resume() {
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
}

# =============================================================================
# SECURE TEMP FILE HANDLING
# =============================================================================

# Create a secure temp file, preferring worker-local tmp directory
#
# This prevents race conditions with /tmp and ensures temp files
# are cleaned up with the worker directory.
#
# Args:
#   base_dir - Optional base directory (typically worker_dir)
#              If provided and valid, creates tmp/ subdirectory there
#              Otherwise falls back to TMPDIR or /tmp
#
# Returns: Path to newly created temp file
agent_mktemp() {
    local base_dir="${1:-}"
    local tmp_dir

    if [ -n "$base_dir" ] && [ -d "$base_dir" ]; then
        tmp_dir="$base_dir/tmp"
        mkdir -p "$tmp_dir"
    else
        tmp_dir="${TMPDIR:-/tmp}"
    fi

    mktemp -p "$tmp_dir"
}

# =============================================================================
# AGENT LOGGING HELPERS
# =============================================================================

# Log agent startup with full context and configuration
#
# Args:
#   worker_dir  - Worker directory path
#   config_pairs... - Optional key=value pairs to log
#
# Uses: AGENT_TYPE, WIGGUM_STEP_ID, WIGGUM_TASK_ID, AGENT_CONFIG_* variables
agent_log_startup() {
    local worker_dir="${1:-}"
    shift || true

    local worker_id=""
    [ -n "$worker_dir" ] && worker_id=$(basename "$worker_dir" 2>/dev/null || echo "")

    log_agent_header "${AGENT_TYPE:-unknown}" "$worker_id" "${WIGGUM_TASK_ID:-}"

    # Log standard agent config if available
    local has_config=false
    if [ -n "${AGENT_CONFIG_MAX_ITERATIONS:-}" ] || [ -n "${AGENT_CONFIG_MAX_TURNS:-}" ]; then
        has_config=true
        log_subsection "AGENT CONFIG"
        [ -n "${AGENT_CONFIG_MAX_ITERATIONS:-}" ] && log_kv "max_iterations" "$AGENT_CONFIG_MAX_ITERATIONS"
        [ -n "${AGENT_CONFIG_MAX_TURNS:-}" ] && log_kv "max_turns" "$AGENT_CONFIG_MAX_TURNS"
        [ -n "${AGENT_CONFIG_SUPERVISOR_INTERVAL:-}" ] && log_kv "supervisor_interval" "$AGENT_CONFIG_SUPERVISOR_INTERVAL"
        [ -n "${AGENT_CONFIG_MAX_RESTARTS:-}" ] && log_kv "max_restarts" "$AGENT_CONFIG_MAX_RESTARTS"
    fi

    # Log any extra config pairs passed as arguments
    if [ $# -ge 2 ]; then
        [ "$has_config" = false ] && log_subsection "AGENT CONFIG"
        while [ $# -ge 2 ]; do
            log_kv "$1" "$2"
            shift 2
        done
    fi
}

# Log agent phase start (e.g., "Execution", "Audit", "Summary")
#
# Args:
#   phase_name - Name of the phase
#   details... - Optional detail strings to log
agent_log_phase_start() {
    local phase_name="$1"
    shift || true

    log_subsection "PHASE: $phase_name"

    while [ $# -gt 0 ]; do
        log "  $1"
        shift
    done
}

# Log agent phase completion
#
# Args:
#   phase_name - Name of the phase
#   result     - Result (PASS, FAIL, SKIP, etc.)
#   details... - Optional detail strings
agent_log_phase_complete() {
    local phase_name="$1"
    local result="${2:-}"
    shift 2 || true

    log ""
    log "Phase '$phase_name' completed: ${result:-done}"

    while [ $# -gt 0 ]; do
        log "  $1"
        shift
    done
}

# Log agent completion with summary
#
# Args:
#   exit_code - Exit code (0 = success)
#   result    - Result value (PASS, FAIL, FIX, etc.)
agent_log_completion() {
    local exit_code="${1:-0}"
    local result="${2:-}"

    local duration=""
    if [ -n "${_AGENT_START_EPOCH:-}" ]; then
        duration=$(($(date +%s) - _AGENT_START_EPOCH))
    fi

    log_agent_complete "${AGENT_TYPE:-unknown}" "$exit_code" "$duration"

    if [ -n "$result" ]; then
        log_kv "Result" "$result"
    fi
}

# =============================================================================
# LIFECYCLE HOOKS (Default Implementations)
# =============================================================================

# Called before PID file creation during agent initialization
# Override in agent to perform early setup
#
# Args:
#   worker_dir  - Worker directory path
#   project_dir - Project root directory
#
# Returns: 0 to continue, non-zero to abort
agent_on_init() {
    local worker_dir="$1"
    local project_dir="$2"
    # Default: no-op
    return 0
}

# Called after init, before agent_run
# Override in agent to perform pre-run setup
#
# Args:
#   worker_dir  - Worker directory path
#   project_dir - Project root directory
#
# Returns: 0 to continue, non-zero to abort
agent_on_ready() {
    local worker_dir="$1"
    # shellcheck disable=SC2034  # project_dir is available for agent overrides
    local project_dir="${2:-}"
    # Default: no-op
    return 0
}

# Called on validation/prerequisite failure
# Override in agent to handle errors
#
# Args:
#   worker_dir - Worker directory path
#   exit_code  - The exit code that will be returned
#   error_type - Type of error: "prereq", "output", "runtime"
agent_on_error() {
    local worker_dir="$1"
    local exit_code="$2"
    # shellcheck disable=SC2034  # error_type is available for subclass implementations
    local error_type="$3"
    # Default: no-op
    return 0
}

# Called on INT/TERM signal before cleanup
# Override in agent to handle graceful shutdown
#
# Args:
#   signal - Signal name: "INT" or "TERM"
agent_on_signal() {
    # shellcheck disable=SC2034  # signal is available for agent overrides
    local signal="$1"
    # Default: no-op
    return 0
}

# =============================================================================
# UTILITY FUNCTIONS
# =============================================================================

# Create standard directory structure for an agent
#
# Args:
#   worker_dir - Worker directory path
agent_create_directories() {
    local worker_dir="$1"
    mkdir -p "$worker_dir/logs"
    mkdir -p "$worker_dir/summaries"
    mkdir -p "$worker_dir/results"
    mkdir -p "$worker_dir/reports"
}

# Log agent start event
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier (optional)
agent_log_start() {
    local worker_dir="$1"
    local task_id="${2:-unknown}"
    local worker_id
    worker_id=$(basename "$worker_dir")

    echo "[$(date -Iseconds)] INFO: AGENT_STARTED agent=$AGENT_TYPE worker_id=$worker_id task_id=$task_id pipeline=${WIGGUM_PIPELINE:-default} start_time=$(date +%s)" >> "$worker_dir/worker.log"
}

# Log agent completion event
#
# Args:
#   worker_dir - Worker directory path
#   exit_code  - Exit code from agent_run
#   start_time - Start timestamp (from date +%s)
agent_log_complete() {
    local worker_dir="$1"
    local exit_code="$2"
    local start_time="$3"

    local end_time duration
    end_time=$(date +%s)
    duration=$((end_time - start_time))

    echo "[$(date -Iseconds)] INFO: AGENT_COMPLETED agent=$AGENT_TYPE duration_sec=$duration exit_code=$exit_code" >> "$worker_dir/worker.log"
}
