#!/usr/bin/env bash
# =============================================================================
# task-source.sh - Abstract interface for task sources
#
# Pluggable interface supporting both local kanban and distributed GitHub Issues
# modes. Implementations provide concrete adapters for each source type.
#
# Modes:
#   local  - kanban.md only (single-user, current behavior)
#   github - GitHub Issues only (distributed, no local kanban)
#   hybrid - GitHub Issues primary, kanban.md as cache/mirror
#
# Provides:
#   task_source_init()           - Initialize the task source
#   task_source_get_all_tasks()  - Get all tasks with metadata
#   task_source_claim_task()     - Atomically claim a task
#   task_source_release_task()   - Release task ownership
#   task_source_set_status()     - Update task status
#   task_source_get_owner()      - Get task owner (server_id)
#   task_source_get_task()       - Get single task details
#   task_source_get_ready_tasks() - Get tasks ready to execute
# =============================================================================
set -euo pipefail

[ -n "${_TASK_SOURCE_LOADED:-}" ] && return 0
_TASK_SOURCE_LOADED=1

# Source dependencies
source "$WIGGUM_HOME/lib/core/logger.sh"

# =============================================================================
# Configuration
# =============================================================================

# Task source mode: local, github, hybrid
WIGGUM_TASK_SOURCE_MODE="${WIGGUM_TASK_SOURCE_MODE:-local}"

# Current server ID (set during init for distributed modes)
_TASK_SOURCE_SERVER_ID=""

# Ralph directory (set during init)
_TASK_SOURCE_RALPH_DIR=""

# Project directory (set during init)
_TASK_SOURCE_PROJECT_DIR=""

# Loaded adapter module
_TASK_SOURCE_ADAPTER=""

# =============================================================================
# Interface Functions
# =============================================================================

# Initialize the task source
#
# Loads the appropriate adapter based on WIGGUM_TASK_SOURCE_MODE and initializes
# it with the provided configuration.
#
# Args:
#   ralph_dir   - Path to .ralph directory
#   project_dir - Path to project directory
#   server_id   - Server identifier (optional, generated if not provided)
#
# Returns: 0 on success, 1 on failure
task_source_init() {
    local ralph_dir="$1"
    local project_dir="$2"
    local server_id="${3:-}"

    _TASK_SOURCE_RALPH_DIR="$ralph_dir"
    _TASK_SOURCE_PROJECT_DIR="$project_dir"

    # Load mode-specific adapter
    case "$WIGGUM_TASK_SOURCE_MODE" in
        local)
            source "$WIGGUM_HOME/lib/tasks/task-source-kanban.sh"
            _TASK_SOURCE_ADAPTER="kanban"
            ;;
        github)
            source "$WIGGUM_HOME/lib/tasks/task-source-github.sh"
            _TASK_SOURCE_ADAPTER="github"
            ;;
        hybrid)
            source "$WIGGUM_HOME/lib/tasks/task-source-kanban.sh"
            source "$WIGGUM_HOME/lib/tasks/task-source-github.sh"
            _TASK_SOURCE_ADAPTER="hybrid"
            ;;
        *)
            log_error "Unknown task source mode: $WIGGUM_TASK_SOURCE_MODE"
            return 1
            ;;
    esac

    # For distributed modes, require server identity
    if [[ "$WIGGUM_TASK_SOURCE_MODE" != "local" ]]; then
        source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
        if [ -z "$server_id" ]; then
            server_id=$(server_identity_get_or_create "$ralph_dir")
        fi
        _TASK_SOURCE_SERVER_ID="$server_id"
        log_debug "Task source initialized: mode=$WIGGUM_TASK_SOURCE_MODE server_id=$server_id"
    else
        _TASK_SOURCE_SERVER_ID="local"
        log_debug "Task source initialized: mode=local"
    fi

    # Initialize the adapter
    _task_source_adapter_init "$ralph_dir" "$project_dir" "$server_id"
}

# Get all tasks with metadata
#
# Returns task data in a standardized format regardless of source.
#
# Returns: Lines of "task_id|status|priority|dependencies|owner" on stdout
task_source_get_all_tasks() {
    case "$_TASK_SOURCE_ADAPTER" in
        kanban)
            _task_source_kanban_get_all_tasks "$_TASK_SOURCE_RALPH_DIR"
            ;;
        github)
            _task_source_github_get_all_tasks "$_TASK_SOURCE_RALPH_DIR"
            ;;
        hybrid)
            # Hybrid: GitHub is authoritative, but merge with local cache
            _task_source_hybrid_get_all_tasks "$_TASK_SOURCE_RALPH_DIR"
            ;;
        *)
            log_error "Task source not initialized"
            return 1
            ;;
    esac
}

# Claim a task for this server
#
# Atomically claims a task. In distributed mode, uses GitHub labels/assignee
# for coordination. In local mode, uses file-based locking.
#
# Args:
#   task_id - Task identifier
#
# Returns: 0 if claim succeeded, 1 if task already claimed or error
task_source_claim_task() {
    local task_id="$1"

    case "$_TASK_SOURCE_ADAPTER" in
        kanban)
            _task_source_kanban_claim_task "$_TASK_SOURCE_RALPH_DIR" "$task_id"
            ;;
        github|hybrid)
            _task_source_github_claim_task "$task_id" "$_TASK_SOURCE_SERVER_ID"
            ;;
        *)
            log_error "Task source not initialized"
            return 1
            ;;
    esac
}

# Release task ownership
#
# Releases a previously claimed task, allowing other servers to claim it.
#
# Args:
#   task_id - Task identifier
#
# Returns: 0 on success
task_source_release_task() {
    local task_id="$1"

    case "$_TASK_SOURCE_ADAPTER" in
        kanban)
            _task_source_kanban_release_task "$_TASK_SOURCE_RALPH_DIR" "$task_id"
            ;;
        github|hybrid)
            _task_source_github_release_task "$task_id" "$_TASK_SOURCE_SERVER_ID"
            ;;
        *)
            log_error "Task source not initialized"
            return 1
            ;;
    esac
}

# Update task status
#
# Updates the status of a task in the source. Status chars follow kanban convention:
#   " " = pending, "=" = in-progress, "P" = pending approval,
#   "x" = complete, "*" = failed, "N" = not planned
#
# Args:
#   task_id - Task identifier
#   status  - New status character
#
# Returns: 0 on success
task_source_set_status() {
    local task_id="$1"
    local status="$2"

    case "$_TASK_SOURCE_ADAPTER" in
        kanban)
            _task_source_kanban_set_status "$_TASK_SOURCE_RALPH_DIR" "$task_id" "$status"
            ;;
        github)
            _task_source_github_set_status "$task_id" "$status"
            ;;
        hybrid)
            # Update both sources
            _task_source_github_set_status "$task_id" "$status"
            _task_source_kanban_set_status "$_TASK_SOURCE_RALPH_DIR" "$task_id" "$status" || true
            ;;
        *)
            log_error "Task source not initialized"
            return 1
            ;;
    esac
}

# Get task owner (server_id)
#
# Returns the server_id that currently owns the task, or empty if unclaimed.
#
# Args:
#   task_id - Task identifier
#
# Returns: server_id on stdout, or empty string if unclaimed
task_source_get_owner() {
    local task_id="$1"

    case "$_TASK_SOURCE_ADAPTER" in
        kanban)
            # Local mode: no distributed ownership
            echo ""
            ;;
        github|hybrid)
            _task_source_github_get_owner "$task_id"
            ;;
        *)
            log_error "Task source not initialized"
            return 1
            ;;
    esac
}

# Get single task details
#
# Returns detailed information about a specific task.
#
# Args:
#   task_id - Task identifier
#
# Returns: JSON object with task details on stdout
task_source_get_task() {
    local task_id="$1"

    case "$_TASK_SOURCE_ADAPTER" in
        kanban)
            _task_source_kanban_get_task "$_TASK_SOURCE_RALPH_DIR" "$task_id"
            ;;
        github)
            _task_source_github_get_task "$task_id"
            ;;
        hybrid)
            # Prefer GitHub, fall back to kanban cache
            _task_source_github_get_task "$task_id" || \
                _task_source_kanban_get_task "$_TASK_SOURCE_RALPH_DIR" "$task_id"
            ;;
        *)
            log_error "Task source not initialized"
            return 1
            ;;
    esac
}

# Get tasks ready to execute
#
# Returns tasks that are pending with satisfied dependencies and not claimed
# by another server (in distributed mode).
#
# Args:
#   ready_since_file - Path to ready-since tracking file (for aging)
#   aging_factor     - Aging factor for priority calculation
#   sibling_penalty  - Penalty for sibling tasks in progress
#   plan_bonus       - Bonus for tasks with implementation plans
#   dep_bonus        - Bonus per dependent task
#
# Returns: Lines of "effective_pri|task_id" on stdout, sorted by priority
task_source_get_ready_tasks() {
    local ready_since_file="${1:-}"
    local aging_factor="${2:-7}"
    local sibling_penalty="${3:-20000}"
    local plan_bonus="${4:-15000}"
    local dep_bonus="${5:-7000}"

    case "$_TASK_SOURCE_ADAPTER" in
        kanban)
            _task_source_kanban_get_ready_tasks "$_TASK_SOURCE_RALPH_DIR" \
                "$ready_since_file" "$aging_factor" "$sibling_penalty" \
                "$plan_bonus" "$dep_bonus"
            ;;
        github)
            _task_source_github_get_ready_tasks "$_TASK_SOURCE_SERVER_ID" \
                "$ready_since_file" "$aging_factor" "$sibling_penalty" \
                "$plan_bonus" "$dep_bonus"
            ;;
        hybrid)
            # Use GitHub for authoritative ready list, but apply local priority logic
            _task_source_hybrid_get_ready_tasks "$_TASK_SOURCE_RALPH_DIR" \
                "$_TASK_SOURCE_SERVER_ID" "$ready_since_file" "$aging_factor" \
                "$sibling_penalty" "$plan_bonus" "$dep_bonus"
            ;;
        *)
            log_error "Task source not initialized"
            return 1
            ;;
    esac
}

# Check if task is claimable (unclaimed and ready)
#
# Args:
#   task_id - Task identifier
#
# Returns: 0 if claimable, 1 if not
task_source_is_claimable() {
    local task_id="$1"

    case "$_TASK_SOURCE_ADAPTER" in
        kanban)
            # Local mode: check if pending
            local status
            status=$(_task_source_kanban_get_status "$_TASK_SOURCE_RALPH_DIR" "$task_id")
            [ "$status" = " " ]
            ;;
        github|hybrid)
            _task_source_github_is_claimable "$task_id"
            ;;
        *)
            return 1
            ;;
    esac
}

# Get the current task source mode
#
# Returns: mode string (local, github, hybrid)
task_source_get_mode() {
    echo "$WIGGUM_TASK_SOURCE_MODE"
}

# Get the current server ID (for distributed modes)
#
# Returns: server_id string, or empty for local mode
task_source_get_server_id() {
    echo "$_TASK_SOURCE_SERVER_ID"
}

# Verify this server still owns a task
#
# Args:
#   task_id - Task identifier
#
# Returns: 0 if we own it, 1 if not
task_source_verify_ownership() {
    local task_id="$1"

    case "$_TASK_SOURCE_ADAPTER" in
        kanban)
            # Local mode: always "own" tasks we're working on
            return 0
            ;;
        github|hybrid)
            local owner
            owner=$(task_source_get_owner "$task_id")
            [ "$owner" = "$_TASK_SOURCE_SERVER_ID" ]
            ;;
        *)
            return 1
            ;;
    esac
}

# Invalidate any internal caches
#
# Call this after externally modifying issue state (e.g. reopening a closed
# issue) so that subsequent lookups see the updated state.
#
# Returns: 0 always
task_source_invalidate_cache() {
    case "${_TASK_SOURCE_ADAPTER:-}" in
        github|hybrid)
            _github_invalidate_cache 2>/dev/null || true
            ;;
    esac
    return 0
}
