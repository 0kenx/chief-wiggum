#!/usr/bin/env bash
# =============================================================================
# scheduler-integration.sh - Task source integration for scheduler
#
# Provides integration between the task source abstraction and the existing
# scheduler. Hooks into scheduler_init and scheduler_tick to use the
# appropriate task source based on WIGGUM_TASK_SOURCE_MODE.
#
# For local mode: delegates to existing kanban-based functions (default)
# For github/hybrid: uses task-source interface for distributed coordination
#
# This module wraps the scheduler functions to add distributed support
# without modifying the core scheduler.sh file.
# =============================================================================
set -euo pipefail

[ -n "${_SCHEDULER_INTEGRATION_LOADED:-}" ] && return 0
_SCHEDULER_INTEGRATION_LOADED=1

# Source dependencies
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/tasks/task-source.sh"

# Source distributed modules unconditionally — they use double-source guards
# and define only functions (no side effects). The functions themselves check
# _SCHED_DIST_MODE and return early in local mode. Sourcing here ensures
# they're available when the bridge calls service handlers like
# scheduler_update_heartbeats without going through scheduler_init_with_task_source.
source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
source "$WIGGUM_HOME/lib/distributed/claim-manager.sh"
source "$WIGGUM_HOME/lib/distributed/heartbeat.sh"
source "$WIGGUM_HOME/lib/distributed/orphan-recovery.sh"

# =============================================================================
# State
# =============================================================================

# Track if distributed mode is active
_SCHED_DIST_MODE="${WIGGUM_TASK_SOURCE_MODE:-local}"

# =============================================================================
# Extended Scheduler Initialization
# =============================================================================

# Initialize scheduler with task source support
#
# Extends scheduler_init to also initialize the task source for distributed modes.
#
# Args:
#   ralph_dir              - Ralph directory path
#   project_dir            - Project directory path
#   aging_factor           - Aging factor (default: 7)
#   sibling_wip_penalty    - Sibling penalty (default: 20000)
#   plan_bonus             - Plan bonus (default: 15000)
#   dep_bonus_per_task     - Dependency bonus (default: 7000)
#   resume_initial_bonus   - Resume bonus (default: 20000)
#   resume_fail_penalty    - Resume penalty (default: 8000)
#   server_id              - Server ID for distributed modes (optional)
#
# Returns: 0 on success, 1 on failure
scheduler_init_with_task_source() {
    local ralph_dir="$1"
    local project_dir="$2"
    local aging_factor="${3:-7}"
    local sibling_wip_penalty="${4:-20000}"
    local plan_bonus="${5:-15000}"
    local dep_bonus_per_task="${6:-7000}"
    local resume_initial_bonus="${7:-20000}"
    local resume_fail_penalty="${8:-8000}"
    local server_id="${9:-}"

    _SCHED_DIST_MODE="${WIGGUM_TASK_SOURCE_MODE:-local}"

    # Initialize task source for distributed modes
    if [ "$_SCHED_DIST_MODE" != "local" ]; then
        log "Initializing task source: mode=$_SCHED_DIST_MODE"
        task_source_init "$ralph_dir" "$project_dir" "$server_id" || {
            log_error "Failed to initialize task source"
            return 1
        }

        # Load server config
        server_config_load "$ralph_dir"

        local _server_id
        _server_id=$(task_source_get_server_id)
        log "Distributed mode enabled: server_id=$_server_id"

        # Initialize heartbeat tracking
        heartbeat_init "$ralph_dir" "$_server_id" || true
    fi

    # Call standard scheduler_init
    scheduler_init "$ralph_dir" "$project_dir" "$aging_factor" \
        "$sibling_wip_penalty" "$plan_bonus" "$dep_bonus_per_task" \
        "$resume_initial_bonus" "$resume_fail_penalty"
}

# =============================================================================
# Distributed Tick Extensions
# =============================================================================

# Extended scheduler tick with distributed support
#
# In distributed mode, uses task source for task metadata instead of
# direct kanban access.
#
# Returns: 0 on success
scheduler_tick_distributed() {
    # For local mode, use standard tick
    if [ "$_SCHED_DIST_MODE" = "local" ]; then
        scheduler_tick
        return $?
    fi

    # Distributed mode: use task source interface
    SCHED_SCHEDULING_EVENT=false

    local prev_ready="$SCHED_READY_TASKS"
    local prev_blocked="$SCHED_BLOCKED_TASKS"

    local server_id
    server_id=$(task_source_get_server_id)

    # Get all tasks from task source
    local all_tasks
    all_tasks=$(task_source_get_all_tasks)

    # Cache metadata in scheduler format (task_id|status|priority|deps)
    _SCHED_TICK_METADATA=$(echo "$all_tasks" | cut -d'|' -f1-4)

    # Get ready tasks
    _SCHED_READY_WITH_PRIORITIES=$(task_source_get_ready_tasks \
        "$_SCHED_READY_SINCE_FILE" \
        "$_SCHED_AGING_FACTOR" \
        "$_SCHED_SIBLING_WIP_PENALTY" \
        "$_SCHED_PLAN_BONUS" \
        "$_SCHED_DEP_BONUS_PER_TASK")
    SCHED_READY_TASKS=$(echo "$_SCHED_READY_WITH_PRIORITIES" | cut -d'|' -f2 | sed '/^$/d')

    # Get blocked tasks (pending with unsatisfied deps)
    SCHED_BLOCKED_TASKS=""
    while IFS='|' read -r task_id status _ _ _; do
        [ -n "$task_id" ] || continue
        [ "$status" = " " ] || continue  # Only pending

        # Check if in ready list
        if ! echo "$SCHED_READY_TASKS" | grep -qxF "$task_id"; then
            # Not ready = blocked
            SCHED_BLOCKED_TASKS="$SCHED_BLOCKED_TASKS $task_id"
        fi
    done <<< "$all_tasks"
    SCHED_BLOCKED_TASKS=$(echo "$SCHED_BLOCKED_TASKS" | xargs)

    # Derive pending tasks (global scheduler state, used by other modules)
    # shellcheck disable=SC2034
    SCHED_PENDING_TASKS=$(echo "$all_tasks" | awk -F'|' '$2 == " " { print $1 }' | xargs)

    # Refresh worker directories
    scheduler_refresh_worker_dirs

    # Build unified queue (global scheduler state, used by other modules)
    # shellcheck disable=SC2034
    SCHED_UNIFIED_QUEUE=$(get_unified_work_queue)

    # Detect scheduling event (global scheduler state, used by other modules)
    if [ "$SCHED_READY_TASKS" != "$prev_ready" ] || [ "$SCHED_BLOCKED_TASKS" != "$prev_blocked" ]; then
        # shellcheck disable=SC2034
        SCHED_SCHEDULING_EVENT=true
    fi
}

# =============================================================================
# Distributed Task Operations
# =============================================================================

# Claim a task for this server (distributed mode only)
#
# Args:
#   task_id - Task identifier
#
# Returns: 0 if claimed, 1 if failed
scheduler_claim_task() {
    local task_id="$1"

    if [ "$_SCHED_DIST_MODE" = "local" ]; then
        # Local mode: always succeeds
        return 0
    fi

    task_source_claim_task "$task_id"
}

# Release a task (distributed mode only)
#
# Args:
#   task_id - Task identifier
#
# Returns: 0 on success
scheduler_release_task() {
    local task_id="$1"

    if [ "$_SCHED_DIST_MODE" = "local" ]; then
        return 0
    fi

    task_source_release_task "$task_id"
}

# Set task status with distributed sync
#
# Args:
#   task_id - Task identifier
#   status  - New status character
#
# Returns: 0 on success
scheduler_set_task_status() {
    local task_id="$1"
    local status="$2"

    if [ "$_SCHED_DIST_MODE" = "local" ]; then
        # Local: update kanban directly
        update_kanban_status "$_SCHED_RALPH_DIR/kanban.md" "$task_id" "$status"
        return $?
    fi

    # Distributed: use task source
    task_source_set_status "$task_id" "$status"
}

# Verify we still own a task
#
# Args:
#   task_id - Task identifier
#
# Returns: 0 if we own it, 1 if not
scheduler_verify_ownership() {
    local task_id="$1"

    if [ "$_SCHED_DIST_MODE" = "local" ]; then
        return 0
    fi

    task_source_verify_ownership "$task_id"
}

# =============================================================================
# Heartbeat Service Integration
# =============================================================================

# Update heartbeats for all owned tasks
#
# Called by orchestrator periodic service.
#
# Returns: 0 on success
scheduler_update_heartbeats() {
    if [ "$_SCHED_DIST_MODE" = "local" ]; then
        return 0
    fi

    local server_id
    server_id=$(task_source_get_server_id)

    heartbeat_update_all "$_SCHED_RALPH_DIR" "$server_id"
}

# =============================================================================
# Orphan Recovery Service Integration
# =============================================================================

# Run orphan recovery scan
#
# Called by orchestrator periodic service.
#
# Returns: 0 on success
scheduler_run_orphan_recovery() {
    if [ "$_SCHED_DIST_MODE" = "local" ]; then
        return 0
    fi

    local server_id
    server_id=$(task_source_get_server_id)

    orphan_run_scan "$_SCHED_RALPH_DIR" "$server_id"
}

# =============================================================================
# Extended Can-Spawn Check
# =============================================================================

# Check if a task can be spawned (with distributed checks)
#
# Extends scheduler_can_spawn_task to add distributed ownership checks.
#
# Args:
#   task_id     - Task identifier
#   max_workers - Maximum workers allowed
#
# Returns: 0 if can spawn, 1 if should skip
scheduler_can_spawn_task_distributed() {
    local task_id="$1"
    local max_workers="$2"

    # Run standard checks first
    if ! scheduler_can_spawn_task "$task_id" "$max_workers"; then
        return 1
    fi

    # For distributed mode, check if task is claimable
    if [ "$_SCHED_DIST_MODE" != "local" ]; then
        if ! task_source_is_claimable "$task_id"; then
            # shellcheck disable=SC2034  # Global scheduler state used by other modules
            SCHED_SKIP_REASON="claimed_by_other"
            return 1
        fi
    fi

    return 0
}

# =============================================================================
# Shutdown
# =============================================================================

# Clean shutdown of distributed components
#
# Releases all claimed tasks and stops heartbeats.
scheduler_shutdown_distributed() {
    if [ "$_SCHED_DIST_MODE" = "local" ]; then
        return 0
    fi

    local server_id
    server_id=$(task_source_get_server_id)

    log "Shutting down distributed scheduler..."

    # Post final heartbeats
    heartbeat_shutdown "$_SCHED_RALPH_DIR" "$server_id" || true

    # Release all claimed tasks
    claim_release_all "$server_id" "$_SCHED_RALPH_DIR" "Server shutdown" || true

    log "Distributed scheduler shutdown complete"
}

# =============================================================================
# Status/Info
# =============================================================================

# Get distributed scheduler status
#
# Returns: JSON object on stdout
scheduler_get_distributed_status() {
    if [ "$_SCHED_DIST_MODE" = "local" ]; then
        echo '{"mode": "local", "distributed": false}'
        return 0
    fi

    local server_id
    server_id=$(task_source_get_server_id)

    local claimed_count=0
    local claimed_tasks
    claimed_tasks=$(claim_list_owned "$server_id")
    [ -n "$claimed_tasks" ] && claimed_count=$(echo "$claimed_tasks" | wc -l)

    local orphan_status
    orphan_status=$(orphan_get_status "$_SCHED_RALPH_DIR")

    jq -n \
        --arg mode "$_SCHED_DIST_MODE" \
        --arg server_id "$server_id" \
        --argjson claimed_count "$claimed_count" \
        --argjson orphan "$orphan_status" \
        '{
            mode: $mode,
            distributed: true,
            server_id: $server_id,
            claimed_tasks: $claimed_count,
            orphan_status: $orphan
        }'
}
