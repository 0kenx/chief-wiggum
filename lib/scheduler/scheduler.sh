#!/usr/bin/env bash
# scheduler.sh - Main scheduling interface
#
# Provides the high-level scheduling interface that ties together:
#   - worker-pool.sh: Unified worker tracking
#   - priority-workers.sh: Fix/resolve worker management
#   - merge-manager.sh: PR merge workflow
#   - status-display.sh: Status output formatting
#
# This module encapsulates the scheduling logic from wiggum-run's main loop.
#
# shellcheck disable=SC2034  # Global variables are exported for caller use
# shellcheck disable=SC2329  # Functions are invoked indirectly via callbacks
set -euo pipefail

[ -n "${_SCHEDULER_LOADED:-}" ] && return 0
_SCHEDULER_LOADED=1

# Source platform helpers for portable time functions
source "$WIGGUM_HOME/lib/core/platform.sh"

# Source all scheduler components
source "$WIGGUM_HOME/lib/scheduler/worker-pool.sh"
source "$WIGGUM_HOME/lib/scheduler/priority-workers.sh"
source "$WIGGUM_HOME/lib/scheduler/fix-workers.sh"
source "$WIGGUM_HOME/lib/scheduler/resolve-workers.sh"
source "$WIGGUM_HOME/lib/scheduler/merge-manager.sh"
source "$WIGGUM_HOME/lib/scheduler/status-display.sh"
source "$WIGGUM_HOME/lib/tasks/task-parser.sh"
source "$WIGGUM_HOME/lib/tasks/conflict-detection.sh"
source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/resume-state.sh"

# Scheduler configuration (set by scheduler_init)
declare -g _SCHED_RALPH_DIR=""
declare -g _SCHED_PROJECT_DIR=""
declare -g _SCHED_READY_SINCE_FILE=""
declare -g _SCHED_AGING_FACTOR=7
declare -g _SCHED_SIBLING_WIP_PENALTY=20000
declare -g _SCHED_PLAN_BONUS=15000
declare -g _SCHED_DEP_BONUS_PER_TASK=7000
declare -g _SCHED_RESUME_INITIAL_BONUS=20000
declare -g _SCHED_RESUME_FAIL_PENALTY=8000

# Scheduler state (updated by scheduler_tick)
declare -g SCHED_READY_TASKS=""
declare -g SCHED_BLOCKED_TASKS=""
declare -g SCHED_PENDING_TASKS=""
declare -g SCHED_UNIFIED_QUEUE=""
declare -g SCHED_SCHEDULING_EVENT=false

# Cyclic tasks tracking (task_id -> error type)
declare -gA _SCHED_CYCLIC_TASKS=()

# Skip tasks tracking (task_id -> consecutive failure count)
declare -gA _SCHED_SKIP_TASKS=()

# Per-tick cached kanban metadata (set by scheduler_tick, used by get_unified_work_queue et al.)
declare -g _SCHED_TICK_METADATA=""
# Per-tick ready tasks with priorities: "effective_pri|task_id" lines
declare -g _SCHED_READY_WITH_PRIORITIES=""
# Git pull time guard: epoch of last successful git pull
declare -g _SCHED_LAST_GIT_PULL=0
# Cached worker directory listing (per-tick)
declare -g _SCHED_WORKER_DIRS=""
declare -g _SCHED_WORKER_DIRS_TICK=0

# Initialize the scheduler
#
# Args:
#   ralph_dir              - Ralph directory path
#   project_dir            - Project directory path
#   aging_factor           - Aging factor for priority calculation (default: 7)
#   sibling_wip_penalty    - Penalty when sibling is WIP (default: 20000)
#   plan_bonus             - Bonus for tasks with plans (default: 15000)
#   dep_bonus_per_task     - Bonus per blocking task (default: 7000)
#   resume_initial_bonus   - Initial priority bonus for resume tasks (default: 20000)
#   resume_fail_penalty    - Priority penalty per failed resume attempt (default: 8000)
scheduler_init() {
    _SCHED_RALPH_DIR="$1"
    _SCHED_PROJECT_DIR="$2"
    _SCHED_AGING_FACTOR="${3:-7}"
    _SCHED_SIBLING_WIP_PENALTY="${4:-20000}"
    _SCHED_PLAN_BONUS="${5:-15000}"
    _SCHED_DEP_BONUS_PER_TASK="${6:-7000}"
    _SCHED_RESUME_INITIAL_BONUS="${7:-20000}"
    _SCHED_RESUME_FAIL_PENALTY="${8:-8000}"

    _SCHED_READY_SINCE_FILE="$_SCHED_RALPH_DIR/orchestrator/task-ready-since"

    # Initialize ready-since file if it doesn't exist
    touch "$_SCHED_READY_SINCE_FILE"

    # Initialize worker pool
    pool_init

    # Reset state
    SCHED_READY_TASKS=""
    SCHED_BLOCKED_TASKS=""
    SCHED_PENDING_TASKS=""
    SCHED_UNIFIED_QUEUE=""
    SCHED_SCHEDULING_EVENT=false
    _SCHED_CYCLIC_TASKS=()
    _SCHED_SKIP_TASKS=()
    _SCHED_TICK_METADATA=""
    _SCHED_READY_WITH_PRIORITIES=""
    _SCHED_LAST_GIT_PULL=0
    _SCHED_WORKER_DIRS=""
    _SCHED_WORKER_DIRS_TICK=0
}

# Detect and register cyclic dependencies
#
# Populates _SCHED_CYCLIC_TASKS with tasks that should be skipped
# due to self-dependency or circular dependencies.
#
# Returns: 0 if no cycles, 1 if cycles detected
scheduler_detect_cycles() {
    local dep_errors

    _SCHED_CYCLIC_TASKS=()

    if dep_errors=$(detect_circular_dependencies "$_SCHED_RALPH_DIR/kanban.md"); then
        log "No dependency cycles detected"
        return 0
    fi

    # Parse errors and populate cyclic_tasks for skipping
    while IFS= read -r line; do
        if [[ "$line" =~ ^SELF:(.+)$ ]]; then
            local task_id="${BASH_REMATCH[1]}"
            _SCHED_CYCLIC_TASKS[$task_id]="SELF"
            log_error "Self-dependency detected: $task_id depends on itself - will be skipped"
        elif [[ "$line" =~ ^CYCLE:(.+)$ ]]; then
            local cycle_members="${BASH_REMATCH[1]}"
            for task_id in $cycle_members; do
                _SCHED_CYCLIC_TASKS[$task_id]="CYCLE"
            done
            log_error "Circular dependency detected involving:$cycle_members - will be skipped"
        fi
    done <<< "$dep_errors"

    if [ ${#_SCHED_CYCLIC_TASKS[@]} -gt 0 ]; then
        log_warn "Skipping ${#_SCHED_CYCLIC_TASKS[@]} task(s) due to dependency errors"
        return 1
    fi

    return 0
}

# Restore scheduler state from existing worker directories
#
# Call this after scheduler_init to recover tracking state when
# the orchestrator restarts.
scheduler_restore_workers() {
    if [ -d "$_SCHED_RALPH_DIR/workers" ]; then
        log "Scanning for active workers from previous runs..."
        pool_restore_from_workers "$_SCHED_RALPH_DIR"

        local restored_count
        restored_count=$(pool_count)
        if [ "$restored_count" -gt 0 ]; then
            log "Restored tracking for $restored_count worker(s)"
        fi

        # Re-claim issues for restored workers in distributed mode
        if [[ "${WIGGUM_TASK_SOURCE_MODE:-local}" != "local" ]] && [ "$restored_count" -gt 0 ]; then
            _scheduler_reclaim_restored_workers
        fi

        # Migrate legacy .needs-fix markers to git-state.json
        for worker_dir in "$_SCHED_RALPH_DIR/workers"/worker-*; do
            [ -d "$worker_dir" ] || continue
            if [ -f "$worker_dir/.needs-fix" ] && [ ! -f "$worker_dir/git-state.json" ]; then
                local migrated_task_id
                migrated_task_id=$(get_task_id_from_worker "$(basename "$worker_dir")")
                git_state_set "$worker_dir" "needs_fix" "scheduler.migration" "Migrated from .needs-fix marker"
                rm -f "$worker_dir/.needs-fix"
                log "Migrated legacy .needs-fix for $migrated_task_id to git-state.json"
            fi
        done
    fi
}

# Re-claim GitHub issues for restored workers
#
# After worker pool restoration, ensures this server owns the associated
# GitHub issues. Skips issues where another server has a fresh heartbeat
# (< 10 min). Removes other servers' labels and assignees.
_scheduler_reclaim_restored_workers() {
    # Populate issue cache so we can resolve task_id -> issue_number
    if declare -F _github_refresh_cache &>/dev/null; then
        _github_refresh_cache 2>/dev/null || true
    fi

    local server_id=""
    if declare -F task_source_get_server_id &>/dev/null; then
        server_id=$(task_source_get_server_id)
    fi
    [ -n "$server_id" ] || return 0

    local reclaimed=0
    _reclaim_worker_cb() {
        local _pid="$1" _type="$2" _task_id="$3"

        # Resolve issue number from task ID
        local issue_number=""
        if declare -F _github_find_issue_by_task_id &>/dev/null; then
            issue_number=$(_github_find_issue_by_task_id "$_task_id" 2>/dev/null) || true
        fi

        if [ -z "$issue_number" ]; then
            log_debug "reclaim: no issue found for $_task_id — skipping"
            return 0
        fi

        if claim_reclaim_on_restore "$issue_number" "$server_id" "$_SCHED_RALPH_DIR"; then
            ((++reclaimed)) || true
        fi
    }
    pool_foreach "all" _reclaim_worker_cb

    if [ "$reclaimed" -gt 0 ]; then
        log "Re-claimed $reclaimed issue(s) for server $server_id"
    fi
}

# Reclaim in-progress tasks that have no worker directory
#
# Detects tasks marked [=] in the kanban that have no corresponding worker
# directory (e.g., orchestrator crashed between kanban update and spawn).
# Resets them to [ ] (pending) so get_ready_tasks() can pick them up.
#
# Uses _SCHED_TICK_METADATA (must be set before calling).
# Invalidates metadata cache and refreshes _SCHED_TICK_METADATA if any
# tasks are reclaimed.
_scheduler_reclaim_workerless_tasks() {
    local in_progress_tasks
    in_progress_tasks=$(echo "$_SCHED_TICK_METADATA" | awk -F'|' '$2 == "=" { print $1 }')

    [ -n "$in_progress_tasks" ] || return 0

    local reclaimed=0

    for task_id in $in_progress_tasks; do
        [ -n "$task_id" ] || continue

        # Skip if the worker pool already tracks this task (process may be starting)
        pool_has_task "$task_id" > /dev/null 2>&1 && continue

        # Check if any worker directory exists for this task
        local worker_dir
        worker_dir=$(find_any_worker_by_task_id "$_SCHED_RALPH_DIR" "$task_id") || true

        if [ -z "$worker_dir" ] || [ ! -d "$worker_dir" ]; then
            log_warn "Reclaiming in-progress task $task_id — no worker directory found"
            update_kanban_status "$_SCHED_RALPH_DIR/kanban.md" "$task_id" " " || true
            ((++reclaimed)) || true
        fi
    done

    if [ "$reclaimed" -gt 0 ]; then
        log "Reclaimed $reclaimed workerless in-progress task(s)"
        # Invalidate metadata cache so get_ready_tasks sees updated statuses
        _KANBAN_CACHE_MTIME=""
        _SCHED_TICK_METADATA=$(_get_cached_metadata "$_SCHED_RALPH_DIR/kanban.md")
        SCHED_SCHEDULING_EVENT=true
    fi
}

# One tick of the scheduling loop
#
# Updates SCHED_READY_TASKS, SCHED_BLOCKED_TASKS, SCHED_PENDING_TASKS
# and SCHED_SCHEDULING_EVENT.
scheduler_tick() {
    SCHED_SCHEDULING_EVENT=false

    local prev_ready="$SCHED_READY_TASKS"
    local prev_blocked="$SCHED_BLOCKED_TASKS"

    # Parse kanban metadata once in the parent process (avoids subshell cache loss)
    _SCHED_TICK_METADATA=$(_get_cached_metadata "$_SCHED_RALPH_DIR/kanban.md")

    # Reclaim in-progress tasks that have no worker directory.
    # These are stuck: get_ready_tasks only picks up status=" " and nothing else
    # will re-schedule an [=] task without a worker.
    _scheduler_reclaim_workerless_tasks

    # Get tasks ready to run, passing pre-fetched metadata to avoid redundant parse.
    # Returns "effective_pri|task_id" lines when metadata is passed.
    _SCHED_READY_WITH_PRIORITIES=$(get_ready_tasks \
        "$_SCHED_RALPH_DIR/kanban.md" \
        "$_SCHED_READY_SINCE_FILE" \
        "$_SCHED_AGING_FACTOR" \
        "$_SCHED_SIBLING_WIP_PENALTY" \
        "$_SCHED_RALPH_DIR" \
        "$_SCHED_PLAN_BONUS" \
        "$_SCHED_DEP_BONUS_PER_TASK" \
        "$_SCHED_TICK_METADATA")
    SCHED_READY_TASKS=$(echo "$_SCHED_READY_WITH_PRIORITIES" | cut -d'|' -f2 | sed '/^$/d')

    SCHED_BLOCKED_TASKS=$(get_blocked_tasks "$_SCHED_RALPH_DIR/kanban.md" "$_SCHED_TICK_METADATA")

    # Derive pending tasks from cached metadata (avoids separate kanban parse)
    SCHED_PENDING_TASKS=$(echo "$_SCHED_TICK_METADATA" | awk -F'|' '$2 == " " { print $1 }')

    # Refresh cached worker directory listing for this tick
    scheduler_refresh_worker_dirs

    # Build unified queue merging new tasks and resume candidates.
    # Guard: if get_unified_work_queue fails (e.g. corrupt worker JSON), log
    # and continue with empty queue so the tick still completes and
    # SCHED_SCHEDULING_EVENT can be set.
    SCHED_UNIFIED_QUEUE=$(get_unified_work_queue) || {
        log_warn "scheduler_tick: get_unified_work_queue failed — queue empty this tick"
        SCHED_UNIFIED_QUEUE=""
    }

    # Mark scheduling event when task lists change (ensures first-tick display)
    if [ "$SCHED_READY_TASKS" != "$prev_ready" ] || [ "$SCHED_BLOCKED_TASKS" != "$prev_blocked" ]; then
        SCHED_SCHEDULING_EVENT=true
    fi
}

# Check if a task can be spawned
#
# Applies all filters: cyclic deps, skip count, file conflicts, capacity
#
# Args:
#   task_id     - Task identifier
#   max_workers - Maximum workers allowed
#
# Returns: 0 if can spawn, 1 if should skip (sets SCHED_SKIP_REASON)
scheduler_can_spawn_task() {
    local task_id="$1"
    local max_workers="$2"

    SCHED_SKIP_REASON=""

    # Check capacity
    local main_count
    main_count=$(pool_count "main")
    if [ "$main_count" -ge "$max_workers" ]; then
        SCHED_SKIP_REASON="at_capacity"
        return 1
    fi

    # Skip tasks with dependency cycles
    if [ -n "${_SCHED_CYCLIC_TASKS[$task_id]+x}" ]; then
        SCHED_SKIP_REASON="cyclic_dependency"
        return 1
    fi

    # Skip tasks with active cooldown (count acts as cycles-to-skip)
    if [ -n "${_SCHED_SKIP_TASKS[$task_id]+x}" ] && [ "${_SCHED_SKIP_TASKS[$task_id]}" -gt 0 ]; then
        # Decrement cooldown each check
        _SCHED_SKIP_TASKS[$task_id]=$(( ${_SCHED_SKIP_TASKS[$task_id]} - 1 ))
        if [ "${_SCHED_SKIP_TASKS[$task_id]}" -le 0 ]; then
            unset "_SCHED_SKIP_TASKS[$task_id]"
        fi
        SCHED_SKIP_REASON="skip_count"
        return 1
    fi

    # Build temporary workers map for conflict detection
    local -A _temp_workers=()
    _build_workers_map() {
        local pid="$1" type="$2" tid="$3"
        if [ "$type" = "main" ]; then
            _temp_workers[$pid]="$tid"
        fi
    }
    pool_foreach "main" _build_workers_map

    # Skip if file conflict with active worker
    if has_file_conflict "$_SCHED_RALPH_DIR" "$task_id" _temp_workers; then
        SCHED_SKIP_REASON="file_conflict"
        return 1
    fi

    return 0
}

# Increment skip count for a task
#
# Args:
#   task_id - Task identifier
scheduler_increment_skip() {
    local task_id="$1"
    local current=${_SCHED_SKIP_TASKS[$task_id]:-0}
    # Exponential backoff: 1, 2, 4, 8, 16, capped at 30 cycles
    local next=$(( current < 1 ? 1 : current * 2 ))
    (( next > 30 )) && next=30
    _SCHED_SKIP_TASKS[$task_id]=$next
}

# Get skip count for a task
#
# Args:
#   task_id - Task identifier
#
# Returns: echoes skip count
scheduler_get_skip_count() {
    local task_id="$1"
    echo "${_SCHED_SKIP_TASKS[$task_id]:-0}"
}

# Mark that a scheduling event occurred
scheduler_mark_event() {
    SCHED_SCHEDULING_EVENT=true
}

# Update aging tracking after scheduling events
#
# Should be called when scheduling events occurred (task spawned or worker finished)
scheduler_update_aging() {
    if [ "$SCHED_SCHEDULING_EVENT" != true ]; then
        return 0
    fi

    local new_ready_since
    local _sched_tmp_dir="${RALPH_DIR:-/tmp}"
    mkdir -p "$_sched_tmp_dir/tmp" 2>/dev/null || _sched_tmp_dir="/tmp"
    new_ready_since=$(mktemp "$_sched_tmp_dir/tmp/wiggum-sched-XXXXXX")

    # Use cached ready tasks from scheduler_tick (same in-process tick cycle;
    # scheduler_tick runs at order 30 before aging_update at order 70)
    for task_id in $SCHED_READY_TASKS; do
        local prev_count
        prev_count=$(awk -F'|' -v t="$task_id" '$1 == t { print $2 }' "$_SCHED_READY_SINCE_FILE" 2>/dev/null)
        prev_count=${prev_count:-0}
        echo "$task_id|$(( prev_count + 1 ))" >> "$new_ready_since"
    done

    mv "$new_ready_since" "$_SCHED_READY_SINCE_FILE"
}

# Remove a task from ready-since tracking (e.g., when spawned)
#
# Args:
#   task_id - Task identifier
scheduler_remove_from_aging() {
    local task_id="$1"

    if [ -f "$_SCHED_READY_SINCE_FILE" ]; then
        # Use platform-appropriate sed in-place
        if [[ "$OSTYPE" == darwin* ]]; then
            sed -i "" "/^${task_id}|/d" "$_SCHED_READY_SINCE_FILE"
        else
            sed -i "/^${task_id}|/d" "$_SCHED_READY_SINCE_FILE"
        fi
    fi
}

# Check if all tasks are complete
#
# Returns: 0 if complete (no pending tasks, no workers, no pending fixes), 1 otherwise
scheduler_is_complete() {
    local run_mode="${WIGGUM_RUN_MODE:-default}"

    # Check for pending tasks ([ ] status)
    # In fix-only/merge-only modes, don't wait for pending tasks - we're not processing them
    if [[ "$run_mode" == "default" ]]; then
        if [ -n "$SCHED_PENDING_TASKS" ]; then
            # Filter out tasks that are permanently blocked (all unsatisfied deps at [*] or [N])
            local _kanban_file="$_SCHED_RALPH_DIR/kanban.md"
            local _actionable_pending=0
            local _task_id
            for _task_id in $SCHED_PENDING_TASKS; do
                local _unsatisfied
                _unsatisfied=$(get_unsatisfied_dependencies "$_kanban_file" "$_task_id")
                if [ -z "$_unsatisfied" ]; then
                    ((_actionable_pending++)) || true  # No deps or all satisfied
                else
                    # Check if any unsatisfied dep is still alive (not [*] or [N])
                    local _has_alive_dep=false
                    local _dep
                    for _dep in $_unsatisfied; do
                        local _dep_status
                        _dep_status=$(get_task_status "$_kanban_file" "$_dep")
                        if [[ "$_dep_status" != "*" && "$_dep_status" != "N" ]]; then
                            _has_alive_dep=true
                            break
                        fi
                    done
                    $_has_alive_dep && ((_actionable_pending++)) || true
                fi
            done
            if [ "$_actionable_pending" -gt 0 ]; then
                return 1
            fi
        fi
    fi

    # Check for running workers
    local worker_count
    worker_count=$(pool_count)
    if [ "$worker_count" -gt 0 ]; then
        return 1
    fi

    # Check for tasks needing fixes (populated by PR optimization)
    # In merge-only mode, skip this check - we're not fixing tasks
    if [[ "$run_mode" != "merge-only" && "$run_mode" != "resume-only" ]]; then
        local tasks_needing_fix="$_SCHED_RALPH_DIR/orchestrator/tasks-needing-fix.txt"
        if [ -s "$tasks_needing_fix" ]; then
            return 1
        fi
    fi

    # Check for workers in needs_fix or needs_resolve state
    for worker_dir in "$_SCHED_RALPH_DIR/workers"/worker-*; do
        [ -d "$worker_dir" ] || continue
        # Skip plan workers
        [[ "$(basename "$worker_dir")" == *"-plan-"* ]] && continue

        if [ -f "$worker_dir/git-state.json" ]; then
            local git_state
            git_state=$(jq -r '.current_state // ""' "$worker_dir/git-state.json" 2>/dev/null)
            case "$git_state" in
                needs_fix|fixing)
                    # In merge-only/resume-only mode, don't wait for fix tasks
                    [[ "$run_mode" == "merge-only" || "$run_mode" == "resume-only" ]] && continue
                    return 1
                    ;;
                needs_resolve|needs_multi_resolve|resolving)
                    [[ "$run_mode" == "resume-only" ]] && continue
                    return 1
                    ;;
            esac
        fi
    done

    # In resume-only mode, stay alive while there are pending decides, retry decisions, or resumable workers
    if [[ "$run_mode" == "resume-only" ]]; then
        # Check pending decide processes
        if declare -p _PENDING_DECIDES &>/dev/null && [[ ${#_PENDING_DECIDES[@]} -gt 0 ]]; then
            return 1
        fi
        # Check workers with RETRY decisions waiting to be spawned
        local retry_workers
        retry_workers=$(get_workers_with_retry_decision "$_SCHED_RALPH_DIR")
        [[ -n "$retry_workers" ]] && return 1
        # Check workers that still need a decide phase
        local needing_decide
        needing_decide=$(get_workers_needing_decide "$_SCHED_RALPH_DIR")
        [[ -n "$needing_decide" ]] && return 1
    fi

    return 0
}

# Detect orphan workers (running PIDs not tracked in pool)
# Re-tracks them. This is normal when sub-agents are spawned with different PIDs.
scheduler_detect_orphan_workers() {
    [ -d "$_SCHED_RALPH_DIR/workers" ] || return 0

    local scan_output
    scan_output=$(scan_active_workers "$_SCHED_RALPH_DIR") || {
        local scan_rc=$?
        if [ "$scan_rc" -eq 2 ]; then
            log_warn "Worker scan encountered lock contention, results may be incomplete"
        fi
    }

    while read -r worker_pid task_id worker_id _pid_type; do
        [ -n "$worker_pid" ] || continue

        # Check if this PID is already tracked
        if ! pool_get "$worker_pid" > /dev/null 2>&1; then
            # Determine worker type from pipeline config, name pattern, and git-state
            local worker_dir="$_SCHED_RALPH_DIR/workers/$worker_id"
            local type
            type=$(_detect_worker_type "$worker_dir")

            # Check if a different PID for this task is already tracked
            # If so, this is a sub-agent spawn (normal); otherwise it's unexpected
            local existing_tracked=""
            existing_tracked=$(pool_find_by_task "$task_id" 2>/dev/null || true)

            if [ -n "$existing_tracked" ]; then
                # Sub-agent spawned with new PID - replace old tracking
                log "Detected sub-agent for $task_id (PID: $worker_pid) - updating tracking"
                pool_remove "$existing_tracked" 2>/dev/null || true
            else
                log_warn "Detected orphan worker for $task_id (PID: $worker_pid) - re-tracking"
            fi

            pool_add "$worker_pid" "$type" "$task_id"
        fi
    done <<< "$scan_output"
}

# Get reference to cyclic tasks array (for status display)
#
# Returns: name of the array variable
scheduler_get_cyclic_tasks_ref() {
    echo "_SCHED_CYCLIC_TASKS"
}

# Get scheduler configuration values
scheduler_get_ralph_dir() { echo "$_SCHED_RALPH_DIR"; }
scheduler_get_project_dir() { echo "$_SCHED_PROJECT_DIR"; }
scheduler_get_ready_since_file() { echo "$_SCHED_READY_SINCE_FILE"; }
scheduler_get_aging_factor() { echo "$_SCHED_AGING_FACTOR"; }
scheduler_get_plan_bonus() { echo "$_SCHED_PLAN_BONUS"; }
scheduler_get_dep_bonus_per_task() { echo "$_SCHED_DEP_BONUS_PER_TASK"; }
scheduler_get_resume_initial_bonus() { echo "$_SCHED_RESUME_INITIAL_BONUS"; }
scheduler_get_resume_fail_penalty() { echo "$_SCHED_RESUME_FAIL_PENALTY"; }

# Refresh cached worker directories for the current tick
#
# Caches the glob result per orchestrator iteration to avoid repeated
# filesystem scans within the same tick cycle. Must be called in the
# parent process (not in a $() subshell) for the cache to persist.
scheduler_refresh_worker_dirs() {
    local current_tick="${_ORCH_ITERATION:-0}"
    if [ "$_SCHED_WORKER_DIRS_TICK" = "$current_tick" ] && [ -n "$_SCHED_WORKER_DIRS" ]; then
        return 0
    fi
    _SCHED_WORKER_DIRS=""
    if [ -d "$_SCHED_RALPH_DIR/workers" ]; then
        local dir
        for dir in "$_SCHED_RALPH_DIR/workers"/worker-*; do
            [ -d "$dir" ] || continue
            _SCHED_WORKER_DIRS+="$dir"$'\n'
        done
        # Remove trailing newline
        _SCHED_WORKER_DIRS="${_SCHED_WORKER_DIRS%$'\n'}"
    fi
    _SCHED_WORKER_DIRS_TICK="$current_tick"
}

# Get cached list of worker directories for this tick
#
# Returns: newline-separated list of worker directory paths
scheduler_get_worker_dirs() {
    scheduler_refresh_worker_dirs
    echo "$_SCHED_WORKER_DIRS"
}

# Check if worker has repeated failures at the same pipeline step
#
# Examines resume-state.json history for consecutive failures at the
# same step (from most recent backward). Returns 0 (terminal) if the
# threshold is met.
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: 0 if repeated failures detected, 1 otherwise
_has_repeated_step_failures() {
    local worker_dir="$1"
    local state_file="$worker_dir/resume-state.json"
    [ -f "$state_file" ] || return 1

    local threshold="${WIGGUM_MAX_STEP_RETRIES:-3}"

    # Count consecutive entries from most recent where step is the same.
    # USER_RETRY entries break the chain (user explicitly requested retry).
    local consecutive_count
    consecutive_count=$(jq -r --argjson threshold "$threshold" '
        (.history // []) |
        reverse |
        reduce .[] as $entry ({count: 0, first: null, done: false};
            if .done then .
            elif $entry.decision == "USER_RETRY" then .done = true
            elif ($entry.step == null or $entry.step == "") then .
            elif .first == null then .first = $entry.step | .count = 1
            elif $entry.step == .first then .count += 1
            else .done = true
            end
        ) | .count
    ' "$state_file" 2>/dev/null)
    consecutive_count="${consecutive_count:-0}"

    [ "$consecutive_count" -ge "$threshold" ]
}

# Check if worker hit terminal failure
#
# Terminal failure means the worker cannot be usefully resumed and should be
# cleaned up and restarted fresh. A worker is terminal when ANY of these hold:
#
# 1. resume-state marks it terminal (COMPLETE or ABORT decision from resume-decide)
#    - Checked via resume_state_is_terminal()
#
# 2. Pipeline reached the LAST step AND that step's result is FAIL
#    - All pipeline steps exhausted, nothing left to retry
#    - Requires: pipeline-config.json with valid current.step_idx at last step
#    - Requires: result file for current step with gate_result = FAIL
#
# NOT terminal (worker is resumable):
# - No pipeline-config.json (worker never started pipeline — can retry from scratch)
# - current_idx not at last step (pipeline has remaining steps)
# - Last step result is PASS/FIX/SKIP/UNKNOWN (non-terminal outcomes)
# - No result file for current step (step was interrupted before producing result)
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: 0 if terminal failure, 1 otherwise
_is_terminal_failure() {
    local worker_dir="$1"

    # USER_RETRY overrides all automatic terminal criteria — the user
    # explicitly requested a retry, so let the worker through to resume-decide
    local latest_decision
    latest_decision=$(jq -r '(.history // []) | last | .decision // ""' \
        "$worker_dir/resume-state.json" 2>/dev/null)
    if [[ "$latest_decision" == "USER_RETRY" ]]; then
        return 1
    fi

    # Criterion 1: resume-state marks terminal (COMPLETE or ABORT decisions)
    resume_state_is_terminal "$worker_dir" && return 0

    # Criterion 1b: workspace missing (no point resuming if setup completed)
    if [ ! -d "$worker_dir/workspace" ] && [ -f "$worker_dir/prd.md" ]; then
        return 0
    fi

    # Criterion 1c: stop-reason marker from infrastructure failure (workspace deleted)
    [ -f "$worker_dir/stop-reason-workspace-deleted" ] && return 0

    # Criterion 1d: repeated failures at same pipeline step across resumes
    _has_repeated_step_failures "$worker_dir" && return 0

    # Criterion 2: pipeline completed to last step with FAIL result
    local config_file="$worker_dir/pipeline-config.json"
    [ -f "$config_file" ] || return 1

    # Get current step and total count
    local current_idx step_count
    current_idx=$(jq -r '.current.step_idx // -1' "$config_file" 2>/dev/null)
    step_count=$(jq -r '.steps | length' "$config_file" 2>/dev/null)

    [ "$current_idx" -ge 0 ] || return 1
    [ "$step_count" -gt 0 ] || return 1

    # Not terminal if not at last step
    [ "$current_idx" -eq $((step_count - 1)) ] || return 1

    # Check result for current step
    local current_step_id result_file gate_result
    current_step_id=$(jq -r '.current.step_id // ""' "$config_file" 2>/dev/null)
    [ -n "$current_step_id" ] || return 1

    result_file=$(find "$worker_dir/results" -name "*-${current_step_id}-result.json" 2>/dev/null | sort -r | head -1)
    [ -f "$result_file" ] || return 1

    gate_result=$(jq -r '.outputs.gate_result // ""' "$result_file" 2>/dev/null)
    [ "$gate_result" = "FAIL" ]
}

# Find workers that can be resumed
#
# Scans for stopped workers that are eligible for automatic resume. A worker
# is resumable if:
#   - It has a workspace directory (git worktree was set up)
#   - It has a prd.md file (requirements were generated)
#   - It's not currently running (no valid agent.pid)
#   - It's not a terminal failure (last step FAIL)
#   - It's not a plan-only worker
#
# Args:
#   ralph_dir - Ralph directory path
#
# Returns: Lines of "worker_dir task_id current_step worker_type" for each resumable worker
get_resumable_workers() {
    local ralph_dir="$1"
    [ -d "$ralph_dir/workers" ] || return 0

    for worker_dir in "$ralph_dir/workers"/worker-*; do
        [ -d "$worker_dir" ] || continue

        # Skip plan workers (read-only planning sessions)
        [[ "$(basename "$worker_dir")" == *"-plan-"* ]] && continue

        # Must have workspace and prd.md (setup was completed)
        [ -d "$worker_dir/workspace" ] || continue
        [ -f "$worker_dir/prd.md" ] || continue

        # Skip if still running
        is_worker_running "$worker_dir" && continue

        # Skip terminal failures (last step + FAIL, or resume-state terminal)
        # Mark terminal + update kanban when repeated step failures detected
        if _is_terminal_failure "$worker_dir"; then
            if ! resume_state_is_terminal "$worker_dir"; then
                local _term_tid2
                _term_tid2=$(get_task_id_from_worker "$(basename "$worker_dir")")
                if _has_repeated_step_failures "$worker_dir"; then
                    resume_state_set_terminal "$worker_dir" "Repeated failures at same pipeline step"
                    update_kanban_failed "$RALPH_DIR/kanban.md" "$_term_tid2" || true
                    github_issue_sync_task_status "$RALPH_DIR" "$_term_tid2" "*" || true
                    log_error "Worker $(basename "$worker_dir") repeated step failures — marked terminal"
                    activity_log "worker.resume_failed" "$(basename "$worker_dir")" "$_term_tid2" "reason=repeated_step_failures"
                    scheduler_mark_event
                fi
            fi
            continue
        fi

        # Skip workers in cooldown (DEFER)
        resume_state_is_cooling "$worker_dir" && continue

        # Skip workers that exceeded max resume attempts
        resume_state_max_exceeded "$worker_dir" && continue

        local task_id current_step worker_type
        task_id=$(get_task_id_from_worker "$(basename "$worker_dir")")

        # Get current step from pipeline config, default to execution
        if [ -f "$worker_dir/pipeline-config.json" ]; then
            current_step=$(jq -r '.current.step_id // "execution"' "$worker_dir/pipeline-config.json" 2>/dev/null)
        else
            current_step="execution"
        fi

        # Detect worker type from pipeline config, name pattern, and git-state
        worker_type=$(_detect_worker_type "$worker_dir")

        echo "$worker_dir $task_id $current_step $worker_type"
    done
}

# Find workers that need a resume-decide analysis
#
# Scans for stopped workers eligible for the decide phase. These workers:
#   - Have a workspace and prd.md (setup completed)
#   - Are not currently running (no valid agent.pid/resume.pid/decide.pid)
#   - Are not terminal failures
#   - Are not in cooldown
#   - Have not exceeded max resume attempts
#   - Are not plan-only workers
#   - Do NOT already have a resume-decision.json (decision pending or consumed)
#   - Do NOT have an active decide.pid process
#
# Args:
#   ralph_dir - Ralph directory path
#
# Returns: Lines of "worker_dir task_id current_step worker_type" for each worker
get_workers_needing_decide() {
    local ralph_dir="$1"
    [ -d "$ralph_dir/workers" ] || return 0

    for worker_dir in "$ralph_dir/workers"/worker-*; do
        [ -d "$worker_dir" ] || continue

        # Skip plan workers (read-only planning sessions)
        [[ "$(basename "$worker_dir")" == *"-plan-"* ]] && continue

        # Must have workspace — if deleted after setup, mark terminal instead of silently skipping
        if [ ! -d "$worker_dir/workspace" ]; then
            if [ -f "$worker_dir/prd.md" ] && ! resume_state_is_terminal "$worker_dir"; then
                local _wdel_tid
                _wdel_tid=$(get_task_id_from_worker "$(basename "$worker_dir")")
                echo "$(epoch_now)" > "$worker_dir/stop-reason-workspace-deleted"
                resume_state_increment "$worker_dir" "ABORT" "" "" "Workspace deleted — auto-abort"
                resume_state_set_terminal "$worker_dir" "Workspace deleted during execution"
                update_kanban_failed "$RALPH_DIR/kanban.md" "$_wdel_tid" || true
                github_issue_sync_task_status "$RALPH_DIR" "$_wdel_tid" "*" || true
                log_error "Worker $(basename "$worker_dir") workspace deleted — marked terminal"
                activity_log "worker.workspace_deleted" "$(basename "$worker_dir")" "$_wdel_tid"
                scheduler_mark_event
            fi
            continue
        fi
        [ -f "$worker_dir/prd.md" ] || continue

        # Skip if still running
        is_worker_running "$worker_dir" && continue

        # Skip terminal failures (last step + FAIL, or resume-state terminal)
        # Note: _is_terminal_failure includes _has_repeated_step_failures which
        # silently blocks workers. When it triggers here, mark terminal + update kanban
        # so tasks don't stay stuck as [=] forever.
        if _is_terminal_failure "$worker_dir"; then
            if ! resume_state_is_terminal "$worker_dir"; then
                local _term_tid
                _term_tid=$(get_task_id_from_worker "$(basename "$worker_dir")")
                if _has_repeated_step_failures "$worker_dir"; then
                    resume_state_set_terminal "$worker_dir" "Repeated failures at same pipeline step"
                    update_kanban_failed "$RALPH_DIR/kanban.md" "$_term_tid" || true
                    github_issue_sync_task_status "$RALPH_DIR" "$_term_tid" "*" || true
                    log_error "Worker $(basename "$worker_dir") repeated step failures — marked terminal"
                    activity_log "worker.resume_failed" "$(basename "$worker_dir")" "$_term_tid" "reason=repeated_step_failures"
                    scheduler_mark_event
                fi
            fi
            continue
        fi

        # Skip workers in cooldown (DEFER)
        resume_state_is_cooling "$worker_dir" && continue

        # Skip workers that exceeded max resume attempts — mark terminal
        if resume_state_max_exceeded "$worker_dir"; then
            if ! resume_state_is_terminal "$worker_dir"; then
                local _max_tid
                _max_tid=$(get_task_id_from_worker "$(basename "$worker_dir")")
                resume_state_set_terminal "$worker_dir" "Max resume attempts exceeded"
                update_kanban_failed "$RALPH_DIR/kanban.md" "$_max_tid" || true
                github_issue_sync_task_status "$RALPH_DIR" "$_max_tid" "*" || true
                log_error "Worker $(basename "$worker_dir") max resume attempts exceeded — marked terminal"
                activity_log "worker.resume_failed" "$(basename "$worker_dir")" "$_max_tid" "reason=max_attempts"
                scheduler_mark_event
            fi
            continue
        fi

        # Skip if decision already exists (not yet consumed by spawner)
        if [ -f "$worker_dir/resume-decision.json" ]; then
            # If .consumed exists but worker isn't running, stale — remove and allow re-decide
            if [ -f "$worker_dir/resume-decision.json.consumed" ] && ! is_worker_running "$worker_dir"; then
                rm -f "$worker_dir/resume-decision.json.consumed"
            else
                continue
            fi
        fi

        # Skip if decide process is already running
        if [ -f "$worker_dir/decide.pid" ]; then
            get_valid_worker_pid "$worker_dir/decide.pid" "bash" > /dev/null 2>&1 && continue
            # Stale decide.pid — clean up
            rm -f "$worker_dir/decide.pid"
        fi

        local task_id current_step worker_type
        task_id=$(get_task_id_from_worker "$(basename "$worker_dir")")

        # Get current step from pipeline config, default to execution
        if [ -f "$worker_dir/pipeline-config.json" ]; then
            current_step=$(jq -r '.current.step_id // "execution"' "$worker_dir/pipeline-config.json" 2>/dev/null)
        else
            current_step="execution"
        fi

        # Detect worker type from pipeline config, name pattern, and git-state
        worker_type=$(_detect_worker_type "$worker_dir")

        echo "$worker_dir $task_id $current_step $worker_type"
    done
}

# Find workers with a RETRY resume decision ready for spawning
#
# Scans for workers that have a resume-decision.json with decision=RETRY
# and are not yet consumed (no .consumed marker) and not currently running.
#
# Args:
#   ralph_dir - Ralph directory path
#
# Returns: Lines of "worker_dir task_id resume_step worker_type" for each worker
get_workers_with_retry_decision() {
    local ralph_dir="$1"
    [ -d "$ralph_dir/workers" ] || return 0

    for worker_dir in "$ralph_dir/workers"/worker-*; do
        [ -d "$worker_dir" ] || continue

        # Must have a resume-decision.json
        [ -f "$worker_dir/resume-decision.json" ] || continue

        # Skip if already consumed
        [ -f "$worker_dir/resume-decision.json.consumed" ] && continue

        # Skip if worker is running
        is_worker_running "$worker_dir" && continue

        # Skip terminal workers (stale decision file from before terminal was set)
        if resume_state_is_terminal "$worker_dir"; then
            rm -f "$worker_dir/resume-decision.json"
            continue
        fi

        # Skip max-exceeded workers (decision written before max check caught up)
        if resume_state_max_exceeded "$worker_dir"; then
            rm -f "$worker_dir/resume-decision.json"
            continue
        fi

        # Read decision (guard jq: corrupt JSON must not abort the loop)
        local decision
        decision=$(jq -r '.decision // ""' "$worker_dir/resume-decision.json" 2>/dev/null) || continue
        [ "$decision" = "RETRY" ] || continue

        local task_id resume_step worker_type
        task_id=$(get_task_id_from_worker "$(basename "$worker_dir")")
        resume_step=$(jq -r '.resume_step // "execution"' "$worker_dir/resume-decision.json" 2>/dev/null) || true
        [ "$resume_step" = "null" ] && resume_step="execution"

        worker_type=$(_detect_worker_type "$worker_dir")

        echo "$worker_dir $task_id $resume_step $worker_type"
    done
}

# Build a unified work queue merging new tasks and resume candidates
#
# Each line is: effective_pri|work_type|task_id|worker_dir|worker_type|resume_step
#   work_type: "new" or "resume"
#   For new tasks: worker_dir, worker_type, resume_step are empty
#   For resume tasks: all fields populated
#
# Sorted by effective_pri ascending (lower = higher priority).
# Respects WIGGUM_NO_RESUME to exclude resume items.
#
# Returns: sorted queue lines on stdout
get_unified_work_queue() {
    local kanban="$_SCHED_RALPH_DIR/kanban.md"
    local no_resume="${WIGGUM_NO_RESUME:-false}"

    # Use per-tick cached metadata when available (set by scheduler_tick)
    local all_metadata
    all_metadata="${_SCHED_TICK_METADATA:-$(_get_cached_metadata "$kanban")}"

    local reverse_graph
    reverse_graph=$(_build_reverse_dep_graph "$all_metadata")

    local queue=""

    # --- New tasks (use pre-computed priorities from scheduler_tick) ---
    if [ -n "${_SCHED_READY_WITH_PRIORITIES:-}" ]; then
        local _rwp_pri _rwp_tid
        while IFS='|' read -r _rwp_pri _rwp_tid; do
            [ -n "$_rwp_tid" ] || continue
            queue+="${_rwp_pri}|new|${_rwp_tid}|||"$'\n'
        done <<< "$_SCHED_READY_WITH_PRIORITIES"
    fi

    # --- Resume tasks (only workers with RETRY decision from two-phase resume) ---
    if [ "$no_resume" != "true" ]; then
        local retry_workers
        retry_workers=$(get_workers_with_retry_decision "$_SCHED_RALPH_DIR")

        while read -r worker_dir task_id resume_step worker_type; do
            [ -n "$worker_dir" ] || continue

            # Base priority from kanban
            local priority
            priority=$(echo "$all_metadata" | awk -F'|' -v t="$task_id" '$1 == t { print $3 }')
            local effective_pri
            case "$priority" in
                CRITICAL) effective_pri=0 ;;
                HIGH)     effective_pri=10000 ;;
                MEDIUM)   effective_pri=20000 ;;
                LOW)      effective_pri=30000 ;;
                *)        effective_pri=20000 ;;
            esac

            # Dependency depth bonus
            if [ "$_SCHED_DEP_BONUS_PER_TASK" -gt 0 ]; then
                local dep_depth
                dep_depth=$(_bfs_count_from_graph "$reverse_graph" "$task_id")
                effective_pri=$(( effective_pri - dep_depth * _SCHED_DEP_BONUS_PER_TASK ))
            fi

            # Pipeline progress bonus (up to 5000 for workers close to completion)
            if [ -f "$worker_dir/pipeline-config.json" ]; then
                local step_idx step_count
                step_idx=$(jq -r '.current.step_idx // 0' "$worker_dir/pipeline-config.json" 2>/dev/null) || true
                step_count=$(jq -r '.steps | length' "$worker_dir/pipeline-config.json" 2>/dev/null) || true
                step_idx="${step_idx:-0}"
                step_count="${step_count:-1}"
                if [ "$step_count" -gt 0 ]; then
                    local progress_bonus=$(( step_idx * 5000 / step_count ))
                    effective_pri=$(( effective_pri - progress_bonus ))
                fi
            fi

            # Resume initial bonus (makes fresh resumes compete well)
            effective_pri=$(( effective_pri - _SCHED_RESUME_INITIAL_BONUS ))

            # Failure penalty (each failed attempt degrades priority)
            local attempt_count
            attempt_count=$(resume_state_attempts "$worker_dir") || true
            attempt_count="${attempt_count:-0}"
            if [ "$attempt_count" -gt 0 ]; then
                effective_pri=$(( effective_pri + attempt_count * _SCHED_RESUME_FAIL_PENALTY ))
            fi

            [ "$effective_pri" -lt 0 ] && effective_pri=0

            queue+="${effective_pri}|resume|${task_id}|${worker_dir}|${worker_type}|${resume_step}"$'\n'
        done <<< "$retry_workers"
    fi

    # Sort by effective_pri ascending and output
    if [ -n "$queue" ]; then
        echo "$queue" | LC_ALL=C sort -t'|' -k1,1n | sed '/^$/d'
    fi
}

# Write scheduler state to JSON file
#
# Persists SCHED_READY_TASKS, SCHED_BLOCKED_TASKS, SCHED_PENDING_TASKS
# to scheduler-state.json for file-based state sharing.
#
# Args:
#   state_dir - Directory to write scheduler-state.json
scheduler_write_state() {
    local state_dir="$1"
    local state_file="$state_dir/scheduler-state.json"
    local now
    now=$(epoch_now)

    # Convert space-separated lists to JSON arrays
    local ready_json blocked_json pending_json
    ready_json=$(echo "$SCHED_READY_TASKS" | tr ' ' '\n' | jq -R 'select(length > 0)' | jq -s '.')
    blocked_json=$(echo "$SCHED_BLOCKED_TASKS" | tr ' ' '\n' | jq -R 'select(length > 0)' | jq -s '.')
    pending_json=$(echo "$SCHED_PENDING_TASKS" | tr ' ' '\n' | jq -R 'select(length > 0)' | jq -s '.')

    jq -n \
        --argjson computed_at "$now" \
        --argjson ready "$ready_json" \
        --argjson blocked "$blocked_json" \
        --argjson pending "$pending_json" \
        '{computed_at: $computed_at, ready_tasks: $ready, blocked_tasks: $blocked, pending_tasks: $pending}' \
        > "$state_file"
}

# Read scheduler state from JSON file
#
# Loads scheduler-state.json into SCHED_READY_TASKS, SCHED_BLOCKED_TASKS,
# SCHED_PENDING_TASKS global variables.
#
# Args:
#   state_dir - Directory containing scheduler-state.json
#
# Returns: 0 on success, 1 if file not found
scheduler_read_state() {
    local state_dir="$1"
    local state_file="$state_dir/scheduler-state.json"

    [ -f "$state_file" ] || return 1

    SCHED_READY_TASKS=$(jq -r '.ready_tasks // [] | .[]' "$state_file" 2>/dev/null | tr '\n' ' ')
    SCHED_BLOCKED_TASKS=$(jq -r '.blocked_tasks // [] | .[]' "$state_file" 2>/dev/null | tr '\n' ' ')
    SCHED_PENDING_TASKS=$(jq -r '.pending_tasks // [] | .[]' "$state_file" 2>/dev/null | tr '\n' ' ')

    # Trim trailing spaces
    SCHED_READY_TASKS="${SCHED_READY_TASKS% }"
    SCHED_BLOCKED_TASKS="${SCHED_BLOCKED_TASKS% }"
    SCHED_PENDING_TASKS="${SCHED_PENDING_TASKS% }"

    return 0
}

# Write cyclic tasks to JSON file
#
# Persists _SCHED_CYCLIC_TASKS to cyclic-tasks.json.
#
# Args:
#   state_dir - Directory to write cyclic-tasks.json
scheduler_write_cyclic() {
    local state_dir="$1"
    local cyclic_file="$state_dir/cyclic-tasks.json"

    local json='{'
    local first=true
    for task_id in "${!_SCHED_CYCLIC_TASKS[@]}"; do
        if [ "$first" = true ]; then
            first=false
        else
            json+=","
        fi
        json+="\"$task_id\":\"${_SCHED_CYCLIC_TASKS[$task_id]}\""
    done
    json+='}'

    echo "$json" > "$cyclic_file"
}

# Write skip tasks to JSON file
#
# Persists _SCHED_SKIP_TASKS to skip-tasks.json.
#
# Args:
#   state_dir - Directory to write skip-tasks.json
scheduler_write_skip_tasks() {
    local state_dir="$1"
    local skip_file="$state_dir/skip-tasks.json"

    local json='{'
    local first=true
    for task_id in "${!_SCHED_SKIP_TASKS[@]}"; do
        if [ "$first" = true ]; then
            first=false
        else
            json+=","
        fi
        json+="\"$task_id\":${_SCHED_SKIP_TASKS[$task_id]}"
    done
    json+='}'

    echo "$json" > "$skip_file"
}

# Read skip tasks from JSON file
#
# Loads skip-tasks.json into _SCHED_SKIP_TASKS.
#
# Args:
#   state_dir - Directory containing skip-tasks.json
#
# Returns: 0 on success, 1 if file not found
scheduler_read_skip_tasks() {
    local state_dir="$1"
    local skip_file="$state_dir/skip-tasks.json"

    [ -f "$skip_file" ] || return 1

    _SCHED_SKIP_TASKS=()
    local entries
    entries=$(jq -r 'to_entries[] | "\(.key)|\(.value)"' "$skip_file" 2>/dev/null) || return 1

    while IFS='|' read -r task_id count; do
        [ -n "$task_id" ] || continue
        _SCHED_SKIP_TASKS[$task_id]="$count"
    done <<< "$entries"

    return 0
}

# Write pending resumes to JSON file
#
# Args:
#   state_dir - Directory to write pending-resumes.json
#   -         - Pending resumes data is passed via _PENDING_RESUMES associative array
#              (pid -> "worker_dir|task_id|worker_type")
scheduler_write_pending_resumes() {
    local state_dir="$1"
    local resumes_file="$state_dir/pending-resumes.json"

    # Check if _PENDING_RESUMES exists
    if ! declare -p _PENDING_RESUMES &>/dev/null; then
        echo '{}' > "$resumes_file"
        return 0
    fi

    local json='{'
    local first=true
    for pid in "${!_PENDING_RESUMES[@]}"; do
        local info="${_PENDING_RESUMES[$pid]}"
        local worker_dir="${info%%|*}"
        local rest="${info#*|}"
        local task_id="${rest%%|*}"
        local worker_type="${rest##*|}"

        if [ "$first" = true ]; then
            first=false
        else
            json+=","
        fi
        json+="\"$pid\":{\"worker_dir\":\"$worker_dir\",\"task_id\":\"$task_id\",\"worker_type\":\"$worker_type\"}"
    done
    json+='}'

    echo "$json" > "$resumes_file"
}

# Read pending resumes from JSON file
#
# Loads pending-resumes.json into _PENDING_RESUMES associative array.
#
# Args:
#   state_dir - Directory containing pending-resumes.json
#
# Returns: 0 on success, 1 if file not found
scheduler_read_pending_resumes() {
    local state_dir="$1"
    local resumes_file="$state_dir/pending-resumes.json"

    [ -f "$resumes_file" ] || return 1

    # Ensure array exists
    if ! declare -p _PENDING_RESUMES &>/dev/null; then
        declare -gA _PENDING_RESUMES=()
    fi

    _PENDING_RESUMES=()
    local entries
    entries=$(jq -r 'to_entries[] | "\(.key)|\(.value.worker_dir)|\(.value.task_id)|\(.value.worker_type)"' "$resumes_file" 2>/dev/null) || return 1

    while IFS='|' read -r pid worker_dir task_id worker_type; do
        [ -n "$pid" ] || continue
        _PENDING_RESUMES[$pid]="$worker_dir|$task_id|$worker_type"
    done <<< "$entries"

    return 0
}

# Write pending decides to JSON file
#
# Args:
#   state_dir - Directory to write pending-decides.json
#   -         - Pending decides data is passed via _PENDING_DECIDES associative array
#              (pid -> "worker_dir|task_id|worker_type")
scheduler_write_pending_decides() {
    local state_dir="$1"
    local decides_file="$state_dir/pending-decides.json"

    # Check if _PENDING_DECIDES exists
    if ! declare -p _PENDING_DECIDES &>/dev/null; then
        echo '{}' > "$decides_file"
        return 0
    fi

    local json='{'
    local first=true
    for pid in "${!_PENDING_DECIDES[@]}"; do
        local info="${_PENDING_DECIDES[$pid]}"
        local worker_dir="${info%%|*}"
        local rest="${info#*|}"
        local task_id="${rest%%|*}"
        local worker_type="${rest##*|}"

        if [ "$first" = true ]; then
            first=false
        else
            json+=","
        fi
        json+="\"$pid\":{\"worker_dir\":\"$worker_dir\",\"task_id\":\"$task_id\",\"worker_type\":\"$worker_type\"}"
    done
    json+='}'

    echo "$json" > "$decides_file"
}

# Read pending decides from JSON file
#
# Loads pending-decides.json into _PENDING_DECIDES associative array.
#
# Args:
#   state_dir - Directory containing pending-decides.json
#
# Returns: 0 on success, 1 if file not found
scheduler_read_pending_decides() {
    local state_dir="$1"
    local decides_file="$state_dir/pending-decides.json"

    [ -f "$decides_file" ] || return 1

    # Ensure array exists
    if ! declare -p _PENDING_DECIDES &>/dev/null; then
        declare -gA _PENDING_DECIDES=()
    fi

    _PENDING_DECIDES=()
    local entries
    entries=$(jq -r 'to_entries[] | "\(.key)|\(.value.worker_dir)|\(.value.task_id)|\(.value.worker_type)"' "$decides_file" 2>/dev/null) || return 1

    while IFS='|' read -r pid worker_dir task_id worker_type; do
        [ -n "$pid" ] || continue
        _PENDING_DECIDES[$pid]="$worker_dir|$task_id|$worker_type"
    done <<< "$entries"

    return 0
}
