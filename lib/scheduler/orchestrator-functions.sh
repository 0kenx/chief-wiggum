#!/usr/bin/env bash
# =============================================================================
# orchestrator-functions.sh - Standalone functions for service-based orchestration
#
# This module provides callable functions that can be invoked by the service
# scheduler. Each function encapsulates orchestration logic that was previously
# embedded in wiggum-run's main loop.
#
# All functions use global RALPH_DIR and PROJECT_DIR variables, which must be
# set before calling. Alternatively, they can be passed via environment.
#
# Provides:
#   orch_run_periodic_sync()           - Sync PR statuses
#   orch_update_shared_usage()         - Update usage data
#   orch_spawn_pr_optimizer()          - Non-blocking PR optimization
#   orch_check_pr_optimizer()          - Check optimizer completion
#   orch_spawn_multi_pr_planner()      - Check and spawn planner
#   orch_cleanup_main_workers()        - Clean up main workers
#   orch_cleanup_fix_workers()         - Clean up fix workers
#   orch_cleanup_resolve_workers()     - Clean up resolve workers
#   orch_spawn_ready_tasks()           - Spawn workers for ready tasks
#   spawn_worker()                     - Spawn worker via wiggum-worker
#   pre_worker_checks()               - Git pull and conflict checks
#   _handle_main_worker_completion()   - Main worker completion callback
#   _handle_fix_worker_completion()    - Fix worker completion callback
#   _handle_fix_worker_timeout()       - Fix worker timeout callback
#   _handle_resolve_worker_completion() - Resolve worker completion callback
#   _handle_resolve_worker_timeout()   - Resolve worker timeout callback
#   _spawn_next_batch_worker()         - Batch queue continuation
#   _launch_resume_background()        - Launch resume process in background
#   _poll_pending_resumes()            - Poll background resume processes
# =============================================================================

# Prevent double-sourcing
[ -n "${_ORCHESTRATOR_FUNCTIONS_LOADED:-}" ] && return 0
_ORCHESTRATOR_FUNCTIONS_LOADED=1

# These functions depend on scheduler module components
# They should be sourced after the scheduler modules are loaded

# Run periodic sync to update PR statuses and detect new comments
#
# This is a standalone version of the sync logic that can be called
# by the service scheduler.
#
# Globals:
#   RALPH_DIR   - Required
#   PROJECT_DIR - Required
#
# Returns: 0 on success, 1 on failure
orch_run_periodic_sync() {
    local ralph_dir="${RALPH_DIR:-}"
    local project_dir="${PROJECT_DIR:-}"

    [ -n "$ralph_dir" ] || { log_error "RALPH_DIR not set"; return 1; }

    # Call wiggum pr sync and capture output
    local sync_output sync_exit=0
    sync_output=$("$WIGGUM_HOME/bin/wiggum-pr" sync 2>&1) || sync_exit=$?

    if [ $sync_exit -ne 0 ]; then
        log_error "Periodic sync failed"
        echo "$sync_output" | sed 's/^/  [sync] /'
        return 1
    fi

    # Parse sync results - only show output if something happened
    local merged_count comments_count
    merged_count=$(echo "$sync_output" | sed -n 's/.*Merged PRs updated: \([0-9]*\).*/\1/p' | head -1)
    comments_count=$(echo "$sync_output" | sed -n 's/.*Tasks with new comments: \([0-9]*\).*/\1/p' | head -1)
    merged_count=${merged_count:-0}
    comments_count=${comments_count:-0}

    if [ "$comments_count" -gt 0 ]; then
        log "PR sync: $comments_count task(s) with new comments"
        echo "$sync_output" | sed 's/^/  [sync] /'

        # Check for tasks needing fixes
        local tasks_needing_fix="$ralph_dir/orchestrator/tasks-needing-fix.txt"
        if [ -s "$tasks_needing_fix" ]; then
            log "Tasks need comment fixes - will spawn fix workers"
        fi
    fi

    return 0
}

# Update shared usage data for rate limiting
#
# Globals:
#   RALPH_DIR - Required
orch_update_shared_usage() {
    local ralph_dir="${RALPH_DIR:-}"
    [ -n "$ralph_dir" ] || return 1

    usage_tracker_write_shared "$ralph_dir" > /dev/null 2>&1 || true
}

# Spawn PR optimizer in background (non-blocking)
#
# Globals:
#   RALPH_DIR   - Required
#   PROJECT_DIR - Required
orch_spawn_pr_optimizer() {
    local ralph_dir="${RALPH_DIR:-}"
    local project_dir="${PROJECT_DIR:-}"

    [ -n "$ralph_dir" ] || return 1
    [ -d "$ralph_dir/workers" ] || return 0

    # Check if already running
    if pr_optimizer_is_running "$ralph_dir"; then
        log_debug "PR optimizer already running"
        return 0
    fi

    # Spawn in background
    pr_merge_spawn_background "$ralph_dir" "$project_dir"
}

# Check for completed PR optimizer and process results
#
# Globals:
#   RALPH_DIR - Required
orch_check_pr_optimizer() {
    local ralph_dir="${RALPH_DIR:-}"
    [ -n "$ralph_dir" ] || return 1

    local merged_count

    # Check if optimizer completed (or failed)
    if merged_count=$(pr_optimizer_check_completion "$ralph_dir"); then
        if [ "$merged_count" -gt 0 ]; then
            log "PR optimizer completed: merged $merged_count PR(s)"
            activity_log "pr_optimizer.completed" "" "" "merged=$merged_count"
        else
            log_debug "PR optimizer completed: no PRs merged"
        fi

        # Clear status for next cycle
        pr_optimizer_clear_status "$ralph_dir"
    fi
}

# Check for completed multi-PR planners
#
# Globals:
#   RALPH_DIR   - Required
#   PROJECT_DIR - Required
_orch_check_completed_planners() {
    local ralph_dir="${RALPH_DIR:-}"
    local project_dir="${PROJECT_DIR:-}"

    [ -n "$ralph_dir" ] || return 1
    [ -d "$ralph_dir/workers" ] || return 0

    for planner_dir in "$ralph_dir/workers"/planner-batch-*; do
        [ -d "$planner_dir" ] || continue

        local batch_id
        batch_id=$(basename "$planner_dir" | sed 's/^planner-//')

        # Skip if not in planning status
        local status
        status=$(conflict_queue_get_batch_status "$ralph_dir" "$batch_id" 2>/dev/null || echo "unknown")
        [ "$status" = "planning" ] || continue

        # Check if planner is still running
        local pid_file="$planner_dir/planner.pid"
        if [ -f "$pid_file" ]; then
            local pid
            pid=$(cat "$pid_file")
            if kill -0 "$pid" 2>/dev/null; then
                continue  # Still running
            fi
        fi

        # Planner finished - check result
        local result_file
        result_file=$(find "$planner_dir/results" -name "*-result.json" 2>/dev/null | head -1)

        if [ -n "$result_file" ] && [ -f "$result_file" ]; then
            local gate_result
            gate_result=$(jq -r '.outputs.gate_result // "FAIL"' "$result_file")

            if [ "$gate_result" = "PASS" ]; then
                conflict_queue_update_batch_status "$ralph_dir" "$batch_id" "planned"
                log "Multi-PR planning completed for batch $batch_id"

                # Mark individual workers as ready for resolution with plan
                local task_ids
                task_ids=$(conflict_queue_get_batch_tasks "$ralph_dir" "$batch_id")
                while read -r task_id; do
                    [ -n "$task_id" ] || continue
                    local worker_dir
                    worker_dir=$(find_worker_by_task_id "$ralph_dir" "$task_id" 2>/dev/null)
                    if [ -n "$worker_dir" ] && [ -d "$worker_dir" ]; then
                        # Skip workers already in terminal states
                        local current_state
                        current_state=$(git_state_get "$worker_dir" 2>/dev/null || echo "unknown")
                        if [[ "$current_state" == "merged" || "$current_state" == "failed" ]]; then
                            continue
                        fi
                        if [ ! -d "$worker_dir/workspace" ]; then
                            continue
                        fi
                        git_state_set "$worker_dir" "needs_resolve" "orchestrator-functions._orch_check_completed_planners" "Resolution plan ready"
                    fi
                done <<< "$task_ids"
            else
                conflict_queue_update_batch_status "$ralph_dir" "$batch_id" "failed"
                log_error "Multi-PR planning failed for batch $batch_id"
            fi
        else
            if [ -f "$pid_file" ]; then
                log_warn "Multi-PR planner for $batch_id exited without result"
                conflict_queue_update_batch_status "$ralph_dir" "$batch_id" "failed"
            fi
        fi
    done
}

# Check for conflict batches and spawn multi-PR planner if needed
#
# Globals:
#   RALPH_DIR   - Required
#   PROJECT_DIR - Required
orch_spawn_multi_pr_planner() {
    local ralph_dir="${RALPH_DIR:-}"
    local project_dir="${PROJECT_DIR:-}"

    [ -n "$ralph_dir" ] || return 1
    [ -n "$project_dir" ] || return 1

    # First, check for completed planners
    _orch_check_completed_planners

    # Initialize conflict queue if needed
    conflict_queue_init "$ralph_dir"

    # Check if a planner is already running
    for planner_dir in "$ralph_dir/workers"/planner-batch-*; do
        [ -d "$planner_dir" ] || continue
        local pid_file="$planner_dir/planner.pid"
        if [ -f "$pid_file" ]; then
            local pid
            pid=$(cat "$pid_file")
            if kill -0 "$pid" 2>/dev/null; then
                return 0  # Planner already running
            fi
        fi
    done

    local batch_id task_ids

    # First, check for existing "pending" batches
    local queue_file="$ralph_dir/batches/queue.json"
    if [ -f "$queue_file" ]; then
        batch_id=$(jq -r '[.batches | to_entries[] | select(.value.status == "pending")] | .[0].key // empty' "$queue_file")
        if [ -n "$batch_id" ]; then
            task_ids=$(jq -r --arg b "$batch_id" '.batches[$b].task_ids' "$queue_file")
            log "Found pending batch $batch_id ready for planning"
        fi
    fi

    # If no pending batch, try grouping unbatched tasks
    if [ -z "$batch_id" ]; then
        if ! conflict_queue_batch_ready "$ralph_dir"; then
            return 0
        fi

        local groups
        groups=$(conflict_queue_group_related "$ralph_dir")

        local group_count
        group_count=$(echo "$groups" | jq 'length')

        if [ "$group_count" -eq 0 ]; then
            return 0
        fi

        log "Found $group_count conflict group(s) ready for coordinated planning"

        local first_group
        first_group=$(echo "$groups" | jq '.[0]')
        task_ids=$(echo "$first_group" | jq '.task_ids')

        batch_id=$(conflict_queue_create_batch "$ralph_dir" "$task_ids")
        local task_count
        task_count=$(echo "$task_ids" | jq 'length')
        log "Created conflict batch $batch_id with $task_count tasks"
    fi

    # Create planner worker directory
    local planner_worker_dir="$ralph_dir/workers/planner-$batch_id"
    mkdir -p "$planner_worker_dir/logs" "$planner_worker_dir/results"

    # Build batch file
    if ! conflict_queue_build_batch_file "$ralph_dir" "$batch_id" "$planner_worker_dir/conflict-batch.json"; then
        log_error "Failed to build batch file for $batch_id - marking batch as failed"
        conflict_queue_update_batch_status "$ralph_dir" "$batch_id" "failed"
        rm -rf "$planner_worker_dir"
        return 1
    fi

    # Update batch status
    conflict_queue_update_batch_status "$ralph_dir" "$batch_id" "planning"

    log "Spawning multi-PR planner for batch $batch_id (non-blocking)"

    # Launch planner agent in background
    (
        cd "$project_dir" || exit 1
        export WIGGUM_HOME
        source "$WIGGUM_HOME/lib/worker/agent-registry.sh"
        run_agent "workflow.multi-pr-planner" "$planner_worker_dir" "$project_dir" 0
    ) >> "$ralph_dir/logs/planner.log" 2>&1 &

    local planner_pid=$!
    echo "$planner_pid" > "$planner_worker_dir/planner.pid"

    log "Multi-PR planner spawned (PID: $planner_pid)"
}

# Clean up finished main workers
#
# Globals:
#   RALPH_DIR - Required (via scheduler context)
#
# Args:
#   completion_callback - Optional callback function name
# shellcheck disable=SC2120  # Optional callback parameter for extensibility
orch_cleanup_main_workers() {
    local callback="${1:-}"

    # Use default callback if none provided
    if [ -z "$callback" ]; then
        _default_main_completion() {
            local worker_dir="$1"
            local task_id="$2"
            activity_log "worker.completed" "" "$task_id" "worker_dir=$worker_dir"
            log "Worker for $task_id finished"
            scheduler_mark_event
        }
        callback="_default_main_completion"
    fi

    pool_cleanup_finished "main" 0 "$callback" ""
}

# Clean up finished/timed-out fix workers
#
# Globals:
#   RALPH_DIR - Required (via scheduler context)
#
# Args:
#   timeout - Timeout in seconds (default: 1800)
orch_cleanup_fix_workers() {
    local timeout="${1:-1800}"

    # Default completion callback
    _fix_completion() {
        local worker_dir="$1"
        local task_id="$2"

        if handle_fix_worker_completion "$worker_dir" "$task_id"; then
            if git_state_is "$worker_dir" "needs_merge"; then
                attempt_pr_merge "$worker_dir" "$task_id" "$RALPH_DIR" || true
            fi
        fi
    }

    # Default timeout callback
    _fix_timeout() {
        local worker_dir="$1"
        local task_id="$2"
        handle_fix_worker_timeout "$worker_dir" "$task_id" "$timeout"
    }

    pool_cleanup_finished "fix" "$timeout" "_fix_completion" "_fix_timeout"
}

# Clean up finished/timed-out resolve workers
#
# Globals:
#   RALPH_DIR   - Required (via scheduler context)
#   PROJECT_DIR - Required
#
# Args:
#   timeout - Timeout in seconds (default: 1800)
orch_cleanup_resolve_workers() {
    local timeout="${1:-1800}"

    # Default completion callback
    _resolve_completion() {
        local worker_dir="$1"
        local task_id="$2"

        if handle_resolve_worker_completion "$worker_dir" "$task_id"; then
            if git_state_is "$worker_dir" "needs_merge"; then
                attempt_pr_merge "$worker_dir" "$task_id" "$RALPH_DIR" || true
            fi
        fi
    }

    # Default timeout callback
    _resolve_timeout() {
        local worker_dir="$1"
        local task_id="$2"
        handle_resolve_worker_timeout "$worker_dir" "$task_id" "$timeout"
    }

    pool_cleanup_finished "resolve" "$timeout" "_resolve_completion" "_resolve_timeout"
}

# Process orphaned fix_completed/needs_merge workers
#
# Scans for workers stuck in fix_completed or needs_merge states with no
# running agent. These can occur when the orchestrator restarts and workers
# complete outside the pool cleanup callbacks, or when inline merge attempts
# are missed.
#
# For fix_completed: runs the completion handler to transition to needs_merge,
# then attempts merge.
# For needs_merge: attempts merge directly.
#
# Globals:
#   RALPH_DIR - Required (via scheduler context)
#
# Returns: 0 always (errors are logged per-worker)
orch_process_pending_merges() {
    local ralph_dir="${RALPH_DIR:-}"
    [ -n "$ralph_dir" ] || return 1
    [ -d "$ralph_dir/workers" ] || return 0

    for worker_dir in "$ralph_dir/workers"/worker-*; do
        [ -d "$worker_dir" ] || continue

        local state
        state=$(git_state_get "$worker_dir")

        local worker_id task_id
        worker_id=$(basename "$worker_dir")
        task_id=$(get_task_id_from_worker "$worker_id")

        # Skip if agent is still running
        if [ -f "$worker_dir/agent.pid" ]; then
            local pid
            pid=$(cat "$worker_dir/agent.pid" 2>/dev/null || true)
            if [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null; then
                continue
            fi
        fi

        case "$state" in
            fix_completed)
                # Orphaned fix_completed - run completion handler to transition
                if handle_fix_worker_completion "$worker_dir" "$task_id"; then
                    if git_state_is "$worker_dir" "needs_merge"; then
                        attempt_pr_merge "$worker_dir" "$task_id" "$ralph_dir" || true
                    fi
                fi
                ;;
            needs_merge)
                attempt_pr_merge "$worker_dir" "$task_id" "$ralph_dir" || true
                ;;
        esac
    done
}

# Clean up all finished workers (main, fix, resolve)
#
# Consolidated cleanup function that handles all worker types.
# This is more efficient than running 3 separate services.
#
# Globals:
#   RALPH_DIR   - Required (via scheduler context)
#   PROJECT_DIR - Required
#
# Args:
#   fix_timeout     - Timeout for fix workers (default: 1800)
#   resolve_timeout - Timeout for resolve workers (default: 1800)
orch_cleanup_all_workers() {
    local fix_timeout="${1:-1800}"
    local resolve_timeout="${2:-1800}"

    # Clean up main workers (no timeout)
    orch_cleanup_main_workers

    # Clean up fix workers
    orch_cleanup_fix_workers "$fix_timeout"

    # Clean up resolve workers
    orch_cleanup_resolve_workers "$resolve_timeout"

    # Process orphaned fix_completed/needs_merge workers
    orch_process_pending_merges
}

# Spawn workers for ready tasks
#
# This is the main task spawning logic extracted from wiggum-run.
# It spawns workers for tasks that are ready and have capacity.
#
# Globals:
#   RALPH_DIR     - Required
#   PROJECT_DIR   - Required
#   MAX_WORKERS   - Required
#   MAX_ITERATIONS - Required
#   MAX_TURNS     - Required
#   AGENT_TYPE    - Required
#
# Returns: 0 on success
orch_spawn_ready_tasks() {
    local ralph_dir="${RALPH_DIR:-}"
    local project_dir="${PROJECT_DIR:-}"
    local max_workers="${MAX_WORKERS:-4}"
    local max_iterations="${MAX_ITERATIONS:-20}"
    local max_turns="${MAX_TURNS:-50}"
    local agent_type="${AGENT_TYPE:-system.task-worker}"

    [ -n "$ralph_dir" ] || return 1
    [ -n "$project_dir" ] || return 1

    # Tick scheduler to get latest task lists
    scheduler_tick

    # Check rate limit before spawning
    if rate_limit_check "$ralph_dir"; then
        log "Rate limit threshold reached - deferring spawning"
        return 0
    fi

    # Pre-flight: pull latest main once per cycle
    if ! _orch_pre_worker_checks; then
        log_error "Pre-worker git checks failed - skipping all spawns this cycle"
        return 0
    fi

    # Spawn workers for ready tasks
    for task_id in $SCHED_READY_TASKS; do
        # Check if we can spawn this task
        if ! scheduler_can_spawn_task "$task_id" "$max_workers"; then
            case "$SCHED_SKIP_REASON" in
                at_capacity) break ;;
                file_conflict|cyclic_dependency|skip_count) continue ;;
            esac
            continue
        fi

        local task_priority
        task_priority=$(get_task_priority "$ralph_dir/kanban.md" "$task_id")

        # Mark task as in-progress
        log "Assigning $task_id (Priority: ${task_priority:-MEDIUM}) to new worker"
        if ! update_kanban_status "$ralph_dir/kanban.md" "$task_id" "="; then
            log_error "Failed to mark $task_id as in-progress"
            scheduler_increment_skip "$task_id"
            continue
        fi

        # Spawn worker
        if ! _orch_spawn_worker "$task_id" "$max_iterations" "$max_turns" "$agent_type"; then
            log_error "Failed to spawn worker for $task_id"
            update_kanban_status "$ralph_dir/kanban.md" "$task_id" "*"
            continue
        fi

        pool_add "$SPAWNED_WORKER_PID" "main" "$task_id"
        scheduler_mark_event
        scheduler_remove_from_aging "$task_id"

        log "Spawned worker $SPAWNED_WORKER_ID for $task_id (PID: $SPAWNED_WORKER_PID)"
    done

    # Update aging tracking
    scheduler_update_aging
}

# Pre-worker checks before spawning
#
# Pulls latest from main and checks for conflicts.
_orch_pre_worker_checks() {
    # Pull latest changes from main with retry
    local pull_output
    local max_attempts=3
    local delays=(2 4)
    local dirty_reset_done=false

    for ((attempt=1; attempt<=max_attempts; attempt++)); do
        if pull_output=$(git pull --ff-only origin main 2>&1); then
            break
        fi

        # Immediately fail on merge conflicts (requires manual resolution)
        if echo "$pull_output" | grep -qi "CONFLICT"; then
            log_error "Git pull conflict detected: $pull_output"
            return 1
        fi

        # Dirty/untracked working directory - reset the blocking files and retry once
        if [ "$dirty_reset_done" = false ] && echo "$pull_output" | grep -qiE "(local changes|untracked.*files).*overwritten"; then
            local dirty_files
            dirty_files=$(echo "$pull_output" | sed -n '/would be overwritten/,/Please\|Aborting/{//d; s/^[[:space:]]*//; /^$/d; p}')
            if [ -n "$dirty_files" ]; then
                log_warn "Resetting files blocking pull: $dirty_files"
                echo "$dirty_files" | xargs git checkout -- 2>/dev/null || true
                # Also remove untracked files that block merge
                echo "$dirty_files" | while read -r f; do
                    [ -f "$f" ] && rm -f "$f"
                done 2>/dev/null || true
                dirty_reset_done=true
                # Retry immediately (don't burn an attempt on this)
                attempt=$((attempt - 1))
                continue
            fi
        fi

        if [ $attempt -eq $max_attempts ]; then
            log_error "Git pull failed after $max_attempts attempts: $pull_output"
            return 1
        fi

        local delay=${delays[$((attempt-1))]}
        sleep "$delay"
    done

    return 0
}

# Spawn a worker for a task
#
# Sets: SPAWNED_WORKER_ID, SPAWNED_WORKER_PID
_orch_spawn_worker() {
    local task_id="$1"
    local max_iterations="$2"
    local max_turns="$3"
    local agent_type="$4"

    local ralph_dir="${RALPH_DIR:-}"

    local start_output start_exit_code=0
    start_output=$("$WIGGUM_HOME/bin/wiggum-worker" start "$task_id" \
        --max-iters "$max_iterations" --max-turns "$max_turns" \
        --agent-type "$agent_type" 2>&1) || start_exit_code=$?

    if [ "$start_exit_code" -ne 0 ]; then
        log_error "wiggum worker start failed (exit $start_exit_code): $start_output"
        return 1
    fi

    local worker_dir
    worker_dir=$(find_worker_by_task_id "$ralph_dir" "$task_id")

    if [ -z "$worker_dir" ]; then
        log_error "Failed to find worker directory for $task_id"
        return 1
    fi

    SPAWNED_WORKER_ID=$(basename "$worker_dir")

    # Wait for agent.pid
    local wait_timeout="${PID_WAIT_TIMEOUT:-300}"
    if ! wait_for_worker_pid "$worker_dir" "$wait_timeout"; then
        log_error "Agent PID file not created for $task_id"
        return 1
    fi

    SPAWNED_WORKER_PID=$(cat "$worker_dir/agent.pid")

    activity_log "task.started" "$SPAWNED_WORKER_ID" "$task_id"

    return 0
}

# Update header status data and log detailed status on scheduling events
orch_display_status() {
    local ralph_dir="${RALPH_DIR:-}"
    local max_workers="${MAX_WORKERS:-4}"
    local aging_factor="${AGING_FACTOR:-7}"
    local plan_bonus="${PLAN_BONUS:-15000}"
    local dep_bonus="${DEP_BONUS_PER_TASK:-7000}"

    if [ "$SCHED_SCHEDULING_EVENT" = true ]; then
        local cyclic_ref status_counts
        cyclic_ref=$(scheduler_get_cyclic_tasks_ref)
        status_counts=$(compute_status_counts "$SCHED_READY_TASKS" "$SCHED_BLOCKED_TASKS" "$cyclic_ref" "$ralph_dir")
        local _sc_ready _sc_blocked _sc_deferred _sc_cyclic _sc_errors _sc_stuck
        IFS='|' read -r _sc_ready _sc_blocked _sc_deferred _sc_cyclic _sc_errors _sc_stuck <<< "$status_counts"
        _log_detailed_status \
            "0" \
            "$max_workers" \
            "$SCHED_READY_TASKS" \
            "$SCHED_BLOCKED_TASKS" \
            "$cyclic_ref" \
            "$ralph_dir" \
            "$(scheduler_get_ready_since_file)" \
            "$aging_factor" \
            "$plan_bonus" \
            "$dep_bonus"

        log "[status] ready: $_sc_ready | blocked: $_sc_blocked | deferred: $_sc_deferred | errors: $_sc_errors"
    fi
}

# =============================================================================
# Service-callable wrapper functions
#
# These wrappers are designed to be called by the service scheduler.
# They read required arguments from environment variables (RALPH_DIR,
# PROJECT_DIR, etc.) which are exported by the service runner.
# =============================================================================

# Wrapper for usage_tracker_write_shared
#
# Globals:
#   RALPH_DIR - Required
orch_usage_tracker_write_shared() {
    local ralph_dir="${RALPH_DIR:-}"
    [ -n "$ralph_dir" ] || return 1

    usage_tracker_write_shared "$ralph_dir" > /dev/null 2>&1 || true
}

# Wrapper for create_orphan_pr_workspaces
#
# Globals:
#   RALPH_DIR   - Required
#   PROJECT_DIR - Required
orch_create_orphan_pr_workspaces() {
    local ralph_dir="${RALPH_DIR:-}"
    local project_dir="${PROJECT_DIR:-}"

    [ -n "$ralph_dir" ] || return 1
    [ -n "$project_dir" ] || return 1

    create_orphan_pr_workspaces "$ralph_dir" "$project_dir"
}

# Wrapper for spawn_fix_workers
#
# Globals:
#   RALPH_DIR        - Required
#   PROJECT_DIR      - Required
#   FIX_WORKER_LIMIT - Optional (default: 2)
orch_spawn_fix_workers() {
    local ralph_dir="${RALPH_DIR:-}"
    local project_dir="${PROJECT_DIR:-}"
    local limit="${FIX_WORKER_LIMIT:-2}"

    [ -n "$ralph_dir" ] || return 1
    [ -n "$project_dir" ] || return 1

    spawn_fix_workers "$ralph_dir" "$project_dir" "$limit"
}

# Wrapper for spawn_resolve_workers
#
# Globals:
#   RALPH_DIR        - Required
#   PROJECT_DIR      - Required
#   FIX_WORKER_LIMIT - Optional (default: 2)
orch_spawn_resolve_workers() {
    local ralph_dir="${RALPH_DIR:-}"
    local project_dir="${PROJECT_DIR:-}"
    local limit="${FIX_WORKER_LIMIT:-2}"

    [ -n "$ralph_dir" ] || return 1
    [ -n "$project_dir" ] || return 1

    spawn_resolve_workers "$ralph_dir" "$project_dir" "$limit"
}

# Wrapper for scheduler_tick
#
# Note: This function operates on in-memory state, so it only works
# when called in the same process as the scheduler. For the service
# scheduler, this is handled by the main orchestrator loop.
orch_scheduler_tick() {
    # scheduler_tick operates on in-memory state (_SCHED_* vars)
    # This is called in a subshell by the service runner, so it's a no-op
    # The main orchestrator should call scheduler_tick directly
    :
}

# Wrapper for scheduler_detect_orphan_workers
#
# Note: This function operates on in-memory state (worker pool),
# so it only works in the main orchestrator process.
orch_detect_orphan_workers() {
    # scheduler_detect_orphan_workers operates on the worker pool
    # which is in-memory state. This is a no-op in subshells.
    :
}

# Wrapper for scheduler_update_aging
#
# Note: This function operates on in-memory state, so it only works
# when called in the same process as the scheduler.
orch_update_aging() {
    # scheduler_update_aging operates on in-memory state
    # This is a no-op in subshells.
    :
}

# =============================================================================
# GitHub Issue Sync
# =============================================================================

# Run GitHub issue sync (down + up)
#
# Called as a periodic service to sync issues.
# Loads config, checks if enabled, and runs the sync engine.
#
# Globals:
#   RALPH_DIR   - Required
#   WIGGUM_HOME - Required
#
# Returns: 0 on success, 1 on failure
orch_github_issue_sync() {
    local ralph_dir="${RALPH_DIR:-}"
    [ -n "$ralph_dir" ] || { log_error "RALPH_DIR not set"; return 1; }

    source "$WIGGUM_HOME/lib/github/issue-config.sh"
    load_github_sync_config

    if ! github_sync_is_enabled; then
        log_debug "GitHub issue sync disabled - skipping"
        return 0
    fi

    if ! github_sync_validate_config; then
        log_error "GitHub issue sync config invalid - skipping"
        return 1
    fi

    source "$WIGGUM_HOME/lib/github/issue-sync.sh"

    local sync_exit=0
    github_issue_sync "$ralph_dir" "false" || sync_exit=$?

    if [ "$sync_exit" -ne 0 ]; then
        log_error "GitHub issue sync failed"
        return 1
    fi

    return 0
}

# Sync plan files (.ralph/plans/) with GitHub issue comments
#
# Runs bidirectional sync for all tracked plans. Uses the same
# github.issue_sync.enabled gate as issue sync.
#
# Returns: 0 on success, 1 on failure
orch_github_plan_sync() {
    local ralph_dir="${RALPH_DIR:-}"
    [ -n "$ralph_dir" ] || { log_error "RALPH_DIR not set"; return 1; }

    source "$WIGGUM_HOME/lib/github/issue-config.sh"
    load_github_sync_config

    if ! github_sync_is_enabled; then
        log_debug "GitHub issue sync disabled - skipping plan sync"
        return 0
    fi

    if ! github_sync_validate_config; then
        log_error "GitHub sync config invalid - skipping plan sync"
        return 1
    fi

    source "$WIGGUM_HOME/lib/github/plan-sync.sh"

    local sync_exit=0
    github_plan_sync "$ralph_dir" "" "false" "" || sync_exit=$?

    if [ "$sync_exit" -ne 0 ]; then
        log_warn "GitHub plan sync completed with conflicts"
    fi

    return 0
}

# =============================================================================
# Worker Spawn and Lifecycle Functions
#
# Extracted from wiggum-run to keep the entry point minimal.
# These functions are called by service handlers in orchestrator-handlers.sh.
# =============================================================================

# Tracks background resume processes: pid → "worker_dir|task_id|worker_type"
declare -gA _PENDING_RESUMES=()

# Tracks background resume-decide processes: pid → "worker_dir|task_id|worker_type"
declare -gA _PENDING_DECIDES=()

# Spawn a worker for a task using wiggum-worker
# Sets: SPAWNED_WORKER_ID, SPAWNED_WORKER_PID (for caller to use)
spawn_worker() {
    local task_id="$1"

    # Use wiggum-worker to start the worker, capturing exit code
    local start_output
    local start_exit_code
    start_output=$("$WIGGUM_HOME/bin/wiggum-worker" start "$task_id" \
        --max-iters "$MAX_ITERATIONS" --max-turns "$MAX_TURNS" \
        --agent-type "$AGENT_TYPE" 2>&1) || start_exit_code=$?
    start_exit_code=${start_exit_code:-0}

    # Handle specific exit codes
    if [ "$start_exit_code" -eq "$EXIT_WORKER_ALREADY_EXISTS" ]; then
        # Worker directory exists from previous run
        # Exclude plan workers (worker-TASK-xxx-plan-*) - those are read-only planning sessions
        local existing_dir
        existing_dir=$(find_any_worker_by_task_id "$RALPH_DIR" "$task_id" | grep -v -- '-plan-' || true)
        if [ -n "$existing_dir" ]; then
            # Check if the worker process is still running
            local stale_pid
            stale_pid=$(cat "$existing_dir/agent.pid" 2>/dev/null || true)
            if [ -n "$stale_pid" ] && kill -0 "$stale_pid" 2>/dev/null; then
                # Process is still running, refuse to spawn duplicate
                log_error "Worker for $task_id is still running (PID: $stale_pid)"
                log_error "Use 'wiggum worker stop $task_id' or 'wiggum worker kill $task_id' first"
                return 1
            fi
            # Process not running - check if it's resumable
            if ! _is_terminal_failure "$existing_dir"; then
                # Worker is resumable - let resume logic handle it
                # Return 2 (deferred) so caller can distinguish from actual failure
                log "Worker for $task_id is resumable, deferring to resume logic"
                return 2
            fi
            # Terminal failure - clean up and retry fresh
            log "Cleaning up terminal-failure worker for $task_id: $(basename "$existing_dir")"
            rm -rf "$existing_dir"
            # Retry spawning - reset exit code first
            start_exit_code=0
            start_output=$("$WIGGUM_HOME/bin/wiggum-worker" start "$task_id" \
                --max-iters "$MAX_ITERATIONS" --max-turns "$MAX_TURNS" \
                --agent-type "$AGENT_TYPE" 2>&1) || start_exit_code=$?
        fi
    fi

    # Check if spawn succeeded
    if [ "$start_exit_code" -ne 0 ]; then
        log_error "wiggum worker start failed (exit $start_exit_code): $start_output"
        return 1
    fi

    # Find the worker directory that was just created (using shared library)
    local worker_dir
    worker_dir=$(find_worker_by_task_id "$RALPH_DIR" "$task_id")

    if [ -z "$worker_dir" ]; then
        log_error "Failed to find worker directory for $task_id"
        return 1
    fi

    SPAWNED_WORKER_ID=$(basename "$worker_dir")

    # Wait for agent.pid to appear (using shared library)
    if ! wait_for_worker_pid "$worker_dir" "$PID_WAIT_TIMEOUT"; then
        log_error "Agent PID file not created for $task_id"
        return 1
    fi

    SPAWNED_WORKER_PID=$(cat "$worker_dir/agent.pid")
    activity_log "worker.spawned" "$SPAWNED_WORKER_ID" "$task_id" "pid=$SPAWNED_WORKER_PID"
}

# Pre-worker checks before spawning a new worker
# Returns 0 if safe to proceed, 1 if conflicts detected
pre_worker_checks() {
    # Pull latest changes from main with retry
    log "Pulling latest changes from origin/main..."

    local pull_output
    local max_attempts=3
    local delays=(2 4)
    local dirty_reset_done=false

    for ((attempt=1; attempt<=max_attempts; attempt++)); do
        if pull_output=$(git pull --ff-only origin main 2>&1); then
            break
        fi

        # Immediately fail on merge conflicts (requires manual resolution)
        if echo "$pull_output" | grep -qi "CONFLICT"; then
            log_error "Git pull conflict detected: $pull_output"
            log_error "Cannot spawn new workers with unresolved conflicts"
            return 1
        fi

        # Dirty/untracked working directory - reset the blocking files and retry once
        if [ "$dirty_reset_done" = false ] && echo "$pull_output" | grep -qiE "(local changes|untracked.*files).*overwritten"; then
            local dirty_files
            dirty_files=$(echo "$pull_output" | sed -n '/would be overwritten/,/Please\|Aborting/{//d; s/^[[:space:]]*//; /^$/d; p}')
            if [ -n "$dirty_files" ]; then
                log_warn "Resetting files blocking pull: $dirty_files"
                echo "$dirty_files" | xargs git checkout -- 2>/dev/null || true
                # Also remove untracked files that block merge
                echo "$dirty_files" | while read -r f; do
                    [ -f "$f" ] && rm -f "$f"
                done 2>/dev/null || true
                dirty_reset_done=true
                # Retry immediately (don't burn an attempt on this)
                attempt=$((attempt - 1))
                continue
            fi
        fi

        # On last attempt, give up
        if [ $attempt -eq $max_attempts ]; then
            log_error "Git pull failed after $max_attempts attempts: $pull_output"
            return 1
        fi

        # Transient error - retry with backoff
        local delay=${delays[$((attempt-1))]}
        log "Git pull attempt $attempt failed (transient), retrying in ${delay}s..."
        sleep "$delay"
    done

    # Check for conflicts with active worktrees
    local workers_dir="$RALPH_DIR/workers"
    if [ -d "$workers_dir" ]; then
        for worker_dir in "$workers_dir"/worker-*; do
            [ -d "$worker_dir/workspace" ] || continue

            local workspace="$worker_dir/workspace"
            if [ -d "$workspace/.git" ] || [ -f "$workspace/.git" ]; then
                # Check if worktree has conflicts with main
                if git -C "$workspace" diff --name-only origin/main 2>/dev/null | \
                   xargs -I {} git -C "$workspace" diff --check origin/main -- {} 2>&1 | \
                   grep -q "conflict"; then
                    log_error "Conflict detected in $(basename "$worker_dir")"
                    return 1
                fi
            fi
        done
    fi

    return 0
}

# Handle main worker completion (callback for pool_cleanup_finished)
_handle_main_worker_completion() {
    local worker_dir="$1"
    local task_id="$2"
    activity_log "worker.completed" "" "$task_id" "worker_dir=$worker_dir"
    log "Worker for $task_id finished"
    scheduler_mark_event

    local _gate_result="UNKNOWN"
    local _result_file
    _result_file=$(find "$worker_dir/results" -name "*-result.json" 2>/dev/null | sort -r | head -1)
    if [ -n "${_result_file:-}" ] && [ -f "$_result_file" ]; then
        _gate_result=$(jq -r '.outputs.gate_result // "UNKNOWN"' "$_result_file" 2>/dev/null)
        _gate_result="${_gate_result:-UNKNOWN}"
    fi
    activity_log "task.completed" "$(basename "$worker_dir")" "$task_id" "result=$_gate_result"

    # Collect deterministic stats (fast, synchronous)
    source "$WIGGUM_HOME/lib/memory/memory.sh"
    memory_collect_stats "$worker_dir" "$RALPH_DIR" || true
    # Queue for LLM analysis (async, processed by memory-extract service)
    memory_queue_worker "$worker_dir" || true

    # If PR was created and is already in needs_merge state, attempt merge
    # immediately (mirrors fix/resolve completion callbacks)
    if git_state_is "$worker_dir" "needs_merge"; then
        attempt_pr_merge "$worker_dir" "$task_id" "$RALPH_DIR" || true
    fi
}

# Handle fix worker completion (callback for pool_cleanup_finished)
_handle_fix_worker_completion() {
    local worker_dir="$1"
    local task_id="$2"

    if handle_fix_worker_completion "$worker_dir" "$task_id"; then
        # Fix succeeded - attempt merge if needed
        if git_state_is "$worker_dir" "needs_merge"; then
            attempt_pr_merge "$worker_dir" "$task_id" "$RALPH_DIR" || true
        fi
    fi
}

# Handle fix worker timeout (callback for pool_cleanup_finished)
_handle_fix_worker_timeout() {
    local worker_dir="$1"
    local task_id="$2"
    handle_fix_worker_timeout "$worker_dir" "$task_id" "$FIX_WORKER_TIMEOUT"
}

# Handle resolve worker completion (callback for pool_cleanup_finished)
_handle_resolve_worker_completion() {
    local worker_dir="$1"
    local task_id="$2"

    if handle_resolve_worker_completion "$worker_dir" "$task_id"; then
        # Resolution succeeded - attempt merge if needed
        if git_state_is "$worker_dir" "needs_merge"; then
            attempt_pr_merge "$worker_dir" "$task_id" "$RALPH_DIR" || true
        fi

        # If this was a batch worker, immediately spawn the next one
        _spawn_next_batch_worker "$worker_dir" || true
    fi
}

# Spawn the next worker in a batch queue (for back-to-back execution)
#
# Called after a batch worker completes to immediately trigger the next one.
# Returns 0 if a worker was spawned, 1 if batch is complete/failed/no next worker.
_spawn_next_batch_worker() {
    local completed_worker_dir="$1"

    # Check if this was a batch worker
    source "$WIGGUM_HOME/lib/scheduler/batch-coordination.sh"
    batch_coord_has_worker_context "$completed_worker_dir" || return 1

    local batch_id
    batch_id=$(batch_coord_read_worker_context "$completed_worker_dir" "batch_id")
    [ -n "$batch_id" ] || return 1

    # Check batch status
    local status
    status=$(batch_coord_get_status "$batch_id" "$PROJECT_DIR")
    case "$status" in
        complete|failed) return 1 ;;
    esac

    # Find the next worker that should execute
    local next_task_id
    next_task_id=$(batch_coord_get_next_task "$batch_id" "$PROJECT_DIR")
    [ -n "$next_task_id" ] || return 1

    # Find worker directory for next task
    local next_worker_dir
    next_worker_dir=$(find_worker_by_task_id "$RALPH_DIR" "$next_task_id" 2>/dev/null)
    [ -n "$next_worker_dir" ] && [ -d "$next_worker_dir" ] || return 1

    # Verify it's this task's turn and it needs resolution
    git_state_is "$next_worker_dir" "needs_resolve" || return 1
    batch_coord_is_my_turn "$batch_id" "$next_task_id" "$PROJECT_DIR" || return 1

    # Check priority worker capacity
    local fix_count resolve_count total_priority
    fix_count=$(pool_count "fix")
    resolve_count=$(pool_count "resolve")
    total_priority=$((fix_count + resolve_count))
    if [ "$total_priority" -ge "$FIX_WORKER_LIMIT" ]; then
        log "Batch: deferring next worker - at capacity ($total_priority/$FIX_WORKER_LIMIT)"
        return 1
    fi

    log "Batch $batch_id: immediately spawning next worker for $next_task_id"

    # Use the existing spawn function from priority-workers.sh
    source "$WIGGUM_HOME/lib/scheduler/priority-workers.sh"
    _spawn_batch_resolve_worker "$RALPH_DIR" "$PROJECT_DIR" "$next_worker_dir" "$next_task_id"
    return $?
}

# Handle resolve worker timeout (callback for pool_cleanup_finished)
_handle_resolve_worker_timeout() {
    local worker_dir="$1"
    local task_id="$2"
    handle_resolve_worker_timeout "$worker_dir" "$task_id" "$RESOLVE_WORKER_TIMEOUT"
}

# Check if a pipeline step completed (has a result file) vs was interrupted
#
# A step that completed (even with FAIL) needs LLM analysis via resume-decide.
# A step that was interrupted mid-execution can be directly resumed (RETRY).
#
# Args:
#   worker_dir - Worker directory path
#   step_id    - Step ID to check
#
# Returns: 0 if step completed (has result), 1 if interrupted (no result)
_step_has_result() {
    local worker_dir="$1"
    local step_id="$2"

    [ -d "$worker_dir/results" ] || return 1

    local result_file
    result_file=$(find "$worker_dir/results" -name "*-${step_id}-result.json" 2>/dev/null | sort -r | head -1)
    [ -f "$result_file" ]
}

# Run resume-decide analysis for a single worker (blocking)
#
# Determines the resume action for a stopped worker:
#   - Interrupted steps (no result file): writes RETRY decision directly
#   - Completed steps: runs system.resume-decide agent for LLM analysis
#   - Handles COMPLETE/ABORT/DEFER decisions inline
#   - RETRY decisions are left for the unified queue to pick up
#
# Args:
#   worker_dir  - Worker directory path
#   task_id     - Task identifier
#   worker_type - Worker type (main, fix, resolve)
#
# Returns: 0 on success, 1 on failure
_resume_decide_for_worker() {
    local worker_dir="$1"
    local task_id="$2"
    local worker_type="$3"

    local worker_id
    worker_id=$(basename "$worker_dir")

    # Get current step from pipeline config
    local current_step=""
    if [ -f "$worker_dir/pipeline-config.json" ]; then
        current_step=$(jq -r '.current.step_id // ""' "$worker_dir/pipeline-config.json" 2>/dev/null)
    fi

    # Fast path: interrupted step (no result file) → direct RETRY
    if [ -n "$current_step" ] && ! _step_has_result "$worker_dir" "$current_step"; then
        jq -n --arg step "$current_step" '{
            decision: "RETRY",
            pipeline: null,
            resume_step: $step,
            reason: "Step interrupted, direct resume"
        }' > "$worker_dir/resume-decision.json"
        log "Direct RETRY decision for $task_id (interrupted at $current_step)"
        return 0
    fi

    # Slow path: need LLM analysis via resume-decide agent
    # Convert logs to readable conversations
    if [ -d "$worker_dir/logs" ]; then
        "$WIGGUM_HOME/lib/utils/log-converter.sh" --dir "$worker_dir" 2>/dev/null || true
    else
        mkdir -p "$worker_dir/conversations"
        if [ ! -f "$worker_dir/worker.log" ]; then
            echo "[$(date '+%Y-%m-%d %H:%M:%S')] Worker was interrupted before producing logs" > "$worker_dir/worker.log"
        fi
    fi

    # Run system.resume-decide agent
    source "$WIGGUM_HOME/lib/worker/agent-registry.sh"
    source "$WIGGUM_HOME/lib/core/agent-base.sh"
    run_agent "system.resume-decide" "$worker_dir" "$PROJECT_DIR" 0 1

    # Read decision from resume-decision.json
    if [ ! -f "$worker_dir/resume-decision.json" ]; then
        log_error "resume-decide agent did not produce a decision for $task_id"
        return 1
    fi

    local decision
    decision=$(jq -r '.decision // "ABORT"' "$worker_dir/resume-decision.json" 2>/dev/null)

    case "$decision" in
        RETRY)
            # Update resume state and leave decision file for unified queue
            local resume_pipeline resume_step_id
            resume_pipeline=$(jq -r '.pipeline // ""' "$worker_dir/resume-decision.json" 2>/dev/null)
            resume_step_id=$(jq -r '.resume_step // ""' "$worker_dir/resume-decision.json" 2>/dev/null)
            [ "$resume_pipeline" = "null" ] && resume_pipeline=""
            [ "$resume_step_id" = "null" ] && resume_step_id=""

            resume_state_increment "$worker_dir" "RETRY" "$resume_pipeline" "$resume_step_id" \
                "Resume-decide recommended RETRY"

            log "Resume-decide for $task_id: RETRY from '$resume_step_id'"
            ;;
        COMPLETE)
            resume_state_increment "$worker_dir" "COMPLETE" "" "" "Resume-decide finalized as COMPLETE"

            # Create PR if needed
            local pr_url=""
            if [ -f "$worker_dir/pr_url.txt" ]; then
                pr_url=$(cat "$worker_dir/pr_url.txt" 2>/dev/null)
            fi
            if [ -z "$pr_url" ] && [ -d "$worker_dir/workspace" ]; then
                source "$WIGGUM_HOME/lib/git/git-operations.sh"
                local branch_name
                branch_name=$(cd "$worker_dir/workspace" && git rev-parse --abbrev-ref HEAD 2>/dev/null || echo "")
                if [ -n "$branch_name" ] && [ "$branch_name" != "HEAD" ]; then
                    (cd "$worker_dir/workspace" && git push -u origin "$branch_name" 2>/dev/null) || true
                    local task_desc=""
                    if [ -f "$worker_dir/prd.md" ]; then
                        task_desc=$(head -5 "$worker_dir/prd.md" | sed -n 's/^# *//p' | head -1)
                    fi
                    task_desc="${task_desc:-Task $task_id}"
                    local pr_exit=0
                    git_create_pr "$branch_name" "$task_id" "$task_desc" "$worker_dir" "$PROJECT_DIR" || pr_exit=$?
                    if [ $pr_exit -eq 0 ] && [ -n "${GIT_PR_URL:-}" ]; then
                        echo "$GIT_PR_URL" > "$worker_dir/pr_url.txt"
                    fi
                fi
            fi

            # Mark task [P] and set terminal
            update_kanban_pending_approval "$RALPH_DIR/kanban.md" "$task_id" || true
            resume_state_set_terminal "$worker_dir" "Work complete, task marked [P]"

            # Remove decision file so it doesn't enter unified queue
            rm -f "$worker_dir/resume-decision.json"
            log "Task $task_id finalized as COMPLETE by resume-decide"
            activity_log "worker.resume_complete" "$worker_id" "$task_id"
            scheduler_mark_event
            ;;
        ABORT)
            resume_state_increment "$worker_dir" "ABORT" "" "" "Resume-decide: unrecoverable failure"
            update_kanban_failed "$RALPH_DIR/kanban.md" "$task_id" || true
            resume_state_set_terminal "$worker_dir" "Unrecoverable failure — aborted by resume-decide"
            rm -f "$worker_dir/resume-decision.json"
            log_error "Task $task_id marked FAILED by resume-decide (unrecoverable)"
            activity_log "worker.resume_abort" "$worker_id" "$task_id"
            scheduler_mark_event
            ;;
        DEFER)
            load_resume_config
            resume_state_increment "$worker_dir" "DEFER" "" "" "Resume-decide: deferred"
            resume_state_set_cooldown "$worker_dir" "$RESUME_COOLDOWN_SECONDS"
            rm -f "$worker_dir/resume-decision.json"
            log "Task $task_id deferred by resume-decide (cooldown: ${RESUME_COOLDOWN_SECONDS}s)"
            activity_log "worker.resume_defer" "$worker_id" "$task_id"
            ;;
        *)
            resume_state_increment "$worker_dir" "ABORT" "" "" "Unknown decision: $decision"
            update_kanban_failed "$RALPH_DIR/kanban.md" "$task_id" || true
            resume_state_set_terminal "$worker_dir" "Unknown decision '$decision' — treated as ABORT"
            rm -f "$worker_dir/resume-decision.json"
            log_error "Task $task_id: unknown resume decision '$decision' — treated as ABORT"
            activity_log "worker.resume_abort" "$worker_id" "$task_id" "decision=$decision"
            scheduler_mark_event
            ;;
    esac

    return 0
}

# Launch a resume-decide process in background (non-blocking)
#
# Runs _resume_decide_for_worker in a background subshell, tracks the PID
# in _PENDING_DECIDES, and writes decide.pid to the worker directory.
#
# Args:
#   worker_dir  - Worker directory path
#   task_id     - Task identifier
#   worker_type - Worker type (main, fix, resolve)
#
# Side effects:
#   - Writes decide.pid to worker directory
#   - Writes to _PENDING_DECIDES associative array
#   - Appends to $RALPH_DIR/orchestrator/decide-pending disk file
_launch_decide_background() {
    local worker_dir="$1"
    local task_id="$2"
    local worker_type="$3"

    # Export variables needed by the subprocess
    export _DECIDE_WIGGUM_HOME="$WIGGUM_HOME"
    export _DECIDE_WORKER_DIR="$worker_dir"
    export _DECIDE_TASK_ID="$task_id"
    export _DECIDE_WORKER_TYPE="$worker_type"
    export _DECIDE_PROJECT_DIR="$PROJECT_DIR"
    export _DECIDE_RALPH_DIR="$RALPH_DIR"

    # shellcheck disable=SC2016
    (
        set -euo pipefail
        export WIGGUM_HOME="$_DECIDE_WIGGUM_HOME"
        export PROJECT_DIR="$_DECIDE_PROJECT_DIR"
        export RALPH_DIR="$_DECIDE_RALPH_DIR"

        source "$WIGGUM_HOME/lib/core/defaults.sh"
        source "$WIGGUM_HOME/lib/core/logger.sh"
        source "$WIGGUM_HOME/lib/core/exit-codes.sh"
        source "$WIGGUM_HOME/lib/core/platform.sh"
        source "$WIGGUM_HOME/lib/core/resume-state.sh"
        source "$WIGGUM_HOME/lib/core/file-lock.sh"
        source "$WIGGUM_HOME/lib/tasks/task-parser.sh"
        source "$WIGGUM_HOME/lib/utils/activity-log.sh"
        source "$WIGGUM_HOME/lib/scheduler/scheduler.sh"
        source "$WIGGUM_HOME/lib/scheduler/orchestrator-functions.sh"
        activity_init "$PROJECT_DIR"

        mkdir -p "$RALPH_DIR/logs"
        export LOG_FILE="$RALPH_DIR/logs/resume.log"

        _exit_code=0
        _resume_decide_for_worker "$_DECIDE_WORKER_DIR" "$_DECIDE_TASK_ID" "$_DECIDE_WORKER_TYPE" || _exit_code=$?
        echo "$_exit_code" > "$_DECIDE_WORKER_DIR/.decide-exit-code"
        rm -f "$_DECIDE_WORKER_DIR/decide.pid"
        exit "$_exit_code"
    ) >> "$RALPH_DIR/logs/workers.log" 2>&1 &
    local decide_pid=$!

    # Write decide.pid so is_worker_running() sees this worker as busy
    echo "$decide_pid" > "$worker_dir/decide.pid"

    # Track decide process in-memory and persist to disk
    _PENDING_DECIDES[$decide_pid]="$worker_dir|$task_id|$worker_type"
    local _decide_pending="$RALPH_DIR/orchestrator/decide-pending"
    {
        flock -x 200
        echo "$decide_pid|$worker_dir|$task_id|$worker_type" >> "$_decide_pending"
    } 200>"$_decide_pending.lock"

    log "Resume-decide launched for $task_id (decide PID: $decide_pid)"
}

# Poll background resume-decide processes for completion
#
# Called each main-loop iteration. Checks if any resume-decide processes
# have finished. On completion:
#   - Exit 0: decision file written, unified queue handles RETRY next tick
#   - Non-zero: sets cooldown and increments resume state
#
# Side effects:
#   - Removes finished entries from _PENDING_DECIDES
#   - Ingests entries from decide-pending disk file
_poll_pending_decides() {
    # Ingest entries persisted to disk by _launch_decide_background
    local _decide_pending="$RALPH_DIR/orchestrator/decide-pending"
    if [ -s "$_decide_pending" ]; then
        local _dp_lines=""
        {
            flock -x 200
            _dp_lines=$(cat "$_decide_pending")
            : > "$_decide_pending"
        } 200>"$_decide_pending.lock"

        local _dp_line
        while IFS= read -r _dp_line; do
            [ -n "$_dp_line" ] || continue
            local _dp_pid _dp_wdir _dp_tid _dp_wtype
            IFS='|' read -r _dp_pid _dp_wdir _dp_tid _dp_wtype <<< "$_dp_line"
            # Skip if already tracked
            [ -z "${_PENDING_DECIDES[$_dp_pid]+x}" ] || continue
            _PENDING_DECIDES[$_dp_pid]="$_dp_wdir|$_dp_tid|$_dp_wtype"
        done <<< "$_dp_lines"
    fi

    [ ${#_PENDING_DECIDES[@]} -gt 0 ] || return 0

    local pid
    for pid in "${!_PENDING_DECIDES[@]}"; do
        # Still running? Skip.
        if kill -0 "$pid" 2>/dev/null; then
            continue
        fi

        # Parse metadata
        local entry="${_PENDING_DECIDES[$pid]}"
        unset '_PENDING_DECIDES[$pid]'
        local worker_dir task_id worker_type
        IFS='|' read -r worker_dir task_id worker_type <<< "$entry"

        # Clean up decide.pid if still present
        rm -f "$worker_dir/decide.pid"

        # Get exit code from file written by the decide wrapper
        local decide_exit=1
        if [ -f "$worker_dir/.decide-exit-code" ]; then
            decide_exit=$(cat "$worker_dir/.decide-exit-code")
            decide_exit="${decide_exit:-1}"
            rm -f "$worker_dir/.decide-exit-code"
        else
            # Fallback: try wait in case this was a direct child
            local _wait_rc=0
            wait "$pid" 2>/dev/null || _wait_rc=$?
            if [ "$_wait_rc" -ne 127 ]; then
                decide_exit="$_wait_rc"
            fi
        fi

        if [ "$decide_exit" -eq 0 ]; then
            # Decision written (or COMPLETE/ABORT/DEFER handled inline)
            log_debug "Resume-decide completed for $task_id (exit: 0)"
        else
            # Decide process itself crashed — set cooldown
            log_error "Resume-decide failed for $task_id (exit code: $decide_exit)"
            local _err_step=""
            if [ -f "$worker_dir/pipeline-config.json" ]; then
                _err_step=$(jq -r '.current.step_id // ""' "$worker_dir/pipeline-config.json" 2>/dev/null)
            fi
            resume_state_increment "$worker_dir" "ERROR" "" "${_err_step:-}" \
                "Resume-decide process failed (exit code: $decide_exit)"

            if resume_state_max_exceeded "$worker_dir"; then
                resume_state_set_terminal "$worker_dir" \
                    "Max resume attempts exceeded after decide errors (last exit: $decide_exit)"
                update_kanban_failed "$RALPH_DIR/kanban.md" "$task_id" || true
                log_error "Task $task_id marked FAILED — max resume attempts exceeded (decide exit: $decide_exit)"
                activity_log "worker.resume_failed" "$(basename "$worker_dir")" "$task_id" \
                    "exit_code=$decide_exit reason=max_attempts_exceeded"
                scheduler_mark_event
            else
                local _min_retry="${RESUME_MIN_RETRY_INTERVAL:-30}"
                resume_state_set_cooldown "$worker_dir" "$_min_retry"
                log_error "Resume-decide failed for $task_id (exit: $decide_exit) — cooldown ${_min_retry}s"
                activity_log "worker.resume_decide_error" "$(basename "$worker_dir")" "$task_id" \
                    "exit_code=$decide_exit cooldown=$_min_retry"
            fi

            # Clean up any partial decision file
            rm -f "$worker_dir/resume-decision.json"
        fi
    done
}

# Launch a resume worker synchronously (blocking until PID is obtained)
#
# Reads resume-decision.json for resume_step and pipeline, validates the
# step, launches the worker via setsid, waits for agent.pid, and marks
# the decision as consumed.
#
# Sets: SPAWNED_WORKER_PID, SPAWNED_WORKER_ID (for caller to use)
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier
#
# Returns: 0 on success, 1 on failure
_launch_resume_worker() {
    local worker_dir="$1"
    local task_id="$2"

    SPAWNED_WORKER_PID=""
    SPAWNED_WORKER_ID=""

    # Read decision
    if [ ! -f "$worker_dir/resume-decision.json" ]; then
        log_error "No resume-decision.json for $task_id"
        return 1
    fi

    local resume_step resume_pipeline
    resume_step=$(jq -r '.resume_step // "execution"' "$worker_dir/resume-decision.json" 2>/dev/null)
    resume_pipeline=$(jq -r '.pipeline // ""' "$worker_dir/resume-decision.json" 2>/dev/null)
    [ "$resume_step" = "null" ] && resume_step="execution"
    [ "$resume_pipeline" = "null" ] && resume_pipeline=""

    # Read report/instructions path from resume-decide result file
    local resume_instructions_path=""
    local resume_result_file
    source "$WIGGUM_HOME/lib/core/agent-result.sh"
    resume_result_file=$(agent_find_latest_result "$worker_dir" "system.resume-decide" 2>/dev/null || true)
    if [ -n "${resume_result_file:-}" ] && [ -f "$resume_result_file" ]; then
        resume_instructions_path=$(jq -r '.outputs.report_file // ""' "$resume_result_file" 2>/dev/null)
    fi

    # Validate pipeline step
    local effective_pipeline="${resume_pipeline:-${WIGGUM_PIPELINE:-}}"
    source "$WIGGUM_HOME/lib/pipeline/pipeline-loader.sh"
    local pipeline_file
    pipeline_file=$(pipeline_resolve "$PROJECT_DIR" "$task_id" "$effective_pipeline")
    if [ -n "$pipeline_file" ]; then
        pipeline_load "$pipeline_file" || {
            log_error "Failed to load pipeline config: $pipeline_file"
            return 1
        }
    else
        pipeline_load_builtin_defaults
    fi

    local step_idx
    step_idx=$(pipeline_find_step_index "$resume_step") || true
    if [ "$step_idx" = "-1" ]; then
        # Check if it's an inline step (e.g., "test-fix" inside test's on_result)
        local parent_step
        parent_step=$(pipeline_resolve_inline_to_parent "$resume_step")
        if [ -n "$parent_step" ]; then
            log "Mapping inline resume step '$resume_step' to parent step '$parent_step' for $task_id"
            resume_step="$parent_step"
            step_idx=$(pipeline_find_step_index "$resume_step") || true
        fi
    fi
    if [ "$step_idx" = "-1" ]; then
        log_error "Invalid resume step '$resume_step' for $task_id"
        return 1
    fi

    log "Launching resume worker for $task_id from step '$resume_step' (index $step_idx)"

    # Launch worker via setsid (same pattern as bin/wiggum-worker resume)
    export _WORKER_WIGGUM_HOME="$WIGGUM_HOME"
    export _WORKER_DIR="$worker_dir"
    export _WORKER_PROJECT_DIR="$PROJECT_DIR"
    export _WORKER_MAX_ITERATIONS="$MAX_ITERATIONS"
    export _WORKER_MAX_TURNS="$MAX_TURNS"
    export _WORKER_RESUME_STEP="$resume_step"
    export _WORKER_RESUME_INSTRUCTIONS="${resume_instructions_path:-}"

    # shellcheck disable=SC2016
    setsid bash -c '
        set -euo pipefail
        _log_ts() { echo "[$(date -Iseconds)] $*"; }
        _log_ts "INFO: Worker subprocess starting (two-phase resume)"
        _log_ts "INFO: WIGGUM_HOME=$_WORKER_WIGGUM_HOME"
        _log_ts "INFO: worker_dir=$_WORKER_DIR"
        _log_ts "INFO: resume_step=$_WORKER_RESUME_STEP"

        export WIGGUM_HOME="$_WORKER_WIGGUM_HOME"

        if ! source "$WIGGUM_HOME/lib/worker/agent-registry.sh" 2>&1; then
            _log_ts "ERROR: Failed to source agent-registry.sh"
            exit 1
        fi

        _log_ts "INFO: Running agent system.task-worker"
        _exit_code=0
        run_agent "system.task-worker" "$_WORKER_DIR" "$_WORKER_PROJECT_DIR" 30 "$_WORKER_MAX_ITERATIONS" "$_WORKER_MAX_TURNS" \
            "$_WORKER_RESUME_STEP" "$_WORKER_RESUME_INSTRUCTIONS" || _exit_code=$?
        if [ $_exit_code -ne 0 ]; then
            _log_ts "ERROR: run_agent failed with exit code $_exit_code"
            exit 1
        fi
    ' >> "$RALPH_DIR/logs/workers.log" 2>&1 &

    # Wait for agent.pid (with timeout)
    local wait_timeout="${PID_WAIT_TIMEOUT:-300}"
    if ! wait_for_worker_pid "$worker_dir" "$wait_timeout"; then
        log_error "Agent PID file not created for $task_id after resume launch"
        return 1
    fi

    SPAWNED_WORKER_PID=$(cat "$worker_dir/agent.pid")
    SPAWNED_WORKER_ID=$(basename "$worker_dir")

    # Mark decision as consumed so it doesn't re-enter the queue
    mv "$worker_dir/resume-decision.json" "$worker_dir/resume-decision.json.consumed"

    activity_log "worker.resumed" "$SPAWNED_WORKER_ID" "$task_id" \
        "pipeline_step=$resume_step pid=$SPAWNED_WORKER_PID"

    return 0
}

# Poll background resume processes for completion
#
# Called each main-loop iteration. Checks if any wiggum-worker resume processes
# launched by _schedule_resume_workers() have finished, and if so, registers
# the resulting worker into the pool.
_poll_pending_resumes() {
    # Ingest entries persisted to disk by _schedule_resume_workers.
    # This is the primary mechanism when the function runs inside a
    # periodic-service subshell (where in-memory updates are lost).
    local _resume_pending="$RALPH_DIR/orchestrator/resume-pending"
    if [ -s "$_resume_pending" ]; then
        local _rp_lines=""
        {
            flock -x 200
            _rp_lines=$(cat "$_resume_pending")
            : > "$_resume_pending"
        } 200>"$_resume_pending.lock"

        local _rp_line
        while IFS= read -r _rp_line; do
            [ -n "$_rp_line" ] || continue
            local _rp_pid _rp_wdir _rp_tid _rp_wtype
            IFS='|' read -r _rp_pid _rp_wdir _rp_tid _rp_wtype <<< "$_rp_line"
            # Skip if already tracked
            [ -z "${_PENDING_RESUMES[$_rp_pid]+x}" ] || continue
            _PENDING_RESUMES[$_rp_pid]="$_rp_wdir|$_rp_tid|$_rp_wtype"
        done <<< "$_rp_lines"
    fi

    [ ${#_PENDING_RESUMES[@]} -gt 0 ] || return 0

    local pid
    for pid in "${!_PENDING_RESUMES[@]}"; do
        # Still running? Skip.
        if kill -0 "$pid" 2>/dev/null; then
            continue
        fi

        # Parse metadata
        local entry="${_PENDING_RESUMES[$pid]}"
        unset '_PENDING_RESUMES[$pid]'
        local worker_dir task_id worker_type
        IFS='|' read -r worker_dir task_id worker_type <<< "$entry"

        # Get exit code from file written by the resume wrapper.
        # wait(2) cannot be used because the resume PID is not a direct
        # child when _schedule_resume_workers ran in a subshell.
        local resume_exit=1
        if [ -f "$worker_dir/.resume-exit-code" ]; then
            resume_exit=$(cat "$worker_dir/.resume-exit-code")
            resume_exit="${resume_exit:-1}"
            rm -f "$worker_dir/.resume-exit-code"
        else
            # Fallback: try wait in case this was a direct child
            local _wait_rc=0
            wait "$pid" 2>/dev/null || _wait_rc=$?
            if [ "$_wait_rc" -ne 127 ]; then
                resume_exit="$_wait_rc"
            fi
        fi

        case "$resume_exit" in
            0)
                # RETRY: worker subprocess launched — poll for PID
                if wait_for_worker_pid "$worker_dir" "$PID_WAIT_TIMEOUT"; then
                    local wpid
                    wpid=$(cat "$worker_dir/agent.pid")
                    pool_add "$wpid" "$worker_type" "$task_id"
                    scheduler_mark_event
                    activity_log "worker.resumed" "$(basename "$worker_dir")" "$task_id" \
                        "pipeline_step=$(cat "$worker_dir/current_step" 2>/dev/null || echo unknown) pid=$wpid type=$worker_type"
                    log "Resumed worker for $task_id (PID: $wpid, type: $worker_type)"
                else
                    log_error "Resume started but PID not created for $task_id"
                fi
                ;;
            "$EXIT_RESUME_COMPLETE")
                log "Task $task_id finalized as COMPLETE by resume-decide"
                activity_log "worker.resume_complete" "$(basename "$worker_dir")" "$task_id"
                scheduler_mark_event
                ;;
            "$EXIT_RESUME_ABORT")
                log_error "Task $task_id marked FAILED by resume-decide (unrecoverable)"
                activity_log "worker.resume_abort" "$(basename "$worker_dir")" "$task_id"
                scheduler_mark_event
                ;;
            "$EXIT_RESUME_DEFER")
                log "Task $task_id deferred by resume-decide (will retry after cooldown)"
                activity_log "worker.resume_defer" "$(basename "$worker_dir")" "$task_id"
                ;;
            *)
                # Track the failure so resume_state_max_exceeded() eventually stops retrying.
                # wiggum-worker resume only calls resume_state_increment after a successful
                # resume-decide decision, so crashes before that leave state untouched.
                local _err_step=""
                if [[ -f "$worker_dir/pipeline-config.json" ]]; then
                    _err_step=$(jq -r '.current.step_id // ""' "$worker_dir/pipeline-config.json" 2>/dev/null)
                fi
                resume_state_increment "$worker_dir" "ERROR" "" "${_err_step:-}" \
                    "Resume process failed (exit code: $resume_exit)"

                if resume_state_max_exceeded "$worker_dir"; then
                    resume_state_set_terminal "$worker_dir" \
                        "Max resume attempts exceeded after repeated errors (last exit: $resume_exit)"
                    update_kanban_failed "$RALPH_DIR/kanban.md" "$task_id" || true
                    log_error "Task $task_id marked FAILED — max resume attempts exceeded (exit code: $resume_exit)"
                    activity_log "worker.resume_failed" "$(basename "$worker_dir")" "$task_id" \
                        "exit_code=$resume_exit reason=max_attempts_exceeded"
                    scheduler_mark_event
                else
                    # Short cooldown to prevent same-tick retry; priority
                    # degradation is automatic via attempt_count in
                    # get_unified_work_queue().
                    local _min_retry="${RESUME_MIN_RETRY_INTERVAL:-30}"
                    resume_state_set_cooldown "$worker_dir" "$_min_retry"
                    log_error "Resume failed for $task_id (exit code: $resume_exit) — will retry after ${_min_retry}s cooldown"
                    activity_log "worker.resume_error" "$(basename "$worker_dir")" "$task_id" \
                        "exit_code=$resume_exit cooldown=$_min_retry"
                fi
                ;;
        esac
    done
}
