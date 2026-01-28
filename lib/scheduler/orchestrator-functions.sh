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

    # Call wiggum review sync and capture output
    local sync_output sync_exit=0
    sync_output=$("$WIGGUM_HOME/bin/wiggum-review" sync 2>&1) || sync_exit=$?

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
        local tasks_needing_fix="$ralph_dir/.tasks-needing-fix.txt"
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
    fi

    # Create planner worker directory
    local planner_worker_dir="$ralph_dir/workers/planner-$batch_id"
    mkdir -p "$planner_worker_dir/logs" "$planner_worker_dir/results"

    # Build batch file
    conflict_queue_build_batch_file "$ralph_dir" "$batch_id" "$planner_worker_dir/conflict-batch.json"

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

        # Run pre-worker checks
        if ! _orch_pre_worker_checks; then
            log_error "Pre-worker checks failed for $task_id - skipping"
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

    for ((attempt=1; attempt<=max_attempts; attempt++)); do
        if pull_output=$(git pull --ff-only origin main 2>&1); then
            break
        fi

        if echo "$pull_output" | grep -qi "CONFLICT"; then
            log_error "Git pull conflict detected: $pull_output"
            return 1
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
    start_output=$("$WIGGUM_HOME/bin/wiggum-start" "$task_id" \
        --max-iters "$max_iterations" --max-turns "$max_turns" \
        --agent-type "$agent_type" 2>&1) || start_exit_code=$?

    if [ "$start_exit_code" -ne 0 ]; then
        log_error "wiggum start failed (exit $start_exit_code): $start_output"
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
    return 0
}

# Display status on scheduling events
orch_display_status() {
    local ralph_dir="${RALPH_DIR:-}"
    local max_workers="${MAX_WORKERS:-4}"
    local aging_factor="${AGING_FACTOR:-7}"
    local plan_bonus="${PLAN_BONUS:-15000}"
    local dep_bonus="${DEP_BONUS_PER_TASK:-7000}"

    if [ "$SCHED_SCHEDULING_EVENT" = true ]; then
        local cyclic_ref
        cyclic_ref=$(scheduler_get_cyclic_tasks_ref)
        display_orchestrator_status \
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
    fi
}
