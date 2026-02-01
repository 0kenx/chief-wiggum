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
#   spawn_worker()                     - Spawn worker via wiggum-start
#   pre_worker_checks()               - Git pull and conflict checks
#   _handle_main_worker_completion()   - Main worker completion callback
#   _handle_fix_worker_completion()    - Fix worker completion callback
#   _handle_fix_worker_timeout()       - Fix worker timeout callback
#   _handle_resolve_worker_completion() - Resolve worker completion callback
#   _handle_resolve_worker_timeout()   - Resolve worker timeout callback
#   _spawn_next_batch_worker()         - Batch queue continuation
#   _schedule_resume_workers()         - Resume stopped WIP workers
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

# Wrapper for scheduler_decay_skip_counts
#
# Note: This function operates on in-memory state, so it only works
# when called in the same process as the scheduler. For the service
# scheduler, this is a no-op since each service runs in a subshell.
orch_decay_skip_counts() {
    # Skip counts are in-memory state - can only decay in main process
    # This is called in a subshell by the service runner, so it's a no-op
    # The main orchestrator should call scheduler_decay_skip_counts directly
    :
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
#   RALPH_DIR       - Required
#   PROJECT_DIR     - Required
#   PRIORITY_LIMIT  - Optional (default: 2)
orch_spawn_fix_workers() {
    local ralph_dir="${RALPH_DIR:-}"
    local project_dir="${PROJECT_DIR:-}"
    local limit="${PRIORITY_LIMIT:-2}"

    [ -n "$ralph_dir" ] || return 1
    [ -n "$project_dir" ] || return 1

    spawn_fix_workers "$ralph_dir" "$project_dir" "$limit"
}

# Wrapper for spawn_resolve_workers
#
# Globals:
#   RALPH_DIR       - Required
#   PROJECT_DIR     - Required
#   PRIORITY_LIMIT  - Optional (default: 2)
orch_spawn_resolve_workers() {
    local ralph_dir="${RALPH_DIR:-}"
    local project_dir="${PROJECT_DIR:-}"
    local limit="${PRIORITY_LIMIT:-2}"

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

# =============================================================================
# Worker Spawn and Lifecycle Functions
#
# Extracted from wiggum-run to keep the entry point minimal.
# These functions are called by service handlers in orchestrator-handlers.sh.
# =============================================================================

# Tracks background resume processes: pid → "worker_dir|task_id|worker_type"
declare -gA _PENDING_RESUMES=()

# Spawn a worker for a task using wiggum-start
# Sets: SPAWNED_WORKER_ID, SPAWNED_WORKER_PID (for caller to use)
spawn_worker() {
    local task_id="$1"

    # Use wiggum-start to start the worker, capturing exit code
    local start_output
    local start_exit_code
    start_output=$("$WIGGUM_HOME/bin/wiggum-start" "$task_id" \
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
                log_error "Use 'wiggum stop $task_id' or 'wiggum kill $task_id' first"
                return 1
            fi
            # Process not running - check if it's resumable
            if ! _is_terminal_failure "$existing_dir"; then
                # Worker is resumable - let resume logic handle it
                log "Worker for $task_id is resumable, skipping spawn"
                return 1
            fi
            # Terminal failure - clean up and retry fresh
            log "Cleaning up terminal-failure worker for $task_id: $(basename "$existing_dir")"
            rm -rf "$existing_dir"
            # Retry spawning - reset exit code first
            start_exit_code=0
            start_output=$("$WIGGUM_HOME/bin/wiggum-start" "$task_id" \
                --max-iters "$MAX_ITERATIONS" --max-turns "$MAX_TURNS" \
                --agent-type "$AGENT_TYPE" 2>&1) || start_exit_code=$?
        fi
    fi

    # Check if spawn succeeded
    if [ "$start_exit_code" -ne 0 ]; then
        log_error "wiggum start failed (exit $start_exit_code): $start_output"
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

    for ((attempt=1; attempt<=max_attempts; attempt++)); do
        if pull_output=$(git pull --ff-only origin main 2>&1); then
            break
        fi

        # Immediately fail on conflicts (non-transient)
        if echo "$pull_output" | grep -qi "CONFLICT"; then
            log_error "Git pull conflict detected: $pull_output"
            log_error "Cannot spawn new workers with unresolved conflicts"
            return 1
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

# Schedule resume of stopped workers
#
# Called once at startup to resume any stopped workers before starting new
# tasks. Delegates to `wiggum resume` which handles the logic of determining
# whether to use LLM analysis (step completed) or direct resume (interrupted).
#
# Skips workers that:
#   - Are terminal failures (last step + FAIL)
#   - Are at capacity (MAX_WORKERS)
#   - Have tasks no longer pending/in-progress
_schedule_resume_workers() {
    local resumable
    resumable=$(get_resumable_workers "$RALPH_DIR")
    [ -n "$resumable" ] || return 0

    log "Checking for stopped workers to resume..."

    local pending_main_count=0
    local pending_priority_count=0

    while read -r worker_dir task_id current_step worker_type; do
        [ -n "$worker_dir" ] || continue

        # Skip workers not applicable to the current run mode
        if [[ "$WIGGUM_RUN_MODE" != "default" && "$WIGGUM_RUN_MODE" != "resume-only" && "$worker_type" != "fix" && "$worker_type" != "resolve" ]]; then
            log_debug "Skipping resume of main worker $task_id ($WIGGUM_RUN_MODE mode)"
            continue
        fi
        if [[ "$WIGGUM_RUN_MODE" == "merge-only" && "$worker_type" == "fix" ]]; then
            log_debug "Skipping resume of fix worker $task_id (merge-only mode)"
            continue
        fi

        # Check capacity based on worker type
        if [[ "$worker_type" == "fix" || "$worker_type" == "resolve" ]]; then
            local fix_count resolve_count total_priority
            fix_count=$(pool_count "fix")
            resolve_count=$(pool_count "resolve")
            total_priority=$((fix_count + resolve_count + pending_priority_count))
            if [ "$total_priority" -ge "$FIX_WORKER_LIMIT" ]; then
                log "Priority workers at capacity ($total_priority/$FIX_WORKER_LIMIT) - deferring resume of $task_id"
                continue
            fi
        else
            local main_count
            main_count=$(pool_count "main")
            if [ "$((main_count + pending_main_count))" -ge "$MAX_WORKERS" ]; then
                log "At capacity ($((main_count + pending_main_count))/$MAX_WORKERS) - deferring remaining resumes"
                break
            fi
        fi

        # Check task is still pending or in-progress
        local task_status
        task_status=$(get_task_status "$RALPH_DIR/kanban.md" "$task_id")
        case "$task_status" in
            " "|"=") ;;
            *)
                log_debug "Skipping resume of $task_id - task status is '$task_status'"
                continue
                ;;
        esac

        # Mark as in-progress if pending
        if [ "$task_status" = " " ]; then
            if ! update_kanban_status "$RALPH_DIR/kanban.md" "$task_id" "="; then
                log_error "Failed to mark $task_id as in-progress"
                continue
            fi
        fi

        # Resume the worker via wiggum resume (handles interrupted vs completed logic)
        # Note: resume-decide may determine a different starting step based on analysis
        log "Initiating resume for $task_id (pipeline at: '$current_step')"
        local worker_id
        worker_id=$(basename "$worker_dir")

        # Run wiggum resume in background, passing through config
        # --quiet suppresses interactive output
        (
            cd "$PROJECT_DIR" && \
            "$WIGGUM_HOME/bin/wiggum-resume" "$worker_id" --quiet \
                --max-iters "$MAX_ITERATIONS" \
                --max-turns "$MAX_TURNS" \
                ${WIGGUM_PIPELINE:+--pipeline "$WIGGUM_PIPELINE"}
        ) >> "$RALPH_DIR/logs/workers.log" 2>&1 &
        local resume_pid=$!

        # Track resume process for non-blocking polling in main loop.
        # Resume runs LLM analysis (resume-decide) before launching the worker
        # subprocess, so we cannot wait synchronously — it blocks 30+ seconds
        # per worker and delays _main_loop startup.
        _PENDING_RESUMES[$resume_pid]="$worker_dir|$task_id|$worker_type"
        if [[ "$worker_type" == "fix" || "$worker_type" == "resolve" ]]; then
            ((++pending_priority_count))
        else
            ((++pending_main_count))
        fi
        log "Resume process launched for $task_id (resume PID: $resume_pid)"
    done <<< "$resumable"
}

# Poll background resume processes for completion
#
# Called each main-loop iteration. Checks if any wiggum-resume processes
# launched by _schedule_resume_workers() have finished, and if so, registers
# the resulting worker into the pool.
_poll_pending_resumes() {
    [ ${#_PENDING_RESUMES[@]} -gt 0 ] || return 0

    local pid
    for pid in "${!_PENDING_RESUMES[@]}"; do
        # Still running? Skip.
        if kill -0 "$pid" 2>/dev/null; then
            continue
        fi

        # Process finished — get exit code
        local resume_exit=0
        wait "$pid" 2>/dev/null || resume_exit=$?

        # Parse metadata
        local entry="${_PENDING_RESUMES[$pid]}"
        unset '_PENDING_RESUMES[$pid]'
        local worker_dir task_id worker_type
        IFS='|' read -r worker_dir task_id worker_type <<< "$entry"

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
                log_error "Resume failed for $task_id (exit code: $resume_exit)"
                ;;
        esac
    done
}
