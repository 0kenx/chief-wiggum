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

source "$WIGGUM_HOME/lib/core/safe-path.sh"
source "$WIGGUM_HOME/lib/core/gh-error.sh"
source "$WIGGUM_HOME/lib/core/atomic-write.sh"
source "$WIGGUM_HOME/lib/github/issue-sync.sh"
source "$WIGGUM_HOME/lib/scheduler/orch-resume-decide.sh"

# These functions depend on scheduler module components
# They should be sourced after the scheduler modules are loaded

# Run periodic sync to update PR statuses and detect new comments
#
# This is a standalone version of the sync logic that can be called
# by the service scheduler.
# Network errors skip the current cycle (will retry next cycle).
#
# Globals:
#   RALPH_DIR   - Required
#   PROJECT_DIR - Required
#
# Returns: 0 on success (or network error - skips cycle), 1 on permanent failure
orch_run_periodic_sync() {
    local ralph_dir="${RALPH_DIR:-}"
    local project_dir="${PROJECT_DIR:-}"

    [ -n "$ralph_dir" ] || { log_error "RALPH_DIR not set"; return 1; }

    # Call wiggum pr sync and capture output
    local sync_output sync_exit=0
    sync_output=$("$WIGGUM_HOME/bin/wiggum-pr" sync 2>&1) || sync_exit=$?

    if [ $sync_exit -ne 0 ]; then
        # Check for network errors - skip cycle gracefully
        if gh_is_network_error "$sync_exit" "$sync_output"; then
            log_warn "PR sync: skipping cycle due to network error (will retry later)"
            return 0
        fi
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
                        # Use lifecycle engine for state transition
                        lifecycle_is_loaded || lifecycle_load
                        emit_event "$worker_dir" "planner.completed" "orchestrator-functions._orch_check_completed_planners" || \
                            log_warn "planner.completed event failed for $task_id (state=$current_state)"
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
    safe_path "$ralph_dir" "ralph_dir" || return 1

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
        safe_path "$planner_worker_dir" "planner_worker_dir" || return 1
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

    # Default completion callback (idempotent — skips if worker already self-completed)
    _fix_completion() {
        local worker_dir="$1"
        local task_id="$2"

        # Skip if worker already self-completed via worker-complete.sh
        local current_state
        current_state=$(git_state_get "$worker_dir" 2>/dev/null || echo "")
        case "$current_state" in
            fix_completed|needs_merge|merged|failed)
                log_debug "Fix completion: $task_id already at $current_state - skipping handler"
                # Still attempt merge if applicable
                if [[ "$current_state" == "needs_merge" ]]; then
                    attempt_pr_merge "$worker_dir" "$task_id" "$RALPH_DIR" || true
                fi
                return 0
                ;;
        esac

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
    safe_path "$ralph_dir" "ralph_dir" || return 1

    # Tick scheduler to get latest task lists
    if [[ "${WIGGUM_TASK_SOURCE_MODE:-local}" != "local" ]]; then
        scheduler_tick_distributed
    else
        scheduler_tick
    fi

    # Check rate limit before spawning
    if rate_limit_check "$ralph_dir"; then
        log "Rate limit threshold reached - deferring spawning"
        return 0
    fi

    # Pre-flight: pull latest main once per cycle (with exponential backoff cooldown)
    local _pwc_state="$ralph_dir/orchestrator/pre-worker-state.json"
    if [ -f "$_pwc_state" ]; then
        local _pwc_until
        _pwc_until=$(jq -r '.cooldown_until // 0' "$_pwc_state" 2>/dev/null)
        _pwc_until="${_pwc_until:-0}"
        if [ "$_pwc_until" -gt "$(epoch_now)" ]; then
            log_debug "Pre-worker checks in cooldown (until $_pwc_until)"
            return 0
        fi
    fi

    if ! _orch_pre_worker_checks; then
        # Track consecutive failures with exponential backoff
        local _pwc_failures=0
        if [ -f "$_pwc_state" ]; then
            _pwc_failures=$(jq -r '.consecutive_failures // 0' "$_pwc_state" 2>/dev/null)
            _pwc_failures="${_pwc_failures:-0}"
        fi
        ((_pwc_failures++)) || true
        local _pwc_max_cooldown="${WIGGUM_PRE_WORKER_MAX_COOLDOWN:-300}"
        # Exponential: 30, 60, 120, 240, 300 (capped)
        local _pwc_cooldown=$((30 * (1 << (_pwc_failures - 1))))
        [ "$_pwc_cooldown" -gt "$_pwc_max_cooldown" ] && _pwc_cooldown="$_pwc_max_cooldown"
        local _pwc_until=$(( $(epoch_now) + _pwc_cooldown ))
        mkdir -p "$ralph_dir/orchestrator"
        atomic_write "$_pwc_state" jq -n --argjson f "$_pwc_failures" --argjson u "$_pwc_until" \
            '{consecutive_failures:$f, cooldown_until:$u}'
        log_error "Pre-worker checks failed ($_pwc_failures consecutive) — cooldown ${_pwc_cooldown}s"
        return 0
    fi
    # Reset on success
    [ -f "$_pwc_state" ] && rm -f "$_pwc_state"

    # Spawn workers for ready tasks
    for task_id in $SCHED_READY_TASKS; do
        # Check if we can spawn this task (includes distributed claimability check)
        if ! scheduler_can_spawn_task_distributed "$task_id" "$max_workers"; then
            case "$SCHED_SKIP_REASON" in
                at_capacity) break ;;
                claimed_by_other)
                    log_debug "Skipping $task_id - claimed by another server"
                    ;;
                file_conflict|cyclic_dependency|skip_count) continue ;;
            esac
            continue
        fi

        local task_priority
        task_priority=$(get_task_priority "$ralph_dir/kanban.md" "$task_id")

        log "Assigning $task_id (Priority: ${task_priority:-MEDIUM}) to new worker"

        # Claim task in distributed mode (assign issue + server label)
        if ! scheduler_claim_task "$task_id"; then
            log_debug "Failed to claim $task_id - claimed by another server"
            continue
        fi

        # Spawn worker - worker.spawned event inside cmd-start.sh handles kanban update
        if ! _orch_spawn_worker "$task_id" "$max_iterations" "$max_turns" "$agent_type"; then
            log_error "Failed to spawn worker for $task_id"
            # Find worker_dir if it was partially created
            local failed_worker_dir
            failed_worker_dir=$(find_worker_by_task_id "$ralph_dir" "$task_id" 2>/dev/null) || true
            if [ -n "$failed_worker_dir" ] && [ -d "$failed_worker_dir" ]; then
                # Use lifecycle engine for consistent state transition
                lifecycle_is_loaded || lifecycle_load
                emit_event "$failed_worker_dir" "resume.abort" "orchestrator-functions.spawn_failed" || {
                    # Fallback if no worker_dir or emit_event fails
                    update_kanban_status "$ralph_dir/kanban.md" "$task_id" "*" || true
                    github_issue_sync_task_status "$ralph_dir" "$task_id" "*" || true
                }
            else
                # No worker_dir created yet - direct kanban update is acceptable
                update_kanban_status "$ralph_dir/kanban.md" "$task_id" "*" || true
                github_issue_sync_task_status "$ralph_dir" "$task_id" "*" || true
            fi
            scheduler_release_task "$task_id"
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
    # Pull latest changes from default branch with retry
    local default_branch
    default_branch=$(get_default_branch)
    local pull_output
    local max_attempts=3
    local delays=(2 4)
    local dirty_reset_done=false

    for ((attempt=1; attempt<=max_attempts; attempt++)); do
        if pull_output=$(git pull --ff-only origin "$default_branch" 2>&1); then
            break
        fi

        # Immediately fail on merge conflicts (requires manual resolution)
        if echo "$pull_output" | grep -qi "CONFLICT"; then
            log_error "Git pull conflict detected: $pull_output"
            return 1
        fi

        # Dirty/untracked working directory - reset the blocking files and retry once
        if echo "$pull_output" | grep -qiE "(local changes|untracked.*files).*overwritten"; then
            if [ "$dirty_reset_done" = false ]; then
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
            else
                # Targeted reset insufficient — hard reset to match remote
                log_warn "Dirty reset insufficient — performing hard reset of $default_branch"
                git reset --hard "origin/$default_branch" 2>/dev/null || true
                git clean -fd 2>/dev/null || true
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

# Recover workers stuck in "failed" git-state
#
# Scans for failed workers and re-enters them into the fix/resolve cycle
# if recovery is possible. Called before spawning fix/resolve workers so
# recovered workers become candidates for the next cycle.
#
# Globals:
#   RALPH_DIR - Required
orch_recover_failed_workers() {
    local ralph_dir="${RALPH_DIR:-}"
    [ -n "$ralph_dir" ] || return 1

    recover_failed_workers "$ralph_dir"
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

    # Recover failed workers before spawning fix workers so they
    # become candidates for the fix/resolve cycle
    recover_failed_workers "$ralph_dir"

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
# Network errors skip the current cycle (will retry next cycle).
#
# Globals:
#   RALPH_DIR   - Required
#   WIGGUM_HOME - Required
#
# Returns: 0 on success (or network error - skips cycle), 1 on permanent failure
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
        # Network errors: skip cycle gracefully (return 0 so service continues)
        if [ "${GH_LAST_WAS_NETWORK_ERROR:-false}" = true ]; then
            log_debug "GitHub issue sync: skipping cycle due to network error"
            return 0
        fi
        log_error "GitHub issue sync failed"
        return 1
    fi

    return 0
}

# Sync plan files (.ralph/plans/) with GitHub issue comments
#
# Runs bidirectional sync for all tracked plans. Uses the same
# github.issue_sync.enabled gate as issue sync.
# Network errors skip the current cycle (will retry next cycle).
#
# Returns: 0 on success (or network error - skips cycle), 1 on failure
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
        # Network errors are already logged with "will retry later" message
        # Don't log additional warnings for them
        if [ "${GH_LAST_WAS_NETWORK_ERROR:-false}" != true ]; then
            log_warn "GitHub plan sync completed with conflicts"
        fi
    fi

    return 0
}

# =============================================================================
# Failure Recovery
# =============================================================================

# Run failure recovery for failed workers
#
# Scans for workers with [*] status in kanban that are eligible for recovery.
# Runs the failure-recovery pipeline to analyze and cleanup, then triggers
# normal resume flow.
#
# Globals:
#   RALPH_DIR   - Required
#   PROJECT_DIR - Required
#   WIGGUM_HOME - Required
#
# Returns: 0 on success, 1 on failure
orch_failure_recovery() {
    local ralph_dir="${RALPH_DIR:-}"
    local project_dir="${PROJECT_DIR:-}"
    local limit="${RECOVERY_WORKER_LIMIT:-2}"

    [ -n "$ralph_dir" ] || { log_error "RALPH_DIR not set"; return 1; }
    [ -n "$project_dir" ] || { log_error "PROJECT_DIR not set"; return 1; }

    # Phase 1: Poll completed recovery processes
    _poll_pending_recoveries

    # Phase 2: Find eligible failed workers and launch recovery agents
    local kanban_file="$ralph_dir/kanban.md"
    [ -f "$kanban_file" ] || return 0
    [ -d "$ralph_dir/workers" ] || return 0

    local failed_tasks
    failed_tasks=$(get_failed_tasks "$kanban_file")
    [ -n "$failed_tasks" ] || return 0

    local launched=0

    while IFS= read -r task_id; do
        [ -n "$task_id" ] || continue

        # Respect limit
        local active_count
        active_count=$(_count_active_recoveries)
        [ "$active_count" -lt "$limit" ] || break

        # Find newest worker directory (consistent with find_worker_by_task_id)
        local worker_dir=""
        worker_dir=$(find_worker_by_task_id "$ralph_dir" "$task_id")
        [ -n "$worker_dir" ] || continue
        [ -d "$worker_dir/workspace" ] || continue

        # Skip terminal workers (already exhausted retry attempts)
        resume_state_is_terminal "$worker_dir" && continue

        # Skip running workers
        is_worker_running "$worker_dir" && continue

        # Handle recovery-in-progress markers
        if [ -f "$worker_dir/recovery-in-progress" ]; then
            # Check if a tracked recovery PID is still running for this worker
            if _is_recovery_tracked_and_running "$worker_dir"; then
                continue
            fi
            # No running PID tracked — marker is orphaned (crashed/killed process)
            rm -f "$worker_dir/recovery-in-progress"
            log_warn "Removed orphaned recovery-in-progress marker for $(basename "$worker_dir")"
        fi

        # Skip if recovery already completed this failure cycle
        # (PASS from a previous cycle is cleared by the resume path, so if
        # the task is [*] again and recovery-attempted says PASS, the resume
        # failed — allow re-recovery)
        if [ -f "$worker_dir/recovery-attempted" ]; then
            local prev_result
            prev_result=$(cat "$worker_dir/recovery-attempted" 2>/dev/null)
            if [ "$prev_result" = "PASS" ]; then
                # Task is [*] despite PASS — previous resume must have failed.
                # Clear stale marker to allow re-recovery.
                rm -f "$worker_dir/recovery-attempted"
                log_warn "Cleared stale recovery-attempted PASS for $(basename "$worker_dir") (task still failed)"
            fi
        fi

        # Launch recovery agent in background
        _launch_recovery_worker "$worker_dir" "$task_id"
        ((++launched))
    done <<< "$failed_tasks"

    if [ "$launched" -gt 0 ]; then
        log "failure-recovery: launched $launched recovery agent(s)"
    fi

    return 0
}

# Launch a recovery agent in the background for a failed worker
#
# Same pattern as _launch_resume_worker: setsid subprocess that calls
# run_agent with the failure-recovery pipeline, output to workers.log.
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task ID
_launch_recovery_worker() {
    local worker_dir="$1"
    local task_id="$2"

    log "failure-recovery: launching recovery for $task_id"

    # Mark recovery in progress
    epoch_now > "$worker_dir/recovery-in-progress"

    # Save original pipeline name
    if [ -f "$worker_dir/pipeline-config.json" ]; then
        local orig_pipeline
        orig_pipeline=$(jq -r '.pipeline.name // "default"' "$worker_dir/pipeline-config.json" 2>/dev/null) || true
        orig_pipeline="${orig_pipeline:-default}"
        echo "$orig_pipeline" > "$worker_dir/original-pipeline.txt"
    fi

    # Export vars for setsid subprocess
    export _RECOVERY_WIGGUM_HOME="$WIGGUM_HOME"
    export _RECOVERY_WORKER_DIR="$worker_dir"
    export _RECOVERY_PROJECT_DIR="$PROJECT_DIR"
    export _RECOVERY_RALPH_DIR="$RALPH_DIR"
    export _RECOVERY_TASK_ID="$task_id"

    # shellcheck disable=SC2016
    setsid bash -c '
        set -euo pipefail
        _log_ts() { echo "[$(date -Iseconds)] $*"; }
        _log_ts "INFO: Recovery subprocess starting for $_RECOVERY_TASK_ID"

        export WIGGUM_HOME="$_RECOVERY_WIGGUM_HOME"
        export WIGGUM_PIPELINE="failure-recovery"

        worker_dir="$_RECOVERY_WORKER_DIR"
        task_id="$_RECOVERY_TASK_ID"

        if ! source "$WIGGUM_HOME/lib/worker/agent-registry.sh" 2>&1; then
            _log_ts "ERROR: Failed to source agent-registry.sh"
            exit 1
        fi

        _log_ts "INFO: Running failure-recovery pipeline for $task_id"
        _exit_code=0
        run_agent "system.task-worker" "$worker_dir" "$_RECOVERY_PROJECT_DIR" 30 3 50 \
            "failure-summarize" "" || _exit_code=$?

        # Remove in-progress marker and stale agent.pid (the PID belongs to
        # this setsid subprocess which is still alive, so wiggum-worker resume
        # would see it as "already running" and refuse to launch)
        rm -f "$worker_dir/recovery-in-progress"
        rm -f "$worker_dir/agent.pid"

        # Check recovery result
        recovery_result="FAIL"
        result_file=$(find "$worker_dir/results" -name "*-failure-resolve-result.json" 2>/dev/null | sort -r | head -1 || true)
        if [ -n "$result_file" ] && [ -f "$result_file" ]; then
            recovery_result=$(jq -r ".outputs.gate_result // \"FAIL\"" "$result_file" 2>/dev/null)
        fi

        echo "$recovery_result" > "$worker_dir/recovery-attempted"

        if [ "$recovery_result" = "PASS" ]; then
            _log_ts "INFO: Recovery completed successfully for $task_id"

            # Post failure summary to GitHub if issue sync is configured
            report_file=$(find "$worker_dir/reports" -name "*failure-summarizer*" 2>/dev/null | sort -r | head -1 || true)
            if [ -n "$report_file" ] && [ -f "$report_file" ]; then
                export RALPH_DIR="$_RECOVERY_RALPH_DIR"
                source "$WIGGUM_HOME/lib/github/issue-writer.sh" 2>/dev/null || true
                if type github_issue_post_failure_summary &>/dev/null; then
                    summary_content=$(cat "$report_file")
                    github_issue_post_failure_summary "$RALPH_DIR" "$task_id" "$summary_content" 2>/dev/null || true
                fi
            fi

            # Trigger resume flow so the task gets re-queued
            _log_ts "INFO: Triggering resume for $task_id..."
            unset WIGGUM_PIPELINE  # clear recovery pipeline for resume
            _resume_exit=0
            "$WIGGUM_HOME/bin/wiggum-worker" resume "$task_id" --quiet 2>&1 || _resume_exit=$?
            if [ "$_resume_exit" -ne 0 ]; then
                _log_ts "WARN: Resume trigger failed for $task_id (exit $_resume_exit)"
            fi
        else
            _log_ts "WARN: Recovery returned $recovery_result for $task_id (exit $_exit_code)"
        fi
    ' >> "$RALPH_DIR/logs/workers.log" 2>&1 &

    local bg_pid=$!

    # Clean up exported vars
    unset _RECOVERY_WIGGUM_HOME _RECOVERY_WORKER_DIR _RECOVERY_PROJECT_DIR _RECOVERY_RALPH_DIR _RECOVERY_TASK_ID

    # Track the background process via file (persists across bridge invocations)
    mkdir -p "$RALPH_DIR/orchestrator"
    local pending_file="$RALPH_DIR/orchestrator/recovery-pending"
    {
        flock -x 200
        echo "$bg_pid|$worker_dir|$task_id" >> "$pending_file"
    } 200>"$pending_file.lock"

    activity_log "worker.recovery_started" "$(basename "$worker_dir")" "$task_id" "pid=$bg_pid"
}

# Poll completed recovery background processes
#
# Reads recovery-pending file, checks which processes have finished,
# and cleans up.
_poll_pending_recoveries() {
    local pending_file="$RALPH_DIR/orchestrator/recovery-pending"
    [ -s "$pending_file" ] || return 0

    local lines=""
    {
        flock -x 200
        lines=$(cat "$pending_file")
        : > "$pending_file"
    } 200>"$pending_file.lock"

    local remaining=""
    while IFS='|' read -r pid worker_dir task_id; do
        [ -n "$pid" ] || continue
        if kill -0 "$pid" 2>/dev/null; then
            # Still running — keep tracking
            remaining+="$pid|$worker_dir|$task_id"$'\n'
        else
            # Completed — check result
            local result="UNKNOWN"
            if [ -f "$worker_dir/recovery-attempted" ]; then
                result=$(cat "$worker_dir/recovery-attempted" 2>/dev/null)
            fi
            log "failure-recovery: $task_id completed (result=$result)"
            activity_log "worker.recovery_completed" "$(basename "$worker_dir")" "$task_id" "result=$result"
        fi
    done <<< "$lines"

    # Write back still-running processes
    if [ -n "$remaining" ]; then
        {
            flock -x 200
            echo -n "$remaining" >> "$pending_file"
        } 200>"$pending_file.lock"
    fi
}

# Count active recovery processes (running PIDs in recovery-pending)
_count_active_recoveries() {
    local pending_file="$RALPH_DIR/orchestrator/recovery-pending"
    local count=0

    if [ -s "$pending_file" ]; then
        while IFS='|' read -r pid _rest; do
            [ -n "$pid" ] || continue
            kill -0 "$pid" 2>/dev/null && ((++count))
        done < "$pending_file"
    fi

    echo "$count"
}

# Check if a recovery process is tracked and running for a worker directory
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: 0 if tracked PID is running, 1 otherwise
_is_recovery_tracked_and_running() {
    local worker_dir="$1"
    local pending_file="$RALPH_DIR/orchestrator/recovery-pending"
    [ -s "$pending_file" ] || return 1

    while IFS='|' read -r pid tracked_dir _rest; do
        [ -n "$pid" ] || continue
        [ "$tracked_dir" = "$worker_dir" ] || continue
        kill -0 "$pid" 2>/dev/null && return 0
    done < "$pending_file"
    return 1
}

# =============================================================================
# GitHub Resume Trigger
# =============================================================================

# Process wiggum:resume-request labels on failed tasks
#
# Scans for failed tasks that have the wiggum:resume-request label on their
# linked GitHub issue. Resets worker state and re-queues for normal resume
# flow. The resume-decide service (30s) picks up the worker.
#
# Globals:
#   RALPH_DIR   - Required
#   PROJECT_DIR - Required
#   WIGGUM_HOME - Required
#
# Returns: 0 on success
orch_github_resume_trigger() {
    local ralph_dir="${RALPH_DIR:-}"
    local project_dir="${PROJECT_DIR:-}"

    [ -n "$ralph_dir" ] || { log_error "RALPH_DIR not set"; return 1; }
    [ -n "$project_dir" ] || { log_error "PROJECT_DIR not set"; return 1; }

    local kanban_file="$ralph_dir/kanban.md"
    [ -f "$kanban_file" ] || return 0
    [ -d "$ralph_dir/workers" ] || return 0
    [ -f "$ralph_dir/github-sync-state.json" ] || return 0

    local failed_tasks
    failed_tasks=$(get_failed_tasks "$kanban_file")
    [ -n "$failed_tasks" ] || return 0

    source "$WIGGUM_HOME/lib/core/resume-state.sh"
    source "$WIGGUM_HOME/lib/github/issue-writer.sh"
    source "$WIGGUM_HOME/lib/github/issue-state.sh"
    source "$WIGGUM_HOME/lib/github/issue-config.sh"

    # Load config for allowed user IDs (if not already loaded)
    [ -n "${GITHUB_SYNC_ALLOWED_USER_IDS:-}" ] || load_github_sync_config

    while IFS= read -r task_id; do
        [ -n "$task_id" ] || continue

        # Look up issue number from sync state
        local entry
        entry=$(github_sync_state_get_task "$ralph_dir" "$task_id")
        [ "$entry" != "null" ] || continue

        local issue_number
        issue_number=$(echo "$entry" | jq -r '.issue_number')
        [ -n "$issue_number" ] && [ "$issue_number" != "null" ] || continue

        # Fetch labels and check for wiggum:resume-request
        local labels label_exit=0
        labels=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh issue view "$issue_number" \
            --json labels --jq '.labels[].name' 2>/dev/null) || label_exit=$?
        if [ "$label_exit" -ne 0 ]; then
            continue
        fi
        echo "$labels" | grep -qx "wiggum:resume-request" || continue

        # Check who added the resume-request label (whitelist guard)
        if [ -n "${GITHUB_SYNC_ALLOWED_USER_IDS:-}" ]; then
            local actor_info=""
            actor_info=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh api \
                "repos/{owner}/{repo}/issues/${issue_number}/events" \
                --jq '[.[] | select(.event == "labeled" and .label.name == "wiggum:resume-request")] | last | "\(.actor.id // "")|\(.actor.login // "unknown")"' \
                2>/dev/null) || true

            local actor_id="${actor_info%%|*}"
            local actor_login="${actor_info#*|}"

            if [ -z "$actor_id" ] || ! github_sync_is_author_allowed "$actor_id"; then
                log_warn "github-resume-trigger: rejecting resume request for $task_id — user ${actor_login:-unknown} (id: ${actor_id:-unknown}) not in allowed_user_ids"
                github_issue_remove_label "$issue_number" "wiggum:resume-request" || true
                github_issue_post_comment "$issue_number" \
                    "wiggum: resume request rejected — user not authorized. Contact a project maintainer." || true
                continue
            fi
        fi

        # Skip if failure-recovery is running for this worker
        local worker_dir=""
        worker_dir=$(find_worker_by_task_id "$ralph_dir" "$task_id")
        [ -n "$worker_dir" ] || continue

        if [ -f "$worker_dir/recovery-in-progress" ]; then
            if _is_recovery_tracked_and_running "$worker_dir"; then
                log_debug "github-resume-trigger: skipping $task_id - recovery in progress"
                continue
            fi
        fi

        # Skip if workspace doesn't exist
        [ -d "$worker_dir/workspace" ] || continue

        # Skip if worker is still running
        is_worker_running "$worker_dir" && continue

        log "github-resume-trigger: processing resume request for $task_id (#$issue_number)"

        # Reset worker state — all retry counters get a fresh start
        resume_state_reset_for_user_retry "$worker_dir"

        # Reset worker state via lifecycle engine (resets all counters atomically)
        if [ -f "$worker_dir/git-state.json" ]; then
            lifecycle_is_loaded || lifecycle_load
            if ! emit_event "$worker_dir" "user.github_retry" "github-resume-trigger"; then
                # Fallback: direct counter reset for non-failed states
                source "$WIGGUM_HOME/lib/worker/git-state.sh"
                git_state_reset_merge_attempts "$worker_dir"
                git_state_reset_recovery_attempts "$worker_dir"
                git_state_set_error "$worker_dir" ""
            fi
        fi

        rm -f "$worker_dir/resume-decision.json" \
              "$worker_dir/resume-decision.json.consumed" \
              "$worker_dir/recovery-attempted"
        find "$worker_dir" -maxdepth 1 -name 'stop-reason-*' -delete

        # Ensure kanban is [=] via lifecycle engine
        # (user.resume already handled failed→needs_merge, resume.retry handles kanban)
        if ! emit_event "$worker_dir" "resume.retry" "github-resume-trigger.kanban_safety"; then
            # Fallback for workers where lifecycle transition isn't applicable
            update_kanban_status "$ralph_dir/kanban.md" "$task_id" "=" || true
        fi

        # Update GitHub issue: reopen, swap labels, remove resume-request
        github_issue_reopen "$issue_number" || true
        github_issue_set_status_label "$issue_number" "wiggum:in-progress" "wiggum:failed" || true
        github_issue_remove_label "$issue_number" "wiggum:resume-request" || true

        # Update PR labels to match (remove wiggum:failed, add wiggum:in-progress)
        github_pr_sync_task_status "$ralph_dir" "$task_id" "=" "*" || true

        # Invalidate issue cache — the issue was just reopened so the cache
        # (which only holds open issues) is stale and claim would fail lookup.
        task_source_invalidate_cache

        # Warm the reopened issue into the cache immediately — the full cache
        # refresh may not see it yet due to GitHub API eventual consistency.
        task_source_warm_issue "$issue_number" || true

        # Re-claim task in distributed mode (server label removed during shutdown)
        scheduler_claim_task "$task_id" || true

        # Post confirmation comment
        github_issue_post_comment "$issue_number" \
            "wiggum: resume requested — task re-queued for execution." || true

        # Update sync state
        local updated_entry
        updated_entry=$(echo "$entry" | jq \
            --arg status "=" \
            --arg state "open" \
            '.last_synced_status = $status | .last_remote_state = $state')
        github_sync_state_set_task "$ralph_dir" "$task_id" "$updated_entry"

        activity_log "worker.github_resume_triggered" "$(basename "$worker_dir")" "$task_id" \
            "issue=$issue_number"
        scheduler_mark_event

    done <<< "$failed_tasks"

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
            safe_path "$existing_dir" "existing_dir" || return 1
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
    # Git pull time guard: skip if pulled recently (WIGGUM_GIT_PULL_INTERVAL=0 restores old behavior)
    local pull_interval="${WIGGUM_GIT_PULL_INTERVAL:-20}"
    if [ "$pull_interval" -gt 0 ] && [ "${_SCHED_LAST_GIT_PULL:-0}" -gt 0 ]; then
        local _now
        _now=$(epoch_now)
        if (( _now - _SCHED_LAST_GIT_PULL < pull_interval )); then
            log_debug "Skipping git pull (interval ${pull_interval}s not elapsed)"
            return 0
        fi
    fi

    # Pull latest changes from default branch with retry
    local default_branch
    default_branch=$(get_default_branch)
    log "Pulling latest changes from origin/$default_branch..."

    local pull_output
    local max_attempts=3
    local delays=(2 4)
    local dirty_reset_done=false

    for ((attempt=1; attempt<=max_attempts; attempt++)); do
        if pull_output=$(git pull --ff-only origin "$default_branch" 2>&1); then
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

    # Update git pull timestamp on success
    _SCHED_LAST_GIT_PULL=$(epoch_now)

    # Check for conflicts with active worktrees (use cached dirs if available)
    local _worker_dirs="${_SCHED_WORKER_DIRS:-}"
    if [ -z "$_worker_dirs" ] && [ -d "$RALPH_DIR/workers" ]; then
        local _dir
        for _dir in "$RALPH_DIR/workers"/worker-*; do
            [ -d "$_dir" ] || continue
            _worker_dirs+="$_dir"$'\n'
        done
        _worker_dirs="${_worker_dirs%$'\n'}"
    fi

    if [ -n "$_worker_dirs" ]; then
        while IFS= read -r worker_dir; do
            [ -n "$worker_dir" ] || continue
            [ -d "$worker_dir/workspace" ] || continue

            local workspace="$worker_dir/workspace"
            if [ -d "$workspace/.git" ] || [ -f "$workspace/.git" ]; then
                # Check if worktree has conflicts with main
                if git -C "$workspace" diff --name-only "origin/$default_branch" 2>/dev/null | \
                   xargs -I {} git -C "$workspace" diff --check "origin/$default_branch" -- {} 2>&1 | \
                   grep -q "conflict"; then
                    log_error "Conflict detected in $(basename "$worker_dir")"
                    return 1
                fi
            fi
        done <<< "$_worker_dirs"
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

    # Release distributed claim if task reached a terminal failure state
    # (successful tasks stay claimed as [P] until PR merge releases them)
    local _task_status
    _task_status=$(get_task_status "$RALPH_DIR/kanban.md" "$task_id" 2>/dev/null) || true
    if [ "$_task_status" = "*" ]; then
        scheduler_release_task "$task_id"
    fi
}

# Handle fix worker completion (callback for pool_cleanup_finished)
# Idempotent: skips if worker already self-completed via worker-complete.sh
_handle_fix_worker_completion() {
    local worker_dir="$1"
    local task_id="$2"

    # Skip if worker already self-completed
    local current_state
    current_state=$(git_state_get "$worker_dir" 2>/dev/null || echo "")
    case "$current_state" in
        fix_completed|needs_merge|merged|failed)
            log_debug "Fix completion: $task_id already at $current_state - skipping handler"
            if [[ "$current_state" == "needs_merge" ]]; then
                attempt_pr_merge "$worker_dir" "$task_id" "$RALPH_DIR" || true
            fi
            return 0
            ;;
    esac

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

    # Use the existing spawn function from resolve-workers.sh
    source "$WIGGUM_HOME/lib/scheduler/resolve-workers.sh"
    _spawn_batch_resolve_worker "$RALPH_DIR" "$PROJECT_DIR" "$next_worker_dir" "$next_task_id"
    return $?
}

# Handle resolve worker timeout (callback for pool_cleanup_finished)
_handle_resolve_worker_timeout() {
    local worker_dir="$1"
    local task_id="$2"
    handle_resolve_worker_timeout "$worker_dir" "$task_id" "$RESOLVE_WORKER_TIMEOUT"
}

