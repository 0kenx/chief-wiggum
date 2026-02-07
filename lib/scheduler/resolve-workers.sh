#!/usr/bin/env bash
# resolve-workers.sh - Resolve worker spawning and lifecycle management
#
# Handles merge conflict resolution workers: spawning (simple and batch),
# completion, and timeout handling. Extracted from priority-workers.sh
# to reduce module size.
#
# State transitions are driven by the lifecycle engine (emit_event).
# See config/worker-lifecycle.json for the spec.
set -euo pipefail

[ -n "${_RESOLVE_WORKERS_LOADED:-}" ] && return 0
_RESOLVE_WORKERS_LOADED=1

# Source shared priority worker functions
source "$WIGGUM_HOME/lib/scheduler/priority-workers.sh"
source "$WIGGUM_HOME/lib/core/lifecycle-engine.sh"

# Auto-advance a batch past any tasks that are already merged
#
# Checks if the task at the batch's current position is already complete
# (marked [x] in kanban or has merged git state). If so, advances the batch
# and repeats until finding an incomplete task or reaching the end.
#
# This handles cases where PRs get merged through other code paths
# (e.g., PR merge optimizer) without updating batch coordination.
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
#   batch_id    - Batch identifier
#
# Returns: 0 if batch was advanced or already correct, 1 on error
_advance_batch_past_merged_tasks() {
    local ralph_dir="$1"
    local project_dir="$2"
    local batch_id="$3"

    local kanban_file="$ralph_dir/kanban.md"
    local coord_file
    coord_file=$(batch_coord_get_path "$batch_id" "$project_dir")

    [ -f "$coord_file" ] || return 1

    local max_advances=10  # Prevent infinite loop
    local advances=0

    while [ $advances -lt $max_advances ]; do
        local status current_pos total
        status=$(jq -r '.status' "$coord_file")

        # Stop if batch is already complete or failed
        if [ "$status" = "complete" ] || [ "$status" = "failed" ]; then
            return 0
        fi

        current_pos=$(jq -r '.current_position' "$coord_file")
        current_pos="${current_pos:-0}"
        total=$(jq -r '.total' "$coord_file")
        total="${total:-0}"

        # Stop if we've reached the end
        if [ "$current_pos" -ge "$total" ]; then
            return 0
        fi

        # Get the task at current position
        local current_task_id
        current_task_id=$(jq -r ".order[$current_pos]" "$coord_file")

        [ -n "$current_task_id" ] && [ "$current_task_id" != "null" ] || return 0

        # Check if task is already complete in kanban
        local task_status=""
        if [ -f "$kanban_file" ] && [[ "$current_task_id" =~ ^[A-Za-z]{2,10}-[0-9]{1,4}$ ]]; then
            task_status=$(grep -E "^\- \[.\] \*\*\[$current_task_id\]" "$kanban_file" 2>/dev/null | \
                sed 's/^- \[\(.\)\].*/\1/' | head -1 || echo "")
        fi

        # Also check git state of the worker
        local worker_dir git_state=""
        worker_dir=$(find_worker_by_task_id "$ralph_dir" "$current_task_id" 2>/dev/null)
        if [ -n "$worker_dir" ] && [ -d "$worker_dir" ]; then
            git_state=$(git_state_get "$worker_dir" 2>/dev/null || echo "")
        fi

        # If task is complete ([x] in kanban) or merged (git state), advance
        if [ "$task_status" = "x" ] || [ "$git_state" = "merged" ]; then
            log "Batch $batch_id: auto-advancing past already-merged $current_task_id"
            batch_coord_mark_complete "$batch_id" "$current_task_id" "$project_dir"

            # Clean up batch context from worker if present
            if [ -n "$worker_dir" ] && [ -f "$worker_dir/batch-context.json" ]; then
                rm -f "$worker_dir/batch-context.json"
            fi

            ((++advances))
        else
            # Current task is not merged, stop advancing
            return 0
        fi
    done

    log_warn "Batch $batch_id: hit max auto-advances ($max_advances)"
    return 0
}

# Check for workers needing conflict resolution and spawn resolver workers
#
# Scans worker directories for needs_resolve state and spawns resolver
# workers up to the combined priority worker limit.
#
# Workers are sorted by dependency depth (descending) so that tasks which
# unblock the most downstream work are resolved first.
#
# For workers with batch-context.json (part of multi-PR batch), uses the
# multi-pr-resolve pipeline for coordinated sequential resolution.
# For simple single-PR conflicts, uses the standard resolve command.
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
#   limit       - Maximum total priority workers (fix + resolve combined)
#
# Requires:
#   - pool_* functions from worker-pool.sh
#   - git_state_* functions from git-state.sh
#   - batch_coord_* functions from batch-coordination.sh
#   - get_dependency_depth from task-parser.sh
#   - WIGGUM_HOME environment variable
spawn_resolve_workers() {
    local ralph_dir="$1"
    local project_dir="$2"
    local limit="$3"

    [ -d "$ralph_dir/workers" ] || return 0

    local kanban_file="$ralph_dir/kanban.md"

    # Ensure lifecycle spec is loaded
    lifecycle_is_loaded || lifecycle_load

    # Sync file-based capacity tracking with actual pool state
    # This handles cases where workers exited unexpectedly
    _priority_capacity_sync "$ralph_dir"

    # First pass: detect and reset stuck "resolving" workers
    # A worker is stuck if it's in "resolving" state but has no running agent
    for worker_dir in "$ralph_dir/workers"/worker-*; do
        [ -d "$worker_dir" ] || continue
        local git_state
        git_state=$(git_state_get "$worker_dir" 2>/dev/null || echo "")
        if [ "$git_state" = "resolving" ]; then
            # Check if agent is actually running
            local agent_running=false
            if [ -f "$worker_dir/agent.pid" ]; then
                local pid
                pid=$(cat "$worker_dir/agent.pid" 2>/dev/null || true)
                if [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null; then
                    agent_running=true
                fi
            fi

            if [ "$agent_running" = false ]; then
                local worker_id task_id
                worker_id=$(basename "$worker_dir")
                task_id=$(get_task_id_from_worker "$worker_id")

                # Read current attempts (inc_merge_attempts effect runs during emit)
                local attempts
                attempts=$(git_state_get_merge_attempts "$worker_dir" 2>/dev/null || echo "0")
                attempts="${attempts:-0}"

                log "Resetting stuck resolver for $task_id (was in 'resolving' but no agent running, attempt $((attempts + 1))/${MAX_MERGE_ATTEMPTS:-3})"
                emit_event "$worker_dir" "resolve.stuck_reset" "resolve-workers.spawn_resolve_workers"
            fi
        fi
    done

    # Build list of workers needing resolution, sorted by dependency depth
    # Check both needs_resolve (single-PR) and needs_multi_resolve (multi-PR) states
    local -a worker_scores=()
    for worker_dir in "$ralph_dir/workers"/worker-*; do
        [ -d "$worker_dir" ] || continue
        local git_state
        git_state=$(git_state_get "$worker_dir" 2>/dev/null || echo "")
        if [[ "$git_state" != "needs_resolve" && "$git_state" != "needs_multi_resolve" ]]; then
            continue
        fi

        local worker_id
        worker_id=$(basename "$worker_dir")
        local task_id
        task_id=$(get_task_id_from_worker "$worker_id")

        local dep_depth=0
        if [ -f "$kanban_file" ]; then
            dep_depth=$(get_dependency_depth "$kanban_file" "$task_id" 2>/dev/null || echo "0")
        fi
        worker_scores+=("$dep_depth|$worker_dir")
    done

    # Sort by depth descending (higher depth first = unblocks more tasks)
    local -a sorted_workers=()
    while IFS= read -r entry; do
        [ -n "$entry" ] || continue
        sorted_workers+=("${entry#*|}")
    done < <(printf '%s\n' "${worker_scores[@]}" | sort -t'|' -k1 -rn)

    local worker_count=${#sorted_workers[@]}
    if [ "$worker_count" -gt 0 ]; then
        log "Found $worker_count worker(s) needing conflict resolution"
    fi

    for worker_dir in "${sorted_workers[@]}"; do
        [ -d "$worker_dir" ] || continue

        local worker_id
        worker_id=$(basename "$worker_dir")
        local task_id
        task_id=$(get_task_id_from_worker "$worker_id")

        # Escape hatch: check if max merge attempts exceeded
        # This prevents infinite resolve loops
        local merge_attempts
        merge_attempts=$(git_state_get_merge_attempts "$worker_dir" 2>/dev/null || echo "0")
        if [ "$merge_attempts" -ge "${MAX_MERGE_ATTEMPTS:-3}" ]; then
            log_error "Max merge attempts ($merge_attempts) reached for $task_id - marking as failed"
            emit_event "$worker_dir" "resolve.max_exceeded" "resolve-workers.spawn_resolve_workers"
            # Clean up batch context if present
            if [ -f "$worker_dir/batch-context.json" ]; then
                rm -f "$worker_dir/batch-context.json"
            fi
            continue
        fi

        # Guard: skip if agent is already running
        if [ -f "$worker_dir/agent.pid" ]; then
            local existing_pid
            existing_pid=$(cat "$worker_dir/agent.pid")
            if kill -0 "$existing_pid" 2>/dev/null; then
                log "Resolver already running for $task_id (PID: $existing_pid) - skipping"
                continue
            fi
        fi

        # Atomically reserve capacity slot (prevents race with fix-workers)
        if ! _priority_capacity_reserve "$ralph_dir" "$limit"; then
            log "Resolve worker limit reached ($limit) - deferring remaining resolves"
            break
        fi

        # Ensure workspace exists (reconstruct from PR branch if missing)
        if ! ensure_workspace_from_pr "$worker_dir" "$project_dir" "$task_id"; then
            # Reconstruction failed - check if PR is already merged (branch deleted)
            local merge_status
            merge_status=$(_verify_task_merged "$ralph_dir" "$task_id" "$worker_dir")

            if [ "$merge_status" = "merged" ]; then
                log "Resolver not needed for $task_id - PR is already merged (workspace cleaned up)"
                emit_event "$worker_dir" "resolve.already_merged" "resolve-workers.spawn_resolve_workers"
            else
                log_error "Cannot spawn resolver for $task_id: workspace missing and reconstruction failed (PR status: $merge_status)"
            fi
            _priority_capacity_release "$ralph_dir"
            continue
        fi

        # Check if this is a batch worker (part of multi-PR resolution)
        local spawn_result=0
        if batch_coord_has_worker_context "$worker_dir"; then
            local batch_id
            batch_id=$(batch_coord_read_worker_context "$worker_dir" "batch_id")

            # Auto-advance batch past any already-merged tasks (defense in depth)
            if [ -n "$batch_id" ]; then
                _advance_batch_past_merged_tasks "$ralph_dir" "$project_dir" "$batch_id"
            fi

            _spawn_batch_resolve_worker "$ralph_dir" "$project_dir" "$worker_dir" "$task_id" || spawn_result=$?
        else
            _spawn_simple_resolve_worker "$ralph_dir" "$project_dir" "$worker_dir" "$task_id" || spawn_result=$?
        fi

        # If spawn failed, release the capacity slot
        if [ "$spawn_result" -ne 0 ]; then
            _priority_capacity_release "$ralph_dir"
        fi
    done
}

# Spawn a simple (non-batch) resolver worker
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
#   worker_dir  - Worker directory path
#   task_id     - Task identifier
_spawn_simple_resolve_worker() {
    local ralph_dir="$1"
    local project_dir="$2"
    local worker_dir="$3"
    local task_id="$4"

    # Defense-in-depth: verify workspace exists (should have been ensured by caller)
    if [ ! -d "$worker_dir/workspace" ]; then
        # Try one more reconstruction attempt
        if ! ensure_workspace_from_pr "$worker_dir" "$project_dir" "$task_id"; then
            log_warn "Skipping simple resolver for $task_id - workspace missing and reconstruction failed"
            local current_state
            current_state=$(git_state_get "$worker_dir" 2>/dev/null || echo "unknown")
            if [[ "$current_state" != "merged" && "$current_state" != "failed" ]]; then
                emit_event "$worker_dir" "resolve.fail" "resolve-workers._spawn_simple_resolve_worker" \
                    '{"error":"Workspace missing and reconstruction failed"}'
            fi
            return 1
        fi
    fi

    # Transition state: needs_resolve → resolving
    emit_event "$worker_dir" "resolve.started" "resolve-workers._spawn_simple_resolve_worker"

    log "Spawning simple conflict resolver for $task_id..."

    # Call wiggum pr resolve asynchronously
    (
        cd "$project_dir" || exit 1
        "$WIGGUM_HOME/bin/wiggum-pr" resolve "$task_id" 2>&1 | \
            sed "s/^/  [resolve-$task_id] /"
    ) &
    local shell_pid=$!

    # Track the shell wrapper immediately
    pool_add "$shell_pid" "resolve" "$task_id"
    log "Simple resolver spawned for $task_id (PID: $shell_pid)"

    # Also wait briefly for agent.pid - if Claude agent spawns separately, re-track with correct PID
    (
        sleep 2
        if [ -f "$worker_dir/agent.pid" ]; then
            local agent_pid
            agent_pid=$(cat "$worker_dir/agent.pid" 2>/dev/null || true)
            if [ -n "$agent_pid" ] && [ "$agent_pid" != "$shell_pid" ] && kill -0 "$agent_pid" 2>/dev/null; then
                # Agent PID differs from shell PID - update tracking
                # Note: This is async, so we can't directly update pool here
                # Instead, orphan detection will pick it up
                :
            fi
        fi
    ) &
}

# Spawn a batch resolver worker using multi-pr-resolve pipeline
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
#   worker_dir  - Worker directory path
#   task_id     - Task identifier
_spawn_batch_resolve_worker() {
    local ralph_dir="$1"
    local project_dir="$2"
    local worker_dir="$3"
    local task_id="$4"

    # Defense-in-depth: verify workspace exists (should have been ensured by caller)
    # If missing, try reconstruction before giving up
    if [ ! -d "$worker_dir/workspace" ]; then
        # Try to reconstruct from PR branch
        if ensure_workspace_from_pr "$worker_dir" "$project_dir" "$task_id"; then
            log "Reconstructed workspace for batch resolver $task_id"
        else
            # Reconstruction failed - verify actual merge status
            local merge_status
            merge_status=$(_verify_task_merged "$(dirname "$(dirname "$worker_dir")")" "$task_id" "$worker_dir")

            if [ "$merge_status" = "merged" ]; then
                log "Skipping batch resolver for $task_id - PR is merged (workspace cleaned up)"
            else
                log_warn "Skipping batch resolver for $task_id - workspace missing and reconstruction failed (PR status: $merge_status)"
            fi

            # Clean up stale batch context
            rm -f "$worker_dir/batch-context.json"

            # Update git state based on actual status
            local current_state
            current_state=$(git_state_get "$worker_dir" 2>/dev/null || echo "unknown")
            if [[ "$current_state" != "merged" && "$current_state" != "failed" ]]; then
                if [ "$merge_status" = "merged" ]; then
                    emit_event "$worker_dir" "resolve.already_merged" "resolve-workers._spawn_batch_resolve_worker"
                else
                    local data_json
                    data_json=$(jq -n --arg e "Workspace missing and reconstruction failed, PR status: $merge_status" '{error: $e}')
                    emit_event "$worker_dir" "resolve.fail" "resolve-workers._spawn_batch_resolve_worker" "$data_json"
                fi
            fi
            return 1
        fi
    fi

    local batch_id position total
    batch_id=$(batch_coord_read_worker_context "$worker_dir" "batch_id")
    position=$(batch_coord_read_worker_context "$worker_dir" "position")
    total=$(batch_coord_read_worker_context "$worker_dir" "total")

    # Only spawn if it's this worker's turn in the batch sequence
    local turn_result=0
    batch_coord_is_my_turn "$batch_id" "$task_id" "$project_dir" || turn_result=$?
    if [ "$turn_result" -ne 0 ]; then
        if [ "$turn_result" -eq 2 ]; then
            log "Batch resolver for $task_id: batch $batch_id failed - cleaning up"
            rm -f "$worker_dir/batch-context.json"
            # Demote from batch to simple resolve for re-evaluation
            emit_event "$worker_dir" "resolve.batch_failed" "resolve-workers._spawn_batch_resolve_worker"
        else
            log "Batch resolver for $task_id: waiting for turn (batch: $batch_id, position $((position + 1)) of $total)"
        fi
        return 1  # Not my turn - return 1 so capacity is released
    fi

    # Transition state: needs_resolve/needs_multi_resolve → resolving
    emit_event "$worker_dir" "resolve.started" "resolve-workers._spawn_batch_resolve_worker"

    log "Spawning batch resolver for $task_id (batch: $batch_id, position $((position + 1)) of $total)..."

    # Launch worker using multi-pr-resolve pipeline
    # wiggum-worker start daemonizes the worker - we track via agent.pid
    (
        cd "$project_dir" || exit 1
        "$WIGGUM_HOME/bin/wiggum-worker" start --worker-dir "$worker_dir" \
            --pipeline multi-pr-resolve --quiet 2>&1 | \
            sed "s/^/  [batch-resolve-$task_id] /"
    )

    # Wait for agent.pid to appear and use that for tracking
    local wait_count=0
    while [ ! -f "$worker_dir/agent.pid" ] && [ $wait_count -lt 30 ]; do
        sleep 0.1
        ((++wait_count))
    done

    if [ -f "$worker_dir/agent.pid" ]; then
        local resolver_pid
        resolver_pid=$(cat "$worker_dir/agent.pid")
        pool_add "$resolver_pid" "resolve" "$task_id"
        log "Batch resolver spawned for $task_id (PID: $resolver_pid)"
    else
        log_error "Failed to get worker PID for $task_id - agent.pid not created"
        emit_event "$worker_dir" "resolve.fail" "resolve-workers._spawn_batch_resolve_worker" \
            '{"error":"Worker failed to start"}'
        return 1
    fi
}

# Create workspaces for orphaned PRs (PRs with comments but no local workspace)
# Then queue them for fix processing
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
#
# Requires:
#   - git_state_* functions
#   - setup_worktree_from_branch from worktree-helpers.sh
#   - WIGGUM_HOME environment variable
create_orphan_pr_workspaces() {
    local ralph_dir="$1"
    local project_dir="$2"

    local orphan_file="$ralph_dir/orchestrator/prs-needing-workspace.jsonl"

    if [ ! -s "$orphan_file" ]; then
        return 0
    fi

    # Ensure lifecycle spec is loaded
    lifecycle_is_loaded || lifecycle_load

    log "Processing orphaned PRs needing workspace creation..."

    local processed=()
    while IFS= read -r line; do
        [ -z "$line" ] && continue

        local task_id pr_number branch
        task_id=$(echo "$line" | jq -r '.task_id')
        pr_number=$(echo "$line" | jq -r '.pr_number')
        branch=$(echo "$line" | jq -r '.branch')

        if [ -z "$task_id" ] || [ "$task_id" = "null" ]; then
            continue
        fi

        # Skip tasks with terminal kanban status — no point creating a fix
        # worker for a task that's already complete, failed, or not planned
        local kanban_file="$ralph_dir/kanban.md"
        if [ -f "$kanban_file" ]; then
            local _task_status
            _task_status=$(get_task_status "$kanban_file" "$task_id" 2>/dev/null) || true
            case "${_task_status:-}" in
                x|"*"|N)
                    log "  $task_id: skipping (kanban status [$_task_status])"
                    processed+=("$task_id")
                    continue
                    ;;
            esac
        fi

        # Check if workspace already exists now (might have been created elsewhere)
        local existing_worker
        existing_worker=$(find_worker_by_task_id "$ralph_dir" "$task_id" 2>/dev/null)
        if [ -n "$existing_worker" ] && [ -d "$existing_worker/workspace" ]; then
            log "  $task_id: workspace already exists, skipping"
            processed+=("$task_id")
            continue
        fi

        # Create worker directory
        local timestamp worker_id worker_dir
        timestamp=$(epoch_now)
        worker_id="worker-${task_id}-fix-${timestamp}"
        worker_dir="$ralph_dir/workers/$worker_id"

        mkdir -p "$worker_dir"
        log "  $task_id: Creating workspace from branch $branch"

        # Create worktree from PR branch
        if ! setup_worktree_from_branch "$project_dir" "$worker_dir" "$branch"; then
            log_error "  $task_id: Failed to create workspace from branch $branch"
            safe_path "$worker_dir" "worker_dir" || continue
            rm -rf "$worker_dir"
            continue
        fi

        # Record PR info
        git_state_set_pr "$worker_dir" "$pr_number"

        # Sync comments from review directory if they exist
        local review_comments="$ralph_dir/review/${task_id}-comments.json"
        if [ -f "$review_comments" ]; then
            cp "$review_comments" "$worker_dir/${task_id}-comments.json"
        fi

        # Also fetch fresh comments
        "$WIGGUM_HOME/bin/wiggum-pr" comments "$task_id" sync 2>/dev/null || true

        # Queue for fix processing and transition state: none → needs_fix
        echo "$task_id" >> "$ralph_dir/orchestrator/tasks-needing-fix.txt"
        emit_event "$worker_dir" "fix.detected" "resolve-workers.create_orphan_pr_workspaces"

        log "  $task_id: Workspace created, queued for fix"
        processed+=("$task_id")
    done < "$orphan_file"

    # Remove processed entries from orphan file
    if [ ${#processed[@]} -gt 0 ]; then
        local temp_file
        temp_file=$(mktemp "${orphan_file}.XXXXXX")
        while IFS= read -r line; do
            local task_id
            task_id=$(echo "$line" | jq -r '.task_id')
            local skip=false
            for p in "${processed[@]}"; do
                if [ "$task_id" = "$p" ]; then
                    skip=true
                    break
                fi
            done
            if [ "$skip" = false ]; then
                echo "$line" >> "$temp_file"
            fi
        done < "$orphan_file"
        mv "$temp_file" "$orphan_file"
    fi
}

# Handle resolver completion - check result and transition state
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier
#
# Returns: 0 on success, 1 on failure
handle_resolve_worker_completion() {
    local worker_dir="$1"
    local task_id="$2"

    # Ensure lifecycle spec is loaded
    lifecycle_is_loaded || lifecycle_load

    # Check if conflicts are resolved
    local workspace="$worker_dir/workspace"
    if [ ! -d "$workspace" ]; then
        emit_event "$worker_dir" "resolve.fail" "resolve-workers.handle_resolve_worker_completion" \
            '{"error":"Workspace not found"}'
        return 1
    fi

    local remaining_conflicts
    remaining_conflicts=$(git -C "$workspace" diff --name-only --diff-filter=U 2>/dev/null || true)

    if [ -z "$remaining_conflicts" ]; then
        # Commit and push the resolution before transitioning state
        log "Conflicts resolved for $task_id - committing resolution..."

        local ralph_dir project_dir
        ralph_dir=$(dirname "$(dirname "$worker_dir")")
        project_dir=$(dirname "$ralph_dir")

        (
            cd "$project_dir" || exit 1
            "$WIGGUM_HOME/bin/wiggum-pr" commit "$task_id" 2>&1 | sed "s/^/  [commit-$task_id] /"
            "$WIGGUM_HOME/bin/wiggum-pr" push "$task_id" 2>&1 | sed "s/^/  [push-$task_id] /"
        )

        # Transition: resolving → resolved (chain) → needs_merge + rm_conflict_queue effect
        emit_event "$worker_dir" "resolve.succeeded" "resolve-workers.handle_resolve_worker_completion"
        return 0
    else
        local count
        count=$(echo "$remaining_conflicts" | wc -l)
        local data_json
        data_json=$(jq -n --arg e "$count files still have conflicts" '{error: $e}')
        emit_event "$worker_dir" "resolve.fail" "resolve-workers.handle_resolve_worker_completion" "$data_json"
        log_error "Resolver failed for $task_id - $count files still have conflicts"
        return 1
    fi
}

# Handle timeout for resolve workers
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier
#   timeout    - Timeout value in seconds (for logging)
handle_resolve_worker_timeout() {
    local worker_dir="$1"
    local task_id="$2"
    local timeout="${3:-3600}"

    # Ensure lifecycle spec is loaded
    lifecycle_is_loaded || lifecycle_load

    # Don't clobber terminal/completed states - the resolve may have finished
    # before the timeout fired
    local current_state
    current_state=$(git_state_get "$worker_dir")
    case "$current_state" in
        resolved|needs_merge|merged)
            log "Resolve worker for $task_id timed out but state is already $current_state - treating as completed"
            return 0
            ;;
    esac

    log_warn "Resolve worker for $task_id timed out after ${timeout}s - resetting to needs_resolve for retry"
    emit_event "$worker_dir" "resolve.timeout" "resolve-workers.handle_resolve_worker_timeout"
}
