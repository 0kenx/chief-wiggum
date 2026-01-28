#!/usr/bin/env bash
# priority-workers.sh - Fix and resolve worker management
#
# Consolidates check_and_spawn_fixes() and check_and_spawn_resolvers() into
# a unified interface for spawning and managing priority workers (fix/resolve).
# These workers handle PR comment fixes and merge conflict resolution.
set -euo pipefail

[ -n "${_PRIORITY_WORKERS_LOADED:-}" ] && return 0
_PRIORITY_WORKERS_LOADED=1

# Source dependencies
source "$WIGGUM_HOME/lib/scheduler/worker-pool.sh"
source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"
source "$WIGGUM_HOME/lib/worker/git-state.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"
source "$WIGGUM_HOME/lib/scheduler/conflict-queue.sh"
source "$WIGGUM_HOME/lib/scheduler/batch-coordination.sh"
source "$WIGGUM_HOME/lib/tasks/task-parser.sh"
source "$WIGGUM_HOME/lib/git/worktree-helpers.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"

# =============================================================================
# Priority Worker Capacity Management
#
# fix-workers and resolve-workers services share a capacity limit. Since these
# services run in subshells (via service scheduler), they can race when checking
# capacity. This uses file-based locking to ensure atomic capacity reservation.
# =============================================================================

# File storing current priority worker count (fix + resolve)
# Format: single integer on one line
_PRIORITY_CAPACITY_FILE=""

# Initialize capacity tracking for a ralph directory
#
# Args:
#   ralph_dir - Ralph directory path
_priority_capacity_init() {
    local ralph_dir="$1"
    _PRIORITY_CAPACITY_FILE="$ralph_dir/.priority-worker-count"

    # Create file if it doesn't exist
    [ -f "$_PRIORITY_CAPACITY_FILE" ] || echo "0" > "$_PRIORITY_CAPACITY_FILE"
}

# Atomically try to reserve capacity for a priority worker
#
# Args:
#   ralph_dir - Ralph directory path
#   limit     - Maximum total priority workers allowed
#
# Returns: 0 if reservation succeeded, 1 if at capacity
_priority_capacity_reserve() {
    local ralph_dir="$1"
    local limit="$2"

    _priority_capacity_init "$ralph_dir"

    # Use file locking to atomically check and increment
    (
        flock -x -w 5 200 || exit 1

        local current
        current=$(cat "$_PRIORITY_CAPACITY_FILE" 2>/dev/null || echo "0")
        current=${current:-0}

        if (( current < limit )); then
            echo "$((current + 1))" > "$_PRIORITY_CAPACITY_FILE"
            exit 0  # Success - reserved
        fi

        exit 1  # At capacity
    ) 200>"${_PRIORITY_CAPACITY_FILE}.lock"

    return $?
}

# Release a priority worker capacity slot
#
# Args:
#   ralph_dir - Ralph directory path
_priority_capacity_release() {
    local ralph_dir="$1"

    _priority_capacity_init "$ralph_dir"

    # Use file locking to atomically decrement
    (
        flock -x -w 5 200 || exit 1

        local current
        current=$(cat "$_PRIORITY_CAPACITY_FILE" 2>/dev/null || echo "0")
        current=${current:-0}

        if (( current > 0 )); then
            echo "$((current - 1))" > "$_PRIORITY_CAPACITY_FILE"
        fi
    ) 200>"${_PRIORITY_CAPACITY_FILE}.lock"
}

# Sync file-based capacity with actual running priority workers
#
# Called at the start of spawn functions to ensure capacity file reflects reality.
# Counts workers by scanning directories for running agent.pid files with
# git_state = fixing, needs_fix, resolving, or needs_resolve.
# This handles cases where workers exit unexpectedly without releasing.
#
# Args:
#   ralph_dir - Ralph directory path
_priority_capacity_sync() {
    local ralph_dir="$1"

    _priority_capacity_init "$ralph_dir"

    [ -d "$ralph_dir/workers" ] || return 0

    # Use file locking for atomic update
    (
        flock -x -w 5 200 || exit 1

        # Count running priority workers by scanning directories
        local actual_count=0
        for worker_dir in "$ralph_dir/workers"/worker-*; do
            [ -d "$worker_dir" ] || continue

            # Check if this is a priority worker (fix or resolve)
            local state=""
            if [ -f "$worker_dir/git-state.json" ]; then
                state=$(jq -r '.state // ""' "$worker_dir/git-state.json" 2>/dev/null || echo "")
            fi

            # Count only active fix/resolve workers
            case "$state" in
                fixing|resolving)
                    # Check if agent.pid exists and process is running
                    if [ -f "$worker_dir/agent.pid" ]; then
                        local pid
                        pid=$(cat "$worker_dir/agent.pid" 2>/dev/null || echo "")
                        if [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null; then
                            ((++actual_count))
                        fi
                    fi
                    ;;
            esac
        done

        echo "$actual_count" > "$_PRIORITY_CAPACITY_FILE"
    ) 200>"${_PRIORITY_CAPACITY_FILE}.lock"
}

# Reconstruct workspace from PR branch if missing
#
# When a worker directory exists but the workspace is missing (e.g., cleaned up,
# edited remotely), this function reconstructs it from the PR branch.
#
# Args:
#   worker_dir  - Worker directory path
#   project_dir - Project directory path
#   task_id     - Task identifier (for logging)
#
# Returns: 0 if workspace exists or was reconstructed, 1 on failure
ensure_workspace_from_pr() {
    local worker_dir="$1"
    local project_dir="$2"
    local task_id="$3"

    local workspace="$worker_dir/workspace"

    # If workspace exists, nothing to do
    if [ -d "$workspace" ]; then
        return 0
    fi

    log "Workspace missing for $task_id, attempting reconstruction from PR..."

    # Get PR number from git-state.json
    local pr_number
    pr_number=$(git_state_get_pr "$worker_dir")

    if [ -z "$pr_number" ] || [ "$pr_number" = "null" ]; then
        log_error "Cannot reconstruct workspace for $task_id: no PR number in git-state.json"
        return 1
    fi

    # Get branch name from PR using gh CLI
    local branch
    branch=$(gh pr view "$pr_number" --json headRefName -q '.headRefName' 2>/dev/null || true)

    if [ -z "$branch" ]; then
        log_error "Cannot reconstruct workspace for $task_id: failed to get branch from PR #$pr_number"
        return 1
    fi

    log "Reconstructing workspace for $task_id from branch $branch (PR #$pr_number)"

    # Use setup_worktree_from_branch to create the workspace
    if ! setup_worktree_from_branch "$project_dir" "$worker_dir" "$branch"; then
        log_error "Failed to reconstruct workspace for $task_id from branch $branch"
        return 1
    fi

    log "Successfully reconstructed workspace for $task_id"
    return 0
}

# Verify if a task's PR is actually merged
#
# Checks kanban status and optionally GitHub PR state to determine
# if a task is truly merged (not just assumed).
#
# Args:
#   ralph_dir  - Ralph directory path
#   task_id    - Task identifier
#   worker_dir - Worker directory path (optional, for PR number lookup)
#
# Returns: 0 if merged, 1 if not merged or unknown
# Outputs: "merged", "open", "closed", or "unknown"
_verify_task_merged() {
    local ralph_dir="$1"
    local task_id="$2"
    local worker_dir="${3:-}"

    local kanban_file="$ralph_dir/kanban.md"

    # First check: kanban status
    if [ -f "$kanban_file" ]; then
        local task_status
        task_status=$(grep -E "^\- \[.\] \*\*\[$task_id\]" "$kanban_file" 2>/dev/null | \
            sed 's/^- \[\(.\)\].*/\1/' | head -1 || echo "")
        if [ "$task_status" = "x" ]; then
            echo "merged"
            return 0
        fi
    fi

    # Second check: GitHub PR state (if we have PR number)
    local pr_number=""
    if [ -n "$worker_dir" ] && [ -d "$worker_dir" ]; then
        pr_number=$(git_state_get_pr "$worker_dir" 2>/dev/null || echo "")
    fi

    if [ -n "$pr_number" ] && [ "$pr_number" != "null" ]; then
        local pr_state
        pr_state=$(timeout "${WIGGUM_GH_TIMEOUT:-10}" gh pr view "$pr_number" --json state -q '.state' 2>/dev/null || echo "UNKNOWN")
        case "$pr_state" in
            MERGED)
                echo "merged"
                return 0
                ;;
            OPEN)
                echo "open"
                return 1
                ;;
            CLOSED)
                echo "closed"
                return 1
                ;;
        esac
    fi

    echo "unknown"
    return 1
}

# Check for tasks needing fixes and spawn fix workers
#
# Collects tasks from two sources:
# 1. .tasks-needing-fix.txt (populated by wiggum-review sync for fresh comments)
# 2. Worker directories with needs_fix git state (fallback for stuck tasks)
#
# Tasks are sorted by dependency depth (descending) so that tasks which
# unblock the most downstream work are fixed first.
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
#   limit       - Maximum total priority workers (fix + resolve combined)
#
# Requires:
#   - pool_* functions from worker-pool.sh
#   - git_state_* functions from git-state.sh
#   - get_dependency_depth from task-parser.sh
#   - WIGGUM_HOME environment variable
spawn_fix_workers() {
    local ralph_dir="$1"
    local project_dir="$2"
    local limit="$3"

    local tasks_needing_fix="$ralph_dir/.tasks-needing-fix.txt"
    local kanban_file="$ralph_dir/kanban.md"

    [ -d "$ralph_dir/workers" ] || return 0

    # Sync file-based capacity tracking with actual pool state
    # This handles cases where workers exited unexpectedly
    _priority_capacity_sync "$ralph_dir"

    # Collect tasks from both sources into a deduplicated list
    # Use associative array for deduplication
    local -A task_set=()

    # Source 1: tasks-needing-fix.txt (fresh comments from sync)
    if [ -s "$tasks_needing_fix" ]; then
        while read -r task_id; do
            [ -n "$task_id" ] && task_set["$task_id"]=1
        done < "$tasks_needing_fix"
    fi

    # Source 2: scan workers for needs_fix state (fallback for stuck tasks)
    for worker_dir in "$ralph_dir/workers"/worker-*; do
        [ -d "$worker_dir" ] || continue
        git_state_is "$worker_dir" "needs_fix" || continue

        local worker_id task_id
        worker_id=$(basename "$worker_dir")
        task_id=$(get_task_id_from_worker "$worker_id")

        if [ -n "$task_id" ] && [ -z "${task_set[$task_id]:-}" ]; then
            task_set["$task_id"]=1
            log_debug "Found stuck needs_fix task: $task_id"
        fi
    done

    # Exit early if no tasks
    if [ ${#task_set[@]} -eq 0 ]; then
        return 0
    fi

    log "Checking for tasks needing PR comment fixes..."

    # Sort tasks by dependency depth (descending) - tasks that unblock more work go first
    local -a sorted_tasks=()
    local -a task_scores=()
    for task_id in "${!task_set[@]}"; do
        local dep_depth=0
        if [ -f "$kanban_file" ]; then
            dep_depth=$(get_dependency_depth "$kanban_file" "$task_id" 2>/dev/null || echo "0")
        fi
        task_scores+=("$dep_depth|$task_id")
    done

    # Sort by depth descending (higher depth first = unblocks more tasks)
    while IFS= read -r entry; do
        [ -n "$entry" ] || continue
        sorted_tasks+=("${entry#*|}")
    done < <(printf '%s\n' "${task_scores[@]}" | sort -t'|' -k1 -rn)

    for task_id in "${sorted_tasks[@]}"; do
        [ -z "$task_id" ] && continue

        local worker_dir
        worker_dir=$(find_worker_by_task_id "$ralph_dir" "$task_id" 2>/dev/null)

        if [ -z "$worker_dir" ] || [ ! -d "$worker_dir" ]; then
            continue
        fi

        # Verify needs_fix state (may have changed since collection)
        if ! git_state_is "$worker_dir" "needs_fix"; then
            continue
        fi

        # Guard: skip if agent is already running for this worker
        if [ -f "$worker_dir/agent.pid" ]; then
            local existing_pid
            existing_pid=$(cat "$worker_dir/agent.pid")
            if kill -0 "$existing_pid" 2>/dev/null; then
                log "Fix agent already running for $task_id (PID: $existing_pid) - skipping"
                continue
            fi
        fi

        # Atomically reserve capacity slot (prevents race with resolve-workers)
        if ! _priority_capacity_reserve "$ralph_dir" "$limit"; then
            log "Fix worker limit reached ($limit) - deferring remaining fixes"
            break
        fi

        # Ensure workspace exists (reconstruct from PR branch if missing)
        if ! ensure_workspace_from_pr "$worker_dir" "$project_dir" "$task_id"; then
            log_error "Cannot spawn fix worker for $task_id: workspace missing and reconstruction failed"
            _priority_capacity_release "$ralph_dir"
            continue
        fi

        # Transition state to fixing
        git_state_set "$worker_dir" "fixing" "priority-workers.spawn_fix_workers" "Fix worker spawned"

        log "Spawning fix worker for $task_id..."

        # Call wiggum-review task fix synchronously (it returns immediately after async launch)
        (
            cd "$project_dir" || exit 1
            "$WIGGUM_HOME/bin/wiggum-review" task "$task_id" fix 2>&1 | \
                sed "s/^/  [fix-$task_id] /"
        )

        # Wait briefly for agent.pid to appear (async launch race condition)
        local wait_count=0
        while [ ! -f "$worker_dir/agent.pid" ] && [ $wait_count -lt 20 ]; do
            sleep 0.1
            ((++wait_count)) || true
        done

        # Read the agent PID from the worker directory
        if [ -f "$worker_dir/agent.pid" ]; then
            local agent_pid
            agent_pid=$(cat "$worker_dir/agent.pid")
            pool_add "$agent_pid" "fix" "$task_id"
            log "Fix worker spawned for $task_id (PID: $agent_pid)"
        else
            log_warn "Fix agent for $task_id did not produce agent.pid after 2s wait"
            # Revert state so it can be retried
            git_state_set "$worker_dir" "needs_fix" "priority-workers.spawn_fix_workers" "Agent failed to start"
            _priority_capacity_release "$ralph_dir"
        fi
    done

    # Clear the tasks needing fix file after processing
    : > "$tasks_needing_fix"
}

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
        total=$(jq -r '.total' "$coord_file")

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
        if [ -f "$kanban_file" ]; then
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

    # Sync file-based capacity tracking with actual pool state
    # This handles cases where workers exited unexpectedly
    _priority_capacity_sync "$ralph_dir"

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
            git_state_set "$worker_dir" "failed" "priority-workers.spawn_resolve_workers" "Max merge attempts exceeded after resolution"
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
            log_error "Cannot spawn resolver for $task_id: workspace missing and reconstruction failed"
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
                git_state_set "$worker_dir" "failed" "priority-workers._spawn_simple_resolve_worker" "Workspace missing and reconstruction failed"
            fi
            return 1
        fi
    fi

    # Transition state
    git_state_set "$worker_dir" "resolving" "priority-workers.spawn_resolve_workers" "Simple resolver spawned"

    log "Spawning simple conflict resolver for $task_id..."

    # Call wiggum-review task resolve asynchronously
    (
        cd "$project_dir" || exit 1
        "$WIGGUM_HOME/bin/wiggum-review" task "$task_id" resolve 2>&1 | \
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
                    git_state_set "$worker_dir" "merged" "priority-workers._spawn_batch_resolve_worker" "PR confirmed merged"
                else
                    git_state_set "$worker_dir" "failed" "priority-workers._spawn_batch_resolve_worker" "Workspace missing and reconstruction failed, PR status: $merge_status"
                fi
            fi
            return 0
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
            # Re-categorize this task on next cycle
            git_state_set "$worker_dir" "needs_resolve" "priority-workers._spawn_batch_resolve_worker" "Batch failed, needs re-evaluation"
        else
            log "Batch resolver for $task_id: waiting for turn (batch: $batch_id, position $((position + 1)) of $total)"
        fi
        return 1  # Not my turn - return 1 so capacity is released
    fi

    # Transition state
    git_state_set "$worker_dir" "resolving" "priority-workers.spawn_resolve_workers" "Batch resolver spawned (batch: $batch_id, position: $((position + 1))/$total)"

    log "Spawning batch resolver for $task_id (batch: $batch_id, position $((position + 1)) of $total)..."

    # Launch worker using multi-pr-resolve pipeline
    # wiggum-start daemonizes the worker - we track via agent.pid
    (
        cd "$project_dir" || exit 1
        "$WIGGUM_HOME/bin/wiggum-start" --worker-dir "$worker_dir" \
            --pipeline multi-pr-resolve --quiet 2>&1 | \
            sed "s/^/  [batch-resolve-$task_id] /"
    )

    # Wait for agent.pid to appear and use that for tracking
    local wait_count=0
    while [ ! -f "$worker_dir/agent.pid" ] && [ $wait_count -lt 30 ]; do
        sleep 0.1
        ((wait_count++)) || true
    done

    if [ -f "$worker_dir/agent.pid" ]; then
        local resolver_pid
        resolver_pid=$(cat "$worker_dir/agent.pid")
        pool_add "$resolver_pid" "resolve" "$task_id"
        log "Batch resolver spawned for $task_id (PID: $resolver_pid)"
    else
        log_error "Failed to get worker PID for $task_id - agent.pid not created"
        git_state_set "$worker_dir" "failed" "priority-workers.spawn_resolve_workers" "Worker failed to start"
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

    local orphan_file="$ralph_dir/.prs-needing-workspace.jsonl"

    if [ ! -s "$orphan_file" ]; then
        return 0
    fi

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
        timestamp=$(date +%s)
        worker_id="worker-${task_id}-fix-${timestamp}"
        worker_dir="$ralph_dir/workers/$worker_id"

        mkdir -p "$worker_dir"
        log "  $task_id: Creating workspace from branch $branch"

        # Create worktree from PR branch
        if ! setup_worktree_from_branch "$project_dir" "$worker_dir" "$branch"; then
            log_error "  $task_id: Failed to create workspace from branch $branch"
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
        "$WIGGUM_HOME/bin/wiggum-review" task "$task_id" sync 2>/dev/null || true

        # Queue for fix processing
        echo "$task_id" >> "$ralph_dir/.tasks-needing-fix.txt"
        git_state_set "$worker_dir" "needs_fix" "priority-workers.create_orphan_pr_workspaces" "Workspace created from PR branch"

        log "  $task_id: Workspace created, queued for fix"
        processed+=("$task_id")
    done < "$orphan_file"

    # Remove processed entries from orphan file
    if [ ${#processed[@]} -gt 0 ]; then
        local temp_file
        temp_file=$(mktemp)
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

# Handle fix worker completion - verify push and transition state for merge
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier
#
# Returns: 0 on success, 1 on failure
handle_fix_worker_completion() {
    local worker_dir="$1"
    local task_id="$2"

    # Find the fix agent result by looking for result files with gate_result field.
    # Fix agents produce results with gate_result (PASS/FIX/FAIL/SKIP).
    # Check newest results first to get the most recent run.
    local result_file=""
    local candidate
    while read -r candidate; do
        [ -f "$candidate" ] || continue
        # Check if this result has gate_result (fix agent signature)
        # Accept results with either outputs.gate_result or top-level gate_result
        if jq -e '.outputs.gate_result // .gate_result' "$candidate" &>/dev/null; then
            result_file="$candidate"
            break
        fi
    done < <(find "$worker_dir/results" -maxdepth 1 -name "*-result.json" -type f 2>/dev/null | sort -r)

    if [ -z "$result_file" ]; then
        # Fix agent didn't produce a result - it may have failed to start or exited early
        log_warn "No fix agent result for $task_id - fix agent may not have run"
        # Revert state to needs_fix so it can be retried on next cycle
        git_state_set "$worker_dir" "needs_fix" "priority-workers.handle_fix_worker_completion" "No result file found"
        return 1
    fi

    local gate_result push_succeeded
    gate_result=$(jq -r '.outputs.gate_result // .gate_result // "FAIL"' "$result_file" 2>/dev/null)
    push_succeeded=$(jq -r '.outputs.push_succeeded // "false"' "$result_file" 2>/dev/null)

    if [ "$gate_result" = "PASS" ] && [ "$push_succeeded" = "true" ]; then
        git_state_set "$worker_dir" "fix_completed" "priority-workers.handle_fix_worker_completion" "Push verified"
        git_state_set "$worker_dir" "needs_merge" "priority-workers.handle_fix_worker_completion" "Ready for merge attempt"
        log "Fix completed for $task_id - ready for merge"
        return 0
    elif [ "$gate_result" = "PASS" ]; then
        # Fix succeeded but push didn't - still mark as completed
        git_state_set "$worker_dir" "fix_completed" "priority-workers.handle_fix_worker_completion" "Fix passed but push failed"
        log_warn "Fix completed for $task_id but push failed"
        return 0
    elif [ "$gate_result" = "SKIP" ]; then
        # No comments to fix - transition to merge
        git_state_set "$worker_dir" "fix_completed" "priority-workers.handle_fix_worker_completion" "No comments to fix (SKIP)"
        git_state_set "$worker_dir" "needs_merge" "priority-workers.handle_fix_worker_completion" "Ready for merge attempt"
        log "Fix skipped for $task_id (no comments) - ready for merge"
        return 0
    elif [ "$gate_result" = "FIX" ]; then
        # Partial fix - some comments addressed but not all
        git_state_set "$worker_dir" "needs_fix" "priority-workers.handle_fix_worker_completion" "Partial fix, needs more work"
        log_warn "Partial fix for $task_id - will retry"
        return 1
    else
        git_state_set "$worker_dir" "failed" "priority-workers.handle_fix_worker_completion" "Fix agent returned: $gate_result"
        log_error "Fix failed for $task_id (result: $gate_result)"
        return 1
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

    # Check if conflicts are resolved
    local workspace="$worker_dir/workspace"
    if [ ! -d "$workspace" ]; then
        git_state_set "$worker_dir" "failed" "priority-workers.handle_resolve_worker_completion" "Workspace not found"
        return 1
    fi

    local remaining_conflicts
    remaining_conflicts=$(git -C "$workspace" diff --name-only --diff-filter=U 2>/dev/null || true)

    if [ -z "$remaining_conflicts" ]; then
        git_state_set "$worker_dir" "resolved" "priority-workers.handle_resolve_worker_completion" "All conflicts resolved"

        # Need to commit and push the resolution
        log "Conflicts resolved for $task_id - committing resolution..."

        # Derive paths from worker_dir (works correctly with worktrees)
        # worker_dir = project/.ralph/workers/worker-XXX/
        # ralph_dir  = project/.ralph/
        # project_dir = project/
        local ralph_dir
        ralph_dir=$(dirname "$(dirname "$worker_dir")")
        local project_dir
        project_dir=$(dirname "$ralph_dir")

        (
            cd "$project_dir" || exit 1
            "$WIGGUM_HOME/bin/wiggum-review" task "$task_id" commit 2>&1 | sed "s/^/  [commit-$task_id] /"
            "$WIGGUM_HOME/bin/wiggum-review" task "$task_id" push 2>&1 | sed "s/^/  [push-$task_id] /"
        )

        # Remove from conflict queue (ralph_dir already computed above)
        conflict_queue_remove "$ralph_dir" "$task_id"

        # Ready for another merge attempt
        git_state_set "$worker_dir" "needs_merge" "priority-workers.handle_resolve_worker_completion" "Ready for merge retry"
        return 0
    else
        local count
        count=$(echo "$remaining_conflicts" | wc -l)
        git_state_set "$worker_dir" "failed" "priority-workers.handle_resolve_worker_completion" "$count files still have conflicts"
        log_error "Resolver failed for $task_id - $count files still have conflicts"
        return 1
    fi
}

# Handle timeout for fix workers
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier
#   timeout    - Timeout value in seconds (for logging)
handle_fix_worker_timeout() {
    local worker_dir="$1"
    local task_id="$2"
    local timeout="${3:-1800}"

    log_warn "Fix worker for $task_id timed out after ${timeout}s"
    git_state_set "$worker_dir" "failed" "priority-workers" "Fix worker timed out after ${timeout}s"
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
    local timeout="${3:-1800}"

    log_warn "Resolve worker for $task_id timed out after ${timeout}s"
    git_state_set "$worker_dir" "failed" "priority-workers" "Resolve worker timed out after ${timeout}s"
}
