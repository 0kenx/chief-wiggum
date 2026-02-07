#!/usr/bin/env bash
# priority-workers.sh - Shared priority worker infrastructure
#
# Provides capacity management, failure handling, workspace reconstruction,
# and merge verification used by fix-workers.sh and resolve-workers.sh.
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
source "$WIGGUM_HOME/lib/core/safe-path.sh"
source "$WIGGUM_HOME/lib/core/lifecycle-engine.sh"

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
    _PRIORITY_CAPACITY_FILE="$ralph_dir/orchestrator/priority-worker-count"

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
                state=$(jq -r '.current_state // ""' "$worker_dir/git-state.json" 2>/dev/null || echo "")
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

# Check if a failed worker should be marked permanently failed in kanban
#
# Called after setting git-state to "failed". If the worker has exceeded
# max recovery attempts, marks the kanban task as [*] (failed).
#
# Args:
#   worker_dir  - Worker directory path
#   kanban_file - Path to kanban.md
#   task_id     - Task identifier
_check_permanent_failure() {
    local worker_dir="$1"
    local kanban_file="$2"
    local task_id="$3"

    local _recovery_count
    _recovery_count=$(git_state_get_recovery_attempts "$worker_dir")
    _recovery_count="${_recovery_count:-0}"

    if [ "$_recovery_count" -ge "${WIGGUM_MAX_RECOVERY_ATTEMPTS:-2}" ]; then
        log_error "$task_id: permanently failed after $_recovery_count recovery attempts"
        # Ensure lifecycle spec is loaded (this effect may be called from emit_event)
        lifecycle_is_loaded || lifecycle_load
        emit_event "$worker_dir" "permanent_failure" "priority-workers._check_permanent_failure"
    fi
}

# Recover workers stuck in "failed" git-state
#
# Scans for workers with "failed" git-state and re-enters them into
# the fix/resolve cycle if recovery is possible. This implements
# self-healing for the cascade where run_sub_agent failures leave
# workers permanently stuck.
#
# Recovery logic:
#   - If last failure reason contains "merge" or "conflict": reset merge_attempts,
#     set state to needs_resolve
#   - If last failure reason is "UNKNOWN" result: set state to needs_fix
#   - If max recovery attempts exceeded: mark kanban [*] and leave as failed
#
# Args:
#   ralph_dir - Ralph directory path
recover_failed_workers() {
    local ralph_dir="$1"
    local kanban_file="$ralph_dir/kanban.md"
    local max_recovery="${WIGGUM_MAX_RECOVERY_ATTEMPTS:-2}"

    [ -d "$ralph_dir/workers" ] || return 0

    for worker_dir in "$ralph_dir/workers"/worker-*; do
        [ -d "$worker_dir" ] || continue

        # Only process workers in "failed" state
        git_state_is "$worker_dir" "failed" || continue

        local worker_id task_id
        worker_id=$(basename "$worker_dir")
        task_id=$(get_task_id_from_worker "$worker_id")

        # Only recover tasks that are still [P] (pending approval) - not already [*] or [x]
        if [ -f "$kanban_file" ]; then
            local task_status
            task_status=$(get_task_status "$kanban_file" "$task_id")
            if [[ "$task_status" != "P" && "$task_status" != "=" ]]; then
                continue
            fi
        fi

        # Ensure lifecycle spec is loaded
        lifecycle_is_loaded || lifecycle_load

        # Classify failure reason from last transition
        local last_reason
        last_reason=$(jq -r '.transitions[-1].reason // ""' "$worker_dir/git-state.json" 2>/dev/null)

        # The lifecycle guards handle max recovery check:
        # - If recovery_attempts_lt_max passes: transition to needs_resolve/needs_fix
        #   with inc_recovery + reset_merge effects
        # - If guard fails: falls through to failed→failed with check_permanent effect
        if echo "$last_reason" | grep -qiE "UNKNOWN"; then
            emit_event "$worker_dir" "recovery.to_fix" "priority-workers.recover_failed_workers"
        else
            emit_event "$worker_dir" "recovery.to_resolve" "priority-workers.recover_failed_workers"
        fi

        local post_state
        post_state=$(git_state_get "$worker_dir")
        if [ "$post_state" != "failed" ]; then
            local recovery_count
            recovery_count=$(git_state_get_recovery_attempts "$worker_dir")
            recovery_count="${recovery_count:-0}"
            log "Recovered $task_id from failed state -> $post_state (attempt $recovery_count/$max_recovery)"
        fi
    done
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

    # Get branch name and PR state in a single API call
    local branch pr_state pr_info
    pr_info=$(gh pr view "$pr_number" --json headRefName,state 2>/dev/null || true)
    branch=$(echo "$pr_info" | jq -r '.headRefName // empty' 2>/dev/null)
    pr_state=$(echo "$pr_info" | jq -r '.state // empty' 2>/dev/null)

    if [ -z "$branch" ]; then
        log_error "Cannot reconstruct workspace for $task_id: failed to get branch from PR #$pr_number"
        return 1
    fi

    # Don't reconstruct workspace for merged/closed PRs - the branch may have been
    # deleted and reconstructing would re-push it when agents commit changes
    if [ "$pr_state" = "MERGED" ] || [ "$pr_state" = "CLOSED" ]; then
        log "Skipping workspace reconstruction for $task_id: PR #$pr_number is $pr_state"
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
        # Validate task_id format before using in grep -E to prevent regex injection
        if ! [[ "$task_id" =~ ^[A-Za-z]{2,10}-[0-9]{1,4}$ ]]; then
            echo "unknown"
            return 1
        fi
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

