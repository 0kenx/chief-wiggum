#!/usr/bin/env bash
# merge-manager.sh - PR merge workflow management
#
# Handles the PR merge lifecycle:
#   - Attempting merges
#   - Detecting conflicts
#   - Transitioning state for retry/resolution
#   - Updating kanban status on success
#   - Queueing conflicts for multi-PR coordination
set -euo pipefail

[ -n "${_MERGE_MANAGER_LOADED:-}" ] && return 0
_MERGE_MANAGER_LOADED=1

# Source dependencies
source "$WIGGUM_HOME/lib/worker/git-state.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"
source "$WIGGUM_HOME/lib/scheduler/conflict-queue.sh"
source "$WIGGUM_HOME/lib/scheduler/batch-coordination.sh"

# Seconds to wait for GitHub to report PR as mergeable after a push
MERGE_POLL_TIMEOUT="${WIGGUM_MERGE_POLL_TIMEOUT:-30}"
MERGE_POLL_INTERVAL="${WIGGUM_MERGE_POLL_INTERVAL:-5}"

# Poll GitHub until PR mergeable status is determined
#
# After a push, GitHub returns mergeable=UNKNOWN while recalculating.
# This function polls until GitHub resolves to MERGEABLE or CONFLICTING,
# preventing the race condition where gh pr merge is called before
# GitHub has processed the push.
#
# Args:
#   pr_number - PR number to check
#   task_id   - Task identifier (for logging)
#
# Returns:
#   0 - PR is MERGEABLE
#   1 - PR is CONFLICTING
#   2 - Timeout or error (status unknown)
_wait_for_mergeable() {
    local pr_number="$1"
    local task_id="$2"

    local elapsed=0
    local status

    while [ "$elapsed" -lt "$MERGE_POLL_TIMEOUT" ]; do
        status=$(gh pr view "$pr_number" --json mergeable -q '.mergeable' 2>/dev/null || echo "UNKNOWN")

        case "$status" in
            MERGEABLE)
                log_debug "PR #$pr_number is mergeable for $task_id"
                return 0
                ;;
            CONFLICTING)
                log_debug "PR #$pr_number has conflicts for $task_id"
                return 1
                ;;
            UNKNOWN|"")
                # GitHub is still calculating - wait and retry
                if [ "$elapsed" -eq 0 ]; then
                    log_debug "Waiting for GitHub to calculate mergeable status for PR #$pr_number..."
                fi
                sleep "$MERGE_POLL_INTERVAL"
                elapsed=$((elapsed + MERGE_POLL_INTERVAL))
                ;;
            *)
                log_warn "Unexpected mergeable status '$status' for PR #$pr_number"
                return 2
                ;;
        esac
    done

    log_warn "Timed out waiting for mergeable status for PR #$pr_number ($task_id) after ${elapsed}s"
    return 2
}

# Clean up batch coordination state after a PR is merged
#
# When a PR is merged independently (not through batch resolution), we need to:
# 1. Mark the task complete in the batch coordination file
# 2. Remove batch-context.json from the worker
# 3. Remove the task from the conflict queue
#
# This prevents spawn_resolve_workers() from trying to use a deleted workspace.
#
# Args:
#   worker_dir  - Worker directory path
#   task_id     - Task identifier
#   ralph_dir   - Ralph directory path
_cleanup_batch_state() {
    local worker_dir="$1"
    local task_id="$2"
    local ralph_dir="$3"

    # Clean up batch coordination if this worker was part of a batch
    if batch_coord_has_worker_context "$worker_dir"; then
        local batch_id
        batch_id=$(batch_coord_read_worker_context "$worker_dir" "batch_id")
        if [ -n "$batch_id" ]; then
            # Get project_dir from ralph_dir (ralph_dir is typically project_dir/.ralph)
            local project_dir
            project_dir=$(dirname "$ralph_dir")
            batch_coord_mark_complete "$batch_id" "$task_id" "$project_dir"
            log "Marked $task_id complete in batch $batch_id"
        fi
        rm -f "$worker_dir/batch-context.json"
    fi

    # Remove from conflict queue if present
    conflict_queue_remove "$ralph_dir" "$task_id"
}

# Clean up worker directory after PR is merged
#
# Unregisters the git worktree, then removes the entire worker directory.
#
# Args:
#   worker_dir - Worker directory path
_cleanup_merged_pr_worktree() {
    local worker_dir="$1"
    local workspace="$worker_dir/workspace"
    local worker_name
    worker_name=$(basename "$worker_dir")

    # Unregister git worktree if workspace exists
    if [ -d "$workspace" ]; then
        local main_repo
        main_repo=$(git -C "$workspace" worktree list --porcelain 2>/dev/null | head -1 | sed 's/^worktree //')

        if [ -n "$main_repo" ] && [ -d "$main_repo" ]; then
            git -C "$main_repo" worktree remove --force "$workspace" 2>/dev/null || true
        fi
    fi

    # Remove the entire worker directory
    # Retry once after a brief delay to handle race with background build processes
    # (e.g. cargo/rustc writing to target-shared while rm -rf is deleting)
    if [ -d "$worker_dir" ]; then
        rm -rf "$worker_dir" 2>/dev/null
        if [ -d "$worker_dir" ]; then
            sleep 1
            rm -rf "$worker_dir" 2>/dev/null || true
        fi
    fi

    log "Worker directory removed for $worker_name"
}

# Attempt to merge a PR for a worker
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier
#   ralph_dir  - Ralph directory path (for kanban updates)
#
# Returns:
#   0 - Merge succeeded
#   1 - Merge conflict (needs resolver)
#   2 - Other failure (unrecoverable)
attempt_pr_merge() {
    local worker_dir="$1"
    local task_id="$2"
    local ralph_dir="$3"

    local pr_number
    pr_number=$(git_state_get_pr "$worker_dir")

    if [ "$pr_number" = "null" ] || [ -z "$pr_number" ]; then
        # Try to find PR number from workspace branch
        if [ -d "$worker_dir/workspace" ]; then
            local branch
            branch=$(git -C "$worker_dir/workspace" rev-parse --abbrev-ref HEAD 2>/dev/null || true)
            if [ -n "$branch" ] && [ "$branch" != "HEAD" ]; then
                pr_number=$(gh pr list --head "$branch" --state open --json number -q '.[0].number' 2>/dev/null || true)
                if [ -n "$pr_number" ]; then
                    git_state_set_pr "$worker_dir" "$pr_number"
                fi
            fi
        fi
    fi

    if [ -z "$pr_number" ] || [ "$pr_number" = "null" ]; then
        log_warn "No PR number found for $task_id - cannot attempt merge"
        return 2
    fi

    # Check if we've already exceeded max attempts BEFORE incrementing
    local merge_attempts
    merge_attempts=$(git_state_get_merge_attempts "$worker_dir")
    if [ "$merge_attempts" -ge "$MAX_MERGE_ATTEMPTS" ]; then
        git_state_set "$worker_dir" "failed" "merge-manager.attempt_pr_merge" "Max merge attempts ($MAX_MERGE_ATTEMPTS) already reached"
        log_error "Max merge attempts already reached for $task_id (at $merge_attempts attempts)"
        return 2
    fi

    git_state_set "$worker_dir" "merging" "merge-manager.attempt_pr_merge" "Attempting merge of PR #$pr_number"
    git_state_inc_merge_attempts "$worker_dir"
    ((++merge_attempts))

    log "Attempting merge for $task_id PR #$pr_number (attempt $merge_attempts/$MAX_MERGE_ATTEMPTS)"

    # Wait for GitHub to determine mergeable status before attempting merge.
    # After a push, GitHub returns UNKNOWN while recalculating - calling
    # gh pr merge during this window fails with "not mergeable".
    local poll_result=0
    _wait_for_mergeable "$pr_number" "$task_id" || poll_result=$?

    if [ "$poll_result" -eq 1 ]; then
        # PR has conflicts - skip straight to conflict handling
        log "PR #$pr_number has conflicts (detected before merge attempt)"
        git_state_set_error "$worker_dir" "Merge conflict detected via mergeable status"
        git_state_set "$worker_dir" "merge_conflict" "merge-manager.attempt_pr_merge" "PR has conflicts (pre-merge check)"

        local affected_files='[]'
        local workspace="$worker_dir/workspace"
        if [ -d "$workspace" ]; then
            local changed_files
            changed_files=$(git -C "$workspace" diff --name-only origin/main 2>/dev/null | head -50 || true)
            if [ -n "$changed_files" ]; then
                affected_files=$(echo "$changed_files" | jq -R -s 'split("\n") | map(select(length > 0))')
            fi
        fi
        conflict_queue_add "$ralph_dir" "$task_id" "$worker_dir" "$pr_number" "$affected_files"

        if [ "$merge_attempts" -lt "$MAX_MERGE_ATTEMPTS" ]; then
            git_state_set "$worker_dir" "needs_resolve" "merge-manager.attempt_pr_merge" "Conflict resolver required"
            log "Merge conflict for $task_id - will spawn resolver"
            return 1
        else
            git_state_set "$worker_dir" "failed" "merge-manager.attempt_pr_merge" "Max merge attempts ($MAX_MERGE_ATTEMPTS) exceeded"
            log_error "Max merge attempts exceeded for $task_id"
            return 2
        fi
    fi
    # poll_result=2 (timeout/unknown) - proceed with merge attempt anyway

    local merge_output merge_exit=0
    # Don't use --delete-branch: worktrees conflict with local branch deletion
    # Branch cleanup happens when worktree is removed after merge
    merge_output=$(gh pr merge "$pr_number" --merge 2>&1) || merge_exit=$?

    if [ $merge_exit -eq 0 ]; then
        git_state_set "$worker_dir" "merged" "merge-manager.attempt_pr_merge" "PR #$pr_number merged successfully"
        log "PR #$pr_number merged successfully for $task_id"

        # Update kanban status to complete
        if [ -f "$ralph_dir/kanban.md" ]; then
            update_kanban_status "$ralph_dir/kanban.md" "$task_id" "x"
        fi

        # Clean up batch coordination state before removing workspace
        _cleanup_batch_state "$worker_dir" "$task_id" "$ralph_dir"

        # Clean up worktree
        _cleanup_merged_pr_worktree "$worker_dir"
        return 0
    fi

    # Check if PR was already merged (gh returns error but this is actually success)
    if echo "$merge_output" | grep -qi "already merged"; then
        git_state_set "$worker_dir" "merged" "merge-manager.attempt_pr_merge" "PR #$pr_number was already merged"
        log "PR #$pr_number was already merged for $task_id"

        # Update kanban status to complete
        if [ -f "$ralph_dir/kanban.md" ]; then
            update_kanban_status "$ralph_dir/kanban.md" "$task_id" "x"
        fi

        # Clean up batch coordination state before removing workspace
        _cleanup_batch_state "$worker_dir" "$task_id" "$ralph_dir"

        # Clean up worktree
        _cleanup_merged_pr_worktree "$worker_dir"
        return 0
    fi

    # Check failure type - distinguish between conflicts and other issues
    #
    # "out of date" / "branch is behind" = needs rebase, NOT a conflict
    # "local changes would be overwritten" = dirty working tree, NOT a conflict
    # Only "conflict" or "cannot be merged" with actual conflict markers = real conflict

    # First check for non-conflict failures that should not trigger resolver
    if echo "$merge_output" | grep -qiE "(out of date|branch.*behind|is not up to date)"; then
        git_state_set_error "$worker_dir" "Branch out of date: $merge_output"
        git_state_set "$worker_dir" "failed" "merge-manager.attempt_pr_merge" "Branch is out of date - needs rebase (not a conflict)"
        log_error "Merge failed for $task_id: branch is out of date with base branch"
        return 2
    fi

    if echo "$merge_output" | grep -qiE "(local changes.*overwritten|uncommitted changes|working tree.*not clean)"; then
        git_state_set_error "$worker_dir" "Dirty working tree: $merge_output"
        git_state_set "$worker_dir" "failed" "merge-manager.attempt_pr_merge" "Working tree has uncommitted changes"
        log_error "Merge failed for $task_id: working tree has uncommitted changes"
        return 2
    fi

    # Check if failure is due to actual merge conflict
    if echo "$merge_output" | grep -qiE "(conflict|cannot be merged)"; then
        git_state_set_error "$worker_dir" "Merge conflict: $merge_output"
        git_state_set "$worker_dir" "merge_conflict" "merge-manager.attempt_pr_merge" "Merge failed due to conflict"

        # Get affected files for multi-PR tracking
        local affected_files='[]'
        local workspace="$worker_dir/workspace"
        if [ -d "$workspace" ]; then
            # Get list of files changed in this branch vs main
            local changed_files
            changed_files=$(git -C "$workspace" diff --name-only origin/main 2>/dev/null | head -50 || true)
            if [ -n "$changed_files" ]; then
                affected_files=$(echo "$changed_files" | jq -R -s 'split("\n") | map(select(length > 0))')
            fi
        fi

        # Add to conflict queue for multi-PR coordination
        conflict_queue_add "$ralph_dir" "$task_id" "$worker_dir" "$pr_number" "$affected_files"

        if [ "$merge_attempts" -lt "$MAX_MERGE_ATTEMPTS" ]; then
            git_state_set "$worker_dir" "needs_resolve" "merge-manager.attempt_pr_merge" "Conflict resolver required"
            log "Merge conflict for $task_id - will spawn resolver"
            return 1
        else
            git_state_set "$worker_dir" "failed" "merge-manager.attempt_pr_merge" "Max merge attempts ($MAX_MERGE_ATTEMPTS) exceeded"
            log_error "Max merge attempts exceeded for $task_id"
            return 2
        fi
    fi

    # "not mergeable" is transient after a push - GitHub may still be processing.
    # Retry if we have attempts remaining instead of failing permanently.
    if echo "$merge_output" | grep -qiE "not mergeable"; then
        if [ "$merge_attempts" -lt "$MAX_MERGE_ATTEMPTS" ]; then
            git_state_set_error "$worker_dir" "Transient: $merge_output"
            git_state_set "$worker_dir" "needs_merge" "merge-manager.attempt_pr_merge" "PR not yet mergeable - will retry (attempt $merge_attempts/$MAX_MERGE_ATTEMPTS)"
            log_warn "Merge not yet ready for $task_id (attempt $merge_attempts/$MAX_MERGE_ATTEMPTS) - will retry"
            return 1
        fi
    fi

    # Other merge failure (unrecoverable)
    git_state_set_error "$worker_dir" "Merge failed: $merge_output"
    git_state_set "$worker_dir" "failed" "merge-manager.attempt_pr_merge" "Merge failed: ${merge_output:0:100}"
    log_error "Merge failed for $task_id: $merge_output"
    return 2
}

# Check if a worker needs merge and attempt it
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier
#   ralph_dir  - Ralph directory path
#
# Returns: result of attempt_pr_merge or 0 if no merge needed
try_merge_if_needed() {
    local worker_dir="$1"
    local task_id="$2"
    local ralph_dir="$3"

    if git_state_is "$worker_dir" "needs_merge"; then
        attempt_pr_merge "$worker_dir" "$task_id" "$ralph_dir"
        return $?
    fi

    return 0
}

# Process all workers needing merge
#
# Scans worker directories and attempts merge for any in needs_merge state.
# This is useful after fix workers complete or resolvers finish.
#
# Args:
#   ralph_dir - Ralph directory path
#
# Returns:
#   Sets MERGE_MANAGER_PROCESSED to count of workers processed
#   Sets MERGE_MANAGER_MERGED to count of successful merges
#   Sets MERGE_MANAGER_CONFLICTS to count of conflicts requiring resolution
process_pending_merges() {
    local ralph_dir="$1"

    MERGE_MANAGER_PROCESSED=0
    MERGE_MANAGER_MERGED=0
    MERGE_MANAGER_CONFLICTS=0

    [ -d "$ralph_dir/workers" ] || return 0

    for worker_dir in "$ralph_dir/workers"/worker-*; do
        [ -d "$worker_dir" ] || continue

        if git_state_is "$worker_dir" "needs_merge"; then
            local worker_id
            worker_id=$(basename "$worker_dir")
            local task_id
            task_id=$(echo "$worker_id" | sed -E 's/worker-([A-Za-z]{2,10}-[0-9]{1,4})-.*/\1/')

            ((++MERGE_MANAGER_PROCESSED)) || true

            local merge_result=0
            attempt_pr_merge "$worker_dir" "$task_id" "$ralph_dir" || merge_result=$?

            case $merge_result in
                0)
                    ((++MERGE_MANAGER_MERGED)) || true
                    ;;
                1)
                    ((++MERGE_MANAGER_CONFLICTS)) || true
                    ;;
                *)
                    # Failed - already logged
                    ;;
            esac
        fi
    done
}

# Get merge status summary for display
#
# Args:
#   ralph_dir - Ralph directory path
#
# Returns: JSON-like summary of merge states
get_merge_status_summary() {
    local ralph_dir="$1"
    local needs_merge=0
    local merging=0
    local conflicts=0
    local merged=0
    local failed=0

    [ -d "$ralph_dir/workers" ] || { echo "{}"; return 0; }

    for worker_dir in "$ralph_dir/workers"/worker-*; do
        [ -d "$worker_dir" ] || continue

        local state
        state=$(git_state_get "$worker_dir")

        case "$state" in
            needs_merge)   ((++needs_merge)) || true ;;
            merging)       ((++merging)) || true ;;
            merge_conflict|needs_resolve|resolving)
                           ((++conflicts)) || true ;;
            merged)        ((++merged)) || true ;;
            failed)        ((++failed)) || true ;;
        esac
    done

    cat << EOF
{
  "needs_merge": $needs_merge,
  "merging": $merging,
  "conflicts": $conflicts,
  "merged": $merged,
  "failed": $failed
}
EOF
}
