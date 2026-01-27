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
        # Try to find PR number from branch
        local branch_file="$worker_dir/branch.txt"
        if [ -f "$branch_file" ]; then
            local branch
            branch=$(cat "$branch_file")
            pr_number=$(gh pr list --head "$branch" --state open --json number -q '.[0].number' 2>/dev/null || true)
            if [ -n "$pr_number" ]; then
                git_state_set_pr "$worker_dir" "$pr_number"
            fi
        fi
    fi

    if [ -z "$pr_number" ] || [ "$pr_number" = "null" ]; then
        log_warn "No PR number found for $task_id - cannot attempt merge"
        return 2
    fi

    git_state_set "$worker_dir" "merging" "merge-manager.attempt_pr_merge" "Attempting merge of PR #$pr_number"
    git_state_inc_merge_attempts "$worker_dir"

    local merge_attempts
    merge_attempts=$(git_state_get_merge_attempts "$worker_dir")
    log "Attempting merge for $task_id PR #$pr_number (attempt $merge_attempts/$MAX_MERGE_ATTEMPTS)"

    local merge_output merge_exit=0
    merge_output=$(gh pr merge "$pr_number" --merge --delete-branch 2>&1) || merge_exit=$?

    if [ $merge_exit -eq 0 ]; then
        git_state_set "$worker_dir" "merged" "merge-manager.attempt_pr_merge" "PR #$pr_number merged successfully"
        log "PR #$pr_number merged successfully for $task_id"

        # Update kanban status to complete
        if [ -f "$ralph_dir/kanban.md" ]; then
            update_kanban_status "$ralph_dir/kanban.md" "$task_id" "x"
        fi
        return 0
    fi

    # Check if failure is due to merge conflict
    if echo "$merge_output" | grep -qiE "(conflict|cannot be merged|out of date)"; then
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

    # Other merge failure
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
