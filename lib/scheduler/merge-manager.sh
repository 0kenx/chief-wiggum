#!/usr/bin/env bash
# merge-manager.sh - PR merge workflow management
#
# Handles the PR merge lifecycle:
#   - Attempting merges
#   - Detecting conflicts
#   - Transitioning state for retry/resolution
#   - Updating kanban status on success
#   - Queueing conflicts for multi-PR coordination
#
# State transitions are driven by the lifecycle engine (emit_event).
# See config/worker-lifecycle.json for the spec.
set -euo pipefail

[ -n "${_MERGE_MANAGER_LOADED:-}" ] && return 0
_MERGE_MANAGER_LOADED=1

# Source dependencies
source "$WIGGUM_HOME/lib/worker/git-state.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"
source "$WIGGUM_HOME/lib/tasks/task-parser.sh"
source "$WIGGUM_HOME/lib/scheduler/conflict-queue.sh"
source "$WIGGUM_HOME/lib/scheduler/batch-coordination.sh"
source "$WIGGUM_HOME/lib/core/safe-path.sh"
source "$WIGGUM_HOME/lib/core/lifecycle-engine.sh"
source "$WIGGUM_HOME/lib/github/issue-sync.sh"
source "$WIGGUM_HOME/lib/core/agent-result.sh"

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

    # Note: conflict queue removal is handled by rm_conflict_queue lifecycle effect
    # (not duplicated here to avoid redundancy with lifecycle transitions)
}

# Clean up worker directory after PR is merged
#
# Unregisters the git worktree, removes the workspace checkout to save space,
# then moves the remaining worker directory (logs, output, reports, activity)
# to .ralph/history/ for post-merge inspection.
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

    # Remove workspace checkout to save disk space (retry for busy files)
    safe_path "$workspace" "workspace" || return 1
    rm -rf "$workspace" 2>/dev/null
    if [ -d "$workspace" ]; then
        sleep 1
        rm -rf "$workspace" 2>/dev/null || true
    fi

    # Archive remaining worker dir (logs, output, reports, activity) to history
    if [ -d "$worker_dir" ]; then
        local ralph_dir
        ralph_dir=$(dirname "$(dirname "$worker_dir")")
        local history_dir="$ralph_dir/history"
        mkdir -p "$history_dir"
        mv "$worker_dir" "$history_dir/$worker_name" 2>/dev/null || true
    fi

    log "Worker archived to history for $worker_name"
}

# Emit merge.conflict + conflict.needs_resolve events
#
# Shared by pre-merge conflict detection and post-merge conflict handling.
# Computes affected files for multi-PR tracking before emitting events.
#
# Args:
#   worker_dir - Worker directory path
#   pr_number  - PR number
#   error_msg  - Error description for audit trail
_mm_emit_conflict() {
    local worker_dir="$1"
    local pr_number="$2"
    local error_msg="$3"

    local affected_files='[]'
    local workspace="$worker_dir/workspace"
    if [ -d "$workspace" ]; then
        local changed_files
        local default_branch
        default_branch=$(get_default_branch)
        changed_files=$(git -C "$workspace" diff --name-only "origin/$default_branch" 2>/dev/null | head -50 || true)
        if [ -n "$changed_files" ]; then
            affected_files=$(echo "$changed_files" | jq -R -s 'split("\n") | map(select(length > 0))')
        fi
    fi

    local data_json
    data_json=$(jq -n \
        --arg e "$error_msg" \
        --argjson pr "$pr_number" \
        --argjson af "$affected_files" \
        '{error: $e, pr_number: $pr, affected_files: $af}')

    emit_event "$worker_dir" "merge.conflict" "merge-manager.attempt_pr_merge" "$data_json"
    emit_event "$worker_dir" "conflict.needs_resolve" "merge-manager.attempt_pr_merge"
}

# Check if a PR has an approved review from a configured user ID
#
# Reuses the review-checking logic from pr-merge-data.sh. Checks the cached
# pr-reviews.json first; fetches from GitHub API if no cache exists.
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier (for logging)
#
# Returns:
#   0 - PR has an approved review
#   1 - No approved review (merge blocked)
_check_merge_approved() {
    local worker_dir="$1"
    local task_id="$2"

    # Load review config if not already loaded (sets WIGGUM_APPROVED_USER_IDS)
    if [ -z "${WIGGUM_APPROVED_USER_IDS:-}" ]; then
        source "$WIGGUM_HOME/lib/core/defaults.sh"
        load_review_config
    fi

    local approved_ids="${WIGGUM_APPROVED_USER_IDS:-}"

    # No approved IDs configured → block merge (secure by default)
    if [ -z "$approved_ids" ]; then
        log_debug "Merge blocked for $task_id — no WIGGUM_APPROVED_USER_IDS configured"
        return 1
    fi

    # Fetch reviews if no cache exists
    if [ ! -f "$worker_dir/pr-reviews.json" ]; then
        local pr_number
        pr_number=$(git_state_get_pr "$worker_dir")
        if [ -z "$pr_number" ] || [ "$pr_number" = "null" ]; then
            log_debug "Merge blocked for $task_id — no PR number, cannot check reviews"
            return 1
        fi

        local workspace="$worker_dir/workspace"
        local remote_url repo=""
        if [ -d "$workspace" ]; then
            remote_url=$(git -C "$workspace" remote get-url origin 2>/dev/null || echo "")
            if [[ "$remote_url" =~ github\.com[:/]([^/]+/[^/.]+) ]]; then
                repo="${BASH_REMATCH[1]}"
                repo="${repo%.git}"
            fi
        fi

        if [ -n "$repo" ]; then
            local reviews_json
            reviews_json=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh api "repos/$repo/pulls/$pr_number/reviews" \
                --jq '[.[] | {user_id: .user.id, state: .state, submitted_at: .submitted_at}]' \
                2>/dev/null || echo "")
            if [ -n "$reviews_json" ] && [ "$reviews_json" != "[]" ] && [ "$reviews_json" != "null" ]; then
                echo "$reviews_json" > "$worker_dir/pr-reviews.json"
            fi
        fi
    fi

    # Check reviews from approved user IDs
    if [ -f "$worker_dir/pr-reviews.json" ]; then
        local latest_state
        latest_state=$(jq -r --arg ids "$approved_ids" '
            ($ids | split(",") | map(gsub("^\\s+|\\s+$"; "") | tonumber)) as $allowed |
            [.[] | select(.user_id as $uid | $allowed | any(. == $uid))] |
            sort_by(.submitted_at) | last | .state // "NONE"
        ' "$worker_dir/pr-reviews.json" 2>/dev/null || echo "NONE")
        if [ "$latest_state" != "NONE" ]; then
            return 0
        fi
    fi

    log_debug "Merge blocked for $task_id — no approved review found"
    return 1
}

# Check pipeline results gate before allowing merge
#
# Blocks merge if test or validation results indicate failure.
# UNKNOWN results are allowed (fix workers don't write test results,
# custom pipelines may omit the test step).
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier (for logging)
#
# Returns:
#   0 - Pipeline results pass (or unknown)
#   1 - Pipeline results block merge
_check_pipeline_results() {
    local worker_dir="$1"
    local task_id="$2"

    local test_result
    test_result=$(agent_read_step_result "$worker_dir" "test")
    if [ "$test_result" = "FIX" ] || [ "$test_result" = "FAIL" ]; then
        log_debug "Merge blocked for $task_id - test result: $test_result"
        return 1
    fi

    local validation_result
    validation_result=$(agent_read_step_result "$worker_dir" "validation")
    if [ "$validation_result" = "FAIL" ]; then
        log_debug "Merge blocked for $task_id - validation result: FAIL"
        return 1
    fi

    return 0
}

# Attempt to merge a PR for a worker
#
# Uses the lifecycle engine (emit_event) for all state transitions.
# The engine handles guard evaluation, kanban updates, and side effects
# according to config/worker-lifecycle.json.
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier
#   ralph_dir  - Ralph directory path (for kanban updates)
#
# Returns:
#   0 - Merge succeeded
#   1 - Merge conflict (needs resolver) or retry needed
#   2 - Other failure (unrecoverable)
attempt_pr_merge() {
    local worker_dir="$1"
    local task_id="$2"
    local ralph_dir="$3"

    # Ensure lifecycle spec is loaded
    lifecycle_is_loaded || lifecycle_load

    # Gate: require approved review before attempting merge
    if ! _check_merge_approved "$worker_dir" "$task_id"; then
        log_debug "PR merge blocked for $task_id - no approved review"
        return 1
    fi

    # Gate: require passing pipeline results before attempting merge
    if ! _check_pipeline_results "$worker_dir" "$task_id"; then
        log_debug "PR merge blocked for $task_id - pipeline results not passing"
        return 1
    fi

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

    # Attempt to start merge via lifecycle engine.
    # Guard merge_attempts_lt_max determines the path:
    #   pass → merging + inc_merge_attempts
    #   fail → failed  + check_permanent (fallback)
    emit_event "$worker_dir" "merge.start" "merge-manager.attempt_pr_merge"

    local post_start_state
    post_start_state=$(git_state_get "$worker_dir")
    if [ "$post_start_state" = "failed" ]; then
        log_error "Max merge attempts reached for $task_id - cannot attempt merge"
        return 2
    fi

    local merge_attempts
    merge_attempts=$(git_state_get_merge_attempts "$worker_dir")
    log "Attempting merge for $task_id PR #$pr_number (attempt $merge_attempts/$MAX_MERGE_ATTEMPTS)"

    # Wait for GitHub to determine mergeable status before attempting merge.
    # After a push, GitHub returns UNKNOWN while recalculating - calling
    # gh pr merge during this window fails with "not mergeable".
    local poll_result=0
    _wait_for_mergeable "$pr_number" "$task_id" || poll_result=$?

    if [ "$poll_result" -eq 1 ]; then
        # PR has conflicts - skip straight to conflict handling
        log "PR #$pr_number has conflicts (detected before merge attempt)"
        _mm_emit_conflict "$worker_dir" "$pr_number" "Merge conflict detected via mergeable status"

        local conflict_state
        conflict_state=$(git_state_get "$worker_dir")
        if [ "$conflict_state" = "failed" ]; then
            log_error "Max merge attempts exceeded for $task_id"
            return 2
        fi
        log "Merge conflict for $task_id - will spawn resolver"
        return 1
    fi
    # poll_result=2 (timeout/unknown) - proceed with merge attempt anyway

    local merge_output merge_exit=0
    # Squash merge: each task is one logical change → one commit on main.
    # Don't use --delete-branch: worktrees conflict with local branch deletion.
    # Branch cleanup happens when worktree is removed after merge.
    merge_output=$(gh pr merge "$pr_number" --squash 2>&1) || merge_exit=$?

    if [ $merge_exit -eq 0 ]; then
        log "PR #$pr_number merged successfully for $task_id"
        emit_event "$worker_dir" "merge.succeeded" "merge-manager.attempt_pr_merge" \
            "$(jq -n --argjson pr "$pr_number" '{pr_number: $pr}')"
        return 0
    fi

    # Check if PR was already merged (gh returns error but this is actually success)
    if echo "$merge_output" | grep -qi "already merged"; then
        log "PR #$pr_number was already merged for $task_id"
        emit_event "$worker_dir" "merge.already_merged" "merge-manager.attempt_pr_merge" \
            "$(jq -n --argjson pr "$pr_number" '{pr_number: $pr}')"
        return 0
    fi

    # Check failure type - distinguish between conflicts and other issues
    #
    # "out of date" / "branch is behind" = needs rebase, NOT a conflict
    # "local changes would be overwritten" = dirty working tree, NOT a conflict
    # Only "conflict" or "cannot be merged" with actual conflict markers = real conflict

    # "Out of date" — branch is behind main. Rebase recovery via guard.
    # Guard _guard_rebase_succeeded does fetch+rebase+force-push as a side effect.
    # If guard passes: → needs_merge (ready for retry)
    # If guard fails:  → failed + set_error + check_permanent (fallback)
    if echo "$merge_output" | grep -qiE "(out of date|branch.*behind|is not up to date)"; then
        log "Branch out of date for $task_id — attempting rebase recovery"
        emit_event "$worker_dir" "merge.out_of_date" "merge-manager.attempt_pr_merge" \
            "$(jq -n --arg e "Branch out of date and rebase recovery failed: $merge_output" \
                     --arg ws "$worker_dir/workspace" \
                     '{error: $e, workspace: $ws}')"

        local ood_state
        ood_state=$(git_state_get "$worker_dir")
        if [ "$ood_state" = "needs_merge" ]; then
            log "Rebase recovery succeeded for $task_id — retrying merge"
            return 1
        fi
        log_error "Merge failed for $task_id: branch out of date, rebase recovery failed"
        return 2
    fi

    # Dirty working tree — hard failure
    if echo "$merge_output" | grep -qiE "(local changes.*overwritten|uncommitted changes|working tree.*not clean)"; then
        emit_event "$worker_dir" "merge.hard_fail" "merge-manager.attempt_pr_merge" \
            "$(jq -n --arg e "Dirty working tree: $merge_output" '{error: $e}')"
        log_error "Merge failed for $task_id: working tree has uncommitted changes"
        return 2
    fi

    # Actual merge conflict
    if echo "$merge_output" | grep -qiE "(conflict|cannot be merged)"; then
        _mm_emit_conflict "$worker_dir" "$pr_number" "Merge conflict: $merge_output"

        local conflict_state
        conflict_state=$(git_state_get "$worker_dir")
        if [ "$conflict_state" = "failed" ]; then
            log_error "Max merge attempts exceeded for $task_id"
            return 2
        fi
        log "Merge conflict for $task_id - will spawn resolver"
        return 1
    fi

    # "not mergeable" is transient after a push - GitHub may still be processing.
    # Guard merge_attempts_lt_max determines the path:
    #   pass → needs_merge (will retry)
    #   fail → failed + set_error + check_permanent (fallback)
    if echo "$merge_output" | grep -qiE "not mergeable"; then
        emit_event "$worker_dir" "merge.transient_fail" "merge-manager.attempt_pr_merge" \
            "$(jq -n --arg e "Transient: $merge_output" '{error: $e}')"

        local transient_state
        transient_state=$(git_state_get "$worker_dir")
        if [ "$transient_state" = "needs_merge" ]; then
            log_warn "Merge not yet ready for $task_id (attempt $merge_attempts/$MAX_MERGE_ATTEMPTS) - will retry"
            return 1
        fi
        log_error "Max merge attempts exceeded for $task_id"
        return 2
    fi

    # Other merge failure (unrecoverable)
    emit_event "$worker_dir" "merge.hard_fail" "merge-manager.attempt_pr_merge" \
        "$(jq -n --arg e "Merge failed: $merge_output" '{error: $e}')"
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
