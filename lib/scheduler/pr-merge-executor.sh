#!/usr/bin/env bash
# pr-merge-executor.sh - PR merge execution and orchestration
#
# Provides:
#   - Phase 4: EXECUTE - Merge PRs in optimal order
#   - Phase 5: RESOLVE - Handle remaining conflicts
#   - Main orchestration functions
#
# Split from pr-merge-optimizer.sh for maintainability.
set -euo pipefail

[ -n "${_PR_MERGE_EXECUTOR_LOADED:-}" ] && return 0
_PR_MERGE_EXECUTOR_LOADED=1
source "$WIGGUM_HOME/lib/core/safe-path.sh"
source "$WIGGUM_HOME/lib/core/lifecycle-engine.sh"

# =============================================================================
# PHASE 4: EXECUTE - Merge PRs in order with re-evaluation
# =============================================================================

# Attempt to merge a single PR
#
# Args:
#   ralph_dir - Ralph directory path
#   task_id   - Task identifier
#
# Returns: 0 on success, 1 on failure
_attempt_merge() {
    local ralph_dir="$1"
    local task_id="$2"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    local pr_number
    pr_number=$(jq -r --arg t "$task_id" '.prs[$t].pr_number' "$state_file")

    local gh_timeout="${WIGGUM_GH_TIMEOUT:-30}"

    # Squash merge via gh CLI: each task = one clean commit on main.
    # Don't use --delete-branch: worktrees conflict with local branch deletion.
    # Branch cleanup happens when worktree is removed.
    local merge_output
    merge_output=$(timeout "$gh_timeout" gh pr merge "$pr_number" --squash 2>&1) || true

    # Check if PR is now merged (handles case where merge succeeded but branch delete failed)
    local pr_state
    pr_state=$(timeout "$gh_timeout" gh pr view "$pr_number" --json state -q '.state' 2>/dev/null || echo "UNKNOWN")

    if [ "$pr_state" = "MERGED" ]; then
        log "    ✓ Merged PR #$pr_number"

        local worker_dir
        worker_dir=$(jq -r --arg t "$task_id" '.prs[$t].worker_dir' "$state_file")

        # Update PR labels (not covered by lifecycle sync_github effect)
        source "$WIGGUM_HOME/lib/github/issue-sync.sh"
        [ -n "${GITHUB_SYNC_STATUS_LABELS:-}" ] || load_github_sync_config 2>/dev/null || true
        local completed_label pending_label
        completed_label=$(github_sync_get_status_label "x" 2>/dev/null) || true
        pending_label=$(github_sync_get_status_label "P" 2>/dev/null) || true
        if [ -n "$completed_label" ]; then
            github_pr_set_status_label "$pr_number" "$completed_label" "$pending_label" || true
        fi

        # Transition via lifecycle — handles kanban, issue sync, batch cleanup,
        # worktree archive, and claim release
        if [ -n "$worker_dir" ] && [ -d "$worker_dir" ]; then
            lifecycle_is_loaded || lifecycle_load
            emit_event "$worker_dir" "merge.pr_merged" "pr-merge-executor._attempt_merge" || true
        fi

        return 0
    else
        log "    ✗ Failed to merge PR #$pr_number"
        log "      $merge_output"
        return 1
    fi
}

# Re-check merge-ability for remaining PRs after a successful merge
#
# Args:
#   ralph_dir - Ralph directory path
_refresh_merge_status() {
    local ralph_dir="$1"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    # Get remaining task IDs (not yet merged)
    local merged
    merged=$(jq -r '.merged_this_cycle[]' "$state_file" 2>/dev/null || echo "")

    local task_ids
    task_ids=$(jq -r '.prs | keys[]' "$state_file")

    while IFS= read -r task_id; do
        [ -n "$task_id" ] || continue

        # Skip if already merged
        if echo "$merged" | grep -q "^${task_id}$"; then
            continue
        fi

        local worker_dir
        worker_dir=$(jq -r --arg t "$task_id" '.prs[$t].worker_dir' "$state_file")

        if [ -d "$worker_dir/workspace" ]; then
            # Fetch latest main
            git -C "$worker_dir/workspace" fetch origin main 2>/dev/null || true

            # Re-check merge-ability
            local mergeable="true"
            local conflict_files="[]"
            local conflicts
            if conflicts=$(_check_mergeable_to_main "$worker_dir/workspace"); then
                mergeable="true"
            else
                mergeable="false"
                if [ -n "$conflicts" ]; then
                    conflict_files=$(echo "$conflicts" | jq -R -s 'split("\n") | map(select(length > 0))')
                fi
            fi

            # Update state
            jq --arg t "$task_id" --argjson m "$mergeable" --argjson cf "$conflict_files" '
                .prs[$t].mergeable_to_main = $m |
                .prs[$t].conflict_files_with_main = $cf
            ' "$state_file" > "$state_file.tmp"
            mv "$state_file.tmp" "$state_file"
        fi
    done <<< "$task_ids"
}

# Check if a PR is ready to merge (helper for pr_merge_execute)
#
# Args:
#   state_file - Path to state file
#   task_id    - Task identifier
#
# Returns: 0 if ready, 1 if not ready
# Outputs: reason string if not ready
_is_pr_ready_to_merge() {
    local state_file="$1"
    local task_id="$2"

    # Check for new comments
    local has_comments
    has_comments=$(jq -r --arg t "$task_id" '.prs[$t].has_new_comments' "$state_file")
    if [ "$has_comments" = "true" ]; then
        echo "has new comments"
        return 1
    fi

    # Check for unaddressed review requests
    local reviewed
    reviewed=$(jq -r --arg t "$task_id" '.prs[$t].copilot_reviewed' "$state_file")
    if [ "$reviewed" != "true" ]; then
        echo "has unaddressed review requests"
        return 1
    fi

    # Check if mergeable to main
    local mergeable
    mergeable=$(jq -r --arg t "$task_id" '.prs[$t].mergeable_to_main' "$state_file")
    if [ "$mergeable" != "true" ]; then
        echo "has conflicts with main"
        return 1
    fi

    return 0
}

# Execute merges in optimal order
#
# Strategy:
# 1. FIRST: Merge all independent PRs (optimal_batch from Phase 3) in one fast batch
#    - These don't conflict with each other, so no refresh needed between merges
#    - This is deterministic and fast
# 2. THEN: Handle remaining tangled PRs one at a time with refresh after each
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
#
# Returns: Number of successfully merged PRs
pr_merge_execute() {
    local ralph_dir="$1"
    local project_dir="$2"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    log "Phase 4: Executing merges..."

    # Reset merged list
    jq '.merged_this_cycle = []' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    local merged_count=0

    # =========================================================================
    # Step 1: Fast-merge independent PRs (optimal_batch from Phase 3)
    # =========================================================================
    # These PRs don't conflict with each other, so we can merge them all
    # without refreshing between each. This is the fast path.

    log "  Step 1: Merging independent PRs (no inter-PR conflicts)..."

    local optimal_batch
    optimal_batch=$(jq -r '.optimal_batch // [] | .[]' "$state_file")

    local independent_merged=0
    while IFS= read -r task_id; do
        [ -n "$task_id" ] || continue

        # Check if ready to merge
        local reason
        if reason=$(_is_pr_ready_to_merge "$state_file" "$task_id"); then
            log "    $task_id: Merging (independent)..."

            if _attempt_merge "$ralph_dir" "$task_id"; then
                # Mark as merged
                jq --arg t "$task_id" '.merged_this_cycle += [$t]' "$state_file" > "$state_file.tmp"
                mv "$state_file.tmp" "$state_file"

                ((++merged_count))
                ((++independent_merged))
            fi
        else
            log "    $task_id: Skipped ($reason)"
        fi
    done <<< "$optimal_batch"

    log "  Step 1 complete: merged $independent_merged independent PR(s)"

    # =========================================================================
    # Step 2: Handle remaining tangled PRs (with refresh after each merge)
    # =========================================================================
    # These PRs may conflict with each other, so we need to refresh merge
    # status after each successful merge to detect cascade effects.

    log "  Step 2: Merging remaining PRs (with conflict re-evaluation)..."

    local max_passes=10  # Prevent infinite loops
    local pass=0

    while [ $pass -lt $max_passes ]; do
        ((++pass))
        local merged_this_pass=0

        # Get remaining PRs not in optimal_batch
        local remaining_tasks
        remaining_tasks=$(jq -r '
            .merge_order as $order |
            .optimal_batch as $batch |
            .merged_this_cycle as $merged |
            $order | map(select(. as $t | ($batch | index($t) | not) and ($merged | index($t) | not))) | .[]
        ' "$state_file")

        [ -n "$remaining_tasks" ] || break

        while IFS= read -r task_id; do
            [ -n "$task_id" ] || continue

            # Skip if already merged (double-check)
            if jq -e --arg t "$task_id" '.merged_this_cycle | index($t)' "$state_file" >/dev/null 2>&1; then
                continue
            fi

            # Check if ready to merge
            local reason
            if reason=$(_is_pr_ready_to_merge "$state_file" "$task_id"); then
                log "    $task_id: Attempting merge..."

                if _attempt_merge "$ralph_dir" "$task_id"; then
                    # Mark as merged
                    jq --arg t "$task_id" '.merged_this_cycle += [$t]' "$state_file" > "$state_file.tmp"
                    mv "$state_file.tmp" "$state_file"

                    ((++merged_count))
                    ((++merged_this_pass))

                    # Refresh merge status for remaining PRs (may unblock others)
                    _refresh_merge_status "$ralph_dir"
                fi
            else
                log "    $task_id: Skipped ($reason)"
            fi
        done <<< "$remaining_tasks"

        # If no merges this pass, we're done
        if [ $merged_this_pass -eq 0 ]; then
            break
        fi

        log "    Pass $pass: merged $merged_this_pass PR(s), checking for newly unblocked..."
    done

    log "  Total merged: $merged_count PR(s)"
}

# =============================================================================
# PHASE 5: RESOLVE - Handle remaining conflicts
# =============================================================================

# Categorize remaining PRs and queue for appropriate resolution
#
# Categories:
# - needs_fix: Has new comments that need addressing
# - needs_resolve: Single-PR conflict (only conflicts with main, not other PRs)
# - needs_multi_resolve: Multi-PR conflict (conflicts with other unmerged PRs)
#
# Args:
#   ralph_dir - Ralph directory path
pr_merge_handle_remaining() {
    local ralph_dir="$1"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    log_debug "Phase 5: Handling remaining PRs..."

    # Initialize conflict queue
    conflict_queue_init "$ralph_dir"
    conflict_registry_init "$ralph_dir"

    # Get task IDs that weren't merged
    local merged
    merged=$(jq -r '.merged_this_cycle[]' "$state_file" 2>/dev/null || echo "")

    local task_ids
    task_ids=$(jq -r '.prs | keys[]' "$state_file")

    local needs_fix=0
    local needs_resolve=0
    local needs_multi_resolve=0
    local waiting=0

    while IFS= read -r task_id; do
        [ -n "$task_id" ] || continue

        # Skip if merged
        if echo "$merged" | grep -q "^${task_id}$"; then
            continue
        fi

        local worker_dir pr_number has_comments reviewed mergeable conflict_files
        worker_dir=$(jq -r --arg t "$task_id" '.prs[$t].worker_dir' "$state_file")
        pr_number=$(jq -r --arg t "$task_id" '.prs[$t].pr_number' "$state_file")
        has_comments=$(jq -r --arg t "$task_id" '.prs[$t].has_new_comments' "$state_file")
        reviewed=$(jq -r --arg t "$task_id" '.prs[$t].copilot_reviewed' "$state_file")
        mergeable=$(jq -r --arg t "$task_id" '.prs[$t].mergeable_to_main' "$state_file")
        conflict_files=$(jq -r --arg t "$task_id" '.prs[$t].conflict_files_with_main' "$state_file")

        # Case 1: Has new comments → needs_fix (via lifecycle engine)
        if [ "$has_comments" = "true" ]; then
            log "  $task_id: needs_fix (has new comments)"
            emit_event "$worker_dir" "pr.comments_detected" "pr-merge-executor.handle_remaining" || \
                git_state_set "$worker_dir" "needs_fix" "pr-merge-optimizer" "New comments need addressing"
            echo "$task_id" >> "$ralph_dir/orchestrator/tasks-needing-fix.txt"
            ((++needs_fix))
            continue
        fi

        # Case 2: Has unaddressed review requests → waiting
        if [ "$reviewed" != "true" ]; then
            log "  $task_id: waiting (has unaddressed review requests)"
            ((++waiting))
            continue
        fi

        # Case 3: Mergeable but wasn't merged (shouldn't happen, but handle it)
        if [ "$mergeable" = "true" ]; then
            log "  $task_id: will retry merge next cycle"
            continue
        fi

        # Case 4: Has conflicts → check if single or multi-PR
        # Check if this PR conflicts with any OTHER unmerged PR
        local conflicts_with_prs
        conflicts_with_prs=$(jq -r --arg t "$task_id" '.conflict_graph[$t] // []' "$state_file")

        local has_multi_conflict="false"
        while IFS= read -r other_task; do
            [ -n "$other_task" ] || continue
            # Check if other task is also unmerged
            if ! echo "$merged" | grep -q "^${other_task}$"; then
                has_multi_conflict="true"
                break
            fi
        done < <(echo "$conflicts_with_prs" | jq -r '.[]')

        if [ "$has_multi_conflict" = "true" ]; then
            # Check current state - don't interrupt active resolution
            local current_git_state
            current_git_state=$(git_state_get "$worker_dir")
            case "$current_git_state" in
                resolving|resolved|merging|merge_conflict)
                    log "  $task_id: active resolution (state=$current_git_state) - skipping"
                    ((++needs_multi_resolve))
                    continue
                    ;;
            esac

            # Check if this worker is already part of a planned batch
            # If so, don't override the state (planner may have already transitioned to needs_resolve)
            if [ -f "$worker_dir/batch-context.json" ]; then
                log "  $task_id: already in batch (state=$current_git_state) - skipping"
                ((++needs_multi_resolve))
                continue
            fi

            log "  $task_id: needs_multi_resolve (conflicts with other PRs)"

            # Add to conflict registry and queue
            # Use files_modified (not conflict_files_with_main) for grouping - this is
            # what determines PR-to-PR conflicts (same as Phase 2 conflict graph)
            local files_modified
            files_modified=$(jq -r --arg t "$task_id" '.prs[$t].files_modified' "$state_file")
            conflict_registry_add "$ralph_dir" "$task_id" "$pr_number" "$(echo "$files_modified" | jq -r '.[]')"
            emit_event "$worker_dir" "pr.multi_conflict_detected" "pr-merge-executor.handle_remaining" \
                "$(jq -n --arg pr "$pr_number" --argjson af "$files_modified" '{pr_number: $pr, affected_files: $af}')" || {
                conflict_queue_add "$ralph_dir" "$task_id" "$worker_dir" "$pr_number" "$files_modified"
                git_state_set "$worker_dir" "needs_multi_resolve" "pr-merge-optimizer" "Multi-PR conflict detected"
            }
            ((++needs_multi_resolve))
        else
            # Check current state - don't interrupt active resolution
            local current_git_state
            current_git_state=$(git_state_get "$worker_dir")
            case "$current_git_state" in
                resolving|resolved|merging|merge_conflict)
                    log "  $task_id: active resolution (state=$current_git_state) - skipping"
                    ((++needs_resolve))
                    continue
                    ;;
            esac

            log "  $task_id: needs_resolve (single-PR conflict with main)"

            emit_event "$worker_dir" "pr.conflict_detected" "pr-merge-executor.handle_remaining" \
                "$(jq -n --arg pr "$pr_number" --argjson af "$conflict_files" '{pr_number: $pr, affected_files: $af}')" || \
                git_state_set "$worker_dir" "needs_resolve" "pr-merge-optimizer" "Merge conflict with main"
            ((++needs_resolve))
        fi
    done <<< "$task_ids"

    log "  Summary: $needs_fix need fixes, $needs_resolve need simple resolve, $needs_multi_resolve need multi-PR resolve, $waiting waiting for review"

    # If we have multi-resolve tasks, create a batch using the merge_order from Phase 3
    if [ "$needs_multi_resolve" -gt 1 ]; then
        _create_multi_resolve_batch "$ralph_dir" "$state_file"
    fi
}

# Create a batch for multi-resolve tasks using merge_order from Phase 3
#
# This ensures we use the optimal order computed by the MIS algorithm rather
# than the conflict queue's grouping logic.
#
# Args:
#   ralph_dir  - Ralph directory path
#   state_file - PR merge state file path
_create_multi_resolve_batch() {
    local ralph_dir="$1"
    local state_file="$2"

    local queue_file="$ralph_dir/batches/queue.json"
    [ -f "$queue_file" ] || return 0

    # Get unbatched tasks from the conflict queue
    local unbatched_ids
    unbatched_ids=$(jq -r '[.queue[] | select(.batch_id == null) | .task_id]' "$queue_file")

    local unbatched_count
    unbatched_count=$(echo "$unbatched_ids" | jq 'length')

    if [ "$unbatched_count" -lt 2 ]; then
        return 0
    fi

    # Get merge_order from Phase 3 and filter to unbatched tasks only
    local merge_order
    merge_order=$(jq -r '.merge_order[]' "$state_file" 2>/dev/null || echo "")

    # Build ordered array of unbatched tasks (preserving merge_order sequence)
    local ordered_task_ids='[]'
    while IFS= read -r task_id; do
        [ -n "$task_id" ] || continue
        # Check if this task is in the unbatched set
        if echo "$unbatched_ids" | jq -e ". | index(\"$task_id\")" >/dev/null 2>&1; then
            ordered_task_ids=$(echo "$ordered_task_ids" | jq --arg t "$task_id" '. + [$t]')
        fi
    done <<< "$merge_order"

    local ordered_count
    ordered_count=$(echo "$ordered_task_ids" | jq 'length')

    if [ "$ordered_count" -lt 2 ]; then
        return 0
    fi

    log "  Creating batch for $ordered_count multi-resolve tasks (using Phase 3 merge order)"

    # Create batch using conflict_queue_create_batch
    local batch_id
    batch_id=$(conflict_queue_create_batch "$ralph_dir" "$ordered_task_ids")

    log "  Created batch $batch_id with order: $(echo "$ordered_task_ids" | jq -r 'join(" → ")')"
}

# =============================================================================
# MAIN ORCHESTRATION
# =============================================================================

# Spawn PR optimizer in background
#
# This launches pr_merge_optimize_and_execute in a background process,
# allowing the main orchestration loop to continue immediately.
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
#
# Returns: 0 if spawned (or already running), 1 on error
pr_merge_spawn_background() {
    local ralph_dir="$1"
    local project_dir="$2"
    safe_path "$ralph_dir" "ralph_dir" || return 1

    # Check if already running
    if pr_optimizer_is_running "$ralph_dir"; then
        log_debug "PR optimizer already running - skipping spawn"
        return 0
    fi

    # Clear any stale status
    pr_optimizer_clear_status "$ralph_dir"

    # Ensure log directory exists
    mkdir -p "$ralph_dir/logs"

    log "Spawning PR optimizer in background..."

    # Launch background process
    (
        # Redirect output to log file
        exec >> "$ralph_dir/logs/pr-optimizer.log" 2>&1

        # Source dependencies (needed in subshell)
        source "$WIGGUM_HOME/lib/scheduler/pr-merge-optimizer.sh"
        source "$WIGGUM_HOME/lib/tasks/task-parser.sh"

        log "Background PR optimizer started (PID: $$)"

        # Run the optimization with background mode
        pr_merge_optimize_and_execute "$ralph_dir" "$project_dir" "true"
    ) &

    local bg_pid=$!

    # Mark as started
    pr_optimizer_mark_started "$ralph_dir" "$bg_pid"

    log "PR optimizer spawned (PID: $bg_pid) - will check results on next cycle"
    return 0
}

# Run the complete PR merge optimization flow
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
#   background  - Optional: "true" if running in background mode (updates status file on completion)
#
# Returns: 0 on success
pr_merge_optimize_and_execute() {
    local ralph_dir="$1"
    local project_dir="$2"
    local background="${3:-false}"

    log "Starting PR merge optimization..."
    echo ""

    # Phase 1: Gather
    pr_merge_gather_all "$ralph_dir" "$project_dir"
    echo ""

    # Check if we have any PRs to process
    local pr_count
    pr_count=$(jq '.prs | length' "$(_pr_merge_state_file "$ralph_dir")")

    if [ "$pr_count" -eq 0 ]; then
        log "No pending PRs to process"
        # Mark completed in background mode (0 PRs merged)
        if [ "$background" = "true" ]; then
            pr_optimizer_mark_completed "$ralph_dir" 0
        fi
        return 0
    fi

    # Phase 2: Analyze
    pr_merge_build_conflict_graph "$ralph_dir"
    echo ""

    # Phase 3: Optimize
    pr_merge_find_optimal_order "$ralph_dir"
    echo ""

    # Phase 4: Execute
    pr_merge_execute "$ralph_dir" "$project_dir"
    echo ""

    # Phase 5: Handle remaining
    pr_merge_handle_remaining "$ralph_dir"
    echo ""

    # Get merged count from state file (more reliable than capturing stdout)
    local merged
    merged=$(jq -r '.merged_this_cycle | length' "$(_pr_merge_state_file "$ralph_dir")" 2>/dev/null || echo "0")

    log "PR merge optimization complete (merged $merged PRs)"

    # Mark completed in background mode
    if [ "$background" = "true" ]; then
        pr_optimizer_mark_completed "$ralph_dir" "$merged"
    fi
}

# Get statistics from the current state
#
# Args:
#   ralph_dir - Ralph directory path
#
# Returns: JSON object with stats
pr_merge_stats() {
    local ralph_dir="$1"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    [ -f "$state_file" ] || { echo '{}'; return 0; }

    jq '{
        total_prs: (.prs | length),
        merged: (.merged_this_cycle | length),
        mergeable: [.prs | to_entries[] | select(.value.mergeable_to_main == true)] | length,
        with_conflicts: [.prs | to_entries[] | select(.value.mergeable_to_main == false)] | length,
        with_comments: [.prs | to_entries[] | select(.value.has_new_comments == true)] | length,
        conflict_pairs: ([.conflict_graph | to_entries[] | .value | length] | add // 0 | . / 2)
    }' "$state_file"
}
