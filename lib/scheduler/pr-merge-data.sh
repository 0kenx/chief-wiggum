#!/usr/bin/env bash
# pr-merge-data.sh - Data gathering for PR merge optimization
#
# Provides:
#   - Background optimizer status tracking
#   - PR data gathering (Phase 1: GATHER)
#   - Comment checking utilities
#
# Split from pr-merge-optimizer.sh for maintainability.
set -euo pipefail

[ -n "${_PR_MERGE_DATA_LOADED:-}" ] && return 0
_PR_MERGE_DATA_LOADED=1
source "$WIGGUM_HOME/lib/core/platform.sh"

# =============================================================================
# Background Optimizer Status Tracking
# =============================================================================

# Get path to optimizer status file
_pr_optimizer_status_file() {
    echo "$1/.pr-optimizer-status.json"
}

# Check if PR optimizer is currently running
pr_optimizer_is_running() {
    local ralph_dir="$1"
    local status_file
    status_file=$(_pr_optimizer_status_file "$ralph_dir")

    [ -f "$status_file" ] || return 1

    local status pid
    status=$(jq -r '.status // "unknown"' "$status_file" 2>/dev/null)
    pid=$(jq -r '.pid // 0' "$status_file" 2>/dev/null)

    [ "$status" = "running" ] || return 1
    [ "$pid" != "0" ] && [ "$pid" != "null" ] || return 1

    kill -0 "$pid" 2>/dev/null
}

# Mark optimizer as started
pr_optimizer_mark_started() {
    local ralph_dir="$1"
    local pid="$2"
    local status_file
    status_file=$(_pr_optimizer_status_file "$ralph_dir")

    jq -n \
        --arg status "running" \
        --argjson pid "$pid" \
        --arg started_at "$(TZ=UTC iso_now)" \
        '{status: $status, pid: $pid, started_at: $started_at}' > "$status_file"
}

# Mark optimizer as completed
pr_optimizer_mark_completed() {
    local ralph_dir="$1"
    local merged_count="$2"
    local status_file
    status_file=$(_pr_optimizer_status_file "$ralph_dir")

    [ -f "$status_file" ] || return 0

    jq \
        --arg status "completed" \
        --argjson merged_count "$merged_count" \
        --arg completed_at "$(TZ=UTC iso_now)" \
        '. + {status: $status, merged_count: $merged_count, completed_at: $completed_at}' \
        "$status_file" > "$status_file.tmp"
    mv "$status_file.tmp" "$status_file"
}

# Mark optimizer as failed
pr_optimizer_mark_failed() {
    local ralph_dir="$1"
    local error="$2"
    local status_file
    status_file=$(_pr_optimizer_status_file "$ralph_dir")

    [ -f "$status_file" ] || return 0

    jq \
        --arg status "failed" \
        --arg error "$error" \
        --arg completed_at "$(TZ=UTC iso_now)" \
        '. + {status: $status, error: $error, completed_at: $completed_at}' \
        "$status_file" > "$status_file.tmp"
    mv "$status_file.tmp" "$status_file"
}

# Check if optimizer completed and get result
pr_optimizer_check_completion() {
    local ralph_dir="$1"
    local status_file
    status_file=$(_pr_optimizer_status_file "$ralph_dir")

    [ -f "$status_file" ] || return 1

    local status
    status=$(jq -r '.status // "unknown"' "$status_file" 2>/dev/null)

    case "$status" in
        completed)
            jq -r '.merged_count // 0' "$status_file"
            return 0
            ;;
        failed)
            local error
            error=$(jq -r '.error // "unknown error"' "$status_file" 2>/dev/null)
            log_error "PR optimizer failed: $error"
            echo "0"
            return 0
            ;;
        running)
            local pid
            pid=$(jq -r '.pid // 0' "$status_file" 2>/dev/null)
            if [ "$pid" != "0" ] && [ "$pid" != "null" ] && ! kill -0 "$pid" 2>/dev/null; then
                pr_optimizer_mark_failed "$ralph_dir" "Process died unexpectedly"
                echo "0"
                return 0
            fi
            return 1
            ;;
        *)
            return 1
            ;;
    esac
}

# Clear optimizer status file
pr_optimizer_clear_status() {
    local ralph_dir="$1"
    rm -f "$(_pr_optimizer_status_file "$ralph_dir")"
}

# =============================================================================
# Cleanup and Utility Functions
# =============================================================================

# Clean up worker directory after PR is merged
#
# Unregisters the git worktree, then removes the entire worker directory.
#
# Args:
#   worker_dir - Worker directory path
_cleanup_merged_worktree() {
    local worker_dir="$1"
    local workspace="$worker_dir/workspace"

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
    if [ -d "$worker_dir" ]; then
        rm -rf "$worker_dir" 2>/dev/null
        if [ -d "$worker_dir" ]; then
            sleep 1
            rm -rf "$worker_dir" 2>/dev/null || true
        fi
    fi

    log "      Worker directory removed"
}

# Check if pr-comment-fix agent completed successfully (PASS)
_check_fix_agent_passed() {
    local worker_dir="$1"
    local results_dir="$worker_dir/results"

    [ -d "$results_dir" ] || return 1

    local latest_result
    latest_result=$(find "$results_dir" -name "*pr-comment-fix*.json" -type f 2>/dev/null | sort -r | head -1)

    [ -n "$latest_result" ] && [ -f "$latest_result" ] || return 1

    local gate_result
    gate_result=$(jq -r '.gate_result // empty' "$latest_result" 2>/dev/null)

    [ "$gate_result" = "PASS" ]
}

# Check if there are new comments since the last fix commit
_check_for_new_comments_since_commit() {
    local task_comments_file="$1"

    local main_content
    main_content=$(sed -n '1,/^## Commit$/p' "$task_comments_file" 2>/dev/null | head -n -1)

    local current_ids
    current_ids=$(echo "$main_content" | grep -oE '\*\*ID:\*\* [0-9]+' | grep -oE '[0-9]+' | sort -u)

    if [ -z "$current_ids" ]; then
        echo "false"
        return
    fi

    local commit_section
    commit_section=$(sed -n '/^## Commit$/,$ p' "$task_comments_file" 2>/dev/null)

    local addressed_ids
    addressed_ids=$(echo "$commit_section" | grep -oE 'Comment [0-9]+' | grep -oE '[0-9]+' | sort -u)

    if [ -z "$addressed_ids" ]; then
        echo "true"
        return
    fi

    local new_comments="false"
    while IFS= read -r id; do
        [ -z "$id" ] && continue
        if ! echo "$addressed_ids" | grep -q "^${id}$"; then
            new_comments="true"
            break
        fi
    done <<< "$current_ids"

    echo "$new_comments"
}

# =============================================================================
# PHASE 1: GATHER - Collect data on all pending PRs
# =============================================================================

# Get list of files modified by a PR branch compared to main
_get_files_modified() {
    local workspace="$1"

    cd "$workspace" || return 1

    git fetch origin main 2>/dev/null || true

    local merge_base
    merge_base=$(git merge-base HEAD origin/main 2>/dev/null || echo "")

    if [ -z "$merge_base" ]; then
        echo "[]"
        return 0
    fi

    local files
    files=$(git diff --name-only "$merge_base" HEAD 2>/dev/null || echo "")

    if [ -z "$files" ]; then
        echo "[]"
    else
        echo "$files" | jq -R -s 'split("\n") | map(select(length > 0))'
    fi
}

# Check if PR can merge cleanly into current main
_check_mergeable_to_main() {
    local workspace="$1"

    cd "$workspace" || return 1

    git fetch origin main 2>/dev/null || true

    local merge_base head_commit main_commit
    merge_base=$(git merge-base HEAD origin/main 2>/dev/null || echo "")
    head_commit=$(git rev-parse HEAD 2>/dev/null)
    main_commit=$(git rev-parse origin/main 2>/dev/null)

    if [ -z "$merge_base" ]; then
        return 1
    fi

    local merge_output
    merge_output=$(git merge-tree "$merge_base" "$head_commit" "$main_commit" 2>&1 || true)

    if echo "$merge_output" | grep -q '^<<<<<<<\|^=======\|^>>>>>>>'; then
        echo "$merge_output" | grep -E '^\+\+\+ |^changed in' | \
            sed 's/^+++ //' | sed 's/^changed in .* //' | \
            sort -u
        return 1
    fi

    local stash_result
    stash_result=$(git stash -q 2>&1 || echo "no_stash")

    if git merge --no-commit --no-ff origin/main 2>/dev/null; then
        git merge --abort 2>/dev/null || true
        [ "$stash_result" != "no_stash" ] && git stash pop -q 2>/dev/null || true
        return 0
    else
        git diff --name-only --diff-filter=U 2>/dev/null || true
        git merge --abort 2>/dev/null || true
        [ "$stash_result" != "no_stash" ] && git stash pop -q 2>/dev/null || true
        return 1
    fi
}

# Gather data for a single PR
_gather_pr_data() {
    local ralph_dir="$1"
    local task_id="$2"
    local worker_dir="$3"
    local pr_number="$4"

    local workspace="$worker_dir/workspace"

    local branch=""
    if [ -d "$workspace" ]; then
        branch=$(git -C "$workspace" rev-parse --abbrev-ref HEAD 2>/dev/null || echo "")
    fi

    local base_commit=""
    if [ -d "$workspace" ]; then
        base_commit=$(git -C "$workspace" merge-base HEAD origin/main 2>/dev/null || echo "")
    fi

    local files_modified="[]"
    if [ -d "$workspace" ]; then
        files_modified=$(_get_files_modified "$workspace")
    fi

    local has_new_comments="false"
    if [ -f "$worker_dir/task-comments.md" ]; then
        local comment_count
        comment_count=$(grep -c '^### ' "$worker_dir/task-comments.md" 2>/dev/null) || comment_count=0
        comment_count="${comment_count:-0}"
        if [[ "$comment_count" =~ ^[0-9]+$ ]] && [ "$comment_count" -gt 0 ]; then
            if grep -q '^## Commit$' "$worker_dir/task-comments.md" 2>/dev/null; then
                has_new_comments=$(_check_for_new_comments_since_commit "$worker_dir/task-comments.md")
            elif _check_fix_agent_passed "$worker_dir"; then
                has_new_comments="false"
            elif [ -f "$worker_dir/reports/comment-status.md" ]; then
                local pending
                pending=$(grep -c '^\- \[ \]' "$worker_dir/reports/comment-status.md" 2>/dev/null) || pending=0
                pending="${pending:-0}"
                [[ "$pending" =~ ^[0-9]+$ ]] && [ "$pending" -gt 0 ] && has_new_comments="true"
            else
                has_new_comments="true"
            fi
        fi
    fi

    # Fetch PR reviews from GitHub and filter by approved user IDs.
    # If approved_user_ids is configured, require an APPROVED review from one
    # of those IDs before allowing merge (usernames are not trusted).
    # Ensure review config is loaded (sets WIGGUM_APPROVED_USER_IDS from config.json)
    if [ -z "${WIGGUM_APPROVED_USER_IDS:-}" ]; then
        source "$WIGGUM_HOME/lib/core/defaults.sh"
        load_review_config
    fi
    local _approved_ids="${WIGGUM_APPROVED_USER_IDS:-}"
    local copilot_reviewed="false"

    # No approved user IDs configured → no review gate
    if [ -z "$_approved_ids" ]; then
        copilot_reviewed="true"
    elif [ -d "$workspace" ]; then
        local _remote_url _repo _reviews_json
        _remote_url=$(git -C "$workspace" remote get-url origin 2>/dev/null || echo "")
        _repo=""
        if [[ "$_remote_url" =~ github\.com[:/]([^/]+/[^/.]+) ]]; then
            _repo="${BASH_REMATCH[1]}"
            _repo="${_repo%.git}"
        fi
        if [ -n "$_repo" ]; then
            _reviews_json=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh api "repos/$_repo/pulls/$pr_number/reviews" \
                --jq '[.[] | {user_id: .user.id, state: .state, submitted_at: .submitted_at}]' \
                2>/dev/null || echo "")
            if [ -n "$_reviews_json" ] && [ "$_reviews_json" != "[]" ] && [ "$_reviews_json" != "null" ]; then
                echo "$_reviews_json" > "$worker_dir/pr-reviews.json"
            fi
        fi
        # Check reviews from approved user IDs only.
        # Any completed review (APPROVED, COMMENTED, CHANGES_REQUESTED) satisfies the gate.
        # The has_new_comments check separately handles whether comments need fixing.
        if [ -f "$worker_dir/pr-reviews.json" ]; then
            local _latest_approved_state
            _latest_approved_state=$(jq -r --arg ids "$_approved_ids" '
                ($ids | split(",") | map(gsub("^\\s+|\\s+$"; "") | tonumber)) as $allowed |
                [.[] | select(.user_id as $uid | $allowed | any(. == $uid))] |
                sort_by(.submitted_at) | last | .state // "NONE"
            ' "$worker_dir/pr-reviews.json" 2>/dev/null || echo "NONE")
            if [ "$_latest_approved_state" != "NONE" ]; then
                copilot_reviewed="true"
            fi
        fi
    fi

    local mergeable_to_main="true"
    local conflict_files_with_main="[]"
    if [ -d "$workspace" ]; then
        local conflicts
        if conflicts=$(_check_mergeable_to_main "$workspace"); then
            mergeable_to_main="true"
            conflict_files_with_main="[]"
        else
            mergeable_to_main="false"
            if [ -n "$conflicts" ]; then
                conflict_files_with_main=$(echo "$conflicts" | jq -R -s 'split("\n") | map(select(length > 0))')
            fi
        fi
    fi

    jq -n \
        --arg task_id "$task_id" \
        --argjson pr_number "$pr_number" \
        --arg worker_dir "$worker_dir" \
        --arg branch "$branch" \
        --arg base_commit "$base_commit" \
        --argjson files_modified "$files_modified" \
        --argjson has_new_comments "$has_new_comments" \
        --argjson copilot_reviewed "$copilot_reviewed" \
        --argjson mergeable_to_main "$mergeable_to_main" \
        --argjson conflict_files_with_main "$conflict_files_with_main" \
        '{
            pr_number: $pr_number,
            worker_dir: $worker_dir,
            branch: $branch,
            base_commit: $base_commit,
            files_modified: $files_modified,
            has_new_comments: $has_new_comments,
            copilot_reviewed: $copilot_reviewed,
            mergeable_to_main: $mergeable_to_main,
            conflict_files_with_main: $conflict_files_with_main
        }'
}

# Gather data for all pending PRs
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
#
# Populates the prs object in pr-merge-state.json
pr_merge_gather_all() {
    local ralph_dir="$1"
    # shellcheck disable=SC2034  # project_dir is part of API signature for consistency
    local project_dir="$2"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    # Initialize state
    pr_merge_init "$ralph_dir"

    log_debug "Phase 1: Gathering PR data..."

    local count=0

    # Find all 'P' tasks with PRs
    for worker_dir in "$ralph_dir/workers"/worker-*; do
        [ -d "$worker_dir" ] || continue

        # Skip plan workers
        [[ "$(basename "$worker_dir")" == *"-plan-"* ]] && continue

        # Must have workspace
        [ -d "$worker_dir/workspace" ] || continue

        # Skip if running
        if [ -f "$worker_dir/worker.pid" ]; then
            local pid
            pid=$(cat "$worker_dir/worker.pid")
            if ps -p "$pid" >/dev/null 2>&1; then
                continue
            fi
        fi

        local task_id
        task_id=$(basename "$worker_dir" | sed 's/worker-\([A-Za-z]*-[0-9]*\)-.*/\1/')

        # Check if task is pending approval
        local task_status
        task_status=$(grep -E "^\- \[.\] \*\*\[$task_id\]" "$ralph_dir/kanban.md" 2>/dev/null | \
            sed 's/^- \[\(.\)\].*/\1/' || echo "")
        [ "$task_status" = "P" ] || continue

        # Skip workers in failed state (max merge attempts exceeded, etc.)
        local git_state
        git_state=$(git_state_get "$worker_dir" 2>/dev/null || echo "")
        if [ "$git_state" = "failed" ]; then
            log_debug "  Skipping $task_id: worker in failed state"
            continue
        fi

        # Skip workers with incomplete fix pipeline
        # Only merge PRs that either never entered fix flow (empty/none state)
        # or completed it (needs_merge/fix_completed state)
        if [ -n "$git_state" ] && [ "$git_state" != "none" ] && [ "$git_state" != "needs_merge" ] && [ "$git_state" != "fix_completed" ]; then
            log_debug "  Skipping $task_id: fix pipeline incomplete (state: $git_state)"
            continue
        fi

        # Get PR number (with backfill)
        local pr_number
        pr_number=$(git_state_get_pr "$worker_dir" 2>/dev/null || echo "")
        if { [ -z "$pr_number" ] || [ "$pr_number" = "null" ]; } && [ -f "$worker_dir/pr_url.txt" ]; then
            local pr_url
            pr_url=$(cat "$worker_dir/pr_url.txt")
            pr_number=$(echo "$pr_url" | grep -oE '[0-9]+$' || true)
            if [ -n "$pr_number" ]; then
                git_state_set_pr "$worker_dir" "$pr_number" 2>/dev/null || true
            fi
        fi
        [ -n "$pr_number" ] && [ "$pr_number" != "null" ] || continue

        # Sync PR comments
        "$WIGGUM_HOME/bin/wiggum-review" task "$task_id" sync 2>/dev/null || true

        # Check if PR is already merged on GitHub (sync may have detected this)
        local pr_state
        pr_state=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh pr view "$pr_number" --json state -q '.state' 2>/dev/null || echo "UNKNOWN")
        if [ "$pr_state" = "MERGED" ]; then
            log "  $task_id (PR #$pr_number): Already merged - cleaning up"
            # Update kanban to complete
            update_kanban_status "$ralph_dir/kanban.md" "$task_id" "x" 2>/dev/null || true
            # Clean up batch coordination before workspace deletion
            if batch_coord_has_worker_context "$worker_dir"; then
                local batch_id
                batch_id=$(batch_coord_read_worker_context "$worker_dir" "batch_id")
                if [ -n "$batch_id" ]; then
                    local project_dir
                    project_dir=$(dirname "$ralph_dir")
                    batch_coord_mark_complete "$batch_id" "$task_id" "$project_dir"
                fi
            fi
            # Delete workspace
            _cleanup_merged_worktree "$worker_dir"
            continue
        fi

        # Gather PR data
        log_debug "  $task_id: gathering (PR #$pr_number)"
        local pr_data
        pr_data=$(_gather_pr_data "$ralph_dir" "$task_id" "$worker_dir" "$pr_number")

        # Add to state
        jq --arg task_id "$task_id" --argjson pr_data "$pr_data" \
            '.prs[$task_id] = $pr_data' "$state_file" > "$state_file.tmp"
        mv "$state_file.tmp" "$state_file"

        ((++count))
    done

    log "Gathered $count PR(s) for merge optimization"

    # Update timestamp
    jq '.last_updated = (now | strftime("%Y-%m-%dT%H:%M:%SZ"))' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"
}
