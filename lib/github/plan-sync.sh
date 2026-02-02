#!/usr/bin/env bash
# plan-sync.sh - Bidirectional sync of plan files with GitHub issue comments
#
# Syncs .ralph/plans/<TASK-ID>.md files with comments on the corresponding
# GitHub issue. Plan comments are identified by a <!-- wiggum:plan --> marker.
#
# State is tracked via plan_comment_id and plan_content_hash fields in
# .ralph/github-sync-state.json (managed by issue-state.sh).
set -euo pipefail

# Prevent double-sourcing
[ -n "${_GITHUB_PLAN_SYNC_LOADED:-}" ] && return 0
_GITHUB_PLAN_SYNC_LOADED=1

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/exit-codes.sh"
source "$WIGGUM_HOME/lib/github/issue-state.sh"

# Marker prefix for plan comments (invisible when rendered)
PLAN_COMMENT_MARKER="<!-- wiggum:plan -->"

# =============================================================================
# GitHub API Operations
# =============================================================================

# Find the plan comment on a GitHub issue
#
# Searches issue comments for one starting with the wiggum:plan marker.
# Returns JSON with "id" and "body" fields, or empty string if not found.
#
# Args:
#   issue_number - GitHub issue number
#
# Returns: JSON string on stdout, or empty string if no plan comment exists
github_plan_find_comment() {
    local issue_number="$1"

    local exit_code=0
    local result
    result=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh api \
        "repos/{owner}/{repo}/issues/${issue_number}/comments" \
        --paginate \
        --jq '[.[] | select(.body | startswith("<!-- wiggum:plan -->"))] | .[0] // empty | {id, body}' \
        2>/dev/null) || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        log_warn "Failed to fetch comments for issue #$issue_number (exit: $exit_code)"
        return 1
    fi

    echo "$result"
}

# Create a new plan comment on a GitHub issue
#
# Prepends the wiggum:plan marker to the content and posts as a comment.
#
# Args:
#   issue_number - GitHub issue number
#   content      - Plan content (without marker)
#
# Returns: comment ID on stdout, 1 on failure
github_plan_create_comment() {
    local issue_number="$1"
    local content="$2"

    local body="${PLAN_COMMENT_MARKER}
${content}"

    local exit_code=0
    local result
    result=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh api \
        "repos/{owner}/{repo}/issues/${issue_number}/comments" \
        -X POST \
        --field body="$body" \
        --jq '.id' \
        2>/dev/null) || exit_code=$?

    if [ "$exit_code" -ne 0 ] || [ -z "$result" ]; then
        log_error "Failed to create plan comment on issue #$issue_number (exit: $exit_code)"
        return 1
    fi

    echo "$result"
}

# Update an existing plan comment in-place
#
# Args:
#   comment_id - GitHub comment ID
#   content    - Plan content (without marker)
#
# Returns: 0 on success, 1 on failure
github_plan_update_comment() {
    local comment_id="$1"
    local content="$2"

    local body="${PLAN_COMMENT_MARKER}
${content}"

    local exit_code=0
    timeout "${WIGGUM_GH_TIMEOUT:-30}" gh api \
        "repos/{owner}/{repo}/issues/comments/${comment_id}" \
        -X PATCH \
        --field body="$body" \
        >/dev/null 2>&1 || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        log_error "Failed to update plan comment $comment_id (exit: $exit_code)"
        return 1
    fi
    return 0
}

# =============================================================================
# Content Helpers
# =============================================================================

# Strip the plan marker from comment body to get raw plan content
#
# Args:
#   body - Full comment body (with marker)
#
# Returns: content without marker on stdout
_strip_plan_marker() {
    local body="$1"
    # Remove marker line and the newline after it
    local stripped="${body#"${PLAN_COMMENT_MARKER}"}"
    # Remove leading newline if present
    stripped="${stripped#$'\n'}"
    echo "$stripped"
}

# =============================================================================
# Single-Task Sync
# =============================================================================

# Sync one task's plan between local file and GitHub issue comment
#
# Args:
#   ralph_dir - Path to .ralph directory
#   task_id   - Kanban task ID (e.g., "TASK-001")
#   dry_run   - "true" to preview changes without executing
#   force     - "" (none), "up" (push local), or "down" (pull remote)
#
# Returns: 0=synced/skipped, 1=conflict (no --force), 2=error
github_plan_sync_task() {
    local ralph_dir="$1"
    local task_id="$2"
    local dry_run="${3:-false}"
    local force="${4:-}"

    # Look up issue_number from sync state
    local task_state
    task_state=$(github_sync_state_get_task "$ralph_dir" "$task_id")

    if [ "$task_state" = "null" ]; then
        log_debug "Task $task_id has no sync state entry, skipping"
        return 0
    fi

    local issue_number
    issue_number=$(echo "$task_state" | jq -r '.issue_number // empty')
    if [ -z "$issue_number" ]; then
        log_debug "Task $task_id has no issue_number, skipping"
        return 0
    fi

    # Read local plan file
    local plan_file="$ralph_dir/plans/${task_id}.md"
    local local_content=""
    if [ -f "$plan_file" ]; then
        local_content=$(cat "$plan_file")
    fi

    # Fetch remote plan comment
    local remote_comment=""
    remote_comment=$(github_plan_find_comment "$issue_number") || true
    local remote_content=""
    local remote_comment_id=""
    if [ -n "$remote_comment" ]; then
        remote_comment_id=$(echo "$remote_comment" | jq -r '.id // empty')
        local remote_body
        remote_body=$(echo "$remote_comment" | jq -r '.body // empty')
        if [ -n "$remote_body" ]; then
            remote_content=$(_strip_plan_marker "$remote_body")
        fi
    fi

    # Get stored hash from sync state
    local stored_hash
    stored_hash=$(echo "$task_state" | jq -r '.plan_content_hash // empty')

    # Hash current contents
    local local_hash="" remote_hash=""
    if [ -n "$local_content" ]; then
        local_hash=$(github_sync_hash_content "$local_content")
    fi
    if [ -n "$remote_content" ]; then
        remote_hash=$(github_sync_hash_content "$remote_content")
    fi

    # Determine what changed
    local local_changed="false"
    local remote_changed="false"

    if [ -n "$local_content" ]; then
        if [ -z "$stored_hash" ] || [ "$local_hash" != "$stored_hash" ]; then
            local_changed="true"
        fi
    fi

    if [ -n "$remote_content" ]; then
        if [ -z "$stored_hash" ] || [ "$remote_hash" != "$stored_hash" ]; then
            remote_changed="true"
        fi
    fi

    # Handle case where neither side has content
    if [ -z "$local_content" ] && [ -z "$remote_content" ]; then
        log_debug "$task_id: no plan locally or remotely, skipping"
        return 0
    fi

    # Handle case where one side has content but hash matches stored (no change)
    # Also handle the case where only one side exists and no stored hash
    if [ -z "$local_content" ] && [ -n "$remote_content" ]; then
        # Remote exists, local doesn't — treat as remote changed (pull)
        remote_changed="true"
    fi
    if [ -n "$local_content" ] && [ -z "$remote_content" ]; then
        # Local exists, remote doesn't — treat as local changed (push)
        local_changed="true"
    fi

    # Decision matrix
    if [ "$local_changed" = "false" ] && [ "$remote_changed" = "false" ]; then
        log_debug "$task_id: in sync, skipping"
        return 0
    fi

    if [ "$local_changed" = "true" ] && [ "$remote_changed" = "true" ]; then
        # Both changed — conflict
        if [ "$force" = "up" ]; then
            log_info "$task_id: conflict resolved — forcing push (local wins)"
        elif [ "$force" = "down" ]; then
            log_info "$task_id: conflict resolved — forcing pull (remote wins)"
        else
            log_warn "$task_id: CONFLICT — both local and remote changed. Use --force up or --force down"
            if [ "$dry_run" = "true" ]; then
                echo "[dry-run] $task_id: CONFLICT — both local and remote changed"
            fi
            return 1
        fi
    fi

    # Determine action direction
    local action=""
    if [ "$force" = "up" ]; then
        action="push"
    elif [ "$force" = "down" ]; then
        action="pull"
    elif [ "$local_changed" = "true" ] && [ "$remote_changed" = "false" ]; then
        action="push"
    elif [ "$remote_changed" = "true" ] && [ "$local_changed" = "false" ]; then
        action="pull"
    fi

    # Execute action
    case "$action" in
        push)
            if [ -z "$local_content" ]; then
                log_debug "$task_id: nothing to push (local plan empty)"
                return 0
            fi
            if [ "$dry_run" = "true" ]; then
                if [ -n "$remote_comment_id" ]; then
                    echo "[dry-run] $task_id: would update comment $remote_comment_id on issue #$issue_number"
                else
                    echo "[dry-run] $task_id: would create comment on issue #$issue_number"
                fi
                return 0
            fi

            local new_comment_id=""
            if [ -n "$remote_comment_id" ]; then
                # Update existing comment
                github_plan_update_comment "$remote_comment_id" "$local_content" || return 2
                new_comment_id="$remote_comment_id"
                log_info "$task_id: updated plan comment on issue #$issue_number"
            else
                # Create new comment
                new_comment_id=$(github_plan_create_comment "$issue_number" "$local_content") || return 2
                log_info "$task_id: created plan comment on issue #$issue_number"
            fi

            # Update sync state
            local new_hash
            new_hash=$(github_sync_hash_content "$local_content")
            local updated_state
            updated_state=$(echo "$task_state" | jq \
                --argjson cid "$new_comment_id" \
                --arg hash "$new_hash" \
                '.plan_comment_id = $cid | .plan_content_hash = $hash')
            github_sync_state_set_task "$ralph_dir" "$task_id" "$updated_state"
            ;;

        pull)
            if [ -z "$remote_content" ]; then
                log_debug "$task_id: nothing to pull (remote plan empty)"
                return 0
            fi
            if [ "$dry_run" = "true" ]; then
                echo "[dry-run] $task_id: would write remote plan to $plan_file"
                return 0
            fi

            # Ensure plans directory exists
            mkdir -p "$ralph_dir/plans"

            # Write remote content to local file
            printf '%s\n' "$remote_content" > "$plan_file"
            log_info "$task_id: pulled plan from issue #$issue_number"

            # Update sync state
            local new_hash
            new_hash=$(github_sync_hash_content "$remote_content")
            local comment_id_val="${remote_comment_id:-null}"
            if [ "$comment_id_val" != "null" ]; then
                comment_id_val="$remote_comment_id"
            fi
            local updated_state
            updated_state=$(echo "$task_state" | jq \
                --argjson cid "${remote_comment_id:-null}" \
                --arg hash "$new_hash" \
                '.plan_comment_id = $cid | .plan_content_hash = $hash')
            github_sync_state_set_task "$ralph_dir" "$task_id" "$updated_state"
            ;;
    esac

    return 0
}

# =============================================================================
# All-Tasks Sync
# =============================================================================

# Sync plans for all tracked tasks
#
# Collects the union of local plan files and sync state entries with
# plan_comment_id, filtered to tasks that have a mapped issue_number.
#
# Args:
#   ralph_dir - Path to .ralph directory
#   dry_run   - "true" to preview changes without executing
#   force     - "" (none), "up" (push local), or "down" (pull remote)
#
# Returns: 0 on success, 1 if any conflicts
github_plan_sync_all() {
    local ralph_dir="$1"
    local dry_run="${2:-false}"
    local force="${3:-}"

    local -A task_ids=()

    # Collect from local plan files
    if [ -d "$ralph_dir/plans" ]; then
        local plan_file
        for plan_file in "$ralph_dir/plans/"*.md; do
            [ -f "$plan_file" ] || continue
            local basename
            basename=$(basename "$plan_file" .md)
            task_ids["$basename"]=1
        done
    fi

    # Collect from sync state entries with plan_comment_id
    local state_file
    state_file="$ralph_dir/github-sync-state.json"
    if [ -f "$state_file" ]; then
        local task_id
        while IFS= read -r task_id; do
            [ -n "$task_id" ] && task_ids["$task_id"]=1
        done < <(jq -r '.issues | to_entries[] | select(.value.plan_comment_id != null) | .key' "$state_file" 2>/dev/null || true)
    fi

    if [ ${#task_ids[@]} -eq 0 ]; then
        log_info "No plans to sync"
        return 0
    fi

    local had_conflict="false"
    local synced=0
    local skipped=0
    local conflicts=0
    local errors=0

    local tid
    for tid in "${!task_ids[@]}"; do
        # Only sync tasks that have a mapped issue_number
        local task_state
        task_state=$(github_sync_state_get_task "$ralph_dir" "$tid")
        if [ "$task_state" = "null" ]; then
            log_debug "$tid: no sync state, skipping"
            ((++skipped))
            continue
        fi

        local issue_number
        issue_number=$(echo "$task_state" | jq -r '.issue_number // empty')
        if [ -z "$issue_number" ]; then
            log_debug "$tid: no issue_number, skipping"
            ((++skipped))
            continue
        fi

        # Skip completed/terminal tasks to reduce API overhead
        local synced_status
        synced_status=$(echo "$task_state" | jq -r '.last_synced_status // " "')
        case "$synced_status" in
            x|"*"|N)
                log_debug "$tid: terminal status ($synced_status), skipping"
                ((++skipped))
                continue
                ;;
        esac

        local exit_code=0
        github_plan_sync_task "$ralph_dir" "$tid" "$dry_run" "$force" || exit_code=$?

        case "$exit_code" in
            0) ((++synced)) ;;
            1) ((++conflicts)); had_conflict="true" ;;
            *) ((++errors)) ;;
        esac
    done

    log_info "Plan sync: $synced synced, $skipped skipped, $conflicts conflicts, $errors errors"

    if [ "$had_conflict" = "true" ]; then
        return 1
    fi
    return 0
}

# =============================================================================
# Top-Level Dispatcher
# =============================================================================

# Main entry point for plan sync (called from wiggum-github)
#
# Args:
#   ralph_dir - Path to .ralph directory
#   task_id   - Optional task ID to sync (empty = all)
#   dry_run   - "true" to preview changes
#   force     - "" (none), "up", or "down"
#
# Returns: 0 on success, 1 on conflict, 2 on error
github_plan_sync() {
    local ralph_dir="$1"
    local task_id="${2:-}"
    local dry_run="${3:-false}"
    local force="${4:-}"

    if [ -n "$task_id" ]; then
        github_plan_sync_task "$ralph_dir" "$task_id" "$dry_run" "$force"
    else
        github_plan_sync_all "$ralph_dir" "$dry_run" "$force"
    fi
}
