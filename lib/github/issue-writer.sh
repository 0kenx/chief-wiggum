#!/usr/bin/env bash
# issue-writer.sh - Write status updates back to GitHub issues
#
# Manages GitHub issue labels, comments, and open/close state.
# All API calls use timeout and error handling via gh CLI.
set -euo pipefail

# Prevent double-sourcing
[ -n "${_GITHUB_ISSUE_WRITER_LOADED:-}" ] && return 0
_GITHUB_ISSUE_WRITER_LOADED=1

# =============================================================================
# Label Management
# =============================================================================

# Add a label to a GitHub issue
#
# Args:
#   issue_number - GitHub issue number
#   label        - Label name to add
#
# Returns: 0 on success, 1 on failure
github_issue_add_label() {
    local issue_number="$1"
    local label="$2"

    local exit_code=0
    timeout "${WIGGUM_GH_TIMEOUT:-30}" gh issue edit "$issue_number" \
        --add-label "$label" >/dev/null 2>&1 || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        log_warn "Failed to add label '$label' to issue #$issue_number (exit: $exit_code)"
        return 1
    fi
    return 0
}

# Remove a label from a GitHub issue
#
# Args:
#   issue_number - GitHub issue number
#   label        - Label name to remove
#
# Returns: 0 on success, 1 on failure (label might not exist)
github_issue_remove_label() {
    local issue_number="$1"
    local label="$2"

    local exit_code=0
    timeout "${WIGGUM_GH_TIMEOUT:-30}" gh issue edit "$issue_number" \
        --remove-label "$label" >/dev/null 2>&1 || exit_code=$?

    # Label removal failure is non-critical (label might not be present)
    if [ "$exit_code" -ne 0 ]; then
        log_debug "Could not remove label '$label' from issue #$issue_number (may not exist)"
    fi
    return 0
}

# Remove all wiggum status labels from an issue, then add the new one
#
# Status labels are mutually exclusive. This removes any existing status
# label before adding the new one.
#
# Args:
#   issue_number - GitHub issue number
#   new_label    - New status label to set (empty = remove all status labels)
#   old_label    - Previous status label to remove (empty = skip removal)
#
# Returns: 0 on success
github_issue_set_status_label() {
    local issue_number="$1"
    local new_label="${2:-}"
    local old_label="${3:-}"

    # Remove old status label if present and different from new
    if [ -n "$old_label" ] && [ "$old_label" != "$new_label" ]; then
        github_issue_remove_label "$issue_number" "$old_label"
    fi

    # Add new status label if present
    if [ -n "$new_label" ]; then
        github_issue_add_label "$issue_number" "$new_label"
    fi
}

# =============================================================================
# Comment Management
# =============================================================================

# Post a comment on a GitHub issue
#
# Args:
#   issue_number - GitHub issue number
#   body         - Comment body text
#
# Returns: 0 on success, 1 on failure
github_issue_post_comment() {
    local issue_number="$1"
    local body="$2"

    local exit_code=0
    timeout "${WIGGUM_GH_TIMEOUT:-30}" gh issue comment "$issue_number" \
        --body "$body" >/dev/null 2>&1 || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        log_warn "Failed to post comment on issue #$issue_number (exit: $exit_code)"
        return 1
    fi
    return 0
}

# Post a status transition comment
#
# Args:
#   issue_number - GitHub issue number
#   old_status   - Previous human-readable status (e.g., "pending")
#   new_status   - New human-readable status (e.g., "in-progress")
#
# Returns: 0 on success
github_issue_post_transition_comment() {
    local issue_number="$1"
    local old_status="$2"
    local new_status="$3"

    local body="wiggum: status changed — ${old_status} → ${new_status}"
    github_issue_post_comment "$issue_number" "$body"
}

# Post a PR link comment (only once per issue)
#
# Args:
#   issue_number - GitHub issue number
#   pr_url       - Pull request URL
#
# Returns: 0 on success
github_issue_post_pr_link() {
    local issue_number="$1"
    local pr_url="$2"

    local body="wiggum: pull request created — $pr_url"
    github_issue_post_comment "$issue_number" "$body"
}

# =============================================================================
# Issue Creation
# =============================================================================

# Create a new GitHub issue for a kanban task
#
# Args:
#   task_id - Kanban task ID (e.g., "TASK-001")
#   brief   - Short task summary for title
#   body    - Issue body text (description, fields, etc.)
#   labels  - Space-separated label names (optional, beyond gate label)
#
# Returns: issue number on stdout, 1 on failure
github_issue_create() {
    local task_id="$1"
    local brief="$2"
    local body="${3:-}"
    shift 3
    local labels=("$@")

    local title="[$task_id] $brief"

    # Build label args — always include gate label
    local gate_label="${GITHUB_SYNC_LABEL_FILTER:-wiggum}"
    local label_args=()
    label_args+=(--label "$gate_label")
    local label
    for label in "${labels[@]}"; do
        [[ -n "$label" && "$label" != "$gate_label" ]] && \
            label_args+=(--label "$label")
    done

    local result stderr_file exit_code=0
    stderr_file=$(mktemp)

    result=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh issue create \
        --title "$title" \
        --body "$body" \
        "${label_args[@]}" \
        2>"$stderr_file") || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        local err_output
        err_output=$(cat "$stderr_file" 2>/dev/null)
        rm -f "$stderr_file"
        log_error "Failed to create GitHub issue for $task_id (exit: $exit_code): $err_output"
        return 1
    fi
    rm -f "$stderr_file"

    # gh issue create outputs the issue URL; extract number from it
    local issue_number
    issue_number=$(echo "$result" | grep -oE '/issues/[0-9]+' | grep -oE '[0-9]+' | tail -1)

    if [ -z "$issue_number" ]; then
        log_error "Could not parse issue number from gh output: $result"
        return 1
    fi

    echo "$issue_number"
}

# =============================================================================
# Issue State Management
# =============================================================================

# Close a GitHub issue
#
# Args:
#   issue_number - GitHub issue number
#
# Returns: 0 on success, 1 on failure
github_issue_close() {
    local issue_number="$1"

    local exit_code=0
    timeout "${WIGGUM_GH_TIMEOUT:-30}" gh issue close "$issue_number" \
        >/dev/null 2>&1 || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        log_warn "Failed to close issue #$issue_number (exit: $exit_code)"
        return 1
    fi
    return 0
}

# Reopen a GitHub issue
#
# Args:
#   issue_number - GitHub issue number
#
# Returns: 0 on success, 1 on failure
github_issue_reopen() {
    local issue_number="$1"

    local exit_code=0
    timeout "${WIGGUM_GH_TIMEOUT:-30}" gh issue reopen "$issue_number" \
        >/dev/null 2>&1 || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        log_warn "Failed to reopen issue #$issue_number (exit: $exit_code)"
        return 1
    fi
    return 0
}

# =============================================================================
# High-Level Status Update
# =============================================================================

# Map kanban status char to human-readable name
#
# Args:
#   status_char - Single kanban status character
#
# Returns: human-readable name on stdout
_kanban_status_name() {
    local status_char="$1"
    case "$status_char" in
        " ") echo "pending" ;;
        "=") echo "in-progress" ;;
        "P") echo "pending-approval" ;;
        "x") echo "completed" ;;
        "*") echo "failed" ;;
        "N") echo "not-planned" ;;
        *)   echo "unknown" ;;
    esac
}

# Perform a full status update on a GitHub issue
#
# Handles label changes, state changes (close/reopen), and transition comments.
#
# Args:
#   issue_number   - GitHub issue number
#   new_status     - New kanban status char
#   old_status     - Previous kanban status char
#   old_state      - Previous GitHub issue state ("open" or "closed")
#   dry_run        - "true" to only log changes without making them
#
# Returns: 0 on success
github_issue_update_status() {
    local issue_number="$1"
    local new_status="$2"
    local old_status="$3"
    local old_state="${4:-open}"
    local dry_run="${5:-false}"

    # Determine label changes
    local new_label old_label
    new_label=$(github_sync_get_status_label "$new_status")
    old_label=$(github_sync_get_status_label "$old_status")

    # Determine state changes
    local should_close="false"
    local should_reopen="false"

    if github_sync_should_close "$new_status"; then
        if [ "$old_state" = "open" ]; then
            should_close="true"
        fi
    else
        # Not a close_on status — reopen if issue was closed by a previous close_on status
        if [ "$old_state" = "closed" ] && github_sync_should_close "$old_status"; then
            should_reopen="true"
        fi
    fi

    local old_name new_name
    old_name=$(_kanban_status_name "$old_status")
    new_name=$(_kanban_status_name "$new_status")

    if [ "$dry_run" = "true" ]; then
        echo "[dry-run] Issue #$issue_number: $old_name -> $new_name"
        [ -n "$old_label" ] && [ "$old_label" != "$new_label" ] && \
            echo "  - Remove label: $old_label"
        [ -n "$new_label" ] && echo "  + Add label: $new_label"
        [ "$should_close" = "true" ] && echo "  * Close issue"
        [ "$should_reopen" = "true" ] && echo "  * Reopen issue"
        return 0
    fi

    # Apply label changes
    github_issue_set_status_label "$issue_number" "$new_label" "$old_label"

    # Apply state changes
    if [ "$should_close" = "true" ]; then
        github_issue_close "$issue_number"
    elif [ "$should_reopen" = "true" ]; then
        github_issue_reopen "$issue_number"
    fi

}

# =============================================================================
# Failure Summary Posting
# =============================================================================

# Post failure analysis summary to GitHub issue
#
# Posts the failure analysis generated by failure-summarizer agent to the
# linked GitHub issue, keeping stakeholders informed about task failures.
#
# Args:
#   ralph_dir   - Path to .ralph directory
#   task_id     - Task ID (e.g., "GH-42")
#   summary_md  - Markdown summary content
#
# Returns: 0 on success, 1 on failure
github_issue_post_failure_summary() {
    local ralph_dir="$1"
    local task_id="$2"
    local summary_md="$3"

    # No-op if no sync state exists
    [ -f "$ralph_dir/github-sync-state.json" ] || return 0

    # Get issue number from sync state
    local entry
    entry=$(jq -r --arg tid "$task_id" '.issues[$tid] // "null"' "$ralph_dir/github-sync-state.json" 2>/dev/null)
    [ "$entry" != "null" ] || return 0

    local issue_number
    issue_number=$(echo "$entry" | jq -r '.issue_number')
    [ -n "$issue_number" ] && [ "$issue_number" != "null" ] || return 0

    local body
    body="## Failure Analysis

$summary_md

---
_Generated by Chief Wiggum failure recovery pipeline_"

    github_issue_post_comment "$issue_number" "$body"
}
