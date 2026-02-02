#!/usr/bin/env bash
# File locking utilities for concurrent worker access
set -euo pipefail

source "$WIGGUM_HOME/lib/core/platform.sh"

# =============================================================================
# APPEND WITH LOCK (Common Pattern)
# =============================================================================
# Consolidates duplicate flock-based append implementations from:
#   - activity-log.sh
#   - audit-logger.sh

# Append content to a file with flock protection
#
# Uses flock for safe concurrent appends from multiple workers.
# Lock file is NOT removed after use (avoids TOCTOU race conditions).
#
# Args:
#   file    - File to append to
#   content - Content to append
#   timeout - Lock timeout in seconds (default: 2)
#
# Returns: 0 on success (or if lock fails, content is still written)
append_with_lock() {
    local file="$1"
    local content="$2"
    local timeout="${3:-2}"
    local lock_file="${file}.lock"

    (
        flock -w "$timeout" 200 || {
            # Lock failed, write directly (better than losing data)
            echo "$content" >> "$file"
            exit 0
        }
        echo "$content" >> "$file"
    ) 200>"$lock_file"
}

# Retry a command with file locking
# Usage: with_file_lock <file> <max_retries> <command>
#
# Only retries on lock acquisition failure (flock timeout).
# If the lock is acquired but the command itself fails,
# returns the command's exit code immediately (no retry).
with_file_lock() {
    local file="$1"
    local max_retries="${2:-5}"
    shift 2
    local lock_file="${file}.lock"
    local retry=0
    local _lock_fail=200  # Sentinel exit code for lock acquisition failure

    while [ $retry -lt "$max_retries" ]; do
        # Try to acquire lock with flock
        # Note: lock file is intentionally NOT removed after use.
        # Removing it creates a TOCTOU race where concurrent processes
        # can hold locks on different inodes simultaneously.
        local result=0
        (
            flock -w 10 200 || exit "$_lock_fail"

            # Execute command while holding lock
            "$@"

        ) 200>"$lock_file" || result=$?

        if [ $result -eq 0 ]; then
            return 0
        fi

        # Command itself failed (lock was acquired) - return immediately
        if [ $result -ne "$_lock_fail" ]; then
            return $result
        fi

        # Lock acquisition failed - retry after delay
        ((++retry))
        if [ $retry -lt "$max_retries" ]; then
            sleep $((retry * 2))  # Exponential backoff
        fi
    done

    return 1
}

# Update kanban.md status with locking
# Usage: update_kanban_status <kanban_file> <task_id> <new_status>
# new_status can be: [ ] (pending), [=] (in-progress), [P] (pending approval),
#                    [x] (merged/complete), [N] (not planned), [*] (failed)
update_kanban_status() {
    local kanban_file="$1"
    local task_id="$2"
    local new_status="$3"

    # Escape all sed special characters in task_id
    # Includes: ] \ [ ^ $ . * & /
    # The order matters: ] and \ must be escaped first in the character class
    local escaped_task_id
    escaped_task_id=$(printf '%s' "$task_id" | sed 's/[]\[^$.*&/\\]/\\&/g')

    # Match any status and replace with new status
    # Security: Use umask 077 to ensure sed -i temp files have restricted permissions
    # Pass variables via environment to avoid shell injection through quotes
    # Note: Inline OS check for portable sed -i (GNU vs BSD)
    _SED_ESCAPED_TASK_ID="$escaped_task_id" \
    _SED_NEW_STATUS="$new_status" \
    with_file_lock "$kanban_file" 5 \
        bash -c 'umask 077; sed_i() { if [[ "$OSTYPE" == darwin* ]]; then sed -i "" "$@"; else sed -i "$@"; fi; }; sed_i "s/- \[[^\]]*\] \*\*\[$_SED_ESCAPED_TASK_ID\]\*\*/- [$_SED_NEW_STATUS] **[$_SED_ESCAPED_TASK_ID]**/" "$1"' _ "$kanban_file"
}

# Update kanban.md to mark complete with locking (convenience function)
# Usage: update_kanban <kanban_file> <task_id>
update_kanban() {
    update_kanban_status "$1" "$2" "x"
}

# Update kanban.md to mark failed with locking (convenience function)
# Usage: update_kanban_failed <kanban_file> <task_id>
update_kanban_failed() {
    update_kanban_status "$1" "$2" "*"
}

# Update kanban.md to mark pending approval with locking (convenience function)
# Usage: update_kanban_pending_approval <kanban_file> <task_id>
update_kanban_pending_approval() {
    update_kanban_status "$1" "$2" "P"
}

# Update kanban.md to mark not planned with locking (convenience function)
# Usage: update_kanban_not_planned <kanban_file> <task_id>
update_kanban_not_planned() {
    update_kanban_status "$1" "$2" "N"
}

# =============================================================================
# KANBAN TASK MANAGEMENT (Used by GitHub Issue Sync)
# =============================================================================

# Add a new task entry to kanban.md under flock
#
# Inserts at the end of the TASKS section. Double-checks under lock
# that the task doesn't already exist.
#
# Args:
#   kanban_file - Path to kanban.md
#   task_id     - Task ID (e.g., "GH-42")
#   brief       - Brief description
#   description - Detailed description (optional)
#   priority    - Priority level (CRITICAL|HIGH|MEDIUM|LOW)
#   dependencies - Dependencies string (e.g., "GH-10, GH-15" or "none")
#   extra_fields - Additional fields as "key1: value1\nkey2: value2" (optional)
#
# Returns: 0 on success, 1 if duplicate
add_kanban_task() {
    local kanban_file="$1"
    local task_id="$2"
    local brief="$3"
    local description="${4:-}"
    local priority="${5:-MEDIUM}"
    local dependencies="${6:-none}"
    local extra_fields="${7:-}"

    # Collapse multi-line description to single line (kanban format requires it)
    if [[ "$description" == *$'\n'* ]]; then
        description=$(echo "$description" | tr '\n' ' ' | sed 's/  */ /g; s/^ *//; s/ *$//')
    fi

    # Build the task block via direct string construction (safe — no format interpretation)
    local task_block
    task_block="- [ ] **[${task_id}]** ${brief}"$'\n'
    if [ -n "$description" ]; then
        task_block="${task_block}  - Description: ${description}"$'\n'
    fi
    task_block="${task_block}  - Priority: ${priority}"$'\n'
    task_block="${task_block}  - Dependencies: ${dependencies}"$'\n'

    # Add any extra fields (scope, complexity, acceptance criteria, etc.)
    if [ -n "$extra_fields" ]; then
        while IFS= read -r field_line; do
            [ -n "$field_line" ] || continue
            task_block="${task_block}  - ${field_line}"$'\n'
        done <<< "$extra_fields"
    fi

    # Use environment variables for lock safety (no shell injection via quotes)
    _AKT_TASK_ID="$task_id" \
    _AKT_TASK_BLOCK="$task_block" \
    with_file_lock "$kanban_file" 5 \
        bash -c '
            # Double-check: task must not already exist
            if grep -qF "**[$_AKT_TASK_ID]**" "$1" 2>/dev/null; then
                exit 1  # Duplicate
            fi
            # Append to end of file
            printf "\n%s" "$_AKT_TASK_BLOCK" >> "$1"
        ' _ "$kanban_file"
}

# Update fields of an existing kanban task under flock
#
# Updates Description, Priority, and Dependencies of a pending task.
# Only modifies fields that are provided (non-empty).
#
# Args:
#   kanban_file  - Path to kanban.md
#   task_id      - Task ID (e.g., "GH-42")
#   description  - New description (empty = no change)
#   priority     - New priority (empty = no change)
#   dependencies - New dependencies (empty = no change)
#
# Returns: 0 on success, 1 if task not found
update_kanban_task_fields() {
    local kanban_file="$1"
    local task_id="$2"
    local description="${3:-}"
    local priority="${4:-}"
    local dependencies="${5:-}"

    # Collapse multi-line description to single line (kanban format requires it)
    if [[ -n "$description" && "$description" == *$'\n'* ]]; then
        description=$(echo "$description" | tr '\n' ' ' | sed 's/  */ /g; s/^ *//; s/ *$//')
    fi

    # Pass fields via environment to avoid injection
    _UKTF_TASK_ID="$task_id" \
    _UKTF_DESC="$description" \
    _UKTF_PRI="$priority" \
    _UKTF_DEPS="$dependencies" \
    with_file_lock "$kanban_file" 5 \
        bash -c '
            # Verify task exists
            if ! grep -qF "**[$_UKTF_TASK_ID]**" "$1" 2>/dev/null; then
                exit 1  # Task not found
            fi

            # Use awk to update fields in place
            awk_script=$(cat <<'"'"'AWKEOF'"'"'
BEGIN { in_task = 0; found = 0; task_pat = "\\*\\*\\[" TASK_ID "\\]\\*\\*" }
$0 ~ task_pat {
    in_task = 1
    found = 1
    print
    next
}
in_task && /^  - Description:/ && DESC != "" {
    print "  - Description: " DESC
    next
}
in_task && /^  - Priority:/ && PRI != "" {
    print "  - Priority: " PRI
    next
}
in_task && /^  - Dependencies:/ && DEPS != "" {
    print "  - Dependencies: " DEPS
    next
}
# End of task block (next task line or non-indented line)
in_task && /^- \[/ { in_task = 0 }
in_task && /^[^[:space:]]/ && !/^$/ { in_task = 0 }
{ print }
END { if (!found) exit 1 }
AWKEOF
)
            tmp_file=$(mktemp "${1}.XXXXXX")
            if awk -v TASK_ID="$_UKTF_TASK_ID" \
                   -v DESC="$_UKTF_DESC" \
                   -v PRI="$_UKTF_PRI" \
                   -v DEPS="$_UKTF_DEPS" \
                   "$awk_script" "$1" > "$tmp_file"; then
                mv "$tmp_file" "$1"
            else
                rm -f "$tmp_file"
                exit 1
            fi
        ' _ "$kanban_file"
}

# Append to changelog.md with locking
# Usage: append_changelog <changelog_file> <task_id> <worker_id> <description> <pr_url> [summary]
append_changelog() {
    local changelog_file="$1"
    local task_id="$2"
    local worker_id="$3"
    local description="$4"
    local pr_url="${5:-N/A}"
    local summary="${6:-}"
    local timestamp
    timestamp=$(iso_now)

    local entry="
## [$task_id] - $timestamp

- **Description**: $description
- **Worker**: $worker_id
- **PR**: $pr_url
- **Status**: Completed
"

    # Add detailed summary if provided
    if [ -n "$summary" ]; then
        entry="${entry}
### Summary

${summary}
"
    fi

    # Use a temporary file to handle multi-line content safely
    local temp_file
    temp_file=$(mktemp)
    echo "$entry" > "$temp_file"

    # shellcheck disable=SC2016
    with_file_lock "$changelog_file" 5 \
        bash -c 'cat "$1" >> "$2"' _ "$temp_file" "$changelog_file"

    rm -f "$temp_file"
}
