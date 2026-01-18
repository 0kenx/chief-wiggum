#!/usr/bin/env bash
# File locking utilities for concurrent worker access

# Get the directory where this script is located
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/string-utils.sh"

# Retry a command with file locking
# Usage: with_file_lock <file> <max_retries> <command>
with_file_lock() {
    local file="$1"
    local max_retries="${2:-5}"
    local command="${@:3}"
    local lock_file="${file}.lock"
    local retry=0

    while [ $retry -lt $max_retries ]; do
        # Try to acquire lock with flock
        (
            flock -w 10 200 || exit 1

            # Execute command while holding lock
            eval "$command"

        ) 200>"$lock_file"

        local result=$?

        if [ $result -eq 0 ]; then
            # Success - clean up lock file
            rm -f "$lock_file"
            return 0
        fi

        # Failed - retry after delay
        ((retry++))
        if [ $retry -lt $max_retries ]; then
            sleep $((retry * 2))  # Exponential backoff
        fi
    done

    # All retries failed
    rm -f "$lock_file"
    return 1
}

# Update kanban.md status with locking
# Usage: update_kanban_status <kanban_file> <task_id> <new_status>
# new_status can be: [ ] (pending), [=] (in-progress), [x] (complete)
update_kanban_status() {
    local kanban_file="$1"
    local task_id="$2"
    local new_status="$3"

    # Escape special regex characters in task_id for safe use in sed pattern
    local escaped_task_id=$(escape_regex_chars "$task_id")

    # Match any status and replace with new status
    # Use | as delimiter instead of / to avoid conflicts with forward slashes in task IDs
    with_file_lock "$kanban_file" 5 \
        "sed -i 's|- \[[^\]]*\] \*\*\[$escaped_task_id\]\*\*|- [$new_status] **[$task_id]**|' '$kanban_file'"
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

# Append to changelog.md with locking
# Usage: append_changelog <changelog_file> <task_id> <worker_id> <description> <pr_url> [summary]
append_changelog() {
    local changelog_file="$1"
    local task_id="$2"
    local worker_id="$3"
    local description="$4"
    local pr_url="${5:-N/A}"
    local summary="${6:-}"
    local timestamp=$(date -Iseconds)

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
    local temp_file=$(mktemp)
    echo "$entry" > "$temp_file"

    with_file_lock "$changelog_file" 5 \
        "cat '$temp_file' >> '$changelog_file'"

    rm -f "$temp_file"
}
