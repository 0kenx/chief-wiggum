#!/usr/bin/env bash
# conflict-registry.sh - Track file conflicts across PRs
#
# Maintains a registry of files in conflict and which tasks/PRs have conflicts
# in each file. Used to determine whether a simple single-PR resolve or a
# multi-PR coordinated resolve is needed.
#
# Registry format (.conflict-registry.json):
# {
#   "files": {
#     "src/foo.ts": ["TASK-001", "TASK-002"],
#     "src/bar.ts": ["TASK-001"]
#   },
#   "tasks": {
#     "TASK-001": {
#       "files": ["src/foo.ts", "src/bar.ts"],
#       "pr_number": 123,
#       "added_at": "2024-01-15T10:30:00Z"
#     }
#   }
# }
set -euo pipefail

[ -n "${_CONFLICT_REGISTRY_LOADED:-}" ] && return 0
_CONFLICT_REGISTRY_LOADED=1

# Initialize conflict registry file if it doesn't exist
#
# Args:
#   ralph_dir - Ralph directory path
conflict_registry_init() {
    local ralph_dir="$1"
    local registry_file="$ralph_dir/.conflict-registry.json"

    if [ ! -f "$registry_file" ]; then
        echo '{"files": {}, "tasks": {}}' > "$registry_file"
    fi
}

# Add a task's conflicting files to the registry
#
# Args:
#   ralph_dir    - Ralph directory path
#   task_id      - Task identifier
#   pr_number    - PR number
#   files        - Newline-separated list of conflicting files
conflict_registry_add() {
    local ralph_dir="$1"
    local task_id="$2"
    local pr_number="$3"
    local files="$4"
    local registry_file="$ralph_dir/.conflict-registry.json"
    local timestamp
    timestamp=$(date -Iseconds)

    conflict_registry_init "$ralph_dir"

    # Convert newline-separated files to JSON array
    local files_json
    files_json=$(echo "$files" | jq -R -s 'split("\n") | map(select(length > 0))')

    # Update registry
    jq --arg tid "$task_id" \
       --argjson pr "$pr_number" \
       --argjson files "$files_json" \
       --arg ts "$timestamp" '
        # Add task entry
        .tasks[$tid] = {
            files: $files,
            pr_number: $pr,
            added_at: $ts
        }
        |
        # Add files to file index
        reduce ($files[]) as $file (.;
            .files[$file] = ((.files[$file] // []) + [$tid] | unique)
        )
    ' "$registry_file" > "$registry_file.tmp" && mv "$registry_file.tmp" "$registry_file"
}

# Remove a task from the registry
#
# Args:
#   ralph_dir - Ralph directory path
#   task_id   - Task identifier
conflict_registry_remove() {
    local ralph_dir="$1"
    local task_id="$2"
    local registry_file="$ralph_dir/.conflict-registry.json"

    [ -f "$registry_file" ] || return 0

    jq --arg tid "$task_id" '
        # Get files for this task
        .tasks[$tid].files as $task_files |
        # Remove task from tasks
        del(.tasks[$tid]) |
        # Remove task from each file entry
        if $task_files then
            reduce ($task_files[]) as $file (.;
                .files[$file] = (.files[$file] | map(select(. != $tid)))
            )
            # Clean up empty file entries
            | .files = (.files | with_entries(select(.value | length > 0)))
        else
            .
        end
    ' "$registry_file" > "$registry_file.tmp" && mv "$registry_file.tmp" "$registry_file"
}

# Get all tasks with conflicts in a specific file
#
# Args:
#   ralph_dir - Ralph directory path
#   file_path - File path to check
#
# Returns: Space-separated list of task IDs
conflict_registry_get_file_tasks() {
    local ralph_dir="$1"
    local file_path="$2"
    local registry_file="$ralph_dir/.conflict-registry.json"

    [ -f "$registry_file" ] || return 0

    jq -r --arg f "$file_path" '.files[$f] // [] | .[]' "$registry_file"
}

# Check if any file has conflicts in multiple PRs
#
# Args:
#   ralph_dir - Ralph directory path
#   task_id   - Task identifier to check
#
# Returns: 0 if multi-PR conflict exists, 1 otherwise
# Outputs: The conflicting files (one per line) if multi-PR conflict exists
conflict_registry_has_multi_pr_conflict() {
    local ralph_dir="$1"
    local task_id="$2"
    local registry_file="$ralph_dir/.conflict-registry.json"

    [ -f "$registry_file" ] || return 1

    # Get files for this task that have more than one task in conflict
    local multi_conflict_files
    multi_conflict_files=$(jq -r --arg tid "$task_id" '
        .tasks[$tid].files as $task_files |
        if $task_files then
            $task_files[] | select(. as $f | .files[$f] | length > 1)
        else
            empty
        end
    ' "$registry_file" 2>/dev/null)

    if [ -n "$multi_conflict_files" ]; then
        echo "$multi_conflict_files"
        return 0
    fi
    return 1
}

# Get all tasks in the registry
#
# Args:
#   ralph_dir - Ralph directory path
#
# Returns: Space-separated list of task IDs
conflict_registry_list_tasks() {
    local ralph_dir="$1"
    local registry_file="$ralph_dir/.conflict-registry.json"

    [ -f "$registry_file" ] || return 0

    jq -r '.tasks | keys[]' "$registry_file"
}

# Get conflicting files for a task
#
# Args:
#   ralph_dir - Ralph directory path
#   task_id   - Task identifier
#
# Returns: Newline-separated list of file paths
conflict_registry_get_task_files() {
    local ralph_dir="$1"
    local task_id="$2"
    local registry_file="$ralph_dir/.conflict-registry.json"

    [ -f "$registry_file" ] || return 0

    jq -r --arg tid "$task_id" '.tasks[$tid].files // [] | .[]' "$registry_file"
}

# Get PR number for a task in the registry
#
# Args:
#   ralph_dir - Ralph directory path
#   task_id   - Task identifier
#
# Returns: PR number or empty if not found
conflict_registry_get_pr() {
    local ralph_dir="$1"
    local task_id="$2"
    local registry_file="$ralph_dir/.conflict-registry.json"

    [ -f "$registry_file" ] || return 0

    jq -r --arg tid "$task_id" '.tasks[$tid].pr_number // empty' "$registry_file"
}

# Check if a task is in the registry
#
# Args:
#   ralph_dir - Ralph directory path
#   task_id   - Task identifier
#
# Returns: 0 if task is in registry, 1 otherwise
conflict_registry_has_task() {
    local ralph_dir="$1"
    local task_id="$2"
    local registry_file="$ralph_dir/.conflict-registry.json"

    [ -f "$registry_file" ] || return 1

    jq -e --arg tid "$task_id" '.tasks[$tid] != null' "$registry_file" > /dev/null 2>&1
}

# Get summary of registry state
#
# Args:
#   ralph_dir - Ralph directory path
#
# Returns: JSON summary of registry state
conflict_registry_summary() {
    local ralph_dir="$1"
    local registry_file="$ralph_dir/.conflict-registry.json"

    [ -f "$registry_file" ] || { echo '{"task_count": 0, "file_count": 0, "multi_conflict_files": 0}'; return 0; }

    jq '{
        task_count: (.tasks | length),
        file_count: (.files | length),
        multi_conflict_files: ([.files | to_entries[] | select(.value | length > 1)] | length),
        tasks: [.tasks | keys[]]
    }' "$registry_file"
}

# Clear the registry (for testing or recovery)
#
# Args:
#   ralph_dir - Ralph directory path
conflict_registry_clear() {
    local ralph_dir="$1"
    local registry_file="$ralph_dir/.conflict-registry.json"

    rm -f "$registry_file"
}
