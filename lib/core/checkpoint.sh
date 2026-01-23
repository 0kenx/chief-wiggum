#!/usr/bin/env bash
# checkpoint.sh - Structured checkpoint management for agent sessions
#
# Provides functions to create, read, and manage JSON checkpoints
# alongside prose summaries. Enables robust resume capabilities.
set -euo pipefail

source "$WIGGUM_HOME/lib/core/logger.sh"

# Checkpoint schema version
CHECKPOINT_VERSION="1.0"

# Get checkpoint directory for a worker
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: Checkpoint directory path
checkpoint_get_dir() {
    local worker_dir="$1"
    echo "$worker_dir/checkpoints"
}

# Get checkpoint file path for a specific iteration
#
# Args:
#   worker_dir - Worker directory path
#   iteration  - Iteration number
#
# Returns: Checkpoint file path
checkpoint_get_path() {
    local worker_dir="$1"
    local iteration="$2"
    local checkpoint_dir
    checkpoint_dir=$(checkpoint_get_dir "$worker_dir")
    echo "$checkpoint_dir/checkpoint-${iteration}.json"
}

# Initialize checkpoint directory
#
# Args:
#   worker_dir - Worker directory path
checkpoint_init() {
    local worker_dir="$1"
    local checkpoint_dir
    checkpoint_dir=$(checkpoint_get_dir "$worker_dir")
    mkdir -p "$checkpoint_dir"
}

# Write a structured checkpoint
#
# Args:
#   worker_dir      - Worker directory path
#   iteration       - Iteration number
#   session_id      - Claude session ID
#   status          - Status: in_progress, completed, failed, interrupted
#   files_modified  - JSON array of modified file paths
#   completed_tasks - JSON array of completed task descriptions
#   next_steps      - JSON array of planned next steps
#   prose_summary   - Plain text summary (optional)
#
# Returns: 0 on success, 1 on failure
checkpoint_write() {
    local worker_dir="$1"
    local iteration="$2"
    local session_id="$3"
    local status="$4"
    local files_modified="${5:-[]}"
    local completed_tasks="${6:-[]}"
    local next_steps="${7:-[]}"
    local prose_summary="${8:-}"

    checkpoint_init "$worker_dir"

    local checkpoint_file
    checkpoint_file=$(checkpoint_get_path "$worker_dir" "$iteration")

    local timestamp
    timestamp=$(date -Iseconds)

    local worker_id task_id
    worker_id=$(basename "$worker_dir")
    task_id=$(echo "$worker_id" | sed -E 's/worker-([A-Z]+-[0-9]+)-.*/\1/' 2>/dev/null || echo "unknown")

    # Build checkpoint JSON
    cat > "$checkpoint_file" << CHECKPOINT_JSON
{
  "version": "$CHECKPOINT_VERSION",
  "iteration": $iteration,
  "session_id": "$session_id",
  "timestamp": "$timestamp",
  "status": "$status",
  "worker_id": "$worker_id",
  "task_id": "$task_id",
  "files_modified": $files_modified,
  "completed_tasks": $completed_tasks,
  "next_steps": $next_steps,
  "prose_summary": $(jq -Rs . <<< "$prose_summary")
}
CHECKPOINT_JSON

    log_debug "Checkpoint written: $checkpoint_file"
    return 0
}

# Read a checkpoint
#
# Args:
#   worker_dir - Worker directory path
#   iteration  - Iteration number (optional, defaults to latest)
#   field      - Specific field to extract (optional, uses jq syntax)
#
# Returns: Checkpoint JSON or specific field value
checkpoint_read() {
    local worker_dir="$1"
    local iteration="${2:-}"
    local field="${3:-}"

    local checkpoint_file

    if [ -z "$iteration" ]; then
        # Find latest checkpoint
        checkpoint_file=$(checkpoint_get_latest "$worker_dir")
    else
        checkpoint_file=$(checkpoint_get_path "$worker_dir" "$iteration")
    fi

    if [ ! -f "$checkpoint_file" ]; then
        log_debug "Checkpoint not found: $checkpoint_file"
        return 1
    fi

    if [ -n "$field" ]; then
        jq -r "$field // empty" "$checkpoint_file" 2>/dev/null
    else
        cat "$checkpoint_file"
    fi
}

# Get the latest checkpoint file
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: Path to latest checkpoint file, or empty if none
checkpoint_get_latest() {
    local worker_dir="$1"
    local checkpoint_dir
    checkpoint_dir=$(checkpoint_get_dir "$worker_dir")

    if [ ! -d "$checkpoint_dir" ]; then
        return 1
    fi

    # Find checkpoint with highest iteration number
    find "$checkpoint_dir" -maxdepth 1 -name "checkpoint-*.json" -printf '%f\n' 2>/dev/null | \
        sort -t'-' -k2 -n | tail -1 | while read -r file; do
            echo "$checkpoint_dir/$file"
        done
}

# Get the latest iteration number from checkpoints
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: Latest iteration number, or -1 if no checkpoints
checkpoint_get_latest_iteration() {
    local worker_dir="$1"
    local checkpoint_dir
    checkpoint_dir=$(checkpoint_get_dir "$worker_dir")

    if [ ! -d "$checkpoint_dir" ]; then
        echo "-1"
        return
    fi

    local latest_file
    latest_file=$(checkpoint_get_latest "$worker_dir")

    if [ -z "$latest_file" ] || [ ! -f "$latest_file" ]; then
        echo "-1"
        return
    fi

    jq -r '.iteration // -1' "$latest_file" 2>/dev/null || echo "-1"
}

# List all checkpoints for a worker
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: List of iteration numbers with their status
checkpoint_list() {
    local worker_dir="$1"
    local checkpoint_dir
    checkpoint_dir=$(checkpoint_get_dir "$worker_dir")

    if [ ! -d "$checkpoint_dir" ]; then
        return 0
    fi

    for checkpoint_file in "$checkpoint_dir"/checkpoint-*.json; do
        [ -f "$checkpoint_file" ] || continue

        local iteration status timestamp
        iteration=$(jq -r '.iteration' "$checkpoint_file" 2>/dev/null)
        status=$(jq -r '.status' "$checkpoint_file" 2>/dev/null)
        timestamp=$(jq -r '.timestamp' "$checkpoint_file" 2>/dev/null)

        echo "$iteration $status $timestamp"
    done | sort -n
}

# Update checkpoint status
#
# Args:
#   worker_dir - Worker directory path
#   iteration  - Iteration number
#   new_status - New status value
#
# Returns: 0 on success, 1 on failure
checkpoint_update_status() {
    local worker_dir="$1"
    local iteration="$2"
    local new_status="$3"

    local checkpoint_file
    checkpoint_file=$(checkpoint_get_path "$worker_dir" "$iteration")

    if [ ! -f "$checkpoint_file" ]; then
        log_error "Checkpoint not found: $checkpoint_file"
        return 1
    fi

    local tmp_file
    tmp_file=$(mktemp)

    jq --arg status "$new_status" '.status = $status' "$checkpoint_file" > "$tmp_file"
    mv "$tmp_file" "$checkpoint_file"

    log_debug "Checkpoint $iteration status updated to: $new_status"
    return 0
}

# Update checkpoint with prose summary
#
# Args:
#   worker_dir    - Worker directory path
#   iteration     - Iteration number
#   summary_file  - Path to summary text file
#
# Returns: 0 on success, 1 on failure
checkpoint_update_summary() {
    local worker_dir="$1"
    local iteration="$2"
    local summary_file="$3"

    local checkpoint_file
    checkpoint_file=$(checkpoint_get_path "$worker_dir" "$iteration")

    if [ ! -f "$checkpoint_file" ]; then
        log_error "Checkpoint not found: $checkpoint_file"
        return 1
    fi

    local prose_summary=""
    if [ -f "$summary_file" ]; then
        prose_summary=$(cat "$summary_file")
    fi

    local tmp_file
    tmp_file=$(mktemp)

    jq --arg summary "$prose_summary" '.prose_summary = $summary' "$checkpoint_file" > "$tmp_file"
    mv "$tmp_file" "$checkpoint_file"

    log_debug "Checkpoint $iteration updated with summary"
    return 0
}

# Update checkpoint with supervisor decision
#
# Args:
#   worker_dir   - Worker directory path
#   iteration    - Iteration number
#   decision     - Supervisor decision (CONTINUE|STOP|RESTART)
#   guidance     - Supervisor guidance text (optional)
#
# Returns: 0 on success, 1 on failure
checkpoint_update_supervisor() {
    local worker_dir="$1"
    local iteration="$2"
    local decision="$3"
    local guidance="${4:-}"

    local checkpoint_file
    checkpoint_file=$(checkpoint_get_path "$worker_dir" "$iteration")

    if [ ! -f "$checkpoint_file" ]; then
        log_error "Checkpoint not found: $checkpoint_file"
        return 1
    fi

    local tmp_file
    tmp_file=$(mktemp)

    jq --arg decision "$decision" --arg guidance "$guidance" \
        '.supervisor_decision = $decision | .supervisor_guidance = $guidance' \
        "$checkpoint_file" > "$tmp_file"
    mv "$tmp_file" "$checkpoint_file"

    log_debug "Checkpoint $iteration updated with supervisor decision: $decision"
    return 0
}

# Extract files modified from iteration log
#
# Args:
#   log_file - Path to iteration log file
#
# Returns: JSON array of file paths
checkpoint_extract_files_modified() {
    local log_file="$1"

    if [ ! -f "$log_file" ]; then
        echo "[]"
        return
    fi

    # Look for Edit, Write tool calls and extract file paths
    local files
    files=$(grep -oP '"name":"(Edit|Write)".*?"file_path":"[^"]+' "$log_file" 2>/dev/null | \
        grep -oP '"file_path":"[^"]+' | \
        sed 's/"file_path":"//g' | \
        sort -u) || true

    if [ -z "$files" ]; then
        echo "[]"
    else
        echo "$files" | jq -Rs 'split("\n") | map(select(length > 0))'
    fi
}

# Create checkpoint from iteration summary
#
# Args:
#   worker_dir   - Worker directory path
#   iteration    - Iteration number
#   session_id   - Session ID
#   status       - Status
#   log_file     - Path to iteration log (optional, for file extraction)
#   summary_file - Path to summary file (optional, for prose content)
#
# Returns: 0 on success
checkpoint_from_summary() {
    local worker_dir="$1"
    local iteration="$2"
    local session_id="$3"
    local status="$4"
    local log_file="${5:-}"
    local summary_file="${6:-}"

    local files_modified="[]"
    local prose_summary=""

    # Extract files modified from log if available
    if [ -n "$log_file" ] && [ -f "$log_file" ]; then
        files_modified=$(checkpoint_extract_files_modified "$log_file")
    fi

    # Read prose summary if available
    if [ -n "$summary_file" ] && [ -f "$summary_file" ]; then
        prose_summary=$(cat "$summary_file")
    fi

    checkpoint_write "$worker_dir" "$iteration" "$session_id" "$status" \
        "$files_modified" "[]" "[]" "$prose_summary"
}

# Check if checkpoint exists for iteration
#
# Args:
#   worker_dir - Worker directory path
#   iteration  - Iteration number
#
# Returns: 0 if exists, 1 otherwise
checkpoint_exists() {
    local worker_dir="$1"
    local iteration="$2"

    local checkpoint_file
    checkpoint_file=$(checkpoint_get_path "$worker_dir" "$iteration")
    [ -f "$checkpoint_file" ]
}
