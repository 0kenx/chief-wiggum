#!/usr/bin/env bash
# =============================================================================
# batch-coordination.sh - Atomic coordination for multi-PR batch operations
#
# Provides flock-protected operations on a shared coordination file that allows
# multiple isolated workers to execute in sequence. Each worker polls until it's
# their turn, executes, then signals completion for the next worker.
#
# Coordination file location: .ralph/batches/{batch_id}/coordination.json
# Worker context file: {worker_dir}/batch-context.json
#
# Usage:
#   source "$WIGGUM_HOME/lib/scheduler/batch-coordination.sh"
#   batch_coord_init "batch-123" "TASK-001,TASK-002,TASK-003" "/path/to/project"
#   batch_coord_is_my_turn "batch-123" "TASK-002" "/path/to/project" && echo "My turn!"
#   batch_coord_mark_complete "batch-123" "TASK-002" "/path/to/project"
# =============================================================================
set -euo pipefail

# Prevent double-sourcing
[ -n "${_BATCH_COORDINATION_LOADED:-}" ] && return 0
_BATCH_COORDINATION_LOADED=1

# Source file locking utilities
source "$WIGGUM_HOME/lib/core/file-lock.sh"

# =============================================================================
# COORDINATION FILE OPERATIONS
# =============================================================================

# Get the path to the coordination file for a batch
#
# Args:
#   batch_id    - Unique identifier for the batch
#   project_dir - Project root directory
#
# Returns: Path to coordination file
batch_coord_get_path() {
    local batch_id="$1"
    local project_dir="$2"
    echo "$project_dir/.ralph/batches/${batch_id}/coordination.json"
}

# Initialize a new coordination file for a batch
#
# Creates the coordination file with initial state. Should be called once
# by the planning agent before workers start executing.
#
# Args:
#   batch_id    - Unique identifier for the batch
#   task_order  - Comma-separated list of task IDs in execution order
#   project_dir - Project root directory
#
# Returns: 0 on success, 1 on failure
batch_coord_init() {
    local batch_id="$1"
    local task_order="$2"
    local project_dir="$3"

    local coord_file
    coord_file=$(batch_coord_get_path "$batch_id" "$project_dir")

    # Ensure directory exists
    mkdir -p "$(dirname "$coord_file")"

    # Convert comma-separated to JSON array
    local order_json
    order_json=$(echo "$task_order" | tr ',' '\n' | jq -R . | jq -s .)

    local total
    total=$(echo "$order_json" | jq 'length')

    # Create initial coordination file with flock
    local init_json
    init_json=$(jq -n \
        --arg batch_id "$batch_id" \
        --argjson total "$total" \
        --argjson order "$order_json" \
        '{
            batch_id: $batch_id,
            total: $total,
            current_position: 0,
            status: "executing",
            order: $order,
            completed: [],
            failed: null,
            created_at: (now | strftime("%Y-%m-%dT%H:%M:%SZ"))
        }')

    # Use flock to safely write
    with_file_lock "$coord_file" 3 \
        bash -c 'echo "$1" > "$2"' _ "$init_json" "$coord_file"
}

# Check if it's a specific task's turn to execute
#
# Args:
#   batch_id    - Batch identifier
#   task_id     - Task ID to check
#   project_dir - Project root directory
#
# Returns: 0 if it's this task's turn, 1 if not yet, 2 if batch failed
batch_coord_is_my_turn() {
    local batch_id="$1"
    local task_id="$2"
    local project_dir="$3"

    local coord_file
    coord_file=$(batch_coord_get_path "$batch_id" "$project_dir")

    if [ ! -f "$coord_file" ]; then
        return 1
    fi

    local result
    result=$(with_file_lock "$coord_file" 3 \
        bash -c '
            coord_file="$1"
            task_id="$2"

            status=$(jq -r ".status" "$coord_file")
            if [ "$status" = "failed" ]; then
                echo "failed"
                exit 0
            fi

            current_pos=$(jq -r ".current_position" "$coord_file")
            current_pos="${current_pos:-0}"
            my_pos=$(jq -r --arg tid "$task_id" ".order | to_entries[] | select(.value == \$tid) | .key" "$coord_file")

            if [ -z "$my_pos" ]; then
                echo "not_in_batch"
                exit 0
            fi

            if [ "$current_pos" -eq "$my_pos" ]; then
                echo "my_turn"
            else
                echo "waiting"
            fi
        ' _ "$coord_file" "$task_id")

    case "$result" in
        my_turn)
            return 0
            ;;
        failed)
            return 2
            ;;
        *)
            return 1
            ;;
    esac
}

# Mark a task as complete and advance to the next position
#
# Args:
#   batch_id    - Batch identifier
#   task_id     - Task ID that completed
#   project_dir - Project root directory
#
# Returns: 0 on success, 1 on failure
batch_coord_mark_complete() {
    local batch_id="$1"
    local task_id="$2"
    local project_dir="$3"

    local coord_file
    coord_file=$(batch_coord_get_path "$batch_id" "$project_dir")

    if [ ! -f "$coord_file" ]; then
        return 1
    fi

    with_file_lock "$coord_file" 5 \
        bash -c '
            coord_file="$1"
            task_id="$2"

            # Update: add to completed, advance position
            tmp_file=$(mktemp "${coord_file}.XXXXXX")
            jq --arg tid "$task_id" "
                .completed += [\$tid] |
                .current_position += 1 |
                if .current_position >= .total then .status = \"complete\" else . end |
                .updated_at = (now | strftime(\"%Y-%m-%dT%H:%M:%SZ\"))
            " "$coord_file" > "$tmp_file"
            mv "$tmp_file" "$coord_file"
        ' _ "$coord_file" "$task_id"
}

# Mark the batch as failed, preventing remaining tasks from executing
#
# Args:
#   batch_id    - Batch identifier
#   task_id     - Task ID that failed
#   project_dir - Project root directory
#   reason      - Failure reason (optional)
#
# Returns: 0 on success, 1 on failure
batch_coord_mark_failed() {
    local batch_id="$1"
    local task_id="$2"
    local project_dir="$3"
    local reason="${4:-Unknown failure}"

    local coord_file
    coord_file=$(batch_coord_get_path "$batch_id" "$project_dir")

    if [ ! -f "$coord_file" ]; then
        return 1
    fi

    with_file_lock "$coord_file" 5 \
        bash -c '
            coord_file="$1"
            task_id="$2"
            reason="$3"

            tmp_file=$(mktemp "${coord_file}.XXXXXX")
            jq --arg tid "$task_id" --arg reason "$reason" "
                .status = \"failed\" |
                .failed = {task_id: \$tid, reason: \$reason} |
                .updated_at = (now | strftime(\"%Y-%m-%dT%H:%M:%SZ\"))
            " "$coord_file" > "$tmp_file"
            mv "$tmp_file" "$coord_file"
        ' _ "$coord_file" "$task_id" "$reason"
}

# Get the current status of a batch
#
# Args:
#   batch_id    - Batch identifier
#   project_dir - Project root directory
#
# Returns: Status string: "executing", "complete", or "failed"
batch_coord_get_status() {
    local batch_id="$1"
    local project_dir="$2"

    local coord_file
    coord_file=$(batch_coord_get_path "$batch_id" "$project_dir")

    if [ ! -f "$coord_file" ]; then
        echo "not_found"
        return 1
    fi

    jq -r '.status // "unknown"' "$coord_file"
}

# Get the current position in the batch
#
# Args:
#   batch_id    - Batch identifier
#   project_dir - Project root directory
#
# Returns: Current position (0-indexed)
batch_coord_get_position() {
    local batch_id="$1"
    local project_dir="$2"

    local coord_file
    coord_file=$(batch_coord_get_path "$batch_id" "$project_dir")

    if [ ! -f "$coord_file" ]; then
        echo "-1"
        return 1
    fi

    jq -r '.current_position // -1' "$coord_file"
}

# Get the task's position in the batch order
#
# Args:
#   batch_id    - Batch identifier
#   task_id     - Task ID to find
#   project_dir - Project root directory
#
# Returns: Position (0-indexed), or -1 if not found
batch_coord_get_task_position() {
    local batch_id="$1"
    local task_id="$2"
    local project_dir="$3"

    local coord_file
    coord_file=$(batch_coord_get_path "$batch_id" "$project_dir")

    if [ ! -f "$coord_file" ]; then
        echo "-1"
        return 1
    fi

    local pos
    pos=$(jq -r --arg tid "$task_id" '.order | to_entries[] | select(.value == $tid) | .key' "$coord_file")

    if [ -z "$pos" ]; then
        echo "-1"
        return 1
    fi

    echo "$pos"
}

# Get the task ID of the next worker that should execute
#
# Args:
#   batch_id    - Batch identifier
#   project_dir - Project root directory
#
# Returns: Task ID of next worker, or empty if batch complete/failed
batch_coord_get_next_task() {
    local batch_id="$1"
    local project_dir="$2"

    local coord_file
    coord_file=$(batch_coord_get_path "$batch_id" "$project_dir")

    if [ ! -f "$coord_file" ]; then
        echo ""
        return 1
    fi

    jq -r '
        if .status == "complete" or .status == "failed" then
            ""
        elif .current_position >= .total then
            ""
        else
            .order[.current_position]
        end
    ' "$coord_file"
}

# =============================================================================
# WORKER CONTEXT FILE OPERATIONS
# =============================================================================

# Write batch context to a worker directory
#
# Creates batch-context.json in the worker directory with the task's
# batch information for use by subsequent pipeline steps.
#
# Args:
#   worker_dir  - Worker directory path
#   batch_id    - Batch identifier
#   task_id     - Task ID for this worker
#   position    - Position in the batch order (0-indexed)
#   total       - Total number of tasks in batch
#
# Returns: 0 on success
batch_coord_write_worker_context() {
    local worker_dir="$1"
    local batch_id="$2"
    local task_id="$3"
    local position="$4"
    local total="$5"

    local context_file="$worker_dir/batch-context.json"

    jq -n \
        --arg batch_id "$batch_id" \
        --arg task_id "$task_id" \
        --argjson position "$position" \
        --argjson total "$total" \
        '{
            batch_id: $batch_id,
            task_id: $task_id,
            position: $position,
            total: $total
        }' > "$context_file"
}

# Read batch context from a worker directory
#
# Args:
#   worker_dir - Worker directory path
#   field      - Optional: specific field to extract (batch_id, task_id, position, total)
#
# Returns: Full JSON or specific field value
batch_coord_read_worker_context() {
    local worker_dir="$1"
    local field="${2:-}"

    local context_file="$worker_dir/batch-context.json"

    if [ ! -f "$context_file" ]; then
        echo ""
        return 1
    fi

    if [ -n "$field" ]; then
        jq -r ".${field} // empty" "$context_file"
    else
        cat "$context_file"
    fi
}

# Check if worker has batch context
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: 0 if batch context exists, 1 otherwise
batch_coord_has_worker_context() {
    local worker_dir="$1"
    [ -f "$worker_dir/batch-context.json" ]
}
