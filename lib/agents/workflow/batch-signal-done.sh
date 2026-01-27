#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: batch-signal-done
# AGENT_DESCRIPTION: Signals completion of this task in the batch coordination
#   file, allowing the next task to proceed. Pure bash, no LLM involved.
# REQUIRED_PATHS:
#   - batch-context.json : Worker's batch context with batch_id
# OUTPUT_FILES:
#   - result.json : Contains PASS on success
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "workflow.batch-signal-done" "Signal batch completion"

# Source dependencies
agent_source_core

# Source batch coordination
source "$WIGGUM_HOME/lib/scheduler/batch-coordination.sh"

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Set up context
    agent_setup_context "$worker_dir" "$worker_dir/workspace" "$project_dir"

    # Check for batch context
    if ! batch_coord_has_worker_context "$worker_dir"; then
        log "No batch-context.json - not part of a batch, skipping"
        agent_write_result "$worker_dir" "SKIP" '{}' '[]'
        return 0
    fi

    local batch_id task_id
    batch_id=$(batch_coord_read_worker_context "$worker_dir" "batch_id")
    task_id=$(batch_coord_read_worker_context "$worker_dir" "task_id")

    log "Signaling completion for $task_id in batch $batch_id"

    # Mark this task as complete
    if ! batch_coord_mark_complete "$batch_id" "$task_id" "$project_dir"; then
        log_error "Failed to mark task complete in coordination file"
        agent_write_result "$worker_dir" "FAIL" \
            "{\"batch_id\":\"$batch_id\",\"task_id\":\"$task_id\"}" \
            '["Failed to update coordination file"]'
        return 1
    fi

    # Get updated status
    local status new_position
    status=$(batch_coord_get_status "$batch_id" "$project_dir")
    new_position=$(batch_coord_get_position "$batch_id" "$project_dir")

    log "Task $task_id marked complete (batch position now: $new_position, status: $status)"

    agent_write_result "$worker_dir" "PASS" \
        "{\"batch_id\":\"$batch_id\",\"task_id\":\"$task_id\",\"batch_status\":\"$status\",\"next_position\":$new_position}"
    return 0
}
