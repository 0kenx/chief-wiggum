#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: batch-signal-failed
# AGENT_DESCRIPTION: Marks the batch as failed in the coordination file,
#   preventing remaining tasks from executing. Pure bash, no LLM involved.
#   Called when a task fails mid-batch to propagate the failure.
# REQUIRED_PATHS:
#   - batch-context.json : Worker's batch context with batch_id
# OUTPUT_FILES:
#   - result.json : Contains PASS (failure signaled successfully)
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "workflow.batch-signal-failed" "Signal batch failure"

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

    # Get failure reason from environment or step config
    local reason="${WIGGUM_FAILURE_REASON:-Task execution failed}"

    # Check for failure reason from previous step result
    local prev_result_file
    prev_result_file=$(find "$worker_dir/results" -name "*-result.json" -type f 2>/dev/null | sort | tail -2 | head -1)
    if [ -n "$prev_result_file" ] && [ -f "$prev_result_file" ]; then
        local prev_errors
        prev_errors=$(jq -r '.errors[0] // empty' "$prev_result_file" 2>/dev/null)
        if [ -n "$prev_errors" ]; then
            reason="$prev_errors"
        fi
    fi

    log_error "Signaling failure for $task_id in batch $batch_id"
    log_error "Reason: $reason"

    # Mark batch as failed
    if ! batch_coord_mark_failed "$batch_id" "$task_id" "$project_dir" "$reason"; then
        log_error "Failed to mark batch as failed in coordination file"
        agent_write_result "$worker_dir" "FAIL" \
            "{\"batch_id\":\"$batch_id\",\"task_id\":\"$task_id\"}" \
            '["Failed to update coordination file"]'
        return 1
    fi

    log "Batch $batch_id marked as failed"
    log "Remaining tasks will abort when they check for their turn"

    # Return PASS because we successfully signaled the failure
    # The batch failure is a workflow state, not an agent error
    agent_write_result "$worker_dir" "PASS" \
        "{\"batch_id\":\"$batch_id\",\"task_id\":\"$task_id\",\"reason\":\"$reason\",\"batch_status\":\"failed\"}"
    return 0
}
