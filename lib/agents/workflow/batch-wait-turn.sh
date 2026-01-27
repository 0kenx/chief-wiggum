#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: batch-wait-turn
# AGENT_DESCRIPTION: Polls the batch coordination file until it's this task's
#   turn to execute. Pure bash, no LLM involved. Used in multi-PR workflows.
# REQUIRED_PATHS:
#   - batch-context.json : Worker's batch context with batch_id and position
# OUTPUT_FILES:
#   - result.json : Contains PASS (turn arrived) or FAIL (batch failed)
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "workflow.batch-wait-turn" "Wait for batch turn"

# Source dependencies
agent_source_core

# Source batch coordination
source "$WIGGUM_HOME/lib/scheduler/batch-coordination.sh"

# Configurable polling interval (seconds)
BATCH_POLL_INTERVAL="${WIGGUM_BATCH_POLL_INTERVAL:-5}"

# Maximum wait time before giving up (seconds) - default 30 minutes
BATCH_MAX_WAIT="${WIGGUM_BATCH_MAX_WAIT:-1800}"

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Set up context
    agent_setup_context "$worker_dir" "$worker_dir/workspace" "$project_dir"

    # Read batch context
    if ! batch_coord_has_worker_context "$worker_dir"; then
        log_error "No batch-context.json found in worker directory"
        agent_write_result "$worker_dir" "SKIP" '{}' '["No batch context - not part of a batch"]'
        return 0
    fi

    local batch_id task_id position total
    batch_id=$(batch_coord_read_worker_context "$worker_dir" "batch_id")
    task_id=$(batch_coord_read_worker_context "$worker_dir" "task_id")
    position=$(batch_coord_read_worker_context "$worker_dir" "position")
    total=$(batch_coord_read_worker_context "$worker_dir" "total")

    log "Waiting for turn in batch $batch_id"
    log "Task: $task_id (position $((position + 1)) of $total)"

    local start_time elapsed
    start_time=$(date +%s)

    while true; do
        # Check if it's our turn
        local turn_result=0
        batch_coord_is_my_turn "$batch_id" "$task_id" "$project_dir" || turn_result=$?

        case $turn_result in
            0)
                # It's our turn
                log "Turn arrived for $task_id"
                agent_write_result "$worker_dir" "PASS" \
                    "{\"batch_id\":\"$batch_id\",\"position\":$position,\"waited_seconds\":$(($(date +%s) - start_time))}"
                return 0
                ;;
            2)
                # Batch failed
                log_error "Batch $batch_id failed - aborting"
                agent_write_result "$worker_dir" "FAIL" \
                    "{\"batch_id\":\"$batch_id\",\"reason\":\"batch_failed\"}" \
                    '["Batch failed before this task could execute"]'
                return 0
                ;;
            *)
                # Not our turn yet
                ;;
        esac

        # Check timeout
        elapsed=$(($(date +%s) - start_time))
        if [ "$elapsed" -ge "$BATCH_MAX_WAIT" ]; then
            log_error "Timeout waiting for turn after ${elapsed}s"
            agent_write_result "$worker_dir" "FAIL" \
                "{\"batch_id\":\"$batch_id\",\"waited_seconds\":$elapsed}" \
                '["Timeout waiting for batch turn"]'
            return 0
        fi

        # Get current position for status logging
        local current_pos
        current_pos=$(batch_coord_get_position "$batch_id" "$project_dir" 2>/dev/null || echo "?")
        log "Position $((position + 1)) waiting (current: $((current_pos + 1)), elapsed: ${elapsed}s)"

        sleep "$BATCH_POLL_INTERVAL"
    done
}
