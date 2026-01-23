#!/usr/bin/env bash
# event-emitter.sh - Structured event logging for observability
#
# Emits JSON events to .ralph/logs/events.jsonl for querying and analysis.
# Events follow a consistent schema with type, timestamp, and context.
set -euo pipefail

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"

# Default events log location
EVENTS_LOG="${EVENTS_LOG:-}"

# Get events log path for project
#
# Args:
#   project_dir - Project directory (optional, defaults to PROJECT_DIR)
#
# Returns: Path to events.jsonl
_get_events_log() {
    local project_dir="${1:-${PROJECT_DIR:-.}}"
    echo "$project_dir/.ralph/logs/events.jsonl"
}

# Initialize events log (creates file and directory if needed)
#
# Args:
#   project_dir - Project directory (optional)
events_init() {
    local project_dir="${1:-${PROJECT_DIR:-.}}"
    local events_log
    events_log=$(_get_events_log "$project_dir")
    local events_dir
    events_dir=$(dirname "$events_log")

    if [ ! -d "$events_dir" ]; then
        mkdir -p "$events_dir"
    fi

    if [ ! -f "$events_log" ]; then
        touch "$events_log"
    fi

    EVENTS_LOG="$events_log"
}

# Emit a generic event
#
# Args:
#   event_type - Event type (e.g., "task.started", "iteration.completed")
#   data       - Additional JSON object data (without braces)
#
# Example:
#   emit_event "task.started" '"task_id": "TASK-001", "worker_id": "worker-TASK-001-123"'
emit_event() {
    local event_type="$1"
    local data="${2:-}"

    # Initialize if not already done
    if [ -z "$EVENTS_LOG" ]; then
        events_init
    fi

    local timestamp
    timestamp=$(date -Iseconds)

    local event_json
    if [ -n "$data" ]; then
        event_json="{\"timestamp\":\"$timestamp\",\"event_type\":\"$event_type\",$data}"
    else
        event_json="{\"timestamp\":\"$timestamp\",\"event_type\":\"$event_type\"}"
    fi

    # Write with file locking to prevent race conditions
    local lock_file="$EVENTS_LOG.lock"
    (
        flock -w 5 200 || {
            # Lock failed, write directly
            echo "$event_json" >> "$EVENTS_LOG"
            exit 0
        }
        echo "$event_json" >> "$EVENTS_LOG"
    ) 200>"$lock_file"
}

# Emit task started event
#
# Args:
#   task_id   - Task identifier
#   worker_id - Worker identifier
emit_task_started() {
    local task_id="$1"
    local worker_id="$2"

    emit_event "task.started" "\"task_id\":\"$task_id\",\"worker_id\":\"$worker_id\""
    log_debug "Event: task.started task_id=$task_id worker_id=$worker_id"
}

# Emit task completed event
#
# Args:
#   task_id   - Task identifier
#   worker_id - Worker identifier
#   result    - Result: PASS, FAIL, etc.
emit_task_completed() {
    local task_id="$1"
    local worker_id="$2"
    local result="$3"

    emit_event "task.completed" "\"task_id\":\"$task_id\",\"worker_id\":\"$worker_id\",\"result\":\"$result\""
    log_debug "Event: task.completed task_id=$task_id result=$result"
}

# Emit task failed event
#
# Args:
#   task_id   - Task identifier
#   worker_id - Worker identifier
#   reason    - Failure reason
emit_task_failed() {
    local task_id="$1"
    local worker_id="$2"
    local reason="$3"

    emit_event "task.failed" "\"task_id\":\"$task_id\",\"worker_id\":\"$worker_id\",\"reason\":\"$reason\""
    log_debug "Event: task.failed task_id=$task_id reason=$reason"
}

# Emit iteration started event
#
# Args:
#   worker_id - Worker identifier
#   iteration - Iteration number
#   session_id - Claude session ID
emit_iteration_started() {
    local worker_id="$1"
    local iteration="$2"
    local session_id="$3"

    emit_event "iteration.started" "\"worker_id\":\"$worker_id\",\"iteration\":$iteration,\"session_id\":\"$session_id\""
}

# Emit iteration completed event
#
# Args:
#   worker_id  - Worker identifier
#   iteration  - Iteration number
#   exit_code  - Exit code from iteration
emit_iteration_completed() {
    local worker_id="$1"
    local iteration="$2"
    local exit_code="$3"

    emit_event "iteration.completed" "\"worker_id\":\"$worker_id\",\"iteration\":$iteration,\"exit_code\":$exit_code"
}

# Emit error event
#
# Args:
#   worker_id  - Worker identifier
#   error_type - Type of error (e.g., "timeout", "api_error", "validation")
#   message    - Error message
emit_error() {
    local worker_id="$1"
    local error_type="$2"
    local message="$3"

    # Escape quotes in message for JSON
    message=${message//\"/\\\"}

    emit_event "error" "\"worker_id\":\"$worker_id\",\"error_type\":\"$error_type\",\"message\":\"$message\""
    log_debug "Event: error worker_id=$worker_id error_type=$error_type"
}

# Emit agent started event
#
# Args:
#   agent_type - Type of agent
#   worker_id  - Worker identifier
#   task_id    - Task identifier (optional)
emit_agent_started() {
    local agent_type="$1"
    local worker_id="$2"
    local task_id="${3:-}"

    local data="\"agent_type\":\"$agent_type\",\"worker_id\":\"$worker_id\""
    if [ -n "$task_id" ]; then
        data="$data,\"task_id\":\"$task_id\""
    fi

    emit_event "agent.started" "$data"
    log_debug "Event: agent.started agent_type=$agent_type worker_id=$worker_id"
}

# Emit agent completed event
#
# Args:
#   agent_type - Type of agent
#   worker_id  - Worker identifier
#   exit_code  - Exit code
#   result     - Result value (optional)
emit_agent_completed() {
    local agent_type="$1"
    local worker_id="$2"
    local exit_code="$3"
    local result="${4:-}"

    local data="\"agent_type\":\"$agent_type\",\"worker_id\":\"$worker_id\",\"exit_code\":$exit_code"
    if [ -n "$result" ]; then
        data="$data,\"result\":\"$result\""
    fi

    emit_event "agent.completed" "$data"
    log_debug "Event: agent.completed agent_type=$agent_type exit_code=$exit_code"
}

# Emit PR created event
#
# Args:
#   task_id - Task identifier
#   pr_url  - PR URL
#   branch  - Branch name
emit_pr_created() {
    local task_id="$1"
    local pr_url="$2"
    local branch="$3"

    emit_event "pr.created" "\"task_id\":\"$task_id\",\"pr_url\":\"$pr_url\",\"branch\":\"$branch\""
    log_debug "Event: pr.created task_id=$task_id pr_url=$pr_url"
}

# Emit PR merged event
#
# Args:
#   task_id - Task identifier
#   pr_url  - PR URL
emit_pr_merged() {
    local task_id="$1"
    local pr_url="$2"

    emit_event "pr.merged" "\"task_id\":\"$task_id\",\"pr_url\":\"$pr_url\""
    log_debug "Event: pr.merged task_id=$task_id"
}

# Emit violation detected event
#
# Args:
#   worker_id      - Worker identifier
#   violation_type - Type of violation
#   details        - Violation details
emit_violation() {
    local worker_id="$1"
    local violation_type="$2"
    local details="$3"

    # Escape quotes in details for JSON
    details=${details//\"/\\\"}

    emit_event "violation" "\"worker_id\":\"$worker_id\",\"violation_type\":\"$violation_type\",\"details\":\"$details\""
    log_debug "Event: violation worker_id=$worker_id violation_type=$violation_type"
}

# Query events by type
#
# Args:
#   event_type  - Event type to filter (uses jq select)
#   project_dir - Project directory (optional)
#
# Returns: Matching events as JSON lines
events_query_by_type() {
    local event_type="$1"
    local project_dir="${2:-${PROJECT_DIR:-.}}"
    local events_log
    events_log=$(_get_events_log "$project_dir")

    if [ ! -f "$events_log" ]; then
        return 0
    fi

    jq -c "select(.event_type == \"$event_type\")" "$events_log" 2>/dev/null
}

# Query events for a specific task
#
# Args:
#   task_id     - Task identifier
#   project_dir - Project directory (optional)
#
# Returns: Matching events as JSON lines
events_query_by_task() {
    local task_id="$1"
    local project_dir="${2:-${PROJECT_DIR:-.}}"
    local events_log
    events_log=$(_get_events_log "$project_dir")

    if [ ! -f "$events_log" ]; then
        return 0
    fi

    jq -c "select(.task_id == \"$task_id\")" "$events_log" 2>/dev/null
}

# Query events for a specific worker
#
# Args:
#   worker_id   - Worker identifier
#   project_dir - Project directory (optional)
#
# Returns: Matching events as JSON lines
events_query_by_worker() {
    local worker_id="$1"
    local project_dir="${2:-${PROJECT_DIR:-.}}"
    local events_log
    events_log=$(_get_events_log "$project_dir")

    if [ ! -f "$events_log" ]; then
        return 0
    fi

    jq -c "select(.worker_id == \"$worker_id\")" "$events_log" 2>/dev/null
}

# Get event count by type
#
# Args:
#   event_type  - Event type (optional, all if not specified)
#   project_dir - Project directory (optional)
#
# Returns: Count of events
events_count() {
    local event_type="${1:-}"
    local project_dir="${2:-${PROJECT_DIR:-.}}"
    local events_log
    events_log=$(_get_events_log "$project_dir")

    if [ ! -f "$events_log" ]; then
        echo "0"
        return
    fi

    if [ -n "$event_type" ]; then
        grep -c "\"event_type\":\"$event_type\"" "$events_log" 2>/dev/null || echo "0"
    else
        wc -l < "$events_log" 2>/dev/null || echo "0"
    fi
}
