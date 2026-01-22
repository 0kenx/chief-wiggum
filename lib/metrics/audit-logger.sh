#!/usr/bin/env bash
# Audit logging utilities for Chief Wiggum
# Tracks who ran what task and when for security audit trail
set -euo pipefail

AUDIT_LOG="${AUDIT_LOG:-$PROJECT_DIR/.ralph/logs/audit.log}"

# Get git user information
get_git_user_info() {
    local user_name user_email
    user_name=$(git config user.name 2>/dev/null || echo "unknown")
    user_email=$(git config user.email 2>/dev/null || echo "unknown")
    echo "$user_name <$user_email>"
}

# Get system user information
get_system_user_info() {
    echo "$USER@$(hostname)"
}

# Initialize audit log with header if it doesn't exist
init_audit_log() {
    local log_dir
    log_dir=$(dirname "$AUDIT_LOG")
    mkdir -p "$log_dir"

    if [ ! -f "$AUDIT_LOG" ]; then
        cat > "$AUDIT_LOG" << 'EOF'
# Chief Wiggum Audit Log
# Format: [TIMESTAMP] EVENT_TYPE | KEY=VALUE pairs
#
# EVENT_TYPES:
#   - TASK_ASSIGNED: A task was assigned to a worker
#   - WORKER_START: Worker process started
#   - WORKER_COMPLETE: Worker completed successfully
#   - WORKER_FAILED: Worker failed or encountered errors
#   - WORKER_CLEANUP: Worker cleanup phase started
#
# FIELDS:
#   - timestamp: ISO 8601 timestamp
#   - event: Event type
#   - task_id: Task identifier (e.g., TASK-001)
#   - worker_id: Worker identifier (e.g., worker-TASK-001-12345)
#   - git_user: Git user from git config (name <email>)
#   - system_user: System user who invoked the command (user@host)
#   - pid: Process ID of the worker
#   - status: Task completion status (COMPLETE/FAILED/TIMEOUT)
#
# Example:
# [2025-01-18T12:00:00+00:00] TASK_ASSIGNED | task_id=TASK-001 | worker_id=worker-TASK-001-12345 | git_user=John Doe <john@example.com> | system_user=john@localhost | pid=12345
#
================================================================================

EOF
    fi
}

# Log a generic audit event
# Usage: audit_log "EVENT_TYPE" "key1=value1" "key2=value2" ...
audit_log() {
    local event_type="$1"
    shift

    # Ensure log is initialized
    init_audit_log

    local timestamp
    timestamp=$(date -Iseconds)
    local log_entry="[$timestamp] $event_type"

    # Append all key=value pairs
    for kvp in "$@"; do
        log_entry="$log_entry | $kvp"
    done

    echo "$log_entry" >> "$AUDIT_LOG"
}

# Log task assignment
# Usage: audit_log_task_assigned "TASK-001" "worker-TASK-001-12345" "12345"
audit_log_task_assigned() {
    local task_id="$1"
    local worker_id="$2"
    local pid="$3"

    local git_user system_user
    git_user=$(get_git_user_info)
    system_user=$(get_system_user_info)

    audit_log "TASK_ASSIGNED" \
        "task_id=$task_id" \
        "worker_id=$worker_id" \
        "git_user=$git_user" \
        "system_user=$system_user" \
        "pid=$pid"
}

# Log worker start
# Usage: audit_log_worker_start "TASK-001" "worker-TASK-001-12345"
audit_log_worker_start() {
    local task_id="$1"
    local worker_id="$2"

    local git_user system_user pid=$$
    git_user=$(get_git_user_info)
    system_user=$(get_system_user_info)

    audit_log "WORKER_START" \
        "task_id=$task_id" \
        "worker_id=$worker_id" \
        "git_user=$git_user" \
        "system_user=$system_user" \
        "pid=$pid"
}

# Log worker completion
# Usage: audit_log_worker_complete "TASK-001" "worker-TASK-001-12345" "COMPLETE"
audit_log_worker_complete() {
    local task_id="$1"
    local worker_id="$2"
    local status="$3"  # COMPLETE, FAILED, or TIMEOUT

    local git_user system_user pid=$$
    git_user=$(get_git_user_info)
    system_user=$(get_system_user_info)

    local event_type="WORKER_COMPLETE"
    if [ "$status" != "COMPLETE" ]; then
        event_type="WORKER_FAILED"
    fi

    audit_log "$event_type" \
        "task_id=$task_id" \
        "worker_id=$worker_id" \
        "status=$status" \
        "git_user=$git_user" \
        "system_user=$system_user" \
        "pid=$pid"
}

# Log worker cleanup
# Usage: audit_log_worker_cleanup "TASK-001" "worker-TASK-001-12345"
audit_log_worker_cleanup() {
    local task_id="$1"
    local worker_id="$2"

    local git_user system_user pid=$$
    git_user=$(get_git_user_info)
    system_user=$(get_system_user_info)

    audit_log "WORKER_CLEANUP" \
        "task_id=$task_id" \
        "worker_id=$worker_id" \
        "git_user=$git_user" \
        "system_user=$system_user" \
        "pid=$pid"
}
