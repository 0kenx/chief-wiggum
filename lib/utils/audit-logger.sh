#!/usr/bin/env bash
# Audit logging utilities for Chief Wiggum
# Tracks who ran what task and when for security audit trail
set -euo pipefail

source "$WIGGUM_HOME/lib/core/file-lock.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"

AUDIT_LOG="${AUDIT_LOG:-${RALPH_DIR:-$PROJECT_DIR/.ralph}/logs/audit.log}"

# Session-scoped cache for git user info (performance optimization)
# Avoids repeated git config calls within the same session.
_GIT_USER_INFO_CACHE=""

# Get git user information (cached)
get_git_user_info() {
    # Return cached result if available
    if [ -n "$_GIT_USER_INFO_CACHE" ]; then
        echo "$_GIT_USER_INFO_CACHE"
        return 0
    fi

    local user_name user_email
    user_name=$(git config user.name 2>/dev/null || echo "unknown")
    user_email=$(git config user.email 2>/dev/null || echo "unknown")
    _GIT_USER_INFO_CACHE="$user_name <$user_email>"
    echo "$_GIT_USER_INFO_CACHE"
}

# Get system user information
get_system_user_info() {
    echo "$USER@$(hostname)"
}

# Initialize audit log with header if it doesn't exist
# Security: Creates audit log with restricted permissions (owner read/write only)
init_audit_log() {
    local log_dir
    log_dir=$(dirname "$AUDIT_LOG")
    mkdir -p "$log_dir"
    # Security: Restrict directory permissions
    chmod 700 "$log_dir" 2>/dev/null || true

    if [ ! -f "$AUDIT_LOG" ]; then
        # Security: Create log file with restricted permissions before writing
        umask 077
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

# Sanitize a string for audit log output
# Strips newlines, carriage returns, and pipe characters to prevent log injection
_audit_sanitize() {
    printf '%s' "$1" | tr -d '\n\r' | tr '|' '_'
}

# Log a generic audit event
# Usage: audit_log "EVENT_TYPE" "key1=value1" "key2=value2" ...
# Security: Uses flock for safe concurrent writes from multiple workers
# Security: Sanitizes all inputs to prevent log injection
audit_log() {
    local event_type="$1"
    shift

    # Security: Validate event_type format (alphanumeric + underscore only)
    if ! [[ "$event_type" =~ ^[A-Z][A-Z0-9_]*$ ]]; then
        log_warn "audit_log: Invalid event type rejected: $(printf '%q' "$event_type")"
        return 1
    fi

    # Ensure log is initialized
    init_audit_log

    local timestamp
    timestamp=$(iso_now)
    local log_entry="[$timestamp] $event_type"

    # Append all key=value pairs (sanitized)
    for kvp in "$@"; do
        log_entry="$log_entry | $(_audit_sanitize "$kvp")"
    done

    # Atomic append with flock (using shared utility)
    append_with_lock "$AUDIT_LOG" "$log_entry"
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
