#!/usr/bin/env bash
# =============================================================================
# service-state.sh - Persistent state for service scheduler recovery
#
# Manages state file: .ralph/.service-state.json
#
# Provides:
#   service_state_init(ralph_dir)    - Initialize state tracking
#   service_state_save()             - Persist current state to disk
#   service_state_restore()          - Load state from disk on restart
#   service_state_get_last_run(id)   - Get last run timestamp for a service
#   service_state_set_last_run(id)   - Record execution timestamp
#   service_state_get_status(id)     - Get current status of a service
#   service_state_set_status(id, status) - Set service status
#   service_state_get_run_count(id)  - Get total run count for a service
#   service_state_increment_runs(id) - Increment run count
#   service_state_clear()            - Clear all state (for testing)
# =============================================================================

# Prevent double-sourcing
[ -n "${_SERVICE_STATE_LOADED:-}" ] && return 0
_SERVICE_STATE_LOADED=1

# State tracking
_SERVICE_STATE_FILE=""
declare -gA _SERVICE_LAST_RUN=()     # service_id -> epoch timestamp
declare -gA _SERVICE_STATUS=()       # service_id -> running|stopped|failed|skipped
declare -gA _SERVICE_RUN_COUNT=()    # service_id -> total runs
declare -gA _SERVICE_FAIL_COUNT=()   # service_id -> consecutive failures
declare -gA _SERVICE_RUNNING_PID=()  # service_id -> PID (for background services)

# Initialize service state tracking
#
# Args:
#   ralph_dir - Ralph directory path
service_state_init() {
    local ralph_dir="$1"
    _SERVICE_STATE_FILE="$ralph_dir/.service-state.json"

    # Reset in-memory state
    _SERVICE_LAST_RUN=()
    _SERVICE_STATUS=()
    _SERVICE_RUN_COUNT=()
    _SERVICE_FAIL_COUNT=()
    _SERVICE_RUNNING_PID=()
}

# Persist current state to disk
#
# Called periodically and on shutdown to preserve state for recovery.
service_state_save() {
    [ -n "$_SERVICE_STATE_FILE" ] || return 1

    local state_json='{"version":"1.0","services":{}}'

    # Build services object
    for id in "${!_SERVICE_LAST_RUN[@]}"; do
        local last_run="${_SERVICE_LAST_RUN[$id]:-0}"
        local status="${_SERVICE_STATUS[$id]:-stopped}"
        local run_count="${_SERVICE_RUN_COUNT[$id]:-0}"
        local fail_count="${_SERVICE_FAIL_COUNT[$id]:-0}"
        local pid="${_SERVICE_RUNNING_PID[$id]:-}"

        state_json=$(echo "$state_json" | jq --arg id "$id" \
            --argjson last_run "$last_run" \
            --arg status "$status" \
            --argjson run_count "$run_count" \
            --argjson fail_count "$fail_count" \
            --arg pid "$pid" \
            '.services[$id] = {
                "last_run": $last_run,
                "status": $status,
                "run_count": $run_count,
                "fail_count": $fail_count,
                "pid": (if $pid == "" then null else ($pid | tonumber) end)
            }')
    done

    # Add metadata
    state_json=$(echo "$state_json" | jq --argjson ts "$(date +%s)" '.saved_at = $ts')

    # Write atomically
    local tmp_file
    tmp_file=$(mktemp)
    echo "$state_json" > "$tmp_file"
    mv "$tmp_file" "$_SERVICE_STATE_FILE"
}

# Load state from disk on restart
#
# Restores last_run timestamps and run counts. Running statuses are
# verified against actual process state.
#
# Returns: 0 on success, 1 if no state file
service_state_restore() {
    [ -n "$_SERVICE_STATE_FILE" ] || return 1
    [ -f "$_SERVICE_STATE_FILE" ] || return 1

    # Validate JSON
    if ! jq empty "$_SERVICE_STATE_FILE" 2>/dev/null; then
        log_warn "Invalid service state file, starting fresh"
        return 1
    fi

    # Read services
    local service_ids
    service_ids=$(jq -r '.services | keys[]' "$_SERVICE_STATE_FILE" 2>/dev/null)

    while read -r id; do
        [ -n "$id" ] || continue

        _SERVICE_LAST_RUN[$id]=$(jq -r --arg id "$id" '.services[$id].last_run // 0' "$_SERVICE_STATE_FILE")
        _SERVICE_RUN_COUNT[$id]=$(jq -r --arg id "$id" '.services[$id].run_count // 0' "$_SERVICE_STATE_FILE")
        _SERVICE_FAIL_COUNT[$id]=$(jq -r --arg id "$id" '.services[$id].fail_count // 0' "$_SERVICE_STATE_FILE")

        # Check if previously running service is still running
        local saved_status saved_pid
        saved_status=$(jq -r --arg id "$id" '.services[$id].status // "stopped"' "$_SERVICE_STATE_FILE")
        saved_pid=$(jq -r --arg id "$id" '.services[$id].pid // null' "$_SERVICE_STATE_FILE")

        if [ "$saved_status" = "running" ] && [ "$saved_pid" != "null" ] && [ -n "$saved_pid" ]; then
            # Verify process is still running
            if kill -0 "$saved_pid" 2>/dev/null; then
                _SERVICE_STATUS[$id]="running"
                _SERVICE_RUNNING_PID[$id]="$saved_pid"
                log_debug "Service $id still running (PID: $saved_pid)"
            else
                _SERVICE_STATUS[$id]="stopped"
                log_debug "Service $id was running but process exited"
            fi
        else
            _SERVICE_STATUS[$id]="stopped"
        fi
    done <<< "$service_ids"

    local saved_at
    saved_at=$(jq -r '.saved_at // 0' "$_SERVICE_STATE_FILE")
    local age=$(($(date +%s) - saved_at))
    log "Restored service state from $age seconds ago"

    return 0
}

# Get last run timestamp for a service
#
# Args:
#   id - Service identifier
#
# Returns: Epoch timestamp via stdout (0 if never run)
service_state_get_last_run() {
    local id="$1"
    echo "${_SERVICE_LAST_RUN[$id]:-0}"
}

# Record execution timestamp for a service
#
# Args:
#   id   - Service identifier
#   time - Optional epoch timestamp (default: now)
service_state_set_last_run() {
    local id="$1"
    local time="${2:-$(date +%s)}"
    _SERVICE_LAST_RUN[$id]="$time"
}

# Get current status of a service
#
# Args:
#   id - Service identifier
#
# Returns: Status string (running|stopped|failed|skipped)
service_state_get_status() {
    local id="$1"
    echo "${_SERVICE_STATUS[$id]:-stopped}"
}

# Set service status
#
# Args:
#   id     - Service identifier
#   status - Status string (running|stopped|failed|skipped)
service_state_set_status() {
    local id="$1"
    local status="$2"
    _SERVICE_STATUS[$id]="$status"
}

# Get total run count for a service
#
# Args:
#   id - Service identifier
#
# Returns: Run count via stdout
service_state_get_run_count() {
    local id="$1"
    echo "${_SERVICE_RUN_COUNT[$id]:-0}"
}

# Increment run count for a service
#
# Args:
#   id - Service identifier
service_state_increment_runs() {
    local id="$1"
    _SERVICE_RUN_COUNT[$id]=$(( ${_SERVICE_RUN_COUNT[$id]:-0} + 1 ))
}

# Get consecutive failure count for a service
#
# Args:
#   id - Service identifier
#
# Returns: Failure count via stdout
service_state_get_fail_count() {
    local id="$1"
    echo "${_SERVICE_FAIL_COUNT[$id]:-0}"
}

# Increment failure count for a service
#
# Args:
#   id - Service identifier
service_state_increment_failures() {
    local id="$1"
    _SERVICE_FAIL_COUNT[$id]=$(( ${_SERVICE_FAIL_COUNT[$id]:-0} + 1 ))
}

# Reset failure count for a service (on successful run)
#
# Args:
#   id - Service identifier
service_state_reset_failures() {
    local id="$1"
    _SERVICE_FAIL_COUNT[$id]=0
}

# Get running PID for a service
#
# Args:
#   id - Service identifier
#
# Returns: PID if running, empty string otherwise
service_state_get_pid() {
    local id="$1"
    echo "${_SERVICE_RUNNING_PID[$id]:-}"
}

# Set running PID for a service
#
# Args:
#   id  - Service identifier
#   pid - Process ID
service_state_set_pid() {
    local id="$1"
    local pid="$2"
    _SERVICE_RUNNING_PID[$id]="$pid"
}

# Clear PID for a service (when process exits)
#
# Args:
#   id - Service identifier
service_state_clear_pid() {
    local id="$1"
    unset "_SERVICE_RUNNING_PID[$id]"
}

# Check if a service is currently running
#
# Args:
#   id - Service identifier
#
# Returns: 0 if running, 1 otherwise
service_state_is_running() {
    local id="$1"
    local status="${_SERVICE_STATUS[$id]:-stopped}"
    local pid="${_SERVICE_RUNNING_PID[$id]:-}"

    # Must be marked running and have valid PID
    if [ "$status" = "running" ] && [ -n "$pid" ]; then
        # Verify process is actually running
        if kill -0 "$pid" 2>/dev/null; then
            return 0
        else
            # Process died, update status
            _SERVICE_STATUS[$id]="stopped"
            unset "_SERVICE_RUNNING_PID[$id]"
        fi
    fi
    return 1
}

# Clear all state (for testing)
service_state_clear() {
    _SERVICE_LAST_RUN=()
    _SERVICE_STATUS=()
    _SERVICE_RUN_COUNT=()
    _SERVICE_FAIL_COUNT=()
    _SERVICE_RUNNING_PID=()

    if [ -n "$_SERVICE_STATE_FILE" ] && [ -f "$_SERVICE_STATE_FILE" ]; then
        rm -f "$_SERVICE_STATE_FILE"
    fi
}

# Get all tracked service IDs
#
# Returns: Space-separated list of service IDs
service_state_get_all_ids() {
    echo "${!_SERVICE_LAST_RUN[@]}"
}

# Mark a service as started
#
# Convenience function that sets status to running and records timestamp.
#
# Args:
#   id  - Service identifier
#   pid - Optional PID for background services
service_state_mark_started() {
    local id="$1"
    local pid="${2:-}"

    _SERVICE_STATUS[$id]="running"
    _SERVICE_LAST_RUN[$id]=$(date +%s)
    _SERVICE_RUN_COUNT[$id]=$(( ${_SERVICE_RUN_COUNT[$id]:-0} + 1 ))

    if [ -n "$pid" ]; then
        _SERVICE_RUNNING_PID[$id]="$pid"
    fi
}

# Mark a service as completed successfully
#
# Args:
#   id - Service identifier
service_state_mark_completed() {
    local id="$1"
    _SERVICE_STATUS[$id]="stopped"
    _SERVICE_FAIL_COUNT[$id]=0
    unset "_SERVICE_RUNNING_PID[$id]"
}

# Mark a service as failed
#
# Args:
#   id - Service identifier
service_state_mark_failed() {
    local id="$1"
    _SERVICE_STATUS[$id]="failed"
    _SERVICE_FAIL_COUNT[$id]=$(( ${_SERVICE_FAIL_COUNT[$id]:-0} + 1 ))
    unset "_SERVICE_RUNNING_PID[$id]"
}

# Mark a service as skipped (e.g., already running)
#
# Args:
#   id - Service identifier
service_state_mark_skipped() {
    local id="$1"
    _SERVICE_STATUS[$id]="skipped"
}
