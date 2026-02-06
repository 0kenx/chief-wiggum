#!/usr/bin/env bash
# =============================================================================
# service-state.sh - Persistent state for service scheduler recovery
#
# Manages state file: .ralph/services/state.json
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
#
# Circuit Breaker:
#   service_state_get_circuit_state(id)    - Get circuit state (closed|open|half-open)
#   service_state_set_circuit_state(id, state) - Set circuit state
#   service_state_get_circuit_opened_at(id) - Get when circuit was opened
#
# Metrics:
#   service_state_record_execution(id, duration, exit_code) - Record execution
#   service_state_get_metrics(id)    - Get metrics for a service
#
# Queue:
#   service_state_queue_add(id, args...) - Add to execution queue
#   service_state_queue_pop(id)      - Pop from execution queue
#   service_state_queue_size(id)     - Get queue size
#   service_state_queue_clear(id)    - Clear queue
# =============================================================================

# Prevent double-sourcing
[ -n "${_SERVICE_STATE_LOADED:-}" ] && return 0
_SERVICE_STATE_LOADED=1
source "$WIGGUM_HOME/lib/core/platform.sh"

# State tracking
_SERVICE_STATE_FILE=""
_SERVICE_METRICS_FILE=""
declare -gA _SERVICE_LAST_RUN=()     # service_id -> epoch timestamp
declare -gA _SERVICE_STATUS=()       # service_id -> running|stopped|failed|skipped
declare -gA _SERVICE_RUN_COUNT=()    # service_id -> total runs
declare -gA _SERVICE_FAIL_COUNT=()   # service_id -> consecutive failures
declare -gA _SERVICE_RUNNING_PID=()  # service_id -> PID (for background services)

# Circuit breaker state
declare -gA _SERVICE_CIRCUIT_STATE=()     # service_id -> closed|open|half-open
declare -gA _SERVICE_CIRCUIT_OPENED_AT=() # service_id -> epoch when opened
declare -gA _SERVICE_HALF_OPEN_ATTEMPTS=() # service_id -> attempts in half-open

# Metrics tracking
declare -gA _SERVICE_TOTAL_DURATION=()    # service_id -> total execution time (ms)
declare -gA _SERVICE_SUCCESS_COUNT=()     # service_id -> successful runs
declare -gA _SERVICE_LAST_DURATION=()     # service_id -> last execution duration (ms)
declare -gA _SERVICE_MIN_DURATION=()      # service_id -> minimum duration (ms)
declare -gA _SERVICE_MAX_DURATION=()      # service_id -> maximum duration (ms)

# Execution queue (for if_running=queue)
declare -gA _SERVICE_QUEUE=()             # service_id -> JSON array of queued args
declare -gA _SERVICE_QUEUE_PRIORITY=()    # service_id -> JSON array of priorities

# Backoff state
declare -gA _SERVICE_BACKOFF_UNTIL=()     # service_id -> epoch until backoff ends
declare -gA _SERVICE_RETRY_COUNT=()       # service_id -> current retry count

# Dependencies tracking
declare -gA _SERVICE_LAST_SUCCESS=()      # service_id -> epoch of last successful run

# Initialize service state tracking
#
# Args:
#   ralph_dir - Ralph directory path
service_state_init() {
    local ralph_dir="$1"
    _SERVICE_STATE_FILE="$ralph_dir/services/state.json"
    _SERVICE_METRICS_FILE="$ralph_dir/services/metrics.jsonl"

    # Reset in-memory state
    _SERVICE_LAST_RUN=()
    _SERVICE_STATUS=()
    _SERVICE_RUN_COUNT=()
    _SERVICE_FAIL_COUNT=()
    _SERVICE_RUNNING_PID=()
    _SERVICE_CIRCUIT_STATE=()
    _SERVICE_CIRCUIT_OPENED_AT=()
    _SERVICE_HALF_OPEN_ATTEMPTS=()
    _SERVICE_TOTAL_DURATION=()
    _SERVICE_SUCCESS_COUNT=()
    _SERVICE_LAST_DURATION=()
    _SERVICE_MIN_DURATION=()
    _SERVICE_MAX_DURATION=()
    _SERVICE_QUEUE=()
    _SERVICE_QUEUE_PRIORITY=()
    _SERVICE_BACKOFF_UNTIL=()
    _SERVICE_RETRY_COUNT=()
    _SERVICE_LAST_SUCCESS=()
}

# Persist current state to disk
#
# Called periodically and on shutdown to preserve state for recovery.
# Builds JSON entirely in bash to avoid N+1 jq subprocess calls per tick.
# All values are simple numbers or known-safe strings from bash arrays.
service_state_save() {
    [ -n "$_SERVICE_STATE_FILE" ] || return 1

    local now
    now=$(epoch_now)

    # Build JSON in bash (no jq needed — values are numbers/simple strings)
    local json='{"version":"1.0","saved_at":'"$now"',"services":{'
    local first=true

    for id in "${!_SERVICE_LAST_RUN[@]}"; do
        if [ "$first" = true ]; then
            first=false
        else
            json+=','
        fi

        local pid="${_SERVICE_RUNNING_PID[$id]:-}"
        local pid_json="null"
        if [ -n "$pid" ]; then
            pid_json="$pid"
        fi

        json+='"'"$id"'":{'
        json+='"last_run":'"${_SERVICE_LAST_RUN[$id]:-0}"
        json+=',"status":"'"${_SERVICE_STATUS[$id]:-stopped}"'"'
        json+=',"run_count":'"${_SERVICE_RUN_COUNT[$id]:-0}"
        json+=',"fail_count":'"${_SERVICE_FAIL_COUNT[$id]:-0}"
        json+=',"pid":'"$pid_json"
        json+=',"circuit":{"state":"'"${_SERVICE_CIRCUIT_STATE[$id]:-closed}"'"'
        json+=',"opened_at":'"${_SERVICE_CIRCUIT_OPENED_AT[$id]:-0}"
        json+=',"half_open_attempts":'"${_SERVICE_HALF_OPEN_ATTEMPTS[$id]:-0}"'}'
        json+=',"metrics":{"total_duration_ms":'"${_SERVICE_TOTAL_DURATION[$id]:-0}"
        json+=',"success_count":'"${_SERVICE_SUCCESS_COUNT[$id]:-0}"
        json+=',"last_duration_ms":'"${_SERVICE_LAST_DURATION[$id]:-0}"
        json+=',"min_duration_ms":'"${_SERVICE_MIN_DURATION[$id]:-0}"
        json+=',"max_duration_ms":'"${_SERVICE_MAX_DURATION[$id]:-0}"'}'
        json+=',"queue":'"${_SERVICE_QUEUE[$id]:-[]}"
        json+=',"backoff_until":'"${_SERVICE_BACKOFF_UNTIL[$id]:-0}"
        json+=',"retry_count":'"${_SERVICE_RETRY_COUNT[$id]:-0}"
        json+=',"last_success":'"${_SERVICE_LAST_SUCCESS[$id]:-0}"
        json+='}'
    done

    json+='}}'

    # Write atomically
    local tmp_file
    tmp_file=$(mktemp "${_SERVICE_STATE_FILE}.XXXXXX")
    echo "$json" > "$tmp_file"
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

        # Basic state
        _SERVICE_LAST_RUN[$id]=$(jq -r --arg id "$id" '.services[$id].last_run // 0' "$_SERVICE_STATE_FILE")
        _SERVICE_RUN_COUNT[$id]=$(jq -r --arg id "$id" '.services[$id].run_count // 0' "$_SERVICE_STATE_FILE")
        _SERVICE_FAIL_COUNT[$id]=$(jq -r --arg id "$id" '.services[$id].fail_count // 0' "$_SERVICE_STATE_FILE")
        _SERVICE_LAST_SUCCESS[$id]=$(jq -r --arg id "$id" '.services[$id].last_success // 0' "$_SERVICE_STATE_FILE")

        # Circuit breaker state
        _SERVICE_CIRCUIT_STATE[$id]=$(jq -r --arg id "$id" '.services[$id].circuit.state // "closed"' "$_SERVICE_STATE_FILE")
        _SERVICE_CIRCUIT_OPENED_AT[$id]=$(jq -r --arg id "$id" '.services[$id].circuit.opened_at // 0' "$_SERVICE_STATE_FILE")
        _SERVICE_HALF_OPEN_ATTEMPTS[$id]=$(jq -r --arg id "$id" '.services[$id].circuit.half_open_attempts // 0' "$_SERVICE_STATE_FILE")

        # Metrics
        _SERVICE_TOTAL_DURATION[$id]=$(jq -r --arg id "$id" '.services[$id].metrics.total_duration_ms // 0' "$_SERVICE_STATE_FILE")
        _SERVICE_SUCCESS_COUNT[$id]=$(jq -r --arg id "$id" '.services[$id].metrics.success_count // 0' "$_SERVICE_STATE_FILE")
        _SERVICE_LAST_DURATION[$id]=$(jq -r --arg id "$id" '.services[$id].metrics.last_duration_ms // 0' "$_SERVICE_STATE_FILE")
        _SERVICE_MIN_DURATION[$id]=$(jq -r --arg id "$id" '.services[$id].metrics.min_duration_ms // 0' "$_SERVICE_STATE_FILE")
        _SERVICE_MAX_DURATION[$id]=$(jq -r --arg id "$id" '.services[$id].metrics.max_duration_ms // 0' "$_SERVICE_STATE_FILE")

        # Queue
        _SERVICE_QUEUE[$id]=$(jq -c --arg id "$id" '.services[$id].queue // []' "$_SERVICE_STATE_FILE")

        # Backoff
        _SERVICE_BACKOFF_UNTIL[$id]=$(jq -r --arg id "$id" '.services[$id].backoff_until // 0' "$_SERVICE_STATE_FILE")
        _SERVICE_RETRY_COUNT[$id]=$(jq -r --arg id "$id" '.services[$id].retry_count // 0' "$_SERVICE_STATE_FILE")

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
    local age=$(($(epoch_now) - saved_at))
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
    local time="${2:-$(epoch_now)}"
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
    _SERVICE_CIRCUIT_STATE=()
    _SERVICE_CIRCUIT_OPENED_AT=()
    _SERVICE_HALF_OPEN_ATTEMPTS=()
    _SERVICE_TOTAL_DURATION=()
    _SERVICE_SUCCESS_COUNT=()
    _SERVICE_LAST_DURATION=()
    _SERVICE_MIN_DURATION=()
    _SERVICE_MAX_DURATION=()
    _SERVICE_QUEUE=()
    _SERVICE_QUEUE_PRIORITY=()
    _SERVICE_BACKOFF_UNTIL=()
    _SERVICE_RETRY_COUNT=()
    _SERVICE_LAST_SUCCESS=()

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
    _SERVICE_LAST_RUN[$id]=$(epoch_now)
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
    _SERVICE_RETRY_COUNT[$id]=0
    _SERVICE_BACKOFF_UNTIL[$id]=0
    _SERVICE_LAST_SUCCESS[$id]=$(epoch_now)
    _SERVICE_SUCCESS_COUNT[$id]=$(( ${_SERVICE_SUCCESS_COUNT[$id]:-0} + 1 ))
    unset "_SERVICE_RUNNING_PID[$id]"

    # Reset circuit breaker on success
    if [ "${_SERVICE_CIRCUIT_STATE[$id]:-closed}" != "closed" ]; then
        _SERVICE_CIRCUIT_STATE[$id]="closed"
        _SERVICE_HALF_OPEN_ATTEMPTS[$id]=0
        log_debug "Service $id circuit breaker closed (success)"
    fi
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

# =============================================================================
# Circuit Breaker Functions
# =============================================================================

# Get circuit breaker state for a service
#
# Args:
#   id - Service identifier
#
# Returns: Circuit state (closed|open|half-open)
service_state_get_circuit_state() {
    local id="$1"
    echo "${_SERVICE_CIRCUIT_STATE[$id]:-closed}"
}

# Set circuit breaker state for a service
#
# Args:
#   id    - Service identifier
#   state - Circuit state (closed|open|half-open)
service_state_set_circuit_state() {
    local id="$1"
    local state="$2"
    _SERVICE_CIRCUIT_STATE[$id]="$state"

    if [ "$state" = "open" ]; then
        _SERVICE_CIRCUIT_OPENED_AT[$id]=$(epoch_now)
        _SERVICE_HALF_OPEN_ATTEMPTS[$id]=0
    fi
}

# Get when circuit was opened
#
# Args:
#   id - Service identifier
#
# Returns: Epoch timestamp (0 if never opened)
service_state_get_circuit_opened_at() {
    local id="$1"
    echo "${_SERVICE_CIRCUIT_OPENED_AT[$id]:-0}"
}

# Increment half-open attempts counter
#
# Args:
#   id - Service identifier
service_state_increment_half_open_attempts() {
    local id="$1"
    _SERVICE_HALF_OPEN_ATTEMPTS[$id]=$(( ${_SERVICE_HALF_OPEN_ATTEMPTS[$id]:-0} + 1 ))
}

# Get half-open attempts counter
#
# Args:
#   id - Service identifier
#
# Returns: Number of half-open attempts
service_state_get_half_open_attempts() {
    local id="$1"
    echo "${_SERVICE_HALF_OPEN_ATTEMPTS[$id]:-0}"
}

# =============================================================================
# Metrics Functions
# =============================================================================

# Record an execution with metrics
#
# Args:
#   id        - Service identifier
#   duration  - Execution duration in milliseconds
#   exit_code - Exit code from execution
service_state_record_execution() {
    local id="$1"
    local duration="$2"
    local exit_code="$3"

    _SERVICE_LAST_DURATION[$id]="$duration"
    _SERVICE_TOTAL_DURATION[$id]=$(( ${_SERVICE_TOTAL_DURATION[$id]:-0} + duration ))

    # Update min/max
    local current_min="${_SERVICE_MIN_DURATION[$id]:-0}"
    local current_max="${_SERVICE_MAX_DURATION[$id]:-0}"

    if [ "$current_min" -eq 0 ] || [ "$duration" -lt "$current_min" ]; then
        _SERVICE_MIN_DURATION[$id]="$duration"
    fi

    if [ "$duration" -gt "$current_max" ]; then
        _SERVICE_MAX_DURATION[$id]="$duration"
    fi

    # Emit metrics to file if configured
    if [ -n "$_SERVICE_METRICS_FILE" ]; then
        local now
        now=$(epoch_now)
        local metrics_json
        metrics_json=$(jq -n -c \
            --arg id "$id" \
            --argjson ts "$now" \
            --argjson duration "$duration" \
            --argjson exit_code "$exit_code" \
            --argjson run_count "${_SERVICE_RUN_COUNT[$id]:-0}" \
            '{
                "timestamp": $ts,
                "service_id": $id,
                "event": "execution",
                "duration_ms": $duration,
                "exit_code": $exit_code,
                "run_count": $run_count
            }')
        echo "$metrics_json" >> "$_SERVICE_METRICS_FILE"
    fi
}

# Get metrics for a service
#
# Args:
#   id - Service identifier
#
# Returns: JSON object with metrics
service_state_get_metrics() {
    local id="$1"

    local run_count="${_SERVICE_RUN_COUNT[$id]:-0}"
    local success_count="${_SERVICE_SUCCESS_COUNT[$id]:-0}"
    local fail_count="${_SERVICE_FAIL_COUNT[$id]:-0}"
    local total_duration="${_SERVICE_TOTAL_DURATION[$id]:-0}"
    local last_duration="${_SERVICE_LAST_DURATION[$id]:-0}"
    local min_duration="${_SERVICE_MIN_DURATION[$id]:-0}"
    local max_duration="${_SERVICE_MAX_DURATION[$id]:-0}"

    local avg_duration=0
    if [ "$run_count" -gt 0 ]; then
        avg_duration=$((total_duration / run_count))
    fi

    local success_rate=0
    if [ "$run_count" -gt 0 ]; then
        success_rate=$((success_count * 100 / run_count))
    fi

    jq -n \
        --argjson run_count "$run_count" \
        --argjson success_count "$success_count" \
        --argjson fail_count "$fail_count" \
        --argjson success_rate "$success_rate" \
        --argjson total_duration "$total_duration" \
        --argjson avg_duration "$avg_duration" \
        --argjson last_duration "$last_duration" \
        --argjson min_duration "$min_duration" \
        --argjson max_duration "$max_duration" \
        '{
            "run_count": $run_count,
            "success_count": $success_count,
            "fail_count": $fail_count,
            "success_rate_pct": $success_rate,
            "total_duration_ms": $total_duration,
            "avg_duration_ms": $avg_duration,
            "last_duration_ms": $last_duration,
            "min_duration_ms": $min_duration,
            "max_duration_ms": $max_duration
        }'
}

# =============================================================================
# Queue Functions
# =============================================================================

# Add execution to queue
#
# Args:
#   id       - Service identifier
#   priority - Priority (low|normal|high|critical)
#   args     - Arguments to queue (as JSON array)
service_state_queue_add() {
    local id="$1"
    local priority="${2:-normal}"
    local args="${3:-[]}"

    local current_queue="${_SERVICE_QUEUE[$id]:-[]}"
    local entry
    entry=$(jq -n -c --arg priority "$priority" --argjson args "$args" \
        '{"priority": $priority, "args": $args, "queued_at": now | floor}')

    _SERVICE_QUEUE[$id]=$(echo "$current_queue" | jq -c --argjson entry "$entry" '. + [$entry]')
}

# Pop highest priority item from queue
#
# Args:
#   id - Service identifier
#
# Returns: JSON object with args, empty if queue empty
service_state_queue_pop() {
    local id="$1"

    local current_queue="${_SERVICE_QUEUE[$id]:-[]}"
    local queue_size
    queue_size=$(echo "$current_queue" | jq 'length')

    if [ "$queue_size" -eq 0 ]; then
        echo ""
        return 1
    fi

    # Priority order: critical > high > normal > low
    local priority_order='{"critical": 0, "high": 1, "normal": 2, "low": 3}'

    # Sort by priority then by queued_at and take first
    local sorted
    sorted=$(echo "$current_queue" | jq -c --argjson order "$priority_order" \
        'sort_by(($order[.priority] // 2), .queued_at)')

    local first
    first=$(echo "$sorted" | jq -c '.[0]')

    # Remove from queue
    _SERVICE_QUEUE[$id]=$(echo "$sorted" | jq -c '.[1:]')

    echo "$first"
}

# Get queue size
#
# Args:
#   id - Service identifier
#
# Returns: Number of queued items
service_state_queue_size() {
    local id="$1"
    local current_queue="${_SERVICE_QUEUE[$id]:-[]}"
    echo "$current_queue" | jq 'length'
}

# Clear queue
#
# Args:
#   id - Service identifier
service_state_queue_clear() {
    local id="$1"
    _SERVICE_QUEUE[$id]="[]"
}

# =============================================================================
# Backoff Functions
# =============================================================================

# Set backoff for a service
#
# Args:
#   id       - Service identifier
#   duration - Backoff duration in seconds
service_state_set_backoff() {
    local id="$1"
    local duration="$2"
    local now
    now=$(epoch_now)
    _SERVICE_BACKOFF_UNTIL[$id]=$((now + duration))
}

# Check if service is in backoff
#
# Args:
#   id - Service identifier
#
# Returns: 0 if in backoff, 1 if not
service_state_is_in_backoff() {
    local id="$1"
    local backoff_until="${_SERVICE_BACKOFF_UNTIL[$id]:-0}"
    local now
    now=$(epoch_now)
    [ "$now" -lt "$backoff_until" ]
}

# Get remaining backoff time
#
# Args:
#   id - Service identifier
#
# Returns: Remaining seconds (0 if not in backoff)
service_state_get_backoff_remaining() {
    local id="$1"
    local backoff_until="${_SERVICE_BACKOFF_UNTIL[$id]:-0}"
    local now
    now=$(epoch_now)
    local remaining=$((backoff_until - now))
    [ "$remaining" -lt 0 ] && remaining=0
    echo "$remaining"
}

# Increment retry count
#
# Args:
#   id - Service identifier
service_state_increment_retry() {
    local id="$1"
    _SERVICE_RETRY_COUNT[$id]=$(( ${_SERVICE_RETRY_COUNT[$id]:-0} + 1 ))
}

# Get retry count
#
# Args:
#   id - Service identifier
#
# Returns: Current retry count
service_state_get_retry_count() {
    local id="$1"
    echo "${_SERVICE_RETRY_COUNT[$id]:-0}"
}

# Reset retry count
#
# Args:
#   id - Service identifier
service_state_reset_retry() {
    local id="$1"
    _SERVICE_RETRY_COUNT[$id]=0
}

# =============================================================================
# Dependency Functions
# =============================================================================

# Get last successful run timestamp
#
# Args:
#   id - Service identifier
#
# Returns: Epoch timestamp (0 if never succeeded)
service_state_get_last_success() {
    local id="$1"
    echo "${_SERVICE_LAST_SUCCESS[$id]:-0}"
}

# Check if a service ran successfully within a time window
#
# Args:
#   id      - Service identifier
#   seconds - Time window in seconds
#
# Returns: 0 if ran successfully within window, 1 otherwise
service_state_succeeded_within() {
    local id="$1"
    local seconds="$2"
    local last_success="${_SERVICE_LAST_SUCCESS[$id]:-0}"
    local now
    now=$(epoch_now)
    local cutoff=$((now - seconds))
    [ "$last_success" -ge "$cutoff" ]
}

# Get count of running instances for a service
#
# For now just returns 1 if running, 0 otherwise.
# TODO: Track multiple instances when max_instances > 1
#
# Args:
#   id - Service identifier
#
# Returns: Number of running instances
service_state_get_running_count() {
    local id="$1"
    if service_state_is_running "$id"; then
        echo 1
    else
        echo 0
    fi
}
