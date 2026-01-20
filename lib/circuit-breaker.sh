#!/usr/bin/env bash
# Circuit Breaker - Detects stuck workers and repeated failures
#
# State tracking files (stored in worker directory):
#   circuit-state.json - Current circuit breaker state
#   error-hashes.log   - History of error hashes for pattern detection
#   progress-log.json  - Progress indicators per iteration
#
# Circuit states:
#   CLOSED  - Normal operation (default)
#   OPEN    - Circuit tripped, worker should stop
#
# Actions:
#   reset   - Manual override to force circuit back to CLOSED state

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/logger.sh"

# Constants
CB_MAX_NO_PROGRESS_LOOPS=3         # Open circuit after N loops without progress
CB_MAX_IDENTICAL_ERROR_LOOPS=5     # Open circuit after N loops with identical errors
CB_TRANSIENT_ERROR_THRESHOLD=2     # Errors that occur <= N times are transient

# Initialize circuit breaker state for a worker
# Usage: cb_init <worker_dir>
cb_init() {
    local worker_dir="$1"
    local state_file="$worker_dir/circuit-state.json"

    # Create initial state
    jq -n '{
        state: "CLOSED",
        iteration: 0,
        no_progress_count: 0,
        identical_error_count: 0,
        last_error_hash: null,
        last_progress_time: null,
        trip_reason: null,
        trip_time: null,
        trip_message: null,
        created_at: now | strftime("%Y-%m-%dT%H:%M:%SZ")
    }' > "$state_file"

    # Initialize error hash log
    echo "# Error hash history" > "$worker_dir/error-hashes.log"

    # Initialize progress log
    jq -n '[]' > "$worker_dir/progress-log.json"

    log_debug "Circuit breaker initialized for $worker_dir"
}

# Get current circuit state
# Usage: cb_get_state <worker_dir>
# Returns: CLOSED or OPEN
cb_get_state() {
    local worker_dir="$1"
    local state_file="$worker_dir/circuit-state.json"

    if [ ! -f "$state_file" ]; then
        echo "CLOSED"
        return
    fi

    jq -r '.state // "CLOSED"' "$state_file"
}

# Check if circuit is open (worker should stop)
# Usage: cb_is_open <worker_dir>
# Returns: 0 if open (should stop), 1 if closed (continue)
cb_is_open() {
    local worker_dir="$1"
    local state=$(cb_get_state "$worker_dir")

    [ "$state" = "OPEN" ]
}

# Record progress indicators for an iteration
# Usage: cb_record_progress <worker_dir> <iteration> <file_changes> <prd_updated> <meaningful_output>
# file_changes: number of files changed
# prd_updated: 1 if PRD was updated, 0 otherwise
# meaningful_output: 1 if iteration produced meaningful output, 0 otherwise
cb_record_progress() {
    local worker_dir="$1"
    local iteration="$2"
    local file_changes="${3:-0}"
    local prd_updated="${4:-0}"
    local meaningful_output="${5:-0}"
    local progress_file="$worker_dir/progress-log.json"
    local state_file="$worker_dir/circuit-state.json"

    # Determine if this iteration made progress
    local has_progress=0
    if [ "$file_changes" -gt 0 ] || [ "$prd_updated" -eq 1 ] || [ "$meaningful_output" -eq 1 ]; then
        has_progress=1
    fi

    # Record progress entry
    local entry=$(jq -n \
        --arg iteration "$iteration" \
        --arg file_changes "$file_changes" \
        --arg prd_updated "$prd_updated" \
        --arg meaningful_output "$meaningful_output" \
        --arg has_progress "$has_progress" \
        '{
            iteration: ($iteration | tonumber),
            file_changes: ($file_changes | tonumber),
            prd_updated: ($prd_updated | tonumber),
            meaningful_output: ($meaningful_output | tonumber),
            has_progress: ($has_progress | tonumber),
            timestamp: now | strftime("%Y-%m-%dT%H:%M:%SZ")
        }')

    # Append to progress log
    local temp_file
    temp_file=$(mktemp)
    jq --argjson entry "$entry" '. + [$entry]' "$progress_file" > "$temp_file"
    mv "$temp_file" "$progress_file"

    # Temporary file for safely updating state
    local state_temp_file
    state_temp_file=$(mktemp)

    # Update state based on progress
    if [ "$has_progress" -eq 1 ]; then
        # Reset no-progress counter on any progress and update iteration
        jq --arg iteration "$iteration" \
            '.no_progress_count = 0
             | .last_progress_time = (now | strftime("%Y-%m-%dT%H:%M:%SZ"))
             | .iteration = ($iteration | tonumber)' \
            "$state_file" > "$state_temp_file"
        mv "$state_temp_file" "$state_file"
        log_debug "Progress detected in iteration $iteration (files: $file_changes, prd: $prd_updated)"
    else
        # Increment no-progress counter and update iteration
        local new_count
        new_count=$(jq '.no_progress_count + 1' "$state_file")
        jq --arg count "$new_count" --arg iteration "$iteration" \
            '.no_progress_count = ($count | tonumber)
             | .iteration = ($iteration | tonumber)' \
            "$state_file" > "$state_temp_file"
        mv "$state_temp_file" "$state_file"
        log_debug "No progress in iteration $iteration (count: $new_count)"

        # Check if we should open the circuit
        if [ "$new_count" -ge "$CB_MAX_NO_PROGRESS_LOOPS" ]; then
            cb_open "$worker_dir" "NO_PROGRESS" "No progress detected for $new_count consecutive iterations"
        fi
    fi
}

# Record an error and check for patterns
# Usage: cb_record_error <worker_dir> <error_message>
cb_record_error() {
    local worker_dir="$1"
    local error_message="$2"
    local state_file="$worker_dir/circuit-state.json"
    local hash_file="$worker_dir/error-hashes.log"

    # Compute error hash (normalize whitespace and timestamps)
    local normalized_error=$(echo "$error_message" | \
        sed -E 's/[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}[^ ]*/TIMESTAMP/g' | \
        sed -E 's/[0-9]+\.[0-9]+s/TIME/g' | \
        tr -s '[:space:]' ' ' | \
        head -c 1000)
    local error_hash=$(echo "$normalized_error" | md5sum | cut -d' ' -f1)

    # Get last error hash
    local last_hash=$(jq -r '.last_error_hash // ""' "$state_file")

    # Record error hash with timestamp
    echo "$(date -Iseconds) $error_hash" >> "$hash_file"

    # Check if identical to last error
    if [ "$error_hash" = "$last_hash" ]; then
        # Increment identical error count
        local temp_file=$(mktemp)
        local new_count=$(jq '.identical_error_count + 1' "$state_file")
        jq --arg count "$new_count" --arg hash "$error_hash" \
            '.identical_error_count = ($count | tonumber) | .last_error_hash = $hash' \
            "$state_file" > "$temp_file"
        mv "$temp_file" "$state_file"

        log_debug "Identical error detected (hash: ${error_hash:0:8}..., count: $new_count)"

        # Check if we should open the circuit
        if [ "$new_count" -ge "$CB_MAX_IDENTICAL_ERROR_LOOPS" ]; then
            cb_open "$worker_dir" "IDENTICAL_ERROR" "Same error pattern repeated $new_count times (hash: ${error_hash:0:8}...)"
        fi
    else
        # Different error - reset identical count but keep hash
        local temp_file=$(mktemp)
        jq --arg hash "$error_hash" \
            '.identical_error_count = 1 | .last_error_hash = $hash' \
            "$state_file" > "$temp_file"
        mv "$temp_file" "$state_file"
        log_debug "New error pattern detected (hash: ${error_hash:0:8}...)"
    fi
}

# Classify error as transient or persistent
# Usage: cb_classify_error <worker_dir> <error_hash>
# Returns: "transient" or "persistent"
cb_classify_error() {
    local worker_dir="$1"
    local error_hash="$2"
    local hash_file="$worker_dir/error-hashes.log"

    if [ ! -f "$hash_file" ]; then
        echo "transient"
        return
    fi

    # Count occurrences of this error hash (fixed-string, whole-word match)
    local count=$(grep -Fwc -- "$error_hash" "$hash_file" 2>/dev/null || echo "0")

    if [ "$count" -le "$CB_TRANSIENT_ERROR_THRESHOLD" ]; then
        echo "transient"
    else
        echo "persistent"
    fi
}

# Get error classification summary
# Usage: cb_get_error_summary <worker_dir>
# Returns: JSON with transient and persistent error counts
cb_get_error_summary() {
    local worker_dir="$1"
    local hash_file="$worker_dir/error-hashes.log"

    if [ ! -f "$hash_file" ]; then
        jq -n '{ transient: 0, persistent: 0, unique_errors: 0 }'
        return
    fi

    # Get unique hashes and their counts
    local unique_hashes=$(grep -v '^#' "$hash_file" | awk '{print $2}' | sort | uniq -c | sort -rn)

    local transient=0
    local persistent=0
    local unique=0

    while read -r count hash; do
        # Skip empty lines or invalid entries
        [ -z "$hash" ] && continue
        # Ensure count is a valid number before comparison
        [[ ! "$count" =~ ^[0-9]+$ ]] && continue
        ((unique++))
        if [ "$count" -le "$CB_TRANSIENT_ERROR_THRESHOLD" ]; then
            ((transient++))
        else
            ((persistent++))
        fi
    done <<< "$unique_hashes"

    jq -n \
        --arg transient "$transient" \
        --arg persistent "$persistent" \
        --arg unique "$unique" \
        '{
            transient: ($transient | tonumber),
            persistent: ($persistent | tonumber),
            unique_errors: ($unique | tonumber)
        }'
}

# Open the circuit (trip the breaker)
# Usage: cb_open <worker_dir> <reason_code> <reason_message>
cb_open() {
    local worker_dir="$1"
    local reason_code="$2"
    local reason_message="$3"
    local state_file="$worker_dir/circuit-state.json"

    local temp_file=$(mktemp)
    jq --arg reason "$reason_code" --arg message "$reason_message" \
        '.state = "OPEN" | .trip_reason = $reason | .trip_message = $message | .trip_time = (now | strftime("%Y-%m-%dT%H:%M:%SZ"))' \
        "$state_file" > "$temp_file"
    mv "$temp_file" "$state_file"

    log_error "Circuit breaker OPENED: $reason_code - $reason_message"
}

# Reset the circuit (close the breaker)
# Usage: cb_reset <worker_dir>
cb_reset() {
    local worker_dir="$1"
    local state_file="$worker_dir/circuit-state.json"

    if [ ! -f "$state_file" ]; then
        cb_init "$worker_dir"
        return
    fi

    local temp_file=$(mktemp)
    jq '.state = "CLOSED" | .no_progress_count = 0 | .identical_error_count = 0 | .trip_reason = null | .trip_message = null | .trip_time = null | .reset_time = (now | strftime("%Y-%m-%dT%H:%M:%SZ"))' \
        "$state_file" > "$temp_file"
    mv "$temp_file" "$state_file"

    log "Circuit breaker RESET to CLOSED state"
}

# Get circuit breaker status for display
# Usage: cb_get_status <worker_dir>
# Returns: JSON with full status info
cb_get_status() {
    local worker_dir="$1"
    local state_file="$worker_dir/circuit-state.json"
    local progress_file="$worker_dir/progress-log.json"

    if [ ! -f "$state_file" ]; then
        jq -n '{
            state: "NOT_INITIALIZED",
            no_progress_count: 0,
            identical_error_count: 0,
            total_iterations: 0
        }'
        return
    fi

    # Get base state
    local base_state=$(cat "$state_file")

    # Get progress summary
    local total_iterations=0
    local progress_iterations=0
    if [ -f "$progress_file" ]; then
        total_iterations=$(jq 'length' "$progress_file")
        progress_iterations=$(jq '[.[] | select(.has_progress == 1)] | length' "$progress_file")
    fi

    # Get error summary
    local error_summary=$(cb_get_error_summary "$worker_dir")

    # Combine into full status
    echo "$base_state" | jq \
        --argjson total "$total_iterations" \
        --argjson progress "$progress_iterations" \
        --argjson errors "$error_summary" \
        '. + {
            total_iterations: $total,
            progress_iterations: $progress,
            error_summary: $errors
        }'
}

# Get human-readable status line for display
# Usage: cb_get_status_line <worker_dir>
cb_get_status_line() {
    local worker_dir="$1"
    local state=$(cb_get_state "$worker_dir")
    local state_file="$worker_dir/circuit-state.json"

    if [ ! -f "$state_file" ]; then
        echo "Circuit: NOT_INITIALIZED"
        return
    fi

    local no_progress=$(jq -r '.no_progress_count // 0' "$state_file")
    local identical_err=$(jq -r '.identical_error_count // 0' "$state_file")

    case "$state" in
        CLOSED)
            echo "Circuit: CLOSED (no-progress: $no_progress/$CB_MAX_NO_PROGRESS_LOOPS, errors: $identical_err/$CB_MAX_IDENTICAL_ERROR_LOOPS)"
            ;;
        OPEN)
            local reason=$(jq -r '.trip_reason // "UNKNOWN"' "$state_file")
            local message=$(jq -r '.trip_message // ""' "$state_file")
            echo "Circuit: OPEN [$reason] - $message"
            ;;
        *)
            echo "Circuit: $state"
            ;;
    esac
}

# Detect progress by comparing git state before and after iteration
# Usage: cb_detect_file_changes <workspace_dir>
# Returns: number of files changed
cb_detect_file_changes() {
    local workspace="$1"

    if [ ! -d "$workspace" ]; then
        echo "0"
        return
    fi

    # Run in a subshell so the caller's working directory is not changed
    local changes=$(
        cd "$workspace" 2>/dev/null || { echo "0"; exit; }
        git status --porcelain 2>/dev/null | wc -l
    )
    echo "$changes"
}

# Detect if PRD was updated since last check
# Usage: cb_detect_prd_update <prd_file> <state_file>
# Returns: 1 if updated, 0 if not
cb_detect_prd_update() {
    local prd_file="$1"
    local state_file="$2"

    if [ ! -f "$prd_file" ]; then
        echo "0"
        return
    fi

    # Get current PRD hash
    local current_hash=$(md5sum "$prd_file" 2>/dev/null | cut -d' ' -f1)

    # Get stored PRD hash from state
    local stored_hash=""
    if [ -f "$state_file" ]; then
        stored_hash=$(jq -r '.last_prd_hash // ""' "$state_file")
    fi

    # Update stored hash
    if [ -f "$state_file" ]; then
        local temp_file=$(mktemp)
        jq --arg hash "$current_hash" '.last_prd_hash = $hash' "$state_file" > "$temp_file"
        mv "$temp_file" "$state_file"
    fi

    # Return 1 if hashes differ and we had a previous hash
    if [ -n "$stored_hash" ] && [ "$current_hash" != "$stored_hash" ]; then
        echo "1"
    else
        echo "0"
    fi
}

# Check iteration output for meaningful content
# Usage: cb_detect_meaningful_output <log_file>
# Returns: 1 if meaningful, 0 if not
cb_detect_meaningful_output() {
    local log_file="$1"

    if [ ! -f "$log_file" ]; then
        echo "0"
        return
    fi

    # Check for tool usage (file edits, writes, etc.)
    local tool_uses=$(grep -c '"type":"tool_use"' "$log_file" 2>/dev/null || echo "0")

    # Check for actual text output
    local text_output=$(grep -c '"type":"text"' "$log_file" 2>/dev/null || echo "0")

    # Consider meaningful if there were tool uses or substantial text output
    if [ "$tool_uses" -gt 0 ] || [ "$text_output" -gt 5 ]; then
        echo "1"
    else
        echo "0"
    fi
}

# Run circuit breaker check at end of iteration
# This is the main integration point called from ralph-loop.sh
# Usage: cb_check_iteration <worker_dir> <iteration> <workspace> <prd_file> <log_file>
# Returns: 0 if should continue, 1 if should stop (circuit open)
cb_check_iteration() {
    local worker_dir="$1"
    local iteration="$2"
    local workspace="$3"
    local prd_file="$4"
    local log_file="$5"
    local state_file="$worker_dir/circuit-state.json"

    # Initialize if needed
    if [ ! -f "$state_file" ]; then
        cb_init "$worker_dir"
    fi

    # Check if circuit is already open
    if cb_is_open "$worker_dir"; then
        log_error "Circuit breaker is OPEN - worker should stop"
        return 1
    fi

    # Detect progress indicators
    local file_changes=$(cb_detect_file_changes "$workspace")
    local prd_updated=$(cb_detect_prd_update "$prd_file" "$state_file")
    local meaningful_output=$(cb_detect_meaningful_output "$log_file")

    # Record progress
    cb_record_progress "$worker_dir" "$iteration" "$file_changes" "$prd_updated" "$meaningful_output"

    # Check if circuit was opened by progress check
    if cb_is_open "$worker_dir"; then
        return 1
    fi

    return 0
}

# Check for error patterns in iteration output
# Usage: cb_check_errors <worker_dir> <log_file>
cb_check_errors() {
    local worker_dir="$1"
    local log_file="$2"

    if [ ! -f "$log_file" ]; then
        return 0
    fi

    # Extract error messages from log
    local errors=$(grep -i '"error"' "$log_file" 2>/dev/null | head -5)

    if [ -n "$errors" ]; then
        cb_record_error "$worker_dir" "$errors"
    fi

    # Check if circuit was opened
    cb_is_open "$worker_dir" && return 1
    return 0
}
