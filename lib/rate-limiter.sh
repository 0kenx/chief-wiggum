#!/usr/bin/env bash
# Rate limiter for API calls using a sliding window algorithm
# Tracks API calls per hour across all workers to prevent runaway costs

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/logger.sh"
source "$SCRIPT_DIR/file-lock.sh"

# Default rate limit: 100 calls per hour
DEFAULT_RATE_LIMIT=100

# Window size in seconds (1 hour)
RATE_LIMIT_WINDOW=3600

# Get the rate limit file path
# Usage: get_rate_limit_file [ralph_dir]
get_rate_limit_file() {
    local ralph_dir="${1:-$RALPH_DIR}"
    echo "$ralph_dir/rate-limit.json"
}

# Initialize rate limit state file if it doesn't exist
# Usage: init_rate_limit_state <rate_limit_file>
init_rate_limit_state() {
    local rate_limit_file="$1"

    if [ ! -f "$rate_limit_file" ]; then
        echo '{"calls":[]}' > "$rate_limit_file"
    fi
}

# Record an API call with the current timestamp
# Usage: record_api_call <rate_limit_file>
record_api_call() {
    local rate_limit_file="$1"
    local current_time=$(date +%s)

    # Ensure file exists
    init_rate_limit_state "$rate_limit_file"

    # Use file locking to prevent race conditions between workers
    with_file_lock "$rate_limit_file" 5 \
        _record_api_call_internal "$rate_limit_file" "$current_time"
}

# Internal function to record API call (called with lock held)
_record_api_call_internal() {
    local rate_limit_file="$1"
    local current_time="$2"
    local window_start=$((current_time - RATE_LIMIT_WINDOW))

    # Read current state, prune old calls, and add new call
    local temp_file=$(mktemp)

    jq --argjson now "$current_time" --argjson window_start "$window_start" \
       '.calls = ([.calls[] | select(. >= $window_start)] + [$now])' \
       "$rate_limit_file" > "$temp_file" 2>/dev/null

    if [ $? -eq 0 ] && [ -s "$temp_file" ]; then
        mv "$temp_file" "$rate_limit_file"
    else
        rm -f "$temp_file"
        # If jq fails, create fresh state with new call
        echo "{\"calls\":[$current_time]}" > "$rate_limit_file"
    fi
}

# Get the current number of API calls in the sliding window
# Usage: get_current_call_count <rate_limit_file>
# Returns: Number of calls in the current hour window
get_current_call_count() {
    local rate_limit_file="$1"
    local current_time=$(date +%s)
    local window_start=$((current_time - RATE_LIMIT_WINDOW))

    if [ ! -f "$rate_limit_file" ]; then
        echo "0"
        return
    fi

    # Count calls within the window
    jq --argjson window_start "$window_start" \
       '[.calls[] | select(. >= $window_start)] | length' \
       "$rate_limit_file" 2>/dev/null || echo "0"
}

# Check rate limit status and return appropriate action
# Usage: check_rate_limit <rate_limit_file> <max_calls>
# Returns: 0 = OK, 1 = Warning (80%+), 2 = Exceeded (100%+)
# Output: JSON with status information
check_rate_limit() {
    local rate_limit_file="$1"
    local max_calls="${2:-$DEFAULT_RATE_LIMIT}"
    local current_count=$(get_current_call_count "$rate_limit_file")

    local percentage=0
    if [ "$max_calls" -gt 0 ]; then
        percentage=$((current_count * 100 / max_calls))
    fi

    local status="ok"
    local exit_code=0

    if [ "$current_count" -ge "$max_calls" ]; then
        status="exceeded"
        exit_code=2
    elif [ "$percentage" -ge 80 ]; then
        status="warning"
        exit_code=1
    fi

    # Output JSON status
    jq -n --arg status "$status" \
          --argjson current "$current_count" \
          --argjson limit "$max_calls" \
          --argjson percentage "$percentage" \
          '{
            status: $status,
            current_calls: $current,
            limit: $limit,
            percentage: $percentage,
            remaining: ($limit - $current)
          }'

    return $exit_code
}

# Wait until rate limit allows another call
# Usage: wait_for_rate_limit <rate_limit_file> <max_calls>
# Returns: 0 when ready to proceed
wait_for_rate_limit() {
    local rate_limit_file="$1"
    local max_calls="${2:-$DEFAULT_RATE_LIMIT}"
    local check_interval=30  # Check every 30 seconds
    local first_wait=true

    while true; do
        local current_count=$(get_current_call_count "$rate_limit_file")

        if [ "$current_count" -lt "$max_calls" ]; then
            # Under limit, can proceed
            return 0
        fi

        if [ "$first_wait" = true ]; then
            log_error "Rate limit reached ($current_count/$max_calls calls/hour). Worker paused - will resume when calls expire from window."
            first_wait=false
        fi

        # Calculate when oldest call will expire
        local oldest_call=$(jq '.calls | min // 0' "$rate_limit_file" 2>/dev/null || echo "0")
        local current_time=$(date +%s)
        local window_end=$((oldest_call + RATE_LIMIT_WINDOW))
        local wait_time=$((window_end - current_time + 1))

        if [ "$wait_time" -gt 0 ]; then
            log "Waiting ~$wait_time seconds for rate limit to reset..."
            # Wait in smaller chunks so we can respond to signals
            local waited=0
            while [ "$waited" -lt "$wait_time" ] && [ "$waited" -lt "$check_interval" ]; do
                sleep 5
                waited=$((waited + 5))
            done
        else
            sleep "$check_interval"
        fi
    done
}

# Print human-readable rate limit status
# Usage: print_rate_status <rate_limit_file> <max_calls>
print_rate_status() {
    local rate_limit_file="$1"
    local max_calls="${2:-$DEFAULT_RATE_LIMIT}"

    if [ ! -f "$rate_limit_file" ]; then
        echo "No rate limit data found. No API calls recorded yet."
        return 0
    fi

    local current_count=$(get_current_call_count "$rate_limit_file")
    local percentage=0
    if [ "$max_calls" -gt 0 ]; then
        percentage=$((current_count * 100 / max_calls))
    fi
    local remaining=$((max_calls - current_count))

    echo "=== API Rate Limit Status ==="
    echo ""
    echo "Current usage: $current_count / $max_calls calls per hour ($percentage%)"
    echo "Remaining:     $remaining calls"
    echo ""

    # Visual progress bar
    local bar_width=40
    local filled=$((percentage * bar_width / 100))
    if [ "$filled" -gt "$bar_width" ]; then
        filled=$bar_width
    fi
    local empty=$((bar_width - filled))

    printf "["
    if [ "$percentage" -ge 100 ]; then
        printf "\033[31m"  # Red
    elif [ "$percentage" -ge 80 ]; then
        printf "\033[33m"  # Yellow
    else
        printf "\033[32m"  # Green
    fi
    printf "%${filled}s" | tr ' ' '█'
    printf "\033[0m"
    printf "%${empty}s" | tr ' ' '░'
    printf "] %d%%\n" "$percentage"
    echo ""

    # Status message
    if [ "$percentage" -ge 100 ]; then
        echo "⚠️  RATE LIMIT EXCEEDED - Workers are paused"

        # Show time until oldest call expires
        local oldest_call=$(jq '.calls | min // 0' "$rate_limit_file" 2>/dev/null || echo "0")
        local current_time=$(date +%s)
        local window_end=$((oldest_call + RATE_LIMIT_WINDOW))
        local wait_time=$((window_end - current_time))

        if [ "$wait_time" -gt 0 ]; then
            local wait_mins=$((wait_time / 60))
            local wait_secs=$((wait_time % 60))
            echo "   Next slot available in: ${wait_mins}m ${wait_secs}s"
        fi
    elif [ "$percentage" -ge 80 ]; then
        echo "⚠️  WARNING: Approaching rate limit ($percentage%)"
    else
        echo "✓ Rate limit OK"
    fi
    echo ""

    # Show recent call distribution
    echo "Call distribution (last hour):"
    local current_time=$(date +%s)
    local intervals=6  # 10-minute intervals
    local interval_size=$((RATE_LIMIT_WINDOW / intervals))

    for ((i=0; i<intervals; i++)); do
        local interval_start=$((current_time - RATE_LIMIT_WINDOW + i * interval_size))
        local interval_end=$((interval_start + interval_size))
        local interval_count=$(jq --argjson start "$interval_start" --argjson end "$interval_end" \
            '[.calls[] | select(. >= $start and . < $end)] | length' \
            "$rate_limit_file" 2>/dev/null || echo "0")

        local mins_ago=$(((intervals - i - 1) * 10 + 10))
        local mins_ago_end=$(((intervals - i - 1) * 10))
        printf "  %2d-%2d min ago: %3d calls\n" "$mins_ago" "$mins_ago_end" "$interval_count"
    done
}

# Get the configured rate limit from environment or default
# Usage: get_rate_limit
get_rate_limit() {
    echo "${WIGGUM_RATE_LIMIT:-$DEFAULT_RATE_LIMIT}"
}
