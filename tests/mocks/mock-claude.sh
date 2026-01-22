#!/usr/bin/env bash
# mock-claude.sh - Mock Claude CLI for testing without API calls
#
# Simulates Claude CLI behavior for testing agent workflows.
# Controlled by environment variables to simulate different scenarios.
#
# Usage:
#   export CLAUDE=/path/to/mock-claude.sh
#   # Run wiggum tests
#
# Environment variables:
#   MOCK_CLAUDE_EXIT_CODE    - Exit code to return (default: 0)
#   MOCK_CLAUDE_RESPONSE     - Response text to output
#   MOCK_CLAUDE_DELAY        - Seconds to delay before responding (default: 0)
#   MOCK_CLAUDE_FAIL_AFTER   - Fail after N invocations (for testing retries)
#   MOCK_CLAUDE_LOG_DIR      - Directory to log invocations
set -euo pipefail

# Track invocations
MOCK_INVOCATION_COUNT_FILE="${MOCK_CLAUDE_LOG_DIR:-/tmp}/mock-claude-invocations"

# Log invocation for debugging
_log_invocation() {
    local log_dir="${MOCK_CLAUDE_LOG_DIR:-/tmp}"
    mkdir -p "$log_dir"

    # Increment invocation counter
    local count=0
    if [ -f "$MOCK_INVOCATION_COUNT_FILE" ]; then
        count=$(cat "$MOCK_INVOCATION_COUNT_FILE")
    fi
    count=$((count + 1))
    echo "$count" > "$MOCK_INVOCATION_COUNT_FILE"

    # Log arguments
    local log_file="$log_dir/mock-claude-invocation-$count.log"
    {
        echo "Timestamp: $(date -Iseconds)"
        echo "Arguments: $*"
        echo "Working Directory: $(pwd)"
        echo "---"
    } > "$log_file"
}

# Generate mock stream-JSON response
_generate_stream_json() {
    local response="${MOCK_CLAUDE_RESPONSE:-Task completed successfully.}"
    local session_id="${MOCK_SESSION_ID:-mock-session-$(date +%s)}"

    # Output in stream-JSON format
    cat << EOF
{"type":"session_start","session_id":"$session_id"}
{"type":"assistant","message":{"content":[{"type":"text","text":"$response"}]}}
{"type":"result","is_error":false}
EOF
}

# Main mock logic
main() {
    _log_invocation "$@"

    # Handle --version
    if [[ " $* " == *" --version "* ]]; then
        echo "claude 1.0.0 (mock)"
        exit 0
    fi

    # Simulate delay if configured
    local delay="${MOCK_CLAUDE_DELAY:-0}"
    if [ "$delay" -gt 0 ]; then
        sleep "$delay"
    fi

    # Check if should fail after N invocations
    if [ -n "${MOCK_CLAUDE_FAIL_AFTER:-}" ]; then
        local count=0
        if [ -f "$MOCK_INVOCATION_COUNT_FILE" ]; then
            count=$(cat "$MOCK_INVOCATION_COUNT_FILE")
        fi
        if [ "$count" -ge "$MOCK_CLAUDE_FAIL_AFTER" ]; then
            echo "Mock Claude: Simulated failure after $count invocations" >&2
            exit 1
        fi
    fi

    # Check output format
    local output_format="text"
    local args=("$@")
    for i in "${!args[@]}"; do
        if [[ "${args[$i]}" == "--output-format" ]] && [ $((i + 1)) -lt ${#args[@]} ]; then
            output_format="${args[$((i + 1))]}"
        fi
    done

    # Generate output based on format
    if [[ "$output_format" == "stream-json" ]]; then
        _generate_stream_json
    else
        echo "${MOCK_CLAUDE_RESPONSE:-Task completed successfully.}"
    fi

    # Return configured exit code
    exit "${MOCK_CLAUDE_EXIT_CODE:-0}"
}

main "$@"
