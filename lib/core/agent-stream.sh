#!/usr/bin/env bash
# =============================================================================
# agent-stream.sh - Stream-JSON extraction utilities
#
# Provides utilities for parsing Claude CLI stream-JSON output format.
# Stream-JSON contains one JSON object per line, with assistant messages having
# the format: {"type":"assistant","message":{"content":[{"type":"text","text":"..."}]}}
#
# Split from agent-base.sh for maintainability.
# =============================================================================
set -euo pipefail

[ -n "${_AGENT_STREAM_LOADED:-}" ] && return 0
_AGENT_STREAM_LOADED=1

# Source platform helpers for portable grep
source "${WIGGUM_HOME:-$(dirname "$(dirname "$(dirname "${BASH_SOURCE[0]}")")")}/lib/core/platform.sh"

# =============================================================================
# STREAM-JSON EXTRACTION UTILITIES
# =============================================================================

# Extract all text content from assistant messages in a stream-JSON log file
#
# Args:
#   log_file - Path to the stream-JSON log file
#
# Returns: All text content from assistant messages, one per line
_extract_text_from_stream_json() {
    local log_file="$1"

    if [ ! -f "$log_file" ]; then
        return 1
    fi

    grep '"type":"assistant"' "$log_file" 2>/dev/null | \
        jq -r 'select(.message.content[]? | .type == "text") | .message.content[] | select(.type == "text") | .text' 2>/dev/null \
        || true
}

# Extract the LAST occurrence of a result value from stream-JSON
# This fixes the bug where the first occurrence (from examples in prompts) was returned
#
# Args:
#   log_file     - Path to the stream-JSON log file
#   valid_values - Pipe-separated list of valid values (e.g., "PASS|FAIL")
#
# Returns: The LAST result value found, or empty string if none
_extract_result_value_from_stream_json() {
    local log_file="$1"
    local valid_values="$2"

    if [ ! -f "$log_file" ]; then
        return 1
    fi

    # Extract text, find all <result>VALUE</result> matches, take LAST one
    _extract_text_from_stream_json "$log_file" | \
        grep_pcre_match "(?<=<result>)(${valid_values})(?=</result>)" | \
        tail -1 \
        || true
}

# Extract session_id from stream-JSON log file
#
# The session_id is stored in the iteration_start JSON object at the beginning
# of the log file with format: {"type":"iteration_start",...,"session_id":"<uuid>",...}
#
# Args:
#   log_file - Path to the stream-JSON log file
#
# Returns: UUID session_id or empty string if not found
_extract_session_id_from_log() {
    local log_file="$1"

    [ ! -f "$log_file" ] && return 0

    # Look for session_id in iteration_start JSON object (typically first line)
    # Pattern matches: "session_id":"<uuid>" where uuid is hex with dashes
    grep_pcre_match '"session_id"\s*:\s*"\K[a-f0-9-]+(?=")' "$log_file" | head -1 || true
}

# Resume session with focused prompt to extract result (backup mechanism)
#
# When result extraction fails (UNKNOWN), this function attempts to resume
# the Claude session and request only the result tag.
#
# Args:
#   session_id   - Session ID to resume
#   valid_values - Pipe-separated valid result values (e.g., "PASS|FAIL")
#   worker_dir   - Worker directory path
#   log_prefix   - Log file prefix for naming the backup log
#
# Returns: Extracted result value or "UNKNOWN"
_backup_result_extraction() {
    local session_id="$1"
    local valid_values="$2"
    local worker_dir="$3"
    local log_prefix="$4"

    # Convert pipe-separated values to human-readable format
    local human_values="${valid_values//|/, }"

    # Strong prompt to interrupt ongoing work and force result output
    local prompt="STOP ALL YOUR WORK IMMEDIATELY. DO NOT CONTINUE ANY PREVIOUS TASKS.

Based on your previous work, provide ONLY the final result.
Valid results: ${human_values}
Format: <result>VALUE</result>

RESPOND ONLY WITH THE RESULT TAG. NO OTHER OUTPUT."

    # Create backup log directory and file
    local run_id="${RALPH_RUN_ID:-default}"
    local backup_log
    backup_log="$worker_dir/logs/$run_id/${log_prefix}-backup-$(date +%s).log"
    mkdir -p "$(dirname "$backup_log")"

    # Source runtime (provides resume capabilities)
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"

    # Attempt to resume session with focused prompt (max 7 turns to allow completion)
    if ! run_agent_resume "$session_id" "$prompt" "$backup_log" 7 2>/dev/null; then
        echo "UNKNOWN"
        return 0
    fi

    # Extract result from backup log
    local backup_result
    backup_result=$(_extract_result_value_from_stream_json "$backup_log" "$valid_values") || true

    if [ -n "$backup_result" ]; then
        echo "$backup_result"
    else
        echo "UNKNOWN"
    fi
}

# Extract content between the LAST occurrence of XML-style tags from stream-JSON
# This fixes the bug where sed was trying to match tags in raw JSON instead of extracted text
#
# Args:
#   log_file - Path to the stream-JSON log file
#   tag      - Tag name without brackets (e.g., "review", "report")
#
# Returns: Content between the last occurrence of <tag> and </tag>
_extract_tag_content_from_stream_json() {
    local log_file="$1"
    local tag="$2"

    if [ ! -f "$log_file" ]; then
        return 1
    fi

    # Extract text content first, then find the last occurrence of the tag
    # Use tac to reverse lines, find first match (which is last in original), reverse back
    local extracted_text
    extracted_text=$(_extract_text_from_stream_json "$log_file") || true

    if [ -z "$extracted_text" ]; then
        return 1
    fi

    # Use awk to extract the last occurrence of tag content
    # Handles both same-line tags (<tag>content</tag>) and multi-line tags
    echo "$extracted_text" | awk -v tag="$tag" '
        BEGIN { content = ""; in_tag = 0 }
        {
            # Check for opening tag
            if ($0 ~ "<" tag ">") {
                in_tag = 1
                content = ""
                # Extract content after opening tag on same line
                line = $0
                sub(".*<" tag ">", "", line)
                # Check if closing tag is also on same line
                if (line ~ "</" tag ">") {
                    sub("</" tag ">.*", "", line)
                    if (line != "") content = line
                    in_tag = 0
                } else if (line != "") {
                    content = line
                }
                next
            }
            # Check for closing tag
            if ($0 ~ "</" tag ">") {
                # Extract content before closing tag on same line
                line = $0
                sub("</" tag ">.*", "", line)
                if (line != "") content = content (content ? "\n" : "") line
                in_tag = 0
                next
            }
            # Inside tag, accumulate content
            if (in_tag) {
                content = content (content ? "\n" : "") $0
            }
        }
        END { print content }
    '
}
