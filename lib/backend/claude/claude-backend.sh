#!/usr/bin/env bash
# =============================================================================
# claude-backend.sh - Claude Code backend implementation
#
# Implements the backend interface (lib/runtime/backend-interface.sh) for
# Claude Code CLI. Extracted from lib/claude/ files.
# =============================================================================
set -euo pipefail

[ -n "${_CLAUDE_BACKEND_LOADED:-}" ] && return 0
_CLAUDE_BACKEND_LOADED=1

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"

# =============================================================================
# BACKEND IDENTITY
# =============================================================================

runtime_backend_name() {
    echo "claude"
}

# =============================================================================
# INITIALIZATION
# =============================================================================

runtime_backend_init() {
    # Claude binary (allows specifying a different binary or path)
    CLAUDE="${CLAUDE:-claude}"

    # Security: Store auth token in non-exported variable to limit exposure
    _WIGGUM_AUTH_TOKEN="${ANTHROPIC_AUTH_TOKEN:-}"

    # Pass through API configuration environment variables if set
    [ -n "${ANTHROPIC_BASE_URL:-}" ] && export ANTHROPIC_BASE_URL
    [ -n "${API_TIMEOUT_MS:-}" ] && export API_TIMEOUT_MS
    [ -n "${ANTHROPIC_DEFAULT_OPUS_MODEL:-}" ] && export ANTHROPIC_DEFAULT_OPUS_MODEL
    [ -n "${ANTHROPIC_DEFAULT_SONNET_MODEL:-}" ] && export ANTHROPIC_DEFAULT_SONNET_MODEL
    [ -n "${ANTHROPIC_DEFAULT_HAIKU_MODEL:-}" ] && export ANTHROPIC_DEFAULT_HAIKU_MODEL

    log_debug "Claude backend initialized (binary: $CLAUDE)"
}

# =============================================================================
# INVOCATION
# =============================================================================

# Invoke Claude CLI with auth token scoped only to that process
runtime_backend_invoke() {
    if [ -n "${_WIGGUM_AUTH_TOKEN:-}" ]; then
        ANTHROPIC_AUTH_TOKEN="$_WIGGUM_AUTH_TOKEN" "$CLAUDE" "$@"
    else
        "$CLAUDE" "$@"
    fi
}

# =============================================================================
# ARGUMENT BUILDING
# =============================================================================

# Build CLI arguments for single-shot execution
runtime_backend_build_exec_args() {
    # shellcheck disable=SC2178  # nameref pattern for array population
    local -n _args="$1"
    # shellcheck disable=SC2034  # workspace available for other backends
    local workspace="$2"
    local system_prompt="$3"
    local user_prompt="$4"
    # shellcheck disable=SC2034  # output_file handled by caller redirection
    local output_file="$5"
    local max_turns="$6"
    local session_id="${7:-}"

    _args=(--verbose --output-format stream-json)

    if [ -n "$system_prompt" ]; then
        _args+=(--append-system-prompt "$system_prompt")
    fi

    _args+=(--max-turns "$max_turns")
    _args+=(--dangerously-skip-permissions)

    if [ -n "$session_id" ]; then
        _args+=(--session-id "$session_id")
    fi

    if [ -d "${WIGGUM_HOME:-}/skills" ]; then
        _args+=(--plugin-dir "$WIGGUM_HOME/skills")
    fi

    _args+=(-p "$user_prompt")
}

# Build CLI arguments for session resume
runtime_backend_build_resume_args() {
    # shellcheck disable=SC2178  # nameref pattern for array population
    local -n _args="$1"
    local session_id="$2"
    local prompt="$3"
    # shellcheck disable=SC2034  # output_file handled by caller redirection
    local output_file="$4"
    local max_turns="${5:-3}"

    _args=(--verbose --resume "$session_id")
    _args+=(--output-format stream-json)
    _args+=(--max-turns "$max_turns")
    _args+=(--dangerously-skip-permissions)
    _args+=(-p "$prompt")
}

# =============================================================================
# ERROR CLASSIFICATION
# =============================================================================

# Exit codes considered retryable:
# 5 = Claude CLI error (API/service issues)
# 124 = timeout (command timed out)
#
# Also retries exit code 1 with rate-limit stderr patterns

runtime_backend_is_retryable() {
    local exit_code="$1"
    local stderr_file="$2"

    # Direct retryable exit codes
    [[ "$exit_code" -eq 5 || "$exit_code" -eq 124 ]] && return 0

    # Exit 1 + stderr rate-limit patterns
    if [ "$exit_code" -eq 1 ] && [ -s "$stderr_file" ]; then
        local pattern
        for pattern in "429" "rate limit" "too many requests" "High concurrency"; do
            grep -qi "$pattern" "$stderr_file" 2>/dev/null && return 0
        done
    fi

    return 1
}

# =============================================================================
# OUTPUT EXTRACTION
# =============================================================================

# Extract plain text from Claude CLI stream-JSON output
runtime_backend_extract_text() {
    local log_file="$1"

    if [ ! -f "$log_file" ]; then
        return 1
    fi

    grep '"type":"assistant"' "$log_file" 2>/dev/null | \
        jq -r 'select(.message.content[]? | .type == "text") |
               .message.content[] | select(.type == "text") | .text' 2>/dev/null \
        || true
}

# Extract session ID from Claude CLI stream-JSON output
runtime_backend_extract_session_id() {
    local log_file="$1"

    [ ! -f "$log_file" ] && { echo ""; return 0; }

    # Session ID is in iteration_start JSON: {"session_id":"<uuid>"}
    grep_pcre_match '"session_id"\s*:\s*"\K[a-f0-9-]+(?=")' "$log_file" | head -1 || true
}

# =============================================================================
# SESSION SUPPORT
# =============================================================================

runtime_backend_supports_sessions() {
    return 0  # Claude supports sessions
}

runtime_backend_generate_session_id() {
    uuidgen 2>/dev/null || cat /proc/sys/kernel/random/uuid 2>/dev/null || echo "$(date +%s)-$$-$RANDOM"
}

# =============================================================================
# USAGE TRACKING & RATE LIMITING
# =============================================================================

# Lazy-source the usage tracker only when needed
_claude_backend_ensure_usage_tracker() {
    if [ -z "${_CLAUDE_USAGE_TRACKER_LOADED:-}" ]; then
        source "$WIGGUM_HOME/lib/backend/claude/usage-tracker.sh"
        _CLAUDE_USAGE_TRACKER_LOADED=1
    fi
}

runtime_backend_usage_update() {
    local ralph_dir="${1:-}"
    _claude_backend_ensure_usage_tracker
    if [ -n "$ralph_dir" ]; then
        usage_tracker_write_shared "$ralph_dir"
    else
        usage_tracker_update
    fi
}

runtime_backend_rate_limit_check() {
    local ralph_dir="$1"
    _claude_backend_ensure_usage_tracker
    rate_limit_check "$ralph_dir"
}

runtime_backend_rate_limit_wait() {
    _claude_backend_ensure_usage_tracker
    rate_limit_wait_for_cycle_reset
}
