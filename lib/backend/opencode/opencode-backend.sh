#!/usr/bin/env bash
# =============================================================================
# opencode-backend.sh - OpenCode backend skeleton
#
# Stub implementation of the backend interface (lib/runtime/backend-interface.sh)
# for the OpenCode CLI. Each function has a documented TODO for implementors.
#
# To complete this backend:
#   1. Implement each TODO function
#   2. Test with: WIGGUM_RUNTIME_BACKEND=opencode wiggum run
#   3. See docs/RUNTIME-SCHEMA.md for the full backend contract
# =============================================================================
set -euo pipefail

[ -n "${_OPENCODE_BACKEND_LOADED:-}" ] && return 0
_OPENCODE_BACKEND_LOADED=1

source "$WIGGUM_HOME/lib/core/logger.sh"

# =============================================================================
# BACKEND IDENTITY
# =============================================================================

runtime_backend_name() {
    echo "opencode"
}

# =============================================================================
# INITIALIZATION
# =============================================================================

runtime_backend_init() {
    OPENCODE="${OPENCODE:-opencode}"
    # TODO: Load OpenCode-specific config, auth tokens, API settings
    # TODO: Validate that the opencode binary exists on PATH
    log_debug "OpenCode backend initialized (binary: $OPENCODE)"
}

# =============================================================================
# INVOCATION
# =============================================================================

runtime_backend_invoke() {
    # TODO: Invoke OpenCode CLI with appropriate auth scoping
    # Example: OPENCODE_API_KEY="$_TOKEN" "$OPENCODE" "$@"
    "$OPENCODE" "$@"
}

# =============================================================================
# ARGUMENT BUILDING
# =============================================================================

runtime_backend_build_exec_args() {
    local -n _args="$1"
    # shellcheck disable=SC2034  # All args defined for implementors to use
    local workspace="$2" system_prompt="$3" user_prompt="$4"
    # shellcheck disable=SC2034
    local output_file="$5" max_turns="$6" session_id="${7:-}"

    # TODO: Build OpenCode CLI arguments for single-shot execution
    # Map workspace, system_prompt, user_prompt, max_turns to OpenCode flags
    # Example:
    #   _args=(--workspace "$workspace" --system "$system_prompt" --prompt "$user_prompt")
    #   [ -n "$session_id" ] && _args+=(--session "$session_id")
    log_error "opencode backend: build_exec_args not yet implemented"
    return 1
}

runtime_backend_build_resume_args() {
    local -n _args="$1"
    # shellcheck disable=SC2034  # All args defined for implementors to use
    local session_id="$2" prompt="$3"
    # shellcheck disable=SC2034
    local output_file="$4" max_turns="${5:-3}"

    # TODO: Build OpenCode CLI arguments for session resume (if supported)
    # Example:
    #   _args=(--resume "$session_id" --prompt "$prompt" --max-turns "$max_turns")
    log_error "opencode backend: build_resume_args not yet implemented"
    return 1
}

# =============================================================================
# ERROR CLASSIFICATION
# =============================================================================

runtime_backend_is_retryable() {
    # shellcheck disable=SC2034  # Args defined for implementors to use
    local exit_code="$1" stderr_file="$2"

    # TODO: Define OpenCode-specific retryable exit codes and error patterns
    # Example:
    #   [[ "$exit_code" -eq 5 || "$exit_code" -eq 124 ]] && return 0
    #   if [ "$exit_code" -eq 1 ] && [ -s "$stderr_file" ]; then
    #       grep -qi "rate limit" "$stderr_file" 2>/dev/null && return 0
    #   fi
    return 1  # Conservative default: nothing is retryable
}

# =============================================================================
# OUTPUT EXTRACTION
# =============================================================================

runtime_backend_extract_text() {
    # shellcheck disable=SC2034  # log_file for implementors
    local log_file="$1"

    # TODO: Parse OpenCode output format to extract assistant text
    # The implementation depends on OpenCode's output format (JSON, plain text, etc.)
    return 1
}

runtime_backend_extract_session_id() {
    # shellcheck disable=SC2034  # log_file for implementors
    local log_file="$1"

    # TODO: Extract session ID from OpenCode output (if applicable)
    echo ""
}

# =============================================================================
# SESSION SUPPORT
# =============================================================================

runtime_backend_supports_sessions() {
    # TODO: Set to 0 (return 0) if OpenCode supports session resumption
    return 1  # Default: no session support
}
