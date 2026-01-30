#!/usr/bin/env bash
# =============================================================================
# backend-interface.sh - Backend contract for runtime abstraction
#
# Defines all functions a backend must implement. Provides sensible defaults
# (no-op / error) for optional functions. A backend sources this file first,
# then overrides the functions it supports.
#
# Required functions (backend MUST override):
#   runtime_backend_init
#   runtime_backend_invoke
#   runtime_backend_build_exec_args
#   runtime_backend_build_resume_args
#   runtime_backend_is_retryable
#   runtime_backend_extract_text
#   runtime_backend_extract_session_id
#
# Optional functions (defaults provided):
#   runtime_backend_supports_sessions
#   runtime_backend_usage_update
#   runtime_backend_rate_limit_check
#   runtime_backend_rate_limit_wait
#   runtime_backend_generate_session_id
#   runtime_backend_name
# =============================================================================
set -euo pipefail

[ -n "${_BACKEND_INTERFACE_LOADED:-}" ] && return 0
_BACKEND_INTERFACE_LOADED=1

# =============================================================================
# REQUIRED FUNCTIONS (must be overridden by backend)
# =============================================================================

# Initialize backend (load config, set env vars, validate binary exists)
# Called once during runtime_init()
runtime_backend_init() {
    log_error "runtime_backend_init: not implemented by backend"
    return 1
}

# Invoke the backend CLI with scoped auth
# This is the raw execution primitive - no retry, no parsing
#
# Args: all CLI arguments (as array elements)
# Returns: exit code from the CLI
runtime_backend_invoke() {
    log_error "runtime_backend_invoke: not implemented by backend"
    return 1
}

# Build CLI arguments for single-shot execution (nameref array pattern)
# Populates the caller's array by reference - avoids word-splitting issues
#
# Args:
#   _out_args     - nameref to caller's array (populated by this function)
#   workspace     - working directory
#   system_prompt - system context string
#   user_prompt   - user task string
#   output_file   - log destination path
#   max_turns     - turn limit
#   session_id    - session ID (empty string for anonymous)
#
# Usage:
#   local -a cli_args=()
#   runtime_backend_build_exec_args cli_args "$workspace" "$prompt" ...
#   runtime_exec_with_retry "${cli_args[@]}"
runtime_backend_build_exec_args() {
    log_error "runtime_backend_build_exec_args: not implemented by backend"
    return 1
}

# Build CLI arguments for session resume (nameref array pattern)
#
# Args:
#   _out_args   - nameref to caller's array
#   session_id  - session to resume
#   prompt      - follow-up prompt
#   output_file - log destination
#   max_turns   - turn limit
runtime_backend_build_resume_args() {
    log_error "runtime_backend_build_resume_args: not implemented by backend"
    return 1
}

# Classify whether an error is retryable
#
# Args:
#   exit_code    - exit code from the CLI
#   stderr_file  - path to file containing captured stderr output
#
# Returns: 0 = retryable, 1 = not retryable
runtime_backend_is_retryable() {
    return 1  # Default: nothing is retryable
}

# Extract plain text from backend-specific output format
#
# Args:
#   log_file - path to the output log file
#
# Echoes: extracted text content
runtime_backend_extract_text() {
    log_error "runtime_backend_extract_text: not implemented by backend"
    return 1
}

# Extract session ID from backend output log
#
# Args:
#   log_file - path to the output log file
#
# Echoes: session ID string (or empty if not supported)
runtime_backend_extract_session_id() {
    echo ""
}

# =============================================================================
# OPTIONAL FUNCTIONS (defaults provided, override as needed)
# =============================================================================

# Check if backend supports session resumption
# Returns: 0 = yes, 1 = no
# Default: return 1 (no session support)
runtime_backend_supports_sessions() {
    return 1
}

# Update usage statistics to shared file
#
# Args:
#   ralph_dir - ralph directory path
#
# Default: no-op
runtime_backend_usage_update() {
    return 0
}

# Check if rate limited
#
# Args:
#   ralph_dir - ralph directory path
#
# Returns: 0 = rate limited, 1 = OK
# Default: return 1 (never limited)
runtime_backend_rate_limit_check() {
    return 1
}

# Wait for rate limit window to reset
# Default: sleep 60
runtime_backend_rate_limit_wait() {
    sleep 60
}

# Generate a new unique session ID
# Echoes: session ID string
runtime_backend_generate_session_id() {
    uuidgen 2>/dev/null || cat /proc/sys/kernel/random/uuid 2>/dev/null || echo "$(date +%s)-$$-$RANDOM"
}

# Get backend name for logging/config
# Echoes: backend name string
runtime_backend_name() {
    echo "unknown"
}
