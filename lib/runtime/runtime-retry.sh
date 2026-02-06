#!/usr/bin/env bash
# =============================================================================
# runtime-retry.sh - Generic retry with exponential backoff
#
# The backoff math is generic; error classification delegates to the active
# backend via runtime_backend_is_retryable().
#
# Config resolution (highest priority first):
#   1. WIGGUM_RUNTIME_MAX_RETRIES env var
#   2. config/config.json → .runtime.backends.<backend>.max_retries
#   3. Hardcoded default: 3
# =============================================================================
set -euo pipefail

[ -n "${_RUNTIME_RETRY_LOADED:-}" ] && return 0
_RUNTIME_RETRY_LOADED=1

source "$WIGGUM_HOME/lib/core/logger.sh"

# =============================================================================
# RETRY CONFIGURATION
# =============================================================================

RUNTIME_MAX_RETRIES="${WIGGUM_RUNTIME_MAX_RETRIES:-3}"
RUNTIME_INITIAL_BACKOFF="${WIGGUM_RUNTIME_INITIAL_BACKOFF:-5}"
RUNTIME_MAX_BACKOFF="${WIGGUM_RUNTIME_MAX_BACKOFF:-60}"
RUNTIME_BACKOFF_MULTIPLIER="${WIGGUM_RUNTIME_BACKOFF_MULTIPLIER:-2}"

# =============================================================================
# RETRY HELPER FUNCTIONS
# =============================================================================

# Load retry config from config.json with env var overrides
load_runtime_retry_config() {
    local config_file="$WIGGUM_HOME/config/config.json"

    if [ -f "$config_file" ]; then
        local backend="${WIGGUM_RUNTIME_BACKEND:-claude}"

        RUNTIME_MAX_RETRIES="${WIGGUM_RUNTIME_MAX_RETRIES:-$(
            jq -r ".runtime.backends.${backend}.max_retries // 3" "$config_file" 2>/dev/null
        )}"
        RUNTIME_INITIAL_BACKOFF="${WIGGUM_RUNTIME_INITIAL_BACKOFF:-$(
            jq -r ".runtime.backends.${backend}.initial_backoff // 5" "$config_file" 2>/dev/null
        )}"
        RUNTIME_MAX_BACKOFF="${WIGGUM_RUNTIME_MAX_BACKOFF:-$(
            jq -r ".runtime.backends.${backend}.max_backoff // 60" "$config_file" 2>/dev/null
        )}"
        RUNTIME_BACKOFF_MULTIPLIER="${WIGGUM_RUNTIME_BACKOFF_MULTIPLIER:-$(
            jq -r ".runtime.backends.${backend}.backoff_multiplier // 2" "$config_file" 2>/dev/null
        )}"
    fi

    # Ensure defaults if parsing fails
    RUNTIME_MAX_RETRIES="${RUNTIME_MAX_RETRIES:-3}"
    RUNTIME_INITIAL_BACKOFF="${RUNTIME_INITIAL_BACKOFF:-5}"
    RUNTIME_MAX_BACKOFF="${RUNTIME_MAX_BACKOFF:-60}"
    RUNTIME_BACKOFF_MULTIPLIER="${RUNTIME_BACKOFF_MULTIPLIER:-2}"
}

# Calculate backoff delay for a given attempt number
#
# Args:
#   attempt - The attempt number (0-indexed)
#
# Returns: Delay in seconds (echoed)
_calculate_backoff() {
    local attempt="$1"
    local delay="$RUNTIME_INITIAL_BACKOFF"

    # Exponential backoff: initial * multiplier^attempt
    local i=0
    while [ "$i" -lt "$attempt" ]; do
        delay=$((delay * RUNTIME_BACKOFF_MULTIPLIER))
        ((++i))
    done

    # Cap at max backoff
    if [ "$delay" -gt "$RUNTIME_MAX_BACKOFF" ]; then
        delay="$RUNTIME_MAX_BACKOFF"
    fi

    echo "$delay"
}

# =============================================================================
# RETRY WRAPPER FUNCTION
# =============================================================================

# Run backend with retry logic for transient failures
#
# Wraps runtime_backend_invoke with exponential backoff retry.
# Error classification is delegated to the backend via runtime_backend_is_retryable().
#
# Args:
#   All arguments are passed through to runtime_backend_invoke
#
# Returns: Exit code from final attempt
runtime_exec_with_retry() {
    # Load config on first use
    load_runtime_retry_config

    local attempt=0
    local exit_code=0

    # Temp file for capturing stderr to detect retryable errors
    local _retry_stderr_file
    _retry_stderr_file=$(mktemp /tmp/wiggum-retry-XXXXXX)
    # shellcheck disable=SC2064
    trap "rm -f '$_retry_stderr_file'" RETURN

    while [ "$attempt" -le "$RUNTIME_MAX_RETRIES" ]; do
        # Clear stderr capture between attempts
        : > "$_retry_stderr_file"

        # Run backend, capturing stderr for error classification
        exit_code=0
        runtime_backend_invoke "$@" 2>"$_retry_stderr_file" || exit_code=$?

        # Replay captured stderr to the caller
        if [ -s "$_retry_stderr_file" ]; then
            cat "$_retry_stderr_file" >&2
        fi

        # Success - return immediately
        if [ "$exit_code" -eq 0 ]; then
            return 0
        fi

        # Check if retryable via backend
        if ! runtime_backend_is_retryable "$exit_code" "$_retry_stderr_file"; then
            log_debug "Backend failed with non-retryable exit code $exit_code"
            return "$exit_code"
        fi

        # Check if we've exhausted retries
        if [ "$attempt" -ge "$RUNTIME_MAX_RETRIES" ]; then
            log_warn "Backend failed (exit $exit_code) after $((attempt + 1)) attempts - giving up"
            return "$exit_code"
        fi

        # Calculate backoff delay
        local delay
        delay=$(_calculate_backoff "$attempt")

        log_warn "Backend failed (exit $exit_code), retrying in ${delay}s (attempt $((attempt + 1))/$RUNTIME_MAX_RETRIES)"
        sleep "$delay"

        ((++attempt)) || true
    done

    return "$exit_code"
}
