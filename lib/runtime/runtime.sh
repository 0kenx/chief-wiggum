#!/usr/bin/env bash
# =============================================================================
# runtime.sh - Backend-agnostic runtime module
#
# Main entry point for the runtime abstraction layer. Handles backend
# discovery, loading, and provides the public API for agent execution.
#
# Backend discovery (priority order):
#   1. WIGGUM_RUNTIME_BACKEND environment variable
#   2. .ralph/config.json → .runtime.backend
#   3. config/config.json → .runtime.backend
#   4. Default: "claude"
#
# Public API:
#   runtime_init               - Initialize the runtime (call once)
#   run_agent_once             - Single-shot execution
#   run_agent_once_with_session - Single-shot with named session
#   run_agent_resume           - Resume an existing session
#   runtime_exec_with_retry    - Retry-wrapped backend invocation
#
# Usage:
#   source "$WIGGUM_HOME/lib/runtime/runtime.sh"
#   runtime_init  # (auto-called on source if not already initialized)
# =============================================================================
set -euo pipefail

[ -n "${_RUNTIME_LOADED:-}" ] && return 0
_RUNTIME_LOADED=1
source "$WIGGUM_HOME/lib/core/platform.sh"

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"
source "$WIGGUM_HOME/lib/runtime/runtime-retry.sh"
source "$WIGGUM_HOME/lib/runtime/runtime-prompts.sh"

# =============================================================================
# BACKEND DISCOVERY AND LOADING
# =============================================================================

_RUNTIME_INITIALIZED=0

# Discover which backend to use (priority: env > project config > global config > default)
_runtime_discover_backend() {
    local backend="${WIGGUM_RUNTIME_BACKEND:-}"

    # Check project-level config
    if [ -z "$backend" ] && [ -f "${RALPH_DIR:-}/.ralph/config.json" ]; then
        backend=$(jq -r '.runtime.backend // empty' "${RALPH_DIR}/.ralph/config.json" 2>/dev/null) || true
    fi

    # Check global config
    if [ -z "$backend" ] && [ -f "$WIGGUM_HOME/config/config.json" ]; then
        backend=$(jq -r '.runtime.backend // empty' "$WIGGUM_HOME/config/config.json" 2>/dev/null) || true
    fi

    # Default
    echo "${backend:-claude}"
}

# Initialize the runtime - discovers and loads the backend
#
# Call this once before using any runtime functions.
# Safe to call multiple times (idempotent).
runtime_init() {
    [ "$_RUNTIME_INITIALIZED" -eq 1 ] && return 0

    local backend
    backend=$(_runtime_discover_backend)

    # Validate backend name to prevent path traversal (e.g., "../" or "/")
    if [[ ! "$backend" =~ ^[a-zA-Z0-9_-]+$ ]]; then
        log_error "Invalid runtime backend name: $backend (must be alphanumeric/hyphens/underscores)"
        return 3  # Configuration error
    fi

    local backend_file="$WIGGUM_HOME/lib/backend/${backend}/${backend}-backend.sh"

    if [ ! -f "$backend_file" ]; then
        log_error "Runtime backend not found: $backend (expected: $backend_file)"
        return 3  # Configuration error
    fi

    # Source interface defaults first (provides no-op stubs for optional functions)
    source "$WIGGUM_HOME/lib/runtime/backend-interface.sh"

    # Source backend implementation (overrides interface stubs)
    # shellcheck disable=SC1090  # Dynamic backend loading by design
    source "$backend_file"

    # Initialize the backend
    runtime_backend_init

    export WIGGUM_RUNTIME_BACKEND="$backend"
    _RUNTIME_INITIALIZED=1

    # Initialize prompt wrappers for the active backend
    runtime_prompts_init "$backend"

    log_debug "Runtime initialized with backend: $backend"
}

# =============================================================================
# PUBLIC API
# =============================================================================

# Single-shot execution (replaces the old run_agent_once from run-claude-once.sh)
#
# Args:
#   workspace      - Directory to run in
#   system_prompt  - System prompt for context
#   user_prompt    - User prompt (the task)
#   output_file    - Where to save output
#   max_turns      - Max turns (default: 3)
#   session_id     - Optional session ID for resume
#
# Returns: Exit code from backend
run_agent_once() {
    runtime_init

    local workspace="$1"
    local system_prompt="$2"
    local user_prompt="$3"
    local output_file="$4"
    local max_turns="${5:-3}"
    local session_id="${6:-}"
    _run_once_completed_normally=false

    # Exit handler for detecting unexpected exits
    # shellcheck disable=SC2329
    _run_once_exit_handler() {
        local exit_code=$?
        if [ "$_run_once_completed_normally" != true ]; then
            log_error "Unexpected exit from run_agent_once (exit_code=$exit_code, workspace=$workspace)"
        fi
        trap - EXIT
    }
    trap _run_once_exit_handler EXIT

    # Validate required parameters
    if [ -z "$workspace" ] || [ -z "$system_prompt" ] || [ -z "$user_prompt" ]; then
        log_error "run_agent_once: missing required parameters"
        log_error "Usage: run_agent_once <workspace> <system_prompt> <user_prompt> [output_file] [max_turns] [session_id]"
        return 1
    fi

    # Change to workspace
    cd "$workspace" || {
        log_error "run_agent_once: failed to cd to workspace: $workspace"
        return 1
    }

    # Apply prompt wrappers
    system_prompt=$(runtime_wrap_system "$system_prompt")
    user_prompt=$(runtime_wrap_user "$user_prompt")

    log_debug "Running agent once in workspace: $workspace (max_turns: $max_turns)"

    # Build command arguments via backend
    local -a cmd_args=()
    if [ -n "$session_id" ]; then
        # When session_id is provided without --session-id flag, use resume
        runtime_backend_build_resume_args cmd_args "$session_id" "$user_prompt" "$output_file" "$max_turns"
    else
        runtime_backend_build_exec_args cmd_args "$workspace" "$system_prompt" "$user_prompt" "$output_file" "$max_turns" ""
    fi

    # Auto-generate log file path if not specified
    if [ -z "$output_file" ] && [ -n "${WIGGUM_LOG_DIR:-}" ]; then
        mkdir -p "$WIGGUM_LOG_DIR"
        output_file="$WIGGUM_LOG_DIR/once-$(epoch_now)-$$.log"
        log_debug "Auto-generated log file: $output_file"
    fi

    # Run with retry and capture output
    if [ -n "$output_file" ]; then
        local exit_code=0
        runtime_exec_with_retry "${cmd_args[@]}" > "$output_file" 2>&1 || exit_code=$?
        log_debug "Agent completed (exit_code: $exit_code, output: $output_file)"
        _run_once_completed_normally=true
        return $exit_code
    else
        local exit_code=0
        runtime_exec_with_retry "${cmd_args[@]}" 2>&1 || exit_code=$?
        _run_once_completed_normally=true
        return $exit_code
    fi
}

# Single-shot with a specific session ID (creates a named session)
#
# Unlike run_agent_once which uses --resume for existing sessions,
# this function uses --session-id to CREATE a new session with a specific UUID.
#
# Args:
#   workspace      - Directory to run in
#   system_prompt  - System prompt for context
#   user_prompt    - User prompt (the task)
#   output_file    - Where to save output
#   max_turns      - Max turns (default: 3)
#   session_id     - UUID for the new session
#
# Returns: Exit code from backend
run_agent_once_with_session() {
    runtime_init

    local workspace="$1"
    local system_prompt="$2"
    local user_prompt="$3"
    local output_file="$4"
    local max_turns="${5:-3}"
    local session_id="$6"
    _run_once_with_session_completed_normally=false

    # Exit handler for detecting unexpected exits
    # shellcheck disable=SC2329
    _run_once_with_session_exit_handler() {
        local exit_code=$?
        if [ "$_run_once_with_session_completed_normally" != true ]; then
            log_error "Unexpected exit from run_agent_once_with_session (exit_code=$exit_code, workspace=$workspace)"
        fi
        trap - EXIT
    }
    trap _run_once_with_session_exit_handler EXIT

    # Validate required parameters
    if [ -z "$workspace" ] || [ -z "$system_prompt" ] || [ -z "$user_prompt" ] || [ -z "$session_id" ]; then
        log_error "run_agent_once_with_session: missing required parameters"
        log_error "Usage: run_agent_once_with_session <workspace> <system_prompt> <user_prompt> <output_file> <max_turns> <session_id>"
        return 1
    fi

    # Change to workspace
    cd "$workspace" || {
        log_error "run_agent_once_with_session: failed to cd to workspace: $workspace"
        return 1
    }

    # Apply prompt wrappers
    system_prompt=$(runtime_wrap_system "$system_prompt")
    user_prompt=$(runtime_wrap_user "$user_prompt")

    log_debug "Running agent with named session in workspace: $workspace (max_turns: $max_turns, session_id: $session_id)"

    # Build command arguments via backend (with session_id for creation)
    local -a cmd_args=()
    runtime_backend_build_exec_args cmd_args "$workspace" "$system_prompt" "$user_prompt" "$output_file" "$max_turns" "$session_id"

    # Auto-generate log file path if not specified
    if [ -z "$output_file" ] && [ -n "${WIGGUM_LOG_DIR:-}" ]; then
        mkdir -p "$WIGGUM_LOG_DIR"
        output_file="$WIGGUM_LOG_DIR/once-session-$(epoch_now)-$$.log"
        log_debug "Auto-generated log file: $output_file"
    fi

    # Run with retry and capture output
    if [ -n "$output_file" ]; then
        local exit_code=0
        runtime_exec_with_retry "${cmd_args[@]}" > "$output_file" 2>&1 || exit_code=$?
        log_debug "Agent completed with session (exit_code: $exit_code, output: $output_file)"
        _run_once_with_session_completed_normally=true
        return $exit_code
    else
        local exit_code=0
        runtime_exec_with_retry "${cmd_args[@]}" 2>&1 || exit_code=$?
        _run_once_with_session_completed_normally=true
        return $exit_code
    fi
}

# Resume an existing session with a new prompt
#
# Args:
#   session_id    - The session ID to resume
#   prompt        - The prompt to send
#   output_file   - Where to save the output
#   max_turns     - Maximum turns for this resumption (default: 3)
#
# Returns: Exit code from backend
run_agent_resume() {
    runtime_init

    local session_id="$1"
    local prompt="$2"
    local output_file="$3"
    local max_turns="${4:-3}"
    _run_resume_completed_normally=false

    # Exit handler for detecting unexpected exits
    # shellcheck disable=SC2329
    _run_resume_exit_handler() {
        local exit_code=$?
        if [ "$_run_resume_completed_normally" != true ]; then
            log_error "Unexpected exit from run_agent_resume (exit_code=$exit_code, session_id=$session_id)"
        fi
        trap - EXIT
    }
    trap _run_resume_exit_handler EXIT

    if [ -z "$session_id" ] || [ -z "$prompt" ]; then
        log_error "run_agent_resume: session_id and prompt are required"
        _run_resume_completed_normally=true
        return 1
    fi

    # Apply user prompt wrapper
    prompt=$(runtime_wrap_user "$prompt")

    log_debug "Resuming session $session_id (max_turns: $max_turns)"

    # Auto-generate log file path if not specified
    if [ -z "$output_file" ] && [ -n "${WIGGUM_LOG_DIR:-}" ]; then
        mkdir -p "$WIGGUM_LOG_DIR"
        output_file="$WIGGUM_LOG_DIR/resume-${session_id:0:8}-$(epoch_now).log"
        log_debug "Auto-generated log file: $output_file"
    fi

    # Build resume arguments via backend
    local -a cmd_args=()
    runtime_backend_build_resume_args cmd_args "$session_id" "$prompt" "$output_file" "$max_turns"

    if [ -n "$output_file" ]; then
        local exit_code=0
        runtime_exec_with_retry "${cmd_args[@]}" > "$output_file" 2>&1 || exit_code=$?
        log_debug "Resume completed (exit_code: $exit_code, output: $output_file)"
        _run_resume_completed_normally=true
        return $exit_code
    else
        local exit_code=0
        runtime_exec_with_retry "${cmd_args[@]}" 2>&1 || exit_code=$?
        _run_resume_completed_normally=true
        return $exit_code
    fi
}

# Auto-initialize on source (safe to call multiple times)
runtime_init
