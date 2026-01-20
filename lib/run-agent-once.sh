#!/usr/bin/env bash
# Run Claude agent once with configurable parameters
# Generic one-shot agent execution

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/logger.sh"

run_agent_once() {
    local workspace="$1"
    local system_prompt="$2"
    local user_prompt="$3"
    local output_file="$4"
    local max_turns="${5:-3}"
    local session_id="${6:-}"

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

    log_debug "Running agent once in workspace: $workspace (max_turns: $max_turns)"

    # Build command arguments
    local cmd_args=(
        --verbose
        --output-format stream-json
        --append-system-prompt "$system_prompt"
        --max-turns "$max_turns"
        --dangerously-skip-permissions
        -p "$user_prompt"
    )

    # Add plugin dir if WIGGUM_HOME is set
    if [ -n "$WIGGUM_HOME" ]; then
        cmd_args+=(--plugin-dir "$WIGGUM_HOME/skills")
    fi

    # Add session-id or resume based on whether we're continuing
    if [ -n "$session_id" ]; then
        cmd_args+=(--resume "$session_id")
    fi

    # Run claude and capture output
    if [ -n "$output_file" ]; then
        claude "${cmd_args[@]}" > "$output_file" 2>&1
        local exit_code=$?
        log_debug "Agent completed (exit_code: $exit_code, output: $output_file)"
        return $exit_code
    else
        claude "${cmd_args[@]}" 2>&1
        return $?
    fi
}
