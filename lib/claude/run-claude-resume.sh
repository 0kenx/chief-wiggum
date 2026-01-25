#!/usr/bin/env bash
# run-claude-resume.sh - Resume a Claude session for follow-up prompts
#
# Used for generating summaries or continuing a conversation after
# the main work loop completes. This is a primitive that agents can use.
set -euo pipefail

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"

# Resume an existing Claude session with a new prompt
#
# Args:
#   session_id    - The session ID to resume
#   prompt        - The prompt to send
#   output_file   - Where to save the output
#   max_turns     - Maximum turns for this resumption (default: 3)
#
# Returns: Exit code from claude
run_agent_resume() {
    local session_id="$1"
    local prompt="$2"
    local output_file="$3"
    local max_turns="${4:-3}"
    local _run_resume_completed_normally=false

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

    log_debug "Resuming session $session_id (max_turns: $max_turns)"

    # Auto-generate log file path if not specified
    if [ -z "$output_file" ] && [ -n "${WIGGUM_LOG_DIR:-}" ]; then
        mkdir -p "$WIGGUM_LOG_DIR"
        output_file="$WIGGUM_LOG_DIR/resume-${session_id:0:8}-$(date +%s).log"
        log_debug "Auto-generated log file: $output_file"
    fi

    if [ -n "$output_file" ]; then
        local exit_code=0
        "$CLAUDE" --verbose \
            --resume "$session_id" \
            --output-format stream-json \
            --max-turns "$max_turns" \
            --dangerously-skip-permissions \
            -p "$prompt" > "$output_file" 2>&1 || exit_code=$?
        log_debug "Resume completed (exit_code: $exit_code, output: $output_file)"
        _run_resume_completed_normally=true
        return $exit_code
    else
        # No WIGGUM_LOG_DIR set - output goes to stdout only (not recommended)
        local exit_code=0
        "$CLAUDE" --resume "$session_id" \
            --max-turns "$max_turns" \
            --dangerously-skip-permissions \
            -p "$prompt" 2>&1 || exit_code=$?
        _run_resume_completed_normally=true
        return $exit_code
    fi
}
