#!/usr/bin/env bash
# run-claude-resume.sh - Resume a Claude session for follow-up prompts
#
# Used for generating summaries or continuing a conversation after
# the main work loop completes. This is a primitive that agents can use.

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

    if [ -z "$session_id" ] || [ -z "$prompt" ]; then
        log_error "run_agent_resume: session_id and prompt are required"
        return 1
    fi

    log_debug "Resuming session $session_id (max_turns: $max_turns)"

    if [ -n "$output_file" ]; then
        "$CLAUDE" --verbose \
            --resume "$session_id" \
            --output-format stream-json \
            --max-turns "$max_turns" \
            --dangerously-skip-permissions \
            -p "$prompt" > "$output_file" 2>&1
        local exit_code=$?
        log_debug "Resume completed (exit_code: $exit_code, output: $output_file)"
        return $exit_code
    else
        "$CLAUDE" --resume "$session_id" \
            --max-turns "$max_turns" \
            --dangerously-skip-permissions \
            -p "$prompt" 2>&1
        return $?
    fi
}
