#!/usr/bin/env bash
# run-claude-ralph-loop.sh - Generic self-prompting loop mechanism
#
# Provides the core ralph loop pattern that can be parameterized for different use cases:
# - Task execution (original ralph-loop)
# - PR comment fixing
# - Other iterative agent workflows
#
# Core concept: ralph-loop runs claude in a loop, run-agent-once runs it just once.
# This script extracts the loop to be reusable across different contexts.
set -euo pipefail

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"
source "$WIGGUM_HOME/lib/core/checkpoint.sh"
source "$WIGGUM_HOME/lib/utils/work-log.sh"
source "$WIGGUM_HOME/lib/claude/usage-tracker.sh"

# Extract clean text from Claude CLI stream-JSON output
# Filters out JSON and returns only assistant text responses
extract_summary_text() {
    local input="$1"
    echo "$input" | grep '"type":"assistant"' | \
        jq -r 'select(.message.content[]? | .type == "text") | .message.content[] | select(.type == "text") | .text' 2>/dev/null | \
        grep -v '^$'
}

# Generic ralph loop execution
#
# Args:
#   workspace           - Working directory for the agent
#   system_prompt       - System prompt for the agent
#   user_prompt_fn      - Function name that generates user prompt (called with iteration number and output_dir)
#   completion_check_fn - Function name that returns 0 if work is complete, 1 otherwise
#   max_iterations      - Maximum loop iterations (default: 20)
#   max_turns           - Max turns per Claude session (default: 50)
#   output_dir          - Directory for logs and summaries (default: workspace parent)
#   session_prefix      - Prefix for session files (default: iteration)
#
# The user_prompt_fn and completion_check_fn are callback function names that will be invoked.
# This allows customization of the loop behavior without code duplication.
#
# Returns: 0 on successful completion, 1 if max iterations reached or error
run_ralph_loop() {
    local workspace="$1"
    local system_prompt="$2"
    local user_prompt_fn="$3"
    local completion_check_fn="$4"
    local max_iterations="${5:-20}"
    local max_turns="${6:-50}"
    local output_dir="${7:-}"
    local session_prefix="${8:-iteration}"

    # Validate callback functions exist before starting loop
    if ! declare -F "$user_prompt_fn" > /dev/null 2>&1; then
        log_error "Callback function '$user_prompt_fn' does not exist"
        log_error "The user_prompt_fn must be a defined shell function that generates the user prompt"
        return 1
    fi

    if ! declare -F "$completion_check_fn" > /dev/null 2>&1; then
        log_error "Callback function '$completion_check_fn' does not exist"
        log_error "The completion_check_fn must be a defined shell function that checks if work is complete"
        return 1
    fi

    # Default output_dir to workspace parent if not specified
    if [ -z "$output_dir" ]; then
        output_dir=$(cd "$workspace/.." && pwd)
    fi

    local iteration=0
    local shutdown_requested=false
    local last_session_id=""

    # Signal handler for graceful shutdown (invoked by trap)
    # shellcheck disable=SC2329
    _ralph_loop_signal_handler() {
        log "Ralph loop received shutdown signal"
        shutdown_requested=true
    }
    trap _ralph_loop_signal_handler INT TERM

    # Record start time
    local start_time
    start_time=$(date +%s)

    # Generate unique run ID for this execution (namespaces logs, work-log, checkpoints)
    local run_id="${session_prefix}-${start_time}"
    export RALPH_RUN_ID="$run_id"

    log "Ralph loop starting (max $max_iterations iterations, $max_turns turns/session, run_id=$run_id)"

    # Change to workspace
    cd "$workspace" || {
        log_error "Cannot access workspace: $workspace"
        return 1
    }

    # Create run-namespaced subdirectories
    mkdir -p "$output_dir/logs/$run_id"
    mkdir -p "$output_dir/summaries"

    # Initialize work log (uses RALPH_RUN_ID for namespacing)
    work_log_init "$output_dir"

    # Track the last session ID for potential final summary
    while [ $iteration -lt "$max_iterations" ]; do
        # Check for shutdown request
        if [ "$shutdown_requested" = true ]; then
            log "Ralph loop shutting down due to signal"
            break
        fi

        # Check rate limit from shared usage data (written by orchestrator)
        local _rl_ralph_dir="${RALPH_DIR:-}"
        if [ -z "$_rl_ralph_dir" ] && [ -n "$output_dir" ]; then
            _rl_ralph_dir=$(cd "$output_dir/../.." 2>/dev/null && pwd || echo "")
        fi
        if [ -n "$_rl_ralph_dir" ] && rate_limit_check "$_rl_ralph_dir"; then
            log "Rate limit active - pausing before iteration $iteration"
            rate_limit_wait_for_cycle_reset
            log "Rate limit cleared - resuming iteration $iteration"
        fi

        # Check completion using callback
        if $completion_check_fn 2>/dev/null; then
            log "Completion check passed - work is done"
            break
        fi

        # Generate unique session ID for this iteration
        local session_id
        session_id=$(uuidgen)
        last_session_id="$session_id"

        # Get user prompt from callback (pass iteration and output_dir for context)
        local user_prompt
        user_prompt=$($user_prompt_fn "$iteration" "$output_dir")

        log_debug "Iteration $iteration: Session $session_id (max $max_turns turns)"

        # Log iteration start to worker.log if it exists
        echo "[$(date -Iseconds)] ITERATION_START iteration=$iteration session_id=$session_id max_turns=$max_turns" >> "$output_dir/worker.log" 2>/dev/null || true

        # Generate timestamp for log filename uniqueness
        local log_timestamp
        log_timestamp=$(date +%s)
        local log_file="$output_dir/logs/$run_id/${session_prefix}-${iteration}-${log_timestamp}.log"

        log "Work phase starting (see logs/$run_id/${session_prefix}-${iteration}-${log_timestamp}.log for details)"

        # Log initial prompt to iteration log as JSON
        {
            jq -c -n --arg iteration "$iteration" \
                  --arg session "$session_id" \
                  --arg sys_prompt "$system_prompt" \
                  --arg user_prompt "$user_prompt" \
                  --arg max_turns "$max_turns" \
                  '{
                    type: "iteration_start",
                    iteration: ($iteration | tonumber),
                    session_id: $session,
                    max_turns: ($max_turns | tonumber),
                    system_prompt: $sys_prompt,
                    user_prompt: $user_prompt,
                    timestamp: now | strftime("%Y-%m-%dT%H:%M:%SZ")
                  }'
        } > "$log_file"

        # PHASE 1: Work session with turn limit
        local exit_code=0
        "$CLAUDE" --verbose \
            --output-format stream-json \
            ${WIGGUM_HOME:+--plugin-dir "$WIGGUM_HOME/skills"} \
            --append-system-prompt "$system_prompt" \
            --session-id "$session_id" \
            --max-turns "$max_turns" \
            --dangerously-skip-permissions \
            -p "$user_prompt" >> "$log_file" 2>&1 || exit_code=$?
        log "Work phase completed (exit code: $exit_code, session: $session_id)"

        # Log work phase completion
        echo "[$(date -Iseconds)] WORK_PHASE_COMPLETE iteration=$iteration exit_code=$exit_code" >> "$output_dir/worker.log" 2>/dev/null || true

        # Create checkpoint after work phase (deterministic: status from exit code, files from log parsing)
        local checkpoint_status="in_progress"
        if [ $exit_code -eq 130 ] || [ $exit_code -eq 143 ]; then
            checkpoint_status="interrupted"
        elif [ $exit_code -ne 0 ]; then
            checkpoint_status="failed"
        fi
        local files_modified
        files_modified=$(checkpoint_extract_files_modified "$log_file")
        checkpoint_write "$output_dir" "$iteration" "$session_id" "$checkpoint_status" \
            "$files_modified" "[]" "[]" ""

        # Check for interruption signals
        if [ $exit_code -eq 130 ] || [ $exit_code -eq 143 ]; then
            log "Work phase was interrupted by signal (exit code: $exit_code)"
            shutdown_requested=true
            break
        fi

        # Check if shutdown was requested during work phase
        if [ "$shutdown_requested" = true ]; then
            log "Shutdown requested during work phase - exiting loop"
            break
        fi

        # PHASE 2: Generate summary for context continuity
        log "Generating summary for iteration $iteration (session: $session_id)"

        local summary_prompt="Your task is to create a detailed summary of the conversation so far, paying close attention to the user's explicit requests and your previous actions.
This summary should be thorough in capturing technical details, code patterns, and architectural decisions that would be essential for continuing development work without losing context.

Before providing your final summary, wrap your analysis in <analysis> tags to organize your thoughts and ensure you've covered all necessary points. In your analysis process:

1. Chronologically analyze each message and section of the conversation. For each section thoroughly identify:
   - The user's explicit requests and intents
   - Your approach to addressing the user's requests
   - Key decisions, technical concepts and code patterns
   - Specific details like file names, full code snippets, function signatures, file edits, etc
2. Double-check for technical accuracy and completeness, addressing each required element thoroughly.

Your summary should include the following sections:

1. Primary Request and Intent: Capture all of the user's explicit requests and intents in detail
2. Key Technical Concepts: List all important technical concepts, technologies, and frameworks discussed.
3. Files and Code Sections: Enumerate specific files and code sections examined, modified, or created.
4. Problem Solving: Document problems solved and any ongoing troubleshooting efforts.
5. Pending Tasks: Outline any pending tasks that you have explicitly been asked to work on.
6. Current Work: Describe in detail precisely what was being worked on immediately before this summary request.
7. Optional Next Step: List the next step that you will take that is related to the most recent work you were doing.

Please provide your summary based on the conversation so far, following this structure and ensuring precision and thoroughness in your response."

        log "Requesting summary for session $session_id"

        # Capture full JSON output to logs directory (same format as work phase)
        local summary_log="$output_dir/logs/$run_id/${session_prefix}-${iteration}-${log_timestamp}-summary.log"
        local summary_txt="$output_dir/summaries/${session_prefix}-${iteration}-summary.txt"

        local summary_exit_code=0
        "$CLAUDE" --verbose --resume "$session_id" --max-turns 2 \
            --output-format stream-json \
            --dangerously-skip-permissions -p "$summary_prompt" \
            > "$summary_log" 2>&1 || summary_exit_code=$?
        log "Summary generation completed (exit code: $summary_exit_code)"

        # Extract clean text from JSON stream and save to summaries directory
        local summary
        summary=$(extract_summary_text "$(cat "$summary_log")")

        # Check if summary is empty
        if [ -z "$summary" ]; then
            log_warn "Summary for iteration $iteration is empty"
            summary="[Summary generation failed or produced no output]"
        fi

        # Save plain text summary
        echo "$summary" > "$summary_txt"

        # Write structured work log entry
        work_log_write_iteration "$output_dir" "$iteration" "$session_id" "$exit_code" "$summary" "$log_file"

        log "Summary generated for iteration $iteration"

        # Update checkpoint with summary prose (deterministic: reads saved text file)
        checkpoint_update_summary "$output_dir" "$iteration" "$summary_txt"

        # Log iteration completion to iteration log file as JSON
        {
            jq -c -n --arg iteration "$iteration" \
                  --arg session "$session_id" \
                  --arg exit_code "$exit_code" \
                  --arg summary_exit_code "$summary_exit_code" \
                  '{
                    type: "iteration_complete",
                    iteration: ($iteration | tonumber),
                    session_id: $session,
                    work_exit_code: ($exit_code | tonumber),
                    summary_exit_code: ($summary_exit_code | tonumber),
                    timestamp: now | strftime("%Y-%m-%dT%H:%M:%SZ")
                  }'
        } >> "$log_file"

        # Check if shutdown was requested during summary phase
        if [ "$shutdown_requested" = true ]; then
            log "Shutdown requested during summary phase - exiting loop"
            break
        fi

        iteration=$((iteration + 1))
        sleep 2  # Prevent tight loop
    done

    # Record end time
    local end_time
    end_time=$(date +%s)
    local duration=$((end_time - start_time))

    if [ $iteration -ge "$max_iterations" ]; then
        log_error "Ralph loop reached max iterations ($max_iterations) without completing"
        echo "[$(date -Iseconds)] LOOP_INCOMPLETE end_time=$end_time duration_sec=$duration iterations=$iteration max_iterations=$max_iterations" >> "$output_dir/worker.log" 2>/dev/null || true
        return 1
    fi

    echo "[$(date -Iseconds)] LOOP_COMPLETED end_time=$end_time duration_sec=$duration iterations=$iteration" >> "$output_dir/worker.log" 2>/dev/null || true
    log "Ralph loop finished after $iteration iterations (duration: ${duration}s)"

    # Export last session ID for potential follow-up (e.g., final summary generation)
    export RALPH_LOOP_LAST_SESSION_ID="$last_session_id"

    return 0
}
