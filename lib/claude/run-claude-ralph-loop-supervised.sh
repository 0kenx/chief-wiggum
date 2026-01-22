#!/usr/bin/env bash
# run-claude-ralph-loop-supervised.sh - Ralph loop with periodic supervisor intervention
#
# Extends the basic ralph loop with a supervisor that:
# - Runs every M iterations (configurable)
# - Reviews progress and makes control flow decisions (CONTINUE/STOP/RESTART)
# - Provides guidance/feedback that gets injected into the next work round
#
# The supervisor can:
# - CONTINUE: Work is progressing, inject feedback for next round
# - STOP: Halt the loop (supervisor explains why)
# - RESTART: Reset to iteration 0, archive current run, inject redirect guidance
set -euo pipefail

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"
source "$WIGGUM_HOME/lib/claude/run-claude-ralph-loop.sh"

# =============================================================================
# SUPERVISOR TAG EXTRACTION HELPERS
# =============================================================================

# Extract decision from supervisor output (CONTINUE|STOP|RESTART)
_extract_supervisor_decision() {
    local log_file="$1"
    local decision
    decision=$(grep -oP '(?<=<decision>)(CONTINUE|STOP|RESTART)(?=</decision>)' "$log_file" 2>/dev/null | head -1)

    # Default to CONTINUE if not found or invalid
    if [ -z "$decision" ]; then
        echo "CONTINUE"
    else
        echo "$decision"
    fi
}

# Extract review content from supervisor output
_extract_supervisor_review() {
    local log_file="$1"
    local output_file="$2"

    if grep -q '<review>' "$log_file" 2>/dev/null; then
        sed -n '/<review>/,/<\/review>/p' "$log_file" | sed '1d;$d' > "$output_file"
        return 0
    fi
    return 1
}

# Extract guidance from supervisor output
_extract_supervisor_guidance() {
    local log_file="$1"
    local output_file="$2"

    if grep -q '<guidance>' "$log_file" 2>/dev/null; then
        sed -n '/<guidance>/,/<\/guidance>/p' "$log_file" | sed '1d;$d' > "$output_file"
        return 0
    fi
    return 1
}

# =============================================================================
# DEFAULT SUPERVISOR PROMPT
# =============================================================================

# Default supervisor prompt template
# Override by passing a custom supervisor_prompt_fn
_default_supervisor_prompt() {
    local iteration="$1"
    # shellcheck disable=SC2034  # output_dir available for custom prompt functions
    local output_dir="$2"
    local last_summary="$3"

    cat << SUPERVISOR_PROMPT_EOF
SUPERVISOR REVIEW:

You oversee an iterative work loop. Review progress and decide how to proceed.

**Iteration**: ${iteration}
**Summary**: @../summaries/${last_summary}

## Supervisor Philosophy

* DEFAULT TO CONTINUE - Only intervene when you have HIGH CONFIDENCE (>90%) something is wrong
* Let workers work - Minor issues, slow progress, or imperfect approaches are NOT reasons to stop
* Restarts are expensive - Only restart if the fundamental approach is broken
* Trust the process - The completion check will detect when work is actually done

## Decision Criteria

### CONTINUE

Use CONTINUE when:
* Work is progressing (even slowly)
* There are minor issues but forward momentum exists
* You're uncertain whether there's a problem
* The approach seems reasonable even if not optimal

### STOP

Use STOP ONLY when one of these is TRUE:
* Hard blocker exists that CANNOT be resolved (missing permissions, impossible requirement)
* Continuing would cause harm (runaway resource usage, destructive actions)

DO NOT use STOP for:
* Slow progress
* Minor bugs or issues
* Approaches you'd do differently
* Uncertainty about completion

### RESTART

Use RESTART ONLY when:
* The fundamental approach is PROVABLY wrong (not just suboptimal)
* Significant work has gone in a completely wrong direction
* Starting fresh with a different strategy is clearly better than course-correcting
* Worker is stuck in an infinite loop doing the exact same thing repeatedly

DO NOT use RESTART for:
* Minor course corrections (use CONTINUE with guidance instead)
* Slow progress
* Code quality concerns

## Response Format

Be concise. Analyze then decide.

<review>
**Progress**: [1-2 sentences - what was accomplished]
**Assessment**: [1-2 sentences - on track or concern]
**Rationale**: [1-2 sentences - why this decision]
</review>

<decision>CONTINUE</decision>

<guidance>
[3-5 sentences max. For CONTINUE: what to focus on next. For STOP: why halting. For RESTART: what to try instead.]
</guidance>

The <decision> tag MUST be exactly: CONTINUE, STOP, or RESTART.
SUPERVISOR_PROMPT_EOF
}

# =============================================================================
# MAIN SUPERVISED LOOP FUNCTION
# =============================================================================

# Supervised ralph loop execution
#
# Args:
#   workspace           - Working directory for the agent
#   system_prompt       - System prompt for the agent
#   user_prompt_fn      - Callback: generates work prompts (iteration, output_dir, supervisor_dir, supervisor_feedback)
#   completion_check_fn - Callback: checks if work complete
#   max_iterations      - Maximum loop iterations (default: 20)
#   max_turns           - Max turns per Claude session (default: 50)
#   output_dir          - Directory for logs and summaries (default: workspace parent)
#   session_prefix      - Prefix for session files (default: iteration)
#   supervisor_interval - Run supervisor every M iterations (default: 3)
#   supervisor_prompt_fn - Callback: generates supervisor prompts (default: _default_supervisor_prompt)
#   max_restarts        - Max RESTART decisions before forcing STOP (default: 2)
#
# Returns: 0 on successful completion, 1 if max iterations reached or error
run_ralph_loop_supervised() {
    local workspace="$1"
    local system_prompt="$2"
    local user_prompt_fn="$3"
    local completion_check_fn="$4"
    local max_iterations="${5:-20}"
    local max_turns="${6:-50}"
    local output_dir="${7:-}"
    local session_prefix="${8:-iteration}"
    local supervisor_interval="${9:-3}"
    local supervisor_prompt_fn="${10:-_default_supervisor_prompt}"
    local max_restarts="${11:-2}"

    # Default output_dir to workspace parent if not specified
    if [ -z "$output_dir" ]; then
        output_dir=$(cd "$workspace/.." && pwd)
    fi

    local iteration=0
    local restart_count=0
    local shutdown_requested=false
    local last_session_id=""
    local supervisor_feedback=""

    # Signal handler for graceful shutdown
    # shellcheck disable=SC2329  # Function is used via trap
    _ralph_supervised_signal_handler() {
        log "Supervised ralph loop received shutdown signal"
        shutdown_requested=true
    }
    trap _ralph_supervised_signal_handler INT TERM

    # Record start time
    local start_time
    start_time=$(date +%s)
    log "Supervised ralph loop starting (max $max_iterations iterations, supervisor every $supervisor_interval)"

    # Change to workspace
    cd "$workspace" || {
        log_error "Cannot access workspace: $workspace"
        return 1
    }

    # Create directory structure
    mkdir -p "$output_dir/logs"
    mkdir -p "$output_dir/summaries"
    mkdir -p "$output_dir/supervisors"

    # Main loop
    while [ $iteration -lt "$max_iterations" ]; do
        # Check for shutdown request
        if [ "$shutdown_requested" = true ]; then
            log "Supervised loop shutting down due to signal"
            break
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

        # Get user prompt from callback (extended signature with supervisor context)
        local user_prompt
        user_prompt=$($user_prompt_fn "$iteration" "$output_dir" "$output_dir/supervisors" "$supervisor_feedback")

        log_debug "Iteration $iteration: Session $session_id (max $max_turns turns)"

        # Log iteration start to worker.log
        echo "[$(date -Iseconds)] ITERATION_START iteration=$iteration session_id=$session_id max_turns=$max_turns restart_count=$restart_count" >> "$output_dir/worker.log" 2>/dev/null || true

        # Generate timestamp for log filename uniqueness
        local log_timestamp
        log_timestamp=$(date +%s)
        local log_file="$output_dir/logs/${session_prefix}-${iteration}-${log_timestamp}.log"

        log "Work phase starting (see logs/${session_prefix}-${iteration}-${log_timestamp}.log for details)"

        # Log initial prompt to iteration log as JSON
        {
            jq -c -n --arg iteration "$iteration" \
                  --arg session "$session_id" \
                  --arg sys_prompt "$system_prompt" \
                  --arg user_prompt "$user_prompt" \
                  --arg max_turns "$max_turns" \
                  --arg restart_count "$restart_count" \
                  '{
                    type: "iteration_start",
                    iteration: ($iteration | tonumber),
                    session_id: $session,
                    max_turns: ($max_turns | tonumber),
                    restart_count: ($restart_count | tonumber),
                    system_prompt: $sys_prompt,
                    user_prompt: $user_prompt,
                    timestamp: now | strftime("%Y-%m-%dT%H:%M:%SZ")
                  }'
        } > "$log_file"

        # PHASE 1: Work session with turn limit
        "$CLAUDE" --verbose \
            --output-format stream-json \
            ${WIGGUM_HOME:+--plugin-dir "$WIGGUM_HOME/skills"} \
            --append-system-prompt "$system_prompt" \
            --session-id "$session_id" \
            --max-turns "$max_turns" \
            --dangerously-skip-permissions \
            -p "$user_prompt" >> "$log_file" 2>&1

        local exit_code=$?
        log "Work phase completed (exit code: $exit_code, session: $session_id)"

        # Log work phase completion
        echo "[$(date -Iseconds)] WORK_PHASE_COMPLETE iteration=$iteration exit_code=$exit_code" >> "$output_dir/worker.log" 2>/dev/null || true

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

        # Capture full JSON output to logs directory
        local summary_log="$output_dir/logs/${session_prefix}-${iteration}-${log_timestamp}-summary.log"
        local summary_txt="$output_dir/summaries/${session_prefix}-${iteration}-summary.txt"

        "$CLAUDE" --verbose --resume "$session_id" --max-turns 2 \
            --output-format stream-json \
            --dangerously-skip-permissions -p "$summary_prompt" \
            > "$summary_log" 2>&1

        local summary_exit_code=$?
        log "Summary generation completed (exit code: $summary_exit_code)"

        # Extract clean text from JSON stream and save
        local summary
        summary=$(extract_summary_text "$(cat "$summary_log")")

        if [ -z "$summary" ]; then
            log_warn "Summary for iteration $iteration is empty"
            summary="[Summary generation failed or produced no output]"
        fi

        echo "$summary" > "$summary_txt"
        log "Summary generated for iteration $iteration"

        # Log iteration completion
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

        # =================================================================
        # SUPERVISOR PHASE (every M iterations)
        # =================================================================
        if [ $((iteration % supervisor_interval)) -eq 0 ]; then
            log "Supervisor phase triggered at iteration $iteration"

            # Run supervisor session
            local supervisor_session_id
            supervisor_session_id=$(uuidgen)

            local supervisor_log="$output_dir/supervisors/supervisor-$iteration.log"
            local supervisor_review="$output_dir/supervisors/supervisor-$iteration-review.md"
            local supervisor_decision_file="$output_dir/supervisors/supervisor-$iteration-decision.txt"
            local supervisor_guidance_file="$output_dir/supervisors/supervisor-$iteration-guidance.md"

            # Get supervisor prompt (use last summary)
            local prev_iter=$((iteration - 1))
            local last_summary_file="${session_prefix}-$prev_iter-summary.txt"
            local supervisor_prompt
            supervisor_prompt=$($supervisor_prompt_fn "$iteration" "$output_dir" "$last_summary_file")

            local supervisor_system_prompt="You are a supervisor overseeing an iterative work process. Your bias is toward CONTINUE - only intervene with STOP or RESTART when you have high confidence something is fundamentally wrong. Let workers work."

            log "Running supervisor session $supervisor_session_id"
            echo "[$(date -Iseconds)] SUPERVISOR_START iteration=$iteration session_id=$supervisor_session_id" >> "$output_dir/worker.log" 2>/dev/null || true

            # Log supervisor prompt
            {
                jq -c -n --arg iteration "$iteration" \
                      --arg session "$supervisor_session_id" \
                      --arg prompt "$supervisor_prompt" \
                      '{
                        type: "supervisor_start",
                        iteration: ($iteration | tonumber),
                        session_id: $session,
                        prompt: $prompt,
                        timestamp: now | strftime("%Y-%m-%dT%H:%M:%SZ")
                      }'
            } > "$supervisor_log"

            # Run supervisor
            "$CLAUDE" --verbose \
                --output-format stream-json \
                ${WIGGUM_HOME:+--plugin-dir "$WIGGUM_HOME/skills"} \
                --append-system-prompt "$supervisor_system_prompt" \
                --session-id "$supervisor_session_id" \
                --max-turns 5 \
                --dangerously-skip-permissions \
                -p "$supervisor_prompt" >> "$supervisor_log" 2>&1

            local supervisor_exit_code=$?
            log "Supervisor session completed (exit code: $supervisor_exit_code)"

            # Extract decision and guidance
            local decision
            decision=$(_extract_supervisor_decision "$supervisor_log")
            echo "$decision" > "$supervisor_decision_file"

            # Extract review content
            _extract_supervisor_review "$supervisor_log" "$supervisor_review" || true

            # Extract guidance (always try to capture)
            _extract_supervisor_guidance "$supervisor_log" "$supervisor_guidance_file" || true

            # Read guidance for next round
            if [ -f "$supervisor_guidance_file" ]; then
                supervisor_feedback=$(cat "$supervisor_guidance_file")
            else
                supervisor_feedback=""
            fi

            log "Supervisor decision: $decision"
            echo "[$(date -Iseconds)] SUPERVISOR_COMPLETE iteration=$iteration decision=$decision" >> "$output_dir/worker.log" 2>/dev/null || true

            # Handle decision
            case "$decision" in
                CONTINUE)
                    log "Supervisor: CONTINUE - proceeding with guidance"
                    # supervisor_feedback is already set, loop continues
                    ;;

                STOP)
                    log "Supervisor: STOP - halting loop"
                    echo "[$(date -Iseconds)] SUPERVISOR_STOP iteration=$iteration reason=supervisor_decision" >> "$output_dir/worker.log" 2>/dev/null || true

                    # Record end time and exit
                    local end_time
                    end_time=$(date +%s)
                    local duration=$((end_time - start_time))

                    log "Supervised loop stopped by supervisor after $iteration iterations (duration: ${duration}s)"
                    echo "[$(date -Iseconds)] LOOP_STOPPED_BY_SUPERVISOR end_time=$end_time duration_sec=$duration iterations=$iteration" >> "$output_dir/worker.log" 2>/dev/null || true

                    export RALPH_LOOP_LAST_SESSION_ID="$last_session_id"
                    return 0
                    ;;

                RESTART)
                    restart_count=$((restart_count + 1))

                    if [ $restart_count -gt "$max_restarts" ]; then
                        log_warn "Supervisor: RESTART requested but max_restarts ($max_restarts) exceeded - forcing STOP"
                        echo "[$(date -Iseconds)] RESTART_LIMIT_EXCEEDED restart_count=$restart_count max_restarts=$max_restarts" >> "$output_dir/worker.log" 2>/dev/null || true

                        local end_time
                        end_time=$(date +%s)
                        local duration=$((end_time - start_time))

                        log "Supervised loop stopped due to restart limit (duration: ${duration}s)"
                        export RALPH_LOOP_LAST_SESSION_ID="$last_session_id"
                        return 1
                    fi

                    log "Supervisor: RESTART - archiving run-$((restart_count - 1)) and resetting to iteration 0"
                    echo "[$(date -Iseconds)] SUPERVISOR_RESTART iteration=$iteration restart_count=$restart_count" >> "$output_dir/worker.log" 2>/dev/null || true

                    # Archive current run
                    local archive_dir="$output_dir/supervisors/run-$((restart_count - 1))"
                    mkdir -p "$archive_dir"

                    # Move logs and summaries to archive
                    mv "$output_dir/logs/"* "$archive_dir/" 2>/dev/null || true
                    mv "$output_dir/summaries/"* "$archive_dir/" 2>/dev/null || true

                    # Re-create directories
                    mkdir -p "$output_dir/logs"
                    mkdir -p "$output_dir/summaries"

                    # Reset iteration
                    iteration=0
                    log "Restarted loop - beginning run-$restart_count with supervisor guidance"
                    ;;
            esac
        fi

        sleep 2  # Prevent tight loop
    done

    # Record end time
    local end_time
    end_time=$(date +%s)
    local duration=$((end_time - start_time))

    if [ $iteration -ge "$max_iterations" ]; then
        log_error "Supervised ralph loop reached max iterations ($max_iterations) without completing"
        echo "[$(date -Iseconds)] LOOP_INCOMPLETE end_time=$end_time duration_sec=$duration iterations=$iteration restarts=$restart_count" >> "$output_dir/worker.log" 2>/dev/null || true
        return 1
    fi

    echo "[$(date -Iseconds)] LOOP_COMPLETED end_time=$end_time duration_sec=$duration iterations=$iteration restarts=$restart_count" >> "$output_dir/worker.log" 2>/dev/null || true
    log "Supervised ralph loop finished after $iteration iterations, $restart_count restarts (duration: ${duration}s)"

    # Export last session ID for potential follow-up
    export RALPH_LOOP_LAST_SESSION_ID="$last_session_id"

    return 0
}
