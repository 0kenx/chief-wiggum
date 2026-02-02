#!/usr/bin/env bash
# =============================================================================
# runtime-loop.sh - Backend-agnostic self-prompting loop with optional supervision
#
# Refactored from lib/claude/run-claude-ralph-loop.sh. The orchestration logic
# (iterate, checkpoint, supervise) is generic. Backend-specific calls are
# dispatched through the runtime_backend_* interface.
#
# Provides the core ralph loop pattern that can be parameterized:
# - Task execution (with supervision)
# - Security audits (without supervision)
# - PR comment fixing
# - Other iterative agent workflows
#
# Supervision is opt-in via supervisor_interval parameter:
# - supervisor_interval=0 (default): No supervision, pure iterative loop
# - supervisor_interval=N: Run supervisor every N iterations
# =============================================================================
set -euo pipefail

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/checkpoint.sh"
source "$WIGGUM_HOME/lib/runtime/runtime.sh"
source "$WIGGUM_HOME/lib/utils/work-log.sh"

# =============================================================================
# HELPER FUNCTIONS
# =============================================================================

# Extract clean text from backend output log
# Delegates to the active backend's extract_text function
extract_summary_text() {
    local input="$1"

    # If input looks like a file path, pass directly
    if [ -f "$input" ]; then
        runtime_backend_extract_text "$input"
        return
    fi

    # Otherwise, write to temp file and extract (for backward compat with piped content)
    local tmp_file
    tmp_file=$(mktemp)
    echo "$input" > "$tmp_file"
    runtime_backend_extract_text "$tmp_file"
    rm -f "$tmp_file"
}

# =============================================================================
# SUPERVISOR TAG EXTRACTION HELPERS
# =============================================================================

# Extract decision from supervisor output (CONTINUE|STOP|RESTART)
_extract_supervisor_decision() {
    local log_file="$1"
    local decision

    # First try to extract from text content via backend
    local text_content
    text_content=$(runtime_backend_extract_text "$log_file" 2>/dev/null) || true

    if [ -n "$text_content" ]; then
        decision=$(echo "$text_content" | grep_pcre_match '(?<=<decision>)(CONTINUE|STOP|RESTART)(?=</decision>)' | head -1) || true
    fi

    # Fallback: grep raw log file
    if [ -z "${decision:-}" ]; then
        decision=$(grep_pcre_match '(?<=<decision>)(CONTINUE|STOP|RESTART)(?=</decision>)' "$log_file" | head -1) || true
    fi

    # Default to CONTINUE if not found or invalid
    if [ -z "${decision:-}" ]; then
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
# MAIN RALPH LOOP FUNCTION
# =============================================================================

# Unified ralph loop execution with optional supervision
#
# Args:
#   workspace           - Working directory for the agent
#   system_prompt       - System prompt for the agent
#   user_prompt_fn      - Callback: generates work prompts (iteration, output_dir, supervisor_dir, supervisor_feedback)
#   completion_check_fn - Callback: checks if work complete (returns 0 if done, 1 otherwise)
#   max_iterations      - Maximum loop iterations (default: 20)
#   max_turns           - Max turns per session (default: 50)
#   output_dir          - Directory for logs and summaries (default: workspace parent)
#   session_prefix      - Prefix for session files (default: iteration)
#   supervisor_interval - Run supervisor every N iterations; 0 = disabled (default: 0)
#   supervisor_prompt_fn - Callback: generates supervisor prompts (default: _default_supervisor_prompt)
#   max_restarts        - Max RESTART decisions before forcing STOP (default: 2)
#
# Returns: 0 on successful completion, 1 if max iterations reached or error
run_ralph_loop() {
    runtime_init

    local workspace="$1"
    local system_prompt="$2"
    local user_prompt_fn="$3"
    local completion_check_fn="$4"
    local max_iterations="${5:-20}"
    local max_turns="${6:-50}"
    local output_dir="${7:-}"
    local session_prefix="${8:-iteration}"
    local supervisor_interval="${9:-0}"
    local supervisor_prompt_fn="${10:-_default_supervisor_prompt}"
    local max_restarts="${11:-2}"

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
    local restart_count=0
    local shutdown_requested=false
    local last_session_id=""
    local supervisor_feedback=""
    _ralph_loop_completed_normally=false
    local loop_stop_reason="completed"
    local consecutive_fast_fails=0
    local max_consecutive_fast_fails="${WIGGUM_MAX_FAST_FAILS:-3}"
    local fast_fail_threshold_secs="${WIGGUM_FAST_FAIL_THRESHOLD:-5}"

    # Check if backend supports sessions
    local _has_sessions=false
    if runtime_backend_supports_sessions; then
        _has_sessions=true
    fi

    # Determine if supervision is enabled
    local supervision_enabled=false
    if [ "$supervisor_interval" -gt 0 ]; then
        supervision_enabled=true
    fi

    # Signal handler for graceful shutdown
    # shellcheck disable=SC2329
    _ralph_loop_signal_handler() {
        log "Ralph loop received shutdown signal"
        shutdown_requested=true
    }

    # Exit handler for detecting unexpected exits
    # shellcheck disable=SC2329
    _ralph_loop_exit_handler() {
        local exit_code=$?
        if [ "${_ralph_loop_completed_normally:-}" != true ]; then
            log_error "Unexpected exit from ralph loop (exit_code=$exit_code, iteration=${iteration:-unknown}, workspace=${workspace:-unknown})"
        fi
        trap - EXIT
    }
    trap _ralph_loop_exit_handler EXIT
    trap _ralph_loop_signal_handler INT TERM

    # Record start time
    local start_time
    start_time=$(epoch_now)

    # Generate unique run ID for this execution
    local run_id="${session_prefix}-${start_time}"
    export RALPH_RUN_ID="$run_id"

    if [ "$supervision_enabled" = true ]; then
        log "Ralph loop starting with supervision (max $max_iterations iterations, supervisor every $supervisor_interval, run_id=$run_id)"
    else
        log "Ralph loop starting (max $max_iterations iterations, $max_turns turns/session, run_id=$run_id)"
    fi

    # Change to workspace
    cd "$workspace" || {
        log_error "Cannot access workspace: $workspace"
        return 1
    }

    # Ensure base output directories exist (fix workers may skip agent_create_directories)
    mkdir -p "$output_dir/logs"
    mkdir -p "$output_dir/summaries"

    # Create run-namespaced subdirectories
    mkdir -p "$output_dir/logs/$run_id"
    mkdir -p "$output_dir/summaries/$run_id"
    if [ "$supervision_enabled" = true ]; then
        mkdir -p "$output_dir/supervisors"
    fi

    # Initialize work log
    work_log_init "$output_dir"

    # Main iteration loop
    while [ $iteration -lt "$max_iterations" ]; do
        # Check for shutdown request
        if [ "$shutdown_requested" = true ]; then
            log "Ralph loop shutting down due to signal"
            loop_stop_reason="shutdown"
            break
        fi

        # Check rate limit via backend
        local _rl_ralph_dir="${RALPH_DIR:-}"
        if [ -z "$_rl_ralph_dir" ] && [ -n "$output_dir" ]; then
            _rl_ralph_dir=$(cd "$output_dir/../.." 2>/dev/null && pwd || echo "")
        fi
        if [ -n "$_rl_ralph_dir" ] && runtime_backend_rate_limit_check "$_rl_ralph_dir"; then
            log "Rate limit active - pausing before iteration $iteration"
            runtime_backend_rate_limit_wait
            log "Rate limit cleared - resuming iteration $iteration"
        fi

        # Check completion using callback
        if $completion_check_fn 2>/dev/null; then
            log "Completion check passed - work is done"
            loop_stop_reason="completed"
            break
        fi

        # Generate unique session ID for this iteration
        local session_id
        session_id=$(runtime_backend_generate_session_id)
        last_session_id="$session_id"

        # Get user prompt from callback (unified 4-arg signature)
        local supervisor_dir="$output_dir/supervisors"
        local user_prompt
        user_prompt=$($user_prompt_fn "$iteration" "$output_dir" "$supervisor_dir" "$supervisor_feedback")

        log_debug "Iteration $iteration: Session $session_id (max $max_turns turns)"

        # Log iteration start
        if [ "$supervision_enabled" = true ]; then
            echo "[$(iso_now)] INFO: ITERATION_START iteration=$iteration session_id=$session_id max_turns=$max_turns restart_count=$restart_count" >> "$output_dir/worker.log" 2>/dev/null || true
        else
            echo "[$(iso_now)] INFO: ITERATION_START iteration=$iteration session_id=$session_id max_turns=$max_turns" >> "$output_dir/worker.log" 2>/dev/null || true
        fi

        # Generate timestamp for log filename
        local log_timestamp
        log_timestamp=$(epoch_now)
        local log_file="$output_dir/logs/$run_id/${session_prefix}-${iteration}-${log_timestamp}.log"

        log "Work phase starting (see logs/$run_id/${session_prefix}-${iteration}-${log_timestamp}.log for details)"

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

        # PHASE 1: Work session - build args via backend and execute with retry
        local -a work_args=()
        runtime_backend_build_exec_args work_args "$workspace" "$system_prompt" "$user_prompt" "$log_file" "$max_turns" "$session_id"

        local work_start_epoch
        work_start_epoch=$(epoch_now)

        local exit_code=0
        runtime_exec_with_retry "${work_args[@]}" >> "$log_file" 2>&1 || exit_code=$?
        log "Work phase completed (exit code: $exit_code, session: $session_id)"

        local work_duration=$(( $(epoch_now) - work_start_epoch ))

        # Log work phase completion
        echo "[$(iso_now)] INFO: WORK_PHASE_COMPLETE iteration=$iteration exit_code=$exit_code duration_sec=$work_duration" >> "$output_dir/worker.log" 2>/dev/null || true

        # Create checkpoint after work phase
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
            loop_stop_reason="shutdown"
            break
        fi

        # Check if shutdown was requested during work phase
        if [ "$shutdown_requested" = true ]; then
            log "Shutdown requested during work phase - exiting loop"
            loop_stop_reason="shutdown"
            break
        fi

        # Fast-fail detection: if iteration completed in under threshold with non-zero
        # exit, the backend is likely broken (expired session, auth issue, bad workspace).
        # Burning remaining iterations wastes API calls and produces no useful output.
        if [ $exit_code -ne 0 ] && [ "$work_duration" -lt "$fast_fail_threshold_secs" ]; then
            ((++consecutive_fast_fails))
            if [ "$consecutive_fast_fails" -ge "$max_consecutive_fast_fails" ]; then
                log_error "Fast-fail: $consecutive_fast_fails consecutive iterations failed in <${fast_fail_threshold_secs}s — backend is not functional"
                loop_stop_reason="fast_fail"
                break
            fi
            log_warn "Fast-fail: iteration $iteration failed in ${work_duration}s ($consecutive_fast_fails/$max_consecutive_fast_fails before abort)"
        else
            consecutive_fast_fails=0
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

        local summary_log="$output_dir/logs/$run_id/${session_prefix}-${iteration}-${log_timestamp}-summary.log"
        local summary_txt="$output_dir/summaries/$run_id/${session_prefix}-${iteration}-summary.txt"

        local summary_exit_code=0

        if [ "$_has_sessions" = true ]; then
            # Backend supports sessions: resume to get summary
            local -a summary_args=()
            runtime_backend_build_resume_args summary_args "$session_id" "$summary_prompt" "$summary_log" 2

            runtime_exec_with_retry "${summary_args[@]}" \
                > "$summary_log" 2>&1 || summary_exit_code=$?
        else
            # Session-less backend: run a fresh invocation with summary context
            local summary_system="You are summarizing a work session. The following is the log of work performed."
            local summary_with_context
            summary_with_context="Previous work output (from log file):
---
$(runtime_backend_extract_text "$log_file" 2>/dev/null | head -200 || echo "[no output extracted]")
---

${summary_prompt}"

            local -a summary_args=()
            runtime_backend_build_exec_args summary_args "$workspace" "$summary_system" "$summary_with_context" "$summary_log" 2 ""

            runtime_exec_with_retry "${summary_args[@]}" \
                > "$summary_log" 2>&1 || summary_exit_code=$?
        fi

        log "Summary generation completed (exit code: $summary_exit_code)"

        # Extract clean text from output and save
        local summary
        summary=$(extract_summary_text "$summary_log")

        if [ -z "$summary" ]; then
            log_warn "Summary for iteration $iteration is empty"
            summary="[Summary generation failed or produced no output]"
        fi

        echo "$summary" > "$summary_txt"

        # Write structured work log entry
        work_log_write_iteration "$output_dir" "$iteration" "$session_id" "$exit_code" "$summary" "$log_file"

        log "Summary generated for iteration $iteration"

        # Update checkpoint with summary
        checkpoint_update_summary "$output_dir" "$iteration" "$summary_txt"

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
            loop_stop_reason="shutdown"
            break
        fi

        iteration=$((iteration + 1))

        # =================================================================
        # SUPERVISOR PHASE (every N iterations, if enabled)
        # =================================================================
        if [ "$supervision_enabled" = true ] && [ $((iteration % supervisor_interval)) -eq 0 ]; then
            log "Supervisor phase triggered at iteration $iteration"

            local supervisor_session_id
            supervisor_session_id=$(runtime_backend_generate_session_id)

            local supervisor_log="$output_dir/supervisors/supervisor-$iteration.log"
            local supervisor_review="$output_dir/supervisors/supervisor-$iteration-review.md"
            local supervisor_decision_file="$output_dir/supervisors/supervisor-$iteration-decision.txt"
            local supervisor_guidance_file="$output_dir/supervisors/supervisor-$iteration-guidance.md"

            local prev_iter=$((iteration - 1))
            local last_summary_file="$run_id/${session_prefix}-$prev_iter-summary.txt"
            local supervisor_prompt
            supervisor_prompt=$($supervisor_prompt_fn "$iteration" "$output_dir" "$last_summary_file")

            local supervisor_system_prompt="You are a supervisor overseeing an iterative work process. Your bias is toward CONTINUE - only intervene with STOP or RESTART when you have high confidence something is fundamentally wrong. Let workers work."

            log "Running supervisor session $supervisor_session_id"
            echo "[$(iso_now)] INFO: SUPERVISOR_START iteration=$iteration session_id=$supervisor_session_id" >> "$output_dir/worker.log" 2>/dev/null || true

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

            # Run supervisor via backend
            local -a supervisor_args=()
            runtime_backend_build_exec_args supervisor_args "$workspace" "$supervisor_system_prompt" "$supervisor_prompt" "$supervisor_log" 5 "$supervisor_session_id"

            local supervisor_exit_code=0
            runtime_exec_with_retry "${supervisor_args[@]}" >> "$supervisor_log" 2>&1 || supervisor_exit_code=$?
            log "Supervisor session completed (exit code: $supervisor_exit_code)"

            # Extract decision and guidance
            local decision
            decision=$(_extract_supervisor_decision "$supervisor_log")
            echo "$decision" > "$supervisor_decision_file"

            _extract_supervisor_review "$supervisor_log" "$supervisor_review" || true
            _extract_supervisor_guidance "$supervisor_log" "$supervisor_guidance_file" || true

            if [ -f "$supervisor_guidance_file" ]; then
                supervisor_feedback=$(cat "$supervisor_guidance_file")
            else
                supervisor_feedback=""
            fi

            log "Supervisor decision: $decision"
            echo "[$(iso_now)] INFO: SUPERVISOR_COMPLETE iteration=$iteration decision=$decision" >> "$output_dir/worker.log" 2>/dev/null || true

            # Update checkpoint with supervisor decision
            local reviewed_iteration=$((iteration - 1))
            checkpoint_update_supervisor "$output_dir" "$reviewed_iteration" "$decision" "$supervisor_feedback"

            # Handle decision
            case "$decision" in
                CONTINUE)
                    log "Supervisor: CONTINUE - proceeding with guidance"
                    ;;

                STOP)
                    log "Supervisor: STOP - halting loop"
                    echo "[$(iso_now)] INFO: SUPERVISOR_STOP iteration=$iteration reason=supervisor_decision" >> "$output_dir/worker.log" 2>/dev/null || true

                    local end_time
                    end_time=$(epoch_now)
                    local duration=$((end_time - start_time))

                    log "Ralph loop stopped by supervisor after $iteration iterations (duration: ${duration}s)"
                    echo "[$(iso_now)] INFO: LOOP_STOPPED_BY_SUPERVISOR end_time=$end_time duration_sec=$duration iterations=$iteration" >> "$output_dir/worker.log" 2>/dev/null || true

                    export RALPH_LOOP_LAST_SESSION_ID="$last_session_id"
                    export RALPH_LOOP_STOP_REASON="supervisor_stop"
                    _ralph_loop_completed_normally=true
                    trap - EXIT
                    return 0
                    ;;

                RESTART)
                    restart_count=$((restart_count + 1))

                    if [ $restart_count -gt "$max_restarts" ]; then
                        log_warn "Supervisor: RESTART requested but max_restarts ($max_restarts) exceeded - forcing STOP"
                        echo "[$(iso_now)] WARN: RESTART_LIMIT_EXCEEDED restart_count=$restart_count max_restarts=$max_restarts" >> "$output_dir/worker.log" 2>/dev/null || true

                        local end_time
                        end_time=$(epoch_now)
                        local duration=$((end_time - start_time))

                        log "Ralph loop stopped due to restart limit (duration: ${duration}s)"
                        export RALPH_LOOP_LAST_SESSION_ID="$last_session_id"
                        export RALPH_LOOP_STOP_REASON="restart_limit"
                        _ralph_loop_completed_normally=true
                        trap - EXIT
                        return 1
                    fi

                    log "Supervisor: RESTART - archiving run $run_id and resetting to iteration 0"
                    echo "[$(iso_now)] INFO: SUPERVISOR_RESTART iteration=$iteration restart_count=$restart_count run_id=$run_id" >> "$output_dir/worker.log" 2>/dev/null || true

                    local archive_dir="$output_dir/supervisors/run-$((restart_count - 1))"
                    mkdir -p "$archive_dir"
                    mv "$output_dir/logs/$run_id" "$archive_dir/" 2>/dev/null || true
                    mv "$output_dir/summaries/$run_id" "$archive_dir/" 2>/dev/null || true

                    run_id="${session_prefix}-$(epoch_now)"
                    export RALPH_RUN_ID="$run_id"

                    mkdir -p "$output_dir/logs/$run_id"
                    mkdir -p "$output_dir/summaries/$run_id"

                    iteration=0
                    log "Restarted loop - beginning run $run_id (restart_count=$restart_count) with supervisor guidance"
                    ;;
            esac
        fi

        sleep "${WIGGUM_LOOP_DELAY:-2}"  # Prevent tight loop (override with WIGGUM_LOOP_DELAY=0 in tests)
    done

    # Record end time
    local end_time
    end_time=$(epoch_now)
    local duration=$((end_time - start_time))

    if [ "$loop_stop_reason" = "fast_fail" ]; then
        echo "[$(iso_now)] ERROR: LOOP_FAST_FAIL end_time=$end_time duration_sec=$duration iterations=$((iteration + 1)) consecutive_failures=$consecutive_fast_fails" >> "$output_dir/worker.log" 2>/dev/null || true
        export RALPH_LOOP_STOP_REASON="fast_fail"
        export RALPH_LOOP_LAST_SESSION_ID="$last_session_id"
        _ralph_loop_completed_normally=true
        trap - EXIT
        return 1
    fi

    if [ $iteration -ge "$max_iterations" ]; then
        log_error "Ralph loop reached max iterations ($max_iterations) without completing"
        if [ "$supervision_enabled" = true ]; then
            echo "[$(iso_now)] WARN: LOOP_INCOMPLETE end_time=$end_time duration_sec=$duration iterations=$iteration restarts=$restart_count" >> "$output_dir/worker.log" 2>/dev/null || true
        else
            echo "[$(iso_now)] WARN: LOOP_INCOMPLETE end_time=$end_time duration_sec=$duration iterations=$iteration max_iterations=$max_iterations" >> "$output_dir/worker.log" 2>/dev/null || true
        fi
        export RALPH_LOOP_STOP_REASON="max_iterations"
        _ralph_loop_completed_normally=true
        trap - EXIT
        return 1
    fi

    if [ "$supervision_enabled" = true ]; then
        echo "[$(iso_now)] INFO: LOOP_COMPLETED end_time=$end_time duration_sec=$duration iterations=$iteration restarts=$restart_count" >> "$output_dir/worker.log" 2>/dev/null || true
        log "Ralph loop finished after $iteration iterations, $restart_count restarts (duration: ${duration}s)"
    else
        echo "[$(iso_now)] INFO: LOOP_COMPLETED end_time=$end_time duration_sec=$duration iterations=$iteration" >> "$output_dir/worker.log" 2>/dev/null || true
        log "Ralph loop finished after $iteration iterations (duration: ${duration}s)"
    fi

    export RALPH_LOOP_LAST_SESSION_ID="$last_session_id"
    export RALPH_LOOP_STOP_REASON="$loop_stop_reason"

    _ralph_loop_completed_normally=true
    trap - EXIT
    return 0
}

# =============================================================================
# BACKWARD COMPATIBILITY ALIAS
# =============================================================================

run_ralph_loop_supervised() {
    local workspace="$1"
    local system_prompt="$2"
    local user_prompt_fn="$3"
    local completion_check_fn="$4"
    local max_iterations="${5:-20}"
    local max_turns="${6:-50}"
    local output_dir="${7:-}"
    local session_prefix="${8:-iteration}"
    local supervisor_interval="${9:-2}"
    local supervisor_prompt_fn="${10:-_default_supervisor_prompt}"
    local max_restarts="${11:-2}"

    run_ralph_loop "$workspace" "$system_prompt" "$user_prompt_fn" "$completion_check_fn" \
        "$max_iterations" "$max_turns" "$output_dir" "$session_prefix" \
        "$supervisor_interval" "$supervisor_prompt_fn" "$max_restarts"
}
