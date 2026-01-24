#!/usr/bin/env bash
# =============================================================================
# pipeline-runner.sh - Execute pipeline steps sequentially
#
# Provides:
#   pipeline_run_all(worker_dir, project_dir, workspace, start_from_step)
#
# Requires:
#   - pipeline-loader.sh sourced and pipeline loaded
#   - agent-base.sh sourced (for run_sub_agent, agent_read_subagent_result, etc.)
#   - _phase_start/_phase_end/_commit_subagent_changes from task-worker.sh
#   - PIPELINE_PLAN_FILE, PIPELINE_RESUME_INSTRUCTIONS exported by caller
# =============================================================================

# Prevent double-sourcing
[ -n "${_PIPELINE_RUNNER_LOADED:-}" ] && return 0
_PIPELINE_RUNNER_LOADED=1

source "$WIGGUM_HOME/lib/utils/activity-log.sh"

# Run all pipeline steps from start_from_step onward
#
# Args:
#   worker_dir      - Worker directory path
#   project_dir     - Project root directory
#   workspace       - Workspace directory (git worktree)
#   start_from_step - Step ID to start from (empty = first step)
#
# Returns: 0 on success, 1 if a blocking step failed
pipeline_run_all() {
    local worker_dir="$1"
    local project_dir="$2"
    local workspace="$3"
    local start_from_step="${4:-}"

    local step_count
    step_count=$(pipeline_step_count)
    local start_idx=0

    # Resolve start_from_step to index
    if [ -n "$start_from_step" ]; then
        local resolved_idx
        resolved_idx=$(pipeline_find_step_index "$start_from_step")
        if [ "$resolved_idx" -ge 0 ]; then
            start_idx="$resolved_idx"
        else
            log_warn "Unknown start_from_step '$start_from_step' - starting from beginning"
        fi
    fi

    local i="$start_idx"
    while [ "$i" -lt "$step_count" ]; do
        local step_id
        step_id=$(pipeline_get "$i" ".id")

        # Check enabled_by condition
        local enabled_by
        enabled_by=$(pipeline_get "$i" ".enabled_by")
        if [ -n "$enabled_by" ]; then
            local env_val="${!enabled_by:-}"
            if [ "$env_val" != "true" ]; then
                log_debug "Skipping step '$step_id' (enabled_by=$enabled_by is not 'true')"
                ((++i))
                continue
            fi
        fi

        # Check depends_on condition
        local depends_on
        depends_on=$(pipeline_get "$i" ".depends_on")
        if [ -n "$depends_on" ]; then
            local dep_result
            dep_result=$(agent_read_step_result "$worker_dir" "$depends_on")
            if [ "$dep_result" = "FAIL" ] || [ "$dep_result" = "UNKNOWN" ]; then
                log "Skipping step '$step_id' (depends_on '$depends_on' result: $dep_result)"
                ((++i))
                continue
            fi
        fi

        # Check workspace still exists
        if [ ! -d "$workspace" ]; then
            log_error "Workspace no longer exists, aborting pipeline at step '$step_id'"
            return 1
        fi

        # Run the step
        if ! _pipeline_run_step "$i" "$worker_dir" "$project_dir" "$workspace"; then
            local blocking
            blocking=$(pipeline_get "$i" ".blocking" "true")
            if [ "$blocking" = "true" ]; then
                log_error "Blocking step '$step_id' failed - halting pipeline"
                return 1
            fi
        fi

        ((++i))
    done

    return 0
}

# Run a single pipeline step
#
# Args:
#   idx         - Step index in pipeline arrays
#   worker_dir  - Worker directory path
#   project_dir - Project root directory
#   workspace   - Workspace directory
#
# Returns: 0 on success/non-blocking-failure, 1 on blocking failure
_pipeline_run_step() {
    local idx="$1"
    local worker_dir="$2"
    local project_dir="$3"
    local workspace="$4"

    local step_id step_agent blocking step_readonly commit_after
    step_id=$(pipeline_get "$idx" ".id")
    step_agent=$(pipeline_get "$idx" ".agent")
    blocking=$(pipeline_get "$idx" ".blocking" "true")
    step_readonly=$(pipeline_get "$idx" ".readonly" "false")
    commit_after=$(pipeline_get "$idx" ".commit_after" "false")

    log "Running pipeline step: $step_id (agent=$step_agent, blocking=$blocking, readonly=$step_readonly)"

    # Emit activity log event
    local _worker_id
    _worker_id=$(basename "$worker_dir" 2>/dev/null || echo "")
    activity_log "step.started" "$_worker_id" "${WIGGUM_TASK_ID:-}" "step_id=$step_id" "agent=$step_agent"

    # Track phase timing
    _phase_start "$step_id"

    # Export step ID for result file naming
    export WIGGUM_STEP_ID="$step_id"

    # Write step config
    _write_step_config "$worker_dir" "$idx"

    # Special handling for task-executor: write executor-config.json
    if [ "$step_agent" = "task-executor" ]; then
        _prepare_executor_config "$worker_dir" "$idx"
    fi

    # Run pre-hooks
    _run_step_hooks "pre" "$idx" "$worker_dir" "$project_dir" "$workspace"

    # Export readonly flag for agent-registry's git checkpoint logic
    export WIGGUM_STEP_READONLY="$step_readonly"

    # Run the agent
    run_sub_agent "$step_agent" "$worker_dir" "$project_dir"
    local agent_exit=$?

    unset WIGGUM_STEP_READONLY

    # Read the step result
    local gate_result
    gate_result=$(agent_read_step_result "$worker_dir" "$step_id")
    log "Step '$step_id' result: $gate_result (exit: $agent_exit)"

    # Run post-hooks
    _run_step_hooks "post" "$idx" "$worker_dir" "$project_dir" "$workspace"

    # Handle FIX result
    if [ "$gate_result" = "FIX" ]; then
        local fix_agent
        fix_agent=$(pipeline_get_fix "$idx" ".agent")
        if [ -n "$fix_agent" ]; then
            gate_result=$(_handle_fix_retry "$idx" "$worker_dir" "$project_dir" "$workspace")
        else
            # No fix agent configured, treat FIX as failure for blocking
            if [ "$blocking" = "true" ]; then
                log_error "Step '$step_id' returned FIX but no fix agent configured"
                _phase_end "$step_id"
                unset WIGGUM_STEP_ID
                return 1
            fi
        fi
    fi

    # Handle FAIL/STOP
    if [ "$gate_result" = "FAIL" ] || [ "$gate_result" = "STOP" ]; then
        if [ "$blocking" = "true" ]; then
            _phase_end "$step_id"
            unset WIGGUM_STEP_ID
            return 1
        fi
    fi

    # Commit changes if configured (and not readonly)
    if [ "$commit_after" = "true" ] && [ "$step_readonly" != "true" ]; then
        _commit_subagent_changes "$workspace" "$step_agent"
    fi

    _phase_end "$step_id"
    activity_log "step.completed" "$_worker_id" "${WIGGUM_TASK_ID:-}" "step_id=$step_id" "agent=$step_agent" "result=${gate_result:-UNKNOWN}"
    unset WIGGUM_STEP_ID
    return 0
}

# Handle FIX retry loop
#
# Behaviour: agentA returned FIX. Deduct max_attempts, run fix agent.
# If max_attempts > 0 after deduction, re-run agentA. If agentA returns
# FIX again, repeat. If max_attempts reaches 0, continue to next step.
#
# Args:
#   idx         - Step index
#   worker_dir  - Worker directory
#   project_dir - Project directory
#   workspace   - Workspace directory
#
# Outputs: final gate result to stdout (from verify or fix agent's result)
_handle_fix_retry() {
    local idx="$1"
    local worker_dir="$2"
    local project_dir="$3"
    local workspace="$4"

    local step_id step_agent step_readonly fix_id fix_agent max_attempts fix_commit
    step_id=$(pipeline_get "$idx" ".id")
    step_agent=$(pipeline_get "$idx" ".agent")
    step_readonly=$(pipeline_get "$idx" ".readonly" "false")
    fix_id=$(pipeline_get_fix "$idx" ".id")
    fix_agent=$(pipeline_get_fix "$idx" ".agent")
    max_attempts=$(pipeline_get_fix "$idx" ".max_attempts" "2")
    fix_commit=$(pipeline_get_fix "$idx" ".commit_after" "true")

    local _fix_result="CONTINUE"
    local attempt=0

    while true; do
        ((++attempt))
        ((max_attempts--))

        log "Fix attempt $attempt for step '$step_id' using agent '$fix_agent' (remaining=$max_attempts)" >&2

        # Run fix agent (never readonly - it must modify files)
        export WIGGUM_STEP_ID="${fix_id}-${attempt}"
        run_sub_agent "$fix_agent" "$worker_dir" "$project_dir" >&2

        # Commit fix changes
        if [ "$fix_commit" = "true" ]; then
            _commit_subagent_changes "$workspace" "$fix_agent" >&2
        fi

        # If no attempts remaining, do not re-run agentA - pass fix agent's result on
        if [ "$max_attempts" -le 0 ]; then
            _fix_result=$(agent_read_step_result "$worker_dir" "${fix_id}-${attempt}")
            log "Fix attempts exhausted for step '$step_id', passing fix result: $_fix_result" >&2
            break
        fi

        # Re-run original agent to verify
        local verify_id="${step_id}-verify-${attempt}"
        export WIGGUM_STEP_ID="$verify_id"

        export WIGGUM_STEP_READONLY="$step_readonly"
        run_sub_agent "$step_agent" "$worker_dir" "$project_dir" >&2
        unset WIGGUM_STEP_READONLY

        # Check verification result
        local verify_result
        verify_result=$(agent_read_step_result "$worker_dir" "$verify_id")
        log "Verify attempt $attempt result: $verify_result" >&2

        if [ "$verify_result" != "FIX" ]; then
            log "Step '$step_id' returned '$verify_result' after fix attempt $attempt" >&2
            _fix_result="$verify_result"
            break
        fi

        # Still FIX - loop again
    done

    export WIGGUM_STEP_ID="$step_id"
    echo "$_fix_result"
}

# Execute pre or post hook commands for a step
#
# Args:
#   phase       - "pre" or "post"
#   idx         - Step index
#   worker_dir  - Worker directory
#   project_dir - Project directory
#   workspace   - Workspace directory
_run_step_hooks() {
    local phase="$1"
    local idx="$2"
    local worker_dir="$3"
    local project_dir="$4"
    local workspace="$5"

    local hooks_json
    if [ "$phase" = "pre" ]; then
        hooks_json=$(pipeline_get_json "$idx" ".hooks.pre" "[]")
    else
        hooks_json=$(pipeline_get_json "$idx" ".hooks.post" "[]")
    fi

    # Skip if empty array
    if [ "$hooks_json" = "[]" ] || [ -z "$hooks_json" ]; then
        return 0
    fi

    local hook_count
    hook_count=$(echo "$hooks_json" | jq 'length')

    local step_id
    step_id=$(pipeline_get "$idx" ".id")

    local h=0
    while [ "$h" -lt "$hook_count" ]; do
        local cmd
        cmd=$(echo "$hooks_json" | jq -r ".[$h]")

        log_debug "Running $phase hook for step '$step_id': $cmd"

        # Execute hook via function dispatch (no eval)
        (
            export PIPELINE_WORKER_DIR="$worker_dir"
            export PIPELINE_PROJECT_DIR="$project_dir"
            export PIPELINE_WORKSPACE="$workspace"
            export PIPELINE_STEP_ID="$step_id"
            cd "$workspace" 2>/dev/null || true

            # Split into function name + args
            local func_name="${cmd%% *}"
            local func_args="${cmd#* }"
            [ "$func_args" = "$func_name" ] && func_args=""
            # Validate and call
            if declare -F "$func_name" > /dev/null 2>&1; then
                $func_name $func_args
            else
                log_warn "Hook function not found: $func_name"
            fi
        ) || log_warn "$phase hook failed for step '$step_id': $cmd"

        ((++h))
    done
}

# Write step-config.json for the current step
#
# Args:
#   worker_dir - Worker directory
#   idx        - Step index
_write_step_config() {
    local worker_dir="$1"
    local idx="$2"

    local config_json
    config_json=$(pipeline_get_json "$idx" ".config")
    echo "$config_json" > "$worker_dir/step-config.json"
}

# Special case: prepare executor-config.json for task-executor
# Merges step config with PIPELINE_PLAN_FILE and PIPELINE_RESUME_INSTRUCTIONS
#
# Args:
#   worker_dir - Worker directory
#   idx        - Step index
_prepare_executor_config() {
    local worker_dir="$1"
    local idx="$2"

    local config_json
    config_json=$(pipeline_get_json "$idx" ".config")

    # Extract values from step config with defaults
    local max_iterations max_turns supervisor_interval
    max_iterations=$(echo "$config_json" | jq -r '.max_iterations // 20')
    max_turns=$(echo "$config_json" | jq -r '.max_turns // 50')
    supervisor_interval=$(echo "$config_json" | jq -r '.supervisor_interval // 2')

    local plan_file="${PIPELINE_PLAN_FILE:-}"
    local resume_instructions="${PIPELINE_RESUME_INSTRUCTIONS:-}"

    jq -n \
        --argjson max_iterations "$max_iterations" \
        --argjson max_turns "$max_turns" \
        --argjson supervisor_interval "$supervisor_interval" \
        --arg plan_file "$plan_file" \
        --arg resume_instructions "$resume_instructions" \
        '{
            max_iterations: $max_iterations,
            max_turns: $max_turns,
            supervisor_interval: $supervisor_interval,
            plan_file: $plan_file,
            resume_instructions: $resume_instructions
        }' > "$worker_dir/executor-config.json"
}

