#!/usr/bin/env bash
# =============================================================================
# pipeline-runner.sh - Execute pipeline steps as a jump-based state machine
#
# Provides:
#   pipeline_run_all(worker_dir, project_dir, workspace, start_from_step)
#
# Requires:
#   - pipeline-loader.sh sourced and pipeline loaded
#   - agent-base.sh sourced (for run_sub_agent, agent_read_subagent_result, etc.)
#   - _phase_start/_phase_end/_commit_subagent_changes from system/task-worker.sh
#   - PIPELINE_PLAN_FILE, PIPELINE_RESUME_INSTRUCTIONS exported by caller
#
# Jump target semantics:
#   self  - Re-run the current step
#   prev  - Re-run the caller (step that invoked current step)
#   next  - Continue to next step in array order
#   abort - Halt pipeline with failure
#   <id>  - Jump to step with matching ID
# =============================================================================

# Prevent double-sourcing
[ -n "${_PIPELINE_RUNNER_LOADED:-}" ] && return 0
_PIPELINE_RUNNER_LOADED=1

source "$WIGGUM_HOME/lib/utils/activity-log.sh"
source "$WIGGUM_HOME/lib/core/agent-base.sh"

# =============================================================================
# PARENT/NEXT CONTEXT PROPAGATION
# =============================================================================

# Compute and export parent step context for the current step
#
# This enables markdown agents to access upstream outputs via variables like
# {{parent.step_id}}, {{parent.session_id}}, {{parent.report}}, etc.
#
# Args:
#   idx        - Current step index
#   worker_dir - Worker directory
#
# Exports:
#   WIGGUM_PARENT_STEP_ID     - Parent step's ID
#   WIGGUM_PARENT_RUN_ID      - Parent step's run ID
#   WIGGUM_PARENT_SESSION_ID  - Parent step's Claude session ID (if any)
#   WIGGUM_PARENT_RESULT      - Parent step's gate result
#   WIGGUM_PARENT_REPORT      - Path to parent step's report file (if any)
#   WIGGUM_PARENT_OUTPUT_DIR  - Parent step's output directory
#   WIGGUM_NEXT_STEP_ID       - Next step's ID
_export_step_context() {
    local idx="$1"
    local worker_dir="$2"

    # Clear previous context
    unset WIGGUM_PARENT_STEP_ID WIGGUM_PARENT_RUN_ID WIGGUM_PARENT_SESSION_ID
    unset WIGGUM_PARENT_RESULT WIGGUM_PARENT_REPORT WIGGUM_PARENT_OUTPUT_DIR
    unset WIGGUM_NEXT_STEP_ID

    local step_count
    step_count=$(pipeline_step_count)

    # Determine parent step (previous step in pipeline, if any)
    if [ "$idx" -gt 0 ]; then
        local parent_idx=$((idx - 1))
        local parent_step_id
        parent_step_id=$(pipeline_get "$parent_idx" ".id")

        export WIGGUM_PARENT_STEP_ID="$parent_step_id"

        # Find parent's latest result file
        local parent_result_file
        parent_result_file=$(agent_find_latest_result "$worker_dir" "$parent_step_id")

        if [ -n "$parent_result_file" ] && [ -f "$parent_result_file" ]; then
            # Extract outputs from parent result
            local parent_session_id parent_result parent_report
            parent_session_id=$(jq -r '.outputs.session_id // ""' "$parent_result_file" 2>/dev/null)
            parent_result=$(jq -r '.outputs.gate_result // ""' "$parent_result_file" 2>/dev/null)
            parent_report=$(jq -r '.outputs.report_file // ""' "$parent_result_file" 2>/dev/null)

            [ -n "$parent_session_id" ] && export WIGGUM_PARENT_SESSION_ID="$parent_session_id"
            [ -n "$parent_result" ] && export WIGGUM_PARENT_RESULT="$parent_result"
            [ -n "$parent_report" ] && export WIGGUM_PARENT_REPORT="$parent_report"

            # Extract run_id from result filename (format: <epoch>-<step_id>-result.json)
            local result_basename
            result_basename=$(basename "$parent_result_file" "-result.json")
            export WIGGUM_PARENT_RUN_ID="$result_basename"
        fi

        # Parent output directory (logs under parent's run_id)
        if [ -n "${WIGGUM_PARENT_RUN_ID:-}" ]; then
            export WIGGUM_PARENT_OUTPUT_DIR="$worker_dir/logs/${WIGGUM_PARENT_RUN_ID}"
        fi
    fi

    # Determine next step (next in pipeline, if any)
    local next_idx=$((idx + 1))
    if [ "$next_idx" -lt "$step_count" ]; then
        local next_step_id
        next_step_id=$(pipeline_get "$next_idx" ".id")
        export WIGGUM_NEXT_STEP_ID="$next_step_id"
    fi

    log_debug "Step context: parent=${WIGGUM_PARENT_STEP_ID:-none}, next=${WIGGUM_NEXT_STEP_ID:-none}"
}

# Clear exported step context (called after step completes)
_clear_step_context() {
    unset WIGGUM_PARENT_STEP_ID WIGGUM_PARENT_RUN_ID WIGGUM_PARENT_SESSION_ID
    unset WIGGUM_PARENT_RESULT WIGGUM_PARENT_REPORT WIGGUM_PARENT_OUTPUT_DIR
    unset WIGGUM_NEXT_STEP_ID
}

# =============================================================================
# JUMP-BASED STATE MACHINE
# =============================================================================

# Global state for jump-based control flow
declare -A _PIPELINE_VISITS=()          # step_id -> visit count (global for workflow)
declare -A _PIPELINE_INLINE_VISITS=()   # "parent_id:handler_id" -> count (global for workflow)
declare -A _PIPELINE_ON_MAX_CASCADE=()  # step_id -> 1 if hit on_max in current cascade
_PIPELINE_NEXT_IDX=0                    # return value for dispatch functions

# Resolve a jump target to a step index
#
# Args:
#   target      - Jump target (self, prev, next, abort, or step ID)
#   current_idx - Current step index
#
# Sets: _PIPELINE_NEXT_IDX
_resolve_jump_target() {
    local target="$1"
    local current_idx="$2"

    case "$target" in
        self)
            _PIPELINE_NEXT_IDX="$current_idx"
            ;;
        prev)
            _PIPELINE_NEXT_IDX=$((current_idx - 1))
            ;;
        next)
            _PIPELINE_NEXT_IDX=$((current_idx + 1))
            ;;
        abort)
            _PIPELINE_NEXT_IDX=-1
            ;;
        *)
            # Named step ID
            local resolved
            resolved=$(pipeline_find_step_index "$target")
            if [ "$resolved" -ge 0 ]; then
                _PIPELINE_NEXT_IDX="$resolved"
            else
                log_error "Jump target '$target' not found, aborting"
                _PIPELINE_NEXT_IDX=-1
            fi
            ;;
    esac
}

# Dispatch on a gate result using the step's on_result handlers
#
# Args:
#   idx         - Step index
#   gate_result - Gate result value from the agent
#   worker_dir  - Worker directory
#   project_dir - Project directory
#   workspace   - Workspace directory
#
# Sets: _PIPELINE_NEXT_IDX
_dispatch_on_result() {
    local idx="$1"
    local gate_result="$2"
    local worker_dir="$3"
    local project_dir="$4"
    local workspace="$5"

    local handler
    handler=$(pipeline_get_on_result "$idx" "$gate_result")

    if [ -z "$handler" ]; then
        # No explicit handler - apply default behaviors per spec:
        # PASS -> next, FAIL -> abort, FIX -> prev, SKIP -> next
        case "$gate_result" in
            FAIL)
                _resolve_jump_target "abort" "$idx"
                ;;
            FIX)
                _resolve_jump_target "prev" "$idx"
                ;;
            *)
                # PASS, SKIP, and unknown results continue to next
                _PIPELINE_NEXT_IDX=$((idx + 1))
                ;;
        esac
        return
    fi

    # Check if it's a jump handler (has "jump" field)
    local jump_target
    jump_target=$(echo "$handler" | jq -r '.jump // empty' 2>/dev/null)

    if [ -n "$jump_target" ]; then
        # Jump handler
        _resolve_jump_target "$jump_target" "$idx"
        return
    fi

    # Check if it's an inline agent handler (has "agent" field)
    local inline_agent
    inline_agent=$(echo "$handler" | jq -r '.agent // empty' 2>/dev/null)

    if [ -n "$inline_agent" ]; then
        # Inline agent handler
        _run_inline_agent "$idx" "$handler" "$worker_dir" "$project_dir" "$workspace"
        return
    fi

    # Unknown handler format - default to next
    log_warn "Unknown on_result handler format for step index $idx, continuing"
    _PIPELINE_NEXT_IDX=$((idx + 1))
}

# Run an inline agent handler
#
# Args:
#   parent_idx   - Parent step index (the caller)
#   handler_json - JSON string of the inline agent handler
#   worker_dir   - Worker directory
#   project_dir  - Project directory
#   workspace    - Workspace directory
#
# Sets: _PIPELINE_NEXT_IDX
_run_inline_agent() {
    local parent_idx="$1"
    local handler_json="$2"
    local worker_dir="$3"
    local project_dir="$4"
    local workspace="$5"

    local parent_id
    parent_id=$(pipeline_get "$parent_idx" ".id")

    # Parse inline handler fields
    local handler_id handler_agent handler_max handler_on_max handler_readonly handler_commit
    handler_id=$(echo "$handler_json" | jq -r '.id // "inline"')
    handler_agent=$(echo "$handler_json" | jq -r '.agent')
    handler_max=$(echo "$handler_json" | jq -r '.max // 0')
    handler_on_max=$(echo "$handler_json" | jq -r '.on_max // "next"')
    handler_readonly=$(echo "$handler_json" | jq -r '.readonly // false')
    handler_commit=$(echo "$handler_json" | jq -r '.commit_after // false')

    # Check inline max visits (global count, never resets)
    local visit_key="${parent_id}:${handler_id}"
    local current_visits="${_PIPELINE_INLINE_VISITS[$visit_key]:-0}"

    if [ "$handler_max" -gt 0 ] && [ "$current_visits" -ge "$handler_max" ]; then
        log "Inline handler '$handler_id' max ($handler_max) exceeded, resolving on_max"
        _resolve_jump_target "$handler_on_max" "$parent_idx"
        return
    fi

    # Increment inline visit counter
    _PIPELINE_INLINE_VISITS[$visit_key]=$((current_visits + 1))

    # Log inline agent header
    local _worker_id
    _worker_id=$(basename "$worker_dir" 2>/dev/null || echo "")

    log_subsection "INLINE AGENT: $handler_id"
    log_kv "Agent" "$handler_agent"
    log_kv "Parent Step" "$parent_id"
    log_kv "Worker ID" "$_worker_id"
    log_kv "Task ID" "${WIGGUM_TASK_ID:-}"
    log_kv "Readonly" "$handler_readonly"
    log_kv "Visit #" "${_PIPELINE_INLINE_VISITS[$visit_key]}"

    # Run the inline agent
    export WIGGUM_STEP_ID="$handler_id"
    export WIGGUM_STEP_READONLY="$handler_readonly"

    # Change to workspace directory before running the agent
    cd "$workspace" || {
        log_error "Cannot access workspace: $workspace"
        _PIPELINE_NEXT_IDX=-1
        return
    }

    run_sub_agent "$handler_agent" "$worker_dir" "$project_dir"

    unset WIGGUM_STEP_READONLY

    # Commit if configured
    if [ "$handler_commit" = "true" ] && [ "$handler_readonly" != "true" ]; then
        _commit_subagent_changes "$workspace" "$handler_agent"
    fi

    # Read inline agent result
    local inline_result
    inline_result=$(agent_read_step_result "$worker_dir" "$handler_id")

    log ""
    log_kv "Inline Result" "$inline_result"

    # Check inline handler's own on_result
    local inline_on_result
    inline_on_result=$(echo "$handler_json" | jq -c ".on_result.\"$inline_result\" // null" 2>/dev/null)

    if [ -n "$inline_on_result" ] && [ "$inline_on_result" != "null" ]; then
        # Inline handler has its own on_result for this value
        local inline_jump
        inline_jump=$(echo "$inline_on_result" | jq -r '.jump // empty' 2>/dev/null)

        if [ -n "$inline_jump" ]; then
            # Jump target resolves in parent context (prev = parent's caller)
            _resolve_jump_target "$inline_jump" "$parent_idx"
            return
        fi
    fi

    # Default: re-run caller (parent step) - implicit jump:prev
    _PIPELINE_NEXT_IDX="$parent_idx"
}

# Run all pipeline steps using jump-based state machine
#
# Args:
#   worker_dir      - Worker directory path
#   project_dir     - Project root directory
#   workspace       - Workspace directory (git worktree)
#   start_from_step - Step ID to start from (empty = first step)
#
# Returns: 0 on success, 1 on abort
pipeline_run_all() {
    local worker_dir="$1"
    local project_dir="$2"
    local workspace="$3"
    local start_from_step="${4:-}"

    local step_count
    step_count=$(pipeline_step_count)

    # Initialize visit counters (global for entire workflow)
    # Use declare -gA to ensure associative array type is set (required for set -u compatibility)
    declare -gA _PIPELINE_VISITS=()
    declare -gA _PIPELINE_INLINE_VISITS=()
    declare -gA _PIPELINE_ON_MAX_CASCADE=()

    local current_idx=0

    # Resolve start_from_step to index
    if [ -n "$start_from_step" ]; then
        local resolved_idx
        resolved_idx=$(pipeline_find_step_index "$start_from_step")
        if [ "$resolved_idx" -ge 0 ]; then
            current_idx="$resolved_idx"
        else
            log_warn "Unknown start_from_step '$start_from_step' - starting from beginning"
        fi
    fi

    # Main state machine loop
    while [ "$current_idx" -ge 0 ] && [ "$current_idx" -lt "$step_count" ]; do
        local step_id
        step_id=$(pipeline_get "$current_idx" ".id")

        # Check enabled_by condition
        local enabled_by
        enabled_by=$(pipeline_get "$current_idx" ".enabled_by")
        if [ -n "$enabled_by" ]; then
            local env_val="${!enabled_by:-}"
            if [ "$env_val" != "true" ]; then
                log_debug "Skipping step '$step_id' (enabled_by=$enabled_by is not 'true')"
                current_idx=$((current_idx + 1))
                continue
            fi
        fi

        # Check workspace still exists
        if [ ! -d "$workspace" ]; then
            log_error "Workspace no longer exists, aborting pipeline at step '$step_id'"
            return 1
        fi

        # Check max visits (global count, never resets)
        local max_visits
        max_visits=$(pipeline_get_max "$current_idx")
        local visit_count="${_PIPELINE_VISITS[$step_id]:-0}"

        if [ "$max_visits" -gt 0 ] && [ "$visit_count" -ge "$max_visits" ]; then
            log "Step '$step_id' max visits ($max_visits) exceeded"

            # Check for on_max loop: if this step already hit on_max in this cascade, abort
            if [ "${_PIPELINE_ON_MAX_CASCADE[$step_id]:-0}" = "1" ]; then
                log_error "Detected on_max loop at step '$step_id', aborting"
                return 1
            fi
            _PIPELINE_ON_MAX_CASCADE[$step_id]=1

            local on_max_target
            on_max_target=$(pipeline_get_on_max "$current_idx")
            _resolve_jump_target "$on_max_target" "$current_idx"
            if [ "$_PIPELINE_NEXT_IDX" -lt 0 ]; then
                log_error "Step '$step_id' max exceeded, aborting"
                return 1
            fi
            current_idx="$_PIPELINE_NEXT_IDX"
            continue
        fi

        # Clear on_max cascade tracker when we actually run a step
        _PIPELINE_ON_MAX_CASCADE=()

        # Increment visit counter
        _PIPELINE_VISITS[$step_id]=$((visit_count + 1))

        # Run the step (agent execution only)
        _pipeline_run_step "$current_idx" "$worker_dir" "$project_dir" "$workspace"

        # Read the gate result
        local gate_result
        gate_result=$(agent_read_step_result "$worker_dir" "$step_id")

        # Dispatch on result (sets _PIPELINE_NEXT_IDX)
        _dispatch_on_result "$current_idx" "$gate_result" "$worker_dir" "$project_dir" "$workspace"

        if [ "$_PIPELINE_NEXT_IDX" -lt 0 ]; then
            log_error "Step '$step_id' result '$gate_result' triggered abort"
            return 1
        fi

        current_idx="$_PIPELINE_NEXT_IDX"
    done

    return 0
}

# Run a single pipeline step (agent execution only)
#
# Args:
#   idx         - Step index in pipeline arrays
#   worker_dir  - Worker directory path
#   project_dir - Project root directory
#   workspace   - Workspace directory
_pipeline_run_step() {
    local idx="$1"
    local worker_dir="$2"
    local project_dir="$3"
    local workspace="$4"

    local step_id step_agent step_readonly commit_after
    step_id=$(pipeline_get "$idx" ".id")
    step_agent=$(pipeline_get "$idx" ".agent")
    step_readonly=$(pipeline_get "$idx" ".readonly" "false")
    commit_after=$(pipeline_get "$idx" ".commit_after" "false")

    # Emit activity log event
    local _worker_id
    _worker_id=$(basename "$worker_dir" 2>/dev/null || echo "")
    activity_log "step.started" "$_worker_id" "${WIGGUM_TASK_ID:-}" "step_id=$step_id" "agent=$step_agent"

    # Log step header with full context
    log_section "PIPELINE STEP: $step_id"
    log_kv "Agent" "$step_agent"
    log_kv "Worker ID" "$_worker_id"
    log_kv "Task ID" "${WIGGUM_TASK_ID:-}"
    log_kv "Readonly" "$step_readonly"
    log_kv "Commit After" "$commit_after"
    log_kv "Visit #" "${_PIPELINE_VISITS[$step_id]:-1}"

    # Track phase timing
    _phase_start "$step_id"

    # Export step ID for result file naming
    export WIGGUM_STEP_ID="$step_id"

    # Export parent/next step context for markdown agents
    _export_step_context "$idx" "$worker_dir"

    # Write step config
    _write_step_config "$worker_dir" "$idx"

    # Special handling for system.task-executor: write executor-config.json
    if [ "$step_agent" = "system.task-executor" ]; then
        _prepare_executor_config "$worker_dir" "$idx"
    fi

    # Run pre-hooks
    _run_step_hooks "pre" "$idx" "$worker_dir" "$project_dir" "$workspace"

    # Export readonly flag for agent-registry's git checkpoint logic
    export WIGGUM_STEP_READONLY="$step_readonly"

    # Change to workspace directory before running the agent
    # Claude sessions are stored per-directory in .claude/, so agents must run
    # from the workspace to access sessions created by the executor
    cd "$workspace" || {
        log_error "Cannot access workspace: $workspace"
        return 1
    }

    # Run the agent
    run_sub_agent "$step_agent" "$worker_dir" "$project_dir"

    unset WIGGUM_STEP_READONLY

    # Run post-hooks
    _run_step_hooks "post" "$idx" "$worker_dir" "$project_dir" "$workspace"

    # Commit changes if configured (and not readonly)
    if [ "$commit_after" = "true" ] && [ "$step_readonly" != "true" ]; then
        _commit_subagent_changes "$workspace" "$step_agent"
    fi

    _phase_end "$step_id"
    local gate_result
    gate_result=$(agent_read_step_result "$worker_dir" "$step_id")

    # Log step completion
    log_subsection "STEP COMPLETED: $step_id"
    log_kv "Result" "${gate_result:-UNKNOWN}"
    log_kv "Finished" "$(date -Iseconds)"

    activity_log "step.completed" "$_worker_id" "${WIGGUM_TASK_ID:-}" "step_id=$step_id" "agent=$step_agent" "result=${gate_result:-UNKNOWN}"

    # Clear step context exports
    _clear_step_context
    unset WIGGUM_STEP_ID
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
            # Validate and call (word splitting on func_args is intentional for multi-arg hooks)
            if declare -F "$func_name" > /dev/null 2>&1; then
                # shellcheck disable=SC2086
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

# Special case: prepare executor-config.json for system.task-executor
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
