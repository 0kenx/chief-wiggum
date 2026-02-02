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
source "$WIGGUM_HOME/lib/core/platform.sh"

source "$WIGGUM_HOME/lib/utils/activity-log.sh"
source "$WIGGUM_HOME/lib/core/agent-base.sh"
source "$WIGGUM_HOME/lib/core/agent-stream.sh"

# =============================================================================
# RESULT CACHING (Performance Optimization)
# =============================================================================
# Cache the last gate result to avoid repeated file lookups and jq parsing.
# agent_read_step_result is called 2-3x per step - caching reduces I/O.

_PIPELINE_LAST_STEP_ID=""
_PIPELINE_LAST_GATE_RESULT=""

# Reset all pipeline runner state (for test isolation without re-sourcing)
_pipeline_runner_reset() {
    _PIPELINE_LAST_STEP_ID=""
    _PIPELINE_LAST_GATE_RESULT=""
    _PIPELINE_NEXT_IDX=0
    unset _PIPELINE_VISITS _PIPELINE_INLINE_VISITS _PIPELINE_ON_MAX_CASCADE
    declare -gA _PIPELINE_VISITS=()
    declare -gA _PIPELINE_INLINE_VISITS=()
    declare -gA _PIPELINE_ON_MAX_CASCADE=()
}

# Get cached step result, or read from file if not cached
#
# Args:
#   worker_dir - Worker directory path
#   step_id    - Pipeline step ID
#
# Returns: gate_result value
_get_cached_step_result() {
    local worker_dir="$1"
    local step_id="$2"

    # Return cached result if same step
    if [ "$_PIPELINE_LAST_STEP_ID" = "$step_id" ] && [ -n "$_PIPELINE_LAST_GATE_RESULT" ]; then
        echo "$_PIPELINE_LAST_GATE_RESULT"
        return 0
    fi

    # Cache miss - read from file
    local result
    result=$(agent_read_step_result "$worker_dir" "$step_id")
    _PIPELINE_LAST_STEP_ID="$step_id"
    _PIPELINE_LAST_GATE_RESULT="$result"

    echo "$result"
}

# Clear the result cache (called when starting a new step)
_clear_result_cache() {
    _PIPELINE_LAST_STEP_ID=""
    _PIPELINE_LAST_GATE_RESULT=""
}

# =============================================================================
# PIPELINE-LEVEL BACKUP RESULT EXTRACTION
# =============================================================================
# When a step returns UNKNOWN, attempt to recover the result by resuming the
# session and explicitly asking for the result tag. This generalizes the
# backup mechanism from agent-stream.sh/_backup_result_extraction so that ALL
# pipeline steps benefit, regardless of agent type or completion_check mode.

# Attempt backup session resume to recover an UNKNOWN result
#
# Args:
#   worker_dir - Worker directory path
#   step_id    - Pipeline step ID
#   step_agent - Agent type (for looking up valid results)
#
# Returns: Recovered gate_result or "UNKNOWN"
_pipeline_backup_result_extraction() {
    local worker_dir="$1"
    local step_id="$2"
    local step_agent="$3"

    local backup_enabled="${WIGGUM_RESULT_BACKUP_ENABLED:-true}"
    if [ "$backup_enabled" != "true" ]; then
        echo "UNKNOWN"
        return 0
    fi

    # Get session_id from the result file
    local result_file session_id
    result_file=$(agent_find_latest_result "$worker_dir" "$step_id")
    if [ -z "$result_file" ] || [ ! -f "$result_file" ]; then
        echo "UNKNOWN"
        return 0
    fi
    session_id=$(jq -r '.outputs.session_id // ""' "$result_file" 2>/dev/null)

    # Fallback: try RALPH_LOOP_LAST_SESSION_ID if result file has no session
    if [ -z "$session_id" ]; then
        session_id="${RALPH_LOOP_LAST_SESSION_ID:-}"
    fi

    if [ -z "$session_id" ]; then
        log_debug "Pipeline backup: no session_id for step '$step_id' — cannot resume"
        echo "UNKNOWN"
        return 0
    fi

    # Build valid values from result_mappings keys (excluding UNKNOWN itself)
    local valid_values=""
    local config_file="$WIGGUM_HOME/config/agents.json"
    if [ -f "$config_file" ]; then
        valid_values=$(jq -r '
            [.defaults.result_mappings // {} | keys[]] +
            [.agents["'"$step_agent"'"].result_mappings // {} | keys[]]
            | unique | map(select(. != "UNKNOWN")) | join("|")
        ' "$config_file" 2>/dev/null)
    fi
    valid_values="${valid_values:-PASS|FAIL|FIX|SKIP}"

    log "Pipeline backup: attempting session resume for step '$step_id' (session: ${session_id:0:8}...)"

    local recovered
    recovered=$(_backup_result_extraction "$session_id" "$valid_values" "$worker_dir" "$step_id")

    if [ -n "$recovered" ] && [ "$recovered" != "UNKNOWN" ]; then
        log "Pipeline backup: recovered result '$recovered' for step '$step_id'"
        # Rewrite result file with recovered value
        agent_write_result "$worker_dir" "$recovered"
        echo "$recovered"
    else
        log_warn "Pipeline backup: session resume failed for step '$step_id' — result remains UNKNOWN"
        echo "UNKNOWN"
    fi
}

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
    # Search backward from idx-1 to find a step with a result file containing
    # a session_id. This handles resumed pipelines where the immediate parent
    # may not have been executed in this run.
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

            # If immediate parent has no session_id (e.g., resumed pipeline skipped it),
            # search backward through earlier steps for one with a session_id
            if [ -z "$parent_session_id" ]; then
                local search_idx=$((parent_idx - 1))
                while [ "$search_idx" -ge 0 ]; do
                    local search_step_id
                    search_step_id=$(pipeline_get "$search_idx" ".id")
                    local search_result_file
                    search_result_file=$(agent_find_latest_result "$worker_dir" "$search_step_id")
                    if [ -n "$search_result_file" ] && [ -f "$search_result_file" ]; then
                        local search_session_id
                        search_session_id=$(jq -r '.outputs.session_id // ""' "$search_result_file" 2>/dev/null)
                        if [ -n "$search_session_id" ]; then
                            parent_session_id="$search_session_id"
                            log_debug "Inherited session_id from step '$search_step_id' (parent '$parent_step_id' had none)"
                            break
                        fi
                    fi
                    ((search_idx--))
                done
            fi

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

    # If this is the first step of a resumed run and no parent report was set,
    # use resume_instructions as the parent report
    if [ "$idx" -eq "${_PIPELINE_START_IDX:-0}" ] && [ -z "${WIGGUM_PARENT_REPORT:-}" ]; then
        if [ -n "${PIPELINE_RESUME_INSTRUCTIONS:-}" ] && [ -f "${PIPELINE_RESUME_INSTRUCTIONS:-}" ]; then
            export WIGGUM_PARENT_REPORT="$PIPELINE_RESUME_INSTRUCTIONS"
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

    log_debug "Jump: '$target' from step $current_idx -> $_PIPELINE_NEXT_IDX"
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

    local step_id
    step_id=$(pipeline_get "$idx" ".id")
    local step_agent
    step_agent=$(pipeline_get "$idx" ".agent")

    log_debug "Step '$step_id' result: $gate_result"

    local handler
    handler=$(pipeline_get_on_result "$idx" "$gate_result")

    if [ -z "$handler" ]; then
        # No explicit handler - use config-driven default_jump from result_mappings
        # Resolution order: pipeline -> agent -> defaults
        local default_jump
        default_jump=$(pipeline_get_result_mapping "$gate_result" "default_jump" "$step_agent")

        log_debug "Result mapping: step=$step_id agent=$step_agent result=$gate_result -> default_jump=${default_jump:-none}"

        if [ -n "$default_jump" ]; then
            _resolve_jump_target "$default_jump" "$idx"
        else
            # Unknown result - abort to prevent silent continuation on unexpected values
            local step_id
            step_id=$(pipeline_get "$idx" ".id")
            log_error "Step '$step_id' returned unknown result '$gate_result' (not in result_mappings)"
            log_error "Define '$gate_result' in result_mappings (config/agents.json or pipeline.json)"
            _resolve_jump_target "abort" "$idx"
        fi
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

    # Write pipeline-config.json once at pipeline start
    _write_pipeline_config "$worker_dir"

    # Reset all pipeline state (defensive, ensures clean slate for each run)
    _PIPELINE_NEXT_IDX=0

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

    # Track start index for resume context propagation
    export _PIPELINE_START_IDX="$current_idx"

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

        log_debug "Step '$step_id' visits: $visit_count/${max_visits:-unlimited}"

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

        # Clear result cache before running step
        _clear_result_cache

        # Run the step (agent execution only)
        _pipeline_run_step "$current_idx" "$worker_dir" "$project_dir" "$workspace"

        # Read the gate result (using cache - subsequent calls use cached value)
        local gate_result
        gate_result=$(_get_cached_step_result "$worker_dir" "$step_id")

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

    # Update current step pointer in pipeline-config.json
    _update_current_step "$worker_dir" "$idx" "$step_id"

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
    local commit_failed=false
    if [ "$commit_after" = "true" ] && [ "$step_readonly" != "true" ]; then
        if ! _commit_subagent_changes "$workspace" "$step_agent"; then
            commit_failed=true
        fi
    fi

    _phase_end "$step_id"

    # Read result and populate cache for subsequent calls
    local gate_result
    gate_result=$(agent_read_step_result "$worker_dir" "$step_id")

    # Override gate_result when commit failed due to conflict markers.
    # The agent may report PASS but the work is uncommittable — FIX signals
    # the pipeline to jump back and resolve the issue.
    if [ "$commit_failed" = true ] && [ "$gate_result" = "PASS" ]; then
        log_warn "Overriding gate_result PASS -> FIX: commit failed (likely conflict markers)"
        gate_result="FIX"
        # Rewrite the result file so downstream reads see FIX
        agent_write_result "$worker_dir" "$gate_result"
    fi

    # Pipeline-level backup extraction: when result is UNKNOWN, resume the
    # session and ask for the result tag. This catches cases where agent-level
    # extraction failed (status_file agents, empty logs, truncated output).
    if [ "$gate_result" = "UNKNOWN" ]; then
        gate_result=$(_pipeline_backup_result_extraction "$worker_dir" "$step_id" "$step_agent")
    fi

    _PIPELINE_LAST_STEP_ID="$step_id"
    _PIPELINE_LAST_GATE_RESULT="$gate_result"

    # Log step completion
    log_subsection "STEP COMPLETED: $step_id"
    log_kv "Result" "${gate_result:-UNKNOWN}"
    log_kv "Finished" "$(iso_now)"

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

# =============================================================================
# PIPELINE CONFIG MANAGEMENT
# =============================================================================

# Write pipeline-config.json once at pipeline start
#
# This file contains all step configurations and runtime context in a single file.
# It replaces both step-config.json and executor-config.json.
#
# Structure:
# {
#   "pipeline": { "name": "...", "source": "..." },
#   "runtime": { "plan_file": "...", "resume_instructions": "..." },
#   "current": { "step_idx": 0, "step_id": "planning" },
#   "steps": {
#     "step-id": { "agent": "...", "config": {...} },
#     ...
#   }
# }
#
# Args:
#   worker_dir - Worker directory path
_write_pipeline_config() {
    local worker_dir="$1"
    local step_count
    step_count=$(pipeline_step_count)

    # Build steps map - iterate through all steps including inline handlers
    local steps_json="{}"
    local idx=0
    while [ "$idx" -lt "$step_count" ]; do
        local step_id step_agent step_config_json
        step_id=$(pipeline_get "$idx" ".id")
        step_agent=$(pipeline_get "$idx" ".agent")
        step_config_json=$(pipeline_get_json "$idx" ".config" "{}")

        # Add step to map
        steps_json=$(echo "$steps_json" | jq \
            --arg id "$step_id" \
            --arg agent "$step_agent" \
            --argjson config "$step_config_json" \
            '.[$id] = {"agent": $agent, "config": $config}')

        # Check for inline handlers in on_result and add them too
        local on_result_json
        on_result_json=$(pipeline_get_json "$idx" ".on_result" "null")
        if [ "$on_result_json" != "null" ]; then
            # Extract inline handler IDs and their configs
            local inline_handlers
            inline_handlers=$(echo "$on_result_json" | jq -r '
                to_entries[] |
                select(.value.agent != null) |
                [.value.id // "inline", .value.agent, (.value.config // {} | tojson)] |
                @tsv
            ' 2>/dev/null || true)

            if [ -n "$inline_handlers" ]; then
                while IFS=$'\t' read -r handler_id handler_agent handler_config; do
                    [ -z "$handler_id" ] && continue
                    steps_json=$(echo "$steps_json" | jq \
                        --arg id "$handler_id" \
                        --arg agent "$handler_agent" \
                        --argjson config "$handler_config" \
                        '.[$id] = {"agent": $agent, "config": $config}')
                done <<< "$inline_handlers"
            fi
        fi

        ((++idx))
    done

    # Get pipeline source path
    local pipeline_source=""
    if [ -n "${_PIPELINE_JSON_FILE:-}" ]; then
        pipeline_source="$_PIPELINE_JSON_FILE"
    fi

    # Build runtime context
    local plan_file="${PIPELINE_PLAN_FILE:-}"
    local resume_instructions="${PIPELINE_RESUME_INSTRUCTIONS:-}"

    # Write the full config
    jq -n \
        --arg name "${PIPELINE_NAME:-unnamed}" \
        --arg source "$pipeline_source" \
        --arg plan_file "$plan_file" \
        --arg resume_instructions "$resume_instructions" \
        --argjson steps "$steps_json" \
        '{
            pipeline: {
                name: $name,
                source: $source
            },
            runtime: {
                plan_file: $plan_file,
                resume_instructions: $resume_instructions
            },
            current: {
                step_idx: 0,
                step_id: ""
            },
            steps: $steps
        }' > "$worker_dir/pipeline-config.json"

    log_debug "Wrote pipeline-config.json with $(echo "$steps_json" | jq 'keys | length') steps"
}

# Update current step in pipeline-config.json (atomic jq update)
#
# Args:
#   worker_dir - Worker directory path
#   idx        - Current step index
#   step_id    - Current step ID
_update_current_step() {
    local worker_dir="$1"
    local idx="$2"
    local step_id="$3"
    local config_file="$worker_dir/pipeline-config.json"

    if [ ! -f "$config_file" ]; then
        log_warn "pipeline-config.json not found, cannot update current step"
        return 0
    fi

    # Atomic update using temp file
    local tmp_file
    tmp_file=$(mktemp)
    jq --argjson idx "$idx" --arg id "$step_id" \
        '.current = {step_idx: $idx, step_id: $id}' \
        "$config_file" > "$tmp_file" && mv "$tmp_file" "$config_file"
}

