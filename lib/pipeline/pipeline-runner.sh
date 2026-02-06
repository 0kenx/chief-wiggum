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
source "$WIGGUM_HOME/lib/core/atomic-write.sh"

source "$WIGGUM_HOME/lib/utils/activity-log.sh"
source "$WIGGUM_HOME/lib/core/agent-base.sh"
source "$WIGGUM_HOME/lib/core/agent-stream.sh"
source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"

# =============================================================================
# RESULT CACHING (Performance Optimization)
# =============================================================================
# Cache the last gate result to avoid repeated file lookups and jq parsing.
# agent_read_step_result is called 2-3x per step - caching reduces I/O.

_PIPELINE_LAST_STEP_ID=""
_PIPELINE_LAST_GATE_RESULT=""

# Circuit breaker: consecutive same-result tracking per step
declare -gA _PIPELINE_CONSECUTIVE_RESULT=()   # step_id -> "result:count"
_PIPELINE_CIRCUIT_BREAKER_THRESHOLD="${WIGGUM_CIRCUIT_BREAKER_THRESHOLD:-3}"

# Reset all pipeline runner state (for test isolation without re-sourcing)
_pipeline_runner_reset() {
    _PIPELINE_LAST_STEP_ID=""
    _PIPELINE_LAST_GATE_RESULT=""
    _PIPELINE_NEXT_IDX=0
    _PIPELINE_CIRCUIT_BREAKER_THRESHOLD="${WIGGUM_CIRCUIT_BREAKER_THRESHOLD:-3}"
    unset _PIPELINE_VISITS _PIPELINE_INLINE_VISITS _PIPELINE_ON_MAX_CASCADE _PIPELINE_CONSECUTIVE_RESULT
    declare -gA _PIPELINE_VISITS=()
    declare -gA _PIPELINE_INLINE_VISITS=()
    declare -gA _PIPELINE_ON_MAX_CASCADE=()
    declare -gA _PIPELINE_CONSECUTIVE_RESULT=()
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
# CIRCUIT BREAKER: CONSECUTIVE SAME-RESULT DETECTION
# =============================================================================
# When a step produces the same non-terminal result (e.g., FIX) N times in a
# row, escalate to FAIL. This prevents unfixable issues (like merge conflicts)
# from burning pipeline iterations indefinitely.

# Track a step result and check circuit breaker
#
# Args:
#   step_id     - Pipeline step ID
#   gate_result - The result to track
#
# Returns: 0 if circuit breaker NOT tripped, 1 if tripped (should escalate)
_circuit_breaker_check() {
    local step_id="$1"
    local gate_result="$2"

    # Only track non-terminal results that cause loops (FIX, UNKNOWN)
    # PASS and FAIL are terminal for the step, SKIP moves forward
    if [ "$gate_result" = "PASS" ] || [ "$gate_result" = "FAIL" ] || [ "$gate_result" = "SKIP" ]; then
        _PIPELINE_CONSECUTIVE_RESULT[$step_id]=""
        return 0
    fi

    local prev="${_PIPELINE_CONSECUTIVE_RESULT[$step_id]:-}"
    local prev_result="${prev%%:*}"
    local prev_count="${prev##*:}"
    prev_count="${prev_count:-0}"

    if [ "$prev_result" = "$gate_result" ]; then
        ((++prev_count))
    else
        prev_count=1
    fi

    _PIPELINE_CONSECUTIVE_RESULT[$step_id]="${gate_result}:${prev_count}"

    if [ "$prev_count" -ge "$_PIPELINE_CIRCUIT_BREAKER_THRESHOLD" ]; then
        log_error "Circuit breaker: step '$step_id' returned '$gate_result' $prev_count consecutive times (threshold: $_PIPELINE_CIRCUIT_BREAKER_THRESHOLD)"
        return 1
    fi

    return 0
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

    # Fallback: read valid_results from agent markdown front matter (more precise)
    if [ -z "$valid_values" ] || [ "$valid_values" = "PASS|FAIL|FIX|SKIP" ]; then
        local agent_md="$WIGGUM_HOME/lib/agents/${step_agent//.//}.md"
        if [ -f "$agent_md" ]; then
            local fm_values
            fm_values=$(sed -n '/^---$/,/^---$/p' "$agent_md" | grep 'valid_results:' | \
                sed 's/.*\[//;s/\].*//;s/,/|/g;s/ //g')
            [ -n "$fm_values" ] && valid_values="$fm_values"
        fi
    fi

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
    unset WIGGUM_CONTEXT_UPDATES WIGGUM_CONTEXT_UPDATES_FILE
}

# =============================================================================
# CONTEXT UPDATE INJECTION
# =============================================================================
# Load context updates for a worker from the context-updates.json file.
# This file is written by GitHub sync when issue content changes for
# in-progress tasks, allowing agents to see updated requirements.

# Load context updates for this worker
#
# Reads context-updates.json if it exists and exports the content
# as WIGGUM_CONTEXT_UPDATES for agent prompt interpolation.
#
# Args:
#   worker_dir - Worker directory path
#
# Exports:
#   WIGGUM_CONTEXT_UPDATES      - JSON content of context updates
#   WIGGUM_CONTEXT_UPDATES_FILE - Path to the context file
_load_context_updates() {
    local worker_dir="$1"
    local context_file="$worker_dir/context-updates.json"

    if [ -f "$context_file" ]; then
        export WIGGUM_CONTEXT_UPDATES
        WIGGUM_CONTEXT_UPDATES=$(cat "$context_file")
        export WIGGUM_CONTEXT_UPDATES_FILE="$context_file"
        log_debug "Loaded context updates from $context_file"
    else
        export WIGGUM_CONTEXT_UPDATES=""
        export WIGGUM_CONTEXT_UPDATES_FILE=""
    fi
}

# =============================================================================
# PER-WORKER COST BUDGETING
# =============================================================================

# Update incremental cost tracking after a pipeline step completes
#
# Reads total_cost_usd from the step's log files and appends to
# the worker's cost-tracker.json. Skips silently if no cost data found.
#
# Args:
#   worker_dir - Worker directory path
#   step_id    - Pipeline step ID that just completed
_update_step_cost() {
    local worker_dir="$1"
    local step_id="$2"
    local tracker="$worker_dir/cost-tracker.json"

    local log_dir
    log_dir=$(find "$worker_dir/logs" -maxdepth 1 -type d -name "${step_id}-*" 2>/dev/null | sort | tail -1)
    [ -n "$log_dir" ] || return 0

    local step_cost
    step_cost=$(find "$log_dir" -name "*.log" ! -name "*summary*" ! -name "*backup*" \
        -exec grep '"type":"result"' {} \; 2>/dev/null | \
        jq -s '[.[] | .total_cost_usd // 0] | add // 0' 2>/dev/null)
    step_cost="${step_cost:-0}"

    if [ ! -f "$tracker" ]; then
        jq -n --argjson cost "$step_cost" --arg step "$step_id" \
            '{total_cost: $cost, steps: [{id: $step, cost: $cost}]}' > "$tracker"
    else
        jq --argjson cost "$step_cost" --arg step "$step_id" \
            '.total_cost += $cost | .steps += [{id: $step, cost: $cost}]' \
            "$tracker" > "${tracker}.tmp" && mv "${tracker}.tmp" "$tracker"
    fi
}

# Check if the worker's accumulated cost exceeds the budget
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: 0 if within budget (or no limit set), 1 if over budget
_check_cost_budget() {
    local worker_dir="$1"
    local limit="${WIGGUM_WORKER_COST_LIMIT:-}"
    [ -n "$limit" ] || return 0

    local tracker="$worker_dir/cost-tracker.json"
    [ -f "$tracker" ] || return 0

    local current_cost
    current_cost=$(jq -r '.total_cost // 0' "$tracker" 2>/dev/null)
    current_cost="${current_cost:-0}"

    local cost_cents limit_cents
    cost_cents=$(awk "BEGIN {printf \"%d\", $current_cost * 100}")
    limit_cents=$(awk "BEGIN {printf \"%d\", $limit * 100}")

    if [ "${cost_cents:-0}" -gt "${limit_cents:-0}" ]; then
        log_error "Worker cost \$${current_cost} exceeds limit \$${limit}"
        return 1
    fi
    return 0
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
            if [ "$current_idx" -le 0 ]; then
                log_warn "Jump target 'prev' at step 0 has no previous step, falling back to 'self'"
                _PIPELINE_NEXT_IDX=0
            else
                _PIPELINE_NEXT_IDX=$((current_idx - 1))
            fi
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

    # Verify workspace exists before inline agent invocation
    if [ ! -d "$workspace" ]; then
        log_error "Workspace disappeared before inline agent '$handler_id': $workspace"
        _PIPELINE_NEXT_IDX=-1
        return
    fi

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

    # Reset parent step's circuit breaker counter — the inline handler ran
    # between parent re-runs, so consecutive same-result tracking restarts.
    _PIPELINE_CONSECUTIVE_RESULT[$parent_id]=""

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
    declare -gA _PIPELINE_CONSECUTIVE_RESULT=()

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

    # Resolve per-task cost limit override (pipeline JSON > env > default)
    if [ -n "${_PIPELINE_JSON_FILE:-}" ] && [ -f "$_PIPELINE_JSON_FILE" ]; then
        local task_cost_limit
        task_cost_limit=$(jq -r '.cost_limit // empty' "$_PIPELINE_JSON_FILE" 2>/dev/null) || true
        if [ -n "$task_cost_limit" ]; then
            WIGGUM_WORKER_COST_LIMIT="$task_cost_limit"
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

        # Check cost budget before each step
        if ! _check_cost_budget "$worker_dir"; then
            log_error "Pipeline aborted: cost budget exceeded"
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

        # Track incremental cost after step completes
        _update_step_cost "$worker_dir" "$step_id"

        # Read the gate result (using cache - subsequent calls use cached value)
        local gate_result
        gate_result=$(_get_cached_step_result "$worker_dir" "$step_id")

        # Circuit breaker: if the same step returns the same non-terminal result
        # (e.g., FIX) too many times in a row, escalate to FAIL. This prevents
        # unfixable issues from burning iterations (e.g., merge conflicts causing
        # repeated FIX loops in generic-fix agent).
        if ! _circuit_breaker_check "$step_id" "$gate_result"; then
            log_error "Escalating '$gate_result' to FAIL for step '$step_id' due to circuit breaker"
            gate_result="FAIL"
            agent_write_result "$worker_dir" "$gate_result"
            _PIPELINE_LAST_GATE_RESULT="$gate_result"
        fi

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

    local step_id step_agent step_readonly commit_after step_timeout
    step_id=$(pipeline_get "$idx" ".id")
    step_agent=$(pipeline_get "$idx" ".agent")
    step_readonly=$(pipeline_get "$idx" ".readonly" "false")
    commit_after=$(pipeline_get "$idx" ".commit_after" "false")
    step_timeout=$(pipeline_get "$idx" ".timeout_seconds" "")

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

    # Write step start time for heartbeat progress display
    epoch_now > "$worker_dir/step-start-time"

    # Export step ID for result file naming
    export WIGGUM_STEP_ID="$step_id"

    # Export parent/next step context for markdown agents
    _export_step_context "$idx" "$worker_dir"

    # Load context updates for this worker (from GitHub sync)
    _load_context_updates "$worker_dir"

    # Update current step pointer in pipeline-config.json
    _update_current_step "$worker_dir" "$idx" "$step_id"

    # Run pre-hooks
    _run_step_hooks "pre" "$idx" "$worker_dir" "$project_dir" "$workspace"

    # Export readonly flag for agent-registry's git checkpoint logic
    export WIGGUM_STEP_READONLY="$step_readonly"

    # Verify workspace exists immediately before agent invocation.
    # This catches cases where workspace was deleted mid-pipeline (e.g., by
    # orchestrator cleanup) — without this check, the agent gets a confusing
    # 0-second failure with no useful error.
    if [ ! -d "$workspace" ]; then
        log_error "Workspace disappeared before agent invocation: $workspace"
        log_error "Step '$step_id' cannot proceed — aborting pipeline"
        # Write a FAIL result so the step has a recorded outcome
        agent_write_result "$worker_dir" "FAIL"
        return 1
    fi

    # Change to workspace directory before running the agent
    # Claude sessions are stored per-directory in .claude/, so agents must run
    # from the workspace to access sessions created by the executor
    cd "$workspace" || {
        log_error "Cannot access workspace: $workspace"
        return 1
    }

    # Resolve step timeout: step config > agent config > no timeout
    if [ -z "$step_timeout" ]; then
        step_timeout=$(jq -r ".agents[\"$step_agent\"].timeout_seconds // 0" \
            "$WIGGUM_HOME/config/agents.json" 2>/dev/null)
        step_timeout="${step_timeout:-0}"
    fi

    # Run the agent (with optional timeout enforcement)
    if [ "${step_timeout:-0}" -gt 0 ]; then
        log_debug "Step '$step_id' timeout: ${step_timeout}s"
        export WIGGUM_STEP_TIMEOUT="$step_timeout"
        local _step_timed_out=false

        # Run agent in a subshell (preserves shell functions) with a watchdog.
        # Previous approach used `bash -c 'run_sub_agent ...'` which fails because
        # run_sub_agent is a shell function not available in the new bash process.
        local _agent_exit=0
        (
            run_sub_agent "$step_agent" "$worker_dir" "$project_dir"
        ) &
        local _agent_pid=$!

        # Watchdog: kill the subshell and all descendants after timeout
        # Uses kill_process_tree to ensure grandchild processes (like claude CLI
        # spawned inside ralph loops) are also terminated, preventing orphans.
        (
            sleep "$step_timeout"
            # TERM first to allow graceful shutdown
            kill_process_tree "$_agent_pid" TERM
            sleep 30
            # KILL if still running
            kill_process_tree "$_agent_pid" KILL
        ) &
        local _watchdog_pid=$!

        wait "$_agent_pid" 2>/dev/null || _agent_exit=$?
        # Clean up watchdog
        kill "$_watchdog_pid" 2>/dev/null; wait "$_watchdog_pid" 2>/dev/null || true

        # 143 = SIGTERM (128+15), 137 = SIGKILL (128+9)
        if [ "$_agent_exit" -eq 143 ] || [ "$_agent_exit" -eq 137 ]; then
            _step_timed_out=true
            log_error "Step '$step_id' timed out after ${step_timeout}s"
            agent_write_result "$worker_dir" "FAIL"
        fi

        unset WIGGUM_STEP_TIMEOUT
    else
        run_sub_agent "$step_agent" "$worker_dir" "$project_dir"
    fi

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
    # The agent may report PASS but the work is uncommittable.
    # Classify the failure as FIX so the previous agent retries and
    # resolves any conflict markers.
    if [ "$commit_failed" = true ] && [ "$gate_result" = "PASS" ]; then
        local failure_type
        failure_type=$(git_classify_commit_failure "$workspace")
        log_warn "Overriding gate_result PASS -> $failure_type: commit failed"
        gate_result="$failure_type"
        # Rewrite the result file so downstream reads see the classified result
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

    # Emit step-completed event for heartbeat to pick up
    echo "${step_id}|${gate_result:-UNKNOWN}" > "$worker_dir/step-completed-event"

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
                join("\u001e")
            ' 2>/dev/null || true)

            if [ -n "$inline_handlers" ]; then
                while IFS=$'\x1e' read -r handler_id handler_agent handler_config; do
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
    atomic_write "$worker_dir/pipeline-config.json" jq -n \
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
        }'

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
    tmp_file=$(mktemp "${config_file}.XXXXXX")
    jq --argjson idx "$idx" --arg id "$step_id" \
        '.current = {step_idx: $idx, step_id: $id}' \
        "$config_file" > "$tmp_file" && mv "$tmp_file" "$config_file"
}

