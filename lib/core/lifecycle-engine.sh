#!/usr/bin/env bash
# lifecycle-engine.sh - Generic event engine for worker lifecycle state machine
#
# Provides emit_event() — the single function replacing all scattered
# git_state_set / update_kanban / effect calls across the orchestrator.
#
# emit_event() is entirely generic: it contains zero knowledge of specific
# states, events, or transitions. All behavior comes from the loaded spec
# (via lifecycle-loader.sh). Adding a new state or transition means editing
# JSON, not bash.
set -euo pipefail

[ -n "${_LIFECYCLE_ENGINE_LOADED:-}" ] && return 0
_LIFECYCLE_ENGINE_LOADED=1

source "$WIGGUM_HOME/lib/core/lifecycle-loader.sh"
source "$WIGGUM_HOME/lib/core/lifecycle-guards.sh"
source "$WIGGUM_HOME/lib/worker/git-state.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"

# Emit an event to transition a worker through the lifecycle state machine
#
# Finds the matching transition for the current state + event, evaluates
# guards, executes side effects, updates git-state and kanban.
#
# Args:
#   worker_dir  - Worker directory path
#   event       - Event name (e.g., "merge.succeeded")
#   source      - Caller identifier for audit trail
#   data_json   - Optional context JSON for guards/effects (default: '{}')
#
# Returns:
#   0 - Transition matched and executed
#   1 - No matching transition found
#   2 - All matching transitions rejected by guards
emit_event() {
    local worker_dir="$1"
    local event="$2"
    local source="${3:-unknown}"
    local data_json="${4:-'{}'}"

    if [ "$_LC_LOADED" -ne 1 ]; then
        log_error "lifecycle: spec not loaded — call lifecycle_load() first"
        return 1
    fi

    local current_state
    current_state=$(git_state_get "$worker_dir")

    # Find matching transition: scan transitions for this state+event
    local idx=0 matched=0
    while [ "$idx" -lt "$_LC_TRANSITION_COUNT" ]; do
        local key="${current_state}:${event}:${idx}"
        local wkey="*:${event}:${idx}"    # wildcard check

        local target=""
        local use_key=""
        if [ -n "${_LC_TRANSITIONS[$key]+x}" ]; then
            target="${_LC_TRANSITIONS[$key]}"
            use_key="$key"
        elif [ -n "${_LC_TRANSITIONS[$wkey]+x}" ]; then
            target="${_LC_TRANSITIONS[$wkey]}"
            use_key="$wkey"
        fi

        if [ -n "$use_key" ]; then
            # Evaluate guard if present
            local guard="${_LC_GUARDS[$use_key]:-}"
            if [ -n "$guard" ]; then
                local guard_fn="${_LC_GUARD_FN[$guard]:-}"
                if [ -z "$guard_fn" ]; then
                    log_warn "lifecycle: unknown guard '$guard' for $event"
                    ((++idx)); continue
                fi
                if ! "$guard_fn" "$worker_dir" "$data_json" 2>/dev/null; then
                    ((++idx)); continue  # Guard failed, try next transition
                fi
            fi

            # --- Transition matched ---
            matched=1

            # Record chain state if present (audit trail for transient states)
            local chain="${_LC_CHAINS[$use_key]:-}"
            if [ -n "$chain" ]; then
                git_state_set "$worker_dir" "$chain" "lifecycle:$source" "transient: $event"
            fi

            # Set git state (if target is not "null")
            if [ "$target" != "null" ]; then
                git_state_set "$worker_dir" "$target" "lifecycle:$source" "$event"
            fi

            # Update kanban if specified
            local kanban="${_LC_KANBAN[$use_key]:-}"
            if [ -n "$kanban" ]; then
                _lifecycle_update_kanban "$worker_dir" "$kanban" "$data_json"
            fi

            # Write event log before effects (effects like cleanup_worktree may move worker_dir)
            _lifecycle_log_event "$worker_dir" "$event" "$source" "$current_state" "$target" "$data_json"

            # Execute side effects
            local effects="${_LC_EFFECTS[$use_key]:-}"
            if [ -n "$effects" ]; then
                _lifecycle_run_effects "$effects" "$worker_dir" "$data_json" "$kanban"
            fi

            break
        fi
        ((++idx))
    done

    if [ "$matched" -eq 0 ]; then
        log_warn "lifecycle: no transition for event '$event' from state '$current_state' (source: $source)"
        return 1
    fi
    return 0
}

# Update kanban status for a worker
#
# Resolves task_id and ralph_dir from worker_dir, then calls
# update_kanban_status or update_kanban_failed as appropriate.
#
# Args:
#   worker_dir - Worker directory path
#   kanban     - Kanban status character ("x", "*", "=", " ", etc.)
#   data_json  - Event data JSON (for task_id override)
_lifecycle_update_kanban() {
    local worker_dir="$1"
    local kanban="$2"
    local data_json="${3:-'{}'}"

    local task_id ralph_dir
    task_id=$(_lifecycle_resolve_task_id "$worker_dir" "$data_json")
    ralph_dir=$(_lifecycle_resolve_ralph_dir "$worker_dir" "$data_json")

    local kanban_file="$ralph_dir/kanban.md"
    [ -f "$kanban_file" ] || return 0

    if [ "$kanban" = "*" ]; then
        update_kanban_failed "$kanban_file" "$task_id" || true
    else
        update_kanban_status "$kanban_file" "$task_id" "$kanban" || true
    fi
}

# Execute side effects for a transition
#
# Resolves effect function names and arguments from the spec, substituting
# runtime context (worker_dir, task_id, ralph_dir) and event data (data.*)
# into the argument list.
#
# Args:
#   effects_csv - Comma-separated list of effect names
#   worker_dir  - Worker directory path
#   data_json   - Event data JSON
#   kanban      - Kanban status from this transition (may be empty)
_lifecycle_run_effects() {
    local effects_csv="$1"
    local worker_dir="$2"
    local data_json="${3:-'{}'}"
    local kanban="${4:-}"

    local task_id ralph_dir
    task_id=$(_lifecycle_resolve_task_id "$worker_dir" "$data_json")
    ralph_dir=$(_lifecycle_resolve_ralph_dir "$worker_dir" "$data_json")

    IFS=',' read -ra effect_list <<< "$effects_csv"
    for effect_name in "${effect_list[@]}"; do
        local fn="${_LC_EFFECT_FN[$effect_name]:-}"
        [ -z "$fn" ] && { log_warn "lifecycle: unknown effect: $effect_name"; continue; }

        # Resolve args from spec + runtime context
        local args_spec="${_LC_EFFECT_ARGS[$effect_name]:-}"
        local resolved_args=()
        IFS=',' read -ra arg_names <<< "$args_spec"
        for arg in "${arg_names[@]}"; do
            case "$arg" in
                worker_dir)   resolved_args+=("$worker_dir") ;;
                task_id)      resolved_args+=("$task_id") ;;
                ralph_dir)    resolved_args+=("$ralph_dir") ;;
                kanban_file)  resolved_args+=("$ralph_dir/kanban.md") ;;
                kanban)       resolved_args+=("$kanban") ;;
                data.*)
                    local data_key="${arg#data.}"
                    local data_val
                    data_val=$(echo "$data_json" | jq -r ".${data_key} // empty" 2>/dev/null)
                    resolved_args+=("${data_val:-}")
                    ;;
                *)          resolved_args+=("$arg") ;;
            esac
        done

        "$fn" "${resolved_args[@]}" 2>/dev/null || log_warn "lifecycle: effect '$effect_name' failed (non-fatal)"
    done
}

# Write an event to the worker's lifecycle event log
#
# Args:
#   worker_dir    - Worker directory path
#   event         - Event name
#   source        - Caller identifier
#   from_state    - State before transition
#   to_state      - State after transition
#   data_json     - Event data JSON
_lifecycle_log_event() {
    local worker_dir="$1"
    local event="$2"
    local source="$3"
    local from_state="$4"
    local to_state="$5"
    local data_json="${6:-'{}'}"

    local events_file="$worker_dir/events.jsonl"

    local timestamp
    timestamp=$(iso_now)

    # Write single-line JSON entry
    jq -c -n \
        --arg ts "$timestamp" \
        --arg ev "$event" \
        --arg src "$source" \
        --arg from "$from_state" \
        --arg to "$to_state" \
        '{timestamp: $ts, event: $ev, source: $src, from: $from, to: $to}' \
        >> "$events_file" 2>/dev/null || true
}

# Resolve task_id from worker_dir basename or event data
#
# Priority: data_json.task_id > WIGGUM_TASK_ID env > parsed from worker_dir name
#
# Args:
#   worker_dir - Worker directory path
#   data_json  - Event data JSON
#
# Returns: task_id on stdout
_lifecycle_resolve_task_id() {
    local worker_dir="$1"
    local data_json="${2:-'{}'}"

    # Try data_json first
    local from_data=""
    if [ "$data_json" != "'{}'" ] && [ "$data_json" != "{}" ]; then
        from_data=$(echo "$data_json" | jq -r '.task_id // empty' 2>/dev/null)
    fi
    if [ -n "$from_data" ]; then
        echo "$from_data"
        return 0
    fi

    # Try env var
    if [ -n "${WIGGUM_TASK_ID:-}" ]; then
        echo "$WIGGUM_TASK_ID"
        return 0
    fi

    # Parse from worker_dir basename: worker-TASK-001-12345 -> TASK-001
    local worker_name
    worker_name=$(basename "$worker_dir")
    # Match pattern: worker-<PREFIX>-<NUM>-<rest>
    if [[ "$worker_name" =~ ^worker-([A-Za-z]{2,10}-[0-9]{1,4})- ]]; then
        echo "${BASH_REMATCH[1]}"
        return 0
    fi

    echo "unknown"
}

# Resolve ralph_dir from worker_dir path or event data
#
# worker_dir is typically ralph_dir/workers/worker-XXX, so ralph_dir
# is two levels up.
#
# Args:
#   worker_dir - Worker directory path
#   data_json  - Event data JSON
#
# Returns: ralph_dir on stdout
_lifecycle_resolve_ralph_dir() {
    local worker_dir="$1"
    local data_json="${2:-'{}'}"

    # Try data_json first
    local from_data=""
    if [ "$data_json" != "'{}'" ] && [ "$data_json" != "{}" ]; then
        from_data=$(echo "$data_json" | jq -r '.ralph_dir // empty' 2>/dev/null)
    fi
    if [ -n "$from_data" ]; then
        echo "$from_data"
        return 0
    fi

    # Try RALPH_DIR env
    if [ -n "${RALPH_DIR:-}" ]; then
        echo "$RALPH_DIR"
        return 0
    fi

    # Derive from worker_dir path
    dirname "$(dirname "$worker_dir")"
}
