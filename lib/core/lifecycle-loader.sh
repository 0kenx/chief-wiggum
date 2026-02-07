#!/usr/bin/env bash
# lifecycle-loader.sh - Load-time compilation of worker lifecycle spec
#
# Reads config/worker-lifecycle.json once at source time and populates
# bash associative arrays for O(1) lookups by the lifecycle engine.
#
# The spec is the single source of truth for all states, transitions,
# guards, and effects. No code outside this module and lifecycle-engine.sh
# should need to know about specific state names or transition rules.
set -euo pipefail

[ -n "${_LIFECYCLE_LOADER_LOADED:-}" ] && return 0
_LIFECYCLE_LOADER_LOADED=1

# Associative arrays populated at load time from worker-lifecycle.json
declare -gA _LC_TRANSITIONS=()    # "state:event:N" -> "target_state"
declare -gA _LC_GUARDS=()         # "state:event:N" -> "guard_name"
declare -gA _LC_KANBAN=()         # "state:event:N" -> "kanban_status"
declare -gA _LC_EFFECTS=()        # "state:event:N" -> "effect1,effect2,..."
declare -gA _LC_CHAINS=()         # "state:event:N" -> "chain_state"
declare -gA _LC_STATE_TYPE=()     # "state" -> "type"
declare -gA _LC_VALID_STATES=()   # "state" -> "1"
declare -gA _LC_GUARD_FN=()       # "guard_name" -> "function_name"
declare -gA _LC_EFFECT_FN=()      # "effect_name" -> "function_name"
declare -gA _LC_EFFECT_ARGS=()    # "effect_name" -> "arg1,arg2,..."
declare -g  _LC_TRANSITION_COUNT=0
declare -g  _LC_LOADED=0

# Load the worker lifecycle spec from JSON into associative arrays
#
# Args:
#   spec_file - Path to worker-lifecycle.json (optional, defaults to
#               $WIGGUM_HOME/config/worker-lifecycle.json)
#
# Returns: 0 on success, 1 on failure
lifecycle_load() {
    local spec_file="${1:-${WIGGUM_HOME:-}/config/worker-lifecycle.json}"

    if [ ! -f "$spec_file" ]; then
        echo "lifecycle_load: spec file not found: $spec_file" >&2
        return 1
    fi

    # Reset arrays for idempotent reloading (e.g., in tests)
    _LC_TRANSITIONS=()
    _LC_GUARDS=()
    _LC_KANBAN=()
    _LC_EFFECTS=()
    _LC_CHAINS=()
    _LC_STATE_TYPE=()
    _LC_VALID_STATES=()
    _LC_GUARD_FN=()
    _LC_EFFECT_FN=()
    _LC_EFFECT_ARGS=()
    _LC_TRANSITION_COUNT=0

    # Read states
    while IFS=$'\x1e' read -r state type; do
        [ -n "$state" ] || continue
        _LC_STATE_TYPE["$state"]="$type"
        _LC_VALID_STATES["$state"]=1
    done < <(jq -r '.states | to_entries[] | [.key, .value.type] | join("\u001e")' "$spec_file")

    # Read transitions (ordered - guards evaluated in spec order)
    local idx=0
    while IFS=$'\x1e' read -r event from to guard kanban effects chain; do
        [ -n "$event" ] || continue
        local key="${from}:${event}:${idx}"
        _LC_TRANSITIONS["$key"]="$to"
        [ "$guard" != "null" ] && [ -n "$guard" ] && _LC_GUARDS["$key"]="$guard"
        [ "$kanban" != "null" ] && [ -n "$kanban" ] && _LC_KANBAN["$key"]="$kanban"
        [ "$effects" != "null" ] && [ -n "$effects" ] && _LC_EFFECTS["$key"]="$effects"
        [ "$chain" != "null" ] && [ -n "$chain" ] && _LC_CHAINS["$key"]="$chain"
        ((++idx))
    done < <(jq -r '.transitions[] | [
        .event, .from, (.to // "null"),
        (.guard // "null"), (.kanban // "null"),
        ((.effects // []) | if length == 0 then "null" else join(",") end),
        (.chain // "null")
    ] | join("\u001e")' "$spec_file")
    _LC_TRANSITION_COUNT="$idx"

    # Read guards
    while IFS=$'\x1e' read -r name fn; do
        [ -n "$name" ] || continue
        _LC_GUARD_FN["$name"]="$fn"
    done < <(jq -r '.guards | to_entries[] | [.key, .value.fn] | join("\u001e")' "$spec_file")

    # Read effects
    while IFS=$'\x1e' read -r name fn args; do
        [ -n "$name" ] || continue
        _LC_EFFECT_FN["$name"]="$fn"
        _LC_EFFECT_ARGS["$name"]="$args"
    done < <(jq -r '.effects | to_entries[] | [.key, .value.fn, (.value.args | join(","))] | join("\u001e")' "$spec_file")

    _LC_LOADED=1
    return 0
}

# Check if lifecycle spec is loaded
#
# Returns: 0 if loaded, 1 if not
lifecycle_is_loaded() {
    [ "$_LC_LOADED" -eq 1 ]
}

# Get the type of a state (initial, waiting, running, transient, terminal, terminal_recoverable)
#
# Args:
#   state - State name
#
# Returns: state type on stdout, or empty if unknown
lifecycle_state_type() {
    local state="$1"
    echo "${_LC_STATE_TYPE[$state]:-}"
}

# Check if a state is valid (defined in the spec)
#
# Args:
#   state - State name
#
# Returns: 0 if valid, 1 if not
lifecycle_is_valid_state() {
    local state="$1"
    [ -n "${_LC_VALID_STATES[$state]:-}" ]
}

# Get the total number of transitions in the spec
#
# Returns: count on stdout
lifecycle_transition_count() {
    echo "$_LC_TRANSITION_COUNT"
}
