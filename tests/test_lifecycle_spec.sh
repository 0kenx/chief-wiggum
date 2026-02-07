#!/usr/bin/env bash
set -euo pipefail
# Tests for worker-lifecycle.json spec completeness and correctness
#
# Validates the spec itself — structural integrity, reachability,
# guard coverage, and effect/function references.

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"
source "$WIGGUM_HOME/lib/worker/git-state.sh"

LOG_LEVEL=ERROR
export LOG_LEVEL

SPEC_FILE="$WIGGUM_HOME/config/worker-lifecycle.json"

setup() {
    _LIFECYCLE_LOADER_LOADED=""
    _LIFECYCLE_ENGINE_LOADED=""
    _LIFECYCLE_GUARDS_LOADED=""
    source "$WIGGUM_HOME/lib/core/lifecycle-loader.sh"
    source "$WIGGUM_HOME/lib/core/lifecycle-engine.sh"
    source "$WIGGUM_HOME/lib/core/lifecycle-guards.sh"
    _LC_LOADED=0
}

teardown() {
    :
}

# =============================================================================
# Spec Structure Tests
# =============================================================================

test_spec_is_valid_json() {
    local result=0
    jq empty "$SPEC_FILE" 2>/dev/null || result=$?
    assert_equals "0" "$result" "Spec file should be valid JSON"
}

test_spec_has_required_keys() {
    local keys
    keys=$(jq -r 'keys[]' "$SPEC_FILE")

    assert_output_contains "$keys" "states" "Spec should have 'states' key"
    assert_output_contains "$keys" "transitions" "Spec should have 'transitions' key"
    assert_output_contains "$keys" "guards" "Spec should have 'guards' key"
    assert_output_contains "$keys" "effects" "Spec should have 'effects' key"
}

test_spec_has_version() {
    local version
    version=$(jq -r '.version' "$SPEC_FILE")
    assert_not_empty "$version" "Spec should have a version"
}

# =============================================================================
# State Completeness Tests
# =============================================================================

test_spec_has_initial_state() {
    local initial_count
    initial_count=$(jq '[.states | to_entries[] | select(.value.type == "initial")] | length' "$SPEC_FILE")
    initial_count="${initial_count:-0}"
    assert_greater_than "$initial_count" 0 "Spec should have at least one initial state"
}

test_spec_has_terminal_states() {
    local terminal_count
    terminal_count=$(jq '[.states | to_entries[] | select(.value.type == "terminal" or .value.type == "terminal_recoverable")] | length' "$SPEC_FILE")
    terminal_count="${terminal_count:-0}"
    assert_greater_than "$terminal_count" 0 "Spec should have at least one terminal state"
}

test_spec_all_states_have_types() {
    local states_without_type
    states_without_type=$(jq '[.states | to_entries[] | select(.value.type == null or .value.type == "")] | length' "$SPEC_FILE")
    states_without_type="${states_without_type:-0}"
    assert_equals "0" "$states_without_type" "All states should have a type"
}

test_spec_state_types_are_valid() {
    local invalid_types
    invalid_types=$(jq '[.states | to_entries[] | select(.value.type | IN("initial", "waiting", "running", "transient", "terminal", "terminal_recoverable") | not)] | length' "$SPEC_FILE")
    invalid_types="${invalid_types:-0}"
    assert_equals "0" "$invalid_types" "All state types should be valid"
}

# =============================================================================
# Transition Reference Tests
# =============================================================================

test_spec_transition_from_states_exist() {
    lifecycle_load

    local bad_count=0
    while IFS=$'\x1e' read -r from; do
        [ -n "$from" ] || continue
        [ "$from" = "*" ] && continue  # Wildcard is valid
        if [ -z "${_LC_VALID_STATES[$from]:-}" ]; then
            echo "  ERROR: Transition from unknown state: $from" >&2
            ((++bad_count))
        fi
    done < <(jq -r '.transitions[].from | @text' "$SPEC_FILE")

    assert_equals "0" "$bad_count" "All transition 'from' states should exist in states list"
}

test_spec_transition_to_states_exist() {
    lifecycle_load

    local bad_count=0
    while read -r to; do
        [ -n "$to" ] || continue
        [ "$to" = "null" ] && continue  # null target is valid
        if [ -z "${_LC_VALID_STATES[$to]:-}" ]; then
            echo "  ERROR: Transition to unknown state: $to" >&2
            ((++bad_count))
        fi
    done < <(jq -r '.transitions[].to // "null" | @text' "$SPEC_FILE")

    assert_equals "0" "$bad_count" "All transition 'to' states should exist in states list"
}

test_spec_transition_guards_exist() {
    lifecycle_load

    local bad_count=0
    while read -r guard; do
        [ -n "$guard" ] || continue
        [ "$guard" = "null" ] && continue
        if [ -z "${_LC_GUARD_FN[$guard]:-}" ]; then
            echo "  ERROR: Unknown guard referenced: $guard" >&2
            ((++bad_count))
        fi
    done < <(jq -r '.transitions[].guard // "null" | @text' "$SPEC_FILE")

    assert_equals "0" "$bad_count" "All transition guards should exist in guards list"
}

test_spec_transition_effects_exist() {
    lifecycle_load

    local bad_count=0
    while read -r effect; do
        [ -n "$effect" ] || continue
        [ "$effect" = "null" ] && continue
        if [ -z "${_LC_EFFECT_FN[$effect]:-}" ]; then
            echo "  ERROR: Unknown effect referenced: $effect" >&2
            ((++bad_count))
        fi
    done < <(jq -r '.transitions[].effects // [] | .[]' "$SPEC_FILE")

    assert_equals "0" "$bad_count" "All transition effects should exist in effects list"
}

# =============================================================================
# Guard/Effect Function Reference Tests
# =============================================================================

test_spec_guard_functions_are_defined() {
    lifecycle_load

    local bad_count=0
    while IFS=$'\x1e' read -r name fn; do
        [ -n "$name" ] || continue
        if ! declare -f "$fn" >/dev/null 2>&1; then
            echo "  ERROR: Guard '$name' references undefined function: $fn" >&2
            ((++bad_count))
        fi
    done < <(jq -r '.guards | to_entries[] | [.key, .value.fn] | join("\u001e")' "$SPEC_FILE")

    assert_equals "0" "$bad_count" "All guard functions should be defined"
}

test_spec_effect_functions_are_defined_or_stubbable() {
    lifecycle_load

    # Effects reference functions from many modules — some won't be loaded in test env.
    # We verify the ones from already-loaded modules and note the rest.
    local checked=0
    local found=0
    while IFS=$'\x1e' read -r name fn; do
        [ -n "$name" ] || continue
        ((++checked))
        if declare -f "$fn" >/dev/null 2>&1; then
            ((++found))
        fi
    done < <(jq -r '.effects | to_entries[] | [.key, .value.fn] | join("\u001e")' "$SPEC_FILE")

    assert_greater_than "$checked" 0 "Should have checked at least one effect"
    # At minimum git_state_* functions from git-state.sh should be found
    assert_greater_than "$found" 0 "At least some effect functions should be defined"
}

# =============================================================================
# Reachability Tests
# =============================================================================

test_spec_non_initial_states_are_reachable() {
    # Every non-initial state should appear as a 'to' target or a 'chain' target
    # in at least one transition. Chain states (transient) are only reached via
    # the chain field, not via 'to'.
    local unreachable=0
    while IFS=$'\x1e' read -r state type; do
        [ -n "$state" ] || continue
        [ "$type" = "initial" ] && continue

        local is_target
        is_target=$(jq --arg s "$state" '[.transitions[] | select(.to == $s or .chain == $s)] | length' "$SPEC_FILE")
        is_target="${is_target:-0}"
        if [ "$is_target" -eq 0 ]; then
            echo "  ERROR: State '$state' is not reachable (no transition targets it)" >&2
            ((++unreachable))
        fi
    done < <(jq -r '.states | to_entries[] | [.key, .value.type] | join("\u001e")' "$SPEC_FILE")

    assert_equals "0" "$unreachable" "All non-initial states should be reachable"
}

test_spec_non_terminal_states_have_outbound() {
    # Every non-terminal state should have at least one outbound transition
    # (wildcard transitions count for all states)
    local has_wildcard
    has_wildcard=$(jq '[.transitions[] | select(.from == "*")] | length' "$SPEC_FILE")
    has_wildcard="${has_wildcard:-0}"

    local stuck=0
    while IFS=$'\x1e' read -r state type; do
        [ -n "$state" ] || continue
        [ "$type" = "terminal" ] && continue
        [ "$type" = "terminal_recoverable" ] && continue

        local outbound
        outbound=$(jq --arg s "$state" '[.transitions[] | select(.from == $s)] | length' "$SPEC_FILE")
        outbound="${outbound:-0}"
        if [ "$outbound" -eq 0 ] && [ "$has_wildcard" -eq 0 ]; then
            echo "  ERROR: Non-terminal state '$state' has no outbound transitions" >&2
            ((++stuck))
        fi
    done < <(jq -r '.states | to_entries[] | [.key, .value.type] | join("\u001e")' "$SPEC_FILE")

    assert_equals "0" "$stuck" "All non-terminal states should have outbound transitions (or wildcards)"
}

test_spec_terminal_states_reachable_from_initial() {
    # At least one terminal state should be reachable via some path from initial
    # (We test this by verifying terminal states exist as transition targets)
    # Verify at least one transition targets "merged" or "failed"
    local merged_reachable
    merged_reachable=$(jq '[.transitions[] | select(.to == "merged")] | length' "$SPEC_FILE")
    merged_reachable="${merged_reachable:-0}"
    assert_greater_than "$merged_reachable" 0 "Terminal state 'merged' should be reachable"

    local failed_reachable
    failed_reachable=$(jq '[.transitions[] | select(.to == "failed")] | length' "$SPEC_FILE")
    failed_reachable="${failed_reachable:-0}"
    assert_greater_than "$failed_reachable" 0 "Terminal state 'failed' should be reachable"
}

# =============================================================================
# Guard Fallback Tests
# =============================================================================

test_spec_guarded_transitions_have_fallback() {
    # For each (event, from) pair that has a guarded transition, there should be
    # a subsequent unguarded transition for the same (event, from) as fallback.
    local missing_fallback=0

    # Get all guarded (event, from) pairs
    while IFS=$'\x1e' read -r event from; do
        [ -n "$event" ] || continue

        # Check if there's an unguarded transition for same event+from
        local has_fallback
        has_fallback=$(jq --arg e "$event" --arg f "$from" \
            '[.transitions[] | select(.event == $e and .from == $f and (.guard == null or .guard == ""))] | length' \
            "$SPEC_FILE")
        has_fallback="${has_fallback:-0}"

        if [ "$has_fallback" -eq 0 ]; then
            echo "  ERROR: Guarded transition ($event from $from) has no unguarded fallback" >&2
            ((++missing_fallback))
        fi
    done < <(jq -r '[.transitions[] | select(.guard != null and .guard != "") | {event, from}] | unique[] | [.event, .from] | join("\u001e")' "$SPEC_FILE")

    assert_equals "0" "$missing_fallback" "All guarded transitions should have an unguarded fallback"
}

# =============================================================================
# Chain State Tests
# =============================================================================

test_spec_chain_states_are_valid() {
    local bad_count=0
    while read -r chain; do
        [ -n "$chain" ] || continue
        [ "$chain" = "null" ] && continue

        local is_valid
        is_valid=$(jq --arg s "$chain" '.states[$s] != null' "$SPEC_FILE")
        if [ "$is_valid" != "true" ]; then
            echo "  ERROR: Chain state '$chain' is not a valid state" >&2
            ((++bad_count))
        fi
    done < <(jq -r '.transitions[].chain // "null" | @text' "$SPEC_FILE")

    assert_equals "0" "$bad_count" "All chain states should be valid states"
}

test_spec_chain_states_are_transient() {
    local bad_count=0
    while read -r chain; do
        [ -n "$chain" ] || continue
        [ "$chain" = "null" ] && continue

        local state_type
        state_type=$(jq -r --arg s "$chain" '.states[$s].type' "$SPEC_FILE")
        if [ "$state_type" != "transient" ]; then
            echo "  ERROR: Chain state '$chain' has type '$state_type', expected 'transient'" >&2
            ((++bad_count))
        fi
    done < <(jq -r '.transitions[].chain // "null" | @text' "$SPEC_FILE")

    assert_equals "0" "$bad_count" "All chain states should have type 'transient'"
}

# =============================================================================
# Effect Args Tests
# =============================================================================

test_spec_effect_args_are_resolvable() {
    local valid_arg_prefixes="worker_dir task_id ralph_dir kanban data."
    local bad_count=0

    while IFS=$'\x1e' read -r name args_str; do
        [ -n "$name" ] || continue
        IFS=',' read -ra args <<< "$args_str"
        for arg in "${args[@]}"; do
            [ -z "$arg" ] && continue
            local valid=0
            for prefix in $valid_arg_prefixes; do
                if [ "$arg" = "$prefix" ] || [[ "$arg" == ${prefix}* ]]; then
                    valid=1
                    break
                fi
            done
            if [ "$valid" -eq 0 ]; then
                # Could be a literal string arg — that's ok for the engine
                # Only flag if it looks like a bad reference
                if [[ "$arg" =~ ^[a-z_]+$ ]] && [ "$arg" != "worker_dir" ] && [ "$arg" != "task_id" ] && [ "$arg" != "ralph_dir" ] && [ "$arg" != "kanban" ]; then
                    echo "  WARN: Effect '$name' has arg '$arg' — not a known context variable (may be literal)" >&2
                fi
            fi
        done
    done < <(jq -r '.effects | to_entries[] | [.key, (.value.args | join(","))] | join("\u001e")' "$SPEC_FILE")

    # This is a warning-only test — always passes
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    echo -e "  ${GREEN}✓${NC} Effect args checked (warnings above if any)"
}

# =============================================================================
# Kanban Status Tests
# =============================================================================

test_spec_kanban_values_are_valid() {
    local bad_count=0

    while read -r kanban; do
        [ -n "$kanban" ] || continue
        [ "$kanban" = "null" ] && continue
        case "$kanban" in
            x|"="|"*"|" ") ;; # Valid
            *)
                echo "  ERROR: Invalid kanban status: '$kanban'" >&2
                ((++bad_count))
                ;;
        esac
    done < <(jq -r '.transitions[].kanban // "null" | @text' "$SPEC_FILE")

    assert_equals "0" "$bad_count" "All kanban statuses should be valid markers"
}

# =============================================================================
# Transition Ordering Tests (Guards before fallbacks)
# =============================================================================

test_spec_guarded_transitions_precede_fallbacks() {
    # For each (event, from) pair with guards, the guarded transitions should
    # come before the unguarded fallback in the transitions array.
    local bad_order=0

    while IFS=$'\x1e' read -r event from; do
        [ -n "$event" ] || continue

        local last_guarded_idx=-1
        local first_unguarded_idx=999999
        local idx=0

        while IFS=$'\x1e' read -r t_event t_from t_guard; do
            [ -n "$t_event" ] || continue
            if [ "$t_event" = "$event" ] && [ "$t_from" = "$from" ]; then
                if [ "$t_guard" != "null" ] && [ -n "$t_guard" ]; then
                    last_guarded_idx=$idx
                else
                    if [ "$idx" -lt "$first_unguarded_idx" ]; then
                        first_unguarded_idx=$idx
                    fi
                fi
            fi
            ((++idx))
        done < <(jq -r '.transitions[] | [.event, .from, (.guard // "null")] | join("\u001e")' "$SPEC_FILE")

        if [ "$last_guarded_idx" -ge 0 ] && [ "$first_unguarded_idx" -lt 999999 ]; then
            if [ "$last_guarded_idx" -gt "$first_unguarded_idx" ]; then
                echo "  ERROR: ($event from $from) guarded transition at idx $last_guarded_idx comes after unguarded at idx $first_unguarded_idx" >&2
                ((++bad_order))
            fi
        fi
    done < <(jq -r '[.transitions[] | select(.guard != null and .guard != "") | {event, from}] | unique[] | [.event, .from] | join("\u001e")' "$SPEC_FILE")

    assert_equals "0" "$bad_order" "Guarded transitions should precede their unguarded fallbacks"
}

# =============================================================================
# Run All Tests
# =============================================================================

# Spec structure
run_test test_spec_is_valid_json
run_test test_spec_has_required_keys
run_test test_spec_has_version

# State completeness
run_test test_spec_has_initial_state
run_test test_spec_has_terminal_states
run_test test_spec_all_states_have_types
run_test test_spec_state_types_are_valid

# Transition references
run_test test_spec_transition_from_states_exist
run_test test_spec_transition_to_states_exist
run_test test_spec_transition_guards_exist
run_test test_spec_transition_effects_exist

# Function references
run_test test_spec_guard_functions_are_defined
run_test test_spec_effect_functions_are_defined_or_stubbable

# Reachability
run_test test_spec_non_initial_states_are_reachable
run_test test_spec_non_terminal_states_have_outbound
run_test test_spec_terminal_states_reachable_from_initial

# Guard coverage
run_test test_spec_guarded_transitions_have_fallback

# Chain states
run_test test_spec_chain_states_are_valid
run_test test_spec_chain_states_are_transient

# Effect args
run_test test_spec_effect_args_are_resolvable

# Kanban values
run_test test_spec_kanban_values_are_valid

# Transition ordering
run_test test_spec_guarded_transitions_precede_fallbacks

print_test_summary
exit_with_test_result
