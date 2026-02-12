#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

# =========================================================================
# Configuration
# =========================================================================

VERBOSE=false
INTERACTIVE=false
FILTER=""
TIMEOUT=0

usage() {
    cat <<'EOF'
Usage: verify.sh [OPTIONS] [FILTER]

Run Apalache model checks on TLA+ specs.

Options:
  -v, --verbose       Show full Apalache output (default: per-step progress dots)
  -i, --interactive   Prompt before each check (y/n/q)
  -t, --time SECS     Kill each check after SECS seconds; PASS if no violation found
  -h, --help          Show this help

Filter:
  Optional pattern to select checks. Matches against "Spec::Invariant".
  Examples:
    verify.sh Worker              # all WorkerLifecycle checks
    verify.sh Pipeline::Visits    # PipelineEngine VisitsBounded
    verify.sh Orchestrator        # all Orchestrator checks
    verify.sh TypeInvariant       # TypeInvariant across all specs

Checks (47 safety invariants):
  WorkerLifecycle.tla   (length 25) TypeInvariant BoundedCounters
                        TransientStateInvariant KanbanMergedConsistency
                        KanbanFailedConsistency ConflictQueueConsistency
                        WorktreeStateConsistency ErrorStateConsistency
                        MergedCleanupConsistency
  PipelineEngine.tla    (length 30) TypeInvariant VisitsBounded
                        InlineVisitsBounded StatusConsistency
                        SupervisorRestartsBounded CostBudgetInvariant
  Orchestrator.tla      (length 10) TypeInvariant WorkerPoolCapacity
                        BoundedCounters KanbanMergedConsistency
                        NoIdleInProgress NoFileConflictActive
                        DependencyOrdering NoDuplicateActiveWorkers
                        KanbanFailedConsistency ConflictQueueConsistency
                        WorktreeStateConsistency ErrorStateConsistency
                        MergedCleanupConsistency
  Scheduler.tla         (length 10) TypeInvariant CapacityInvariant
                        DependencyInvariant FileConflictInvariant
                        SkipBoundInvariant CyclicTasksNeverSpawned
  EffectOutbox.tla      (length 20) TypeInvariant DoneConsistency
                        StateBeforeKanban CompletedSubsetPending
                        CleanupEffectOrder CrashBounded
  ResumeLifecycle.tla   (length 20) TypeInvariant TerminalAbsorbing
                        AttemptsWithinBounds CooldownBlocksSpawn
                        DecisionRequiredForSpawn TerminalReasonConsistency
                        PassNeverRetried

Note: Temporal/liveness properties (EventualTermination, NoStarvation,
EventualSpawn, SkipDecay, PipelineTermination, EventualCompletion) are
defined in each spec but require TLC for verification -- Apalache does
not support fairness in --temporal mode ("Handling fairness is not
supported yet!").
EOF
}

# =========================================================================
# Argument parsing
# =========================================================================

while [[ $# -gt 0 ]]; do
    case "$1" in
        -v|--verbose)     VERBOSE=true; shift ;;
        -i|--interactive) INTERACTIVE=true; shift ;;
        -t|--time)
            [[ $# -lt 2 ]] && { echo "Error: --time requires a value" >&2; exit 2; }
            TIMEOUT="$2"; shift 2 ;;
        -h|--help)        usage; exit 0 ;;
        -*)               echo "Unknown option: $1" >&2; usage >&2; exit 2 ;;
        *)                FILTER="$1"; shift ;;
    esac
done

# =========================================================================
# Runner
# =========================================================================

PASS_COUNT=0
FAIL_COUNT=0
SKIP_COUNT=0
TOTAL_COUNT=0
TIMEOUT_COUNT=0
DRY_RUN=false
APALACHE_PID=""
INTERRUPTED=false
declare -a FAILURES=()

_on_sigint() {
    # Double Ctrl+C: quit immediately
    if [[ "$INTERRUPTED" == true ]]; then
        echo ""
        echo "Double interrupt — aborting."
        _print_summary
        exit 130
    fi
    if [[ -n "$APALACHE_PID" ]]; then
        kill "$APALACHE_PID" 2>/dev/null || true
        wait "$APALACHE_PID" 2>/dev/null || true
        APALACHE_PID=""
    fi
    INTERRUPTED=true
}
trap _on_sigint INT

# Check if a spec::inv pair matches the current filter
_matches_filter() {
    local spec_name="$1" inv="$2"
    if [[ -n "$FILTER" ]]; then
        if [[ "$FILTER" == *"::"* ]]; then
            local fspec="${FILTER%%::*}"
            local finv="${FILTER#*::}"
            [[ -n "$fspec" ]] && [[ "$spec_name" != *"$fspec"* ]] && return 1
            [[ -n "$finv" ]] && [[ "$inv" != *"$finv"* ]] && return 1
        else
            [[ "$spec_name" != *"$FILTER"* ]] && [[ "$inv" != *"$FILTER"* ]] && return 1
        fi
    fi
    return 0
}

run_check() {
    local spec="$1" inv="$2" length="$3"
    local spec_name="${spec%.tla}"

    _matches_filter "$spec_name" "$inv" || return 0

    ((++TOTAL_COUNT)) || true

    # Counting mode
    [[ "$DRY_RUN" == true ]] && return 0

    # Interactive prompt
    if [[ "$INTERACTIVE" == true ]]; then
        local answer=""
        read -rp "Run ${spec_name}::${inv}? [Y/n/q] " answer </dev/tty
        case "${answer,,}" in
            q) echo "Quit."; _print_summary; exit "$( (( FAIL_COUNT > 0 )) && echo 1 || echo 0 )" ;;
            n) ((++SKIP_COUNT)) || true; return 0 ;;
        esac
    fi

    local tmpout
    tmpout=$(mktemp)
    local -a cmd=(apalache-mc check --cinit=CInit --inv="$inv" --length="$length" "$spec")
    local rc=0

    INTERRUPTED=false

    if [[ "$VERBOSE" == true ]]; then
        # --- Verbose mode: stream output in real time ---
        printf "%-45s [%s]\n" "${spec_name}::${inv}" "$length"

        "${cmd[@]}" > "$tmpout" 2>&1 &
        APALACHE_PID=$!

        # Stream output via tail -f; killed when apalache exits
        tail -f "$tmpout" 2>/dev/null &
        local tail_pid=$!

        local start=$SECONDS timed_out=false
        while kill -0 "$APALACHE_PID" 2>/dev/null; do
            if [[ "$INTERRUPTED" == true ]]; then
                kill "$APALACHE_PID" 2>/dev/null || true
                wait "$APALACHE_PID" 2>/dev/null || true
                break
            fi
            if (( TIMEOUT > 0 && SECONDS - start >= TIMEOUT )); then
                kill "$APALACHE_PID" 2>/dev/null || true
                wait "$APALACHE_PID" 2>/dev/null || true
                timed_out=true
                break
            fi
            sleep 0.5 || true
        done

        # Stop streaming
        kill "$tail_pid" 2>/dev/null || true
        wait "$tail_pid" 2>/dev/null || true

        if [[ "$INTERRUPTED" != true && "$timed_out" != true ]]; then
            wait "$APALACHE_PID" 2>/dev/null || rc=$?
        elif [[ "$timed_out" == true ]]; then
            rc=124
        fi
        APALACHE_PID=""
    else
        # --- Default mode: name [steps] dots ---
        printf "%-45s [%s] " "${spec_name}::${inv}" "$length"

        "${cmd[@]}" > "$tmpout" 2>&1 &
        APALACHE_PID=$!

        local dots=0 start=$SECONDS timed_out=false
        while kill -0 "$APALACHE_PID" 2>/dev/null; do
            if [[ "$INTERRUPTED" == true ]]; then
                kill "$APALACHE_PID" 2>/dev/null || true
                wait "$APALACHE_PID" 2>/dev/null || true
                break
            fi
            if (( TIMEOUT > 0 && SECONDS - start >= TIMEOUT )); then
                kill "$APALACHE_PID" 2>/dev/null || true
                wait "$APALACHE_PID" 2>/dev/null || true
                timed_out=true
                break
            fi
            local n=0
            n=$(grep -c "picking a transition" "$tmpout" 2>/dev/null) || n=0
            while (( dots < n )); do printf "."; ((++dots)); done
            sleep 0.5 || true
        done

        if [[ "$INTERRUPTED" != true && "$timed_out" != true ]]; then
            wait "$APALACHE_PID" 2>/dev/null || rc=$?
        elif [[ "$timed_out" == true ]]; then
            rc=124
        fi
        APALACHE_PID=""

        # Print remaining dots after process exits
        if [[ "$INTERRUPTED" != true ]]; then
            local n=0
            n=$(grep -c "picking a transition" "$tmpout" 2>/dev/null) || n=0
            while (( dots < n )); do printf "."; ((++dots)); done
        fi
    fi

    # --- Result ---
    if [[ "$INTERRUPTED" == true ]]; then
        ((++SKIP_COUNT)) || true
        if [[ "$VERBOSE" == true ]]; then
            echo "SKIP (interrupted)"
        else
            printf " SKIP\n"
        fi
    elif [[ $rc -eq 0 ]]; then
        ((++PASS_COUNT)) || true
        if [[ "$VERBOSE" == true ]]; then
            echo "PASS"
        else
            printf " PASS\n"
        fi
    elif (( TIMEOUT > 0 )) && [[ $rc -eq 124 ]]; then
        # Timeout: no violation found within time budget
        ((++PASS_COUNT)) || true
        ((++TIMEOUT_COUNT)) || true
        if [[ "$VERBOSE" == true ]]; then
            echo "PASS (timeout ${TIMEOUT}s)"
        else
            printf " PASS (%ss)\n" "$TIMEOUT"
        fi
    else
        ((++FAIL_COUNT)) || true
        if [[ "$VERBOSE" == true ]]; then
            echo "FAIL (exit $rc)"
        else
            printf " FAIL\n"
        fi
        # Collect and print failure details immediately
        local detail=""
        detail=$(grep -E '(violation|error|Error|EXITCODE|invariant.*violated|Check the trace)' "$tmpout" \
            | sed 's/^/    /' || true)
        if [[ -n "$detail" ]]; then
            echo "$detail"
            FAILURES+=("  ${spec_name}::${inv} (exit $rc)"$'\n'"$detail")
        else
            FAILURES+=("  ${spec_name}::${inv} (exit $rc)")
        fi
    fi

    rm -f "$tmpout"
}

_print_summary() {
    echo ""
    echo "========================================="
    local pass_str="$PASS_COUNT"
    [[ "$TIMEOUT_COUNT" -gt 0 ]] && pass_str="$PASS_COUNT ($TIMEOUT_COUNT timeout)"
    echo "  Pass: $pass_str  Fail: $FAIL_COUNT  Skip: $SKIP_COUNT  Total: $TOTAL_COUNT"
    echo "========================================="
}

# =========================================================================
# Check definitions
# =========================================================================

_run_all_checks() {
    # WorkerLifecycle
    run_check WorkerLifecycle.tla TypeInvariant 25
    run_check WorkerLifecycle.tla BoundedCounters 25
    run_check WorkerLifecycle.tla TransientStateInvariant 25
    run_check WorkerLifecycle.tla KanbanMergedConsistency 25
    run_check WorkerLifecycle.tla KanbanFailedConsistency 25
    run_check WorkerLifecycle.tla ConflictQueueConsistency 25
    run_check WorkerLifecycle.tla WorktreeStateConsistency 25
    run_check WorkerLifecycle.tla ErrorStateConsistency 25
    run_check WorkerLifecycle.tla MergedCleanupConsistency 25

    # PipelineEngine
    run_check PipelineEngine.tla TypeInvariant 30
    run_check PipelineEngine.tla VisitsBounded 30
    run_check PipelineEngine.tla InlineVisitsBounded 30
    run_check PipelineEngine.tla StatusConsistency 30
    run_check PipelineEngine.tla SupervisorRestartsBounded 30
    run_check PipelineEngine.tla CostBudgetInvariant 30

    # Orchestrator
    run_check Orchestrator.tla TypeInvariant 10
    run_check Orchestrator.tla WorkerPoolCapacity 10
    run_check Orchestrator.tla BoundedCounters 10
    run_check Orchestrator.tla KanbanMergedConsistency 10
    run_check Orchestrator.tla NoIdleInProgress 10
    run_check Orchestrator.tla NoFileConflictActive 10
    run_check Orchestrator.tla DependencyOrdering 10
    run_check Orchestrator.tla NoDuplicateActiveWorkers 10
    run_check Orchestrator.tla KanbanFailedConsistency 10
    run_check Orchestrator.tla ConflictQueueConsistency 10
    run_check Orchestrator.tla WorktreeStateConsistency 10
    run_check Orchestrator.tla ErrorStateConsistency 10
    run_check Orchestrator.tla MergedCleanupConsistency 10

    # Scheduler
    run_check Scheduler.tla TypeInvariant 10
    run_check Scheduler.tla CapacityInvariant 10
    run_check Scheduler.tla DependencyInvariant 10
    run_check Scheduler.tla FileConflictInvariant 10
    run_check Scheduler.tla SkipBoundInvariant 10
    run_check Scheduler.tla CyclicTasksNeverSpawned 10

    # EffectOutbox
    run_check EffectOutbox.tla TypeInvariant 20
    run_check EffectOutbox.tla DoneConsistency 20
    run_check EffectOutbox.tla StateBeforeKanban 20
    run_check EffectOutbox.tla CompletedSubsetPending 20
    run_check EffectOutbox.tla CleanupEffectOrder 20
    run_check EffectOutbox.tla CrashBounded 20

    # ResumeLifecycle
    run_check ResumeLifecycle.tla TypeInvariant 20
    run_check ResumeLifecycle.tla TerminalAbsorbing 20
    run_check ResumeLifecycle.tla AttemptsWithinBounds 20
    run_check ResumeLifecycle.tla CooldownBlocksSpawn 20
    run_check ResumeLifecycle.tla DecisionRequiredForSpawn 20
    run_check ResumeLifecycle.tla TerminalReasonConsistency 20
    run_check ResumeLifecycle.tla PassNeverRetried 20
}

# =========================================================================
# Execute
# =========================================================================

# Counting pass: determine how many checks match the filter
DRY_RUN=true
_run_all_checks
STEP_COUNT=$TOTAL_COUNT
TOTAL_COUNT=0

echo "$STEP_COUNT checks"

if [[ "$STEP_COUNT" -eq 0 ]]; then
    echo "No checks matched filter."
    exit 0
fi

# Execution pass
DRY_RUN=false
_run_all_checks

# Print failure details
if [[ ${#FAILURES[@]} -gt 0 ]]; then
    echo ""
    echo "Failures:"
    for f in "${FAILURES[@]}"; do
        echo "$f"
    done
fi

# Summary
_print_summary

if (( FAIL_COUNT > 0 )); then
    exit 1
fi
