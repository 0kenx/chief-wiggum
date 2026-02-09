#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

# =========================================================================
# Configuration
# =========================================================================

VERBOSE=false
INTERACTIVE=false
FILTER=""

usage() {
    cat <<'EOF'
Usage: verify.sh [OPTIONS] [FILTER]

Run Apalache model checks on TLA+ specs.

Options:
  -v, --verbose       Show full Apalache output (default: errors only)
  -i, --interactive   Prompt before each check (y/n/q)
  -h, --help          Show this help

Filter:
  Optional pattern to select checks. Matches against "Spec::Invariant".
  Examples:
    verify.sh Worker              # all WorkerLifecycle checks
    verify.sh Pipeline::Visits    # PipelineEngine VisitsBounded
    verify.sh Orchestrator        # all Orchestrator checks
    verify.sh TypeInvariant       # TypeInvariant across all specs

Checks (16 total):
  WorkerLifecycle.tla   TypeInvariant BoundedCounters TransientStateInvariant
                        KanbanMergedConsistency KanbanFailedConsistency
  PipelineEngine.tla    TypeInvariant VisitsBounded InlineVisitsBounded
                        StatusConsistency
  Orchestrator.tla      TypeInvariant WorkerPoolCapacity BoundedCounters
                        KanbanMergedConsistency NoIdleInProgress
                        NoFileConflictActive DependencyOrdering
EOF
}

# =========================================================================
# Argument parsing
# =========================================================================

while [[ $# -gt 0 ]]; do
    case "$1" in
        -v|--verbose)     VERBOSE=true; shift ;;
        -i|--interactive) INTERACTIVE=true; shift ;;
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

run_check() {
    local spec="$1" inv="$2" length="$3"
    local label="${spec}::${inv}"

    # Filter
    if [[ -n "$FILTER" ]] && [[ "$label" != *"$FILTER"* ]]; then
        return 0
    fi

    ((++TOTAL_COUNT)) || true

    # Interactive prompt
    if [[ "$INTERACTIVE" == true ]]; then
        local answer=""
        read -rp "Run $label? [Y/n/q] " answer </dev/tty
        case "${answer,,}" in
            q) echo "Quit."; _print_summary; exit "$( (( FAIL_COUNT > 0 )) && echo 1 || echo 0 )" ;;
            n) ((++SKIP_COUNT)) || true; return 0 ;;
        esac
    fi

    printf "%-55s " "$label"

    local tmpout
    tmpout=$(mktemp)

    local rc=0
    apalache-mc check --cinit=CInit --inv="$inv" --length="$length" "$spec" \
        > "$tmpout" 2>&1 || rc=$?

    if [[ $rc -eq 0 ]]; then
        echo "PASS"
        ((++PASS_COUNT)) || true
    else
        echo "FAIL (exit $rc)"
        ((++FAIL_COUNT)) || true

        if [[ "$VERBOSE" == true ]]; then
            cat "$tmpout"
        else
            # Show only error-relevant lines
            grep -E '(violation|error|Error|EXITCODE|invariant.*violated|Check the trace)' "$tmpout" \
                | sed 's/^/  /'
        fi
        echo ""
    fi

    rm -f "$tmpout"
}

_print_summary() {
    echo ""
    echo "========================================="
    echo "  Pass: $PASS_COUNT  Fail: $FAIL_COUNT  Skip: $SKIP_COUNT  Total: $TOTAL_COUNT"
    echo "========================================="
}

# =========================================================================
# Checks
# =========================================================================

# WorkerLifecycle
run_check WorkerLifecycle.tla TypeInvariant 20
run_check WorkerLifecycle.tla BoundedCounters 20
run_check WorkerLifecycle.tla TransientStateInvariant 20
run_check WorkerLifecycle.tla KanbanMergedConsistency 20
run_check WorkerLifecycle.tla KanbanFailedConsistency 20

# PipelineEngine
run_check PipelineEngine.tla TypeInvariant 30
run_check PipelineEngine.tla VisitsBounded 30
run_check PipelineEngine.tla InlineVisitsBounded 30
run_check PipelineEngine.tla StatusConsistency 30

# Orchestrator
run_check Orchestrator.tla TypeInvariant 20
run_check Orchestrator.tla WorkerPoolCapacity 20
run_check Orchestrator.tla BoundedCounters 20
run_check Orchestrator.tla KanbanMergedConsistency 20
run_check Orchestrator.tla NoIdleInProgress 20
run_check Orchestrator.tla NoFileConflictActive 20
run_check Orchestrator.tla DependencyOrdering 20

# =========================================================================
# Summary
# =========================================================================

_print_summary

if (( FAIL_COUNT > 0 )); then
    exit 1
fi
