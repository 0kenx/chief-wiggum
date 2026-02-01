#!/usr/bin/env bash
# =============================================================================
# arg-parser.sh - Parse wiggum-run CLI arguments
#
# Extracted from wiggum-run main() to keep the orchestrator script lean.
#
# Provides:
#   _parse_run_args()  - Parse CLI arguments, set global config variables
# =============================================================================
set -euo pipefail

[ -n "${_ORCHESTRATOR_ARG_PARSER_LOADED:-}" ] && return 0
_ORCHESTRATOR_ARG_PARSER_LOADED=1

# Parse wiggum run CLI arguments
#
# Sets global variables:
#   MAX_WORKERS, MAX_ITERATIONS, MAX_TURNS, WIGGUM_RUN_MODE,
#   WIGGUM_PLAN_MODE, WIGGUM_SMART_MODE, WIGGUM_PIPELINE,
#   FIX_WORKER_LIMIT, FORCE_LOCK
#
# Args:
#   "$@" - Command line arguments (after verbose flags removed)
_parse_run_args() {
    while [[ $# -gt 0 ]]; do
        case "$1" in
            plan)
                export WIGGUM_PLAN_MODE=true
                shift
                ;;
            --smart)
                export WIGGUM_SMART_MODE=true
                shift
                ;;
            --fix-only)
                WIGGUM_RUN_MODE="fix-only"
                shift
                ;;
            --merge-only)
                WIGGUM_RUN_MODE="merge-only"
                shift
                ;;
            --resume-only)
                WIGGUM_RUN_MODE="resume-only"
                shift
                ;;
            --max-workers)
                if [[ -z "${2:-}" ]] || [[ "${2:-}" =~ ^- ]]; then
                    echo "Error: --max-workers requires a number argument"
                    exit $EXIT_USAGE
                fi
                # shellcheck disable=SC2034
                MAX_WORKERS="$2"
                shift 2
                ;;
            --max-iters)
                if [[ -z "${2:-}" ]] || [[ "${2:-}" =~ ^- ]]; then
                    echo "Error: --max-iters requires a number argument"
                    exit $EXIT_USAGE
                fi
                # shellcheck disable=SC2034
                MAX_ITERATIONS="$2"
                shift 2
                ;;
            --max-turns)
                if [[ -z "${2:-}" ]] || [[ "${2:-}" =~ ^- ]]; then
                    echo "Error: --max-turns requires a number argument"
                    exit $EXIT_USAGE
                fi
                # shellcheck disable=SC2034
                MAX_TURNS="$2"
                shift 2
                ;;
            --fix-agents)
                if [[ -z "${2:-}" ]] || [[ "${2:-}" =~ ^- ]]; then
                    echo "Error: --fix-agents requires a number argument"
                    exit $EXIT_USAGE
                fi
                # shellcheck disable=SC2034
                FIX_WORKER_LIMIT="$2"
                shift 2
                ;;
            --pipeline)
                if [[ -z "${2:-}" ]] || [[ "${2:-}" =~ ^- ]]; then
                    echo "Error: --pipeline requires a name argument"
                    exit $EXIT_USAGE
                fi
                export WIGGUM_PIPELINE="$2"
                shift 2
                ;;
            --force)
                # shellcheck disable=SC2034
                FORCE_LOCK=true
                shift
                ;;
            -h|--help)
                show_help
                exit $EXIT_OK
                ;;
            -*)
                echo "Unknown option: $1"
                echo ""
                show_help
                exit $EXIT_USAGE
                ;;
            *)
                echo "Unknown argument: $1"
                echo ""
                show_help
                exit $EXIT_USAGE
                ;;
        esac
    done

    # Validate mutually exclusive options
    if [[ "$WIGGUM_RUN_MODE" != "default" && "${WIGGUM_PLAN_MODE:-false}" == "true" ]]; then
        echo "Error: --${WIGGUM_RUN_MODE} cannot be combined with plan mode"
        exit $EXIT_USAGE
    fi
    if [[ "${WIGGUM_SMART_MODE:-false}" == "true" ]]; then
        if [[ "${WIGGUM_PLAN_MODE:-false}" == "true" ]]; then
            echo "Error: --smart cannot be combined with plan mode"
            exit $EXIT_USAGE
        fi
        if [[ -n "${WIGGUM_PIPELINE:-}" ]]; then
            echo "Error: --smart cannot be combined with --pipeline"
            exit $EXIT_USAGE
        fi
        if [[ "$WIGGUM_RUN_MODE" != "default" ]]; then
            echo "Error: --smart cannot be combined with --${WIGGUM_RUN_MODE}"
            exit $EXIT_USAGE
        fi
    fi
}
