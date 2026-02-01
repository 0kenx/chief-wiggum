#!/usr/bin/env bash
# run-all-tests.sh - Run all Chief Wiggum test suites
#
# Usage:
#   ./tests/run-all-tests.sh           # Run all tests
#   ./tests/run-all-tests.sh --quick   # Skip slow tests
#   ./tests/run-all-tests.sh --verbose # Show detailed output
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Options
QUICK_MODE=false
VERBOSE=false
SPECIFIC_SUITE=""

# Parse arguments
while [[ $# -gt 0 ]]; do
    case "$1" in
        --quick|-q)
            QUICK_MODE=true
            shift
            ;;
        --verbose|-v)
            VERBOSE=true
            shift
            ;;
        --suite|-s)
            if [[ -z "${2:-}" ]]; then
                echo "Error: --suite requires a suite name argument"
                exit 1
            fi
            SPECIFIC_SUITE="$2"
            shift 2
            ;;
        --help|-h)
            echo "Usage: $0 [options]"
            echo ""
            echo "Options:"
            echo "  --quick, -q     Skip slow tests"
            echo "  --verbose, -v   Show detailed output"
            echo "  --suite, -s     Run specific suite (syntax, integration, e2e, tui)"
            echo "  --help, -h      Show this help"
            exit 0
            ;;
        *)
            echo "Unknown option: $1"
            exit 1
            ;;
    esac
done

# Results tracking
TOTAL_SUITES=0
PASSED_SUITES=0
FAILED_SUITES=0
declare -a FAILED_SUITE_NAMES=()

echo "========================================"
echo "   Chief Wiggum Test Suite Runner"
echo "========================================"
echo ""
echo "Project: $PROJECT_ROOT"
echo "Date: $(date)"
echo ""

# Run a test suite
run_suite() {
    local name="$1"
    local script="$2"

    TOTAL_SUITES=$((TOTAL_SUITES + 1))

    if [ ! -f "$script" ]; then
        if [ "$VERBOSE" = true ]; then
            echo "----------------------------------------"
            echo "Running: $name"
            echo "----------------------------------------"
            echo "ERROR: Test script not found: $script"
            echo ""
        else
            printf "  %-24s SKIP (not found)\n" "$name:"
        fi
        FAILED_SUITES=$((FAILED_SUITES + 1))
        FAILED_SUITE_NAMES+=("$name (not found)")
        return 1
    fi

    chmod +x "$script"

    local start_time end_time duration
    start_time=$(date +%s)

    if [ "$VERBOSE" = true ]; then
        echo "----------------------------------------"
        echo "Running: $name"
        echo "----------------------------------------"

        if "$script"; then
            PASSED_SUITES=$((PASSED_SUITES + 1))
        else
            FAILED_SUITES=$((FAILED_SUITES + 1))
            FAILED_SUITE_NAMES+=("$name")
        fi

        end_time=$(date +%s)
        duration=$((end_time - start_time))
        echo "Duration: ${duration}s"
        echo ""
    else
        printf "  %-24s " "$name:"

        local output_file
        output_file=$(mktemp)
        local exit_code=0

        # Run script in background with output to file (no pipe for child
        # processes to inherit and hold open after the script exits)
        "$script" > "$output_file" 2>&1 &
        local script_pid=$!

        # Show real-time progress by polling for assertion markers
        local prev_pass=0 prev_fail=0
        while kill -0 "$script_pid" 2>/dev/null; do
            sleep 0.3
            local pass fail
            pass=$(grep -c '✓' "$output_file" 2>/dev/null) || true
            fail=$(grep -c '✗' "$output_file" 2>/dev/null) || true
            pass="${pass:-0}"; fail="${fail:-0}"
            while [ "$prev_pass" -lt "$pass" ]; do
                printf "."
                ((++prev_pass))
            done
            while [ "$prev_fail" -lt "$fail" ]; do
                printf "F"
                ((++prev_fail))
            done
        done

        wait "$script_pid" 2>/dev/null || exit_code=$?

        # Flush any remaining markers
        local pass fail
        pass=$(grep -c '✓' "$output_file" 2>/dev/null) || true
        fail=$(grep -c '✗' "$output_file" 2>/dev/null) || true
        pass="${pass:-0}"; fail="${fail:-0}"
        while [ "$prev_pass" -lt "$pass" ]; do
            printf "."
            ((++prev_pass))
        done
        while [ "$prev_fail" -lt "$fail" ]; do
            printf "F"
            ((++prev_fail))
        done

        end_time=$(date +%s)
        duration=$((end_time - start_time))

        if [[ $exit_code -eq 0 ]]; then
            PASSED_SUITES=$((PASSED_SUITES + 1))
            printf " OK (%ds)\n" "$duration"
        else
            FAILED_SUITES=$((FAILED_SUITES + 1))
            FAILED_SUITE_NAMES+=("$name")
            printf " FAILED (%ds)\n" "$duration"
            while IFS= read -r line; do
                if [[ "$line" == *"✗"* ]]; then
                    printf "      %s\n" "$line"
                fi
            done < "$output_file"
        fi

        rm -f "$output_file"
    fi
}

# Syntax check all bash scripts
run_syntax_check() {
    TOTAL_SUITES=$((TOTAL_SUITES + 1))

    if [ "$VERBOSE" = true ]; then
        echo "----------------------------------------"
        echo "Running: Bash Syntax Check"
        echo "----------------------------------------"
    else
        printf "  %-24s " "Syntax Check:"
    fi

    local errors=0
    local checked=0

    # Check all .sh files in bin/ and lib/
    while IFS= read -r -d '' script; do
        ((++checked))
        if ! bash -n "$script" 2>/dev/null; then
            if [ "$VERBOSE" = true ]; then
                echo "Syntax error: $script"
            else
                printf "F"
            fi
            ((++errors))
        else
            [ "$VERBOSE" != true ] && printf "."
        fi
    done < <(find "$PROJECT_ROOT/bin" "$PROJECT_ROOT/lib" -name "*.sh" -print0 2>/dev/null)

    # Also check bin scripts without .sh extension
    for script in "$PROJECT_ROOT/bin/wiggum"*; do
        [ -f "$script" ] || continue
        ((++checked))
        if ! bash -n "$script" 2>/dev/null; then
            if [ "$VERBOSE" = true ]; then
                echo "Syntax error: $script"
            else
                printf "F"
            fi
            ((++errors))
        else
            [ "$VERBOSE" != true ] && printf "."
        fi
    done

    if [ $errors -eq 0 ]; then
        PASSED_SUITES=$((PASSED_SUITES + 1))
        if [ "$VERBOSE" = true ]; then
            echo "PASSED ($checked files checked)"
        else
            printf " OK (%d files)\n" "$checked"
        fi
    else
        FAILED_SUITES=$((FAILED_SUITES + 1))
        FAILED_SUITE_NAMES+=("Syntax Check ($errors errors)")
        if [ "$VERBOSE" = true ]; then
            echo "FAILED ($errors errors in $checked files)"
        else
            printf " FAILED (%d errors)\n" "$errors"
        fi
    fi
    [ "$VERBOSE" = true ] && echo "" || true
}

# Main test execution
main() {
    # Run specific suite if requested
    if [ -n "$SPECIFIC_SUITE" ]; then
        case "$SPECIFIC_SUITE" in
            syntax)
                run_syntax_check
                ;;
            integration)
                run_suite "Agent Lifecycle" "$SCRIPT_DIR/integration/test-agent-lifecycle.sh"
                run_suite "Worker Coordination" "$SCRIPT_DIR/integration/test-worker-coordination.sh"
                ;;
            e2e)
                run_suite "E2E Smoke Tests" "$SCRIPT_DIR/e2e/test-smoke.sh"
                ;;
            tui)
                run_suite "TUI Tests" "$SCRIPT_DIR/tui-test-runner.sh"
                ;;
            *)
                echo "Unknown suite: $SPECIFIC_SUITE"
                exit 1
                ;;
        esac
    else
        # Run all test suites

        # 1. Syntax checks (fast)
        run_syntax_check

        # 2. Shellcheck (mirrors CI)
        if [ "$QUICK_MODE" = false ]; then
            run_suite "Shellcheck Lint" "$SCRIPT_DIR/run-shellcheck.sh"
        fi

        # 3. Unit tests (test_*.sh files)
        run_suite "Unit Tests" "$SCRIPT_DIR/test-runner.sh"

        # 4. Integration tests
        run_suite "Agent Lifecycle" "$SCRIPT_DIR/integration/test-agent-lifecycle.sh"
        run_suite "Worker Coordination" "$SCRIPT_DIR/integration/test-worker-coordination.sh"

        # 5. E2E tests (slower)
        if [ "$QUICK_MODE" = false ]; then
            run_suite "E2E Smoke Tests" "$SCRIPT_DIR/e2e/test-smoke.sh"
        fi

        # 6. TUI tests (Python)
        run_suite "TUI Tests" "$SCRIPT_DIR/tui-test-runner.sh"
    fi

    # Print summary
    echo "========================================"
    echo "            TEST SUMMARY"
    echo "========================================"
    echo ""
    echo "Total Suites:  $TOTAL_SUITES"
    echo "Passed:        $PASSED_SUITES"
    echo "Failed:        $FAILED_SUITES"
    echo ""

    if [ $FAILED_SUITES -gt 0 ]; then
        echo "Failed Suites:"
        for suite in "${FAILED_SUITE_NAMES[@]}"; do
            echo "  - $suite"
        done
        echo ""
        echo "OVERALL: FAILED"
        exit 1
    fi

    echo "OVERALL: PASSED"
    exit 0
}

main
