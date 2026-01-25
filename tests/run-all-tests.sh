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

    echo "----------------------------------------"
    echo "Running: $name"
    echo "----------------------------------------"

    if [ ! -f "$script" ]; then
        echo "ERROR: Test script not found: $script"
        FAILED_SUITES=$((FAILED_SUITES + 1))
        FAILED_SUITE_NAMES+=("$name (not found)")
        return 1
    fi

    chmod +x "$script"

    local start_time end_time duration
    start_time=$(date +%s)

    if [ "$VERBOSE" = true ]; then
        if "$script"; then
            PASSED_SUITES=$((PASSED_SUITES + 1))
        else
            FAILED_SUITES=$((FAILED_SUITES + 1))
            FAILED_SUITE_NAMES+=("$name")
        fi
    else
        # Redirect stdout to /dev/null, let stderr (failures) pass through
        if "$script" > /dev/null; then
            PASSED_SUITES=$((PASSED_SUITES + 1))
            echo "PASSED"
        else
            FAILED_SUITES=$((FAILED_SUITES + 1))
            FAILED_SUITE_NAMES+=("$name")
            echo "FAILED"
        fi
    fi

    end_time=$(date +%s)
    duration=$((end_time - start_time))
    echo "Duration: ${duration}s"
    echo ""
}

# Syntax check all bash scripts
run_syntax_check() {
    echo "----------------------------------------"
    echo "Running: Bash Syntax Check"
    echo "----------------------------------------"

    TOTAL_SUITES=$((TOTAL_SUITES + 1))

    local errors=0
    local checked=0

    # Check all .sh files in bin/ and lib/
    while IFS= read -r -d '' script; do
        ((++checked))
        if ! bash -n "$script" 2>/dev/null; then
            echo "Syntax error: $script"
            ((++errors))
        fi
    done < <(find "$PROJECT_ROOT/bin" "$PROJECT_ROOT/lib" -name "*.sh" -print0 2>/dev/null)

    # Also check bin scripts without .sh extension
    for script in "$PROJECT_ROOT/bin/wiggum"*; do
        [ -f "$script" ] || continue
        ((++checked))
        if ! bash -n "$script" 2>/dev/null; then
            echo "Syntax error: $script"
            ((++errors))
        fi
    done

    if [ $errors -eq 0 ]; then
        PASSED_SUITES=$((PASSED_SUITES + 1))
        echo "PASSED ($checked files checked)"
    else
        FAILED_SUITES=$((FAILED_SUITES + 1))
        FAILED_SUITE_NAMES+=("Syntax Check ($errors errors)")
        echo "FAILED ($errors errors in $checked files)"
    fi
    echo ""
}

# Run shellcheck if available
run_shellcheck() {
    if ! command -v shellcheck &>/dev/null; then
        echo "Shellcheck not installed, skipping..."
        return 0
    fi

    echo "----------------------------------------"
    echo "Running: Shellcheck Linting"
    echo "----------------------------------------"

    TOTAL_SUITES=$((TOTAL_SUITES + 1))

    local errors=0
    local checked=0

    # Match CI: check bin executables, lib/*.sh, tests/*.sh, and root scripts
    while IFS= read -r -d '' script; do
        ((++checked))
        if ! shellcheck --severity=warning "$script" 2>/dev/null; then
            ((++errors))
        fi
    done < <(find "$PROJECT_ROOT/bin" -type f -executable -print0 2>/dev/null)

    while IFS= read -r -d '' script; do
        ((++checked))
        if ! shellcheck --severity=warning "$script" 2>/dev/null; then
            ((++errors))
        fi
    done < <(find "$PROJECT_ROOT/lib" -name "*.sh" -type f -print0 2>/dev/null)

    while IFS= read -r -d '' script; do
        ((++checked))
        if ! shellcheck --severity=warning "$script" 2>/dev/null; then
            ((++errors))
        fi
    done < <(find "$PROJECT_ROOT/tests" -name "*.sh" -type f -print0 2>/dev/null)

    for script in "$PROJECT_ROOT/install.sh" "$PROJECT_ROOT/install-symlink.sh"; do
        if [ -f "$script" ]; then
            ((++checked))
            if ! shellcheck --severity=warning "$script" 2>/dev/null; then
                ((++errors))
            fi
        fi
    done

    if [ $errors -eq 0 ]; then
        PASSED_SUITES=$((PASSED_SUITES + 1))
        echo "PASSED ($checked files checked)"
    else
        FAILED_SUITES=$((FAILED_SUITES + 1))
        FAILED_SUITE_NAMES+=("Shellcheck ($errors files with warnings)")
        echo "FAILED ($errors files with warnings)"
    fi
    echo ""
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

        # 2. Shellcheck (if available)
        if [ "$QUICK_MODE" = false ]; then
            run_shellcheck
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
