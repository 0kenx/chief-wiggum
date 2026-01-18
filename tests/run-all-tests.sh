#!/usr/bin/env bash
# Master test runner for Chief Wiggum

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "======================================"
echo "Chief Wiggum Test Suite"
echo "======================================"
echo ""

# Track overall results
TOTAL_SUITES=0
FAILED_SUITES=0

# Function to run a test suite
run_suite() {
    local test_script="$1"
    local suite_name=$(basename "$test_script" .sh)

    echo ""
    echo "--------------------------------------"
    echo "Running: $suite_name"
    echo "--------------------------------------"

    ((TOTAL_SUITES++))

    if bash "$test_script"; then
        echo "✓ $suite_name PASSED"
    else
        echo "✗ $suite_name FAILED"
        ((FAILED_SUITES++))
    fi
}

# Run all test suites
run_suite "$SCRIPT_DIR/test-task-parser.sh"
run_suite "$SCRIPT_DIR/test-worker.sh"
run_suite "$SCRIPT_DIR/test-ralph-loop.sh"
run_suite "$SCRIPT_DIR/test-edge-cases.sh"

# Print final summary
echo ""
echo "======================================"
echo "Final Test Summary"
echo "======================================"
echo "Total test suites: $TOTAL_SUITES"
echo "Passed suites: $((TOTAL_SUITES - FAILED_SUITES))"
echo "Failed suites: $FAILED_SUITES"
echo "======================================"

if [ $FAILED_SUITES -eq 0 ]; then
    echo "✓ ALL TEST SUITES PASSED!"
    exit 0
else
    echo "✗ SOME TEST SUITES FAILED"
    exit 1
fi
