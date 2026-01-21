#!/usr/bin/env bash
# Test runner for Chief Wiggum
# Executes all test files and reports results

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Counters
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0
SKIPPED_TESTS=0

# Get the script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Source the test framework
source "$SCRIPT_DIR/test-framework.sh"

# Print header
print_header() {
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${BLUE}  Chief Wiggum Test Runner${NC}"
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo ""
}

# Print footer with summary
print_footer() {
    echo ""
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${BLUE}  Test Summary${NC}"
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "  Total:   ${TOTAL_TESTS}"
    echo -e "  ${GREEN}Passed:  ${PASSED_TESTS}${NC}"
    if [ $FAILED_TESTS -gt 0 ]; then
        echo -e "  ${RED}Failed:  ${FAILED_TESTS}${NC}"
    else
        echo -e "  Failed:  ${FAILED_TESTS}"
    fi
    if [ $SKIPPED_TESTS -gt 0 ]; then
        echo -e "  ${YELLOW}Skipped: ${SKIPPED_TESTS}${NC}"
    fi
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo ""

    if [ $FAILED_TESTS -eq 0 ]; then
        echo -e "${GREEN}All tests passed! ✓${NC}"
        return 0
    else
        echo -e "${RED}Some tests failed ✗${NC}"
        return 1
    fi
}

# Run a single test file
run_test_file() {
    local test_file="$1"
    local test_name
    test_name=$(basename "$test_file" .sh)

    echo -e "${YELLOW}Running: ${test_name}${NC}"

    # Create isolated test environment
    TEST_TEMP_DIR=$(mktemp -d)
    export TEST_TEMP_DIR

    # Run the test file
    if bash "$test_file"; then
        echo -e "${GREEN}✓ ${test_name} passed${NC}"
        PASSED_TESTS=$((PASSED_TESTS + 1))
    else
        echo -e "${RED}✗ ${test_name} failed${NC}"
        FAILED_TESTS=$((FAILED_TESTS + 1))
    fi

    TOTAL_TESTS=$((TOTAL_TESTS + 1))

    # Cleanup
    rm -rf "$TEST_TEMP_DIR"
    echo ""
}

# Main execution
main() {
    print_header

    # Change to project root
    cd "$PROJECT_ROOT"

    # Find all test files
    if [ $# -eq 0 ]; then
        # Run all tests in tests/ directory
        test_files=()
        while IFS= read -r -d '' file; do
            test_files+=("$file")
        done < <(find "$SCRIPT_DIR" -maxdepth 1 -name "test_*.sh" -type f -print0 | sort -z)

        if [ ${#test_files[@]} -eq 0 ]; then
            echo -e "${YELLOW}No test files found${NC}"
            echo "Test files should be named test_*.sh in the tests/ directory"
            exit 0
        fi
    else
        # Run specific test files
        test_files=("$@")
    fi

    # Run each test file
    for test_file in "${test_files[@]}"; do
        if [ -f "$test_file" ]; then
            run_test_file "$test_file"
        else
            echo -e "${RED}Test file not found: $test_file${NC}"
            FAILED_TESTS=$((FAILED_TESTS + 1))
            TOTAL_TESTS=$((TOTAL_TESTS + 1))
        fi
    done

    # Print summary and exit
    print_footer
}

# Run main with all arguments
main "$@"
