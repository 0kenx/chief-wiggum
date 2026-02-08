#!/usr/bin/env bash
# Test runner for Chief Wiggum
# Executes all test files and reports results
#
# Usage:
#   ./test-runner.sh                  # Run all tests
#   ./test-runner.sh --filter lock    # Run only tests matching "lock"
#   ./test-runner.sh --filter lock,kanban  # Run tests matching "lock" or "kanban"
#   ./test-runner.sh --filter "lock|kanban" # Pipe-separated also works
#   ./test-runner.sh path/to/test.sh  # Run specific test file

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
DIM='\033[2m'
NC='\033[0m' # No Color

# Counters
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0
SKIPPED_TESTS=0

# Timing
TOTAL_START_TIME=0
declare -a TEST_TIMINGS=()

# Filter pattern
FILTER_PATTERN=""

# Get the script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Source the test framework
source "$SCRIPT_DIR/test-framework.sh"

# Print header
print_header() {
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${BLUE}  Chief Wiggum Test Runner${NC}"
    if [ -n "$FILTER_PATTERN" ]; then
        echo -e "${BLUE}  Filter: ${FILTER_PATTERN}${NC}"
    fi
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo ""
}

# Print footer with summary
print_footer() {
    local total_end_time
    total_end_time=$(date +%s%N 2>/dev/null || date +%s)
    local total_duration_ms=$(( (total_end_time - TOTAL_START_TIME) / 1000000 ))

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
    echo -e "  ${DIM}Duration: ${total_duration_ms}ms${NC}"

    # Show per-test timing breakdown
    if [ ${#TEST_TIMINGS[@]} -gt 0 ]; then
        echo ""
        echo -e "  ${DIM}Per-test timing:${NC}"
        for timing in "${TEST_TIMINGS[@]}"; do
            echo -e "    ${DIM}${timing}${NC}"
        done
    fi

    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo ""

    if [ $FAILED_TESTS -eq 0 ]; then
        echo -e "${GREEN}All tests passed! ✓${NC}"
        return 0
    else
        echo -e "${RED}Some tests failed ✗${NC}" >&2
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

    # Time the test
    local start_time
    start_time=$(date +%s%N 2>/dev/null || date +%s)

    # Run the test file
    if bash "$test_file"; then
        local end_time
        end_time=$(date +%s%N 2>/dev/null || date +%s)
        local duration_ms=$(( (end_time - start_time) / 1000000 ))
        echo -e "${GREEN}✓ ${test_name} passed${NC} ${DIM}(${duration_ms}ms)${NC}"
        PASSED_TESTS=$((PASSED_TESTS + 1))
        TEST_TIMINGS+=("${duration_ms}ms  ${test_name}")
    else
        local end_time
        end_time=$(date +%s%N 2>/dev/null || date +%s)
        local duration_ms=$(( (end_time - start_time) / 1000000 ))
        echo -e "${RED}✗ ${test_name} failed${NC} ${DIM}(${duration_ms}ms)${NC}" >&2
        FAILED_TESTS=$((FAILED_TESTS + 1))
        TEST_TIMINGS+=("${duration_ms}ms  ${test_name} [FAILED]")
    fi

    TOTAL_TESTS=$((TOTAL_TESTS + 1))

    # Cleanup
    [ -n "$TEST_TEMP_DIR" ] && rm -rf "$TEST_TEMP_DIR"
    echo ""
}

# Parse arguments
parse_args() {
    local positional=()

    while [ $# -gt 0 ]; do
        case "$1" in
            --filter|-f)
                if [ $# -lt 2 ]; then
                    echo -e "${RED}--filter requires a pattern argument${NC}" >&2
                    exit 2
                fi
                FILTER_PATTERN="$2"
                shift 2
                ;;
            --filter=*)
                FILTER_PATTERN="${1#--filter=}"
                shift
                ;;
            -*)
                echo -e "${RED}Unknown option: $1${NC}" >&2
                echo "Usage: $0 [--filter PATTERN] [test_file...]" >&2
                exit 2
                ;;
            *)
                positional+=("$1")
                shift
                ;;
        esac
    done

    # Set remaining positional arguments
    set -- "${positional[@]+"${positional[@]}"}"
    POSITIONAL_ARGS=("${positional[@]+"${positional[@]}"}")
}

# Main execution
main() {
    local POSITIONAL_ARGS=()
    parse_args "$@"

    # Record start time
    TOTAL_START_TIME=$(date +%s%N 2>/dev/null || date +%s)

    print_header

    # Change to project root
    cd "$PROJECT_ROOT"

    # Find all test files
    if [ ${#POSITIONAL_ARGS[@]} -eq 0 ]; then
        # Run all tests: unit tests (tests/test_*.sh), integration, and e2e
        test_files=()

        # Unit tests (test_*.sh in tests/)
        while IFS= read -r -d '' file; do
            test_files+=("$file")
        done < <(find "$SCRIPT_DIR" -maxdepth 1 -name "test_*.sh" -type f -print0 | sort -z)

        # Integration tests (tests/integration/test-*.sh)
        if [ -d "$SCRIPT_DIR/integration" ]; then
            while IFS= read -r -d '' file; do
                test_files+=("$file")
            done < <(find "$SCRIPT_DIR/integration" -name "test-*.sh" -type f -print0 | sort -z)
        fi

        # E2E tests (tests/e2e/test-*.sh)
        if [ -d "$SCRIPT_DIR/e2e" ]; then
            while IFS= read -r -d '' file; do
                test_files+=("$file")
            done < <(find "$SCRIPT_DIR/e2e" -name "test-*.sh" -type f -print0 | sort -z)
        fi

        if [ ${#test_files[@]} -eq 0 ]; then
            echo -e "${YELLOW}No test files found${NC}"
            echo "Test files should be named test_*.sh (unit) or test-*.sh (integration/e2e)"
            exit 0
        fi
    else
        # Run specific test files
        test_files=("${POSITIONAL_ARGS[@]}")
    fi

    # Apply filter if specified (supports comma-separated or pipe-separated patterns)
    if [ -n "$FILTER_PATTERN" ]; then
        local filtered_files=()
        # Normalize: strip backslash escapes (\|) and replace | with , so
        # both "a,b" and "a|b" and "a\|b" work as multi-pattern filters.
        local normalized_filter="${FILTER_PATTERN//\\|/,}"
        normalized_filter="${normalized_filter//|/,}"
        IFS=',' read -ra filter_patterns <<< "$normalized_filter"
        for test_file in "${test_files[@]}"; do
            local name
            name=$(basename "$test_file")
            for pattern in "${filter_patterns[@]}"; do
                if [[ "$name" == *"$pattern"* ]]; then
                    filtered_files+=("$test_file")
                    break
                fi
            done
        done

        if [ ${#filtered_files[@]} -eq 0 ]; then
            echo -e "${YELLOW}No test files match filter: ${FILTER_PATTERN}${NC}"
            exit 0
        fi

        test_files=("${filtered_files[@]}")
        echo -e "${DIM}Matched ${#test_files[@]} test file(s)${NC}"
        echo ""
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
