#!/usr/bin/env bash
# Test framework for Chief Wiggum
# Provides assertion functions, fixtures, and test utilities

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Test state
TEST_COUNT=0
ASSERTION_COUNT=0
FAILED_ASSERTIONS=0

# Get the tests directory
TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FIXTURES_DIR="$TESTS_DIR/fixtures"

# =============================================================================
# Assertion Functions
# =============================================================================

# Assert that a command succeeds (exit code 0)
# Usage: assert_success "message" command arg1 arg2...
assert_success() {
    local message="${1:-Command should succeed}"
    shift

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    if "$@" >/dev/null 2>&1; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message" >&2
        echo -e "    ${RED}Expected: success (exit 0)${NC}" >&2
        echo -e "    ${RED}Command: $*${NC}" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}

# Assert that a command fails (non-zero exit code)
# Usage: assert_failure "message" command arg1 arg2...
assert_failure() {
    local message="${1:-Command should fail}"
    shift

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    if "$@" >/dev/null 2>&1; then
        echo -e "  ${RED}✗${NC} $message" >&2
        echo -e "    ${RED}Expected: failure (non-zero exit)${NC}" >&2
        echo -e "    ${RED}Command: $*${NC}" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    else
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    fi
}

# Assert that two strings are equal
assert_equals() {
    local expected="$1"
    local actual="$2"
    local message="${3:-Values should be equal}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    if [ "$expected" = "$actual" ]; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message" >&2
        echo -e "    ${RED}Expected: '$expected'${NC}" >&2
        echo -e "    ${RED}Actual:   '$actual'${NC}" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}

# Assert that two strings are not equal
assert_not_equals() {
    local not_expected="$1"
    local actual="$2"
    local message="${3:-Values should not be equal}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    if [ "$not_expected" != "$actual" ]; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message" >&2
        echo -e "    ${RED}Should not equal: '$not_expected'${NC}" >&2
        echo -e "    ${RED}Actual:           '$actual'${NC}" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}

# Assert that a file exists
assert_file_exists() {
    local file_path="$1"
    local message="${2:-File should exist: $file_path}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    if [ -f "$file_path" ]; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message" >&2
        echo -e "    ${RED}File not found: $file_path${NC}" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}

# Assert that a file does not exist
assert_file_not_exists() {
    local file_path="$1"
    local message="${2:-File should not exist: $file_path}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    if [ ! -f "$file_path" ]; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message" >&2
        echo -e "    ${RED}File exists: $file_path${NC}" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}

# Assert that a directory exists
assert_dir_exists() {
    local dir_path="$1"
    local message="${2:-Directory should exist: $dir_path}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    if [ -d "$dir_path" ]; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message" >&2
        echo -e "    ${RED}Directory not found: $dir_path${NC}" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}

# Assert that a file contains a pattern
assert_file_contains() {
    local file_path="$1"
    local pattern="$2"
    local message="${3:-File should contain pattern: $pattern}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    if [ ! -f "$file_path" ]; then
        echo -e "  ${RED}✗${NC} $message" >&2
        echo -e "    ${RED}File not found: $file_path${NC}" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi

    if grep -qF -- "$pattern" "$file_path"; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message" >&2
        echo -e "    ${RED}Pattern not found: $pattern${NC}" >&2
        echo -e "    ${RED}In file: $file_path${NC}" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}

# Assert that a file does not contain a pattern
assert_file_not_contains() {
    local file_path="$1"
    local pattern="$2"
    local message="${3:-File should not contain pattern: $pattern}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    if [ ! -f "$file_path" ]; then
        echo -e "  ${RED}✗${NC} $message" >&2
        echo -e "    ${RED}File not found: $file_path${NC}" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi

    if grep -qF -- "$pattern" "$file_path"; then
        echo -e "  ${RED}✗${NC} $message" >&2
        echo -e "    ${RED}Pattern found (should not be): $pattern${NC}" >&2
        echo -e "    ${RED}In file: $file_path${NC}" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    else
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    fi
}

# Assert that output contains a pattern
assert_output_contains() {
    local output="$1"
    local pattern="$2"
    local message="${3:-Output should contain pattern: $pattern}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    if echo "$output" | grep -qF -- "$pattern"; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message" >&2
        echo -e "    ${RED}Pattern not found: $pattern${NC}" >&2
        echo -e "    ${RED}In output: $output${NC}" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}

# Assert that output does not contain a pattern
assert_output_not_contains() {
    local output="$1"
    local pattern="$2"
    local message="${3:-Output should not contain pattern: $pattern}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    if echo "$output" | grep -qF -- "$pattern"; then
        echo -e "  ${RED}✗${NC} $message" >&2
        echo -e "    ${RED}Pattern found (should not be): $pattern${NC}" >&2
        echo -e "    ${RED}In output: $output${NC}" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    else
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    fi
}

# Assert that a command exits with a specific code
# Usage: assert_exit_code expected_code "message" command arg1 arg2...
assert_exit_code() {
    local expected_code="$1"
    local message="${2:-Command should exit with code $expected_code}"
    shift 2

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    local actual_code=0
    "$@" >/dev/null 2>&1 || actual_code=$?

    if [ "$actual_code" -eq "$expected_code" ]; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message" >&2
        echo -e "    ${RED}Expected exit code: $expected_code${NC}" >&2
        echo -e "    ${RED}Actual exit code:   $actual_code${NC}" >&2
        echo -e "    ${RED}Command: $*${NC}" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}

# Assert that a number is greater than another
assert_greater_than() {
    local value="$1"
    local threshold="$2"
    local message="${3:-Value should be greater than $threshold}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    if [ "$value" -gt "$threshold" ]; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message" >&2
        echo -e "    ${RED}Expected: > $threshold${NC}" >&2
        echo -e "    ${RED}Actual:   $value${NC}" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}

# Assert that a string/variable is not empty
assert_not_empty() {
    local value="$1"
    local message="${2:-Value should not be empty}"

    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    if [ -n "$value" ]; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message" >&2
        echo -e "    ${RED}Expected: non-empty value${NC}" >&2
        echo -e "    ${RED}Actual:   (empty)${NC}" >&2
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}

# =============================================================================
# Fixture Functions
# =============================================================================

# Load a fixture file into a variable
load_fixture() {
    local fixture_name="$1"
    local fixture_path="$FIXTURES_DIR/$fixture_name"

    if [ ! -f "$fixture_path" ]; then
        echo -e "${RED}Fixture not found: $fixture_path${NC}" >&2
        return 1
    fi

    cat "$fixture_path"
}

# Copy a fixture to a temporary location for testing
copy_fixture() {
    local fixture_name="$1"
    local dest_path="$2"
    local fixture_path="$FIXTURES_DIR/$fixture_name"

    if [ ! -f "$fixture_path" ]; then
        echo -e "${RED}Fixture not found: $fixture_path${NC}" >&2
        return 1
    fi

    cp "$fixture_path" "$dest_path"
}

# Create a temporary directory for test isolation
create_test_dir() {
    mktemp -d
}

# =============================================================================
# Test Lifecycle Functions
# =============================================================================

# Setup function called before each test
setup() {
    # Override this in test files if needed
    :
}

# Teardown function called after each test
teardown() {
    # Override this in test files if needed
    :
}

# Run a test with setup and teardown
run_test() {
    local test_name="$1"

    TEST_COUNT=$((TEST_COUNT + 1))
    echo ""
    echo -e "${YELLOW}Test: $test_name${NC}"

    # Run setup
    setup

    # Time the test
    local _test_start _test_end _test_ms
    _test_start=$(date +%s%N 2>/dev/null || date +%s)

    # Run the test
    local test_result=0
    "$test_name" || test_result=$?

    _test_end=$(date +%s%N 2>/dev/null || date +%s)
    _test_ms=$(( (_test_end - _test_start) / 1000000 ))
    if [ $_test_ms -gt 0 ]; then
        echo -e "  ${DIM}(${_test_ms}ms)${NC}"
    fi

    # Run teardown
    teardown

    return $test_result
}

# Dim color for timing output
DIM='\033[2m'

# =============================================================================
# Test Result Functions
# =============================================================================

# Check if all assertions passed
all_assertions_passed() {
    if [ $FAILED_ASSERTIONS -eq 0 ]; then
        return 0
    else
        return 1
    fi
}

# Print test summary
print_test_summary() {
    echo ""
    echo "Assertions: $ASSERTION_COUNT total, $FAILED_ASSERTIONS failed"

    if all_assertions_passed; then
        echo -e "${GREEN}All assertions passed ✓${NC}"
        return 0
    else
        echo -e "${RED}Some assertions failed ✗${NC}" >&2
        return 1
    fi
}

# Exit with appropriate code based on test results
exit_with_test_result() {
    if all_assertions_passed; then
        exit 0
    else
        exit 1
    fi
}
