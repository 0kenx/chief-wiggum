#!/usr/bin/env bash
# Simple bash test framework for Chief Wiggum

TESTS_PASSED=0
TESTS_FAILED=0
CURRENT_TEST=""

# Test utilities
assert_equals() {
    local expected="$1"
    local actual="$2"
    local message="${3:-}"

    if [ "$expected" = "$actual" ]; then
        echo "  ✓ ${message:-assertion passed}"
        ((TESTS_PASSED++))
        return 0
    else
        echo "  ✗ ${message:-assertion failed}"
        echo "    Expected: '$expected'"
        echo "    Actual:   '$actual'"
        ((TESTS_FAILED++))
        return 1
    fi
}

assert_true() {
    local condition="$1"
    local message="${2:-}"

    if [ "$condition" = "0" ]; then
        echo "  ✓ ${message:-assertion passed}"
        ((TESTS_PASSED++))
        return 0
    else
        echo "  ✗ ${message:-assertion failed (expected true)}"
        ((TESTS_FAILED++))
        return 1
    fi
}

assert_false() {
    local condition="$1"
    local message="${2:-}"

    if [ "$condition" != "0" ]; then
        echo "  ✓ ${message:-assertion passed}"
        ((TESTS_PASSED++))
        return 0
    else
        echo "  ✗ ${message:-assertion failed (expected false)}"
        ((TESTS_FAILED++))
        return 1
    fi
}

assert_contains() {
    local haystack="$1"
    local needle="$2"
    local message="${3:-}"

    if echo "$haystack" | grep -qF -- "$needle"; then
        echo "  ✓ ${message:-contains check passed}"
        ((TESTS_PASSED++))
        return 0
    else
        echo "  ✗ ${message:-contains check failed}"
        echo "    Looking for: '$needle'"
        echo "    In: '$haystack'"
        ((TESTS_FAILED++))
        return 1
    fi
}

assert_not_contains() {
    local haystack="$1"
    local needle="$2"
    local message="${3:-}"

    if ! echo "$haystack" | grep -qF -- "$needle"; then
        echo "  ✓ ${message:-not contains check passed}"
        ((TESTS_PASSED++))
        return 0
    else
        echo "  ✗ ${message:-not contains check failed}"
        echo "    Should not contain: '$needle'"
        echo "    In: '$haystack'"
        ((TESTS_FAILED++))
        return 1
    fi
}

assert_file_exists() {
    local file="$1"
    local message="${2:-}"

    if [ -f "$file" ]; then
        echo "  ✓ ${message:-file exists}"
        ((TESTS_PASSED++))
        return 0
    else
        echo "  ✗ ${message:-file does not exist}: $file"
        ((TESTS_FAILED++))
        return 1
    fi
}

# Test runners
test_suite() {
    local suite_name="$1"
    echo ""
    echo "=== Test Suite: $suite_name ==="
}

test_case() {
    local test_name="$1"
    CURRENT_TEST="$test_name"
    echo ""
    echo "Test: $test_name"
}

# Print test summary
print_summary() {
    echo ""
    echo "======================================="
    echo "Test Summary"
    echo "======================================="
    echo "Passed: $TESTS_PASSED"
    echo "Failed: $TESTS_FAILED"
    echo "Total:  $((TESTS_PASSED + TESTS_FAILED))"
    echo "======================================="

    if [ $TESTS_FAILED -eq 0 ]; then
        echo "✓ All tests passed!"
        return 0
    else
        echo "✗ Some tests failed"
        return 1
    fi
}

# Setup/teardown helpers
setup_test_dir() {
    TEST_TMP_DIR="$(mktemp -d)"
    echo "  Setup: Created temp dir $TEST_TMP_DIR"
}

teardown_test_dir() {
    if [ -n "${TEST_TMP_DIR:-}" ] && [ -d "$TEST_TMP_DIR" ]; then
        rm -rf "$TEST_TMP_DIR"
        echo "  Teardown: Removed temp dir"
    fi
}
