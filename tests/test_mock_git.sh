#!/usr/bin/env bash
# test_mock_git.sh - Verify mock-git.sh functionality

set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$TESTS_DIR/test-framework.sh"
source "$TESTS_DIR/mocks/mock-helpers.sh"
source "$TESTS_DIR/mocks/mock-git-helpers.sh"

setup() {
    mock_setup    # Generic setup (creates MOCK_DIR)
    mock_git_setup # Git specific setup
}

teardown() {
    mock_git_teardown
    mock_teardown
}

test_basic_invocation() {
    git --version > /dev/null
    assert_git_invoked_with 1 "--version"
}

test_forced_output() {
    export MOCK_GIT_OUTPUT="git version 9.9.9-mock"
    export MOCK_GIT_PASSTHROUGH="false" # speed up
    local output
    output=$(git --version)
    assert_equals "git version 9.9.9-mock" "$output"
}

test_forced_exit_code() {
    export MOCK_GIT_EXIT_CODE=1
    export MOCK_GIT_PASSTHROUGH="false"
    local code=0
    git status >/dev/null 2>&1 || code=$?
    assert_equals "1" "$code"
}

test_passthrough_works() {
    # Assuming real git is available and can run 'git --version'
    export MOCK_GIT_PASSTHROUGH="true"
    local output
    output=$(git --version)
    assert_output_contains "$output" "git version"
    assert_git_invoked_with 1 "--version"
}

test_scenario_network_error() {
    export MOCK_GIT_SCENARIO="network-error"
    local code=0
    git clone https://example.com/repo.git >/dev/null 2>&1 || code=$?
    assert_equals "128" "$code"
    assert_git_invoked_with 1 "clone"
}

test_scenario_merge_conflict() {
    export MOCK_GIT_SCENARIO="merge-conflict"
    local code=0
    
    # Setup a dummy file to be conflicted
    echo "original" > "$MOCK_DIR/file.txt"
    export MOCK_GIT_CONFLICT_FILE="$MOCK_DIR/file.txt"
    
    # Run merge
    git merge feature-branch >/dev/null 2>&1 || code=$?
    
    assert_equals "1" "$code" "Merge should fail"
    
    local content
    content=$(cat "$MOCK_DIR/file.txt")
    assert_output_contains "$content" "<<<<<<< HEAD" "File should contain conflict markers"
}

echo "=== Mock Git Tests ==="
run_test test_basic_invocation
run_test test_forced_output
run_test test_forced_exit_code
run_test test_passthrough_works
run_test test_scenario_network_error
run_test test_scenario_merge_conflict

print_test_summary
exit_with_test_result
