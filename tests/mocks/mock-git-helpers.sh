#!/usr/bin/env bash
# mock-git-helpers.sh - Helpers for mock-git.sh
#
# Setup/teardown and assertions for mock git.

# Use existing mock-helpers for generic assertions if compatible, 
# but define git specific ones here.

MOCK_GIT_PATH=""
REAL_GIT_PATH=""

mock_git_setup() {
    # If MOCK_DIR not set (mock-helpers not used), create one
    if [ -z "${MOCK_DIR:-}" ]; then
        MOCK_DIR=$(mktemp -d)
    fi
    export MOCK_GIT_LOG_DIR="$MOCK_DIR/git-logs"
    mkdir -p "$MOCK_GIT_LOG_DIR"
    
    # Store real git path
    if [ -z "${REAL_GIT_PATH:-}" ]; then
        REAL_GIT_PATH=$(type -p git)
        export REAL_GIT_PATH
    fi
    
    # Path to the mock script
    MOCK_GIT_PATH="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/mock-git.sh"
    chmod +x "$MOCK_GIT_PATH"
    
    # We need to make sure calls to 'git' use our mock.
    # We can't just export GIT=... because scripts use `git ...` directly.
    # We need to manipulate PATH or define a function.
    # PATH manipulation is safest for subprocesses.
    
    mkdir -p "$MOCK_DIR/bin"
    ln -sf "$MOCK_GIT_PATH" "$MOCK_DIR/bin/git"
    export PATH="$MOCK_DIR/bin:$PATH"
    
    # Reset env vars
    unset MOCK_GIT_EXIT_CODE
    unset MOCK_GIT_OUTPUT
    unset MOCK_GIT_SCENARIO
    unset MOCK_GIT_PASSTHROUGH
    unset MOCK_GIT_CONFLICT_FILE
}

mock_git_teardown() {
    # If we created MOCK_DIR locally (not shared), clean it?
    # Usually the test framework teardown handles the main MOCK_DIR if setup/teardown pairs
    # are used correctly testing framework. 
    # For now, just unset vars.
    unset MOCK_GIT_LOG_DIR
    unset MOCK_GIT_EXIT_CODE
    unset MOCK_GIT_OUTPUT
    unset MOCK_GIT_SCENARIO
    unset MOCK_GIT_PASSTHROUGH
    unset MOCK_GIT_CONFLICT_FILE
    
    # Restore PATH not easily possible without storing original, 
    # but subshells in tests handle this naturally.
}

# Assertions

assert_git_invoked_with() {
    local index="$1"
    local expected_arg="$2"
    local message="${3:-Git invocation $index should contain '$expected_arg'}"
    
    local args_file="$MOCK_GIT_LOG_DIR/args/invocation-$index.args"
    if [ ! -f "$args_file" ]; then
         echo -e "  ${RED}✗${NC} $message (Invocation $index not found)"
         FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
         return 1
    fi
    
    if grep -qF -- "$expected_arg" "$args_file"; then
        echo -e "  ${GREEN}✓${NC} $message"
        return 0
    else
        echo -e "  ${RED}✗${NC} $message"
        echo "    Expected: $expected_arg"
        echo "    Actual: $(cat "$args_file")"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        return 1
    fi
}
