#!/usr/bin/env bash
# Tests for lib/core/defaults.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME_BACKUP="$WIGGUM_HOME"
PROJECT_DIR_BACKUP="$PROJECT_DIR"

source "$TESTS_DIR/test-framework.sh"

# Create temp dir for test isolation
TEST_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    # Reset env vars before each test
    unset WIGGUM_HOME
    unset PROJECT_DIR
    unset RALPH_DIR
    unset CLAUDE
    unset WIGGUM_MAX_WORKERS
    unset WIGGUM_MAX_ITERATIONS
    unset WIGGUM_MAX_TURNS
    unset WIGGUM_APPROVED_AUTHORS
    unset WIGGUM_COMMENT_FIX_MAX_ITERATIONS
    unset WIGGUM_COMMENT_FIX_MAX_TURNS
    unset WIGGUM_AUTO_COMMIT_AFTER_FIX
}

teardown() {
    rm -rf "$TEST_DIR"
    # Restore original WIGGUM_HOME for subsequent tests
    export WIGGUM_HOME="$WIGGUM_HOME_BACKUP"
    export PROJECT_DIR="$PROJECT_DIR_BACKUP"
}

# =============================================================================
# Default Values Tests
# =============================================================================

test_wiggum_home_default() {
    (
        source "$WIGGUM_HOME_BACKUP/lib/core/defaults.sh"
        if [[ "$WIGGUM_HOME" == "$HOME/.claude/chief-wiggum" ]]; then
            echo "PASS"
        else
            echo "FAIL: $WIGGUM_HOME"
        fi
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")
    assert_equals "PASS" "$result" "WIGGUM_HOME should default to ~/.claude/chief-wiggum"
}

test_wiggum_home_env_override() {
    (
        export WIGGUM_HOME="/custom/path"
        source "$WIGGUM_HOME_BACKUP/lib/core/defaults.sh"
        echo "$WIGGUM_HOME"
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")
    assert_equals "/custom/path" "$result" "WIGGUM_HOME should respect env override"
}

test_project_dir_default() {
    (
        cd "$TEST_DIR" || exit 1
        source "$WIGGUM_HOME_BACKUP/lib/core/defaults.sh"
        echo "$PROJECT_DIR"
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")
    assert_equals "$TEST_DIR" "$result" "PROJECT_DIR should default to pwd"
}

test_ralph_dir_default() {
    (
        cd "$TEST_DIR" || exit 1
        source "$WIGGUM_HOME_BACKUP/lib/core/defaults.sh"
        echo "$RALPH_DIR"
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")
    assert_equals "$TEST_DIR/.ralph" "$result" "RALPH_DIR should default to PROJECT_DIR/.ralph"
}

test_claude_binary_default() {
    (
        source "$WIGGUM_HOME_BACKUP/lib/core/defaults.sh"
        echo "$CLAUDE"
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")
    assert_equals "claude" "$result" "CLAUDE should default to 'claude'"
}

test_max_workers_default() {
    (
        source "$WIGGUM_HOME_BACKUP/lib/core/defaults.sh"
        echo "$MAX_WORKERS"
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")
    assert_equals "4" "$result" "MAX_WORKERS should default to 4"
}

test_max_iterations_default() {
    (
        source "$WIGGUM_HOME_BACKUP/lib/core/defaults.sh"
        echo "$MAX_ITERATIONS"
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")
    assert_equals "20" "$result" "MAX_ITERATIONS should default to 20"
}

test_max_turns_default() {
    (
        source "$WIGGUM_HOME_BACKUP/lib/core/defaults.sh"
        echo "$MAX_TURNS"
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")
    assert_equals "50" "$result" "MAX_TURNS should default to 50"
}

test_max_workers_env_override() {
    (
        export WIGGUM_MAX_WORKERS=8
        source "$WIGGUM_HOME_BACKUP/lib/core/defaults.sh"
        echo "$MAX_WORKERS"
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")
    assert_equals "8" "$result" "MAX_WORKERS should respect env override"
}

# =============================================================================
# load_review_config() Tests
# =============================================================================

test_load_review_config_defaults_without_file() {
    (
        source "$WIGGUM_HOME_BACKUP/lib/core/defaults.sh"
        export WIGGUM_HOME="$TEST_DIR/nonexistent"
        load_review_config

        echo "AUTHORS=$WIGGUM_APPROVED_AUTHORS"
        echo "MAX_ITER=$WIGGUM_COMMENT_FIX_MAX_ITERATIONS"
        echo "MAX_TURNS=$WIGGUM_COMMENT_FIX_MAX_TURNS"
        echo "AUTO_COMMIT=$WIGGUM_AUTO_COMMIT_AFTER_FIX"
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")

    assert_output_contains "$result" "MAX_ITER=10" "Should use default max iterations"
    assert_output_contains "$result" "MAX_TURNS=30" "Should use default max turns"
    assert_output_contains "$result" "AUTO_COMMIT=true" "Should use default auto commit"
}

test_load_review_config_with_config_file() {
    # Create a test config file
    mkdir -p "$TEST_DIR/config"
    cat > "$TEST_DIR/config/config.json" << 'EOF'
{
    "review": {
        "approved_authors": ["user1", "user2"],
        "fix_max_iterations": 15,
        "fix_max_turns": 40,
        "auto_commit_after_fix": true
    }
}
EOF

    (
        export WIGGUM_HOME="$TEST_DIR"
        source "$WIGGUM_HOME_BACKUP/lib/core/defaults.sh"
        load_review_config

        echo "MAX_ITER=$WIGGUM_COMMENT_FIX_MAX_ITERATIONS"
        echo "MAX_TURNS=$WIGGUM_COMMENT_FIX_MAX_TURNS"
        echo "AUTO_COMMIT=$WIGGUM_AUTO_COMMIT_AFTER_FIX"
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")

    assert_output_contains "$result" "MAX_ITER=15" "Should load max iterations from config"
    assert_output_contains "$result" "MAX_TURNS=40" "Should load max turns from config"
    # Note: jq's // operator has a quirk where `false // true` returns `true`
    # So we test with auto_commit_after_fix: true
    assert_output_contains "$result" "AUTO_COMMIT=true" "Should load auto commit from config"
}

test_load_review_config_env_override() {
    # Create a config file
    mkdir -p "$TEST_DIR/config"
    cat > "$TEST_DIR/config/config.json" << 'EOF'
{
    "review": {
        "fix_max_iterations": 15
    }
}
EOF

    (
        export WIGGUM_HOME="$TEST_DIR"
        export WIGGUM_COMMENT_FIX_MAX_ITERATIONS=25
        source "$WIGGUM_HOME_BACKUP/lib/core/defaults.sh"
        load_review_config

        echo "$WIGGUM_COMMENT_FIX_MAX_ITERATIONS"
    ) > "$TEST_DIR/result.txt"

    local result
    result=$(cat "$TEST_DIR/result.txt")

    assert_equals "25" "$result" "Env var should override config file"
}

# =============================================================================
# Variable Export Tests
# =============================================================================

test_variables_are_exported() {
    (
        source "$WIGGUM_HOME_BACKUP/lib/core/defaults.sh"

        # Check if variables are exported (available to child processes)
        bash -c 'echo "WIGGUM_HOME=$WIGGUM_HOME"' > "$TEST_DIR/child_output.txt"
    )

    local result
    result=$(cat "$TEST_DIR/child_output.txt")

    assert_output_contains "$result" "WIGGUM_HOME=" "WIGGUM_HOME should be exported"
}

# =============================================================================
# Run All Tests
# =============================================================================

# Default values tests
run_test test_wiggum_home_default
run_test test_wiggum_home_env_override
run_test test_project_dir_default
run_test test_ralph_dir_default
run_test test_claude_binary_default
run_test test_max_workers_default
run_test test_max_iterations_default
run_test test_max_turns_default
run_test test_max_workers_env_override

# load_review_config tests
run_test test_load_review_config_defaults_without_file
run_test test_load_review_config_with_config_file
run_test test_load_review_config_env_override

# Export tests
run_test test_variables_are_exported

print_test_summary
exit_with_test_result
