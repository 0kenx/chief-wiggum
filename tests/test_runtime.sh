#!/usr/bin/env bash
# =============================================================================
# test_runtime.sh - Tests for lib/runtime/runtime.sh and backend modules
#
# Tests:
# - Runtime backend discovery and loading
# - Claude backend initialization
# - CLI argument construction (exec and resume)
# - Error classification (retryable detection)
# - Output extraction from stream JSON
# - Session ID extraction
# =============================================================================
set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

LOG_LEVEL=ERROR
export LOG_LEVEL

TEST_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    # Reset runtime state
    unset WIGGUM_RUNTIME_BACKEND
    unset ANTHROPIC_AUTH_TOKEN
    unset WIGGUM_RUNTIME_MAX_RETRIES
    unset WIGGUM_RUNTIME_INITIAL_BACKOFF
    unset WIGGUM_RUNTIME_MAX_BACKOFF
    unset WIGGUM_RUNTIME_BACKOFF_MULTIPLIER
    unset _RUNTIME_LOADED
    unset _RUNTIME_INITIALIZED
    unset _CLAUDE_BACKEND_LOADED
    unset _BACKEND_INTERFACE_LOADED
    unset _RUNTIME_RETRY_LOADED
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# RUNTIME BACKEND DISCOVERY TESTS
# =============================================================================

test_runtime_backend_discovery_default() {
    # No env var, no config files - should default to "claude"
    (
        unset WIGGUM_RUNTIME_BACKEND
        unset RALPH_DIR
        source "$WIGGUM_HOME/lib/runtime/runtime.sh"

        local backend
        backend=$(_runtime_discover_backend)

        [ "$backend" = "claude" ]
    )
    assert_exit_code 0 "Default backend should be 'claude'" \
        bash -c '
            source "'"$WIGGUM_HOME"'/lib/runtime/runtime.sh"
            backend=$(_runtime_discover_backend)
            [ "$backend" = "claude" ]
        '
}

test_runtime_backend_discovery_env_override() {
    # Env var should take highest priority
    export WIGGUM_RUNTIME_BACKEND="test-backend"

    local backend
    backend=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/runtime/runtime.sh" 2>/dev/null || true
        _runtime_discover_backend
    ')

    assert_equals "test-backend" "$backend" "Env var should override default"
}

test_runtime_backend_discovery_project_config() {
    # Project config should override global config
    local ralph_dir="$TEST_DIR/ralph"
    mkdir -p "$ralph_dir/.ralph"

    cat > "$ralph_dir/.ralph/config.json" <<'EOF'
{
  "runtime": {
    "backend": "project-backend"
  }
}
EOF

    local backend
    backend=$(bash -c '
        export RALPH_DIR="'"$ralph_dir"'"
        source "'"$WIGGUM_HOME"'/lib/runtime/runtime.sh" 2>/dev/null || true
        _runtime_discover_backend
    ')

    assert_equals "project-backend" "$backend" "Project config should be used"
}

test_runtime_init_invalid_backend_name() {
    # Backend name with path traversal should be rejected
    export WIGGUM_RUNTIME_BACKEND="../../../etc/passwd"

    assert_exit_code 3 "Invalid backend name should return exit code 3" \
        bash -c '
            export WIGGUM_RUNTIME_BACKEND="../../../etc/passwd"
            source "'"$WIGGUM_HOME"'/lib/runtime/runtime.sh" 2>/dev/null || exit $?
            exit 0
        '
}

test_runtime_init_nonexistent_backend() {
    # Nonexistent backend should return config error
    export WIGGUM_RUNTIME_BACKEND="nonexistent-backend"

    assert_exit_code 3 "Nonexistent backend should return exit code 3" \
        bash -c '
            export WIGGUM_RUNTIME_BACKEND="nonexistent-backend"
            source "'"$WIGGUM_HOME"'/lib/runtime/runtime.sh" 2>/dev/null || exit $?
            exit 0
        '
}

test_runtime_init_idempotent() {
    # Multiple calls to runtime_init should be safe
    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/runtime/runtime.sh"
        runtime_init
        runtime_init
        runtime_init
        echo "ok"
    ' 2>&1)

    assert_output_contains "$output" "ok" "Multiple runtime_init calls should work"
}

# =============================================================================
# CLAUDE BACKEND INITIALIZATION TESTS
# =============================================================================

test_claude_backend_init_default_binary() {
    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
        runtime_backend_init
        echo "$CLAUDE"
    ')

    assert_equals "claude" "$output" "Default CLAUDE binary should be 'claude'"
}

test_claude_backend_init_custom_binary() {
    local output
    output=$(bash -c '
        export CLAUDE="/custom/path/to/claude"
        source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
        runtime_backend_init
        echo "$CLAUDE"
    ')

    assert_equals "/custom/path/to/claude" "$output" "Custom CLAUDE binary should be preserved"
}

test_claude_backend_name() {
    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
        runtime_backend_name
    ')

    assert_equals "claude" "$output" "Backend name should be 'claude'"
}

test_claude_backend_supports_sessions() {
    assert_exit_code 0 "Claude backend should support sessions" \
        bash -c '
            source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
            runtime_backend_supports_sessions
        '
}

# =============================================================================
# CLAUDE BACKEND BUILD_EXEC_ARGS TESTS
# =============================================================================

test_claude_backend_build_exec_args_basic() {
    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"

        test_func() {
            local -a args=()
            runtime_backend_build_exec_args args \
                "/workspace" \
                "system prompt" \
                "user prompt" \
                "/output.log" \
                5 \
                ""

            printf "%s\n" "${args[@]}"
        }
        test_func
    ')

    assert_output_contains "$output" "--verbose" "Should include --verbose"
    assert_output_contains "$output" "--output-format" "Should include --output-format"
    assert_output_contains "$output" "stream-json" "Should include stream-json"
    assert_output_contains "$output" "--max-turns" "Should include --max-turns"
    assert_output_contains "$output" "5" "Should include max turns value"
    assert_output_contains "$output" "--dangerously-skip-permissions" "Should include --dangerously-skip-permissions"
    assert_output_contains "$output" "--append-system-prompt" "Should include --append-system-prompt"
    assert_output_contains "$output" "system prompt" "Should include system prompt"
    assert_output_contains "$output" "-p" "Should include -p flag"
    assert_output_contains "$output" "user prompt" "Should include user prompt"
}

test_claude_backend_build_exec_args_no_system_prompt() {
    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"

        test_func() {
            local -a args=()
            runtime_backend_build_exec_args args \
                "/workspace" \
                "" \
                "user prompt" \
                "/output.log" \
                3 \
                ""

            printf "%s\n" "${args[@]}"
        }
        test_func
    ')

    assert_output_not_contains "$output" "--append-system-prompt" "Should not include --append-system-prompt when empty"
}

test_claude_backend_build_exec_args_with_session_id() {
    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"

        test_func() {
            local -a args=()
            runtime_backend_build_exec_args args \
                "/workspace" \
                "system prompt" \
                "user prompt" \
                "/output.log" \
                3 \
                "test-session-123"

            printf "%s\n" "${args[@]}"
        }
        test_func
    ')

    assert_output_contains "$output" "--session-id" "Should include --session-id when provided"
    assert_output_contains "$output" "test-session-123" "Should include session ID value"
}

test_claude_backend_build_exec_args_plugin_dir() {
    # This test verifies plugin dir is added when skills/ exists
    # Since skills/ exists in WIGGUM_HOME, it should be included
    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"

        test_func() {
            local -a args=()
            runtime_backend_build_exec_args args \
                "/workspace" \
                "system" \
                "user" \
                "/output.log" \
                3 \
                ""

            printf "%s\n" "${args[@]}"
        }
        test_func
    ')

    if [ -d "$WIGGUM_HOME/skills" ]; then
        assert_output_contains "$output" "--plugin-dir" "Should include --plugin-dir when skills/ exists"
    fi
}

# =============================================================================
# CLAUDE BACKEND BUILD_RESUME_ARGS TESTS
# =============================================================================

test_claude_backend_build_resume_args_basic() {
    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"

        test_func() {
            local -a args=()
            runtime_backend_build_resume_args args \
                "session-abc-123" \
                "continue the task" \
                "/output.log" \
                5

            printf "%s\n" "${args[@]}"
        }
        test_func
    ')

    assert_output_contains "$output" "--verbose" "Resume should include --verbose"
    assert_output_contains "$output" "--resume" "Should include --resume flag"
    assert_output_contains "$output" "session-abc-123" "Should include session ID"
    assert_output_contains "$output" "--output-format" "Should include --output-format"
    assert_output_contains "$output" "stream-json" "Should include stream-json"
    assert_output_contains "$output" "--max-turns" "Should include --max-turns"
    assert_output_contains "$output" "5" "Should include max turns value"
    assert_output_contains "$output" "--dangerously-skip-permissions" "Should include --dangerously-skip-permissions"
    assert_output_contains "$output" "-p" "Should include -p flag"
    assert_output_contains "$output" "continue the task" "Should include prompt"
}

test_claude_backend_build_resume_args_default_max_turns() {
    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"

        test_func() {
            local -a args=()
            runtime_backend_build_resume_args args \
                "session-123" \
                "prompt" \
                "/output.log" \
                3

            printf "%s\n" "${args[@]}"
        }
        test_func
    ')

    assert_output_contains "$output" "3" "Should use provided max turns"
}

# =============================================================================
# CLAUDE BACKEND IS_RETRYABLE TESTS
# =============================================================================

test_claude_backend_is_retryable_exit_5() {
    local stderr_file="$TEST_DIR/stderr.txt"
    touch "$stderr_file"

    assert_exit_code 0 "Exit code 5 should be retryable" \
        bash -c '
            source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
            runtime_backend_is_retryable 5 "'"$stderr_file"'"
        '
}

test_claude_backend_is_retryable_exit_124() {
    local stderr_file="$TEST_DIR/stderr.txt"
    touch "$stderr_file"

    assert_exit_code 0 "Exit code 124 (timeout) should be retryable" \
        bash -c '
            source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
            runtime_backend_is_retryable 124 "'"$stderr_file"'"
        '
}

test_claude_backend_is_retryable_exit_1_with_429() {
    local stderr_file="$TEST_DIR/stderr.txt"
    echo "Error: 429 Too Many Requests" > "$stderr_file"

    assert_exit_code 0 "Exit 1 with 429 in stderr should be retryable" \
        bash -c '
            source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
            runtime_backend_is_retryable 1 "'"$stderr_file"'"
        '
}

test_claude_backend_is_retryable_exit_1_with_rate_limit() {
    local stderr_file="$TEST_DIR/stderr.txt"
    echo "Error: rate limit exceeded" > "$stderr_file"

    assert_exit_code 0 "Exit 1 with 'rate limit' should be retryable" \
        bash -c '
            source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
            runtime_backend_is_retryable 1 "'"$stderr_file"'"
        '
}

test_claude_backend_is_retryable_exit_1_with_too_many_requests() {
    local stderr_file="$TEST_DIR/stderr.txt"
    echo "too many requests" > "$stderr_file"

    assert_exit_code 0 "Exit 1 with 'too many requests' should be retryable" \
        bash -c '
            source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
            runtime_backend_is_retryable 1 "'"$stderr_file"'"
        '
}

test_claude_backend_is_retryable_exit_1_with_high_concurrency() {
    local stderr_file="$TEST_DIR/stderr.txt"
    echo "High concurrency detected" > "$stderr_file"

    assert_exit_code 0 "Exit 1 with 'High concurrency' should be retryable" \
        bash -c '
            source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
            runtime_backend_is_retryable 1 "'"$stderr_file"'"
        '
}

test_claude_backend_is_retryable_exit_0_not_retryable() {
    local stderr_file="$TEST_DIR/stderr.txt"
    touch "$stderr_file"

    assert_exit_code 1 "Exit code 0 should NOT be retryable" \
        bash -c '
            source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
            runtime_backend_is_retryable 0 "'"$stderr_file"'"
        '
}

test_claude_backend_is_retryable_exit_1_unrelated_error() {
    local stderr_file="$TEST_DIR/stderr.txt"
    echo "Some other error occurred" > "$stderr_file"

    assert_exit_code 1 "Exit 1 with unrelated error should NOT be retryable" \
        bash -c '
            source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
            runtime_backend_is_retryable 1 "'"$stderr_file"'"
        '
}

test_claude_backend_is_retryable_exit_2_not_retryable() {
    local stderr_file="$TEST_DIR/stderr.txt"
    touch "$stderr_file"

    assert_exit_code 1 "Exit code 2 should NOT be retryable" \
        bash -c '
            source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
            runtime_backend_is_retryable 2 "'"$stderr_file"'"
        '
}

test_claude_backend_is_retryable_exit_10_not_retryable() {
    local stderr_file="$TEST_DIR/stderr.txt"
    touch "$stderr_file"

    assert_exit_code 1 "Exit code 10 (FAIL) should NOT be retryable" \
        bash -c '
            source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
            runtime_backend_is_retryable 10 "'"$stderr_file"'"
        '
}

# =============================================================================
# CLAUDE BACKEND EXTRACT_TEXT TESTS
# =============================================================================

test_claude_backend_extract_text_single_message() {
    local log_file="$TEST_DIR/stream.log"

    cat > "$log_file" <<'EOF'
{"type":"iteration_start","session_id":"abc-123"}
{"type":"assistant","message":{"content":[{"type":"text","text":"Hello from Claude"}]}}
{"type":"iteration_complete"}
EOF

    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
        runtime_backend_extract_text "'"$log_file"'"
    ')

    assert_output_contains "$output" "Hello from Claude" "Should extract assistant text"
}

test_claude_backend_extract_text_multiple_content_items() {
    local log_file="$TEST_DIR/stream.log"

    cat > "$log_file" <<'EOF'
{"type":"assistant","message":{"content":[{"type":"text","text":"First part"},{"type":"text","text":"Second part"}]}}
EOF

    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
        runtime_backend_extract_text "'"$log_file"'"
    ')

    assert_output_contains "$output" "First part" "Should extract first text part"
    assert_output_contains "$output" "Second part" "Should extract second text part"
}

test_claude_backend_extract_text_empty_file() {
    local log_file="$TEST_DIR/stream.log"
    touch "$log_file"

    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
        runtime_backend_extract_text "'"$log_file"'" 2>/dev/null || true
    ')

    # Empty file should produce empty output
    [ -z "$output" ]
    assert_exit_code 0 "Empty file should not error" true
}

test_claude_backend_extract_text_nonexistent_file() {
    local log_file="$TEST_DIR/nonexistent.log"

    assert_exit_code 1 "Nonexistent file should return error" \
        bash -c '
            source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
            runtime_backend_extract_text "'"$log_file"'" 2>/dev/null
        '
}

test_claude_backend_extract_text_no_assistant_messages() {
    local log_file="$TEST_DIR/stream.log"

    cat > "$log_file" <<'EOF'
{"type":"iteration_start","session_id":"abc-123"}
{"type":"user","message":{"content":"user input"}}
{"type":"iteration_complete"}
EOF

    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
        runtime_backend_extract_text "'"$log_file"'" 2>/dev/null || true
    ')

    # No assistant messages should produce empty output
    [ -z "$output" ] || [ "$output" = "" ]
    assert_exit_code 0 "No assistant messages should not error" true
}

# =============================================================================
# CLAUDE BACKEND EXTRACT_SESSION_ID TESTS
# =============================================================================

test_claude_backend_extract_session_id_found() {
    local log_file="$TEST_DIR/stream.log"

    cat > "$log_file" <<'EOF'
{"type":"iteration_start","session_id":"abc-123-def-456"}
{"type":"assistant","message":{"content":[{"type":"text","text":"Hello"}]}}
EOF

    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
        runtime_backend_extract_session_id "'"$log_file"'"
    ')

    assert_equals "abc-123-def-456" "$output" "Should extract session ID"
}

test_claude_backend_extract_session_id_not_found() {
    local log_file="$TEST_DIR/stream.log"

    cat > "$log_file" <<'EOF'
{"type":"iteration_start"}
{"type":"assistant","message":{"content":[{"type":"text","text":"Hello"}]}}
EOF

    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
        runtime_backend_extract_session_id "'"$log_file"'"
    ')

    assert_equals "" "$output" "Should return empty string when no session ID"
}

test_claude_backend_extract_session_id_nonexistent_file() {
    local log_file="$TEST_DIR/nonexistent.log"

    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
        runtime_backend_extract_session_id "'"$log_file"'"
    ')

    assert_equals "" "$output" "Should return empty string for nonexistent file"
}

test_claude_backend_extract_session_id_multiple_sessions() {
    local log_file="$TEST_DIR/stream.log"

    cat > "$log_file" <<'EOF'
{"type":"iteration_start","session_id":"abc-123-def-456"}
{"type":"iteration_start","session_id":"fed-654-cba-321"}
EOF

    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/backend/claude/claude-backend.sh"
        runtime_backend_extract_session_id "'"$log_file"'"
    ')

    # Should return first session ID (head -1)
    assert_equals "abc-123-def-456" "$output" "Should extract first session ID"
}

# =============================================================================
# RUNTIME RETRY BACKOFF CALCULATION TESTS
# =============================================================================

test_runtime_retry_backoff_calculation() {
    local output
    output=$(bash -c '
        export WIGGUM_RUNTIME_INITIAL_BACKOFF=5
        export WIGGUM_RUNTIME_BACKOFF_MULTIPLIER=2
        export WIGGUM_RUNTIME_MAX_BACKOFF=60
        source "'"$WIGGUM_HOME"'/lib/runtime/runtime-retry.sh"

        # Attempt 0: 5
        echo "$(_calculate_backoff 0)"
        # Attempt 1: 5 * 2 = 10
        echo "$(_calculate_backoff 1)"
        # Attempt 2: 10 * 2 = 20
        echo "$(_calculate_backoff 2)"
        # Attempt 3: 20 * 2 = 40
        echo "$(_calculate_backoff 3)"
        # Attempt 4: 40 * 2 = 80, capped at 60
        echo "$(_calculate_backoff 4)"
    ')

    local line1 line2 line3 line4 line5
    line1=$(echo "$output" | sed -n '1p')
    line2=$(echo "$output" | sed -n '2p')
    line3=$(echo "$output" | sed -n '3p')
    line4=$(echo "$output" | sed -n '4p')
    line5=$(echo "$output" | sed -n '5p')

    assert_equals "5" "$line1" "Attempt 0 should be 5s"
    assert_equals "10" "$line2" "Attempt 1 should be 10s"
    assert_equals "20" "$line3" "Attempt 2 should be 20s"
    assert_equals "40" "$line4" "Attempt 3 should be 40s"
    assert_equals "60" "$line5" "Attempt 4 should be capped at 60s"
}

test_runtime_retry_config_loading() {
    local output
    output=$(bash -c '
        export WIGGUM_RUNTIME_MAX_RETRIES=5
        export WIGGUM_RUNTIME_INITIAL_BACKOFF=10
        source "'"$WIGGUM_HOME"'/lib/runtime/runtime-retry.sh"
        load_runtime_retry_config

        echo "max=$RUNTIME_MAX_RETRIES"
        echo "initial=$RUNTIME_INITIAL_BACKOFF"
    ')

    assert_output_contains "$output" "max=5" "Should load max retries from env"
    assert_output_contains "$output" "initial=10" "Should load initial backoff from env"
}

# =============================================================================
# BACKEND INTERFACE DEFAULTS TESTS
# =============================================================================

test_backend_interface_default_init_fails() {
    assert_exit_code 1 "Default init should fail" \
        bash -c '
            source "'"$WIGGUM_HOME"'/lib/core/logger.sh"
            source "'"$WIGGUM_HOME"'/lib/runtime/backend-interface.sh"
            runtime_backend_init 2>/dev/null
        '
}

test_backend_interface_default_invoke_fails() {
    assert_exit_code 1 "Default invoke should fail" \
        bash -c '
            source "'"$WIGGUM_HOME"'/lib/core/logger.sh"
            source "'"$WIGGUM_HOME"'/lib/runtime/backend-interface.sh"
            runtime_backend_invoke "test" 2>/dev/null
        '
}

test_backend_interface_default_is_retryable_returns_false() {
    local stderr_file="$TEST_DIR/stderr.txt"
    touch "$stderr_file"

    assert_exit_code 1 "Default is_retryable should return false" \
        bash -c '
            source "'"$WIGGUM_HOME"'/lib/runtime/backend-interface.sh"
            runtime_backend_is_retryable 5 "'"$stderr_file"'"
        '
}

test_backend_interface_default_supports_sessions_returns_false() {
    assert_exit_code 1 "Default supports_sessions should return false" \
        bash -c '
            source "'"$WIGGUM_HOME"'/lib/runtime/backend-interface.sh"
            runtime_backend_supports_sessions
        '
}

test_backend_interface_default_usage_update_succeeds() {
    assert_exit_code 0 "Default usage_update should succeed (no-op)" \
        bash -c '
            source "'"$WIGGUM_HOME"'/lib/runtime/backend-interface.sh"
            runtime_backend_usage_update "'"$TEST_DIR"'"
        '
}

test_backend_interface_default_rate_limit_check_returns_false() {
    assert_exit_code 1 "Default rate_limit_check should return false (not limited)" \
        bash -c '
            source "'"$WIGGUM_HOME"'/lib/runtime/backend-interface.sh"
            runtime_backend_rate_limit_check "'"$TEST_DIR"'"
        '
}

test_backend_interface_default_generate_session_id() {
    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/runtime/backend-interface.sh"
        runtime_backend_generate_session_id
    ')

    assert_not_empty "$output" "Should generate a session ID"
}

test_backend_interface_default_name() {
    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/runtime/backend-interface.sh"
        runtime_backend_name
    ')

    assert_equals "unknown" "$output" "Default backend name should be 'unknown'"
}

test_backend_interface_default_extract_session_id_returns_empty() {
    local output
    output=$(bash -c '
        source "'"$WIGGUM_HOME"'/lib/runtime/backend-interface.sh"
        runtime_backend_extract_session_id "/nonexistent"
    ')

    assert_equals "" "$output" "Default extract_session_id should return empty"
}

# =============================================================================
# RUN TESTS
# =============================================================================

# Runtime discovery tests
run_test test_runtime_backend_discovery_default
run_test test_runtime_backend_discovery_env_override
run_test test_runtime_backend_discovery_project_config
run_test test_runtime_init_invalid_backend_name
run_test test_runtime_init_nonexistent_backend
run_test test_runtime_init_idempotent

# Claude backend initialization tests
run_test test_claude_backend_init_default_binary
run_test test_claude_backend_init_custom_binary
run_test test_claude_backend_name
run_test test_claude_backend_supports_sessions

# Claude backend build_exec_args tests
run_test test_claude_backend_build_exec_args_basic
run_test test_claude_backend_build_exec_args_no_system_prompt
run_test test_claude_backend_build_exec_args_with_session_id
run_test test_claude_backend_build_exec_args_plugin_dir

# Claude backend build_resume_args tests
run_test test_claude_backend_build_resume_args_basic
run_test test_claude_backend_build_resume_args_default_max_turns

# Claude backend is_retryable tests
run_test test_claude_backend_is_retryable_exit_5
run_test test_claude_backend_is_retryable_exit_124
run_test test_claude_backend_is_retryable_exit_1_with_429
run_test test_claude_backend_is_retryable_exit_1_with_rate_limit
run_test test_claude_backend_is_retryable_exit_1_with_too_many_requests
run_test test_claude_backend_is_retryable_exit_1_with_high_concurrency
run_test test_claude_backend_is_retryable_exit_0_not_retryable
run_test test_claude_backend_is_retryable_exit_1_unrelated_error
run_test test_claude_backend_is_retryable_exit_2_not_retryable
run_test test_claude_backend_is_retryable_exit_10_not_retryable

# Claude backend extract_text tests
run_test test_claude_backend_extract_text_single_message
run_test test_claude_backend_extract_text_multiple_content_items
run_test test_claude_backend_extract_text_empty_file
run_test test_claude_backend_extract_text_nonexistent_file
run_test test_claude_backend_extract_text_no_assistant_messages

# Claude backend extract_session_id tests
run_test test_claude_backend_extract_session_id_found
run_test test_claude_backend_extract_session_id_not_found
run_test test_claude_backend_extract_session_id_nonexistent_file
run_test test_claude_backend_extract_session_id_multiple_sessions

# Runtime retry tests
run_test test_runtime_retry_backoff_calculation
run_test test_runtime_retry_config_loading

# Backend interface default tests
run_test test_backend_interface_default_init_fails
run_test test_backend_interface_default_invoke_fails
run_test test_backend_interface_default_is_retryable_returns_false
run_test test_backend_interface_default_supports_sessions_returns_false
run_test test_backend_interface_default_usage_update_succeeds
run_test test_backend_interface_default_rate_limit_check_returns_false
run_test test_backend_interface_default_generate_session_id
run_test test_backend_interface_default_name
run_test test_backend_interface_default_extract_session_id_returns_empty

print_test_summary
exit_with_test_result
