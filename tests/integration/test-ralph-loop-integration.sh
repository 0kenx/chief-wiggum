#!/usr/bin/env bash
# =============================================================================
# Ralph Loop Integration Test
#
# Tests the actual ralph loop with mock claude configured for multiple iterations:
# - Correct number of claude invocations
# - Session resumption uses previous session ID
# - Completion callback fires
# - Exit conditions respected (max_iterations, STOP decision)
# - Checkpoint and summary files created per iteration
# =============================================================================

set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$TESTS_DIR/mocks/mock-helpers.sh"

TEST_DIR=""
WORKSPACE=""
OUTPUT_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    WORKSPACE="$TEST_DIR/workspace"
    OUTPUT_DIR="$TEST_DIR/output"
    mkdir -p "$WORKSPACE" "$OUTPUT_DIR"

    # Setup mock claude
    mock_setup
    export CLAUDE="$TESTS_DIR/mocks/mock-claude.sh"
    export MOCK_CLAUDE_RESPONSE="Working on the task..."
    export MOCK_CLAUDE_DELAY="0"
    export LOG_FILE="$TEST_DIR/test.log"
}

teardown() {
    mock_teardown
    rm -rf "$TEST_DIR"
}

# =============================================================================
# Test: Ralph loop invokes claude correct number of times with max_iterations
# =============================================================================
test_ralph_loop_max_iterations() {
    source "$WIGGUM_HOME/lib/claude/run-claude-ralph-loop.sh"

    # Define callbacks
    _test_user_prompt() {
        echo "Continue working on iteration $1"
    }
    _test_never_complete() {
        return 1  # Never complete - loop should hit max_iterations
    }

    # Run loop with max 3 iterations
    local exit_code=0
    run_ralph_loop "$WORKSPACE" "You are a test agent" \
        "_test_user_prompt" "_test_never_complete" \
        3 5 "$OUTPUT_DIR" "test" || exit_code=$?

    # Should return 1 (max iterations reached)
    assert_equals "1" "$exit_code" "Should return 1 when max iterations reached"

    # Should have invoked claude 6 times (3 work + 3 summary)
    local invocation_count
    invocation_count=$(mock_get_invocation_count)
    assert_equals "6" "$invocation_count" "Should have 6 invocations (3 work + 3 summary)"
}

# =============================================================================
# Test: Ralph loop stops when completion check passes
# =============================================================================
test_ralph_loop_completion_callback() {
    source "$WIGGUM_HOME/lib/claude/run-claude-ralph-loop.sh"

    local completion_file="$TEST_DIR/complete_after"
    echo "2" > "$completion_file"

    _test_user_prompt_2() {
        echo "Continue working"
    }

    # Complete after 2 iterations
    _test_complete_after_2() {
        local current
        current=$(cat "$completion_file")
        if [ "$current" -le 0 ]; then
            return 0  # Complete
        fi
        echo $((current - 1)) > "$completion_file"
        return 1  # Not yet
    }

    local exit_code=0
    run_ralph_loop "$WORKSPACE" "You are a test agent" \
        "_test_user_prompt_2" "_test_complete_after_2" \
        10 5 "$OUTPUT_DIR" "test" || exit_code=$?

    # Should return 0 (completed successfully)
    assert_equals "0" "$exit_code" "Should return 0 when completion check passes"

    # Should have exactly 4 invocations (2 work + 2 summary)
    local invocation_count
    invocation_count=$(mock_get_invocation_count)
    assert_equals "4" "$invocation_count" "Should have 4 invocations (2 work + 2 summary)"
}

# =============================================================================
# Test: Session resumption uses --resume flag for summaries
# =============================================================================
test_ralph_loop_session_resumption() {
    source "$WIGGUM_HOME/lib/claude/run-claude-ralph-loop.sh"

    _test_user_prompt_3() {
        echo "Do work"
    }
    _test_complete_after_1() {
        # Complete after first check (runs at start of iteration 1)
        [ -f "$TEST_DIR/ran_once" ] && return 0
        touch "$TEST_DIR/ran_once"
        return 1
    }

    run_ralph_loop "$WORKSPACE" "System prompt" \
        "_test_user_prompt_3" "_test_complete_after_1" \
        5 5 "$OUTPUT_DIR" "test" || true

    # Check that the summary invocation used --resume
    local invocation_count
    invocation_count=$(mock_get_invocation_count)
    assert_greater_than "$invocation_count" 1 "Should have at least 2 invocations"

    # Second invocation (summary) should have --resume flag
    local args
    args=$(mock_get_args 2)
    assert_output_contains "$args" "--resume" "Summary invocation should use --resume"
}

# =============================================================================
# Test: Checkpoint files created per iteration
# =============================================================================
test_ralph_loop_creates_checkpoints() {
    source "$WIGGUM_HOME/lib/claude/run-claude-ralph-loop.sh"

    _test_user_prompt_4() {
        echo "Work on iteration $1"
    }
    _test_never_complete_2() {
        return 1
    }

    run_ralph_loop "$WORKSPACE" "System prompt" \
        "_test_user_prompt_4" "_test_never_complete_2" \
        2 5 "$OUTPUT_DIR" "test" || true

    # Checkpoint files should exist (namespaced by run_id)
    local checkpoint_dir
    checkpoint_dir=$(find "$OUTPUT_DIR/checkpoints" -mindepth 1 -maxdepth 1 -type d 2>/dev/null | head -1)
    assert_not_empty "$checkpoint_dir" "Checkpoint run directory should be created"
    assert_file_exists "$checkpoint_dir/checkpoint-0.json" \
        "Checkpoint for iteration 0 should exist"
    assert_file_exists "$checkpoint_dir/checkpoint-1.json" \
        "Checkpoint for iteration 1 should exist"

    # Verify checkpoint JSON is valid
    local status
    status=$(jq -r '.status' "$checkpoint_dir/checkpoint-0.json" 2>/dev/null)
    assert_not_equals "" "$status" "Checkpoint should have a status field"
}

# =============================================================================
# Test: Summary files created per iteration
# =============================================================================
test_ralph_loop_creates_summaries() {
    source "$WIGGUM_HOME/lib/claude/run-claude-ralph-loop.sh"

    _test_user_prompt_5() {
        echo "Summarize iteration $1"
    }
    _test_never_complete_3() {
        return 1
    }

    run_ralph_loop "$WORKSPACE" "System prompt" \
        "_test_user_prompt_5" "_test_never_complete_3" \
        2 5 "$OUTPUT_DIR" "test" || true

    # Summary text files should exist
    assert_file_exists "$OUTPUT_DIR/summaries/test-0-summary.txt" \
        "Summary for iteration 0 should exist"
    assert_file_exists "$OUTPUT_DIR/summaries/test-1-summary.txt" \
        "Summary for iteration 1 should exist"
}

# =============================================================================
# Test: Log files created per iteration
# =============================================================================
test_ralph_loop_creates_logs() {
    source "$WIGGUM_HOME/lib/claude/run-claude-ralph-loop.sh"

    _test_user_prompt_6() {
        echo "Log iteration $1"
    }
    _test_never_complete_4() {
        return 1
    }

    run_ralph_loop "$WORKSPACE" "System prompt" \
        "_test_user_prompt_6" "_test_never_complete_4" \
        1 5 "$OUTPUT_DIR" "test" || true

    # Log directory should contain iteration log
    local log_count
    log_count=$(find "$OUTPUT_DIR/logs" -name "test-0-*.log" -not -name "*-summary.log" | wc -l)
    assert_greater_than "$log_count" 0 "Should have at least 1 iteration log file"

    # Summary log should also exist
    local summary_log_count
    summary_log_count=$(find "$OUTPUT_DIR/logs" -name "*-summary.log" | wc -l)
    assert_greater_than "$summary_log_count" 0 "Should have at least 1 summary log file"
}

# =============================================================================
# Test: Work log index is created
# =============================================================================
test_ralph_loop_creates_work_log() {
    source "$WIGGUM_HOME/lib/claude/run-claude-ralph-loop.sh"

    _test_user_prompt_7() {
        echo "Work log test"
    }
    _test_never_complete_5() {
        return 1
    }

    run_ralph_loop "$WORKSPACE" "System prompt" \
        "_test_user_prompt_7" "_test_never_complete_5" \
        1 5 "$OUTPUT_DIR" "test" || true

    # Work log is namespaced by run_id (RALPH_RUN_ID is exported from ralph loop)
    local work_log_dir
    work_log_dir=$(find "$OUTPUT_DIR/work-log" -mindepth 1 -maxdepth 1 -type d 2>/dev/null | head -1)
    assert_not_empty "$work_log_dir" "Work log run directory should be created"
    assert_file_exists "$work_log_dir/index.md" \
        "Work log index should be created"
    assert_file_contains "$work_log_dir/index.md" "Work Log" \
        "Work log index should have header"
}

# =============================================================================
# Test: Ralph loop validates callback functions exist
# =============================================================================
test_ralph_loop_validates_callbacks() {
    source "$WIGGUM_HOME/lib/claude/run-claude-ralph-loop.sh"

    local exit_code=0
    run_ralph_loop "$WORKSPACE" "System prompt" \
        "_nonexistent_prompt_fn" "_nonexistent_check_fn" \
        5 5 "$OUTPUT_DIR" "test" 2>/dev/null || exit_code=$?

    assert_equals "1" "$exit_code" "Should fail with non-existent callback function"
}

# =============================================================================
# Run all tests
# =============================================================================
run_test test_ralph_loop_max_iterations
run_test test_ralph_loop_completion_callback
run_test test_ralph_loop_session_resumption
run_test test_ralph_loop_creates_checkpoints
run_test test_ralph_loop_creates_summaries
run_test test_ralph_loop_creates_logs
run_test test_ralph_loop_creates_work_log
run_test test_ralph_loop_validates_callbacks

print_test_summary
exit_with_test_result
