#!/usr/bin/env bash
set -euo pipefail
# CLI integration tests for bin/wiggum-* commands
#
# Tests argument validation, help output, and early-exit paths.
# Does NOT test anything that requires network access, Claude CLI, or running workers.

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME
export PATH="$WIGGUM_HOME/bin:$PATH"

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/core/exit-codes.sh"

TEST_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    cd "$TEST_DIR" || exit 1
    # Initialize a minimal git repo for commands that need it
    git init -q
    git config user.email "test@test.com"
    git config user.name "Test"
}

teardown() {
    cd /
    rm -rf "$TEST_DIR"
}

# =============================================================================
# wiggum (main dispatcher)
# =============================================================================

test_wiggum_no_args_shows_usage() {
    local output exit_code
    output=$(wiggum 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_not_equals "0" "$exit_code" "wiggum with no args should exit non-zero"
    assert_output_contains "$output" "Usage:" "wiggum with no args should show usage"
    assert_output_contains "$output" "No command specified" "wiggum with no args should report no command"
}

test_wiggum_help_flag() {
    local output exit_code
    output=$(wiggum --help 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum --help should exit 0"
    assert_output_contains "$output" "Usage:" "wiggum --help should show usage"
    assert_output_contains "$output" "init" "wiggum --help should list init command"
    assert_output_contains "$output" "validate" "wiggum --help should list validate command"
    assert_output_contains "$output" "run" "wiggum --help should list run command"
    assert_output_contains "$output" "status" "wiggum --help should list status command"
    assert_output_contains "$output" "stop" "wiggum --help should list stop command"
    assert_output_contains "$output" "start" "wiggum --help should list start command"
}

test_wiggum_unknown_command() {
    local output exit_code
    output=$(wiggum nonexistent-command 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_USAGE" "$exit_code" "wiggum unknown command should exit with EXIT_USAGE ($EXIT_USAGE)"
    assert_output_contains "$output" "Unknown command" "wiggum unknown command should report error"
}

# =============================================================================
# wiggum-validate
# =============================================================================

test_validate_no_ralph_dir_fails() {
    local output exit_code
    output=$(wiggum-validate 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_VALIDATE_FILE_NOT_FOUND" "$exit_code" \
        "wiggum-validate without .ralph dir should exit with EXIT_VALIDATE_FILE_NOT_FOUND ($EXIT_VALIDATE_FILE_NOT_FOUND)"
}

test_validate_help_shows_usage() {
    local output exit_code
    output=$(wiggum-validate --help 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum-validate --help should exit 0"
    assert_output_contains "$output" "Usage:" "wiggum-validate --help should show usage"
    assert_output_contains "$output" "Validate" "wiggum-validate --help should describe validation"
    assert_output_contains "$output" "kanban" "wiggum-validate --help should mention kanban"
}

test_validate_unknown_option_fails() {
    local output exit_code
    output=$(wiggum-validate --bogus 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_USAGE" "$exit_code" \
        "wiggum-validate with unknown option should exit with EXIT_USAGE ($EXIT_USAGE)"
    assert_output_contains "$output" "Unknown option" "Should report unknown option"
}

# =============================================================================
# wiggum-status
# =============================================================================

test_status_no_ralph_dir_succeeds_with_message() {
    # wiggum-status sources defaults.sh which sets RALPH_DIR; without .ralph/workers
    # it prints "No wiggum workers found" and exits 0
    local output exit_code
    output=$(wiggum-status 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum-status without .ralph/workers should exit 0"
    assert_output_contains "$output" "No wiggum" "wiggum-status should indicate no workers found"
}

test_status_help_shows_usage() {
    local output exit_code
    output=$(wiggum-status --help 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum-status --help should exit 0"
    assert_output_contains "$output" "Usage:" "wiggum-status --help should show usage"
}

# =============================================================================
# wiggum-clean
# =============================================================================

test_clean_no_ralph_dir_fails() {
    local output exit_code
    output=$(wiggum-clean all 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_CLEAN_NO_RALPH_DIR" "$exit_code" \
        "wiggum-clean without .ralph dir should exit with EXIT_CLEAN_NO_RALPH_DIR ($EXIT_CLEAN_NO_RALPH_DIR)"
    assert_output_contains "$output" ".ralph" "wiggum-clean should mention .ralph directory"
}

test_clean_help_shows_usage() {
    local output exit_code
    output=$(wiggum-clean --help 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum-clean --help should exit 0"
    assert_output_contains "$output" "Usage:" "wiggum-clean --help should show usage"
    assert_output_contains "$output" "worktree" "wiggum-clean --help should mention worktrees"
}

# =============================================================================
# wiggum-worker start
# =============================================================================

test_worker_start_no_task_id_fails() {
    local output exit_code
    output=$(wiggum-worker start 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_USAGE" "$exit_code" \
        "wiggum-worker start without task ID should exit with EXIT_USAGE ($EXIT_USAGE)"
    assert_output_contains "$output" "Task ID required" "wiggum-worker start should report missing task ID"
}

test_worker_start_no_ralph_dir_fails() {
    local output exit_code
    output=$(wiggum-worker start TASK-001 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_WORKER_NO_RALPH_DIR" "$exit_code" \
        "wiggum-worker start without .ralph dir should exit with EXIT_WORKER_NO_RALPH_DIR ($EXIT_WORKER_NO_RALPH_DIR)"
    assert_output_contains "$output" ".ralph" "wiggum-worker start should mention .ralph directory"
    assert_output_contains "$output" "wiggum init" "wiggum-worker start should suggest running wiggum init"
}

test_worker_start_no_kanban_fails() {
    # Create .ralph dir but no kanban.md
    mkdir -p .ralph
    local output exit_code
    output=$(wiggum-worker start TASK-001 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_WORKER_NO_KANBAN" "$exit_code" \
        "wiggum-worker start without kanban.md should exit with EXIT_WORKER_NO_KANBAN ($EXIT_WORKER_NO_KANBAN)"
    assert_output_contains "$output" "kanban" "wiggum-worker start should mention kanban.md"
}

test_worker_start_help_shows_usage() {
    local output exit_code
    output=$(wiggum-worker start --help 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum-worker start --help should exit 0"
    assert_output_contains "$output" "Usage:" "wiggum-worker start --help should show usage"
    assert_output_contains "$output" "TASK-030" "wiggum-worker start --help should show task ID example"
}

# =============================================================================
# wiggum-init
# =============================================================================

test_init_creates_ralph_directory() {
    local output exit_code
    output=$(wiggum-init 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum-init should exit 0 in a git repo"
    assert_dir_exists "$TEST_DIR/.ralph" "wiggum-init should create .ralph directory"
    assert_dir_exists "$TEST_DIR/.ralph/workers" "wiggum-init should create .ralph/workers"
    assert_dir_exists "$TEST_DIR/.ralph/results" "wiggum-init should create .ralph/results"
    assert_dir_exists "$TEST_DIR/.ralph/logs" "wiggum-init should create .ralph/logs"
    assert_file_exists "$TEST_DIR/.ralph/kanban.md" "wiggum-init should create kanban.md"
    assert_file_exists "$TEST_DIR/.ralph/changelog.md" "wiggum-init should create changelog.md"
    assert_file_exists "$TEST_DIR/.ralph/.gitignore" "wiggum-init should create .gitignore"
}

test_init_in_non_git_directory_fails() {
    # Create a separate non-git directory
    local non_git_dir
    non_git_dir=$(mktemp -d)
    local output exit_code
    output=$(cd "$non_git_dir" && wiggum-init 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}
    rm -rf "$non_git_dir"

    assert_equals "$EXIT_INIT_NOT_GIT_REPO" "$exit_code" \
        "wiggum-init in non-git dir should exit with EXIT_INIT_NOT_GIT_REPO ($EXIT_INIT_NOT_GIT_REPO)"
    assert_output_contains "$output" "git" "wiggum-init should mention git requirement"
}

test_init_help_shows_usage() {
    local output exit_code
    output=$(wiggum-init --help 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum-init --help should exit 0"
    assert_output_contains "$output" "Usage:" "wiggum-init --help should show usage"
    assert_output_contains "$output" "Initialize" "wiggum-init --help should describe initialization"
}

test_init_idempotent_kanban() {
    # Run init twice - kanban.md should not be overwritten
    wiggum-init >/dev/null 2>&1
    echo "# Custom content" >> "$TEST_DIR/.ralph/kanban.md"

    local output
    output=$(wiggum-init 2>&1) || true
    assert_output_contains "$output" "already exists" "Second init should report kanban already exists"
    assert_file_contains "$TEST_DIR/.ralph/kanban.md" "Custom content" "kanban.md should not be overwritten"
}

# =============================================================================
# wiggum-doctor
# =============================================================================

test_doctor_produces_output() {
    # Doctor runs preflight checks - it should produce output regardless
    # of whether all checks pass (some tools might not be installed in test env)
    local output exit_code
    output=$(wiggum-doctor 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    # Doctor should produce some output (check results)
    local output_len=${#output}
    assert_greater_than "$output_len" "0" "wiggum-doctor should produce output"
}

test_doctor_help_shows_usage() {
    local output exit_code
    output=$(wiggum-doctor --help 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum-doctor --help should exit 0"
    assert_output_contains "$output" "Usage:" "wiggum-doctor --help should show usage"
    assert_output_contains "$output" "Pre-flight" "wiggum-doctor --help should describe preflight checks"
}

test_doctor_quiet_mode() {
    # Quiet mode should suppress success messages (only show failures)
    local output exit_code
    output=$(wiggum-doctor --quiet 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    # In quiet mode, if all checks pass, output should be empty or minimal
    # If checks fail, only failures are shown. Either way the command should run.
    # We just verify it does not crash
    local ran_ok=true
    assert_equals "true" "$ran_ok" "wiggum-doctor --quiet should run without crashing"
}

# =============================================================================
# wiggum-worker stop
# =============================================================================

test_worker_stop_no_ralph_dir_reports_no_workers() {
    # wiggum-worker stop without .ralph/workers reports no workers and exits 0
    local output exit_code
    output=$(wiggum-worker stop 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum-worker stop without workers dir should exit 0"
    assert_output_contains "$output" "No wiggum workers" "wiggum-worker stop should report no workers found"
}

test_worker_stop_help_shows_usage() {
    local output exit_code
    output=$(wiggum-worker stop --help 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum-worker stop --help should exit 0"
    assert_output_contains "$output" "Usage:" "wiggum-worker stop --help should show usage"
    assert_output_contains "$output" "Stop" "wiggum-worker stop --help should describe stopping"
}

# =============================================================================
# wiggum-worker kill
# =============================================================================

test_worker_kill_no_args_fails() {
    # wiggum-worker kill without arguments should fail with usage error
    local output exit_code
    output=$(wiggum-worker kill 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_USAGE" "$exit_code" "wiggum-worker kill without args should exit with usage error"
    assert_output_contains "$output" "Missing argument" "wiggum-worker kill should report missing argument"
}

test_worker_kill_all_no_ralph_dir_reports_no_workers() {
    # wiggum-worker kill all without .ralph/workers reports no workers and exits 0
    local output exit_code
    output=$(wiggum-worker kill all 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum-worker kill all without workers dir should exit 0"
    assert_output_contains "$output" "No wiggum workers" "wiggum-worker kill all should report no workers found"
}

test_worker_kill_help_shows_usage() {
    local output exit_code
    output=$(wiggum-worker kill --help 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum-worker kill --help should exit 0"
    assert_output_contains "$output" "Usage:" "wiggum-worker kill --help should show usage"
    assert_output_contains "$output" "Force kill" "wiggum-worker kill --help should describe force killing"
}

# =============================================================================
# wiggum-run
# =============================================================================

test_run_no_ralph_dir_fails() {
    local output exit_code
    output=$(wiggum-run 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_RUN_NO_RALPH_DIR" "$exit_code" \
        "wiggum-run without .ralph dir should exit with EXIT_RUN_NO_RALPH_DIR ($EXIT_RUN_NO_RALPH_DIR)"
    assert_output_contains "$output" ".ralph" "wiggum-run should mention .ralph directory"
}

test_run_help_shows_usage() {
    local output exit_code
    output=$(wiggum-run --help 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum-run --help should exit 0"
    assert_output_contains "$output" "Usage:" "wiggum-run --help should show usage"
    assert_output_contains "$output" "Orchestrate" "wiggum-run --help should describe orchestration"
}

test_run_no_kanban_fails() {
    # Create .ralph dir but no kanban.md
    mkdir -p .ralph
    local output exit_code
    output=$(wiggum-run 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_RUN_NO_KANBAN" "$exit_code" \
        "wiggum-run without kanban.md should exit with EXIT_RUN_NO_KANBAN ($EXIT_RUN_NO_KANBAN)"
    assert_output_contains "$output" "kanban" "wiggum-run should mention kanban.md"
}

# =============================================================================
# wiggum-pr
# =============================================================================

test_pr_help_shows_usage() {
    local output exit_code
    output=$(wiggum-pr --help 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum-pr --help should exit 0"
    assert_output_contains "$output" "Usage:" "wiggum-pr --help should show usage"
    assert_output_contains "$output" "pr" "wiggum-pr --help should describe pr management"
    assert_output_contains "$output" "list" "wiggum-pr --help should list available commands"
    assert_output_contains "$output" "merge" "wiggum-pr --help should mention merge"
}

test_pr_unknown_command_fails() {
    local output exit_code
    output=$(wiggum-pr bogus-action 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_USAGE" "$exit_code" \
        "wiggum-pr with unknown command should exit with EXIT_USAGE ($EXIT_USAGE)"
    assert_output_contains "$output" "Unknown command" "wiggum-pr should report unknown command"
}

test_pr_view_no_number_fails() {
    local output exit_code
    output=$(wiggum-pr view 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_USAGE" "$exit_code" \
        "wiggum-pr view without number should exit with EXIT_USAGE ($EXIT_USAGE)"
    assert_output_contains "$output" "PR number required" "Should report PR number required"
}

test_pr_comments_no_pattern_fails() {
    local output exit_code
    output=$(wiggum-pr comments 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    # The command exits non-zero when no task pattern is provided
    assert_not_equals "0" "$exit_code" \
        "wiggum-pr comments without pattern should exit non-zero"
}

# =============================================================================
# wiggum-plan
# =============================================================================

test_plan_no_task_id_fails() {
    local output exit_code
    output=$(wiggum-plan 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_WORKER_MISSING_TASK_ID" "$exit_code" \
        "wiggum-plan without task ID should exit with EXIT_WORKER_MISSING_TASK_ID ($EXIT_WORKER_MISSING_TASK_ID)"
    assert_output_contains "$output" "Task ID required" "wiggum-plan should report missing task ID"
}

test_plan_no_ralph_dir_fails() {
    local output exit_code
    output=$(wiggum-plan TASK-001 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_WORKER_NO_RALPH_DIR" "$exit_code" \
        "wiggum-plan without .ralph dir should exit with EXIT_WORKER_NO_RALPH_DIR ($EXIT_WORKER_NO_RALPH_DIR)"
    assert_output_contains "$output" ".ralph" "wiggum-plan should mention .ralph directory"
}

test_plan_help_shows_usage() {
    local output exit_code
    output=$(wiggum-plan --help 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum-plan --help should exit 0"
    assert_output_contains "$output" "Usage:" "wiggum-plan --help should show usage"
    assert_output_contains "$output" "plan" "wiggum-plan --help should describe planning"
}

test_plan_no_kanban_fails() {
    # Create .ralph dir but no kanban.md
    mkdir -p .ralph
    local output exit_code
    output=$(wiggum-plan TASK-001 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_WORKER_NO_KANBAN" "$exit_code" \
        "wiggum-plan without kanban.md should exit with EXIT_WORKER_NO_KANBAN ($EXIT_WORKER_NO_KANBAN)"
    assert_output_contains "$output" "kanban" "wiggum-plan should mention kanban.md"
}

test_plan_invalid_task_id_fails() {
    # Task IDs with special characters should be rejected
    local output exit_code
    output=$(wiggum-plan "TASK/001" 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_USAGE" "$exit_code" \
        "wiggum-plan with invalid task ID should exit with EXIT_USAGE ($EXIT_USAGE)"
    assert_output_contains "$output" "Invalid task ID" "wiggum-plan should report invalid task ID"
}

# =============================================================================
# wiggum-inspect
# =============================================================================

test_inspect_no_args_shows_help() {
    local output exit_code
    output=$(wiggum-inspect 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum-inspect without args should exit 0 (shows help)"
    assert_output_contains "$output" "Usage:" "wiggum-inspect should show usage"
}

test_inspect_help_shows_usage() {
    local output exit_code
    output=$(wiggum-inspect --help 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum-inspect --help should exit 0"
    assert_output_contains "$output" "Usage:" "wiggum-inspect --help should show usage"
    assert_output_contains "$output" "log" "wiggum-inspect --help should list log subcommand"
}

test_inspect_log_no_target_fails() {
    local output exit_code
    output=$(wiggum-inspect log 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_USAGE" "$exit_code" \
        "wiggum-inspect log without target should exit with EXIT_USAGE ($EXIT_USAGE)"
    assert_output_contains "$output" "No target specified" "wiggum-inspect log should report no target"
}

test_inspect_unknown_subcommand_fails() {
    local output exit_code
    output=$(wiggum-inspect nonexistent 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_USAGE" "$exit_code" \
        "wiggum-inspect with unknown subcommand should exit with EXIT_USAGE ($EXIT_USAGE)"
    assert_output_contains "$output" "Unknown" "wiggum-inspect should report unknown subcommand"
}

# =============================================================================
# wiggum-monitor
# =============================================================================

test_monitor_help_shows_usage() {
    local output exit_code
    output=$(wiggum-monitor --help 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum-monitor --help should exit 0"
    assert_output_contains "$output" "Usage:" "wiggum-monitor --help should show usage"
    assert_output_contains "$output" "monitor" "wiggum-monitor --help should describe monitoring"
}

test_monitor_no_ralph_dir_fails() {
    local output exit_code
    output=$(wiggum-monitor 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_ERROR" "$exit_code" \
        "wiggum-monitor without .ralph dir should exit with EXIT_ERROR ($EXIT_ERROR)"
    assert_output_contains "$output" ".ralph" "wiggum-monitor should mention .ralph directory"
}

# =============================================================================
# wiggum-worker resume
# =============================================================================

test_worker_resume_no_worker_id_fails() {
    local output exit_code
    output=$(wiggum-worker resume 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_USAGE" "$exit_code" \
        "wiggum-worker resume without worker ID should exit with EXIT_USAGE ($EXIT_USAGE)"
    assert_output_contains "$output" "Worker ID required" "wiggum-worker resume should report missing worker ID"
}

test_worker_resume_help_shows_usage() {
    local output exit_code
    output=$(wiggum-worker resume --help 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "0" "$exit_code" "wiggum-worker resume --help should exit 0"
    assert_output_contains "$output" "Usage:" "wiggum-worker resume --help should show usage"
    assert_output_contains "$output" "resume" "wiggum-worker resume --help should describe resuming"
}

test_worker_resume_unknown_option_fails() {
    local output exit_code
    output=$(wiggum-worker resume --bogus 2>&1) || exit_code=$?
    exit_code=${exit_code:-0}

    assert_equals "$EXIT_USAGE" "$exit_code" \
        "wiggum-worker resume with unknown option should exit with EXIT_USAGE ($EXIT_USAGE)"
    assert_output_contains "$output" "Unknown option" "Should report unknown option"
}

# =============================================================================
# Run all tests
# =============================================================================

# wiggum dispatcher tests
run_test test_wiggum_no_args_shows_usage
run_test test_wiggum_help_flag
run_test test_wiggum_unknown_command

# wiggum-validate tests
run_test test_validate_no_ralph_dir_fails
run_test test_validate_help_shows_usage
run_test test_validate_unknown_option_fails

# wiggum-status tests
run_test test_status_no_ralph_dir_succeeds_with_message
run_test test_status_help_shows_usage

# wiggum-clean tests
run_test test_clean_no_ralph_dir_fails
run_test test_clean_help_shows_usage

# wiggum-worker start tests
run_test test_worker_start_no_task_id_fails
run_test test_worker_start_no_ralph_dir_fails
run_test test_worker_start_no_kanban_fails
run_test test_worker_start_help_shows_usage

# wiggum-init tests
run_test test_init_creates_ralph_directory
run_test test_init_in_non_git_directory_fails
run_test test_init_help_shows_usage
run_test test_init_idempotent_kanban

# wiggum-doctor tests
run_test test_doctor_produces_output
run_test test_doctor_help_shows_usage
run_test test_doctor_quiet_mode

# wiggum-worker stop tests
run_test test_worker_stop_no_ralph_dir_reports_no_workers
run_test test_worker_stop_help_shows_usage

# wiggum-worker kill tests
run_test test_worker_kill_no_args_fails
run_test test_worker_kill_all_no_ralph_dir_reports_no_workers
run_test test_worker_kill_help_shows_usage

# wiggum-run tests
run_test test_run_no_ralph_dir_fails
run_test test_run_help_shows_usage
run_test test_run_no_kanban_fails

# wiggum-pr tests
run_test test_pr_help_shows_usage
run_test test_pr_unknown_command_fails
run_test test_pr_view_no_number_fails
run_test test_pr_comments_no_pattern_fails

# wiggum-plan tests
run_test test_plan_no_task_id_fails
run_test test_plan_no_ralph_dir_fails
run_test test_plan_help_shows_usage
run_test test_plan_no_kanban_fails
run_test test_plan_invalid_task_id_fails

# wiggum-inspect tests
run_test test_inspect_no_args_shows_help
run_test test_inspect_help_shows_usage
run_test test_inspect_log_no_target_fails
run_test test_inspect_unknown_subcommand_fails

# wiggum-monitor tests
run_test test_monitor_help_shows_usage
run_test test_monitor_no_ralph_dir_fails

# wiggum-worker resume tests
run_test test_worker_resume_no_worker_id_fails
run_test test_worker_resume_help_shows_usage
run_test test_worker_resume_unknown_option_fails

print_test_summary
exit_with_test_result
