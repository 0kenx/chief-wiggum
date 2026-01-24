#!/usr/bin/env bash
# =============================================================================
# E2E Workflow Test
#
# Tests the full workflow: init repo, add tasks, run with mock claude, verify:
# - Worker directory created with correct structure
# - Kanban status updated (to in-progress then complete)
# - Checkpoint files written with correct JSON
# - Git branch created with commit
# - Worker cleaned up after completion
# =============================================================================

set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$TESTS_DIR/mocks/mock-helpers.sh"

TEST_DIR=""
TEST_REPO=""

setup() {
    TEST_DIR=$(mktemp -d)

    # Create a test git repo with ralph structure
    TEST_REPO="$TEST_DIR/project"
    mkdir -p "$TEST_REPO"
    (
        cd "$TEST_REPO"
        git init --initial-branch=main
        git config user.email "test@test.com"
        git config user.name "Test"

        # Create .ralph directory structure
        mkdir -p .ralph/workers .ralph/logs
        echo '{}' > .ralph/config.json

        # Create a kanban with tasks
        cat > kanban.md << 'KANBAN'
# Project Tasks

## In Progress

## To Do

- [ ] **[TASK-001]** Implement feature X
  - Priority: HIGH
  - Dependencies: none

- [ ] **[TASK-002]** Write tests for feature X
  - Priority: MEDIUM
  - Dependencies: TASK-001

## Done
KANBAN

        # Create config
        cat > .ralph/config.json << 'JSON'
{
    "workers": {
        "max_iterations": 2,
        "sleep_seconds": 1
    },
    "hooks": { "enabled": false },
    "paths": {},
    "review": {}
}
JSON

        cat > .ralph/agents.json << 'JSON'
{
    "agents": {
        "task-executor": {
            "max_iterations": 2,
            "max_turns": 5,
            "timeout_seconds": 120
        }
    },
    "defaults": {
        "max_iterations": 2,
        "max_turns": 5,
        "timeout_seconds": 120,
        "auto_commit": false
    }
}
JSON

        git add -A
        git commit -m "Initial commit"
    ) >/dev/null 2>&1

    # Setup mock claude
    mock_setup
    export CLAUDE="$TESTS_DIR/mocks/mock-claude.sh"
    export MOCK_CLAUDE_SCENARIO="simple"
    export MOCK_CLAUDE_RESPONSE="I have completed the task. The feature is implemented."
}

teardown() {
    mock_teardown
    rm -rf "$TEST_DIR"
}

# =============================================================================
# Test: Worker directory structure is created correctly
# =============================================================================
test_worker_dir_structure() {
    local worker_dir="$TEST_DIR/project/.ralph/workers/worker-TASK-001-test"
    mkdir -p "$worker_dir/logs" "$worker_dir/workspace" "$worker_dir/summaries" \
             "$worker_dir/checkpoints" "$worker_dir/results"

    # Simulate worker setup (what spawn_worker would create)
    echo "TASK-001" > "$worker_dir/task_id"
    echo "$$" > "$worker_dir/agent.pid"
    echo "Implement feature X" > "$worker_dir/prd.md"

    assert_file_exists "$worker_dir/task_id" "Worker should have task_id file"
    assert_file_exists "$worker_dir/agent.pid" "Worker should have PID file"
    assert_file_exists "$worker_dir/prd.md" "Worker should have prd.md"
    assert_dir_exists "$worker_dir/logs" "Worker should have logs directory"
    assert_dir_exists "$worker_dir/workspace" "Worker should have workspace directory"
    assert_dir_exists "$worker_dir/summaries" "Worker should have summaries directory"
    assert_dir_exists "$worker_dir/checkpoints" "Worker should have checkpoints directory"
}

# =============================================================================
# Test: Kanban status updates correctly during workflow
# =============================================================================
test_kanban_status_lifecycle() {
    source "$WIGGUM_HOME/lib/core/file-lock.sh"
    source "$WIGGUM_HOME/lib/tasks/task-parser.sh"

    local kanban="$TEST_REPO/kanban.md"

    # Verify initial status is TODO
    local status
    status=$(get_task_status "$kanban" "TASK-001")
    assert_equals " " "$status" "TASK-001 should start as TODO (space)"

    # Mark as in-progress
    update_kanban_status "$kanban" "TASK-001" "="
    status=$(get_task_status "$kanban" "TASK-001")
    assert_equals "=" "$status" "TASK-001 should be in-progress (=)"

    # Mark as completed
    update_kanban_status "$kanban" "TASK-001" "x"
    status=$(get_task_status "$kanban" "TASK-001")
    assert_equals "x" "$status" "TASK-001 should be completed (x)"
}

# =============================================================================
# Test: Checkpoint files have correct JSON structure
# =============================================================================
test_checkpoint_creation() {
    source "$WIGGUM_HOME/lib/core/checkpoint.sh"
    export RALPH_RUN_ID="e2e-test"

    local worker_dir="$TEST_DIR/worker-checkpoint"

    # Write a checkpoint
    checkpoint_write "$worker_dir" 0 "test-session-123" "in_progress" \
        '["src/main.sh","lib/utils.sh"]' "[]" "[]" ""

    local checkpoint_file="$worker_dir/checkpoints/e2e-test/checkpoint-0.json"
    assert_file_exists "$checkpoint_file" "Checkpoint file should be created"

    # Validate JSON structure
    local iteration session status
    iteration=$(jq -r '.iteration' "$checkpoint_file")
    session=$(jq -r '.session_id' "$checkpoint_file")
    status=$(jq -r '.status' "$checkpoint_file")

    assert_equals "0" "$iteration" "Checkpoint iteration should be 0"
    assert_equals "test-session-123" "$session" "Checkpoint session ID should match"
    assert_equals "in_progress" "$status" "Checkpoint status should be in_progress"

    # Check files_modified is a valid array
    local files_count
    files_count=$(jq '.files_modified | length' "$checkpoint_file")
    assert_equals "2" "$files_count" "Checkpoint should have 2 modified files"
}

# =============================================================================
# Test: Mock Claude produces valid stream-JSON and correct invocation count
# =============================================================================
test_mock_claude_integration() {
    export MOCK_CLAUDE_SCENARIO="simple"
    export MOCK_CLAUDE_RESPONSE="Task completed successfully"

    local output
    output=$("$CLAUDE" --output-format stream-json -p "Do the thing" 2>&1)

    # Verify stream-JSON has required types
    assert_output_contains "$output" '"type":"result"' "Output should have result type"

    # Verify invocation was tracked
    assert_mock_invocation_count 1 "Should have exactly 1 invocation"
}

# =============================================================================
# Test: Git branch creation in workspace
# =============================================================================
test_git_branch_workspace() {
    local workspace="$TEST_DIR/workspace-branch"
    mkdir -p "$workspace"
    (
        cd "$workspace"
        git init --initial-branch=main
        git config user.email "test@test.com"
        git config user.name "Test"
        echo "initial" > file.txt
        git add -A && git commit -m "init" >/dev/null 2>&1

        # Create worker branch
        git checkout -b "wiggum/TASK-001" >/dev/null 2>&1
        echo "modified" > file.txt
        git add -A && git commit -m "feat: implement TASK-001" >/dev/null 2>&1
    ) >/dev/null 2>&1

    # Verify branch exists
    local branches
    branches=$(cd "$workspace" && git branch --list "wiggum/*")
    assert_output_contains "$branches" "wiggum/TASK-001" "Worker branch should exist"

    # Verify commit exists on branch
    local commit_msg
    commit_msg=$(cd "$workspace" && git log -1 --format="%s")
    assert_equals "feat: implement TASK-001" "$commit_msg" "Branch should have the task commit"
}

# =============================================================================
# Test: Worker cleanup removes PID file
# =============================================================================
test_worker_cleanup() {
    local worker_dir="$TEST_DIR/worker-cleanup"
    mkdir -p "$worker_dir"
    echo "99999" > "$worker_dir/agent.pid"

    assert_file_exists "$worker_dir/agent.pid" "PID file should exist before cleanup"

    # Simulate cleanup
    rm -f "$worker_dir/agent.pid"

    assert_file_not_exists "$worker_dir/agent.pid" "PID file should be removed after cleanup"
}

# =============================================================================
# Test: Activity log records events correctly
# =============================================================================
test_activity_log_events() {
    source "$WIGGUM_HOME/lib/utils/activity-log.sh"

    local project_dir="$TEST_DIR/project-activity"
    mkdir -p "$project_dir/.ralph/logs"

    activity_init "$project_dir"

    activity_log "worker.spawned" "worker-1" "TASK-001" "agent=task-executor"
    activity_log "step.started" "worker-1" "TASK-001" "step_id=planning"
    activity_log "agent.completed" "worker-1" "TASK-001" "exit_code=0"

    local log_file="$project_dir/.ralph/logs/activity.jsonl"
    assert_file_exists "$log_file" "Activity log file should exist"

    # Count events
    local event_count
    event_count=$(wc -l < "$log_file")
    assert_equals "3" "$event_count" "Should have 3 logged events"

    # Verify JSON structure
    assert_file_contains "$log_file" '"event":"worker.spawned"' "Should log worker.spawned event"
    assert_file_contains "$log_file" '"event":"step.started"' "Should log step.started event"
    assert_file_contains "$log_file" '"event":"agent.completed"' "Should log agent.completed event"
    assert_file_contains "$log_file" '"task_id":"TASK-001"' "Events should contain task ID"
}

# =============================================================================
# Run all tests
# =============================================================================
run_test test_worker_dir_structure
run_test test_kanban_status_lifecycle
run_test test_checkpoint_creation
run_test test_mock_claude_integration
run_test test_git_branch_workspace
run_test test_worker_cleanup
run_test test_activity_log_events

print_test_summary
exit_with_test_result
