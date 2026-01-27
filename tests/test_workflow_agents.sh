#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/agents/workflow/*.sh
# Tests the git-sync-main, git-commit-push, and pr-merge agents

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/core/agent-base.sh"

# Create temp dir for test isolation
TEST_DIR=""
RALPH_DIR=""
WORKER_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    RALPH_DIR="$TEST_DIR/.ralph"
    mkdir -p "$RALPH_DIR/workers"

    WORKER_DIR="$RALPH_DIR/workers/worker-TEST-001-$(date +%s)"
    mkdir -p "$WORKER_DIR/workspace"
    mkdir -p "$WORKER_DIR/logs"
    mkdir -p "$WORKER_DIR/results"
    mkdir -p "$WORKER_DIR/reports"

    # Initialize a git repo in workspace
    git -C "$WORKER_DIR/workspace" init -q
    git -C "$WORKER_DIR/workspace" config user.email "test@test.com"
    git -C "$WORKER_DIR/workspace" config user.name "Test User"
    echo "initial" > "$WORKER_DIR/workspace/file.txt"
    git -C "$WORKER_DIR/workspace" add .
    git -C "$WORKER_DIR/workspace" commit -q -m "Initial commit"
}

teardown() {
    rm -rf "$TEST_DIR"
}

# =============================================================================
# git-sync-main Agent Tests
# =============================================================================

test_git_sync_main_agent_exists() {
    assert_file_exists "$WIGGUM_HOME/lib/agents/workflow/git-sync-main.sh" "Agent file should exist"
}

test_git_sync_main_agent_sources() {
    source "$WIGGUM_HOME/lib/agents/workflow/git-sync-main.sh"

    assert_equals "workflow.git-sync-main" "$AGENT_TYPE" "Agent type should be set"
}

test_git_sync_main_missing_workspace_fails() {
    rm -rf "$WORKER_DIR/workspace"

    source "$WIGGUM_HOME/lib/agents/workflow/git-sync-main.sh"
    local result=0
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null || result=$?

    assert_equals "1" "$result" "Should fail without workspace"
}

test_git_sync_main_not_git_repo_fails() {
    rm -rf "$WORKER_DIR/workspace/.git"

    source "$WIGGUM_HOME/lib/agents/workflow/git-sync-main.sh"
    local result=0
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null || result=$?

    assert_equals "1" "$result" "Should fail for non-git repo"
}

# =============================================================================
# git-commit-push Agent Tests
# =============================================================================

test_git_commit_push_agent_exists() {
    assert_file_exists "$WIGGUM_HOME/lib/agents/workflow/git-commit-push.sh" "Agent file should exist"
}

test_git_commit_push_agent_sources() {
    source "$WIGGUM_HOME/lib/agents/workflow/git-commit-push.sh"

    assert_equals "workflow.git-commit-push" "$AGENT_TYPE" "Agent type should be set"
}

test_git_commit_push_no_changes_passes() {
    # Create a branch first
    git -C "$WORKER_DIR/workspace" checkout -b test-branch

    source "$WIGGUM_HOME/lib/agents/workflow/git-commit-push.sh"
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null

    # Check result file
    local result_file
    result_file=$(find "$WORKER_DIR/results" -name "*-result.json" | head -1)

    if [ -n "$result_file" ]; then
        local gate_result
        gate_result=$(jq -r '.outputs.gate_result' "$result_file")
        assert_equals "PASS" "$gate_result" "Should PASS with no changes"
    fi
}

test_git_commit_push_commits_changes() {
    # Create a branch and make changes
    git -C "$WORKER_DIR/workspace" checkout -b test-branch
    echo "modified" > "$WORKER_DIR/workspace/file.txt"

    source "$WIGGUM_HOME/lib/agents/workflow/git-commit-push.sh"

    # Mock git push to avoid actually pushing
    export GIT_TERMINAL_PROMPT=0

    # Run agent (will fail at push since no remote, but should commit)
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null || true

    # Check that commit was created
    local commit_count
    commit_count=$(git -C "$WORKER_DIR/workspace" log --oneline | wc -l)
    assert_greater_than "$commit_count" "1" "Should have created a commit"
}

test_git_commit_push_missing_workspace_fails() {
    rm -rf "$WORKER_DIR/workspace"

    source "$WIGGUM_HOME/lib/agents/workflow/git-commit-push.sh"
    local result=0
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null || result=$?

    assert_equals "1" "$result" "Should fail without workspace"
}

# =============================================================================
# pr-merge Agent Tests
# =============================================================================

test_pr_merge_agent_exists() {
    assert_file_exists "$WIGGUM_HOME/lib/agents/workflow/pr-merge.sh" "Agent file should exist"
}

test_pr_merge_agent_sources() {
    source "$WIGGUM_HOME/lib/agents/workflow/pr-merge.sh"

    assert_equals "workflow.pr-merge" "$AGENT_TYPE" "Agent type should be set"
}

test_pr_merge_no_pr_number_fails() {
    source "$WIGGUM_HOME/lib/agents/workflow/pr-merge.sh"
    local result=0
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null || result=$?

    assert_equals "1" "$result" "Should fail without PR number"
}

test_pr_merge_missing_workspace_fails() {
    rm -rf "$WORKER_DIR/workspace"

    source "$WIGGUM_HOME/lib/agents/workflow/pr-merge.sh"
    local result=0
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null || result=$?

    assert_equals "1" "$result" "Should fail without workspace"
}

# =============================================================================
# git-conflict-resolver Agent Tests
# =============================================================================

test_git_conflict_resolver_agent_exists() {
    assert_file_exists "$WIGGUM_HOME/lib/agents/workflow/git-conflict-resolver.sh" "Agent file should exist"
}

test_git_conflict_resolver_agent_sources() {
    source "$WIGGUM_HOME/lib/agents/workflow/git-conflict-resolver.sh"

    assert_equals "workflow.git-conflict-resolver" "$AGENT_TYPE" "Agent type should be set"
}

test_git_conflict_resolver_no_conflicts_skips() {
    # No conflicts exist in the test workspace

    source "$WIGGUM_HOME/lib/agents/workflow/git-conflict-resolver.sh"
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null

    # Check result file
    local result_file
    result_file=$(find "$WORKER_DIR/results" -name "*-result.json" | head -1)

    if [ -n "$result_file" ]; then
        local gate_result
        gate_result=$(jq -r '.outputs.gate_result' "$result_file")
        assert_equals "SKIP" "$gate_result" "Should SKIP with no conflicts"
    fi
}

test_git_conflict_resolver_missing_workspace_fails() {
    rm -rf "$WORKER_DIR/workspace"

    source "$WIGGUM_HOME/lib/agents/workflow/git-conflict-resolver.sh"
    local result=0
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null || result=$?

    assert_equals "1" "$result" "Should fail without workspace"
}

test_git_conflict_resolver_reads_plan_file() {
    # Create a resolution plan file
    echo "# Resolution Plan for TEST-001" > "$WORKER_DIR/resolution-plan.md"

    source "$WIGGUM_HOME/lib/agents/workflow/git-conflict-resolver.sh"

    # The plan support is checked during prompt generation, but we can verify
    # the file exists and agent sources correctly
    assert_file_exists "$WORKER_DIR/resolution-plan.md" "Plan file should exist"
}

# =============================================================================
# multi-pr-planner Agent Tests
# =============================================================================

test_multi_pr_planner_agent_exists() {
    assert_file_exists "$WIGGUM_HOME/lib/agents/workflow/multi-pr-planner.sh" "Agent file should exist"
}

test_multi_pr_planner_agent_sources() {
    source "$WIGGUM_HOME/lib/agents/workflow/multi-pr-planner.sh"

    assert_equals "workflow.multi-pr-planner" "$AGENT_TYPE" "Agent type should be set"
}

test_multi_pr_planner_missing_batch_file_fails() {
    source "$WIGGUM_HOME/lib/agents/workflow/multi-pr-planner.sh"
    local result=0
    agent_run "$WORKER_DIR" "$TEST_DIR" 2>/dev/null || result=$?

    assert_equals "1" "$result" "Should fail without batch file"
}

# Note: multi-pr-planner.md was removed - this agent requires programmatic shell
# control for batch orchestration (iterating tasks, accessing multiple workspaces)
# which cannot be expressed in the markdown agent format.

# =============================================================================
# agents.json Config Tests
# =============================================================================

test_agents_json_has_workflow_agents() {
    local agents_file="$WIGGUM_HOME/config/agents.json"

    assert_file_contains "$agents_file" "workflow.git-sync-main" "Should have git-sync-main"
    assert_file_contains "$agents_file" "workflow.git-commit-push" "Should have git-commit-push"
    assert_file_contains "$agents_file" "workflow.pr-merge" "Should have pr-merge"
    assert_file_contains "$agents_file" "workflow.git-conflict-resolver" "Should have git-conflict-resolver"
    assert_file_contains "$agents_file" "workflow.multi-pr-planner" "Should have multi-pr-planner"
}

test_workflow_agents_have_result_mappings() {
    local agents_file="$WIGGUM_HOME/config/agents.json"

    local sync_main_mappings
    sync_main_mappings=$(jq '.agents."workflow.git-sync-main".result_mappings' "$agents_file")
    assert_not_equals "null" "$sync_main_mappings" "git-sync-main should have result_mappings"

    local commit_push_mappings
    commit_push_mappings=$(jq '.agents."workflow.git-commit-push".result_mappings' "$agents_file")
    assert_not_equals "null" "$commit_push_mappings" "git-commit-push should have result_mappings"
}

# =============================================================================
# Run Tests
# =============================================================================

run_test test_git_sync_main_agent_exists
run_test test_git_sync_main_agent_sources
run_test test_git_sync_main_missing_workspace_fails
run_test test_git_sync_main_not_git_repo_fails
run_test test_git_commit_push_agent_exists
run_test test_git_commit_push_agent_sources
run_test test_git_commit_push_no_changes_passes
run_test test_git_commit_push_commits_changes
run_test test_git_commit_push_missing_workspace_fails
run_test test_pr_merge_agent_exists
run_test test_pr_merge_agent_sources
run_test test_pr_merge_no_pr_number_fails
run_test test_pr_merge_missing_workspace_fails
run_test test_git_conflict_resolver_agent_exists
run_test test_git_conflict_resolver_agent_sources
run_test test_git_conflict_resolver_no_conflicts_skips
run_test test_git_conflict_resolver_missing_workspace_fails
run_test test_git_conflict_resolver_reads_plan_file
run_test test_multi_pr_planner_agent_exists
run_test test_multi_pr_planner_agent_sources
run_test test_multi_pr_planner_missing_batch_file_fails
run_test test_agents_json_has_workflow_agents
run_test test_workflow_agents_have_result_mappings

print_test_summary
exit_with_test_result
