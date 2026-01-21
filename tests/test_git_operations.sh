#!/usr/bin/env bash
# Tests for lib/git/git-operations.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/git/git-operations.sh"

# Create temp dir for test isolation
TEST_DIR=""
WORKSPACE=""
WORKER_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    WORKSPACE="$TEST_DIR/workspace"
    WORKER_DIR="$TEST_DIR/worker"
    mkdir -p "$WORKSPACE"
    mkdir -p "$WORKER_DIR"

    # Initialize a git repo in workspace
    cd "$WORKSPACE" || return 1
    git init -q
    git config user.email "test@test.com"
    git config user.name "Test User"

    # Create initial commit
    echo "initial content" > README.md
    git add README.md
    git commit -q -m "Initial commit"

    cd "$TESTS_DIR" || return 1
}

teardown() {
    rm -rf "$TEST_DIR"
    cd "$TESTS_DIR" || return 1
}

# =============================================================================
# git_create_commit() Tests
# =============================================================================

test_git_create_commit_creates_branch() {
    # Add a file to commit
    echo "new content" > "$WORKSPACE/new_file.txt"

    local result
    git_create_commit "$WORKSPACE" "TASK-001" "Test task" "HIGH" "worker-001" > /dev/null 2>&1
    result=$?

    assert_equals "0" "$result" "Should succeed"

    # Check branch was created
    cd "$WORKSPACE" || return 1
    local current_branch
    current_branch=$(git branch --show-current)
    if [[ "$current_branch" == task/TASK-001-* ]]; then
        echo -e "  ${GREEN}✓${NC} Branch created with correct prefix"
    else
        echo -e "  ${RED}X${NC} Expected branch starting with task/TASK-001-, got: $current_branch"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    cd "$TESTS_DIR" || return 1
}

test_git_create_commit_sets_branch_variable() {
    echo "another file" > "$WORKSPACE/another.txt"

    git_create_commit "$WORKSPACE" "TASK-002" "Another task" "MEDIUM" "worker-002" > /dev/null 2>&1

    if [[ "$GIT_COMMIT_BRANCH" == task/TASK-002-* ]]; then
        echo -e "  ${GREEN}✓${NC} GIT_COMMIT_BRANCH set correctly"
    else
        echo -e "  ${RED}X${NC} GIT_COMMIT_BRANCH incorrect: $GIT_COMMIT_BRANCH"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_git_create_commit_message_format() {
    echo "content for commit msg test" > "$WORKSPACE/msg_test.txt"

    git_create_commit "$WORKSPACE" "TASK-003" "Test description" "HIGH" "worker-test" > /dev/null 2>&1

    cd "$WORKSPACE" || return 1
    local commit_msg
    commit_msg=$(git log -1 --format=%B)

    assert_output_contains "$commit_msg" "TASK-003:" "Commit message should start with task ID"
    assert_output_contains "$commit_msg" "Test description" "Commit message should include description"
    assert_output_contains "$commit_msg" "Worker: worker-test" "Commit message should include worker ID"
    assert_output_contains "$commit_msg" "Priority: HIGH" "Commit message should include priority"
    assert_output_contains "$commit_msg" "Chief Wiggum" "Commit message should include co-author"
    cd "$TESTS_DIR" || return 1
}

test_git_create_commit_fails_no_changes() {
    # No changes to commit
    local result
    git_create_commit "$WORKSPACE" "TASK-004" "No changes" "LOW" "worker-004" > /dev/null 2>&1
    result=$?

    assert_equals "1" "$result" "Should fail when no changes to commit"
    assert_equals "" "$GIT_COMMIT_BRANCH" "GIT_COMMIT_BRANCH should be empty on failure"
}

test_git_create_commit_fails_invalid_workspace() {
    local result
    git_create_commit "/nonexistent/path" "TASK-005" "Test" "MEDIUM" "worker-005" > /dev/null 2>&1
    result=$?

    assert_equals "1" "$result" "Should fail for invalid workspace"
}

test_git_create_commit_stages_all_changes() {
    # Create multiple files
    echo "file 1" > "$WORKSPACE/file1.txt"
    echo "file 2" > "$WORKSPACE/file2.txt"
    mkdir -p "$WORKSPACE/subdir"
    echo "nested" > "$WORKSPACE/subdir/nested.txt"

    git_create_commit "$WORKSPACE" "TASK-006" "Multiple files" "HIGH" "worker-006" > /dev/null 2>&1

    cd "$WORKSPACE" || return 1
    # Check all files were committed
    local committed_files
    committed_files=$(git diff-tree --no-commit-id --name-only -r HEAD)

    assert_output_contains "$committed_files" "file1.txt" "Should include file1.txt"
    assert_output_contains "$committed_files" "file2.txt" "Should include file2.txt"
    assert_output_contains "$committed_files" "subdir/nested.txt" "Should include nested file"
    cd "$TESTS_DIR" || return 1
}

# =============================================================================
# git_create_pr() Tests (Limited - requires mocking gh)
# =============================================================================

test_git_create_pr_requires_gh() {
    # Test when gh CLI is not available (mock by using non-existent path)
    local original_path="$PATH"
    export PATH="/nonexistent"

    echo "pr test content" > "$WORKSPACE/pr_test.txt"
    git_create_commit "$WORKSPACE" "TASK-007" "PR test" "MEDIUM" "worker-007" > /dev/null 2>&1

    cd "$WORKSPACE" || return 1
    local result
    git_create_pr "$GIT_COMMIT_BRANCH" "TASK-007" "PR test" "$WORKER_DIR" > /dev/null 2>&1
    result=$?

    export PATH="$original_path"
    cd "$TESTS_DIR" || return 1

    # Should fail because we can't push and gh is not available
    # (gh not found or push fails without remote)
    assert_equals "1" "$result" "Should fail when gh CLI not available or no remote"
    assert_equals "N/A" "$GIT_PR_URL" "GIT_PR_URL should be N/A on failure"
}

# =============================================================================
# git_verify_pushed() Tests
# =============================================================================

test_git_verify_pushed_fails_no_remote() {
    cd "$WORKSPACE" || return 1

    local result
    git_verify_pushed "$WORKSPACE" "TASK-008" > /dev/null 2>&1
    result=$?

    cd "$TESTS_DIR" || return 1

    assert_equals "1" "$result" "Should fail when no remote"
}

# =============================================================================
# Branch Naming Convention Tests
# =============================================================================

test_branch_naming_includes_timestamp() {
    echo "timestamp test" > "$WORKSPACE/ts_test.txt"

    local before_ts
    before_ts=$(date +%s)
    git_create_commit "$WORKSPACE" "TASK-009" "Timestamp test" "HIGH" "worker-009" > /dev/null 2>&1
    local after_ts
    after_ts=$(date +%s)

    # Extract timestamp from branch name
    local branch_ts
    branch_ts=$(echo "$GIT_COMMIT_BRANCH" | sed -E 's/task\/TASK-009-//')

    if [ "$branch_ts" -ge "$before_ts" ] && [ "$branch_ts" -le "$after_ts" ]; then
        echo -e "  ${GREEN}✓${NC} Branch timestamp is valid"
    else
        echo -e "  ${RED}X${NC} Branch timestamp out of range: $branch_ts (expected $before_ts-$after_ts)"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# Run All Tests
# =============================================================================

# git_create_commit tests
run_test test_git_create_commit_creates_branch
run_test test_git_create_commit_sets_branch_variable
run_test test_git_create_commit_message_format
run_test test_git_create_commit_fails_no_changes
run_test test_git_create_commit_fails_invalid_workspace
run_test test_git_create_commit_stages_all_changes

# git_create_pr tests (limited without remote)
run_test test_git_create_pr_requires_gh

# git_verify_pushed tests
run_test test_git_verify_pushed_fails_no_remote

# branch naming tests
run_test test_branch_naming_includes_timestamp

print_test_summary
exit_with_test_result
