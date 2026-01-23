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
    assert_output_contains "$commit_msg" "Ralph Wiggum" "Commit message should include co-author"
    cd "$TESTS_DIR" || return 1
}

test_git_create_commit_succeeds_no_uncommitted_changes() {
    # No uncommitted changes - should still succeed (sub-agents may have already committed)
    local result
    git_create_commit "$WORKSPACE" "TASK-004" "No changes" "LOW" "worker-004" > /dev/null 2>&1
    result=$?

    assert_equals "0" "$result" "Should succeed even with no uncommitted changes"
    # Branch should still be set
    if [[ "$GIT_COMMIT_BRANCH" == task/TASK-004-* ]]; then
        echo -e "  ${GREEN}✓${NC} GIT_COMMIT_BRANCH set correctly"
    else
        echo -e "  ${RED}X${NC} GIT_COMMIT_BRANCH should be set: $GIT_COMMIT_BRANCH"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
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
# git_is_readonly_agent() Tests
# =============================================================================

test_git_is_readonly_agent() {
    # These should be read-only
    git_is_readonly_agent "security-audit"
    assert_equals "0" "$?" "security-audit should be read-only"

    git_is_readonly_agent "validation-review"
    assert_equals "0" "$?" "validation-review should be read-only"

    git_is_readonly_agent "plan-mode"
    assert_equals "0" "$?" "plan-mode should be read-only"

    git_is_readonly_agent "code-review"
    assert_equals "0" "$?" "code-review should be read-only"

    # These should NOT be read-only
    git_is_readonly_agent "task-worker"
    assert_equals "1" "$?" "task-worker should NOT be read-only"

    git_is_readonly_agent "security-fix"
    assert_equals "1" "$?" "security-fix should NOT be read-only"

    git_is_readonly_agent "test-coverage"
    assert_equals "1" "$?" "test-coverage should NOT be read-only"
}

# =============================================================================
# git_safety_checkpoint() Tests
# =============================================================================

test_git_safety_checkpoint_creates_commit() {
    # Add uncommitted changes
    echo "uncommitted work" > "$WORKSPACE/uncommitted.txt"

    git_safety_checkpoint "$WORKSPACE"
    local result=$?

    assert_equals "0" "$result" "Checkpoint should succeed"

    # Verify checkpoint SHA is set
    if [ -n "$GIT_SAFETY_CHECKPOINT_SHA" ]; then
        echo -e "  ${GREEN}✓${NC} Checkpoint SHA is set"
    else
        echo -e "  ${RED}X${NC} Checkpoint SHA should be set"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    # Verify changes were committed
    cd "$WORKSPACE" || return 1
    local status
    status=$(git status --porcelain)
    if [ -z "$status" ]; then
        echo -e "  ${GREEN}✓${NC} Working directory is clean after checkpoint"
    else
        echo -e "  ${RED}X${NC} Working directory should be clean after checkpoint"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    cd "$TESTS_DIR" || return 1
}

test_git_safety_checkpoint_no_changes() {
    # No uncommitted changes
    git_safety_checkpoint "$WORKSPACE"
    local result=$?

    assert_equals "0" "$result" "Checkpoint should succeed even with no changes"

    # Verify checkpoint SHA is set (should be current HEAD)
    if [ -n "$GIT_SAFETY_CHECKPOINT_SHA" ]; then
        echo -e "  ${GREEN}✓${NC} Checkpoint SHA is set"
    else
        echo -e "  ${RED}X${NC} Checkpoint SHA should be set"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# git_safety_restore() Tests
# =============================================================================

test_git_safety_restore_discards_changes() {
    # Create checkpoint
    git_safety_checkpoint "$WORKSPACE"
    local checkpoint="$GIT_SAFETY_CHECKPOINT_SHA"

    # Simulate read-only agent making accidental changes
    echo "accidental change" > "$WORKSPACE/accidental.txt"
    echo "modified" >> "$WORKSPACE/README.md"

    # Restore to checkpoint
    git_safety_restore "$WORKSPACE" "$checkpoint"
    local result=$?

    assert_equals "0" "$result" "Restore should succeed"

    # Verify changes were discarded
    cd "$WORKSPACE" || return 1
    if [ ! -f "$WORKSPACE/accidental.txt" ]; then
        echo -e "  ${GREEN}✓${NC} Accidental file was removed"
    else
        echo -e "  ${RED}X${NC} Accidental file should have been removed"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    local status
    status=$(git status --porcelain)
    if [ -z "$status" ]; then
        echo -e "  ${GREEN}✓${NC} Working directory is clean after restore"
    else
        echo -e "  ${RED}X${NC} Working directory should be clean after restore"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
    cd "$TESTS_DIR" || return 1
}

test_git_safety_restore_resets_commits() {
    # Create checkpoint
    git_safety_checkpoint "$WORKSPACE"
    local checkpoint="$GIT_SAFETY_CHECKPOINT_SHA"

    # Simulate read-only agent making a commit (which it shouldn't)
    cd "$WORKSPACE" || return 1
    echo "bad commit content" > "$WORKSPACE/bad_commit.txt"
    git add bad_commit.txt
    git commit -q -m "Bad commit by read-only agent"
    cd "$TESTS_DIR" || return 1

    # Verify HEAD moved
    cd "$WORKSPACE" || return 1
    local bad_sha
    bad_sha=$(git rev-parse HEAD)
    cd "$TESTS_DIR" || return 1

    if [ "$bad_sha" != "$checkpoint" ]; then
        echo -e "  ${GREEN}✓${NC} HEAD moved (as expected for test setup)"
    else
        echo -e "  ${RED}X${NC} HEAD should have moved for test"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))

    # Restore to checkpoint
    git_safety_restore "$WORKSPACE" "$checkpoint"

    # Verify HEAD is back to checkpoint
    cd "$WORKSPACE" || return 1
    local current_sha
    current_sha=$(git rev-parse HEAD)
    cd "$TESTS_DIR" || return 1

    assert_equals "$checkpoint" "$current_sha" "HEAD should be reset to checkpoint"

    # Verify bad file is gone
    if [ ! -f "$WORKSPACE/bad_commit.txt" ]; then
        echo -e "  ${GREEN}✓${NC} Bad commit file was removed"
    else
        echo -e "  ${RED}X${NC} Bad commit file should have been removed"
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
run_test test_git_create_commit_succeeds_no_uncommitted_changes
run_test test_git_create_commit_fails_invalid_workspace
run_test test_git_create_commit_stages_all_changes

# git_verify_pushed tests
run_test test_git_verify_pushed_fails_no_remote

# branch naming tests
run_test test_branch_naming_includes_timestamp

# git safety tests
run_test test_git_is_readonly_agent
run_test test_git_safety_checkpoint_creates_commit
run_test test_git_safety_checkpoint_no_changes
run_test test_git_safety_restore_discards_changes
run_test test_git_safety_restore_resets_commits

print_test_summary
exit_with_test_result
