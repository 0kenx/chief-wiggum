#!/usr/bin/env bash
set -euo pipefail
# Test plan sync (lib/github/plan-sync.sh)
#
# Mocks gh API calls to test sync logic without hitting GitHub.

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/github/issue-state.sh"
source "$WIGGUM_HOME/lib/github/plan-sync.sh"

TEST_DIR=""
MOCK_BIN=""
ORIG_PATH=""

setup() {
    TEST_DIR=$(mktemp -d)
    mkdir -p "$TEST_DIR/plans"

    # Initialize sync state
    github_sync_state_init "$TEST_DIR"

    # Set up a mock gh command
    MOCK_BIN=$(mktemp -d)
    ORIG_PATH="$PATH"
    export PATH="$MOCK_BIN:$PATH"
}

teardown() {
    export PATH="$ORIG_PATH"
    rm -rf "$TEST_DIR" "$MOCK_BIN"
}

# =============================================================================
# Mock Helpers
# =============================================================================

# Create a mock gh script that returns canned responses
#
# Args:
#   behavior - "no-comment", "has-comment", "create-ok", "update-ok", "fail"
#   body     - Comment body to return (for has-comment)
#   id       - Comment ID to return (for has-comment / create-ok)
_setup_gh_mock() {
    local behavior="$1"
    local body="${2:-}"
    local id="${3:-12345}"

    cat > "$MOCK_BIN/gh" << GHEOF
#!/usr/bin/env bash
# Mock gh for plan sync tests
case "\$*" in
    *"issues/"*"/comments"*POST*)
        # Create comment
        case "$behavior" in
            fail) exit 1 ;;
            *) echo '{"id": $id}' ;;
        esac
        ;;
    *"issues/comments/"*PATCH*)
        # Update comment
        case "$behavior" in
            fail) exit 1 ;;
            *) echo '{"id": $id}' ;;
        esac
        ;;
    *"issues/"*"/comments"*)
        # List comments (find plan comment)
        case "$behavior" in
            no-comment|create-ok)
                echo "" ;;
            has-comment|update-ok)
                echo '{"id": $id, "body": "<!-- wiggum:plan -->\n$body"}' ;;
            fail)
                exit 1 ;;
        esac
        ;;
    *)
        echo "mock-gh: unhandled: \$*" >&2
        exit 1
        ;;
esac
GHEOF
    chmod +x "$MOCK_BIN/gh"
}

# Set up a mock that serves specific find/create/update responses independently
#
# Args:
#   find_response   - What to echo for find (comment list) calls
#   create_response - What to echo for POST calls
#   update_response - What to echo for PATCH calls
_setup_gh_mock_detailed() {
    local find_response="${1:-}"
    local create_response="${2:-}"
    local update_response="${3:-}"

    cat > "$MOCK_BIN/gh" << GHEOF
#!/usr/bin/env bash
case "\$*" in
    *"issues/"*"/comments"*POST*|*-X\ POST*)
        echo '$create_response'
        ;;
    *"issues/comments/"*PATCH*|*-X\ PATCH*)
        echo '$update_response'
        ;;
    *"issues/"*"/comments"*)
        echo '$find_response'
        ;;
    *)
        echo "mock-gh: unhandled: \$*" >&2
        exit 1
        ;;
esac
GHEOF
    chmod +x "$MOCK_BIN/gh"
}

# Create a task in sync state with an issue_number
_create_tracked_task() {
    local task_id="$1"
    local issue_number="$2"
    local extra_fields="${3:-}"

    local entry
    if [ -n "$extra_fields" ]; then
        entry=$(jq -n --argjson num "$issue_number" --argjson extra "$extra_fields" \
            '{"issue_number": $num} + $extra')
    else
        entry=$(jq -n --argjson num "$issue_number" '{"issue_number": $num}')
    fi
    github_sync_state_set_task "$TEST_DIR" "$task_id" "$entry"
}

# =============================================================================
# Marker Identification
# =============================================================================

test_strip_plan_marker() {
    local body="<!-- wiggum:plan -->
# My Plan
Some content here"
    local result
    result=$(_strip_plan_marker "$body")
    assert_equals "# My Plan
Some content here" "$result" "Should strip marker and leading newline"
}

test_strip_plan_marker_no_content() {
    local body="<!-- wiggum:plan -->"
    local result
    result=$(_strip_plan_marker "$body")
    assert_equals "" "$result" "Should return empty for marker-only body"
}

# =============================================================================
# Local Only -> Creates Comment
# =============================================================================

test_local_only_creates_comment() {
    _create_tracked_task "TASK-001" 42

    # Write local plan
    printf '%s\n' "# Plan for TASK-001" > "$TEST_DIR/plans/TASK-001.md"

    # Mock: no existing comment, create returns ID 99999
    # gh api --jq '.id' returns just the number, so mock returns plain ID
    _setup_gh_mock_detailed "" '99999' ""

    github_plan_sync_task "$TEST_DIR" "TASK-001" "false" ""

    # Verify state was updated with comment ID and hash
    local state
    state=$(github_sync_state_get_task "$TEST_DIR" "TASK-001")
    local comment_id
    comment_id=$(echo "$state" | jq -r '.plan_comment_id')
    assert_equals "99999" "$comment_id" "Should store plan_comment_id in state"

    local hash
    hash=$(echo "$state" | jq -r '.plan_content_hash')
    assert_output_contains "$hash" "sha256:" "Should store plan_content_hash"
}

# =============================================================================
# Remote Only -> Creates Local File
# =============================================================================

test_remote_only_creates_local_file() {
    _create_tracked_task "TASK-002" 55

    # No local file — only remote comment exists
    _setup_gh_mock_detailed \
        '{"id": 77777, "body": "<!-- wiggum:plan -->\n# Remote Plan\nDetails here"}' \
        "" ""

    github_plan_sync_task "$TEST_DIR" "TASK-002" "false" ""

    assert_file_exists "$TEST_DIR/plans/TASK-002.md" "Should create local plan file"
    assert_file_contains "$TEST_DIR/plans/TASK-002.md" "# Remote Plan" "Should contain remote content"

    # Verify state was updated
    local state
    state=$(github_sync_state_get_task "$TEST_DIR" "TASK-002")
    local comment_id
    comment_id=$(echo "$state" | jq -r '.plan_comment_id')
    assert_equals "77777" "$comment_id" "Should store remote comment ID"
}

# =============================================================================
# Both Changed -> Conflict Warning
# =============================================================================

test_both_changed_conflict() {
    local initial_hash
    initial_hash=$(github_sync_hash_content "original content")

    _create_tracked_task "TASK-003" 60 \
        "{\"plan_comment_id\": 11111, \"plan_content_hash\": \"$initial_hash\"}"

    # Local file with different content
    printf '%s\n' "modified local content" > "$TEST_DIR/plans/TASK-003.md"

    # Remote comment also different
    _setup_gh_mock_detailed \
        '{"id": 11111, "body": "<!-- wiggum:plan -->\nmodified remote content"}' \
        "" ""

    local exit_code=0
    github_plan_sync_task "$TEST_DIR" "TASK-003" "false" "" || exit_code=$?

    assert_equals "1" "$exit_code" "Should return 1 for conflict"
}

# =============================================================================
# Force Up -> Local Wins
# =============================================================================

test_force_up_local_wins() {
    local initial_hash
    initial_hash=$(github_sync_hash_content "original content")

    _create_tracked_task "TASK-004" 70 \
        "{\"plan_comment_id\": 22222, \"plan_content_hash\": \"$initial_hash\"}"

    # Local file with different content
    printf '%s\n' "updated local plan" > "$TEST_DIR/plans/TASK-004.md"

    # Remote comment also different
    _setup_gh_mock_detailed \
        '{"id": 22222, "body": "<!-- wiggum:plan -->\nupdated remote plan"}' \
        "" '{"id": 22222}'

    github_plan_sync_task "$TEST_DIR" "TASK-004" "false" "up"

    # State should reflect local content hash
    local state
    state=$(github_sync_state_get_task "$TEST_DIR" "TASK-004")
    local hash
    hash=$(echo "$state" | jq -r '.plan_content_hash')
    local expected_hash
    expected_hash=$(github_sync_hash_content "updated local plan")
    assert_equals "$expected_hash" "$hash" "Hash should match local content after force up"
}

# =============================================================================
# Force Down -> Remote Wins
# =============================================================================

test_force_down_remote_wins() {
    local initial_hash
    initial_hash=$(github_sync_hash_content "original content")

    _create_tracked_task "TASK-005" 80 \
        "{\"plan_comment_id\": 33333, \"plan_content_hash\": \"$initial_hash\"}"

    # Local file with different content
    printf '%s\n' "updated local plan" > "$TEST_DIR/plans/TASK-005.md"

    # Remote comment also different
    _setup_gh_mock_detailed \
        '{"id": 33333, "body": "<!-- wiggum:plan -->\nupdated remote plan"}' \
        "" ""

    github_plan_sync_task "$TEST_DIR" "TASK-005" "false" "down"

    # Local file should now contain remote content
    assert_file_contains "$TEST_DIR/plans/TASK-005.md" "updated remote plan" \
        "Local file should have remote content after force down"
}

# =============================================================================
# Dry Run -> No Changes
# =============================================================================

test_dry_run_no_changes_push() {
    _create_tracked_task "TASK-006" 90

    printf '%s\n' "# Dry run plan" > "$TEST_DIR/plans/TASK-006.md"

    # Mock: no existing comment
    _setup_gh_mock_detailed "" '{"id": 55555}' ""

    local output
    output=$(github_plan_sync_task "$TEST_DIR" "TASK-006" "true" "" 2>&1)

    assert_output_contains "$output" "[dry-run]" "Should show dry-run prefix"
    assert_output_contains "$output" "TASK-006" "Should mention task ID"

    # State should NOT have plan_comment_id
    local state
    state=$(github_sync_state_get_task "$TEST_DIR" "TASK-006")
    local comment_id
    comment_id=$(echo "$state" | jq -r '.plan_comment_id // "null"')
    assert_equals "null" "$comment_id" "Should not write state in dry-run"
}

test_dry_run_no_changes_pull() {
    _create_tracked_task "TASK-007" 95

    # No local file, remote exists
    _setup_gh_mock_detailed \
        '{"id": 66666, "body": "<!-- wiggum:plan -->\n# Remote Only"}' \
        "" ""

    local output
    output=$(github_plan_sync_task "$TEST_DIR" "TASK-007" "true" "" 2>&1)

    assert_output_contains "$output" "[dry-run]" "Should show dry-run prefix"
    assert_file_not_exists "$TEST_DIR/plans/TASK-007.md" "Should not create file in dry-run"
}

test_dry_run_conflict() {
    local initial_hash
    initial_hash=$(github_sync_hash_content "original content")

    _create_tracked_task "TASK-008" 100 \
        "{\"plan_comment_id\": 44444, \"plan_content_hash\": \"$initial_hash\"}"

    printf '%s\n' "local change" > "$TEST_DIR/plans/TASK-008.md"

    _setup_gh_mock_detailed \
        '{"id": 44444, "body": "<!-- wiggum:plan -->\nremote change"}' \
        "" ""

    local output exit_code=0
    output=$(github_plan_sync_task "$TEST_DIR" "TASK-008" "true" "" 2>&1) || exit_code=$?

    assert_equals "1" "$exit_code" "Should return 1 for conflict even in dry-run"
    assert_output_contains "$output" "CONFLICT" "Should show conflict message"
}

# =============================================================================
# Skip Conditions
# =============================================================================

test_skip_no_sync_state() {
    # Task not in sync state at all
    printf '%s\n' "orphan plan" > "$TEST_DIR/plans/TASK-ORPHAN.md"

    local exit_code=0
    github_plan_sync_task "$TEST_DIR" "TASK-ORPHAN" "false" "" || exit_code=$?

    assert_equals "0" "$exit_code" "Should skip gracefully for untracked task"
}

test_skip_no_issue_number() {
    # Task in sync state but no issue_number
    github_sync_state_set_task "$TEST_DIR" "TASK-NOISSUE" '{"description_hash":"sha256:abc"}'

    printf '%s\n' "some plan" > "$TEST_DIR/plans/TASK-NOISSUE.md"

    local exit_code=0
    github_plan_sync_task "$TEST_DIR" "TASK-NOISSUE" "false" "" || exit_code=$?

    assert_equals "0" "$exit_code" "Should skip gracefully for task without issue_number"
}

test_skip_in_sync() {
    local content="already synced content"
    local hash
    hash=$(github_sync_hash_content "$content")

    _create_tracked_task "TASK-009" 110 \
        "{\"plan_comment_id\": 88888, \"plan_content_hash\": \"$hash\"}"

    printf '%s' "$content" > "$TEST_DIR/plans/TASK-009.md"

    # Remote has same content
    _setup_gh_mock_detailed \
        "{\"id\": 88888, \"body\": \"<!-- wiggum:plan -->\\n$content\"}" \
        "" ""

    local exit_code=0
    github_plan_sync_task "$TEST_DIR" "TASK-009" "false" "" || exit_code=$?

    assert_equals "0" "$exit_code" "Should skip when in sync"
}

# =============================================================================
# Sync All
# =============================================================================

test_sync_all_discovers_local_plans() {
    _create_tracked_task "TASK-010" 120
    _create_tracked_task "TASK-011" 121

    printf '%s\n' "plan 10" > "$TEST_DIR/plans/TASK-010.md"
    printf '%s\n' "plan 11" > "$TEST_DIR/plans/TASK-011.md"

    # Mock: no existing comments, create returns ID
    _setup_gh_mock_detailed "" '50000' ""

    local output
    output=$(github_plan_sync_all "$TEST_DIR" "false" "" 2>&1)

    assert_output_contains "$output" "2 synced" "Should sync both tasks"
}

test_sync_all_no_plans() {
    # No local plan files, no remote comments tracked
    local output
    output=$(github_plan_sync_all "$TEST_DIR" "false" "" 2>&1)

    assert_output_contains "$output" "No plans to sync" "Should report no plans"
}

# =============================================================================
# Skip Completed Tasks in Bulk Sync
# =============================================================================

test_sync_all_skips_completed_tasks() {
    # Completed task (status "x") with a plan — should be skipped in bulk sync
    _create_tracked_task "TASK-DONE" 200 '{"last_synced_status": "x"}'
    printf '%s\n' "completed plan" > "$TEST_DIR/plans/TASK-DONE.md"

    # Active task — should be synced
    _create_tracked_task "TASK-ACTIVE" 201
    printf '%s\n' "active plan" > "$TEST_DIR/plans/TASK-ACTIVE.md"

    _setup_gh_mock_detailed "" '60000' ""

    local output
    output=$(github_plan_sync_all "$TEST_DIR" "false" "" 2>&1)

    assert_output_contains "$output" "1 synced" "Should sync only the active task"
    assert_output_contains "$output" "1 skipped" "Should skip the completed task"
}

test_sync_all_skips_failed_and_not_planned() {
    _create_tracked_task "TASK-FAIL" 210 '{"last_synced_status": "*"}'
    printf '%s\n' "failed plan" > "$TEST_DIR/plans/TASK-FAIL.md"

    _create_tracked_task "TASK-NP" 211 '{"last_synced_status": "N"}'
    printf '%s\n' "not planned" > "$TEST_DIR/plans/TASK-NP.md"

    _setup_gh_mock_detailed "" '61000' ""

    local output
    output=$(github_plan_sync_all "$TEST_DIR" "false" "" 2>&1)

    assert_output_contains "$output" "2 skipped" "Should skip both terminal tasks"
}

test_explicit_task_id_syncs_completed() {
    # Completed task — bulk sync skips it, but explicit TASK-ID should still work
    _create_tracked_task "TASK-COMP" 220 '{"last_synced_status": "x"}'
    printf '%s\n' "completed plan content" > "$TEST_DIR/plans/TASK-COMP.md"

    _setup_gh_mock_detailed "" '70000' ""

    local exit_code=0
    github_plan_sync_task "$TEST_DIR" "TASK-COMP" "false" "" || exit_code=$?

    assert_equals "0" "$exit_code" "Explicit sync should succeed for completed task"

    # Verify it actually synced (state has plan_comment_id)
    local state
    state=$(github_sync_state_get_task "$TEST_DIR" "TASK-COMP")
    local comment_id
    comment_id=$(echo "$state" | jq -r '.plan_comment_id')
    assert_equals "70000" "$comment_id" "Should have synced despite completed status"
}

# =============================================================================
# Run all tests
# =============================================================================
run_test test_strip_plan_marker
run_test test_strip_plan_marker_no_content
run_test test_local_only_creates_comment
run_test test_remote_only_creates_local_file
run_test test_both_changed_conflict
run_test test_force_up_local_wins
run_test test_force_down_remote_wins
run_test test_dry_run_no_changes_push
run_test test_dry_run_no_changes_pull
run_test test_dry_run_conflict
run_test test_skip_no_sync_state
run_test test_skip_no_issue_number
run_test test_skip_in_sync
run_test test_sync_all_discovers_local_plans
run_test test_sync_all_no_plans
run_test test_sync_all_skips_completed_tasks
run_test test_sync_all_skips_failed_and_not_planned
run_test test_explicit_task_id_syncs_completed

print_test_summary
exit_with_test_result
