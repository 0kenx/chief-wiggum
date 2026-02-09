#!/usr/bin/env bash
set -euo pipefail
# Test GitHub issue sync logic (lib/github/issue-sync.sh)
#
# These tests mock the `gh` CLI and `timeout` to test sync behavior
# without real GitHub API calls.

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"
source "$WIGGUM_HOME/lib/github/issue-config.sh"
source "$WIGGUM_HOME/lib/github/issue-state.sh"
source "$WIGGUM_HOME/lib/github/issue-parser.sh"
source "$WIGGUM_HOME/lib/github/issue-writer.sh"
source "$WIGGUM_HOME/lib/github/issue-sync.sh"

# Suppress log output in tests
LOG_LEVEL=ERROR
export LOG_LEVEL

TEST_DIR=""
MOCK_BIN=""

setup() {
    TEST_DIR=$(mktemp -d)
    MOCK_BIN="$TEST_DIR/bin"
    mkdir -p "$MOCK_BIN" "$TEST_DIR/.ralph"

    # Set config globals for tests
    GITHUB_SYNC_ENABLED="true"
    GITHUB_SYNC_ALLOWED_USER_IDS="12345"
    GITHUB_SYNC_LABEL_FILTER="wiggum"
    GITHUB_SYNC_DEFAULT_PRIORITY="MEDIUM"
    # shellcheck disable=SC2089 # JSON strings, not bash arrays
    GITHUB_SYNC_PRIORITY_LABELS='{"priority:critical":"CRITICAL","priority:high":"HIGH","priority:medium":"MEDIUM","priority:low":"LOW"}'
    # shellcheck disable=SC2089 # JSON strings, not bash arrays
    GITHUB_SYNC_STATUS_LABELS='{"wiggum:in-progress":"=","wiggum:pending-approval":"P","wiggum:completed":"x","wiggum:failed":"*","wiggum:not-planned":"N"}'
    # shellcheck disable=SC2089 # JSON strings, not bash arrays
    GITHUB_SYNC_COMPLEXITY_LABELS='{"complexity:high":"HIGH","complexity:medium":"MEDIUM","complexity:low":"LOW"}'
    GITHUB_SYNC_CLOSE_ON="x"
    export GITHUB_SYNC_ENABLED GITHUB_SYNC_ALLOWED_USER_IDS
    export GITHUB_SYNC_LABEL_FILTER GITHUB_SYNC_DEFAULT_PRIORITY
    # shellcheck disable=SC2090 # JSON strings passed to jq, not bash expansions
    export GITHUB_SYNC_PRIORITY_LABELS GITHUB_SYNC_STATUS_LABELS GITHUB_SYNC_CLOSE_ON
    # shellcheck disable=SC2090
    export GITHUB_SYNC_COMPLEXITY_LABELS

    # Create a basic kanban file
    cat > "$TEST_DIR/.ralph/kanban.md" << 'EOF'
# Kanban Board

## TASKS

- [ ] **[EXIST-1]** Existing pending task
  - Description: Already in kanban
  - Priority: LOW
  - Dependencies: none
- [=] **[EXIST-2]** In-progress task
  - Description: Currently being worked on
  - Priority: HIGH
  - Dependencies: none
EOF
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# Config Tests
# =============================================================================

test_config_is_enabled() {
    assert_success "Sync should be enabled" github_sync_is_enabled
}

test_config_is_disabled() {
    GITHUB_SYNC_ENABLED="false"
    assert_failure "Sync should be disabled" github_sync_is_enabled
    GITHUB_SYNC_ENABLED="true"
}

test_config_get_status_label() {
    local label
    label=$(github_sync_get_status_label "=")
    assert_equals "wiggum:in-progress" "$label" "Should map = to wiggum:in-progress"
}

test_config_get_status_label_completed() {
    local label
    label=$(github_sync_get_status_label "x")
    assert_equals "wiggum:completed" "$label" "Should map x to wiggum:completed"
}

test_config_get_status_char() {
    local char
    char=$(github_sync_get_status_char "wiggum:failed")
    assert_equals "*" "$char" "Should map wiggum:failed to *"
}

test_config_should_close() {
    assert_success "x should close" github_sync_should_close "x"
    assert_failure "N should not close" github_sync_should_close "N"
    assert_failure "= should not close" github_sync_should_close "="
    assert_failure "* should not close" github_sync_should_close "*"
}

# =============================================================================
# Author Validation
# =============================================================================

test_author_allowed_by_id() {
    assert_success "User 12345 should be allowed" \
        github_sync_is_author_allowed "12345"
}

test_author_not_allowed() {
    assert_failure "Unknown user should not be allowed" \
        github_sync_is_author_allowed "99999"
}

# =============================================================================
# Priority from Labels
# =============================================================================

test_priority_from_labels() {
    local result
    result=$(github_sync_get_priority_from_labels '[{"name":"wiggum"},{"name":"priority:high"}]')
    assert_equals "HIGH" "$result" "Should extract HIGH from labels"
}

test_priority_from_labels_multiple() {
    local result
    result=$(github_sync_get_priority_from_labels '[{"name":"priority:low"},{"name":"priority:critical"}]')
    assert_equals "CRITICAL" "$result" "Should pick highest priority"
}

test_priority_from_labels_none() {
    local result
    result=$(github_sync_get_priority_from_labels '[{"name":"wiggum"},{"name":"bug"}]')
    assert_equals "" "$result" "Should return empty with no priority labels"
}

# =============================================================================
# Kanban Task Management
# =============================================================================

test_add_kanban_task() {
    local kanban="$TEST_DIR/.ralph/kanban.md"
    add_kanban_task "$kanban" "GH-42" "Add dark mode" \
        "Support dark/light toggling" "HIGH" "GH-30" ""

    assert_file_contains "$kanban" "**[GH-42]**" "Should add task ID"
    assert_file_contains "$kanban" "Add dark mode" "Should add brief"
    assert_file_contains "$kanban" "Priority: HIGH" "Should add priority"
    assert_file_contains "$kanban" "Dependencies: GH-30" "Should add dependencies"
}

test_add_kanban_task_duplicate() {
    local kanban="$TEST_DIR/.ralph/kanban.md"

    local exit_code=0
    add_kanban_task "$kanban" "EXIST-1" "Duplicate" "Desc" "MEDIUM" "none" "" || exit_code=$?

    assert_equals "1" "$exit_code" "Should fail on duplicate task"
}

test_add_kanban_task_with_extra_fields() {
    local kanban="$TEST_DIR/.ralph/kanban.md"
    local extras
    extras=$(printf 'Complexity: HIGH\nScope: Build feature X')

    add_kanban_task "$kanban" "GH-99" "New feature" \
        "Build it" "MEDIUM" "none" "$extras"

    assert_file_contains "$kanban" "Complexity: HIGH" "Should add complexity"
    assert_file_contains "$kanban" "Scope: Build feature X" "Should add scope"
}

test_update_kanban_task_fields() {
    local kanban="$TEST_DIR/.ralph/kanban.md"

    update_kanban_task_fields "$kanban" "EXIST-1" \
        "Updated description" "HIGH" "EXIST-2"

    assert_file_contains "$kanban" "Description: Updated description" "Should update description"
    assert_file_contains "$kanban" "Priority: HIGH" "Should update priority"
    assert_file_contains "$kanban" "Dependencies: EXIST-2" "Should update dependencies"
}

test_update_kanban_task_fields_not_found() {
    local kanban="$TEST_DIR/.ralph/kanban.md"

    local exit_code=0
    update_kanban_task_fields "$kanban" "NONEXIST-1" "Desc" "HIGH" "none" || exit_code=$?

    assert_equals "1" "$exit_code" "Should fail for non-existent task"
}

# =============================================================================
# State Management Integration
# =============================================================================

test_state_full_lifecycle() {
    local ralph_dir="$TEST_DIR/.ralph"

    # Init
    github_sync_state_init "$ralph_dir"
    assert_file_exists "$ralph_dir/github-sync-state.json" "State file should exist"

    # Add task entry (keyed by task_id, entry contains issue_number)
    local entry
    entry=$(github_sync_state_create_entry 42 "2025-01-23T12:00:00Z" " " "open" "sha256:abc")
    github_sync_state_set_task "$ralph_dir" "GH-42" "$entry"

    # Verify by task_id
    local retrieved
    retrieved=$(github_sync_state_get_task "$ralph_dir" "GH-42")
    local issue_number
    issue_number=$(echo "$retrieved" | jq -r '.issue_number')
    assert_equals "42" "$issue_number" "Should retrieve stored issue number"

    # Verify reverse lookup by issue number
    local found_task
    found_task=$(github_sync_state_find_task_by_issue "$ralph_dir" "42")
    assert_equals "GH-42" "$found_task" "Should find task by issue number"

    # Update timestamps
    github_sync_state_set_down_sync_time "$ralph_dir" 1706000000
    github_sync_state_set_up_sync_time "$ralph_dir" 1706000100

    # Verify timestamps
    local down_ts up_ts
    down_ts=$(jq -r '.last_down_sync_at' "$ralph_dir/github-sync-state.json")
    up_ts=$(jq -r '.last_up_sync_at' "$ralph_dir/github-sync-state.json")
    assert_equals "1706000000" "$down_ts" "Should have down sync timestamp"
    assert_equals "1706000100" "$up_ts" "Should have up sync timestamp"

    # List tasks
    local tasks
    tasks=$(github_sync_state_list_tasks "$ralph_dir")
    assert_output_contains "$tasks" "GH-42" "Should list task GH-42"

    # Remove
    github_sync_state_remove_task "$ralph_dir" "GH-42"
    local after
    after=$(github_sync_state_get_task "$ralph_dir" "GH-42")
    assert_equals "null" "$after" "Should be null after removal"
}

# =============================================================================
# Issue Writer Status Mapping
# =============================================================================

test_writer_status_name_mapping() {
    # Test the internal _kanban_status_name function via its use in update_status
    # We can't call _kanban_status_name directly since it's in issue-writer.sh
    # but we can verify the status labels work correctly

    local label
    label=$(github_sync_get_status_label " ")
    assert_equals "" "$label" "Pending should have no label"

    label=$(github_sync_get_status_label "=")
    assert_equals "wiggum:in-progress" "$label" "In-progress label"

    label=$(github_sync_get_status_label "P")
    assert_equals "wiggum:pending-approval" "$label" "Pending approval label"

    label=$(github_sync_get_status_label "x")
    assert_equals "wiggum:completed" "$label" "Completed label"

    label=$(github_sync_get_status_label "*")
    assert_equals "wiggum:failed" "$label" "Failed label"

    label=$(github_sync_get_status_label "N")
    assert_equals "wiggum:not-planned" "$label" "Not-planned label"
}

# =============================================================================
# Kanban Task Enumeration (for sync up create)
# =============================================================================

test_list_all_kanban_task_ids() {
    local kanban="$TEST_DIR/.ralph/kanban.md"
    local result
    result=$(_list_all_kanban_task_ids "$kanban")

    assert_output_contains "$result" "EXIST-1" "Should list EXIST-1"
    assert_output_contains "$result" "EXIST-2" "Should list EXIST-2"
}

test_parse_kanban_task_fields() {
    local kanban="$TEST_DIR/.ralph/kanban.md"
    local result
    result=$(_parse_kanban_task_fields "$kanban" "EXIST-1")

    assert_not_empty "$result" "Should return non-empty JSON"

    local brief priority status
    brief=$(echo "$result" | jq -r '.brief')
    priority=$(echo "$result" | jq -r '.priority')
    status=$(echo "$result" | jq -r '.status')

    assert_equals "Existing pending task" "$brief" "Should extract brief"
    assert_equals "LOW" "$priority" "Should extract priority"
    assert_equals " " "$status" "Should extract pending status"
}

test_parse_kanban_task_fields_in_progress() {
    local kanban="$TEST_DIR/.ralph/kanban.md"
    local result
    result=$(_parse_kanban_task_fields "$kanban" "EXIST-2")

    local status priority
    status=$(echo "$result" | jq -r '.status')
    priority=$(echo "$result" | jq -r '.priority')

    assert_equals "=" "$status" "Should extract in-progress status"
    assert_equals "HIGH" "$priority" "Should extract priority"
}

test_parse_kanban_task_fields_not_found() {
    local kanban="$TEST_DIR/.ralph/kanban.md"
    local result
    result=$(_parse_kanban_task_fields "$kanban" "NONEXIST-99")

    assert_equals "" "$result" "Should return empty for non-existent task"
}

test_get_untracked_task_ids_all_untracked() {
    local ralph_dir="$TEST_DIR/.ralph"
    local kanban="$ralph_dir/kanban.md"

    github_sync_state_init "$ralph_dir"

    local result
    result=$(_get_untracked_task_ids "$kanban" "$ralph_dir")

    assert_output_contains "$result" "EXIST-1" "EXIST-1 should be untracked"
    assert_output_contains "$result" "EXIST-2" "EXIST-2 should be untracked"
}

test_get_untracked_task_ids_some_tracked() {
    local ralph_dir="$TEST_DIR/.ralph"
    local kanban="$ralph_dir/kanban.md"

    github_sync_state_init "$ralph_dir"

    # Track EXIST-1
    local entry
    entry=$(github_sync_state_create_entry 10 "" " " "open" "sha256:abc")
    github_sync_state_set_task "$ralph_dir" "EXIST-1" "$entry"

    local result
    result=$(_get_untracked_task_ids "$kanban" "$ralph_dir")

    assert_output_not_contains "$result" "EXIST-1" "EXIST-1 should be tracked"
    assert_output_contains "$result" "EXIST-2" "EXIST-2 should still be untracked"
}

# =============================================================================
# Issue Creation (github_issue_create)
# =============================================================================

test_issue_create_mock() {
    local kanban="$TEST_DIR/.ralph/kanban.md"
    local ralph_dir="$TEST_DIR/.ralph"

    # Create mock gh that outputs a URL
    cat > "$MOCK_BIN/gh" << 'MOCK'
#!/usr/bin/env bash
if [[ "$1" == "issue" && "$2" == "create" ]]; then
    echo "https://github.com/test/repo/issues/42"
    exit 0
fi
exit 1
MOCK
    chmod +x "$MOCK_BIN/gh"

    # Create mock timeout that just runs the command
    cat > "$MOCK_BIN/timeout" << 'MOCK'
#!/usr/bin/env bash
shift  # skip timeout value
"$@"
MOCK
    chmod +x "$MOCK_BIN/timeout"

    local old_path="$PATH"
    export PATH="$MOCK_BIN:$PATH"

    local issue_num
    issue_num=$(github_issue_create "TEST-1" "Test task" "Task body" "priority:high")

    export PATH="$old_path"

    assert_equals "42" "$issue_num" "Should extract issue number from URL"
}

# =============================================================================
# Sync Up Create (dry run + flow)
# =============================================================================

test_sync_up_create_dry_run() {
    local ralph_dir="$TEST_DIR/.ralph"
    local kanban="$ralph_dir/kanban.md"

    github_sync_state_init "$ralph_dir"

    local output
    output=$(github_issue_sync_up_create "$ralph_dir" "all" "true" "true" 2>&1)

    assert_output_contains "$output" "dry-run" "Should show dry-run marker"
    assert_output_contains "$output" "EXIST-1" "Should list EXIST-1"
    assert_output_contains "$output" "EXIST-2" "Should list EXIST-2"
}

test_sync_up_create_dry_run_single() {
    local ralph_dir="$TEST_DIR/.ralph"
    local kanban="$ralph_dir/kanban.md"

    github_sync_state_init "$ralph_dir"

    local output
    output=$(github_issue_sync_up_create "$ralph_dir" "EXIST-1" "true" "true" 2>&1)

    assert_output_contains "$output" "dry-run" "Should show dry-run marker"
    assert_output_contains "$output" "EXIST-1" "Should list EXIST-1"
}

test_sync_up_create_nonexistent_task() {
    local ralph_dir="$TEST_DIR/.ralph"

    github_sync_state_init "$ralph_dir"

    local exit_code=0
    github_issue_sync_up_create "$ralph_dir" "FAKE-999" "false" "true" 2>/dev/null || exit_code=$?

    assert_equals "1" "$exit_code" "Should fail for non-existent task"
}

test_sync_up_create_already_tracked() {
    local ralph_dir="$TEST_DIR/.ralph"
    local kanban="$ralph_dir/kanban.md"

    github_sync_state_init "$ralph_dir"

    # Track EXIST-1
    local entry
    entry=$(github_sync_state_create_entry 10 "" " " "open" "sha256:abc")
    github_sync_state_set_task "$ralph_dir" "EXIST-1" "$entry"

    local output
    output=$(github_issue_sync_up_create "$ralph_dir" "EXIST-1" "false" "true" 2>&1)

    assert_output_contains "$output" "already tracked" "Should report already tracked"
}

test_sync_up_create_no_untracked() {
    local ralph_dir="$TEST_DIR/.ralph"
    local kanban="$ralph_dir/kanban.md"

    github_sync_state_init "$ralph_dir"

    # Track both tasks
    local entry1 entry2
    entry1=$(github_sync_state_create_entry 10 "" " " "open" "sha256:abc")
    github_sync_state_set_task "$ralph_dir" "EXIST-1" "$entry1"
    entry2=$(github_sync_state_create_entry 11 "" "=" "open" "sha256:def")
    github_sync_state_set_task "$ralph_dir" "EXIST-2" "$entry2"

    local output
    output=$(github_issue_sync_up_create "$ralph_dir" "all" "false" "true" 2>&1)

    assert_output_contains "$output" "No untracked tasks" "Should report no untracked tasks"
}

test_build_issue_body() {
    local kanban="$TEST_DIR/.ralph/kanban_body_test.md"
    cat > "$kanban" << 'EOF'
- [ ] **[BODY-1]** Some task title
  - Description: Some description
  - Priority: HIGH
  - Dependencies: TASK-001, TASK-002
  - Scope:
    - Implement feature X
    - Add tests
  - Acceptance Criteria:
    - Feature X works
EOF

    local body
    body=$(_build_issue_body "$kanban" "BODY-1")

    assert_output_contains "$body" "Some description" "Should contain description"
    assert_output_contains "$body" "Priority" "Should contain priority"
    assert_output_contains "$body" "Dependencies" "Should contain dependencies"
    assert_output_contains "$body" "Scope" "Should contain scope"
    assert_output_contains "$body" "Implement feature X" "Should contain scope items"
    assert_output_contains "$body" "Acceptance Criteria" "Should contain acceptance criteria"
    assert_output_contains "$body" "Feature X works" "Should contain AC items"
}

test_get_priority_label() {
    local label
    label=$(_get_priority_label "HIGH")
    assert_equals "priority:high" "$label" "Should map HIGH to priority:high"

    label=$(_get_priority_label "CRITICAL")
    assert_equals "priority:critical" "$label" "Should map CRITICAL to priority:critical"
}

# =============================================================================
# Complexity from Labels
# =============================================================================

test_complexity_from_labels() {
    local result
    result=$(github_sync_get_complexity_from_labels '[{"name":"wiggum"},{"name":"complexity:high"}]')
    assert_equals "HIGH" "$result" "Should extract HIGH from labels"
}

test_complexity_from_labels_none() {
    local result
    result=$(github_sync_get_complexity_from_labels '[{"name":"wiggum"},{"name":"bug"}]')
    assert_equals "" "$result" "Should return empty with no complexity labels"
}

test_get_complexity_label() {
    local label
    label=$(_get_complexity_label "HIGH")
    assert_equals "complexity:high" "$label" "Should map HIGH to complexity:high"

    label=$(_get_complexity_label "LOW")
    assert_equals "complexity:low" "$label" "Should map LOW to complexity:low"

    label=$(_get_complexity_label "")
    assert_equals "" "$label" "Should return empty for empty complexity"
}

test_parse_kanban_task_fields_with_complexity() {
    local kanban="$TEST_DIR/.ralph/kanban_comp_test.md"
    cat > "$kanban" << 'EOF'
# Kanban Board

## TASKS

- [ ] **[COMP-1]** Task with complexity
  - Description: A complex task
  - Priority: HIGH
  - Complexity: MEDIUM
  - Dependencies: none
EOF

    local result
    result=$(_parse_kanban_task_fields "$kanban" "COMP-1")

    assert_not_empty "$result" "Should return non-empty JSON"

    local complexity priority
    complexity=$(echo "$result" | jq -r '.complexity')
    priority=$(echo "$result" | jq -r '.priority')

    assert_equals "MEDIUM" "$complexity" "Should extract complexity"
    assert_equals "HIGH" "$priority" "Should extract priority"
}

# =============================================================================
# Read-Only Operations Must Not Modify kanban.md
# =============================================================================

_kanban_checksum() {
    sha256sum "$1" | cut -d' ' -f1
}

test_readonly_list_task_ids() {
    local kanban="$TEST_DIR/.ralph/kanban.md"
    local before after
    before=$(_kanban_checksum "$kanban")
    _list_all_kanban_task_ids "$kanban" > /dev/null
    after=$(_kanban_checksum "$kanban")
    assert_equals "$before" "$after" "list_all_kanban_task_ids must not modify kanban"
}

test_readonly_parse_kanban_fields() {
    local kanban="$TEST_DIR/.ralph/kanban.md"
    local before after
    before=$(_kanban_checksum "$kanban")
    _parse_kanban_task_fields "$kanban" "EXIST-1" > /dev/null
    _parse_kanban_task_fields "$kanban" "NONEXIST-99" > /dev/null
    after=$(_kanban_checksum "$kanban")
    assert_equals "$before" "$after" "parse_kanban_task_fields must not modify kanban"
}

test_readonly_kanban_task_exists() {
    local kanban="$TEST_DIR/.ralph/kanban.md"
    local before after
    before=$(_kanban_checksum "$kanban")
    _kanban_task_exists "$kanban" "EXIST-1"
    _kanban_task_exists "$kanban" "NONEXIST-99" || true
    after=$(_kanban_checksum "$kanban")
    assert_equals "$before" "$after" "kanban_task_exists must not modify kanban"
}

test_readonly_get_kanban_status() {
    local kanban="$TEST_DIR/.ralph/kanban.md"
    local before after
    before=$(_kanban_checksum "$kanban")
    _get_kanban_status "$kanban" "EXIST-1" > /dev/null
    _get_kanban_status "$kanban" "EXIST-2" > /dev/null
    after=$(_kanban_checksum "$kanban")
    assert_equals "$before" "$after" "get_kanban_status must not modify kanban"
}

test_readonly_get_untracked_ids() {
    local ralph_dir="$TEST_DIR/.ralph"
    local kanban="$ralph_dir/kanban.md"
    github_sync_state_init "$ralph_dir"

    local before after
    before=$(_kanban_checksum "$kanban")
    _get_untracked_task_ids "$kanban" "$ralph_dir" > /dev/null
    after=$(_kanban_checksum "$kanban")
    assert_equals "$before" "$after" "get_untracked_task_ids must not modify kanban"
}

test_readonly_dry_run_up_create() {
    local ralph_dir="$TEST_DIR/.ralph"
    local kanban="$ralph_dir/kanban.md"
    github_sync_state_init "$ralph_dir"

    local before after
    before=$(_kanban_checksum "$kanban")
    github_issue_sync_up_create "$ralph_dir" "all" "true" "true" > /dev/null 2>&1
    after=$(_kanban_checksum "$kanban")
    assert_equals "$before" "$after" "sync_up_create dry_run must not modify kanban"
}

# =============================================================================
# End-to-End: sync up create → sync down preserves kanban
# =============================================================================

test_sync_up_then_down_preserves_kanban() {
    local ralph_dir="$TEST_DIR/.ralph"
    local kanban="$ralph_dir/kanban.md"

    # Write the scenario kanban: completed + pending + pending-approval tasks
    cat > "$kanban" << 'KANBAN'
# Kanban Board

## TASKS

- [x] **[BUG-004]** Fix dead_code warning for EmbeddingData.index field
  - Description: `main.rs:29` has a dead_code warning for field `index` in `EmbeddingData` struct. The field is never read. Either use the field or remove it if unnecessary.
  - Priority: LOW
  - Complexity: LOW
  - Dependencies: none
  - Scope:
    - Check if `EmbeddingData.index` is needed for the embedding response parsing
    - If not needed: remove the field
    - If needed but unused: add `#[allow(dead_code)]` with justification comment
  - Acceptance Criteria:
    - Warning resolved
    - No functional regression

### Innovative / Exploratory

- [ ] **[INNOV-006]** Explore streaming/incremental ingestion pipeline (Strategy C)
  - Description: Per SPEC-DATA-PIPELINE Section 4.3 and 12.1, Strategy C supports streaming ingestion where content arrives piece by piece.
  - Priority: LOW
  - Complexity: HIGH
  - Dependencies: PIPE-002, PIPE-003
  - Scope:
    - Prototype sliding window segmenter
    - Evaluate latency characteristics vs Strategy A/B
  - Acceptance Criteria:
    - Prototype demonstrates streaming ingestion
    - Trade-offs and recommendation documented



- [P] **[INNOV-007]** Explore multi-modal embedding integration (vision + audio)
  - Description: Per SPEC-DATA-PIPELINE Section 6, the pipeline should eventually handle images and audio.
  - Priority: LOW
  - Complexity: HIGH
  - Dependencies: PIPE-007, EMBED-001
  - Scope:
    - Evaluate vision embedding models (CLIP, SigLIP, Qwen2-VL)
    - Prototype image embedding pipeline stage
  - Acceptance Criteria:
    - Image embedding prototype working
    - Architecture recommendation documented
KANBAN

    github_sync_state_init "$ralph_dir"

    # --- Mock setup ---
    local counter_file="$TEST_DIR/issue_counter"
    echo "227" > "$counter_file"

    # Mock data for down sync: open issues (INNOV-006, INNOV-007)
    # Bodies include ## Checklist section (as produced by extract_task) to test
    # that the parser discards unrecognized sections and doesn't pollute description.
    # updatedAt is realistic (non-empty) to trigger the timestamp comparison path.
    local mock_open_issues="$TEST_DIR/mock_open_issues.json"
    cat > "$mock_open_issues" << 'JSON'
[
  {
    "number": 228,
    "title": "[INNOV-006] Explore streaming/incremental ingestion pipeline (Strategy C)",
    "body": "# Task: INNOV-006 - Explore streaming/incremental ingestion pipeline (Strategy C)\n\n## Description\nPer SPEC-DATA-PIPELINE Section 4.3 and 12.1, Strategy C supports streaming ingestion where content arrives piece by piece.\n\n## Priority\nLOW\n\n## Dependencies\nPIPE-002, PIPE-003\n\n## Scope\n\n- Prototype sliding window segmenter\n- Evaluate latency characteristics vs Strategy A/B\n\n## Acceptance Criteria\n\n- Prototype demonstrates streaming ingestion\n- Trade-offs and recommendation documented\n\n## Checklist\n\n- [ ] Prototype sliding window segmenter\n- [ ] Evaluate latency characteristics vs Strategy A/B\n- [ ] Mark this PRD as complete",
    "labels": [{"name": "wiggum"}, {"name": "priority:low"}],
    "author": {"login": "testuser", "id": "12345"},
    "state": "OPEN",
    "updatedAt": "2025-01-23T15:00:00Z"
  },
  {
    "number": 229,
    "title": "[INNOV-007] Explore multi-modal embedding integration (vision + audio)",
    "body": "# Task: INNOV-007 - Explore multi-modal embedding integration (vision + audio)\n\n## Description\nPer SPEC-DATA-PIPELINE Section 6, the pipeline should eventually handle images and audio.\n\n## Priority\nLOW\n\n## Dependencies\nPIPE-007, EMBED-001\n\n## Scope\n\n- Evaluate vision embedding models (CLIP, SigLIP, Qwen2-VL)\n- Prototype image embedding pipeline stage\n\n## Acceptance Criteria\n\n- Image embedding prototype working\n- Architecture recommendation documented\n\n## Checklist\n\n- [ ] Evaluate vision embedding models (CLIP, SigLIP, Qwen2-VL)\n- [ ] Prototype image embedding pipeline stage\n- [ ] Mark this PRD as complete",
    "labels": [{"name": "wiggum"}, {"name": "priority:low"}, {"name": "wiggum:pending-approval"}],
    "author": {"login": "testuser", "id": "12345"},
    "state": "OPEN",
    "updatedAt": "2025-01-23T15:00:00Z"
  }
]
JSON

    # Mock data for down sync: closed issues (BUG-004)
    local mock_closed_issues="$TEST_DIR/mock_closed_issues.json"
    cat > "$mock_closed_issues" << 'JSON'
[
  {
    "number": 227,
    "title": "[BUG-004] Fix dead_code warning for EmbeddingData.index field",
    "state": "CLOSED",
    "updatedAt": "2025-01-23T12:00:00Z"
  }
]
JSON

    # Mock gh: handles issue create/edit/close/comment/list
    export MOCK_COUNTER_FILE="$counter_file"
    export MOCK_OPEN_ISSUES="$mock_open_issues"
    export MOCK_CLOSED_ISSUES="$mock_closed_issues"

    cat > "$MOCK_BIN/gh" << 'MOCK'
#!/usr/bin/env bash
if [[ "$1" == "issue" ]]; then
    case "$2" in
        create)
            num=$(cat "$MOCK_COUNTER_FILE")
            echo "$((num + 1))" > "$MOCK_COUNTER_FILE"
            echo "https://github.com/test/repo/issues/$num"
            ;;
        edit|comment|close|reopen)
            exit 0
            ;;
        list)
            state=""
            shift 2
            while [[ $# -gt 0 ]]; do
                case "$1" in
                    --state) state="$2"; shift 2 ;;
                    *) shift ;;
                esac
            done
            if [[ "$state" == "open" ]]; then
                cat "$MOCK_OPEN_ISSUES"
            elif [[ "$state" == "closed" ]]; then
                cat "$MOCK_CLOSED_ISSUES"
            fi
            ;;
    esac
fi
MOCK
    chmod +x "$MOCK_BIN/gh"

    cat > "$MOCK_BIN/timeout" << 'MOCK'
#!/usr/bin/env bash
shift
"$@"
MOCK
    chmod +x "$MOCK_BIN/timeout"

    local old_path="$PATH"
    export PATH="$MOCK_BIN:$PATH"

    # --- Phase 1: sync up create all ---
    github_issue_sync_up_create "$ralph_dir" "all" "false" "true" > /dev/null 2>&1

    # Verify state has all 3 tasks with correct issue numbers
    local state_file="$ralph_dir/github-sync-state.json"
    local tracked_count
    tracked_count=$(jq '.issues | length' "$state_file")
    assert_equals "3" "$tracked_count" "Should track 3 tasks after sync up create"

    local bug_num innov6_num innov7_num
    bug_num=$(jq -r '.issues["BUG-004"].issue_number' "$state_file")
    innov6_num=$(jq -r '.issues["INNOV-006"].issue_number' "$state_file")
    innov7_num=$(jq -r '.issues["INNOV-007"].issue_number' "$state_file")
    assert_equals "227" "$bug_num" "BUG-004 should map to issue #227"
    assert_equals "228" "$innov6_num" "INNOV-006 should map to issue #228"
    assert_equals "229" "$innov7_num" "INNOV-007 should map to issue #229"

    # Verify synced statuses match kanban
    local bug_status innov6_status innov7_status
    bug_status=$(jq -r '.issues["BUG-004"].last_synced_status' "$state_file")
    innov6_status=$(jq -r '.issues["INNOV-006"].last_synced_status' "$state_file")
    innov7_status=$(jq -r '.issues["INNOV-007"].last_synced_status' "$state_file")
    assert_equals "x" "$bug_status" "BUG-004 should have completed status"
    assert_equals " " "$innov6_status" "INNOV-006 should have pending status"
    assert_equals "P" "$innov7_status" "INNOV-007 should have pending-approval status"

    # --- Phase 2: sync down must not modify kanban ---
    local before after
    before=$(_kanban_checksum "$kanban")

    github_issue_sync_down "$ralph_dir" "false" > /dev/null 2>&1

    after=$(_kanban_checksum "$kanban")
    assert_equals "$before" "$after" "Down sync must not modify kanban after sync up create"

    export PATH="$old_path"
    unset MOCK_COUNTER_FILE MOCK_OPEN_ISSUES MOCK_CLOSED_ISSUES
}

# =============================================================================
# Run all tests
# =============================================================================
run_test test_config_is_enabled
run_test test_config_is_disabled
run_test test_config_get_status_label
run_test test_config_get_status_label_completed
run_test test_config_get_status_char
run_test test_config_should_close
run_test test_author_allowed_by_id
run_test test_author_not_allowed
run_test test_priority_from_labels
run_test test_priority_from_labels_multiple
run_test test_priority_from_labels_none
run_test test_add_kanban_task
run_test test_add_kanban_task_duplicate
run_test test_add_kanban_task_with_extra_fields
run_test test_update_kanban_task_fields
run_test test_update_kanban_task_fields_not_found
run_test test_state_full_lifecycle
run_test test_writer_status_name_mapping
run_test test_list_all_kanban_task_ids
run_test test_parse_kanban_task_fields
run_test test_parse_kanban_task_fields_in_progress
run_test test_parse_kanban_task_fields_not_found
run_test test_get_untracked_task_ids_all_untracked
run_test test_get_untracked_task_ids_some_tracked
run_test test_issue_create_mock
run_test test_sync_up_create_dry_run
run_test test_sync_up_create_dry_run_single
run_test test_sync_up_create_nonexistent_task
run_test test_sync_up_create_already_tracked
run_test test_sync_up_create_no_untracked
run_test test_build_issue_body
run_test test_get_priority_label
run_test test_complexity_from_labels
run_test test_complexity_from_labels_none
run_test test_get_complexity_label
run_test test_parse_kanban_task_fields_with_complexity
run_test test_readonly_list_task_ids
run_test test_readonly_parse_kanban_fields
run_test test_readonly_kanban_task_exists
run_test test_readonly_get_kanban_status
run_test test_readonly_get_untracked_ids
run_test test_readonly_dry_run_up_create
run_test test_sync_up_then_down_preserves_kanban

print_test_summary
exit_with_test_result
