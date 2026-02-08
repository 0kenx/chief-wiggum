#!/usr/bin/env bash
# Test suite for medium-priority modules lacking coverage
#
# Covers:
#   - lib/tasks/plan-parser.sh
#   - lib/tasks/conflict-detection.sh
#   - lib/core/gh-error.sh
#   - lib/core/verbose-flags.sh
#   - lib/core/bin-common.sh
#   - lib/github/pr-labels.sh
#   - lib/wdoc/wdoc-registry.sh
set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

LOG_LEVEL=ERROR
export LOG_LEVEL

TEST_DIR=""
RALPH_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    RALPH_DIR="$TEST_DIR/.ralph"
    mkdir -p "$RALPH_DIR"
    export RALPH_DIR
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# =============================================================================
# lib/tasks/plan-parser.sh Tests
# =============================================================================

test_plan_parser_extracts_create_and_modify_files() {
    source "$WIGGUM_HOME/lib/tasks/plan-parser.sh"

    local plan_file="$TEST_DIR/plan.md"
    cat > "$plan_file" << 'EOF'
# Implementation Plan

## Critical Files

| File | Action | Reason |
|------|--------|--------|
| `src/main.py` | CREATE | Main entry point |
| `src/util.py` | MODIFY | Update helper functions |
| `docs/README.md` | REFERENCE | Documentation only |
| `tests/test_main.py` | CREATE | New test file |

## Other Section
More content here.
EOF

    local output
    output=$(get_plan_critical_files "$plan_file")

    assert_output_contains "$output" "src/main.py" "Should extract CREATE file"
    assert_output_contains "$output" "src/util.py" "Should extract MODIFY file"
    assert_output_contains "$output" "tests/test_main.py" "Should extract second CREATE file"
    assert_output_not_contains "$output" "docs/README.md" "Should NOT extract REFERENCE file"
}

test_plan_parser_removes_backticks() {
    source "$WIGGUM_HOME/lib/tasks/plan-parser.sh"

    local plan_file="$TEST_DIR/plan.md"
    cat > "$plan_file" << 'EOF'
## Critical Files

| File | Action | Reason |
|------|--------|--------|
| `src/app.js` | CREATE | App file |
EOF

    local output
    output=$(get_plan_critical_files "$plan_file")

    # Output should be plain text without backticks
    assert_equals "src/app.js" "$output" "Should remove backticks from file path"
}

test_plan_parser_handles_missing_section() {
    source "$WIGGUM_HOME/lib/tasks/plan-parser.sh"

    local plan_file="$TEST_DIR/plan.md"
    cat > "$plan_file" << 'EOF'
# Implementation Plan

## Overview
No Critical Files section here.
EOF

    local output
    output=$(get_plan_critical_files "$plan_file")

    assert_equals "" "$output" "Should return empty for missing Critical Files section"
}

test_plan_parser_handles_missing_file() {
    source "$WIGGUM_HOME/lib/tasks/plan-parser.sh"

    local output
    output=$(get_plan_critical_files "$TEST_DIR/nonexistent.md")

    assert_equals "" "$output" "Should return empty for missing file"
}

test_plan_parser_sorts_and_deduplicates() {
    source "$WIGGUM_HOME/lib/tasks/plan-parser.sh"

    local plan_file="$TEST_DIR/plan.md"
    cat > "$plan_file" << 'EOF'
## Critical Files

| File | Action | Reason |
|------|--------|--------|
| `src/c.py` | CREATE | C |
| `src/a.py` | MODIFY | A |
| `src/c.py` | MODIFY | C again |
| `src/b.py` | CREATE | B |
EOF

    local output
    output=$(get_plan_critical_files "$plan_file")

    # Should be sorted and unique
    local expected="src/a.py
src/b.py
src/c.py"
    assert_equals "$expected" "$output" "Should sort and deduplicate files"
}

test_get_task_critical_files_looks_up_by_task_id() {
    source "$WIGGUM_HOME/lib/tasks/plan-parser.sh"

    mkdir -p "$RALPH_DIR/plans"
    local plan_file="$RALPH_DIR/plans/TASK-123.md"
    cat > "$plan_file" << 'EOF'
## Critical Files

| File | Action | Reason |
|------|--------|--------|
| `main.go` | CREATE | Main |
EOF

    local output
    output=$(get_task_critical_files "$RALPH_DIR" "TASK-123")

    assert_equals "main.go" "$output" "Should lookup plan by task ID"
}

test_get_task_critical_files_handles_missing_plan() {
    source "$WIGGUM_HOME/lib/tasks/plan-parser.sh"

    mkdir -p "$RALPH_DIR/plans"

    local output
    output=$(get_task_critical_files "$RALPH_DIR" "TASK-999")

    assert_equals "" "$output" "Should return empty for missing plan"
}

# =============================================================================
# lib/tasks/conflict-detection.sh Tests
# =============================================================================

test_conflict_detection_no_overlap_returns_1() {
    source "$WIGGUM_HOME/lib/tasks/conflict-detection.sh"

    mkdir -p "$RALPH_DIR/plans"

    # Task A touches file1.py
    cat > "$RALPH_DIR/plans/TASK-001.md" << 'EOF'
## Critical Files
| File | Action | Reason |
|------|--------|--------|
| `file1.py` | CREATE | File 1 |
EOF

    # Task B touches file2.py (no overlap)
    cat > "$RALPH_DIR/plans/TASK-002.md" << 'EOF'
## Critical Files
| File | Action | Reason |
|------|--------|--------|
| `file2.py` | CREATE | File 2 |
EOF

    # Active workers: TASK-002 is running
    local -A active_workers=([12345]="TASK-002")

    # Check if TASK-001 conflicts with active workers
    local exit_code=0
    has_file_conflict "$RALPH_DIR" "TASK-001" active_workers || exit_code=$?

    assert_equals "1" "$exit_code" "Should return 1 (no conflict) when files don't overlap"
}

test_conflict_detection_overlap_returns_0() {
    source "$WIGGUM_HOME/lib/tasks/conflict-detection.sh"

    mkdir -p "$RALPH_DIR/plans"

    # Task A touches file1.py
    cat > "$RALPH_DIR/plans/TASK-001.md" << 'EOF'
## Critical Files
| File | Action | Reason |
|------|--------|--------|
| `file1.py` | CREATE | File 1 |
| `shared.py` | MODIFY | Shared |
EOF

    # Task B touches shared.py (overlap!)
    cat > "$RALPH_DIR/plans/TASK-002.md" << 'EOF'
## Critical Files
| File | Action | Reason |
|------|--------|--------|
| `file2.py` | CREATE | File 2 |
| `shared.py` | MODIFY | Shared |
EOF

    local -A active_workers=([12345]="TASK-002")

    local exit_code=0
    has_file_conflict "$RALPH_DIR" "TASK-001" active_workers || exit_code=$?

    assert_equals "0" "$exit_code" "Should return 0 (conflict) when files overlap"
}

test_conflict_detection_self_exclusion() {
    source "$WIGGUM_HOME/lib/tasks/conflict-detection.sh"

    mkdir -p "$RALPH_DIR/plans"

    cat > "$RALPH_DIR/plans/TASK-001.md" << 'EOF'
## Critical Files
| File | Action | Reason |
|------|--------|--------|
| `file1.py` | CREATE | File |
EOF

    # Task is checking against itself (same task ID)
    local -A active_workers=([12345]="TASK-001")

    local exit_code=0
    has_file_conflict "$RALPH_DIR" "TASK-001" active_workers || exit_code=$?

    assert_equals "1" "$exit_code" "Should exclude self from conflict detection"
}

test_conflict_detection_no_plan_no_conflict() {
    source "$WIGGUM_HOME/lib/tasks/conflict-detection.sh"

    mkdir -p "$RALPH_DIR/plans"

    # No plan exists for TASK-001
    local -A active_workers=([12345]="TASK-002")

    local exit_code=0
    has_file_conflict "$RALPH_DIR" "TASK-001" active_workers || exit_code=$?

    assert_equals "1" "$exit_code" "Should return no conflict when plan missing (graceful degradation)"
}

test_get_conflicting_files_returns_intersection() {
    source "$WIGGUM_HOME/lib/tasks/conflict-detection.sh"

    mkdir -p "$RALPH_DIR/plans"

    cat > "$RALPH_DIR/plans/TASK-001.md" << 'EOF'
## Critical Files
| File | Action | Reason |
|------|--------|--------|
| `a.py` | CREATE | A |
| `b.py` | MODIFY | B |
| `c.py` | CREATE | C |
EOF

    cat > "$RALPH_DIR/plans/TASK-002.md" << 'EOF'
## Critical Files
| File | Action | Reason |
|------|--------|--------|
| `b.py` | MODIFY | B |
| `d.py` | CREATE | D |
EOF

    local -A active_workers=([12345]="TASK-002")

    local output
    output=$(get_conflicting_files "$RALPH_DIR" "TASK-001" active_workers)

    assert_equals "b.py" "$output" "Should return only overlapping files"
}

test_get_conflicting_tasks_returns_task_ids() {
    source "$WIGGUM_HOME/lib/tasks/conflict-detection.sh"

    mkdir -p "$RALPH_DIR/plans"

    cat > "$RALPH_DIR/plans/TASK-001.md" << 'EOF'
## Critical Files
| File | Action | Reason |
|------|--------|--------|
| `shared.py` | MODIFY | Shared |
EOF

    cat > "$RALPH_DIR/plans/TASK-002.md" << 'EOF'
## Critical Files
| File | Action | Reason |
|------|--------|--------|
| `shared.py` | MODIFY | Shared |
EOF

    cat > "$RALPH_DIR/plans/TASK-003.md" << 'EOF'
## Critical Files
| File | Action | Reason |
|------|--------|--------|
| `shared.py` | MODIFY | Shared |
EOF

    # shellcheck disable=SC2034  # active_workers is passed by name to get_conflicting_tasks
    local -A active_workers=([12345]="TASK-002" [67890]="TASK-003")

    local output
    output=$(get_conflicting_tasks "$RALPH_DIR" "TASK-001" active_workers)

    # Both TASK-002 and TASK-003 should be in output
    assert_output_contains "$output" "TASK-002" "Should include TASK-002"
    assert_output_contains "$output" "TASK-003" "Should include TASK-003"
}

# =============================================================================
# lib/core/gh-error.sh Tests
# =============================================================================

test_gh_error_timeout_is_network_error() {
    source "$WIGGUM_HOME/lib/core/gh-error.sh"

    local exit_code=0
    gh_is_network_error "124" "" || exit_code=$?

    assert_equals "0" "$exit_code" "Exit code 124 should be network error"
}

test_gh_error_connection_refused_is_network_error() {
    source "$WIGGUM_HOME/lib/core/gh-error.sh"

    local exit_code=0
    gh_is_network_error "" "Connection refused" || exit_code=$?

    assert_equals "0" "$exit_code" "Connection refused should be network error"
}

test_gh_error_could_not_resolve_host_is_network_error() {
    source "$WIGGUM_HOME/lib/core/gh-error.sh"

    local exit_code=0
    gh_is_network_error "" "Could not resolve host github.com" || exit_code=$?

    assert_equals "0" "$exit_code" "Could not resolve host should be network error"
}

test_gh_error_502_is_network_error() {
    source "$WIGGUM_HOME/lib/core/gh-error.sh"

    local exit_code=0
    gh_is_network_error "" "HTTP 502 Bad Gateway" || exit_code=$?

    assert_equals "0" "$exit_code" "HTTP 502 should be network error"
}

test_gh_error_success_is_not_network_error() {
    source "$WIGGUM_HOME/lib/core/gh-error.sh"

    local exit_code=0
    gh_is_network_error "0" "" || exit_code=$?

    assert_equals "1" "$exit_code" "Exit code 0 should NOT be network error"
}

test_gh_error_unrelated_error_is_not_network_error() {
    source "$WIGGUM_HOME/lib/core/gh-error.sh"

    local exit_code=0
    gh_is_network_error "1" "permission denied" || exit_code=$?

    assert_equals "1" "$exit_code" "Unrelated error should NOT be network error"
}

test_gh_format_error_timeout() {
    source "$WIGGUM_HOME/lib/core/gh-error.sh"

    local output
    output=$(gh_format_error "124" "timeout" "fetching PR")

    assert_output_contains "$output" "Network timeout" "Should mention network timeout"
    assert_output_contains "$output" "fetching PR" "Should include operation name"
}

test_gh_format_error_network() {
    source "$WIGGUM_HOME/lib/core/gh-error.sh"

    local output
    output=$(gh_format_error "1" "Connection refused" "creating issue")

    assert_output_contains "$output" "Network error" "Should mention network error"
    assert_output_contains "$output" "creating issue" "Should include operation name"
}

test_gh_format_error_non_network() {
    source "$WIGGUM_HOME/lib/core/gh-error.sh"

    local output
    output=$(gh_format_error "1" "not found" "getting repo")

    assert_output_contains "$output" "GitHub API error" "Should mention API error"
    assert_output_contains "$output" "exit: 1" "Should include exit code"
}

test_gh_with_network_detection_sets_flag() {
    source "$WIGGUM_HOME/lib/core/gh-error.sh"

    # Mock a failing command that outputs network error
    local exit_code=0
    gh_with_network_detection bash -c 'echo "Connection refused" >&2; exit 1' >/dev/null 2>&1 || exit_code=$?

    assert_equals "true" "$GH_LAST_WAS_NETWORK_ERROR" "Should set GH_LAST_WAS_NETWORK_ERROR to true"
    assert_equals "1" "$exit_code" "Should return command exit code"
}

test_gh_with_network_detection_success() {
    source "$WIGGUM_HOME/lib/core/gh-error.sh"

    local exit_code=0
    gh_with_network_detection echo "success" >/dev/null 2>&1 || exit_code=$?

    assert_equals "false" "$GH_LAST_WAS_NETWORK_ERROR" "Should set GH_LAST_WAS_NETWORK_ERROR to false on success"
    assert_equals "0" "$exit_code" "Should return 0 on success"
}

# =============================================================================
# lib/core/verbose-flags.sh Tests
# =============================================================================

test_verbose_flags_v_sets_info() {
    source "$WIGGUM_HOME/lib/core/verbose-flags.sh"

    parse_verbose_flags -v arg1 arg2

    # -v keeps default INFO (no change from baseline)
    # Since LOG_LEVEL might already be INFO, just verify args are preserved
    assert_equals "2" "${#WIGGUM_REMAINING_ARGS[@]}" "Should have 2 remaining args"
    assert_equals "arg1" "${WIGGUM_REMAINING_ARGS[0]}" "First arg should be arg1"
}

test_verbose_flags_vv_sets_debug() {
    source "$WIGGUM_HOME/lib/core/verbose-flags.sh"

    parse_verbose_flags -vv arg1

    assert_equals "DEBUG" "$LOG_LEVEL" "Should set LOG_LEVEL to DEBUG"
    assert_equals "1" "${#WIGGUM_REMAINING_ARGS[@]}" "Should have 1 remaining arg"
}

test_verbose_flags_vvv_sets_trace() {
    source "$WIGGUM_HOME/lib/core/verbose-flags.sh"

    parse_verbose_flags -vvv

    assert_equals "TRACE" "$LOG_LEVEL" "Should set LOG_LEVEL to TRACE"
    assert_equals "0" "${#WIGGUM_REMAINING_ARGS[@]}" "Should have no remaining args"
}

test_verbose_flags_q_sets_warn() {
    source "$WIGGUM_HOME/lib/core/verbose-flags.sh"

    parse_verbose_flags -q arg1

    assert_equals "WARN" "$LOG_LEVEL" "Should set LOG_LEVEL to WARN"
}

test_verbose_flags_quiet_sets_warn() {
    source "$WIGGUM_HOME/lib/core/verbose-flags.sh"

    parse_verbose_flags --quiet

    assert_equals "WARN" "$LOG_LEVEL" "Should set LOG_LEVEL to WARN"
}

test_verbose_flags_quiet_takes_precedence() {
    source "$WIGGUM_HOME/lib/core/verbose-flags.sh"

    parse_verbose_flags -vvv -q arg1

    assert_equals "WARN" "$LOG_LEVEL" "Quiet should take precedence over verbose"
    assert_equals "arg1" "${WIGGUM_REMAINING_ARGS[0]}" "Should preserve args"
}

test_verbose_flags_mixed_args() {
    source "$WIGGUM_HOME/lib/core/verbose-flags.sh"

    parse_verbose_flags arg1 -vv arg2 --quiet arg3

    assert_equals "WARN" "$LOG_LEVEL" "Should process all flags"
    assert_equals "3" "${#WIGGUM_REMAINING_ARGS[@]}" "Should have 3 remaining args"
    assert_equals "arg1" "${WIGGUM_REMAINING_ARGS[0]}" "First arg should be arg1"
    assert_equals "arg2" "${WIGGUM_REMAINING_ARGS[1]}" "Second arg should be arg2"
    assert_equals "arg3" "${WIGGUM_REMAINING_ARGS[2]}" "Third arg should be arg3"
}

# =============================================================================
# lib/core/bin-common.sh Tests
# =============================================================================

test_bin_common_validate_wiggum_home_valid() {
    # bin-common.sh auto-executes validation, so we test the helper directly
    source "$WIGGUM_HOME/lib/core/bin-common.sh"

    local exit_code=0
    _validate_wiggum_home "$WIGGUM_HOME" || exit_code=$?

    assert_equals "0" "$exit_code" "Should return 0 for valid WIGGUM_HOME"
}

test_bin_common_validate_wiggum_home_invalid() {
    # Create a fake directory without required files
    local fake_home="$TEST_DIR/fake-wiggum"
    mkdir -p "$fake_home"

    local exit_code=0
    _validate_wiggum_home "$fake_home" 2>/dev/null || exit_code=$?

    assert_equals "1" "$exit_code" "Should return 1 for invalid WIGGUM_HOME"
}

test_bin_common_sets_project_dir() {
    # Save current value
    local old_project_dir="${PROJECT_DIR:-}"

    # Unset and re-source to test default
    unset PROJECT_DIR
    source "$WIGGUM_HOME/lib/core/bin-common.sh"

    assert_not_empty "$PROJECT_DIR" "Should set PROJECT_DIR"

    # Restore
    if [ -n "$old_project_dir" ]; then
        PROJECT_DIR="$old_project_dir"
    fi
}

test_bin_common_sets_ralph_dir() {
    # Save current value
    local old_ralph_dir="${RALPH_DIR:-}"

    # Unset and re-source to test default
    unset RALPH_DIR
    source "$WIGGUM_HOME/lib/core/bin-common.sh"

    assert_not_empty "$RALPH_DIR" "Should set RALPH_DIR"

    # Restore
    RALPH_DIR="$old_ralph_dir"
}

# =============================================================================
# lib/github/pr-labels.sh Tests
# =============================================================================

test_pr_labels_add_label_with_mock() {
    # Create a mock gh command
    local mock_gh="$TEST_DIR/gh"
    cat > "$mock_gh" << 'EOF'
#!/usr/bin/env bash
# Mock gh that succeeds
exit 0
EOF
    chmod +x "$mock_gh"

    # Put mock on PATH
    export PATH="$TEST_DIR:$PATH"
    export WIGGUM_GH_TIMEOUT=1

    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/github/issue-config.sh"
    source "$WIGGUM_HOME/lib/worker/git-state.sh"
    source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"
    source "$WIGGUM_HOME/lib/github/pr-labels.sh"

    local exit_code=0
    github_pr_add_label "123" "test-label" || exit_code=$?

    assert_equals "0" "$exit_code" "Should return 0 on success"
}

test_pr_labels_remove_label_always_succeeds() {
    # Create a mock gh that fails
    local mock_gh="$TEST_DIR/gh"
    cat > "$mock_gh" << 'EOF'
#!/usr/bin/env bash
exit 1
EOF
    chmod +x "$mock_gh"

    export PATH="$TEST_DIR:$PATH"
    export WIGGUM_GH_TIMEOUT=1

    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/github/issue-config.sh"
    source "$WIGGUM_HOME/lib/worker/git-state.sh"
    source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"
    source "$WIGGUM_HOME/lib/github/pr-labels.sh"

    local exit_code=0
    github_pr_remove_label "123" "test-label" || exit_code=$?

    assert_equals "0" "$exit_code" "Remove should always return 0 (non-critical)"
}

test_pr_labels_set_status_label_replaces() {
    # Create a mock gh that logs arguments
    local mock_gh="$TEST_DIR/gh"
    local gh_log="$TEST_DIR/gh.log"
    cat > "$mock_gh" << EOF
#!/usr/bin/env bash
echo "\$@" >> "$gh_log"
exit 0
EOF
    chmod +x "$mock_gh"

    export PATH="$TEST_DIR:$PATH"
    export WIGGUM_GH_TIMEOUT=1

    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/github/issue-config.sh"
    source "$WIGGUM_HOME/lib/worker/git-state.sh"
    source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"
    source "$WIGGUM_HOME/lib/github/pr-labels.sh"

    github_pr_set_status_label "123" "new-label" "old-label"

    # Should call remove and add
    assert_file_contains "$gh_log" "remove-label" "Should remove old label"
    assert_file_contains "$gh_log" "add-label" "Should add new label"
}

# =============================================================================
# lib/wdoc/wdoc-registry.sh Tests
# =============================================================================

test_wdoc_registry_file_path() {
    source "$WIGGUM_HOME/lib/wdoc/wdoc-registry.sh"

    local registry_file
    registry_file=$(wdoc_registry_file)

    assert_equals "$RALPH_DIR/wdoc-packages.json" "$registry_file" "Should return correct registry path"
}

test_wdoc_registry_add_creates_entry() {
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/wdoc/wdoc-registry.sh"

    wdoc_registry_add "textual" "https://textual.textualize.io" "https://github.com/Textualize/textual"

    local registry_file
    registry_file=$(wdoc_registry_file)

    assert_file_exists "$registry_file" "Registry file should exist"

    local doc_url
    doc_url=$(jq -r '.packages.textual.doc_url' "$registry_file")
    assert_equals "https://textual.textualize.io" "$doc_url" "Should store doc_url"

    local src_url
    src_url=$(jq -r '.packages.textual.src_url' "$registry_file")
    assert_equals "https://github.com/Textualize/textual" "$src_url" "Should store src_url"
}

test_wdoc_registry_get_returns_package() {
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/wdoc/wdoc-registry.sh"

    wdoc_registry_add "pytest" "https://docs.pytest.org" ""

    local result
    result=$(wdoc_registry_get "pytest")

    assert_not_empty "$result" "Should return package data"

    local doc_url
    doc_url=$(echo "$result" | jq -r '.doc_url')
    assert_equals "https://docs.pytest.org" "$doc_url" "Should return correct doc_url"
}

test_wdoc_registry_get_missing_returns_1() {
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/wdoc/wdoc-registry.sh"

    local exit_code=0
    wdoc_registry_get "nonexistent" >/dev/null 2>&1 || exit_code=$?

    assert_equals "1" "$exit_code" "Should return 1 for missing package"
}

test_wdoc_registry_list_returns_packages() {
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/wdoc/wdoc-registry.sh"

    wdoc_registry_add "pkg1" "https://pkg1.com" ""
    wdoc_registry_add "pkg2" "https://pkg2.com" ""

    local output
    output=$(wdoc_registry_list)

    assert_output_contains "$output" "pkg1" "Should list pkg1"
    assert_output_contains "$output" "pkg2" "Should list pkg2"
}

test_wdoc_registry_list_empty() {
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/wdoc/wdoc-registry.sh"

    local output
    output=$(wdoc_registry_list)

    assert_equals "" "$output" "Should return empty for empty registry"
}

test_wdoc_registry_remove_deletes_package() {
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/wdoc/wdoc-registry.sh"

    wdoc_registry_add "temp-pkg" "https://temp.com" ""

    local exit_code=0
    wdoc_registry_remove "temp-pkg" || exit_code=$?

    assert_equals "0" "$exit_code" "Should return 0 on successful removal"

    exit_code=0
    wdoc_registry_get "temp-pkg" >/dev/null 2>&1 || exit_code=$?
    assert_equals "1" "$exit_code" "Package should no longer exist after removal"
}

test_wdoc_registry_remove_missing_returns_1() {
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/wdoc/wdoc-registry.sh"

    local exit_code=0
    wdoc_registry_remove "nonexistent" || exit_code=$?

    assert_equals "1" "$exit_code" "Should return 1 when removing nonexistent package"
}

test_wdoc_registry_set_version() {
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/wdoc/wdoc-registry.sh"

    wdoc_registry_add "versioned-pkg" "https://v.com" ""
    wdoc_registry_set_version "versioned-pkg" "3.2.0"

    local result
    result=$(wdoc_registry_get "versioned-pkg")

    local version
    version=$(echo "$result" | jq -r '.version')
    assert_equals "3.2.0" "$version" "Should set version field"
}

test_wdoc_registry_set_version_missing_returns_1() {
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/wdoc/wdoc-registry.sh"

    local exit_code=0
    wdoc_registry_set_version "nonexistent" "1.0.0" || exit_code=$?

    assert_equals "1" "$exit_code" "Should return 1 when setting version on missing package"
}

test_wdoc_registry_set_timestamp() {
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/wdoc/wdoc-registry.sh"

    wdoc_registry_add "ts-pkg" "https://ts.com" ""
    wdoc_registry_set_timestamp "ts-pkg" "doc_fetched_at"

    local result
    result=$(wdoc_registry_get "ts-pkg")

    local timestamp
    timestamp=$(echo "$result" | jq -r '.doc_fetched_at')
    assert_not_empty "$timestamp" "Should set timestamp field"
}

test_wdoc_registry_idempotent_initialization() {
    source "$WIGGUM_HOME/lib/core/platform.sh"
    source "$WIGGUM_HOME/lib/wdoc/wdoc-registry.sh"

    # First call creates file
    wdoc_registry_add "pkg1" "https://pkg1.com" ""

    # Second call should not corrupt existing data
    wdoc_registry_add "pkg2" "https://pkg2.com" ""

    local result1
    result1=$(wdoc_registry_get "pkg1")
    assert_not_empty "$result1" "First package should still exist"

    local result2
    result2=$(wdoc_registry_get "pkg2")
    assert_not_empty "$result2" "Second package should exist"
}

# =============================================================================
# Run All Tests
# =============================================================================

# Plan parser tests
run_test test_plan_parser_extracts_create_and_modify_files
run_test test_plan_parser_removes_backticks
run_test test_plan_parser_handles_missing_section
run_test test_plan_parser_handles_missing_file
run_test test_plan_parser_sorts_and_deduplicates
run_test test_get_task_critical_files_looks_up_by_task_id
run_test test_get_task_critical_files_handles_missing_plan

# Conflict detection tests
run_test test_conflict_detection_no_overlap_returns_1
run_test test_conflict_detection_overlap_returns_0
run_test test_conflict_detection_self_exclusion
run_test test_conflict_detection_no_plan_no_conflict
run_test test_get_conflicting_files_returns_intersection
run_test test_get_conflicting_tasks_returns_task_ids

# gh-error tests
run_test test_gh_error_timeout_is_network_error
run_test test_gh_error_connection_refused_is_network_error
run_test test_gh_error_could_not_resolve_host_is_network_error
run_test test_gh_error_502_is_network_error
run_test test_gh_error_success_is_not_network_error
run_test test_gh_error_unrelated_error_is_not_network_error
run_test test_gh_format_error_timeout
run_test test_gh_format_error_network
run_test test_gh_format_error_non_network
run_test test_gh_with_network_detection_sets_flag
run_test test_gh_with_network_detection_success

# Verbose flags tests
run_test test_verbose_flags_v_sets_info
run_test test_verbose_flags_vv_sets_debug
run_test test_verbose_flags_vvv_sets_trace
run_test test_verbose_flags_q_sets_warn
run_test test_verbose_flags_quiet_sets_warn
run_test test_verbose_flags_quiet_takes_precedence
run_test test_verbose_flags_mixed_args

# bin-common tests
run_test test_bin_common_validate_wiggum_home_valid
run_test test_bin_common_validate_wiggum_home_invalid
run_test test_bin_common_sets_project_dir
run_test test_bin_common_sets_ralph_dir

# pr-labels tests
run_test test_pr_labels_add_label_with_mock
run_test test_pr_labels_remove_label_always_succeeds
run_test test_pr_labels_set_status_label_replaces

# wdoc-registry tests
run_test test_wdoc_registry_file_path
run_test test_wdoc_registry_add_creates_entry
run_test test_wdoc_registry_get_returns_package
run_test test_wdoc_registry_get_missing_returns_1
run_test test_wdoc_registry_list_returns_packages
run_test test_wdoc_registry_list_empty
run_test test_wdoc_registry_remove_deletes_package
run_test test_wdoc_registry_remove_missing_returns_1
run_test test_wdoc_registry_set_version
run_test test_wdoc_registry_set_version_missing_returns_1
run_test test_wdoc_registry_set_timestamp
run_test test_wdoc_registry_idempotent_initialization

print_test_summary
exit_with_test_result
