#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/scheduler/pr-merge-optimizer.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/scheduler/pr-merge-optimizer.sh"

# Create temp dir for test isolation
TEST_DIR=""
RALPH_DIR=""
PROJECT_DIR=""

setup() {
    TEST_DIR=$(mktemp -d)
    RALPH_DIR="$TEST_DIR/.ralph"
    PROJECT_DIR="$TEST_DIR/project"
    mkdir -p "$RALPH_DIR/workers"
    mkdir -p "$PROJECT_DIR"

    # Create a minimal kanban.md
    cat > "$RALPH_DIR/kanban.md" << 'EOF'
# Kanban

## In Progress

## Pending Approval

- [P] **[TASK-001]** First task
  - Description: Test task 1
  - Priority: HIGH
  - Dependencies: none

- [P] **[TASK-002]** Second task
  - Description: Test task 2
  - Priority: MEDIUM
  - Dependencies: none

- [P] **[TASK-003]** Third task
  - Description: Test task 3
  - Priority: LOW
  - Dependencies: none

## Complete
EOF
}

teardown() {
    rm -rf "$TEST_DIR"
}

# Helper to create a mock worker with git workspace
_create_mock_worker() {
    local task_id="$1"
    local pr_number="$2"
    local files_modified="$3"  # comma-separated list

    local worker_dir="$RALPH_DIR/workers/worker-${task_id}-1234567890"
    mkdir -p "$worker_dir/workspace/.git"
    mkdir -p "$worker_dir/reports"

    # Create git-state.json
    cat > "$worker_dir/git-state.json" << EOF
{
  "current_state": "none",
  "pr_number": $pr_number,
  "merge_attempts": 0,
  "last_error": null,
  "transitions": []
}
EOF

    # Create pr_url.txt
    echo "https://github.com/test/repo/pull/$pr_number" > "$worker_dir/pr_url.txt"

    # Create mock pr-reviews.json (copilot reviewed)
    cat > "$worker_dir/pr-reviews.json" << 'EOF'
[{"user": {"login": "copilot"}, "state": "APPROVED"}]
EOF

    echo "$worker_dir"
}

# =============================================================================
# pr_merge_init() Tests
# =============================================================================

test_pr_merge_init_creates_file() {
    pr_merge_init "$RALPH_DIR"

    assert_file_exists "$RALPH_DIR/pr-merge-state.json" "State file should exist"
}

test_pr_merge_init_creates_valid_json() {
    pr_merge_init "$RALPH_DIR"

    local state_file="$RALPH_DIR/pr-merge-state.json"

    local prs conflict_graph merge_order
    prs=$(jq '.prs' "$state_file")
    conflict_graph=$(jq '.conflict_graph' "$state_file")
    merge_order=$(jq '.merge_order' "$state_file")

    assert_equals "{}" "$prs" "Should have empty prs"
    assert_equals "{}" "$conflict_graph" "Should have empty conflict_graph"
    assert_equals "[]" "$merge_order" "Should have empty merge_order"
}

# =============================================================================
# _check_file_overlap() Tests
# =============================================================================

test_check_file_overlap_no_overlap() {
    local files_a='["src/api.ts", "src/utils.ts"]'
    local files_b='["src/models.ts", "src/types.ts"]'

    local result
    result=$(_check_file_overlap "$files_a" "$files_b")
    local exit_code=$?

    assert_equals "1" "$exit_code" "Should return 1 for no overlap"
    assert_equals "[]" "$result" "Should return empty array"
}

test_check_file_overlap_with_overlap() {
    local files_a='["src/api.ts", "src/utils.ts"]'
    local files_b='["src/api.ts", "src/models.ts"]'

    local result
    if result=$(_check_file_overlap "$files_a" "$files_b"); then
        local count
        count=$(echo "$result" | jq 'length')
        assert_equals "1" "$count" "Should have 1 overlapping file"
        assert_output_contains "$result" "src/api.ts" "Should contain overlapping file"
    else
        assert_failure "Should return 0 for overlap" false
    fi
}

test_check_file_overlap_multiple_overlaps() {
    local files_a='["src/api.ts", "src/utils.ts", "src/config.ts"]'
    local files_b='["src/api.ts", "src/utils.ts", "src/models.ts"]'

    local result
    if result=$(_check_file_overlap "$files_a" "$files_b"); then
        local count
        count=$(echo "$result" | jq 'length')
        assert_equals "2" "$count" "Should have 2 overlapping files"
    else
        assert_failure "Should return 0 for overlap" false
    fi
}

# =============================================================================
# pr_merge_build_conflict_graph() Tests
# =============================================================================

test_build_conflict_graph_no_conflicts() {
    pr_merge_init "$RALPH_DIR"

    # Add PRs with no overlapping files
    local state_file="$RALPH_DIR/pr-merge-state.json"
    jq '.prs = {
        "TASK-001": {"files_modified": ["src/api.ts"]},
        "TASK-002": {"files_modified": ["src/utils.ts"]}
    }' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    pr_merge_build_conflict_graph "$RALPH_DIR" 2>/dev/null

    local graph
    graph=$(jq '.conflict_graph' "$state_file")
    assert_equals "{}" "$graph" "Graph should be empty for no conflicts"
}

test_build_conflict_graph_with_conflicts() {
    pr_merge_init "$RALPH_DIR"

    # Add PRs with overlapping files
    local state_file="$RALPH_DIR/pr-merge-state.json"
    jq '.prs = {
        "TASK-001": {"files_modified": ["src/api.ts", "src/utils.ts"]},
        "TASK-002": {"files_modified": ["src/api.ts", "src/models.ts"]}
    }' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    pr_merge_build_conflict_graph "$RALPH_DIR" 2>/dev/null

    local task1_conflicts
    task1_conflicts=$(jq -r '.conflict_graph["TASK-001"]' "$state_file")
    assert_output_contains "$task1_conflicts" "TASK-002" "TASK-001 should conflict with TASK-002"

    local task2_conflicts
    task2_conflicts=$(jq -r '.conflict_graph["TASK-002"]' "$state_file")
    assert_output_contains "$task2_conflicts" "TASK-001" "TASK-002 should conflict with TASK-001"
}

test_build_conflict_graph_three_way() {
    pr_merge_init "$RALPH_DIR"

    # Add 3 PRs with various overlaps
    local state_file="$RALPH_DIR/pr-merge-state.json"
    jq '.prs = {
        "TASK-001": {"files_modified": ["src/api.ts"]},
        "TASK-002": {"files_modified": ["src/api.ts", "src/utils.ts"]},
        "TASK-003": {"files_modified": ["src/utils.ts"]}
    }' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    pr_merge_build_conflict_graph "$RALPH_DIR" 2>/dev/null

    # TASK-001 conflicts with TASK-002 (api.ts)
    local task1_conflicts
    task1_conflicts=$(jq '.conflict_graph["TASK-001"] | length' "$state_file")
    assert_equals "1" "$task1_conflicts" "TASK-001 should have 1 conflict"

    # TASK-002 conflicts with both (api.ts with 1, utils.ts with 3)
    local task2_conflicts
    task2_conflicts=$(jq '.conflict_graph["TASK-002"] | length' "$state_file")
    assert_equals "2" "$task2_conflicts" "TASK-002 should have 2 conflicts"

    # TASK-003 conflicts with TASK-002 (utils.ts)
    local task3_conflicts
    task3_conflicts=$(jq '.conflict_graph["TASK-003"] | length' "$state_file")
    assert_equals "1" "$task3_conflicts" "TASK-003 should have 1 conflict"
}

# =============================================================================
# _calculate_merge_priority() Tests (tiebreaker within MIS)
# =============================================================================

test_calculate_merge_priority_base_score() {
    pr_merge_init "$RALPH_DIR"

    local state_file="$RALPH_DIR/pr-merge-state.json"
    jq '.prs = {
        "TASK-001": {
            "files_modified": [],
            "mergeable_to_main": false
        }
    } | .conflict_graph = {}' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    local priority
    priority=$(_calculate_merge_priority "$RALPH_DIR" "TASK-001")

    # Base score is 1000, no conflicts, no files
    assert_equals "1000" "$priority" "Base priority should be 1000"
}

test_calculate_merge_priority_conflict_penalty() {
    pr_merge_init "$RALPH_DIR"

    local state_file="$RALPH_DIR/pr-merge-state.json"
    jq '.prs = {
        "TASK-001": {
            "files_modified": [],
            "mergeable_to_main": false
        }
    } | .conflict_graph = {"TASK-001": ["TASK-002", "TASK-003"]}' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    local priority
    priority=$(_calculate_merge_priority "$RALPH_DIR" "TASK-001")

    # Base 1000 - 100 (2 conflicts * 50) = 900
    assert_equals "900" "$priority" "PR with 2 conflicts should have -100 penalty"
}

test_calculate_merge_priority_file_penalty() {
    pr_merge_init "$RALPH_DIR"

    local state_file="$RALPH_DIR/pr-merge-state.json"
    jq '.prs = {
        "TASK-001": {
            "files_modified": ["a.ts", "b.ts", "c.ts", "d.ts", "e.ts"],
            "mergeable_to_main": false
        }
    } | .conflict_graph = {}' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    local priority
    priority=$(_calculate_merge_priority "$RALPH_DIR" "TASK-001")

    # Base 1000 - 50 (5 files * 10) = 950
    assert_equals "950" "$priority" "PR with 5 files should have -50 penalty"
}

# =============================================================================
# Maximum Independent Set Tests
# =============================================================================

test_mis_no_conflicts() {
    pr_merge_init "$RALPH_DIR"

    # All PRs independent - MIS should include all
    local state_file="$RALPH_DIR/pr-merge-state.json"
    jq '.prs = {
        "TASK-001": {"files_modified": ["a.ts"], "mergeable_to_main": true},
        "TASK-002": {"files_modified": ["b.ts"], "mergeable_to_main": true},
        "TASK-003": {"files_modified": ["c.ts"], "mergeable_to_main": true}
    } | .conflict_graph = {}' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    pr_merge_find_optimal_order "$RALPH_DIR" 2>/dev/null

    local mis_size
    mis_size=$(jq '.optimal_batch | length' "$state_file")
    assert_equals "3" "$mis_size" "MIS should include all 3 PRs when no conflicts"
}

test_mis_pairwise_conflict() {
    pr_merge_init "$RALPH_DIR"

    # Two PRs conflict - MIS should be size 1
    local state_file="$RALPH_DIR/pr-merge-state.json"
    jq '.prs = {
        "TASK-001": {"files_modified": ["a.ts"], "mergeable_to_main": true},
        "TASK-002": {"files_modified": ["a.ts"], "mergeable_to_main": true}
    } | .conflict_graph = {"TASK-001": ["TASK-002"], "TASK-002": ["TASK-001"]}' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    pr_merge_find_optimal_order "$RALPH_DIR" 2>/dev/null

    local mis_size
    mis_size=$(jq '.optimal_batch | length' "$state_file")
    assert_equals "1" "$mis_size" "MIS should be size 1 when two PRs conflict"
}

test_mis_chain_conflict() {
    pr_merge_init "$RALPH_DIR"

    # Chain: A-B-C (A conflicts with B, B conflicts with C)
    # MIS should be {A, C} (size 2)
    local state_file="$RALPH_DIR/pr-merge-state.json"
    jq '.prs = {
        "TASK-001": {"files_modified": ["a.ts"], "mergeable_to_main": true},
        "TASK-002": {"files_modified": ["a.ts", "b.ts"], "mergeable_to_main": true},
        "TASK-003": {"files_modified": ["b.ts"], "mergeable_to_main": true}
    } | .conflict_graph = {
        "TASK-001": ["TASK-002"],
        "TASK-002": ["TASK-001", "TASK-003"],
        "TASK-003": ["TASK-002"]
    }' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    pr_merge_find_optimal_order "$RALPH_DIR" 2>/dev/null

    local mis_size
    mis_size=$(jq '.optimal_batch | length' "$state_file")
    assert_equals "2" "$mis_size" "MIS for chain A-B-C should be size 2 (A and C)"

    # Verify A and C are in MIS, not B
    local has_task1 has_task2 has_task3
    has_task1=$(jq '.optimal_batch | index("TASK-001") != null' "$state_file")
    has_task2=$(jq '.optimal_batch | index("TASK-002") != null' "$state_file")
    has_task3=$(jq '.optimal_batch | index("TASK-003") != null' "$state_file")

    assert_equals "true" "$has_task1" "TASK-001 should be in MIS"
    assert_equals "false" "$has_task2" "TASK-002 should NOT be in MIS"
    assert_equals "true" "$has_task3" "TASK-003 should be in MIS"
}

test_mis_prefers_mergeable() {
    pr_merge_init "$RALPH_DIR"

    # Two conflicting PRs: one mergeable, one not
    # MIS should prefer the mergeable one
    local state_file="$RALPH_DIR/pr-merge-state.json"
    jq '.prs = {
        "TASK-001": {"files_modified": ["a.ts"], "mergeable_to_main": true},
        "TASK-002": {"files_modified": ["a.ts"], "mergeable_to_main": false}
    } | .conflict_graph = {"TASK-001": ["TASK-002"], "TASK-002": ["TASK-001"]}' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    pr_merge_find_optimal_order "$RALPH_DIR" 2>/dev/null

    local mis_task
    mis_task=$(jq -r '.optimal_batch[0]' "$state_file")
    assert_equals "TASK-001" "$mis_task" "MIS should prefer mergeable PR"
}

# =============================================================================
# pr_merge_find_optimal_order() Tests
# =============================================================================

test_find_optimal_order_includes_all_prs() {
    pr_merge_init "$RALPH_DIR"

    local state_file="$RALPH_DIR/pr-merge-state.json"
    jq '.prs = {
        "TASK-001": {"files_modified": [], "mergeable_to_main": false},
        "TASK-002": {"files_modified": [], "mergeable_to_main": false},
        "TASK-003": {"files_modified": [], "mergeable_to_main": false}
    } | .conflict_graph = {}' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    pr_merge_find_optimal_order "$RALPH_DIR" 2>/dev/null

    local count
    count=$(jq '.merge_order | length' "$state_file")
    assert_equals "3" "$count" "All PRs should be in merge order"
}

test_find_optimal_order_mis_first() {
    pr_merge_init "$RALPH_DIR"

    # PRs: A conflicts with B, C is independent
    # MIS = {A or B, C} - C should definitely be in first batch
    local state_file="$RALPH_DIR/pr-merge-state.json"
    jq '.prs = {
        "TASK-001": {"files_modified": ["a.ts"], "mergeable_to_main": true},
        "TASK-002": {"files_modified": ["a.ts"], "mergeable_to_main": true},
        "TASK-003": {"files_modified": ["c.ts"], "mergeable_to_main": true}
    } | .conflict_graph = {"TASK-001": ["TASK-002"], "TASK-002": ["TASK-001"]}' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    pr_merge_find_optimal_order "$RALPH_DIR" 2>/dev/null

    # TASK-003 should be in optimal batch (it's independent)
    local has_task3
    has_task3=$(jq '.optimal_batch | index("TASK-003") != null' "$state_file")
    assert_equals "true" "$has_task3" "Independent PR should be in optimal batch"

    local mis_size
    mis_size=$(jq '.optimal_batch | length' "$state_file")
    assert_equals "2" "$mis_size" "MIS should have 2 PRs (one of A/B + C)"
}

# =============================================================================
# pr_merge_stats() Tests
# =============================================================================

test_pr_merge_stats_empty() {
    pr_merge_init "$RALPH_DIR"

    local stats
    stats=$(pr_merge_stats "$RALPH_DIR")

    local total
    total=$(echo "$stats" | jq '.total_prs')
    assert_equals "0" "$total" "Should have 0 PRs"
}

test_pr_merge_stats_with_data() {
    pr_merge_init "$RALPH_DIR"

    local state_file="$RALPH_DIR/pr-merge-state.json"
    jq '.prs = {
        "TASK-001": {"mergeable_to_main": true, "has_new_comments": false},
        "TASK-002": {"mergeable_to_main": false, "has_new_comments": true},
        "TASK-003": {"mergeable_to_main": false, "has_new_comments": false}
    } | .merged_this_cycle = ["TASK-001"]' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    local stats
    stats=$(pr_merge_stats "$RALPH_DIR")

    local total merged mergeable with_comments
    total=$(echo "$stats" | jq '.total_prs')
    merged=$(echo "$stats" | jq '.merged')
    mergeable=$(echo "$stats" | jq '.mergeable')
    with_comments=$(echo "$stats" | jq '.with_comments')

    assert_equals "3" "$total" "Should have 3 total PRs"
    assert_equals "1" "$merged" "Should have 1 merged"
    assert_equals "1" "$mergeable" "Should have 1 mergeable"
    assert_equals "1" "$with_comments" "Should have 1 with comments"
}

# =============================================================================
# Integration Tests
# =============================================================================

test_integration_conflict_detection_and_categorization() {
    pr_merge_init "$RALPH_DIR"

    # Set up state with mixed PRs
    local state_file="$RALPH_DIR/pr-merge-state.json"
    jq '.prs = {
        "TASK-001": {
            "pr_number": 1,
            "worker_dir": "/tmp/w1",
            "files_modified": ["src/api.ts"],
            "has_new_comments": false,
            "copilot_reviewed": true,
            "mergeable_to_main": false,
            "conflict_files_with_main": ["src/api.ts"]
        },
        "TASK-002": {
            "pr_number": 2,
            "worker_dir": "/tmp/w2",
            "files_modified": ["src/api.ts"],
            "has_new_comments": false,
            "copilot_reviewed": true,
            "mergeable_to_main": false,
            "conflict_files_with_main": ["src/api.ts"]
        },
        "TASK-003": {
            "pr_number": 3,
            "worker_dir": "/tmp/w3",
            "files_modified": ["src/utils.ts"],
            "has_new_comments": false,
            "copilot_reviewed": true,
            "mergeable_to_main": false,
            "conflict_files_with_main": ["src/utils.ts"]
        }
    }' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    # Build conflict graph
    pr_merge_build_conflict_graph "$RALPH_DIR" 2>/dev/null

    # TASK-001 and TASK-002 should conflict (both modify api.ts)
    local task1_conflicts
    task1_conflicts=$(jq '.conflict_graph["TASK-001"]' "$state_file")
    assert_output_contains "$task1_conflicts" "TASK-002" "TASK-001 should conflict with TASK-002"

    # TASK-003 should not conflict with others (different file)
    local task3_conflicts
    task3_conflicts=$(jq '.conflict_graph["TASK-003"] // []' "$state_file")
    assert_equals "[]" "$task3_conflicts" "TASK-003 should have no conflicts"
}

test_integration_merge_order_respects_conflicts() {
    pr_merge_init "$RALPH_DIR"

    # PR1: mergeable, conflicts with PR2
    # PR2: not mergeable, conflicts with PR1
    # PR3: mergeable, no conflicts (should be first)
    local state_file="$RALPH_DIR/pr-merge-state.json"
    jq '.prs = {
        "TASK-001": {
            "files_modified": ["src/api.ts"],
            "mergeable_to_main": true
        },
        "TASK-002": {
            "files_modified": ["src/api.ts"],
            "mergeable_to_main": false
        },
        "TASK-003": {
            "files_modified": ["src/utils.ts"],
            "mergeable_to_main": true
        }
    }' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    pr_merge_build_conflict_graph "$RALPH_DIR" 2>/dev/null
    pr_merge_find_optimal_order "$RALPH_DIR" 2>/dev/null

    local first second
    first=$(jq -r '.merge_order[0]' "$state_file")
    second=$(jq -r '.merge_order[1]' "$state_file")

    # TASK-003 should be first (mergeable, no conflicts)
    # TASK-001 should be second (mergeable, but has conflict penalty)
    assert_equals "TASK-003" "$first" "PR with no conflicts should be first"
    assert_equals "TASK-001" "$second" "Mergeable PR with conflicts should be second"
}

# =============================================================================
# Run Tests
# =============================================================================

run_test test_pr_merge_init_creates_file
run_test test_pr_merge_init_creates_valid_json
run_test test_check_file_overlap_no_overlap
run_test test_check_file_overlap_with_overlap
run_test test_check_file_overlap_multiple_overlaps
run_test test_build_conflict_graph_no_conflicts
run_test test_build_conflict_graph_with_conflicts
run_test test_build_conflict_graph_three_way
run_test test_calculate_merge_priority_base_score
run_test test_calculate_merge_priority_conflict_penalty
run_test test_calculate_merge_priority_file_penalty
run_test test_mis_no_conflicts
run_test test_mis_pairwise_conflict
run_test test_mis_chain_conflict
run_test test_mis_prefers_mergeable
run_test test_find_optimal_order_includes_all_prs
run_test test_find_optimal_order_mis_first
run_test test_pr_merge_stats_empty
run_test test_pr_merge_stats_with_data
run_test test_integration_conflict_detection_and_categorization
run_test test_integration_merge_order_respects_conflicts

print_test_summary
exit_with_test_result
