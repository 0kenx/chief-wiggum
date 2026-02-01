#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/memory/memory.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
export LOG_FILE="/dev/null"
source "$WIGGUM_HOME/lib/core/logger.sh"

# Reset module guard so we can source it
unset _MEMORY_LOADED
source "$WIGGUM_HOME/lib/memory/memory.sh"

TEST_DIR=""
setup() {
    TEST_DIR=$(mktemp -d)
}
teardown() {
    rm -rf "$TEST_DIR"
}

# =============================================================================
# memory_init tests
# =============================================================================

test_memory_init_creates_directory_tree() {
    memory_init "$TEST_DIR"

    assert_dir_exists "$TEST_DIR/memory" "Memory root dir should exist"
    assert_dir_exists "$TEST_DIR/memory/patterns/errors" "patterns/errors should exist"
    assert_dir_exists "$TEST_DIR/memory/patterns/fixes" "patterns/fixes should exist"
    assert_dir_exists "$TEST_DIR/memory/patterns/tests" "patterns/tests should exist"
    assert_dir_exists "$TEST_DIR/memory/patterns/security" "patterns/security should exist"
    assert_dir_exists "$TEST_DIR/memory/patterns/environment" "patterns/environment should exist"
    assert_dir_exists "$TEST_DIR/memory/agents" "agents dir should exist"
    assert_dir_exists "$TEST_DIR/memory/tasks" "tasks dir should exist"
}

test_memory_init_creates_index_files() {
    memory_init "$TEST_DIR"

    assert_file_exists "$TEST_DIR/memory/INDEX.md" "Root INDEX.md should exist"
    assert_file_exists "$TEST_DIR/memory/ESCALATED.md" "ESCALATED.md should exist"
    assert_file_exists "$TEST_DIR/memory/stats.json" "Global stats.json should exist"
    assert_file_exists "$TEST_DIR/memory/pending.list" "pending.list should exist"
    assert_file_exists "$TEST_DIR/memory/patterns/INDEX.md" "patterns INDEX.md should exist"
    assert_file_exists "$TEST_DIR/memory/patterns/errors/INDEX.md" "errors INDEX.md should exist"
    assert_file_exists "$TEST_DIR/memory/patterns/fixes/INDEX.md" "fixes INDEX.md should exist"
    assert_file_exists "$TEST_DIR/memory/agents/INDEX.md" "agents INDEX.md should exist"
    assert_file_exists "$TEST_DIR/memory/tasks/INDEX.md" "tasks INDEX.md should exist"
}

test_memory_init_root_index_content() {
    memory_init "$TEST_DIR"

    assert_file_contains "$TEST_DIR/memory/INDEX.md" "# Project Memory" "Should have title"
    assert_file_contains "$TEST_DIR/memory/INDEX.md" "ESCALATED.md" "Should link to escalated"
    assert_file_contains "$TEST_DIR/memory/INDEX.md" "patterns/errors/INDEX.md" "Should link to error patterns"
    assert_file_contains "$TEST_DIR/memory/INDEX.md" "agents/INDEX.md" "Should link to agents"
    assert_file_contains "$TEST_DIR/memory/INDEX.md" "tasks/INDEX.md" "Should link to tasks"
}

test_memory_init_global_stats_json() {
    memory_init "$TEST_DIR"

    local version
    version=$(jq -r '.version' "$TEST_DIR/memory/stats.json")
    assert_equals "1.0" "$version" "Stats version should be 1.0"

    local tasks
    tasks=$(jq -r '.tasks_analyzed' "$TEST_DIR/memory/stats.json")
    assert_equals "0" "$tasks" "Initial tasks_analyzed should be 0"
}

test_memory_init_escalated_content() {
    memory_init "$TEST_DIR"

    assert_file_contains "$TEST_DIR/memory/ESCALATED.md" "# Escalated Issues" "Should have title"
    assert_file_contains "$TEST_DIR/memory/ESCALATED.md" "## OPEN" "Should have OPEN section"
    assert_file_contains "$TEST_DIR/memory/ESCALATED.md" "## RESOLVED" "Should have RESOLVED section"
}

test_memory_init_idempotent() {
    memory_init "$TEST_DIR"
    # Write custom content to INDEX.md
    echo "custom" >> "$TEST_DIR/memory/patterns/errors/INDEX.md"
    local before
    before=$(cat "$TEST_DIR/memory/patterns/errors/INDEX.md")

    # Second init should not overwrite existing INDEX.md
    memory_init "$TEST_DIR"
    local after
    after=$(cat "$TEST_DIR/memory/patterns/errors/INDEX.md")

    assert_equals "$before" "$after" "Init should not overwrite existing INDEX.md"
}

# =============================================================================
# memory_collect_stats tests
# =============================================================================

# Helper to create a mock worker with result files
_create_mock_worker() {
    local worker_dir="$1"
    local task_id="$2"
    local outcome="${3:-success}"

    mkdir -p "$worker_dir/results" "$worker_dir/workspace"

    # Create a mock result file
    local gate_result="PASS"
    local status="success"
    [ "$outcome" = "failure" ] && gate_result="FAIL" && status="failure"

    cat > "$worker_dir/results/1738000000-result.json" << EOF
{
  "agent_type": "engineering.software-engineer",
  "status": "$status",
  "exit_code": 0,
  "started_at": "2026-02-01T06:00:00+0000",
  "completed_at": "2026-02-01T06:20:00+0000",
  "duration_seconds": 1200,
  "task_id": "$task_id",
  "worker_id": "worker-${task_id}-1738000000",
  "iterations_completed": 3,
  "outputs": {"gate_result": "$gate_result"},
  "errors": [],
  "metadata": {}
}
EOF

    # Add a second agent result
    cat > "$worker_dir/results/1738001000-result.json" << EOF
{
  "agent_type": "engineering.validation-review",
  "status": "success",
  "exit_code": 0,
  "started_at": "2026-02-01T06:20:00+0000",
  "completed_at": "2026-02-01T06:30:00+0000",
  "duration_seconds": 600,
  "task_id": "$task_id",
  "worker_id": "worker-${task_id}-1738000000",
  "iterations_completed": 2,
  "outputs": {"gate_result": "PASS"},
  "errors": [],
  "metadata": {}
}
EOF
}

test_memory_collect_stats_creates_task_stats() {
    local ralph_dir="$TEST_DIR/ralph"
    mkdir -p "$ralph_dir/workers"

    local worker_dir="$ralph_dir/workers/worker-UX-016-1738000000"
    _create_mock_worker "$worker_dir" "UX-016"

    memory_init "$ralph_dir"
    memory_collect_stats "$worker_dir" "$ralph_dir"

    assert_file_exists "$ralph_dir/memory/tasks/UX-016/stats.json" "Task stats.json should be created"

    local task_id
    task_id=$(jq -r '.task_id' "$ralph_dir/memory/tasks/UX-016/stats.json")
    assert_equals "UX-016" "$task_id" "task_id should match"

    local outcome
    outcome=$(jq -r '.outcome' "$ralph_dir/memory/tasks/UX-016/stats.json")
    assert_equals "success" "$outcome" "outcome should be success"

    local total_duration
    total_duration=$(jq -r '.total_duration_s' "$ralph_dir/memory/tasks/UX-016/stats.json")
    assert_equals "1800" "$total_duration" "total_duration should be sum of agents (1200+600)"

    local total_iters
    total_iters=$(jq -r '.total_iterations' "$ralph_dir/memory/tasks/UX-016/stats.json")
    assert_equals "5" "$total_iters" "total_iterations should be sum (3+2)"
}

test_memory_collect_stats_failure_outcome() {
    local ralph_dir="$TEST_DIR/ralph"
    mkdir -p "$ralph_dir/workers"

    local worker_dir="$ralph_dir/workers/worker-FE-003-1738000000"
    _create_mock_worker "$worker_dir" "FE-003" "failure"

    memory_init "$ralph_dir"
    memory_collect_stats "$worker_dir" "$ralph_dir"

    local outcome
    outcome=$(jq -r '.outcome' "$ralph_dir/memory/tasks/FE-003/stats.json")
    assert_equals "failure" "$outcome" "outcome should be failure"
}

test_memory_collect_stats_counts_fix_cycles() {
    local ralph_dir="$TEST_DIR/ralph"
    mkdir -p "$ralph_dir/workers"

    local worker_dir="$ralph_dir/workers/worker-UX-016-1738000000"
    mkdir -p "$worker_dir/results" "$worker_dir/workspace"

    # Create result with FIX gate_result
    cat > "$worker_dir/results/1738000000-result.json" << 'EOF'
{
  "agent_type": "engineering.security-audit",
  "status": "partial",
  "exit_code": 0,
  "duration_seconds": 300,
  "iterations_completed": 1,
  "outputs": {"gate_result": "FIX"},
  "errors": [],
  "metadata": {}
}
EOF

    cat > "$worker_dir/results/1738001000-result.json" << 'EOF'
{
  "agent_type": "engineering.security-fix",
  "status": "success",
  "exit_code": 0,
  "duration_seconds": 500,
  "iterations_completed": 2,
  "outputs": {"gate_result": "PASS"},
  "errors": [],
  "metadata": {}
}
EOF

    memory_init "$ralph_dir"
    memory_collect_stats "$worker_dir" "$ralph_dir"

    local fix_cycles
    fix_cycles=$(jq -r '.fix_cycles' "$ralph_dir/memory/tasks/UX-016/stats.json")
    assert_equals "1" "$fix_cycles" "Should count 1 fix cycle"
}

test_memory_collect_stats_pipeline_entries() {
    local ralph_dir="$TEST_DIR/ralph"
    mkdir -p "$ralph_dir/workers"

    local worker_dir="$ralph_dir/workers/worker-UX-016-1738000000"
    _create_mock_worker "$worker_dir" "UX-016"

    memory_init "$ralph_dir"
    memory_collect_stats "$worker_dir" "$ralph_dir"

    # Check pipeline has entries for each agent step
    local sw_result
    sw_result=$(jq -r '.pipeline.software_engineer.result // empty' "$ralph_dir/memory/tasks/UX-016/stats.json")
    assert_equals "PASS" "$sw_result" "Pipeline should have software-engineer entry"

    local vr_result
    vr_result=$(jq -r '.pipeline.validation_review.result // empty' "$ralph_dir/memory/tasks/UX-016/stats.json")
    assert_equals "PASS" "$vr_result" "Pipeline should have validation-review entry"
}

# =============================================================================
# memory_rebuild_agent_stats tests
# =============================================================================

test_memory_rebuild_agent_stats() {
    local ralph_dir="$TEST_DIR/ralph"
    mkdir -p "$ralph_dir/workers"

    # Create two mock workers for different tasks
    local w1="$ralph_dir/workers/worker-UX-016-1738000000"
    local w2="$ralph_dir/workers/worker-FE-003-1738000001"
    _create_mock_worker "$w1" "UX-016"
    _create_mock_worker "$w2" "FE-003"

    memory_init "$ralph_dir"
    memory_collect_stats "$w1" "$ralph_dir"
    memory_collect_stats "$w2" "$ralph_dir"

    # Check agent stats were created
    assert_file_exists "$ralph_dir/memory/agents/software-engineer/stats.json" \
        "software-engineer stats should exist"
    assert_file_exists "$ralph_dir/memory/agents/validation-review/stats.json" \
        "validation-review stats should exist"

    # Check software-engineer has 2 runs
    local runs
    runs=$(jq -r '.runs' "$ralph_dir/memory/agents/software-engineer/stats.json")
    assert_equals "2" "$runs" "software-engineer should have 2 runs"
}

# =============================================================================
# memory_rebuild_global_stats tests
# =============================================================================

test_memory_rebuild_global_stats() {
    local ralph_dir="$TEST_DIR/ralph"
    mkdir -p "$ralph_dir/workers"

    local w1="$ralph_dir/workers/worker-UX-016-1738000000"
    local w2="$ralph_dir/workers/worker-FE-003-1738000001"
    _create_mock_worker "$w1" "UX-016"
    _create_mock_worker "$w2" "FE-003" "failure"

    memory_init "$ralph_dir"
    memory_collect_stats "$w1" "$ralph_dir"
    memory_collect_stats "$w2" "$ralph_dir"

    local tasks_analyzed
    tasks_analyzed=$(jq -r '.tasks_analyzed' "$ralph_dir/memory/stats.json")
    assert_equals "2" "$tasks_analyzed" "Should have 2 tasks analyzed"

    local success_rate
    success_rate=$(jq -r '.success_rate' "$ralph_dir/memory/stats.json")
    assert_equals "0.50" "$success_rate" "Success rate should be 0.50 (1/2)"
}

# =============================================================================
# memory_rebuild_indexes tests
# =============================================================================

test_memory_rebuild_indexes_tasks() {
    local ralph_dir="$TEST_DIR/ralph"
    mkdir -p "$ralph_dir/workers"

    local w1="$ralph_dir/workers/worker-UX-016-1738000000"
    _create_mock_worker "$w1" "UX-016"

    memory_init "$ralph_dir"
    memory_collect_stats "$w1" "$ralph_dir"

    assert_file_contains "$ralph_dir/memory/tasks/INDEX.md" "UX-016" \
        "Tasks INDEX should list UX-016"
    assert_file_contains "$ralph_dir/memory/tasks/INDEX.md" "success" \
        "Tasks INDEX should show outcome"
}

test_memory_rebuild_indexes_agents() {
    local ralph_dir="$TEST_DIR/ralph"
    mkdir -p "$ralph_dir/workers"

    local w1="$ralph_dir/workers/worker-UX-016-1738000000"
    _create_mock_worker "$w1" "UX-016"

    memory_init "$ralph_dir"
    memory_collect_stats "$w1" "$ralph_dir"

    assert_file_contains "$ralph_dir/memory/agents/INDEX.md" "software-engineer" \
        "Agents INDEX should list software-engineer"
    assert_file_contains "$ralph_dir/memory/agents/INDEX.md" "validation-review" \
        "Agents INDEX should list validation-review"
}

test_memory_rebuild_indexes_patterns() {
    local ralph_dir="$TEST_DIR/ralph"
    memory_init "$ralph_dir"

    # Add a mock pattern file
    cat > "$ralph_dir/memory/patterns/errors/test-error.md" << 'EOF'
# Test Error Pattern

First seen: test
EOF

    memory_rebuild_indexes "$ralph_dir/memory"

    assert_file_contains "$ralph_dir/memory/patterns/errors/INDEX.md" "Test Error Pattern" \
        "Error patterns INDEX should list the pattern"
    assert_file_contains "$ralph_dir/memory/patterns/INDEX.md" "1 patterns" \
        "Patterns INDEX should show 1 error pattern"
}

test_memory_rebuild_indexes_root_updates() {
    local ralph_dir="$TEST_DIR/ralph"
    mkdir -p "$ralph_dir/workers"

    local w1="$ralph_dir/workers/worker-UX-016-1738000000"
    _create_mock_worker "$w1" "UX-016"

    memory_init "$ralph_dir"
    memory_collect_stats "$w1" "$ralph_dir"

    assert_file_contains "$ralph_dir/memory/INDEX.md" "Tasks analyzed: 1" \
        "Root INDEX should show 1 task analyzed"
}

# =============================================================================
# memory_queue_worker tests
# =============================================================================

test_memory_queue_worker_appends_to_pending() {
    local ralph_dir="$TEST_DIR/ralph"
    memory_init "$ralph_dir"

    local worker_dir="$ralph_dir/workers/worker-UX-016-1738000000"
    mkdir -p "$worker_dir"

    memory_queue_worker "$worker_dir"

    assert_file_contains "$ralph_dir/memory/pending.list" "$worker_dir" \
        "pending.list should contain worker dir"
}

test_memory_queue_worker_deduplicates() {
    local ralph_dir="$TEST_DIR/ralph"
    memory_init "$ralph_dir"

    local worker_dir="$ralph_dir/workers/worker-UX-016-1738000000"
    mkdir -p "$worker_dir"

    memory_queue_worker "$worker_dir"
    memory_queue_worker "$worker_dir"

    local count
    count=$(grep -c "$worker_dir" "$ralph_dir/memory/pending.list" || true)
    assert_equals "1" "$count" "Worker should only appear once in pending.list"
}

test_memory_queue_worker_multiple_workers() {
    local ralph_dir="$TEST_DIR/ralph"
    memory_init "$ralph_dir"

    local w1="$ralph_dir/workers/worker-UX-016-1738000000"
    local w2="$ralph_dir/workers/worker-FE-003-1738000001"
    mkdir -p "$w1" "$w2"

    memory_queue_worker "$w1"
    memory_queue_worker "$w2"

    local count
    count=$(wc -l < "$ralph_dir/memory/pending.list" | tr -d '[:space:]')
    assert_equals "2" "$count" "pending.list should have 2 entries"
}

# =============================================================================
# memory_is_analyzed tests
# =============================================================================

test_memory_is_analyzed_false_when_missing() {
    local ralph_dir="$TEST_DIR/ralph"
    memory_init "$ralph_dir"

    if memory_is_analyzed "$ralph_dir/memory" "UX-016"; then
        assert_equals "should not reach" "" "Should not be analyzed"
    else
        assert_equals "0" "0" "Task should not be analyzed yet"
    fi
}

test_memory_is_analyzed_true_when_exists() {
    local ralph_dir="$TEST_DIR/ralph"
    memory_init "$ralph_dir"

    mkdir -p "$ralph_dir/memory/tasks/UX-016"
    echo "# Analysis" > "$ralph_dir/memory/tasks/UX-016/analysis.md"

    if memory_is_analyzed "$ralph_dir/memory" "UX-016"; then
        assert_equals "0" "0" "Task should be analyzed"
    else
        assert_equals "should not reach" "" "Should be analyzed"
    fi
}

# =============================================================================
# Edge cases
# =============================================================================

test_memory_collect_stats_no_results_dir() {
    local ralph_dir="$TEST_DIR/ralph"
    mkdir -p "$ralph_dir/workers"

    local worker_dir="$ralph_dir/workers/worker-UX-016-1738000000"
    mkdir -p "$worker_dir/workspace"
    # No results dir

    memory_init "$ralph_dir"
    memory_collect_stats "$worker_dir" "$ralph_dir"

    assert_file_exists "$ralph_dir/memory/tasks/UX-016/stats.json" \
        "Stats should still be created with defaults"

    local outcome
    outcome=$(jq -r '.outcome' "$ralph_dir/memory/tasks/UX-016/stats.json")
    assert_equals "success" "$outcome" "Default outcome should be success"
}

test_memory_collect_stats_invalid_worker_name() {
    local ralph_dir="$TEST_DIR/ralph"
    mkdir -p "$ralph_dir/workers"

    local worker_dir="$ralph_dir/workers/invalid-name"
    mkdir -p "$worker_dir"

    memory_init "$ralph_dir"

    # Should return 1 (can't extract task ID)
    local rc=0
    memory_collect_stats "$worker_dir" "$ralph_dir" || rc=$?
    assert_equals "1" "$rc" "Should fail for invalid worker name"
}

# =============================================================================
# Run all tests
# =============================================================================

run_test test_memory_init_creates_directory_tree
run_test test_memory_init_creates_index_files
run_test test_memory_init_root_index_content
run_test test_memory_init_global_stats_json
run_test test_memory_init_escalated_content
run_test test_memory_init_idempotent
run_test test_memory_collect_stats_creates_task_stats
run_test test_memory_collect_stats_failure_outcome
run_test test_memory_collect_stats_counts_fix_cycles
run_test test_memory_collect_stats_pipeline_entries
run_test test_memory_rebuild_agent_stats
run_test test_memory_rebuild_global_stats
run_test test_memory_rebuild_indexes_tasks
run_test test_memory_rebuild_indexes_agents
run_test test_memory_rebuild_indexes_patterns
run_test test_memory_rebuild_indexes_root_updates
run_test test_memory_queue_worker_appends_to_pending
run_test test_memory_queue_worker_deduplicates
run_test test_memory_queue_worker_multiple_workers
run_test test_memory_is_analyzed_false_when_missing
run_test test_memory_is_analyzed_true_when_exists
run_test test_memory_collect_stats_no_results_dir
run_test test_memory_collect_stats_invalid_worker_name

print_test_summary
