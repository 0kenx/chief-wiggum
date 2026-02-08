#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/utils/metrics-export.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
export LOG_FILE="/dev/null"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/utils/calculate-cost.sh"
source "$WIGGUM_HOME/lib/utils/metrics-export.sh"

# Helper: set a far-future mtime to invalidate stat-based cache fingerprints
# without sleeping. The cache uses stat mtime+size, so any different mtime works.
_touch_future() {
    touch -t 203001010000.00 "$1"
}

TEST_DIR=""
setup() {
    TEST_DIR=$(mktemp -d)
    export PROJECT_DIR="$TEST_DIR"
}

teardown() {
    [ -n "$TEST_DIR" ] && rm -rf "$TEST_DIR"
}

# Helper: create a worker directory with a PRD file
_create_worker() {
    local ralph_dir="$1"
    local worker_id="$2"
    local status="$3"  # success, failed, in_progress

    local worker_dir="$ralph_dir/workers/$worker_id"
    mkdir -p "$worker_dir/logs"

    # Create PRD based on status
    case "$status" in
        success)
            cat > "$worker_dir/prd.md" << 'EOF'
# Task PRD
- [x] Implement feature
- [x] Write tests
EOF
            ;;
        failed)
            cat > "$worker_dir/prd.md" << 'EOF'
# Task PRD
- [*] Implement feature
- [ ] Write tests
EOF
            ;;
        in_progress)
            cat > "$worker_dir/prd.md" << 'EOF'
# Task PRD
- [x] Implement feature
- [ ] Write tests
EOF
            ;;
    esac

    echo "$worker_dir"
}

# Helper: create an iteration log with token usage
_create_iteration_log() {
    local worker_dir="$1"
    local iteration="$2"
    local input_tokens="${3:-1000}"
    local output_tokens="${4:-500}"
    local duration_ms="${5:-60000}"
    local cost="${6:-0.05}"

    # Use generic step ID for test (pattern works with any step ID)
    cat > "$worker_dir/logs/teststep-${iteration}.log" << EOF
{"type":"result","duration_ms":$duration_ms,"total_cost_usd":$cost,"usage":{"input_tokens":$input_tokens,"output_tokens":$output_tokens,"cache_creation_input_tokens":200,"cache_read_input_tokens":100}}
EOF
}

# =============================================================================
# export_metrics() Tests
# =============================================================================

test_export_metrics_no_workers_dir_returns_1() {
    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir"
    # No workers/ directory

    local output
    output=$(export_metrics "$ralph_dir" 2>&1)
    local exit_code=$?

    assert_equals "1" "$exit_code" "Should return 1 when workers dir missing"
    assert_output_contains "$output" "No workers directory" "Should report missing workers directory"
}

test_export_metrics_empty_workers_dir_writes_valid_json() {
    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir/workers"

    export_metrics "$ralph_dir" > /dev/null 2>&1

    local output_file="$ralph_dir/metrics.json"
    assert_file_exists "$output_file" "metrics.json should be created"

    # Validate JSON structure
    jq '.' "$output_file" > /dev/null 2>&1
    local exit_code=$?
    assert_equals "0" "$exit_code" "Output should be valid JSON"

    # Check summary fields exist
    local total_workers
    total_workers=$(jq '.summary.total_workers' "$output_file")
    assert_equals "0" "$total_workers" "total_workers should be 0 for empty dir"
}

test_export_metrics_one_successful_worker() {
    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir/workers"

    local worker_dir
    worker_dir=$(_create_worker "$ralph_dir" "worker-TASK-001-12345" "success")
    _create_iteration_log "$worker_dir" 1 2000 1000 120000 0.10

    export_metrics "$ralph_dir" > /dev/null 2>&1

    local output_file="$ralph_dir/metrics.json"
    assert_file_exists "$output_file" "metrics.json should be created"

    # Verify summary
    local total_workers
    total_workers=$(jq '.summary.total_workers' "$output_file")
    assert_equals "1" "$total_workers" "Should have 1 total worker"

    local successful_workers
    successful_workers=$(jq '.summary.successful_workers' "$output_file")
    assert_equals "1" "$successful_workers" "Should have 1 successful worker"

    local failed_workers
    failed_workers=$(jq '.summary.failed_workers' "$output_file")
    assert_equals "0" "$failed_workers" "Should have 0 failed workers"

    # Verify worker entry
    local worker_status
    worker_status=$(jq -r '.workers[0].status' "$output_file")
    assert_equals "success" "$worker_status" "Worker status should be success"

    local worker_id
    worker_id=$(jq -r '.workers[0].worker_id' "$output_file")
    assert_equals "worker-TASK-001-12345" "$worker_id" "Worker ID should match"
}

test_export_metrics_with_failed_worker() {
    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir/workers"

    _create_worker "$ralph_dir" "worker-TASK-002-22222" "success" > /dev/null
    _create_worker "$ralph_dir" "worker-TASK-003-33333" "failed" > /dev/null
    _create_worker "$ralph_dir" "worker-TASK-004-44444" "success" > /dev/null

    export_metrics "$ralph_dir" > /dev/null 2>&1

    local output_file="$ralph_dir/metrics.json"

    local total_workers
    total_workers=$(jq '.summary.total_workers' "$output_file")
    assert_equals "3" "$total_workers" "Should have 3 total workers"

    local successful_workers
    successful_workers=$(jq '.summary.successful_workers' "$output_file")
    assert_equals "2" "$successful_workers" "Should have 2 successful workers"

    local failed_workers
    failed_workers=$(jq '.summary.failed_workers' "$output_file")
    assert_equals "1" "$failed_workers" "Should have 1 failed worker"
}

test_export_metrics_summary_includes_total_workers() {
    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir/workers"

    local w1 w2
    w1=$(_create_worker "$ralph_dir" "worker-TASK-005-55555" "success")
    w2=$(_create_worker "$ralph_dir" "worker-TASK-006-66666" "success")
    _create_iteration_log "$w1" 1 3000 1500 180000 0.15
    _create_iteration_log "$w2" 1 4000 2000 240000 0.20

    export_metrics "$ralph_dir" > /dev/null 2>&1

    local output_file="$ralph_dir/metrics.json"

    # Check summary has all required fields
    local has_total_workers has_successful has_failed has_success_rate has_total_time has_total_cost
    has_total_workers=$(jq 'has("summary") and (.summary | has("total_workers"))' "$output_file")
    has_successful=$(jq '.summary | has("successful_workers")' "$output_file")
    has_failed=$(jq '.summary | has("failed_workers")' "$output_file")
    has_success_rate=$(jq '.summary | has("success_rate")' "$output_file")
    has_total_time=$(jq '.summary | has("total_time")' "$output_file")
    has_total_cost=$(jq '.summary | has("total_cost")' "$output_file")

    assert_equals "true" "$has_total_workers" "Summary should have total_workers"
    assert_equals "true" "$has_successful" "Summary should have successful_workers"
    assert_equals "true" "$has_failed" "Summary should have failed_workers"
    assert_equals "true" "$has_success_rate" "Summary should have success_rate"
    assert_equals "true" "$has_total_time" "Summary should have total_time"
    assert_equals "true" "$has_total_cost" "Summary should have total_cost"

    local total_workers
    total_workers=$(jq '.summary.total_workers' "$output_file")
    assert_equals "2" "$total_workers" "total_workers should be 2"
}

test_export_metrics_valid_json_structure() {
    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir/workers"

    local w1
    w1=$(_create_worker "$ralph_dir" "worker-TASK-007-77777" "success")
    _create_iteration_log "$w1" 1 5000 2500 300000 0.25

    export_metrics "$ralph_dir" > /dev/null 2>&1

    local output_file="$ralph_dir/metrics.json"

    # Validate overall structure
    local has_summary has_tokens has_context has_workers
    has_summary=$(jq 'has("summary")' "$output_file")
    has_tokens=$(jq 'has("tokens")' "$output_file")
    has_context=$(jq 'has("context")' "$output_file")
    has_workers=$(jq 'has("workers")' "$output_file")

    assert_equals "true" "$has_summary" "Should have summary section"
    assert_equals "true" "$has_tokens" "Should have tokens section"
    assert_equals "true" "$has_context" "Should have context section"
    assert_equals "true" "$has_workers" "Should have workers section"

    # Workers should be an array
    local workers_type
    workers_type=$(jq '.workers | type' "$output_file")
    assert_equals '"array"' "$workers_type" "Workers should be an array"

    # Token section should have expected fields
    local has_input has_output has_total
    has_input=$(jq '.tokens | has("input")' "$output_file")
    has_output=$(jq '.tokens | has("output")' "$output_file")
    has_total=$(jq '.tokens | has("total")' "$output_file")

    assert_equals "true" "$has_input" "Tokens should have input field"
    assert_equals "true" "$has_output" "Tokens should have output field"
    assert_equals "true" "$has_total" "Tokens should have total field"
}

# =============================================================================
# Cache Tests
# =============================================================================

test_export_metrics_creates_cache_files() {
    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir/workers"

    local w1
    w1=$(_create_worker "$ralph_dir" "worker-TASK-010-10101" "success")
    _create_iteration_log "$w1" 1 2000 1000 120000 0.10

    export_metrics "$ralph_dir" > /dev/null 2>&1

    local cache_dir="$ralph_dir/cache/metrics"
    assert_file_exists "$cache_dir/worker-TASK-010-10101.json" "Cache file should be created"

    # Cache file should contain fingerprint and data
    local has_fp has_data
    has_fp=$(jq 'has("fingerprint")' "$cache_dir/worker-TASK-010-10101.json")
    has_data=$(jq 'has("data")' "$cache_dir/worker-TASK-010-10101.json")
    assert_equals "true" "$has_fp" "Cache should have fingerprint"
    assert_equals "true" "$has_data" "Cache should have data"
}

test_export_metrics_cache_hit_produces_same_output() {
    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir/workers"

    local w1
    w1=$(_create_worker "$ralph_dir" "worker-TASK-011-11111" "success")
    _create_iteration_log "$w1" 1 3000 1500 180000 0.15

    # First export
    export_metrics "$ralph_dir" > /dev/null 2>&1
    local first_output
    first_output=$(jq -cS '.' "$ralph_dir/metrics.json")

    # Second export (should hit cache)
    export_metrics "$ralph_dir" > /dev/null 2>&1
    local second_output
    second_output=$(jq -cS '.' "$ralph_dir/metrics.json")

    assert_equals "$first_output" "$second_output" "Cached export should produce identical output"
}

test_export_metrics_cache_invalidation_on_new_log() {
    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir/workers"

    local w1
    w1=$(_create_worker "$ralph_dir" "worker-TASK-012-12121" "success")
    _create_iteration_log "$w1" 1 2000 1000 120000 0.10

    # First export
    export_metrics "$ralph_dir" > /dev/null 2>&1
    local first_cost
    first_cost=$(jq '.summary.total_cost' "$ralph_dir/metrics.json")

    # Add another log file with different mtime to invalidate cache
    _create_iteration_log "$w1" 2 3000 1500 180000 0.20
    _touch_future "$w1/logs/teststep-2.log"

    # Second export should pick up new log
    export_metrics "$ralph_dir" > /dev/null 2>&1
    local second_cost
    second_cost=$(jq '.summary.total_cost' "$ralph_dir/metrics.json")

    # Cost should have increased (0.10 -> 0.30)
    local cost_increased
    cost_increased=$(echo "$second_cost > $first_cost" | bc)
    assert_equals "1" "$cost_increased" "Cost should increase after adding log (was $first_cost, now $second_cost)"
}

test_export_metrics_cache_invalidation_on_prd_change() {
    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir/workers"

    local w1
    w1=$(_create_worker "$ralph_dir" "worker-TASK-013-13131" "in_progress")
    _create_iteration_log "$w1" 1 2000 1000 120000 0.10

    # First export — worker is in_progress
    export_metrics "$ralph_dir" > /dev/null 2>&1
    local first_status
    first_status=$(jq -r '.workers[0].status' "$ralph_dir/metrics.json")
    assert_equals "in_progress" "$first_status" "Should be in_progress initially"

    # Update PRD to mark success (far-future mtime to invalidate cache)
    cat > "$w1/prd.md" << 'EOF'
# Task PRD
- [x] Implement feature
- [x] Write tests
EOF
    _touch_future "$w1/prd.md"

    # Second export should pick up status change
    export_metrics "$ralph_dir" > /dev/null 2>&1
    local second_status
    second_status=$(jq -r '.workers[0].status' "$ralph_dir/metrics.json")
    assert_equals "success" "$second_status" "Should be success after PRD update"
}

test_export_metrics_cache_cleanup_stale_entries() {
    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir/workers"

    local w1 w2
    w1=$(_create_worker "$ralph_dir" "worker-TASK-014-14141" "success")
    w2=$(_create_worker "$ralph_dir" "worker-TASK-015-15151" "success")

    # Export to create cache for both
    export_metrics "$ralph_dir" > /dev/null 2>&1

    local cache_dir="$ralph_dir/cache/metrics"
    assert_file_exists "$cache_dir/worker-TASK-014-14141.json" "Cache for worker 014 should exist"
    assert_file_exists "$cache_dir/worker-TASK-015-15151.json" "Cache for worker 015 should exist"

    # Remove one worker
    [ -n "$ralph_dir" ] && rm -rf "$ralph_dir/workers/worker-TASK-014-14141"

    # Export again — stale cache should be cleaned up
    export_metrics "$ralph_dir" > /dev/null 2>&1

    [ ! -f "$cache_dir/worker-TASK-014-14141.json" ]
    local exit_code=$?
    assert_equals "0" "$exit_code" "Stale cache for removed worker should be cleaned up"
    assert_file_exists "$cache_dir/worker-TASK-015-15151.json" "Cache for remaining worker should still exist"
}

test_export_metrics_cache_invalidation_on_pr_url() {
    local ralph_dir="$TEST_DIR/.ralph"
    mkdir -p "$ralph_dir/workers"

    local w1
    w1=$(_create_worker "$ralph_dir" "worker-TASK-016-16161" "success")

    # First export — no PR URL
    export_metrics "$ralph_dir" > /dev/null 2>&1
    local first_pr
    first_pr=$(jq -r '.workers[0].pr_url' "$ralph_dir/metrics.json")
    assert_equals "" "$first_pr" "PR URL should be empty initially"

    # Add PR URL (far-future mtime to invalidate cache)
    echo "https://github.com/example/repo/pull/42" > "$w1/pr_url.txt"
    _touch_future "$w1/pr_url.txt"

    # Second export should pick up PR URL
    export_metrics "$ralph_dir" > /dev/null 2>&1
    local second_pr
    second_pr=$(jq -r '.workers[0].pr_url' "$ralph_dir/metrics.json")
    assert_equals "https://github.com/example/repo/pull/42" "$second_pr" "PR URL should be set after update"
}

# =============================================================================
# Run All Tests
# =============================================================================

run_test test_export_metrics_no_workers_dir_returns_1
run_test test_export_metrics_empty_workers_dir_writes_valid_json
run_test test_export_metrics_one_successful_worker
run_test test_export_metrics_with_failed_worker
run_test test_export_metrics_summary_includes_total_workers
run_test test_export_metrics_valid_json_structure
run_test test_export_metrics_creates_cache_files
run_test test_export_metrics_cache_hit_produces_same_output
run_test test_export_metrics_cache_invalidation_on_new_log
run_test test_export_metrics_cache_invalidation_on_prd_change
run_test test_export_metrics_cache_cleanup_stale_entries
run_test test_export_metrics_cache_invalidation_on_pr_url

print_test_summary
exit_with_test_result
