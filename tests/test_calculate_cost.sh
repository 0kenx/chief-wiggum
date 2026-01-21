#!/usr/bin/env bash
# Tests for lib/metrics/calculate-cost.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$WIGGUM_HOME/lib/metrics/calculate-cost.sh"

# =============================================================================
# get_context_size() Tests
# =============================================================================

test_get_context_size_known_model() {
    local size
    size=$(get_context_size "claude-sonnet-4-20250514")
    assert_equals "200000" "$size" "Should return 200k for sonnet model"
}

test_get_context_size_opus_model() {
    local size
    size=$(get_context_size "claude-opus-4-0-20250514")
    assert_equals "200000" "$size" "Should return 200k for opus model"
}

test_get_context_size_haiku_model() {
    local size
    size=$(get_context_size "claude-3-5-haiku-20241022")
    assert_equals "200000" "$size" "Should return 200k for haiku model"
}

test_get_context_size_unknown_model_default() {
    local size
    size=$(get_context_size "unknown-model-xyz")
    assert_equals "200000" "$size" "Should return default 200k for unknown model"
}

# =============================================================================
# format_model_name() Tests
# =============================================================================

test_format_model_name_removes_date() {
    local name
    name=$(format_model_name "claude-sonnet-4-20250514")
    # Should strip the date suffix
    if echo "$name" | grep -q "20250514"; then
        echo -e "  ${RED}X${NC} Should remove date suffix"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Date suffix removed"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_format_model_name_removes_claude_prefix() {
    local name
    name=$(format_model_name "claude-3-5-sonnet-20241022")
    # Should remove claude- prefix
    if echo "$name" | grep -q "claude-"; then
        echo -e "  ${RED}X${NC} Should remove claude- prefix"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    else
        echo -e "  ${GREEN}✓${NC} Claude prefix removed"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_format_model_name_uppercase() {
    local name
    name=$(format_model_name "claude-3-5-sonnet-20241022")
    # Should be uppercase
    if [[ "$name" == "${name^^}" ]]; then
        echo -e "  ${GREEN}✓${NC} Name is uppercased"
    else
        echo -e "  ${RED}X${NC} Name should be uppercase, got: $name"
        FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

# =============================================================================
# calculate_worker_cost() Tests (Integration with sample fixture)
# =============================================================================

test_calculate_worker_cost_with_fixture() {
    local fixture_dir="$FIXTURES_DIR/sample-worker-log"

    # Skip if fixture doesn't exist
    if [ ! -d "$fixture_dir/logs" ]; then
        echo -e "  ${YELLOW}⚠${NC} Skipping: fixture not found"
        return 0
    fi

    local output
    output=$(calculate_worker_cost "$fixture_dir/worker.log" 2>&1)
    local exit_code=$?

    assert_equals "0" "$exit_code" "Should succeed with valid logs"
    assert_output_contains "$output" "Worker Time and Cost Report" "Should include report header"
    assert_output_contains "$output" "Token Usage:" "Should include token usage section"
    assert_output_contains "$output" "Total Cost:" "Should include total cost"
}

test_calculate_worker_cost_exports_variables() {
    local fixture_dir="$FIXTURES_DIR/sample-worker-log"

    if [ ! -d "$fixture_dir/logs" ]; then
        echo -e "  ${YELLOW}⚠${NC} Skipping: fixture not found"
        return 0
    fi

    # Run in subshell and capture exported vars
    (
        calculate_worker_cost "$fixture_dir/worker.log" > /dev/null 2>&1

        # Check that expected variables are exported
        if [ -n "$WORKER_TIME_SPENT" ]; then
            echo "WORKER_TIME_SPENT=$WORKER_TIME_SPENT"
        fi
        if [ -n "$WORKER_TOTAL_COST" ]; then
            echo "WORKER_TOTAL_COST=$WORKER_TOTAL_COST"
        fi
        if [ -n "$WORKER_INPUT_TOKENS" ]; then
            echo "WORKER_INPUT_TOKENS=$WORKER_INPUT_TOKENS"
        fi
    ) > /tmp/cost_vars.txt

    local vars_output
    vars_output=$(cat /tmp/cost_vars.txt)
    rm -f /tmp/cost_vars.txt

    assert_output_contains "$vars_output" "WORKER_TIME_SPENT=" "Should export WORKER_TIME_SPENT"
    assert_output_contains "$vars_output" "WORKER_TOTAL_COST=" "Should export WORKER_TOTAL_COST"
}

test_calculate_worker_cost_missing_logs_dir() {
    local tmp_dir
    tmp_dir=$(mktemp -d)
    echo "dummy log" > "$tmp_dir/worker.log"
    # No logs/ subdirectory

    local output
    output=$(calculate_worker_cost "$tmp_dir/worker.log" 2>&1)
    local exit_code=$?

    rm -rf "$tmp_dir"

    assert_equals "1" "$exit_code" "Should fail when logs directory missing"
    assert_output_contains "$output" "Logs directory not found" "Should report missing logs directory"
}

# =============================================================================
# calculate_latest_context_usage() Tests
# =============================================================================

test_calculate_latest_context_usage_with_fixture() {
    local fixture_dir="$FIXTURES_DIR/sample-worker-log/logs"

    if [ ! -d "$fixture_dir" ]; then
        echo -e "  ${YELLOW}⚠${NC} Skipping: fixture not found"
        return 0
    fi

    local output
    output=$(calculate_latest_context_usage "$fixture_dir" 2>&1)

    # Should return: model_name context_tokens context_size context_percent
    if [ -n "$output" ]; then
        local fields
        fields=$(echo "$output" | wc -w)
        if [ "$fields" -ge 3 ]; then
            echo -e "  ${GREEN}✓${NC} Returns expected fields (got $fields)"
        else
            echo -e "  ${RED}X${NC} Expected at least 3 fields, got $fields"
            FAILED_ASSERTIONS=$((FAILED_ASSERTIONS + 1))
        fi
    else
        echo -e "  ${YELLOW}⚠${NC} No output - check if fixture format is correct"
    fi
    ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
}

test_calculate_latest_context_usage_missing_dir() {
    local result
    calculate_latest_context_usage "/nonexistent/path" > /dev/null 2>&1
    result=$?

    assert_equals "1" "$result" "Should fail for missing directory"
}

# =============================================================================
# Run All Tests
# =============================================================================

# get_context_size tests
run_test test_get_context_size_known_model
run_test test_get_context_size_opus_model
run_test test_get_context_size_haiku_model
run_test test_get_context_size_unknown_model_default

# format_model_name tests
run_test test_format_model_name_removes_date
run_test test_format_model_name_removes_claude_prefix
run_test test_format_model_name_uppercase

# calculate_worker_cost tests
run_test test_calculate_worker_cost_with_fixture
run_test test_calculate_worker_cost_exports_variables
run_test test_calculate_worker_cost_missing_logs_dir

# calculate_latest_context_usage tests
run_test test_calculate_latest_context_usage_with_fixture
run_test test_calculate_latest_context_usage_missing_dir

print_test_summary
exit_with_test_result
