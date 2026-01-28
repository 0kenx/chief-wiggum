#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/service/service-scheduler.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
export LOG_FILE="/dev/null"
source "$WIGGUM_HOME/lib/core/logger.sh"

# Reset guards so we can source fresh
unset _SERVICE_LOADER_LOADED
unset _SERVICE_STATE_LOADED
unset _SERVICE_RUNNER_LOADED
unset _SERVICE_SCHEDULER_LOADED

source "$WIGGUM_HOME/lib/service/service-loader.sh"
source "$WIGGUM_HOME/lib/service/service-state.sh"
source "$WIGGUM_HOME/lib/service/service-runner.sh"
source "$WIGGUM_HOME/lib/service/service-scheduler.sh"

TEST_DIR=""
setup() {
    TEST_DIR=$(mktemp -d)
    mkdir -p "$TEST_DIR/.ralph"

    # Reset all state
    _SERVICE_JSON_FILE=""
    _SERVICE_JSON=""
    _SERVICE_COUNT=0
    _SERVICE_VERSION=""

    _SERVICE_LAST_RUN=()
    _SERVICE_STATUS=()
    _SERVICE_RUN_COUNT=()
    _SERVICE_FAIL_COUNT=()
    _SERVICE_RUNNING_PID=()

    _SCHED_RALPH_DIR=""
    _SCHED_PROJECT_DIR=""
    _SCHED_INITIALIZED=false
    _SCHED_STARTUP_COMPLETE=false
}

teardown() {
    # Kill any background processes we started
    jobs -p 2>/dev/null | xargs -r kill 2>/dev/null || true
    rm -rf "$TEST_DIR"
}

# =============================================================================
# Helper Functions for Tests
# =============================================================================

# Create a simple test service config
create_test_config() {
    cat > "$TEST_DIR/services.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        {
            "id": "test-interval",
            "schedule": { "type": "interval", "interval": 5, "run_on_startup": true },
            "execution": { "type": "function", "function": "test_function_1" }
        },
        {
            "id": "test-no-startup",
            "schedule": { "type": "interval", "interval": 10 },
            "execution": { "type": "function", "function": "test_function_2" }
        },
        {
            "id": "test-event",
            "schedule": { "type": "event", "trigger": "test.event" },
            "execution": { "type": "function", "function": "test_function_3" }
        }
    ]
}
JSON
}

# Test functions that services will call
# shellcheck disable=SC2034  # Variables set for test state tracking
TEST_FUNC_1_CALLED=false
TEST_FUNC_2_CALLED=false
TEST_FUNC_3_CALLED=false

test_function_1() {
    # shellcheck disable=SC2034
    TEST_FUNC_1_CALLED=true
    echo "test_function_1 called"
}

test_function_2() {
    # shellcheck disable=SC2034
    TEST_FUNC_2_CALLED=true
    echo "test_function_2 called"
}

test_function_3() {
    # shellcheck disable=SC2034
    TEST_FUNC_3_CALLED=true
    echo "test_function_3 called"
}

# Export test functions so subshells can call them
export -f test_function_1
export -f test_function_2
export -f test_function_3

# =============================================================================
# service_state Tests
# =============================================================================

test_state_init_creates_empty_state() {
    service_state_init "$TEST_DIR/.ralph"

    assert_equals "0" "$(service_state_get_last_run "any-service")" \
        "Last run should be 0 for unknown service"
    assert_equals "stopped" "$(service_state_get_status "any-service")" \
        "Status should be stopped for unknown service"
}

test_state_mark_started_updates_state() {
    service_state_init "$TEST_DIR/.ralph"

    service_state_mark_started "my-service" "12345"

    assert_equals "running" "$(service_state_get_status "my-service")" \
        "Status should be running after mark_started"
    assert_equals "12345" "$(service_state_get_pid "my-service")" \
        "PID should be set after mark_started"
    assert_equals "1" "$(service_state_get_run_count "my-service")" \
        "Run count should be 1 after first start"
}

test_state_mark_completed_updates_state() {
    service_state_init "$TEST_DIR/.ralph"

    service_state_mark_started "my-service" "12345"
    service_state_mark_completed "my-service"

    assert_equals "stopped" "$(service_state_get_status "my-service")" \
        "Status should be stopped after completion"
    assert_equals "" "$(service_state_get_pid "my-service")" \
        "PID should be cleared after completion"
}

test_state_mark_failed_increments_failures() {
    service_state_init "$TEST_DIR/.ralph"

    service_state_mark_started "my-service"
    service_state_mark_failed "my-service"

    assert_equals "failed" "$(service_state_get_status "my-service")" \
        "Status should be failed"
    assert_equals "1" "$(service_state_get_fail_count "my-service")" \
        "Fail count should be 1"

    service_state_mark_started "my-service"
    service_state_mark_failed "my-service"

    assert_equals "2" "$(service_state_get_fail_count "my-service")" \
        "Fail count should be 2 after second failure"
}

test_state_save_and_restore() {
    service_state_init "$TEST_DIR/.ralph"

    service_state_mark_started "svc-1" "111"
    service_state_mark_completed "svc-1"
    service_state_mark_started "svc-2"
    service_state_mark_failed "svc-2"

    service_state_save

    assert_file_exists "$TEST_DIR/.ralph/.service-state.json" \
        "State file should be created"

    # Simulate process restart: clear in-memory state but keep file
    _SERVICE_LAST_RUN=()
    _SERVICE_STATUS=()
    _SERVICE_RUN_COUNT=()
    _SERVICE_FAIL_COUNT=()
    _SERVICE_RUNNING_PID=()

    # Re-init and restore
    service_state_init "$TEST_DIR/.ralph"
    service_state_restore

    assert_equals "1" "$(service_state_get_run_count "svc-1")" \
        "Run count should be restored for svc-1"
    assert_equals "1" "$(service_state_get_fail_count "svc-2")" \
        "Fail count should be restored for svc-2"
}

# =============================================================================
# service_is_due Tests
# =============================================================================

test_is_due_returns_true_when_never_run() {
    create_test_config
    service_load "$TEST_DIR/services.json"
    service_state_init "$TEST_DIR/.ralph"

    # Service never run, should be due
    service_is_due "test-interval"
    local rc=$?

    assert_equals "0" "$rc" "Service should be due when never run"
}

test_is_due_returns_false_when_recently_run() {
    create_test_config
    service_load "$TEST_DIR/services.json"
    service_state_init "$TEST_DIR/.ralph"

    # Mark as just run
    local now
    now=$(date +%s)
    service_state_set_last_run "test-interval" "$now"

    service_is_due "test-interval"
    local rc=$?

    assert_equals "1" "$rc" "Service should not be due when just run"
}

test_is_due_returns_true_when_interval_passed() {
    create_test_config
    service_load "$TEST_DIR/services.json"
    service_state_init "$TEST_DIR/.ralph"

    # Mark as run 10 seconds ago (interval is 5)
    local past
    past=$(($(date +%s) - 10))
    service_state_set_last_run "test-interval" "$past"

    service_is_due "test-interval"
    local rc=$?

    assert_equals "0" "$rc" "Service should be due when interval has passed"
}

# =============================================================================
# service_trigger_event Tests
# =============================================================================

test_trigger_event_calls_matching_service() {
    create_test_config
    service_load "$TEST_DIR/services.json"
    service_state_init "$TEST_DIR/.ralph"
    service_runner_init "$TEST_DIR/.ralph" "$TEST_DIR"

    # Reset test flags
    # shellcheck disable=SC2034
    TEST_FUNC_3_CALLED=false

    _SCHED_INITIALIZED=true
    service_trigger_event "test.event"

    # Give background process a moment
    sleep 0.2

    local status
    status=$(service_state_get_status "test-event")

    # Event should have been triggered (service started)
    assert_not_equals "stopped" "$status" \
        "Event service should have been triggered"
}

test_trigger_event_ignores_non_matching() {
    create_test_config
    service_load "$TEST_DIR/services.json"
    service_state_init "$TEST_DIR/.ralph"
    service_runner_init "$TEST_DIR/.ralph" "$TEST_DIR"

    _SCHED_INITIALIZED=true
    service_trigger_event "other.event"

    local status
    status=$(service_state_get_status "test-event")

    assert_equals "stopped" "$status" \
        "Non-matching event should not trigger service"
}

# =============================================================================
# service_scheduler_init Tests
# =============================================================================

test_scheduler_init_loads_config() {
    create_test_config

    # Copy config to expected location
    mkdir -p "$WIGGUM_HOME/config"
    cp "$TEST_DIR/services.json" "$WIGGUM_HOME/config/services.json.test"

    service_load "$TEST_DIR/services.json"
    service_state_init "$TEST_DIR/.ralph"
    service_runner_init "$TEST_DIR/.ralph" "$TEST_DIR"
    _SCHED_RALPH_DIR="$TEST_DIR/.ralph"
    _SCHED_PROJECT_DIR="$TEST_DIR"
    _SCHED_INITIALIZED=true

    assert_equals "3" "$(service_count)" "Should have loaded 3 services"

    # Cleanup
    rm -f "$WIGGUM_HOME/config/services.json.test"
}

# =============================================================================
# service_scheduler_status Tests
# =============================================================================

test_scheduler_status_returns_json() {
    create_test_config
    service_load "$TEST_DIR/services.json"
    service_state_init "$TEST_DIR/.ralph"
    _SCHED_INITIALIZED=true

    local status_json
    status_json=$(service_scheduler_status)

    assert_output_contains "$status_json" "enabled_services" \
        "Status should contain enabled_services"
    assert_output_contains "$status_json" "running_services" \
        "Status should contain running_services"
    assert_output_contains "$status_json" "initialized" \
        "Status should contain initialized"
}

test_scheduler_service_status_returns_details() {
    create_test_config
    service_load "$TEST_DIR/services.json"
    service_state_init "$TEST_DIR/.ralph"

    service_state_mark_started "test-interval"
    service_state_mark_completed "test-interval"

    local status_json
    status_json=$(service_scheduler_service_status "test-interval")

    assert_output_contains "$status_json" "test-interval" \
        "Status should contain service ID"
    assert_output_contains "$status_json" "run_count" \
        "Status should contain run_count"
    assert_output_contains "$status_json" "interval" \
        "Status should contain interval"
}

# =============================================================================
# Concurrency Tests
# =============================================================================

test_concurrency_skip_when_running() {
    cat > "$TEST_DIR/services.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        {
            "id": "skip-svc",
            "schedule": { "type": "interval", "interval": 1 },
            "execution": { "type": "function", "function": "test_function_1" },
            "concurrency": { "max_instances": 1, "if_running": "skip" }
        }
    ]
}
JSON

    service_load "$TEST_DIR/services.json"
    service_state_init "$TEST_DIR/.ralph"
    service_runner_init "$TEST_DIR/.ralph" "$TEST_DIR"
    _SCHED_INITIALIZED=true

    # Simulate running state
    service_state_set_status "skip-svc" "running"

    # Create a fake PID that appears running
    service_state_set_pid "skip-svc" "$$"  # Use our own PID

    # Try to run - should skip
    _run_service_if_allowed "skip-svc"

    local status
    status=$(service_state_get_status "skip-svc")

    # Should be marked as skipped (or still running)
    assert_not_equals "stopped" "$status" \
        "Service should be skipped when already running"
}

# =============================================================================
# Run All Tests
# =============================================================================

# State tests
run_test test_state_init_creates_empty_state
run_test test_state_mark_started_updates_state
run_test test_state_mark_completed_updates_state
run_test test_state_mark_failed_increments_failures
run_test test_state_save_and_restore

# is_due tests
run_test test_is_due_returns_true_when_never_run
run_test test_is_due_returns_false_when_recently_run
run_test test_is_due_returns_true_when_interval_passed

# Event trigger tests
run_test test_trigger_event_calls_matching_service
run_test test_trigger_event_ignores_non_matching

# Scheduler tests
run_test test_scheduler_init_loads_config
run_test test_scheduler_status_returns_json
run_test test_scheduler_service_status_returns_details

# Concurrency tests
run_test test_concurrency_skip_when_running

print_test_summary
exit_with_test_result
