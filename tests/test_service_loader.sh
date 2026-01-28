#!/usr/bin/env bash
set -euo pipefail
# Tests for lib/service/service-loader.sh

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
export LOG_FILE="/dev/null"
source "$WIGGUM_HOME/lib/core/logger.sh"

# Reset the loader guard so we can source it
unset _SERVICE_LOADER_LOADED
source "$WIGGUM_HOME/lib/service/service-loader.sh"

TEST_DIR=""
setup() {
    TEST_DIR=$(mktemp -d)
    # Reset service state
    _SERVICE_JSON_FILE=""
    _SERVICE_JSON=""
    _SERVICE_COUNT=0
    _SERVICE_VERSION=""
}
teardown() {
    rm -rf "$TEST_DIR"
}

# =============================================================================
# service_load - Valid Input Tests
# =============================================================================

test_load_valid_two_service_config() {
    cat > "$TEST_DIR/services.json" << 'JSON'
{
    "version": "1.0",
    "defaults": {
        "timeout": 300
    },
    "services": [
        {
            "id": "service-one",
            "schedule": { "type": "interval", "interval": 60 },
            "execution": { "type": "command", "command": "echo hello" }
        },
        {
            "id": "service-two",
            "schedule": { "type": "interval", "interval": 120, "run_on_startup": true },
            "execution": { "type": "function", "function": "my_function" }
        }
    ]
}
JSON

    service_load "$TEST_DIR/services.json"
    local rc=$?

    assert_equals "0" "$rc" "service_load should return 0 for valid input"
    assert_equals "1.0" "$(service_version)" "Service version should be 1.0"
    assert_equals "2" "$(service_count)" "Should have 2 services"
}

test_load_gets_service_by_id() {
    cat > "$TEST_DIR/services.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        {
            "id": "test-service",
            "description": "A test service",
            "schedule": { "type": "interval", "interval": 60 },
            "execution": { "type": "command", "command": "echo hello" }
        }
    ]
}
JSON

    service_load "$TEST_DIR/services.json"

    local service_json
    service_json=$(service_get_by_id "test-service")

    assert_output_contains "$service_json" "test-service" "Should contain service ID"
    assert_output_contains "$service_json" "A test service" "Should contain description"
}

# =============================================================================
# service_load - Error Handling Tests
# =============================================================================

test_load_missing_file() {
    service_load "$TEST_DIR/nonexistent.json" 2>/dev/null
    local rc=$?

    assert_equals "1" "$rc" "service_load should return 1 for missing file"
}

test_load_invalid_json() {
    cat > "$TEST_DIR/bad.json" << 'JSON'
{ this is not valid json [[[
JSON

    service_load "$TEST_DIR/bad.json" 2>/dev/null
    local rc=$?

    assert_equals "1" "$rc" "service_load should return 1 for invalid JSON"
}

test_load_empty_services_array() {
    cat > "$TEST_DIR/empty.json" << 'JSON'
{
    "version": "1.0",
    "services": []
}
JSON

    service_load "$TEST_DIR/empty.json" 2>/dev/null
    local rc=$?

    assert_equals "1" "$rc" "service_load should return 1 for empty services array"
}

test_load_duplicate_service_ids() {
    cat > "$TEST_DIR/dupes.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        { "id": "svc-a", "schedule": { "type": "interval", "interval": 60 }, "execution": { "type": "command", "command": "echo 1" } },
        { "id": "svc-a", "schedule": { "type": "interval", "interval": 120 }, "execution": { "type": "command", "command": "echo 2" } }
    ]
}
JSON

    service_load "$TEST_DIR/dupes.json" 2>/dev/null
    local rc=$?

    assert_equals "1" "$rc" "service_load should return 1 for duplicate service IDs"
}

test_load_missing_service_id() {
    cat > "$TEST_DIR/no-id.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        { "schedule": { "type": "interval", "interval": 60 }, "execution": { "type": "command", "command": "echo 1" } }
    ]
}
JSON

    service_load "$TEST_DIR/no-id.json" 2>/dev/null
    local rc=$?

    assert_equals "1" "$rc" "service_load should return 1 for missing service ID"
}

test_load_missing_schedule() {
    cat > "$TEST_DIR/no-schedule.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        { "id": "svc-a", "execution": { "type": "command", "command": "echo 1" } }
    ]
}
JSON

    service_load "$TEST_DIR/no-schedule.json" 2>/dev/null
    local rc=$?

    assert_equals "1" "$rc" "service_load should return 1 for missing schedule"
}

test_load_missing_execution() {
    cat > "$TEST_DIR/no-execution.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        { "id": "svc-a", "schedule": { "type": "interval", "interval": 60 } }
    ]
}
JSON

    service_load "$TEST_DIR/no-execution.json" 2>/dev/null
    local rc=$?

    assert_equals "1" "$rc" "service_load should return 1 for missing execution"
}

test_load_invalid_schedule_type() {
    cat > "$TEST_DIR/bad-schedule.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        { "id": "svc-a", "schedule": { "type": "invalid" }, "execution": { "type": "command", "command": "echo 1" } }
    ]
}
JSON

    service_load "$TEST_DIR/bad-schedule.json" 2>/dev/null
    local rc=$?

    assert_equals "1" "$rc" "service_load should return 1 for invalid schedule type"
}

test_load_invalid_execution_type() {
    cat > "$TEST_DIR/bad-execution.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        { "id": "svc-a", "schedule": { "type": "interval", "interval": 60 }, "execution": { "type": "invalid" } }
    ]
}
JSON

    service_load "$TEST_DIR/bad-execution.json" 2>/dev/null
    local rc=$?

    assert_equals "1" "$rc" "service_load should return 1 for invalid execution type"
}

# =============================================================================
# service_get_* Tests
# =============================================================================

test_get_schedule_returns_config() {
    cat > "$TEST_DIR/services.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        {
            "id": "test-svc",
            "schedule": { "type": "interval", "interval": 300, "run_on_startup": true },
            "execution": { "type": "command", "command": "echo test" }
        }
    ]
}
JSON

    service_load "$TEST_DIR/services.json"

    local schedule
    schedule=$(service_get_schedule "test-svc")

    assert_output_contains "$schedule" "interval" "Schedule should contain type"
    assert_output_contains "$schedule" "300" "Schedule should contain interval"
    assert_output_contains "$schedule" "run_on_startup" "Schedule should contain run_on_startup"
}

test_get_execution_returns_config() {
    cat > "$TEST_DIR/services.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        {
            "id": "test-svc",
            "schedule": { "type": "interval", "interval": 60 },
            "execution": { "type": "function", "function": "my_func", "args": ["arg1", "arg2"] }
        }
    ]
}
JSON

    service_load "$TEST_DIR/services.json"

    local execution
    execution=$(service_get_execution "test-svc")

    assert_output_contains "$execution" "function" "Execution should contain type"
    assert_output_contains "$execution" "my_func" "Execution should contain function name"
    assert_output_contains "$execution" "arg1" "Execution should contain args"
}

test_get_interval() {
    cat > "$TEST_DIR/services.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        {
            "id": "test-svc",
            "schedule": { "type": "interval", "interval": 180 },
            "execution": { "type": "command", "command": "echo test" }
        }
    ]
}
JSON

    service_load "$TEST_DIR/services.json"

    local interval
    interval=$(service_get_interval "test-svc")

    assert_equals "180" "$interval" "Should return correct interval"
}

test_runs_on_startup_true() {
    cat > "$TEST_DIR/services.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        {
            "id": "startup-svc",
            "schedule": { "type": "interval", "interval": 60, "run_on_startup": true },
            "execution": { "type": "command", "command": "echo test" }
        }
    ]
}
JSON

    service_load "$TEST_DIR/services.json"

    service_runs_on_startup "startup-svc"
    local rc=$?

    assert_equals "0" "$rc" "Should return 0 for service with run_on_startup: true"
}

test_runs_on_startup_false() {
    cat > "$TEST_DIR/services.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        {
            "id": "no-startup-svc",
            "schedule": { "type": "interval", "interval": 60 },
            "execution": { "type": "command", "command": "echo test" }
        }
    ]
}
JSON

    service_load "$TEST_DIR/services.json"

    service_runs_on_startup "no-startup-svc"
    local rc=$?

    assert_equals "1" "$rc" "Should return 1 for service without run_on_startup"
}

test_get_enabled_services() {
    cat > "$TEST_DIR/services.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        { "id": "enabled-1", "enabled": true, "schedule": { "type": "interval", "interval": 60 }, "execution": { "type": "command", "command": "echo 1" } },
        { "id": "disabled-1", "enabled": false, "schedule": { "type": "interval", "interval": 60 }, "execution": { "type": "command", "command": "echo 2" } },
        { "id": "enabled-2", "schedule": { "type": "interval", "interval": 60 }, "execution": { "type": "command", "command": "echo 3" } }
    ]
}
JSON

    service_load "$TEST_DIR/services.json"

    local enabled
    enabled=$(service_get_enabled)

    assert_output_contains "$enabled" "enabled-1" "Should include enabled-1"
    assert_output_contains "$enabled" "enabled-2" "Should include enabled-2 (default enabled)"
    assert_output_not_contains "$enabled" "disabled-1" "Should not include disabled-1"
}

test_get_concurrency_config() {
    cat > "$TEST_DIR/services.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        {
            "id": "concurrent-svc",
            "schedule": { "type": "interval", "interval": 60 },
            "execution": { "type": "command", "command": "echo test" },
            "concurrency": { "max_instances": 2, "if_running": "queue" }
        }
    ]
}
JSON

    service_load "$TEST_DIR/services.json"

    local concurrency
    concurrency=$(service_get_concurrency "concurrent-svc")

    assert_output_contains "$concurrency" "max_instances" "Should contain max_instances"
    assert_output_contains "$concurrency" "2" "Should have max_instances: 2"
    assert_output_contains "$concurrency" "queue" "Should have if_running: queue"
}

test_get_default_concurrency() {
    cat > "$TEST_DIR/services.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        {
            "id": "simple-svc",
            "schedule": { "type": "interval", "interval": 60 },
            "execution": { "type": "command", "command": "echo test" }
        }
    ]
}
JSON

    service_load "$TEST_DIR/services.json"

    local concurrency
    concurrency=$(service_get_concurrency "simple-svc")

    assert_output_contains "$concurrency" "max_instances" "Should contain default max_instances"
    assert_output_contains "$concurrency" "skip" "Should have default if_running: skip"
}

test_get_timeout_with_default() {
    cat > "$TEST_DIR/services.json" << 'JSON'
{
    "version": "1.0",
    "defaults": { "timeout": 120 },
    "services": [
        {
            "id": "svc-with-timeout",
            "timeout": 600,
            "schedule": { "type": "interval", "interval": 60 },
            "execution": { "type": "command", "command": "echo test" }
        },
        {
            "id": "svc-without-timeout",
            "schedule": { "type": "interval", "interval": 60 },
            "execution": { "type": "command", "command": "echo test" }
        }
    ]
}
JSON

    service_load "$TEST_DIR/services.json"

    local timeout1 timeout2
    timeout1=$(service_get_timeout "svc-with-timeout")
    timeout2=$(service_get_timeout "svc-without-timeout")

    assert_equals "600" "$timeout1" "Should use service-specific timeout"
    assert_equals "120" "$timeout2" "Should use default timeout"
}

# =============================================================================
# service_load_override Tests
# =============================================================================

test_load_override_replaces_service() {
    cat > "$TEST_DIR/base.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        { "id": "svc-a", "schedule": { "type": "interval", "interval": 60 }, "execution": { "type": "command", "command": "echo base" } }
    ]
}
JSON

    cat > "$TEST_DIR/override.json" << 'JSON'
{
    "services": [
        { "id": "svc-a", "schedule": { "type": "interval", "interval": 120 }, "execution": { "type": "command", "command": "echo override" } }
    ]
}
JSON

    service_load "$TEST_DIR/base.json"
    service_load_override "$TEST_DIR/override.json"

    local interval
    interval=$(service_get_interval "svc-a")

    assert_equals "120" "$interval" "Override should replace base service interval"
}

test_load_override_adds_new_service() {
    cat > "$TEST_DIR/base.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        { "id": "svc-a", "schedule": { "type": "interval", "interval": 60 }, "execution": { "type": "command", "command": "echo a" } }
    ]
}
JSON

    cat > "$TEST_DIR/override.json" << 'JSON'
{
    "services": [
        { "id": "svc-b", "schedule": { "type": "interval", "interval": 120 }, "execution": { "type": "command", "command": "echo b" } }
    ]
}
JSON

    service_load "$TEST_DIR/base.json"
    service_load_override "$TEST_DIR/override.json"

    assert_equals "2" "$(service_count)" "Should have 2 services after override"

    service_exists "svc-a"
    local rc1=$?
    service_exists "svc-b"
    local rc2=$?

    assert_equals "0" "$rc1" "svc-a should exist"
    assert_equals "0" "$rc2" "svc-b should exist"
}

test_load_override_disables_service() {
    cat > "$TEST_DIR/base.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        { "id": "svc-a", "schedule": { "type": "interval", "interval": 60 }, "execution": { "type": "command", "command": "echo a" } },
        { "id": "svc-b", "schedule": { "type": "interval", "interval": 60 }, "execution": { "type": "command", "command": "echo b" } }
    ]
}
JSON

    cat > "$TEST_DIR/override.json" << 'JSON'
{
    "services": [
        { "id": "svc-a", "enabled": false, "schedule": { "type": "interval", "interval": 60 }, "execution": { "type": "command", "command": "echo a" } }
    ]
}
JSON

    service_load "$TEST_DIR/base.json"
    service_load_override "$TEST_DIR/override.json"

    local enabled
    enabled=$(service_get_enabled)

    assert_output_not_contains "$enabled" "svc-a" "svc-a should be disabled"
    assert_output_contains "$enabled" "svc-b" "svc-b should still be enabled"
}

# =============================================================================
# service_load_builtin_defaults Tests
# =============================================================================

test_builtin_defaults_loads_services() {
    service_load_builtin_defaults

    assert_equals "7" "$(service_count)" "Built-in defaults should have 7 services"
    assert_equals "1.0" "$(service_version)" "Built-in version should be 1.0"
}

test_builtin_defaults_has_expected_services() {
    service_load_builtin_defaults

    local enabled
    enabled=$(service_get_enabled)

    assert_output_contains "$enabled" "pr-sync" "Should have pr-sync service"
    assert_output_contains "$enabled" "pr-optimizer" "Should have pr-optimizer service"
    assert_output_contains "$enabled" "scheduler-tick" "Should have scheduler-tick service"
}

test_builtin_pr_sync_runs_on_startup() {
    service_load_builtin_defaults

    service_runs_on_startup "pr-sync"
    local rc=$?

    assert_equals "0" "$rc" "pr-sync should run on startup"
}

# =============================================================================
# service_exists Tests
# =============================================================================

test_service_exists_returns_true() {
    cat > "$TEST_DIR/services.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        { "id": "existing-svc", "schedule": { "type": "interval", "interval": 60 }, "execution": { "type": "command", "command": "echo test" } }
    ]
}
JSON

    service_load "$TEST_DIR/services.json"

    service_exists "existing-svc"
    local rc=$?

    assert_equals "0" "$rc" "Should return 0 for existing service"
}

test_service_exists_returns_false() {
    cat > "$TEST_DIR/services.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        { "id": "some-svc", "schedule": { "type": "interval", "interval": 60 }, "execution": { "type": "command", "command": "echo test" } }
    ]
}
JSON

    service_load "$TEST_DIR/services.json"

    service_exists "nonexistent-svc"
    local rc=$?

    assert_equals "1" "$rc" "Should return 1 for nonexistent service"
}

# =============================================================================
# Event Schedule Tests
# =============================================================================

test_load_event_schedule() {
    cat > "$TEST_DIR/services.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        {
            "id": "event-svc",
            "schedule": { "type": "event", "trigger": "worker.completed" },
            "execution": { "type": "function", "function": "handle_completion" }
        }
    ]
}
JSON

    service_load "$TEST_DIR/services.json"
    local rc=$?

    assert_equals "0" "$rc" "Should load event schedule"

    local schedule
    schedule=$(service_get_schedule "event-svc")

    assert_output_contains "$schedule" "event" "Schedule type should be event"
    assert_output_contains "$schedule" "worker.completed" "Should have trigger"
}

# =============================================================================
# Continuous Schedule Tests
# =============================================================================

test_load_continuous_schedule() {
    cat > "$TEST_DIR/services.json" << 'JSON'
{
    "version": "1.0",
    "services": [
        {
            "id": "continuous-svc",
            "schedule": { "type": "continuous", "restart_delay": 10 },
            "execution": { "type": "command", "command": "run-daemon" }
        }
    ]
}
JSON

    service_load "$TEST_DIR/services.json"
    local rc=$?

    assert_equals "0" "$rc" "Should load continuous schedule"

    local schedule
    schedule=$(service_get_schedule "continuous-svc")

    assert_output_contains "$schedule" "continuous" "Schedule type should be continuous"
    assert_output_contains "$schedule" "restart_delay" "Should have restart_delay"
}

# =============================================================================
# Run All Tests
# =============================================================================

# service_load - valid input
run_test test_load_valid_two_service_config
run_test test_load_gets_service_by_id

# service_load - error handling
run_test test_load_missing_file
run_test test_load_invalid_json
run_test test_load_empty_services_array
run_test test_load_duplicate_service_ids
run_test test_load_missing_service_id
run_test test_load_missing_schedule
run_test test_load_missing_execution
run_test test_load_invalid_schedule_type
run_test test_load_invalid_execution_type

# service_get_* tests
run_test test_get_schedule_returns_config
run_test test_get_execution_returns_config
run_test test_get_interval
run_test test_runs_on_startup_true
run_test test_runs_on_startup_false
run_test test_get_enabled_services
run_test test_get_concurrency_config
run_test test_get_default_concurrency
run_test test_get_timeout_with_default

# service_load_override tests
run_test test_load_override_replaces_service
run_test test_load_override_adds_new_service
run_test test_load_override_disables_service

# service_load_builtin_defaults tests
run_test test_builtin_defaults_loads_services
run_test test_builtin_defaults_has_expected_services
run_test test_builtin_pr_sync_runs_on_startup

# service_exists tests
run_test test_service_exists_returns_true
run_test test_service_exists_returns_false

# Schedule type tests
run_test test_load_event_schedule
run_test test_load_continuous_schedule

print_test_summary
exit_with_test_result
