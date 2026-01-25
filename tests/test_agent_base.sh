#!/usr/bin/env bash
# Test suite for agent architecture improvements
# Tests: agent-base.sh, exit-codes.sh, agents.json config, communication protocol

set -euo pipefail

# Get the script directory and project root
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Source the test framework
source "$SCRIPT_DIR/test-framework.sh"

# Setup WIGGUM_HOME for tests
export WIGGUM_HOME="$PROJECT_ROOT"

# =============================================================================
# Test: Exit Codes
# =============================================================================

test_exit_codes_are_defined() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"

    assert_equals "56" "$EXIT_AGENT_INIT_FAILED" "EXIT_AGENT_INIT_FAILED should be 56"
    assert_equals "57" "$EXIT_AGENT_PREREQ_FAILED" "EXIT_AGENT_PREREQ_FAILED should be 57"
    assert_equals "58" "$EXIT_AGENT_READY_FAILED" "EXIT_AGENT_READY_FAILED should be 58"
    assert_equals "59" "$EXIT_AGENT_OUTPUT_MISSING" "EXIT_AGENT_OUTPUT_MISSING should be 59"
    assert_equals "60" "$EXIT_AGENT_VALIDATION_FAILED" "EXIT_AGENT_VALIDATION_FAILED should be 60"
    assert_equals "61" "$EXIT_AGENT_VIOLATION" "EXIT_AGENT_VIOLATION should be 61"
    assert_equals "62" "$EXIT_AGENT_TIMEOUT" "EXIT_AGENT_TIMEOUT should be 62"
    assert_equals "63" "$EXIT_AGENT_MAX_ITERATIONS" "EXIT_AGENT_MAX_ITERATIONS should be 63"
}

test_exit_codes_under_64() {
    source "$WIGGUM_HOME/lib/core/exit-codes.sh"

    local codes=(
        "$EXIT_AGENT_INIT_FAILED"
        "$EXIT_AGENT_PREREQ_FAILED"
        "$EXIT_AGENT_READY_FAILED"
        "$EXIT_AGENT_OUTPUT_MISSING"
        "$EXIT_AGENT_VALIDATION_FAILED"
        "$EXIT_AGENT_VIOLATION"
        "$EXIT_AGENT_TIMEOUT"
        "$EXIT_AGENT_MAX_ITERATIONS"
    )

    for code in "${codes[@]}"; do
        if [ "$code" -lt 64 ]; then
            assert_success "Exit code $code is under 64" true
        else
            assert_failure "Exit code $code should be under 64" true
        fi
    done
}

# =============================================================================
# Test: Agent Metadata
# =============================================================================

test_agent_init_metadata() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    agent_init_metadata "test-agent" "Test description for agent"

    assert_equals "test-agent" "$AGENT_TYPE" "AGENT_TYPE should be set"
    assert_equals "Test description for agent" "$AGENT_DESCRIPTION" "AGENT_DESCRIPTION should be set"
}

# =============================================================================
# Test: Agent Context
# =============================================================================

test_agent_setup_context() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    agent_setup_context "/tmp/worker-dir" "/tmp/workspace" "/tmp/project" "TASK-001"

    assert_equals "/tmp/worker-dir" "$(agent_get_worker_dir)" "worker_dir should be set"
    assert_equals "/tmp/workspace" "$(agent_get_workspace)" "workspace should be set"
    assert_equals "/tmp/project" "$(agent_get_project_dir)" "project_dir should be set"
    assert_equals "TASK-001" "$(agent_get_task_id)" "task_id should be set"
}

# =============================================================================
# Test: Config Loading (uses test fixture to decouple from real config)
# =============================================================================

# Helper: set up isolated config environment using test fixture
_setup_config_fixture() {
    local fixture_home
    fixture_home=$(mktemp -d)
    mkdir -p "$fixture_home/config"
    cp "$SCRIPT_DIR/fixtures/test-agents.json" "$fixture_home/config/agents.json"
    # Copy lib so agent-base.sh can be sourced from fixture home
    ln -s "$PROJECT_ROOT/lib" "$fixture_home/lib"
    echo "$fixture_home"
}

test_config_loading_task_worker() {
    local fixture_home
    fixture_home=$(_setup_config_fixture)
    WIGGUM_HOME="$fixture_home" source "$fixture_home/lib/core/agent-base.sh"

    WIGGUM_HOME="$fixture_home" load_agent_config "system.task-worker"

    assert_equals "20" "$AGENT_CONFIG_MAX_ITERATIONS" "system.task-worker max_iterations should be 20"
    assert_equals "50" "$AGENT_CONFIG_MAX_TURNS" "system.task-worker max_turns should be 50"
    assert_equals "3600" "$AGENT_CONFIG_TIMEOUT_SECONDS" "system.task-worker timeout_seconds should be 3600"
    rm -rf "$fixture_home"
}

test_config_loading_pr_comment_fix() {
    local fixture_home
    fixture_home=$(_setup_config_fixture)
    WIGGUM_HOME="$fixture_home" source "$fixture_home/lib/core/agent-base.sh"

    WIGGUM_HOME="$fixture_home" load_agent_config "engineering.pr-comment-fix"

    assert_equals "10" "$AGENT_CONFIG_MAX_ITERATIONS" "engineering.pr-comment-fix max_iterations should be 10"
    assert_equals "30" "$AGENT_CONFIG_MAX_TURNS" "engineering.pr-comment-fix max_turns should be 30"
    assert_equals "true" "$AGENT_CONFIG_AUTO_COMMIT" "engineering.pr-comment-fix auto_commit should be true"
    rm -rf "$fixture_home"
}

test_config_loading_validation_review() {
    local fixture_home
    fixture_home=$(_setup_config_fixture)
    WIGGUM_HOME="$fixture_home" source "$fixture_home/lib/core/agent-base.sh"

    WIGGUM_HOME="$fixture_home" load_agent_config "engineering.validation-review"

    assert_equals "5" "$AGENT_CONFIG_MAX_ITERATIONS" "engineering.validation-review max_iterations should be 5"
    assert_equals "50" "$AGENT_CONFIG_MAX_TURNS" "engineering.validation-review max_turns should be 50"
    rm -rf "$fixture_home"
}

test_config_loading_unknown_agent_uses_defaults() {
    local fixture_home
    fixture_home=$(_setup_config_fixture)
    WIGGUM_HOME="$fixture_home" source "$fixture_home/lib/core/agent-base.sh"

    WIGGUM_HOME="$fixture_home" load_agent_config "unknown-agent-type"

    assert_equals "10" "$AGENT_CONFIG_MAX_ITERATIONS" "unknown agent should use default max_iterations"
    assert_equals "30" "$AGENT_CONFIG_MAX_TURNS" "unknown agent should use default max_turns"
    rm -rf "$fixture_home"
}

# =============================================================================
# Test: Communication Protocol - Paths
# =============================================================================

test_agent_comm_path_prd() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local path
    path=$(agent_comm_path "/tmp/worker" "prd")
    assert_equals "/tmp/worker/prd.md" "$path" "prd path should be correct"
}

test_agent_comm_path_workspace() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local path
    path=$(agent_comm_path "/tmp/worker" "workspace")
    assert_equals "/tmp/worker/workspace" "$path" "workspace path should be correct"
}

test_agent_comm_path_summary() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local path
    path=$(agent_comm_path "/tmp/worker" "summary")
    assert_equals "/tmp/worker/summaries/summary.txt" "$path" "summary path should be correct"
}

# =============================================================================
# Test: Structured Agent Results (Epoch-Named)
# =============================================================================

test_agent_write_result_creates_epoch_file() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    mkdir -p "$tmpdir/logs"

    agent_init_metadata "test-agent" "Test"
    agent_setup_context "$tmpdir" "$tmpdir/workspace" "/tmp/project" "TEST-001"

    agent_write_result "$tmpdir" "success" 0 '{}' '[]' '{}'

    # Should create epoch-named file in results/
    local result_file
    result_file=$(ls "$tmpdir/results/"*"-test-agent-result.json" 2>/dev/null | head -1)
    if [ -n "$result_file" ] && [ -f "$result_file" ]; then
        assert_success "epoch-named result file should be created in results/" true
    else
        assert_failure "epoch-named result file should be created in results/" true
    fi

    rm -rf "$tmpdir"
}

test_agent_write_result_valid_json() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    mkdir -p "$tmpdir/logs"

    agent_init_metadata "test-agent" "Test"
    agent_setup_context "$tmpdir" "$tmpdir/workspace" "/tmp/project" "TEST-001"

    agent_write_result "$tmpdir" "success" 0 '{}' '[]' '{}'

    local result_file
    result_file=$(agent_find_latest_result "$tmpdir" "test-agent")

    if [ -n "$result_file" ] && jq '.' "$result_file" > /dev/null 2>&1; then
        assert_success "result file should be valid JSON" true
    else
        assert_failure "result file should be valid JSON" true
    fi

    rm -rf "$tmpdir"
}

test_agent_read_result_status() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    mkdir -p "$tmpdir/logs"

    agent_init_metadata "test-agent" "Test"
    agent_setup_context "$tmpdir" "$tmpdir/workspace" "/tmp/project" "TEST-001"

    agent_write_result "$tmpdir" "success" 0 '{}' '[]' '{}'

    local status
    status=$(agent_read_result "$tmpdir" ".status")

    assert_equals "success" "$status" "Should read back status as success"

    rm -rf "$tmpdir"
}

test_agent_result_is_success() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    mkdir -p "$tmpdir/logs"

    agent_init_metadata "test-agent" "Test"
    agent_setup_context "$tmpdir" "$tmpdir/workspace" "/tmp/project" "TEST-001"

    agent_write_result "$tmpdir" "success" 0 '{}' '[]' '{}'

    if agent_result_is_success "$tmpdir"; then
        assert_success "agent_result_is_success should return true for success" true
    else
        assert_failure "agent_result_is_success should return true for success" true
    fi

    rm -rf "$tmpdir"
}

test_agent_result_is_success_failure() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    mkdir -p "$tmpdir/logs"

    agent_init_metadata "test-agent" "Test"
    agent_setup_context "$tmpdir" "$tmpdir/workspace" "/tmp/project" "TEST-001"

    agent_write_result "$tmpdir" "failure" 1 '{}' '[]' '{}'

    if agent_result_is_success "$tmpdir"; then
        assert_failure "agent_result_is_success should return false for failure" true
    else
        assert_success "agent_result_is_success should return false for failure" true
    fi

    rm -rf "$tmpdir"
}

test_agent_get_output() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    mkdir -p "$tmpdir/logs"

    agent_init_metadata "test-agent" "Test"
    agent_setup_context "$tmpdir" "$tmpdir/workspace" "/tmp/project" "TEST-001"

    local outputs='{"pr_url":"https://github.com/test/pr/123","branch":"feature/test"}'
    agent_write_result "$tmpdir" "success" 0 "$outputs" '[]' '{}'

    local pr_url
    pr_url=$(agent_get_output "$tmpdir" "pr_url")

    assert_equals "https://github.com/test/pr/123" "$pr_url" "Should read pr_url from outputs"

    rm -rf "$tmpdir"
}

# =============================================================================
# Test: Epoch-Named Result/Report Helpers
# =============================================================================

test_agent_find_latest_result() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    mkdir -p "$tmpdir/results"

    # Create two result files with different epochs
    echo '{"status":"old"}' > "$tmpdir/results/1000-engineering.security-audit-result.json"
    sleep 0.1
    echo '{"status":"new"}' > "$tmpdir/results/2000-engineering.security-audit-result.json"

    local found
    found=$(agent_find_latest_result "$tmpdir" "engineering.security-audit")

    assert_equals "$tmpdir/results/2000-engineering.security-audit-result.json" "$found" \
        "Should find the latest (most recent) result file"

    rm -rf "$tmpdir"
}

test_agent_find_latest_result_not_found() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    mkdir -p "$tmpdir/results"

    local found
    found=$(agent_find_latest_result "$tmpdir" "nonexistent-agent")

    assert_equals "" "$found" "Should return empty for nonexistent agent"

    rm -rf "$tmpdir"
}

test_agent_find_latest_report() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    mkdir -p "$tmpdir/reports"

    echo "old report" > "$tmpdir/reports/1000-engineering.security-audit-report.md"
    sleep 0.1
    echo "new report" > "$tmpdir/reports/2000-engineering.security-audit-report.md"

    local found
    found=$(agent_find_latest_report "$tmpdir" "engineering.security-audit")

    assert_equals "$tmpdir/reports/2000-engineering.security-audit-report.md" "$found" \
        "Should find the latest report file"

    rm -rf "$tmpdir"
}

test_agent_write_report() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local tmpdir
    tmpdir=$(mktemp -d)

    agent_init_metadata "test-agent" "Test"
    agent_setup_context "$tmpdir" "$tmpdir/workspace" "/tmp/project" "TEST-001"

    local report_path
    report_path=$(agent_write_report "$tmpdir" "# Test Report\n\nSome content")

    if [ -f "$report_path" ]; then
        assert_success "Report file should be created" true
    else
        assert_failure "Report file should be created" true
    fi

    # Verify it's in reports/ with epoch naming
    if echo "$report_path" | grep -q "reports/.*-test-agent-report.md"; then
        assert_success "Report should have epoch-named path" true
    else
        assert_failure "Report should have epoch-named path" true
    fi

    rm -rf "$tmpdir"
}

test_agent_read_subagent_result() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    mkdir -p "$tmpdir/results"

    # Create a result file for engineering.security-audit with gate_result
    echo '{"outputs":{"gate_result":"PASS"}}' > "$tmpdir/results/1234-engineering.security-audit-result.json"

    local result
    result=$(agent_read_subagent_result "$tmpdir" "engineering.security-audit")

    assert_equals "PASS" "$result" "Should read gate_result from sub-agent result"

    rm -rf "$tmpdir"
}

test_agent_read_subagent_result_unknown() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local tmpdir
    tmpdir=$(mktemp -d)
    mkdir -p "$tmpdir/results"

    local result
    result=$(agent_read_subagent_result "$tmpdir" "nonexistent-agent")

    assert_equals "UNKNOWN" "$result" "Should return UNKNOWN for missing agent result"

    rm -rf "$tmpdir"
}

# =============================================================================
# Test: Utility Functions
# =============================================================================

test_agent_create_directories() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    local tmpdir
    tmpdir=$(mktemp -d)

    agent_create_directories "$tmpdir"

    assert_dir_exists "$tmpdir/logs" "logs directory should be created"
    assert_dir_exists "$tmpdir/summaries" "summaries directory should be created"

    rm -rf "$tmpdir"
}

# =============================================================================
# Test: Lifecycle Hooks (default implementations)
# =============================================================================

test_default_hooks_return_success() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    if agent_on_init "/tmp/worker" "/tmp/project"; then
        assert_success "agent_on_init should return 0 by default" true
    else
        assert_failure "agent_on_init should return 0 by default" true
    fi

    if agent_on_ready "/tmp/worker" "/tmp/project"; then
        assert_success "agent_on_ready should return 0 by default" true
    else
        assert_failure "agent_on_ready should return 0 by default" true
    fi

    if agent_on_error "/tmp/worker" 1 "prereq"; then
        assert_success "agent_on_error should return 0 by default" true
    else
        assert_failure "agent_on_error should return 0 by default" true
    fi

    if agent_on_signal "INT"; then
        assert_success "agent_on_signal should return 0 by default" true
    else
        assert_failure "agent_on_signal should return 0 by default" true
    fi
}

# =============================================================================
# Test: JSON Config File Validity
# =============================================================================

test_agents_json_is_valid() {
    if jq '.' "$WIGGUM_HOME/config/agents.json" > /dev/null 2>&1; then
        assert_success "config/agents.json should be valid JSON" true
    else
        assert_failure "config/agents.json should be valid JSON" true
    fi
}

test_agents_json_has_required_agents() {
    local agents
    agents=$(jq -r '.agents | keys[]' "$WIGGUM_HOME/config/agents.json" 2>/dev/null | sort | tr '\n' ',')

    assert_output_contains "$agents" "system.task-worker" "agents.json should have system.task-worker"
    assert_output_contains "$agents" "engineering.pr-comment-fix" "agents.json should have engineering.pr-comment-fix"
    assert_output_contains "$agents" "engineering.validation-review" "agents.json should have engineering.validation-review"
}

test_agents_json_has_defaults() {
    local has_defaults
    has_defaults=$(jq 'has("defaults")' "$WIGGUM_HOME/config/agents.json" 2>/dev/null)

    assert_equals "true" "$has_defaults" "agents.json should have defaults section"
}

# =============================================================================
# Test: Shell Script Syntax
# =============================================================================

test_agent_base_sh_syntax() {
    if bash -n "$WIGGUM_HOME/lib/core/agent-base.sh" 2>/dev/null; then
        assert_success "agent-base.sh should have valid bash syntax" true
    else
        assert_failure "agent-base.sh should have valid bash syntax" true
    fi
}

test_exit_codes_sh_syntax() {
    if bash -n "$WIGGUM_HOME/lib/core/exit-codes.sh" 2>/dev/null; then
        assert_success "exit-codes.sh should have valid bash syntax" true
    else
        assert_failure "exit-codes.sh should have valid bash syntax" true
    fi
}

test_agent_registry_sh_syntax() {
    if bash -n "$WIGGUM_HOME/lib/worker/agent-registry.sh" 2>/dev/null; then
        assert_success "agent-registry.sh should have valid bash syntax" true
    else
        assert_failure "agent-registry.sh should have valid bash syntax" true
    fi
}

test_task_worker_sh_syntax() {
    if bash -n "$WIGGUM_HOME/lib/agents/system/task-worker.sh" 2>/dev/null; then
        assert_success "system/task-worker.sh should have valid bash syntax" true
    else
        assert_failure "system/task-worker.sh should have valid bash syntax" true
    fi
}

test_pr_comment_fix_sh_syntax() {
    if bash -n "$WIGGUM_HOME/lib/agents/engineering/pr-comment-fix.sh" 2>/dev/null; then
        assert_success "engineering/pr-comment-fix.sh should have valid bash syntax" true
    else
        assert_failure "engineering/pr-comment-fix.sh should have valid bash syntax" true
    fi
}

test_validation_review_md_exists() {
    assert_file_exists "$WIGGUM_HOME/lib/agents/engineering/validation-review.md" "validation-review.md should exist"
}

test_task_executor_sh_syntax() {
    if bash -n "$WIGGUM_HOME/lib/agents/system/task-executor.sh" 2>/dev/null; then
        assert_success "system/task-executor.sh should have valid bash syntax" true
    else
        assert_failure "system/task-executor.sh should have valid bash syntax" true
    fi
}

test_task_summarizer_md_exists() {
    assert_file_exists "$WIGGUM_HOME/lib/agents/general/task-summarizer.md" "task-summarizer.md should exist"
}

test_agents_json_has_new_agents() {
    local agents
    agents=$(jq -r '.agents | keys[]' "$WIGGUM_HOME/config/agents.json" 2>/dev/null | sort | tr '\n' ',')

    assert_output_contains "$agents" "system.task-executor" "agents.json should have system.task-executor"
    assert_output_contains "$agents" "general.task-summarizer" "agents.json should have general.task-summarizer"
}

# =============================================================================
# Run Tests
# =============================================================================

run_test test_exit_codes_are_defined
run_test test_exit_codes_under_64
run_test test_agent_init_metadata
run_test test_agent_setup_context
run_test test_config_loading_task_worker
run_test test_config_loading_pr_comment_fix
run_test test_config_loading_validation_review
run_test test_config_loading_unknown_agent_uses_defaults
run_test test_agent_comm_path_prd
run_test test_agent_comm_path_workspace
run_test test_agent_comm_path_summary
run_test test_agent_write_result_creates_epoch_file
run_test test_agent_write_result_valid_json
run_test test_agent_read_result_status
run_test test_agent_result_is_success
run_test test_agent_result_is_success_failure
run_test test_agent_get_output
run_test test_agent_find_latest_result
run_test test_agent_find_latest_result_not_found
run_test test_agent_find_latest_report
run_test test_agent_write_report
run_test test_agent_read_subagent_result
run_test test_agent_read_subagent_result_unknown
run_test test_agent_create_directories
run_test test_default_hooks_return_success
run_test test_agents_json_is_valid
run_test test_agents_json_has_required_agents
run_test test_agents_json_has_defaults
run_test test_agent_base_sh_syntax
run_test test_exit_codes_sh_syntax
run_test test_agent_registry_sh_syntax
run_test test_task_worker_sh_syntax
run_test test_pr_comment_fix_sh_syntax
run_test test_validation_review_md_exists
run_test test_task_executor_sh_syntax
run_test test_task_summarizer_md_exists
run_test test_agents_json_has_new_agents

# Print summary
print_test_summary
exit_with_test_result
