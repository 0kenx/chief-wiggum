#!/usr/bin/env bash
# =============================================================================
# Markdown Agent Execution Integration Tests
#
# Tests the full execution flow of markdown agents with mock Claude:
# - agent_run wrapper correctly calls md_agent_run
# - Ralph loop mode actually invokes Claude
# - Once mode invokes Claude
# - Logs, summaries, and results are created
# - Valid results are extracted (not UNKNOWN)
# - Workspace override works correctly
# =============================================================================

set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"
source "$TESTS_DIR/mocks/mock-helpers.sh"

TEST_DIR=""
WORKER_DIR=""
PROJECT_DIR=""

# =============================================================================
# Setup / Teardown
# =============================================================================

setup() {
    TEST_DIR=$(mktemp -d)
    WORKER_DIR="$TEST_DIR/worker"
    PROJECT_DIR="$TEST_DIR/project"

    # Create worker structure
    mkdir -p "$WORKER_DIR"/{workspace,logs,results,reports,summaries,checkpoints}
    mkdir -p "$PROJECT_DIR"

    # Create required PRD file
    echo "# Test PRD" > "$WORKER_DIR/prd.md"

    # Setup mock Claude
    mock_setup
    export CLAUDE="$TESTS_DIR/mocks/mock-claude.sh"
    export MOCK_CLAUDE_DELAY="0"
    export LOG_FILE="$TEST_DIR/test.log"
    export LOG_LEVEL="DEBUG"

    # Ensure clean state - unset any previous agent state
    unset _MD_AGENT_FILE 2>/dev/null || true
    unset _AGENT_MD_LOADED 2>/dev/null || true
}

teardown() {
    mock_teardown
    rm -rf "$TEST_DIR"
}

# =============================================================================
# Test Fixtures
# =============================================================================

_create_ralph_loop_agent() {
    local agent_file="$TEST_DIR/ralph-agent.md"

    cat > "$agent_file" << 'EOF'
---
type: test.ralph-agent
description: Test ralph_loop mode agent
required_paths: [prd.md]
valid_results: [PASS, FAIL]
mode: ralph_loop
readonly: false
report_tag: report
result_tag: result
---

<WIGGUM_SYSTEM_PROMPT>
You are a test agent. Complete the task and output a result.
</WIGGUM_SYSTEM_PROMPT>

<WIGGUM_USER_PROMPT>
Complete the test task.

When done, output:
<result>PASS</result>
</WIGGUM_USER_PROMPT>

<WIGGUM_CONTINUATION_PROMPT>
Continue iteration {{iteration}}.
</WIGGUM_CONTINUATION_PROMPT>
EOF

    echo "$agent_file"
}

_create_once_agent() {
    local agent_file="$TEST_DIR/once-agent.md"

    cat > "$agent_file" << 'EOF'
---
type: test.once-agent
description: Test once mode agent
required_paths: [prd.md]
valid_results: [PASS, SKIP]
mode: once
readonly: false
---

<WIGGUM_SYSTEM_PROMPT>
You are a test agent running in once mode.
</WIGGUM_SYSTEM_PROMPT>

<WIGGUM_USER_PROMPT>
Run once and output:
<result>PASS</result>
</WIGGUM_USER_PROMPT>
EOF

    echo "$agent_file"
}

_create_workspace_override_agent() {
    local agent_file="$TEST_DIR/override-agent.md"

    cat > "$agent_file" << 'EOF'
---
type: test.override-agent
description: Test workspace_override
required_paths: [prd.md]
valid_results: [PASS]
mode: ralph_loop
readonly: true
workspace_override: project_dir
---

<WIGGUM_SYSTEM_PROMPT>
You are a test agent with workspace override.
WORKSPACE: {{workspace}}
PROJECT: {{project_dir}}
</WIGGUM_SYSTEM_PROMPT>

<WIGGUM_USER_PROMPT>
Run in project directory and output:
<result>PASS</result>
</WIGGUM_USER_PROMPT>

<WIGGUM_CONTINUATION_PROMPT>
Continue.
</WIGGUM_CONTINUATION_PROMPT>
EOF

    echo "$agent_file"
}

# =============================================================================
# Test: agent_run wrapper invokes md_agent_run correctly
# =============================================================================

test_agent_run_wrapper_calls_md_agent_run() {
    # Fresh source to ensure clean state
    unset _AGENT_MD_LOADED 2>/dev/null || true
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local agent_file
    agent_file=$(_create_ralph_loop_agent)

    # Initialize the agent (this defines agent_run)
    md_agent_init "$agent_file" "test.ralph-agent"

    # Verify _MD_AGENT_FILE is set
    if [ -n "$_MD_AGENT_FILE" ]; then
        assert_success "_MD_AGENT_FILE should be set after md_agent_init" true
    else
        assert_failure "_MD_AGENT_FILE should be set after md_agent_init" true
        return
    fi

    # Verify agent_run is defined
    if type agent_run &>/dev/null; then
        assert_success "agent_run should be defined after md_agent_init" true
    else
        assert_failure "agent_run should be defined after md_agent_init" true
    fi
}

# =============================================================================
# Test: Ralph loop agent invokes Claude
# =============================================================================

test_ralph_loop_agent_invokes_claude() {
    # Fresh source
    unset _AGENT_MD_LOADED 2>/dev/null || true
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local agent_file
    agent_file=$(_create_ralph_loop_agent)

    # Configure mock to return a PASS result
    export MOCK_CLAUDE_RESPONSE='Working on the task...

<result>PASS</result>

Task completed successfully.'

    # Initialize agent
    md_agent_init "$agent_file" "test.ralph-agent"

    # Set required environment for pipeline context
    export WIGGUM_STEP_ID="test-step"

    # Run the agent
    local exit_code=0
    agent_run "$WORKER_DIR" "$PROJECT_DIR" || exit_code=$?

    # Check that Claude was invoked at least once
    local invocation_count
    invocation_count=$(mock_get_invocation_count)

    if [ "$invocation_count" -gt 0 ]; then
        assert_success "Ralph loop agent should invoke Claude (invoked $invocation_count times)" true
    else
        assert_failure "Ralph loop agent should invoke Claude (invoked 0 times)" true
    fi

    unset WIGGUM_STEP_ID
}

# =============================================================================
# Test: Once mode agent invokes Claude
# =============================================================================

test_once_agent_invokes_claude() {
    # Fresh source
    unset _AGENT_MD_LOADED 2>/dev/null || true
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local agent_file
    agent_file=$(_create_once_agent)

    # Configure mock
    export MOCK_CLAUDE_RESPONSE='<result>PASS</result>'

    # Initialize agent
    md_agent_init "$agent_file" "test.once-agent"

    # Set required environment
    export WIGGUM_STEP_ID="once-test"

    # Run the agent
    local exit_code=0
    agent_run "$WORKER_DIR" "$PROJECT_DIR" || exit_code=$?

    # Check Claude was invoked exactly once
    local invocation_count
    invocation_count=$(mock_get_invocation_count)

    if [ "$invocation_count" -eq 1 ]; then
        assert_success "Once mode agent should invoke Claude exactly once" true
    else
        assert_failure "Once mode agent should invoke Claude exactly once (got $invocation_count)" true
    fi

    unset WIGGUM_STEP_ID
}

# =============================================================================
# Test: Logs are created during execution
# =============================================================================

test_agent_creates_logs() {
    # Fresh source
    unset _AGENT_MD_LOADED 2>/dev/null || true
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local agent_file
    agent_file=$(_create_ralph_loop_agent)

    export MOCK_CLAUDE_RESPONSE='<result>PASS</result>'
    export WIGGUM_STEP_ID="log-test"

    md_agent_init "$agent_file" "test.ralph-agent"
    agent_run "$WORKER_DIR" "$PROJECT_DIR" || true

    # Check that log files were created
    local log_count
    log_count=$(find "$WORKER_DIR/logs" -name "*.log" 2>/dev/null | wc -l)

    if [ "$log_count" -gt 0 ]; then
        assert_success "Agent should create log files (found $log_count)" true
    else
        assert_failure "Agent should create log files (found 0)" true
    fi

    unset WIGGUM_STEP_ID
}

# =============================================================================
# Test: Workspace override uses project_dir
# =============================================================================

test_workspace_override_uses_project_dir() {
    # Fresh source
    unset _AGENT_MD_LOADED 2>/dev/null || true
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local agent_file
    agent_file=$(_create_workspace_override_agent)

    export MOCK_CLAUDE_RESPONSE='<result>PASS</result>'
    export WIGGUM_STEP_ID="override-test"

    md_agent_init "$agent_file" "test.override-agent"

    # Capture the workspace that gets set
    agent_run "$WORKER_DIR" "$PROJECT_DIR" || true

    # Check that mock was invoked with project dir as working directory
    # The mock logs the --cwd argument
    local mock_args
    mock_args=$(mock_get_args 1 2>/dev/null || echo "")

    # The workspace_override=project_dir should cause Claude to run in PROJECT_DIR
    if echo "$mock_args" | grep -q "$PROJECT_DIR"; then
        assert_success "workspace_override should use project_dir" true
    else
        # This is expected to fail before the fix
        assert_failure "workspace_override should use project_dir (args: $mock_args)" true
    fi

    unset WIGGUM_STEP_ID
}

# =============================================================================
# Test: Result extraction works
# =============================================================================

test_result_extraction() {
    # Fresh source
    unset _AGENT_MD_LOADED 2>/dev/null || true
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local agent_file
    agent_file=$(_create_ralph_loop_agent)

    export MOCK_CLAUDE_RESPONSE='Completing the task...

<result>PASS</result>

Done!'
    export WIGGUM_STEP_ID="result-test"

    md_agent_init "$agent_file" "test.ralph-agent"
    agent_run "$WORKER_DIR" "$PROJECT_DIR" || true

    # Check that a result file was created
    local result_count
    result_count=$(find "$WORKER_DIR/results" -name "*.json" 2>/dev/null | wc -l)

    if [ "$result_count" -gt 0 ]; then
        # Check the result value - stored in outputs.gate_result
        local result_file
        result_file=$(find "$WORKER_DIR/results" -name "*.json" | head -1)
        local result_value
        result_value=$(jq -r '.outputs.gate_result // "UNKNOWN"' "$result_file" 2>/dev/null || echo "UNKNOWN")

        if [ "$result_value" = "PASS" ]; then
            assert_success "Result should be PASS (not UNKNOWN)" true
        else
            assert_failure "Result should be PASS, got: $result_value" true
        fi
    else
        assert_failure "Agent should create result file (found 0)" true
    fi

    unset WIGGUM_STEP_ID
}

# =============================================================================
# Test: Agent doesn't exit with code 1 before running
# =============================================================================

test_agent_runs_without_immediate_exit() {
    # Fresh source
    unset _AGENT_MD_LOADED 2>/dev/null || true
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local agent_file
    agent_file=$(_create_ralph_loop_agent)

    export MOCK_CLAUDE_RESPONSE='<result>PASS</result>'
    export WIGGUM_STEP_ID="exit-test"

    md_agent_init "$agent_file" "test.ralph-agent"

    # Run and capture exit code
    local exit_code=0
    agent_run "$WORKER_DIR" "$PROJECT_DIR" || exit_code=$?

    # Check invocation count - if 0, agent exited before running
    local invocation_count
    invocation_count=$(mock_get_invocation_count)

    if [ "$invocation_count" -eq 0 ]; then
        assert_failure "Agent should invoke Claude before exiting (exit_code=$exit_code, invocations=0)" true
    else
        assert_success "Agent invoked Claude $invocation_count times before exit" true
    fi

    # Also verify exit code is 0 for successful completion
    if [ "$exit_code" -eq 0 ]; then
        assert_success "Agent should exit with code 0 on successful PASS result" true
    else
        # Exit code 1 might indicate early exit bug
        assert_failure "Agent exited with code $exit_code (expected 0)" true
    fi

    unset WIGGUM_STEP_ID
}

# =============================================================================
# Test: md_agent_run is actually called (not just defined)
# =============================================================================

test_md_agent_run_is_executed() {
    # Fresh source
    unset _AGENT_MD_LOADED 2>/dev/null || true
    source "$WIGGUM_HOME/lib/core/agent-md.sh"

    local agent_file
    agent_file=$(_create_ralph_loop_agent)

    export MOCK_CLAUDE_RESPONSE='<result>PASS</result>'
    export WIGGUM_STEP_ID="exec-test"

    md_agent_init "$agent_file" "test.ralph-agent"

    # Capture stderr which includes debug logs
    local output
    output=$(agent_run "$WORKER_DIR" "$PROJECT_DIR" 2>&1) || true

    # Check for the debug log that indicates md_agent_run was entered
    if echo "$output" | grep -q "md_agent_run: starting\|Running markdown agent"; then
        assert_success "md_agent_run should be executed" true
    else
        # Also check if Claude was invoked (alternative success indicator)
        local invocation_count
        invocation_count=$(mock_get_invocation_count)
        if [ "$invocation_count" -gt 0 ]; then
            assert_success "md_agent_run executed (Claude invoked $invocation_count times)" true
        else
            assert_failure "md_agent_run should be executed (no debug logs, no Claude invocations)" true
        fi
    fi

    unset WIGGUM_STEP_ID
}

# =============================================================================
# Test: Full pipeline step simulation
# =============================================================================

test_full_pipeline_step_with_md_agent() {
    # Fresh source
    unset _AGENT_MD_LOADED 2>/dev/null || true
    source "$WIGGUM_HOME/lib/core/agent-md.sh"
    source "$WIGGUM_HOME/lib/worker/agent-registry.sh"

    local agent_file
    agent_file=$(_create_ralph_loop_agent)

    export MOCK_CLAUDE_RESPONSE='Analysis complete.

<report>
## Test Report
All tests passed.
</report>

<result>PASS</result>'
    export WIGGUM_STEP_ID="pipeline-test"

    # Copy agent to proper location for registry to find
    mkdir -p "$WIGGUM_HOME/lib/agents/test"
    cp "$agent_file" "$WIGGUM_HOME/lib/agents/test/pipeline-agent.md"

    # Use load_agent like the real pipeline does
    if load_agent "test.pipeline-agent"; then
        # Run agent_run as pipeline runner would
        local exit_code=0
        agent_run "$WORKER_DIR" "$PROJECT_DIR" || exit_code=$?

        # Verify Claude was invoked
        local invocation_count
        invocation_count=$(mock_get_invocation_count)

        if [ "$invocation_count" -gt 0 ]; then
            assert_success "Pipeline step should invoke Claude" true
        else
            assert_failure "Pipeline step should invoke Claude (0 invocations, exit=$exit_code)" true
        fi
    else
        assert_failure "load_agent should succeed for test.pipeline-agent" true
    fi

    # Cleanup
    rm -rf "$WIGGUM_HOME/lib/agents/test"
    unset WIGGUM_STEP_ID
}

# =============================================================================
# Run all tests
# =============================================================================

run_test test_agent_run_wrapper_calls_md_agent_run
run_test test_ralph_loop_agent_invokes_claude
run_test test_once_agent_invokes_claude
run_test test_agent_creates_logs
run_test test_workspace_override_uses_project_dir
run_test test_result_extraction
run_test test_agent_runs_without_immediate_exit
run_test test_md_agent_run_is_executed
run_test test_full_pipeline_step_with_md_agent

print_test_summary
exit_with_test_result
