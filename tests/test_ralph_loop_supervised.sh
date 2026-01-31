#!/usr/bin/env bash
# Test suite for ralph loop supervisor functionality
# Tests: extraction helpers, config loading, syntax validation
# Note: Supervisor functionality is now in the unified runtime-loop.sh

set -euo pipefail

# Get the script directory and project root
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# Source the test framework
source "$SCRIPT_DIR/test-framework.sh"

# Setup WIGGUM_HOME for tests
export WIGGUM_HOME="$PROJECT_ROOT"

# Temporary directory for test files
TEST_TMP_DIR=""

# =============================================================================
# Setup and Teardown
# =============================================================================

setup() {
    TEST_TMP_DIR=$(mktemp -d)
}

teardown() {
    if [ -n "$TEST_TMP_DIR" ] && [ -d "$TEST_TMP_DIR" ]; then
        rm -rf "$TEST_TMP_DIR"
    fi
}

# =============================================================================
# Test: Bash Syntax Validation
# =============================================================================

test_ralph_loop_sh_syntax() {
    if bash -n "$WIGGUM_HOME/lib/runtime/runtime-loop.sh" 2>/dev/null; then
        assert_success "runtime-loop.sh should have valid bash syntax" true
    else
        assert_failure "runtime-loop.sh should have valid bash syntax" true
    fi
}

# =============================================================================
# Test: Extraction Helper - _extract_supervisor_decision
# =============================================================================

test_extract_supervisor_decision_continue() {
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
    source "$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    echo "<decision>CONTINUE</decision>" > "$TEST_TMP_DIR/test.log"
    local result
    result=$(_extract_supervisor_decision "$TEST_TMP_DIR/test.log")

    assert_equals "CONTINUE" "$result" "Should extract CONTINUE decision"
}

test_extract_supervisor_decision_stop() {
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
    source "$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    echo "<decision>STOP</decision>" > "$TEST_TMP_DIR/test.log"
    local result
    result=$(_extract_supervisor_decision "$TEST_TMP_DIR/test.log")

    assert_equals "STOP" "$result" "Should extract STOP decision"
}

test_extract_supervisor_decision_restart() {
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
    source "$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    echo "<decision>RESTART</decision>" > "$TEST_TMP_DIR/test.log"
    local result
    result=$(_extract_supervisor_decision "$TEST_TMP_DIR/test.log")

    assert_equals "RESTART" "$result" "Should extract RESTART decision"
}

test_extract_supervisor_decision_missing_defaults_to_continue() {
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
    source "$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    echo "No decision tag here" > "$TEST_TMP_DIR/test.log"
    local result
    result=$(_extract_supervisor_decision "$TEST_TMP_DIR/test.log")

    assert_equals "CONTINUE" "$result" "Missing decision should default to CONTINUE"
}

test_extract_supervisor_decision_invalid_defaults_to_continue() {
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
    source "$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    echo "<decision>INVALID</decision>" > "$TEST_TMP_DIR/test.log"
    local result
    result=$(_extract_supervisor_decision "$TEST_TMP_DIR/test.log")

    assert_equals "CONTINUE" "$result" "Invalid decision should default to CONTINUE"
}

test_extract_supervisor_decision_embedded_in_content() {
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
    source "$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    cat > "$TEST_TMP_DIR/test.log" << 'EOF'
{"type":"assistant","message":{"content":[{"type":"text","text":"Let me review..."}]}}
Some other content here
<review>Review content</review>
<decision>STOP</decision>
<guidance>Some guidance</guidance>
EOF
    local result
    result=$(_extract_supervisor_decision "$TEST_TMP_DIR/test.log")

    assert_equals "STOP" "$result" "Should extract decision from mixed content"
}

# =============================================================================
# Test: Extraction Helper - _extract_supervisor_review
# =============================================================================

test_extract_supervisor_review_success() {
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
    source "$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    cat > "$TEST_TMP_DIR/test.log" << 'EOF'
<review>
## Progress Assessment
Good progress on implementation.

## Quality Check
All tests passing.
</review>
EOF

    _extract_supervisor_review "$TEST_TMP_DIR/test.log" "$TEST_TMP_DIR/review.md"

    assert_file_exists "$TEST_TMP_DIR/review.md" "Review file should be created"
    assert_file_contains "$TEST_TMP_DIR/review.md" "Progress Assessment" "Review should contain content"
    assert_file_contains "$TEST_TMP_DIR/review.md" "Quality Check" "Review should contain all sections"
}

test_extract_supervisor_review_missing_tag() {
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
    source "$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    echo "No review tag here" > "$TEST_TMP_DIR/test.log"

    if _extract_supervisor_review "$TEST_TMP_DIR/test.log" "$TEST_TMP_DIR/review.md" 2>/dev/null; then
        assert_failure "Should return failure when no review tag" true
    else
        assert_success "Should return failure when no review tag" true
    fi
}

test_extract_supervisor_review_strips_tags() {
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
    source "$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    cat > "$TEST_TMP_DIR/test.log" << 'EOF'
<review>
Content here
</review>
EOF

    _extract_supervisor_review "$TEST_TMP_DIR/test.log" "$TEST_TMP_DIR/review.md"

    assert_file_not_contains "$TEST_TMP_DIR/review.md" "<review>" "Should not contain opening tag"
    assert_file_not_contains "$TEST_TMP_DIR/review.md" "</review>" "Should not contain closing tag"
}

# =============================================================================
# Test: Extraction Helper - _extract_supervisor_guidance
# =============================================================================

test_extract_supervisor_guidance_success() {
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
    source "$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    cat > "$TEST_TMP_DIR/test.log" << 'EOF'
<guidance>
Focus on edge cases in the next iteration.
Consider adding error handling for network failures.
</guidance>
EOF

    _extract_supervisor_guidance "$TEST_TMP_DIR/test.log" "$TEST_TMP_DIR/guidance.md"

    assert_file_exists "$TEST_TMP_DIR/guidance.md" "Guidance file should be created"
    assert_file_contains "$TEST_TMP_DIR/guidance.md" "edge cases" "Guidance should contain content"
}

test_extract_supervisor_guidance_missing_tag() {
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
    source "$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    echo "No guidance tag here" > "$TEST_TMP_DIR/test.log"

    if _extract_supervisor_guidance "$TEST_TMP_DIR/test.log" "$TEST_TMP_DIR/guidance.md" 2>/dev/null; then
        assert_failure "Should return failure when no guidance tag" true
    else
        assert_success "Should return failure when no guidance tag" true
    fi
}

test_extract_supervisor_guidance_strips_tags() {
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
    source "$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    cat > "$TEST_TMP_DIR/test.log" << 'EOF'
<guidance>
Guidance content
</guidance>
EOF

    _extract_supervisor_guidance "$TEST_TMP_DIR/test.log" "$TEST_TMP_DIR/guidance.md"

    assert_file_not_contains "$TEST_TMP_DIR/guidance.md" "<guidance>" "Should not contain opening tag"
    assert_file_not_contains "$TEST_TMP_DIR/guidance.md" "</guidance>" "Should not contain closing tag"
}

# =============================================================================
# Test: Full Extraction Workflow
# =============================================================================

test_extract_all_supervisor_outputs() {
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
    source "$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    # Create a realistic supervisor log
    cat > "$TEST_TMP_DIR/supervisor.log" << 'EOF'
{"type":"assistant","message":{"content":[{"type":"text","text":"Let me review the progress..."}]}}

<review>
## Progress Assessment

The implementation is 80% complete. Core functionality works.

## Quality Check

Tests are passing. Code follows project patterns.

## Decision Rationale

Work is on track, should continue with remaining tasks.
</review>

<decision>CONTINUE</decision>

<guidance>
Focus on completing the remaining edge case handling.
Add tests for the error scenarios discussed.
</guidance>
EOF

    # Extract all components
    local decision
    decision=$(_extract_supervisor_decision "$TEST_TMP_DIR/supervisor.log")
    _extract_supervisor_review "$TEST_TMP_DIR/supervisor.log" "$TEST_TMP_DIR/review.md"
    _extract_supervisor_guidance "$TEST_TMP_DIR/supervisor.log" "$TEST_TMP_DIR/guidance.md"

    assert_equals "CONTINUE" "$decision" "Decision should be CONTINUE"
    assert_file_contains "$TEST_TMP_DIR/review.md" "80% complete" "Review should contain progress"
    assert_file_contains "$TEST_TMP_DIR/guidance.md" "edge case" "Guidance should contain next steps"
}

# =============================================================================
# Test: Config Loading for Supervisor Settings
# =============================================================================

test_config_loading_supervisor_interval_default() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    load_agent_config "unknown-agent-type"

    assert_equals "2" "$AGENT_CONFIG_SUPERVISOR_INTERVAL" "Default supervisor_interval should be 2"
}

test_config_loading_max_restarts_default() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    load_agent_config "unknown-agent-type"

    assert_equals "2" "$AGENT_CONFIG_MAX_RESTARTS" "Default max_restarts should be 2"
}

test_config_loading_supervisor_settings_from_json() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    # Verify the values come from config file defaults
    load_agent_config "system.task-worker"

    # These should get the defaults from agents.json since system.task-worker doesn't override them
    assert_equals "2" "$AGENT_CONFIG_SUPERVISOR_INTERVAL" "supervisor_interval from defaults"
    assert_equals "2" "$AGENT_CONFIG_MAX_RESTARTS" "max_restarts from defaults"
}

# =============================================================================
# Test: agents.json has supervisor settings
# =============================================================================

test_agents_json_has_supervisor_interval() {
    local has_supervisor_interval
    has_supervisor_interval=$(jq '.defaults | has("supervisor_interval")' "$WIGGUM_HOME/config/agents.json" 2>/dev/null)

    assert_equals "true" "$has_supervisor_interval" "agents.json defaults should have supervisor_interval"
}

test_agents_json_has_max_restarts() {
    local has_max_restarts
    has_max_restarts=$(jq '.defaults | has("max_restarts")' "$WIGGUM_HOME/config/agents.json" 2>/dev/null)

    assert_equals "true" "$has_max_restarts" "agents.json defaults should have max_restarts"
}

test_agents_json_supervisor_interval_value() {
    local value
    value=$(jq '.defaults.supervisor_interval' "$WIGGUM_HOME/config/agents.json" 2>/dev/null)

    assert_equals "2" "$value" "supervisor_interval should be 2"
}

test_agents_json_max_restarts_value() {
    local value
    value=$(jq '.defaults.max_restarts' "$WIGGUM_HOME/config/agents.json" 2>/dev/null)

    assert_equals "2" "$value" "max_restarts should be 2"
}

# =============================================================================
# Test: agent_source_ralph_supervised helper
# =============================================================================

test_agent_source_ralph_supervised_exists() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"

    if type agent_source_ralph_supervised &>/dev/null; then
        assert_success "agent_source_ralph_supervised function should exist" true
    else
        assert_failure "agent_source_ralph_supervised function should exist" true
    fi
}

test_agent_source_ralph_supervised_sources_file() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"
    agent_source_ralph_supervised

    # After sourcing, the run_ralph_loop_supervised function should exist
    if type run_ralph_loop_supervised &>/dev/null; then
        assert_success "run_ralph_loop_supervised function should exist after sourcing" true
    else
        assert_failure "run_ralph_loop_supervised function should exist after sourcing" true
    fi
}

test_agent_source_ralph_supervised_provides_extraction_helpers() {
    source "$WIGGUM_HOME/lib/core/agent-base.sh"
    agent_source_ralph_supervised

    # Check extraction helpers are available
    if type _extract_supervisor_decision &>/dev/null; then
        assert_success "_extract_supervisor_decision should exist" true
    else
        assert_failure "_extract_supervisor_decision should exist" true
    fi

    if type _extract_supervisor_review &>/dev/null; then
        assert_success "_extract_supervisor_review should exist" true
    else
        assert_failure "_extract_supervisor_review should exist" true
    fi

    if type _extract_supervisor_guidance &>/dev/null; then
        assert_success "_extract_supervisor_guidance should exist" true
    else
        assert_failure "_extract_supervisor_guidance should exist" true
    fi
}

# =============================================================================
# Test: Default Supervisor Prompt
# =============================================================================

test_default_supervisor_prompt_exists() {
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
    source "$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    if type _default_supervisor_prompt &>/dev/null; then
        assert_success "_default_supervisor_prompt function should exist" true
    else
        assert_failure "_default_supervisor_prompt function should exist" true
    fi
}

test_default_supervisor_prompt_contains_required_elements() {
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
    source "$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    local prompt
    # Use generic step ID for test (summary file name comes from session_prefix)
    prompt=$(_default_supervisor_prompt 3 "/tmp/output" "mystep-2-summary.txt")

    assert_output_contains "$prompt" "SUPERVISOR REVIEW" "Prompt should contain review header"
    assert_output_contains "$prompt" "CONTINUE" "Prompt should mention CONTINUE option"
    assert_output_contains "$prompt" "STOP" "Prompt should mention STOP option"
    assert_output_contains "$prompt" "RESTART" "Prompt should mention RESTART option"
    assert_output_contains "$prompt" "<decision>" "Prompt should mention decision tag"
    assert_output_contains "$prompt" "<review>" "Prompt should mention review tag"
    assert_output_contains "$prompt" "<guidance>" "Prompt should mention guidance tag"
}

# =============================================================================
# Test: RALPH_LOOP_STOP_REASON exported on supervisor_stop path
# =============================================================================

test_stop_reason_variable_exported_on_supervisor_stop() {
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
    source "$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    # Verify the source code contains the RALPH_LOOP_STOP_REASON export
    # on the supervisor STOP path
    local loop_file="$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    # Check that RALPH_LOOP_STOP_REASON is exported on the supervisor_stop path
    if grep -q 'RALPH_LOOP_STOP_REASON="supervisor_stop"' "$loop_file"; then
        assert_success "runtime-loop.sh should export RALPH_LOOP_STOP_REASON=supervisor_stop" true
    else
        assert_failure "runtime-loop.sh should export RALPH_LOOP_STOP_REASON=supervisor_stop" true
    fi
}

test_stop_reason_variable_exported_on_max_iterations() {
    local loop_file="$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    if grep -q 'RALPH_LOOP_STOP_REASON="max_iterations"' "$loop_file"; then
        assert_success "runtime-loop.sh should export RALPH_LOOP_STOP_REASON=max_iterations" true
    else
        assert_failure "runtime-loop.sh should export RALPH_LOOP_STOP_REASON=max_iterations" true
    fi
}

test_stop_reason_variable_exported_on_restart_limit() {
    local loop_file="$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    if grep -q 'RALPH_LOOP_STOP_REASON="restart_limit"' "$loop_file"; then
        assert_success "runtime-loop.sh should export RALPH_LOOP_STOP_REASON=restart_limit" true
    else
        assert_failure "runtime-loop.sh should export RALPH_LOOP_STOP_REASON=restart_limit" true
    fi
}

test_stop_reason_variable_exported_on_normal_completion() {
    local loop_file="$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    # Normal completion uses the $loop_stop_reason variable
    if grep -q 'RALPH_LOOP_STOP_REASON="\$loop_stop_reason"' "$loop_file"; then
        assert_success "runtime-loop.sh should export RALPH_LOOP_STOP_REASON from loop_stop_reason variable" true
    else
        assert_failure "runtime-loop.sh should export RALPH_LOOP_STOP_REASON from loop_stop_reason variable" true
    fi
}

test_stop_reason_all_exit_paths_covered() {
    local loop_file="$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

    # Count all return statements in run_ralph_loop function
    # There should be RALPH_LOOP_STOP_REASON export before each return
    # (excluding early returns for validation errors before the loop starts)
    local return_count
    return_count=$(grep -c 'RALPH_LOOP_STOP_REASON=' "$loop_file")

    # We expect 4 exports: supervisor_stop, restart_limit, max_iterations, $loop_stop_reason
    if [ "$return_count" -ge 4 ]; then
        assert_success "Should have RALPH_LOOP_STOP_REASON on all exit paths ($return_count found)" true
    else
        assert_failure "Should have RALPH_LOOP_STOP_REASON on all exit paths (expected >=4, got $return_count)" true
    fi
}

# =============================================================================
# Run Tests
# =============================================================================

# Syntax validation
run_test test_ralph_loop_sh_syntax

# Extraction helpers - decision
run_test test_extract_supervisor_decision_continue
run_test test_extract_supervisor_decision_stop
run_test test_extract_supervisor_decision_restart
run_test test_extract_supervisor_decision_missing_defaults_to_continue
run_test test_extract_supervisor_decision_invalid_defaults_to_continue
run_test test_extract_supervisor_decision_embedded_in_content

# Extraction helpers - review
run_test test_extract_supervisor_review_success
run_test test_extract_supervisor_review_missing_tag
run_test test_extract_supervisor_review_strips_tags

# Extraction helpers - guidance
run_test test_extract_supervisor_guidance_success
run_test test_extract_supervisor_guidance_missing_tag
run_test test_extract_supervisor_guidance_strips_tags

# Full extraction workflow
run_test test_extract_all_supervisor_outputs

# Config loading
run_test test_config_loading_supervisor_interval_default
run_test test_config_loading_max_restarts_default
run_test test_config_loading_supervisor_settings_from_json

# agents.json validation
run_test test_agents_json_has_supervisor_interval
run_test test_agents_json_has_max_restarts
run_test test_agents_json_supervisor_interval_value
run_test test_agents_json_max_restarts_value

# agent_source_ralph_supervised helper
run_test test_agent_source_ralph_supervised_exists
run_test test_agent_source_ralph_supervised_sources_file
run_test test_agent_source_ralph_supervised_provides_extraction_helpers

# Default supervisor prompt
run_test test_default_supervisor_prompt_exists
run_test test_default_supervisor_prompt_contains_required_elements

# RALPH_LOOP_STOP_REASON exports
run_test test_stop_reason_variable_exported_on_supervisor_stop
run_test test_stop_reason_variable_exported_on_max_iterations
run_test test_stop_reason_variable_exported_on_restart_limit
run_test test_stop_reason_variable_exported_on_normal_completion
run_test test_stop_reason_all_exit_paths_covered

# Print summary
print_test_summary
exit_with_test_result
