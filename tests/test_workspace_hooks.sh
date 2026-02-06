#!/usr/bin/env bash
# test_workspace_hooks.sh - Tests for workspace hooks configuration and enforcement
#
# Validates:
#   - _write_workspace_hooks_config generates valid .claude/settings.local.json
#   - PreToolUse hooks block operations outside workspace
#   - PreToolUse hooks allow operations within workspace
#   - CLAUDE_PROJECT_DIR fallback works when WORKER_WORKSPACE is unset
#   - inject-workspace-boundary.sh modifies Task tool prompts
#   - Git commands are blocked regardless of path
#   - Path traversal attempts are caught
#   - Symlink escape attempts are caught
set -euo pipefail

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$TESTS_DIR/test-framework.sh"

PROJECT_ROOT="$(cd "$TESTS_DIR/.." && pwd)"
HOOKS_DIR="$PROJECT_ROOT/hooks/callbacks"
VALIDATE_HOOK="$HOOKS_DIR/validate-workspace-path.sh"
INJECT_HOOK="$HOOKS_DIR/inject-workspace-boundary.sh"

# Test workspace directory (created per test)
TEST_WORKSPACE=""

# =============================================================================
# Helpers
# =============================================================================

# Run the validate hook with given tool call JSON and env vars
# Args: json [WORKER_WORKSPACE] [CLAUDE_PROJECT_DIR]
# Returns: exit code from hook, stdout captured in $HOOK_STDOUT, stderr in $HOOK_STDERR
run_validate_hook() {
    local json="$1"
    local ws="${2:-}"
    local cpd="${3:-}"

    HOOK_STDOUT=""
    # shellcheck disable=SC2034
    HOOK_STDERR=""
    local rc=0

    HOOK_STDOUT=$(echo "$json" | \
        WORKER_WORKSPACE="$ws" CLAUDE_PROJECT_DIR="$cpd" WORKER_DIR="" \
        bash "$VALIDATE_HOOK" 2>"$TEST_WORKSPACE/hook_stderr.tmp") || rc=$?
    # shellcheck disable=SC2034
    HOOK_STDERR=$(cat "$TEST_WORKSPACE/hook_stderr.tmp" 2>/dev/null || true)
    return $rc
}

# Run the inject hook with given tool call JSON and env vars
# Args: json [WORKER_WORKSPACE] [CLAUDE_PROJECT_DIR]
run_inject_hook() {
    local json="$1"
    local ws="${2:-}"
    local cpd="${3:-}"

    HOOK_STDOUT=""
    # shellcheck disable=SC2034
    HOOK_STDERR=""
    local rc=0

    HOOK_STDOUT=$(echo "$json" | \
        WORKER_WORKSPACE="$ws" CLAUDE_PROJECT_DIR="$cpd" WORKER_DIR="" \
        bash "$INJECT_HOOK" 2>"$TEST_WORKSPACE/hook_stderr.tmp") || rc=$?
    # shellcheck disable=SC2034
    HOOK_STDERR=$(cat "$TEST_WORKSPACE/hook_stderr.tmp" 2>/dev/null || true)
    return $rc
}

# Build tool call JSON for a given tool and file_path
tool_json() {
    local tool="$1"
    local file_path="${2:-}"
    local command="${3:-}"

    if [ -n "$file_path" ]; then
        jq -n --arg tool "$tool" --arg fp "$file_path" \
            '{"tool":$tool,"tool_input":{"file_path":$fp}}'
    elif [ -n "$command" ]; then
        jq -n --arg tool "$tool" --arg cmd "$command" \
            '{"tool":$tool,"tool_input":{"command":$cmd}}'
    else
        jq -n --arg tool "$tool" '{"tool":$tool,"tool_input":{}}'
    fi
}

# Build Task tool call JSON
task_json() {
    local prompt="$1"
    local subagent="${2:-Explore}"

    jq -n --arg p "$prompt" --arg s "$subagent" \
        '{"tool":"Task","tool_input":{"prompt":$p,"subagent_type":$s,"description":"test"}}'
}

# =============================================================================
# Setup / Teardown
# =============================================================================

setup() {
    TEST_WORKSPACE=$(mktemp -d)
    mkdir -p "$TEST_WORKSPACE/src"
    echo "hello" > "$TEST_WORKSPACE/src/main.py"
}

teardown() {
    if [ -n "$TEST_WORKSPACE" ] && [ -d "$TEST_WORKSPACE" ]; then
        [ -n "$TEST_WORKSPACE" ] && rm -rf "$TEST_WORKSPACE"
    fi
}

# =============================================================================
# Tests: Settings File Generation
# =============================================================================

test_write_hooks_config_creates_settings_file() {
    (
        export WIGGUM_HOME="$PROJECT_ROOT"
        source "$PROJECT_ROOT/lib/core/logger.sh"
        source "$PROJECT_ROOT/lib/git/worktree-helpers.sh"
        _write_workspace_hooks_config "$TEST_WORKSPACE"
    )

    assert_file_exists "$TEST_WORKSPACE/.claude/settings.local.json" \
        "Should create .claude/settings.local.json"
}

test_write_hooks_config_produces_valid_json() {
    (
        export WIGGUM_HOME="$PROJECT_ROOT"
        source "$PROJECT_ROOT/lib/core/logger.sh"
        source "$PROJECT_ROOT/lib/git/worktree-helpers.sh"
        _write_workspace_hooks_config "$TEST_WORKSPACE"
    )

    local rc=0
    jq empty "$TEST_WORKSPACE/.claude/settings.local.json" 2>/dev/null || rc=$?
    assert_equals "0" "$rc" "Generated settings should be valid JSON"
}

test_write_hooks_config_has_pretooluse_hooks() {
    (
        export WIGGUM_HOME="$PROJECT_ROOT"
        source "$PROJECT_ROOT/lib/core/logger.sh"
        source "$PROJECT_ROOT/lib/git/worktree-helpers.sh"
        _write_workspace_hooks_config "$TEST_WORKSPACE"
    )

    local hook_count
    hook_count=$(jq '.hooks.PreToolUse | length' "$TEST_WORKSPACE/.claude/settings.local.json")
    assert_equals "2" "$hook_count" "Should have 2 PreToolUse hook entries"
}

test_write_hooks_config_has_file_tool_matcher() {
    (
        export WIGGUM_HOME="$PROJECT_ROOT"
        source "$PROJECT_ROOT/lib/core/logger.sh"
        source "$PROJECT_ROOT/lib/git/worktree-helpers.sh"
        _write_workspace_hooks_config "$TEST_WORKSPACE"
    )

    local matcher
    matcher=$(jq -r '.hooks.PreToolUse[0].matcher' "$TEST_WORKSPACE/.claude/settings.local.json")
    assert_equals "Edit|Write|Bash|Read|Glob|Grep" "$matcher" \
        "First hook should match file/command tools"
}

test_write_hooks_config_has_task_matcher() {
    (
        export WIGGUM_HOME="$PROJECT_ROOT"
        source "$PROJECT_ROOT/lib/core/logger.sh"
        source "$PROJECT_ROOT/lib/git/worktree-helpers.sh"
        _write_workspace_hooks_config "$TEST_WORKSPACE"
    )

    local matcher
    matcher=$(jq -r '.hooks.PreToolUse[1].matcher' "$TEST_WORKSPACE/.claude/settings.local.json")
    assert_equals "Task" "$matcher" "Second hook should match Task tool"
}

test_write_hooks_config_has_absolute_command_paths() {
    (
        export WIGGUM_HOME="$PROJECT_ROOT"
        source "$PROJECT_ROOT/lib/core/logger.sh"
        source "$PROJECT_ROOT/lib/git/worktree-helpers.sh"
        _write_workspace_hooks_config "$TEST_WORKSPACE"
    )

    local cmd
    cmd=$(jq -r '.hooks.PreToolUse[0].hooks[0].command' "$TEST_WORKSPACE/.claude/settings.local.json")
    assert_output_contains "$cmd" "validate-workspace-path.sh" \
        "Command should reference validate-workspace-path.sh"
    assert_output_contains "$cmd" "$PROJECT_ROOT" \
        "Command should use absolute WIGGUM_HOME path"
}

test_write_hooks_config_preserves_permissions() {
    (
        export WIGGUM_HOME="$PROJECT_ROOT"
        source "$PROJECT_ROOT/lib/core/logger.sh"
        source "$PROJECT_ROOT/lib/git/worktree-helpers.sh"
        _write_workspace_hooks_config "$TEST_WORKSPACE"
    )

    local allow
    allow=$(jq -r '.permissions.allow[0]' "$TEST_WORKSPACE/.claude/settings.local.json")
    assert_equals "Bash(tail:*)" "$allow" "Should include permissions.allow"
}

# =============================================================================
# Tests: Validate Hook - Blocking
# =============================================================================

test_hook_blocks_write_outside_workspace() {
    local json
    json=$(tool_json "Write" "/etc/passwd")

    local rc=0
    run_validate_hook "$json" "$TEST_WORKSPACE" "" || rc=$?
    assert_equals "2" "$rc" "Should block Write to /etc/passwd (exit 2)"
}

test_hook_blocks_read_outside_workspace() {
    local json
    json=$(tool_json "Read" "/home/user/.ssh/id_rsa")

    local rc=0
    run_validate_hook "$json" "$TEST_WORKSPACE" "" || rc=$?
    assert_equals "2" "$rc" "Should block Read of /home/user/.ssh/id_rsa"
}

test_hook_blocks_edit_outside_workspace() {
    local json
    json=$(tool_json "Edit" "/var/log/syslog")

    local rc=0
    run_validate_hook "$json" "$TEST_WORKSPACE" "" || rc=$?
    assert_equals "2" "$rc" "Should block Edit of /var/log/syslog"
}

test_hook_blocks_git_commands() {
    local json
    json=$(tool_json "Bash" "" "git reset --hard HEAD")

    local rc=0
    run_validate_hook "$json" "$TEST_WORKSPACE" "" || rc=$?
    assert_equals "2" "$rc" "Should block git commands"
}

test_hook_blocks_git_push() {
    local json
    json=$(tool_json "Bash" "" "git push origin main")

    local rc=0
    run_validate_hook "$json" "$TEST_WORKSPACE" "" || rc=$?
    assert_equals "2" "$rc" "Should block git push"
}

test_hook_blocks_git_in_pipeline() {
    local json
    json=$(tool_json "Bash" "" "echo hello && git status")

    local rc=0
    run_validate_hook "$json" "$TEST_WORKSPACE" "" || rc=$?
    assert_equals "2" "$rc" "Should block git in command pipelines"
}

test_hook_blocks_cd_escape() {
    local json
    json=$(tool_json "Bash" "" "cd /tmp && cat secrets.txt")

    local rc=0
    run_validate_hook "$json" "$TEST_WORKSPACE" "" || rc=$?
    assert_equals "2" "$rc" "Should block cd to outside workspace"
}

test_hook_blocks_absolute_path_in_bash() {
    local json
    json=$(tool_json "Bash" "" "cat /home/user/secret.txt")

    local rc=0
    run_validate_hook "$json" "$TEST_WORKSPACE" "" || rc=$?
    assert_equals "2" "$rc" "Should block absolute paths outside workspace in bash"
}

# =============================================================================
# Tests: Validate Hook - Allowing
# =============================================================================

test_hook_allows_write_inside_workspace() {
    local json
    json=$(tool_json "Write" "$TEST_WORKSPACE/src/new_file.py")

    local rc=0
    run_validate_hook "$json" "$TEST_WORKSPACE" "" || rc=$?
    assert_equals "0" "$rc" "Should allow Write inside workspace"
}

test_hook_allows_read_inside_workspace() {
    local json
    json=$(tool_json "Read" "$TEST_WORKSPACE/src/main.py")

    local rc=0
    run_validate_hook "$json" "$TEST_WORKSPACE" "" || rc=$?
    assert_equals "0" "$rc" "Should allow Read inside workspace"
}

test_hook_allows_bash_within_workspace() {
    local json
    json=$(tool_json "Bash" "" "ls $TEST_WORKSPACE/src")

    local rc=0
    run_validate_hook "$json" "$TEST_WORKSPACE" "" || rc=$?
    assert_equals "0" "$rc" "Should allow bash commands within workspace"
}

test_hook_allows_safe_system_paths() {
    local json
    json=$(tool_json "Bash" "" "which python3")

    local rc=0
    run_validate_hook "$json" "$TEST_WORKSPACE" "" || rc=$?
    assert_equals "0" "$rc" "Should allow commands using /usr/bin paths"
}

test_hook_allows_no_path_tools() {
    local json
    json='{"tool":"Bash","tool_input":{"command":"echo hello"}}'

    local rc=0
    run_validate_hook "$json" "$TEST_WORKSPACE" "" || rc=$?
    assert_equals "0" "$rc" "Should allow commands with no file paths"
}

test_hook_blocks_when_no_workspace_set() {
    local json
    json=$(tool_json "Write" "/etc/passwd")

    local rc=0
    run_validate_hook "$json" "" "" || rc=$?
    assert_equals "2" "$rc" "Should block when no workspace is set (fail-closed)"
}

# =============================================================================
# Tests: CLAUDE_PROJECT_DIR Fallback
# =============================================================================

test_hook_uses_claude_project_dir_fallback() {
    local json
    json=$(tool_json "Write" "/etc/passwd")

    # No WORKER_WORKSPACE, but CLAUDE_PROJECT_DIR is set
    local rc=0
    run_validate_hook "$json" "" "$TEST_WORKSPACE" || rc=$?
    assert_equals "2" "$rc" "Should use CLAUDE_PROJECT_DIR when WORKER_WORKSPACE is empty"
}

test_hook_allows_within_claude_project_dir() {
    local json
    json=$(tool_json "Write" "$TEST_WORKSPACE/new.txt")

    local rc=0
    run_validate_hook "$json" "" "$TEST_WORKSPACE" || rc=$?
    assert_equals "0" "$rc" "Should allow paths within CLAUDE_PROJECT_DIR"
}

test_hook_worker_workspace_takes_priority() {
    # WORKER_WORKSPACE is set to TEST_WORKSPACE, CLAUDE_PROJECT_DIR to something else
    local other_dir
    other_dir=$(mktemp -d)

    local json
    json=$(tool_json "Write" "$TEST_WORKSPACE/file.txt")

    # Path is within WORKER_WORKSPACE but not within CLAUDE_PROJECT_DIR
    local rc=0
    run_validate_hook "$json" "$TEST_WORKSPACE" "$other_dir" || rc=$?
    assert_equals "0" "$rc" "WORKER_WORKSPACE should take priority over CLAUDE_PROJECT_DIR"

    [ -n "$other_dir" ] && rm -rf "$other_dir"
}

# =============================================================================
# Tests: Inject Workspace Boundary Hook
# =============================================================================

test_inject_hook_adds_boundary_constraint() {
    local json
    json=$(task_json "Find all Python files")

    run_inject_hook "$json" "$TEST_WORKSPACE" ""

    local decision
    decision=$(echo "$HOOK_STDOUT" | jq -r '.hookSpecificOutput.permissionDecision')
    assert_equals "allow" "$decision" "Inject hook should allow with modified input"

    local modified_prompt
    modified_prompt=$(echo "$HOOK_STDOUT" | jq -r '.hookSpecificOutput.updatedInput.prompt')
    assert_output_contains "$modified_prompt" "CRITICAL WORKSPACE BOUNDARY CONSTRAINT" \
        "Modified prompt should contain boundary constraint"
    assert_output_contains "$modified_prompt" "$TEST_WORKSPACE" \
        "Modified prompt should contain workspace path"
    assert_output_contains "$modified_prompt" "Find all Python files" \
        "Modified prompt should preserve original prompt"
}

test_inject_hook_uses_claude_project_dir() {
    local json
    json=$(task_json "Search for errors")

    run_inject_hook "$json" "" "$TEST_WORKSPACE"

    local modified_prompt
    modified_prompt=$(echo "$HOOK_STDOUT" | jq -r '.hookSpecificOutput.updatedInput.prompt')
    assert_output_contains "$modified_prompt" "$TEST_WORKSPACE" \
        "Should use CLAUDE_PROJECT_DIR in boundary constraint"
}

test_inject_hook_passes_through_without_workspace() {
    local json
    json=$(task_json "Do something")

    run_inject_hook "$json" "" ""

    local decision
    decision=$(echo "$HOOK_STDOUT" | jq -r '.hookSpecificOutput.permissionDecision')
    assert_equals "allow" "$decision" "Should allow without modification when no workspace"

    # Should not have updatedInput when no workspace
    local has_updated
    has_updated=$(echo "$HOOK_STDOUT" | jq 'has("hookSpecificOutput") and (.hookSpecificOutput | has("updatedInput"))')
    assert_equals "false" "$has_updated" \
        "Should not modify input when no workspace is set"
}

test_inject_hook_preserves_subagent_type() {
    local json
    json=$(task_json "Test prompt" "data-scientist")

    run_inject_hook "$json" "$TEST_WORKSPACE" ""

    local subagent
    subagent=$(echo "$HOOK_STDOUT" | jq -r '.hookSpecificOutput.updatedInput.subagent_type')
    assert_equals "data-scientist" "$subagent" "Should preserve subagent_type"
}

# =============================================================================
# Tests: Path Traversal Edge Cases
# =============================================================================

test_hook_blocks_path_traversal_in_file_path() {
    local json
    json=$(tool_json "Read" "$TEST_WORKSPACE/../../etc/passwd")

    local rc=0
    run_validate_hook "$json" "$TEST_WORKSPACE" "" || rc=$?
    assert_equals "2" "$rc" "Should block path traversal in file_path"
}

test_hook_blocks_symlink_escape() {
    # Create a symlink that points outside workspace
    ln -sf /etc/hostname "$TEST_WORKSPACE/evil_link" 2>/dev/null || true

    if [ -L "$TEST_WORKSPACE/evil_link" ]; then
        local json
        json=$(tool_json "Read" "$TEST_WORKSPACE/evil_link")

        local rc=0
        run_validate_hook "$json" "$TEST_WORKSPACE" "" || rc=$?
        assert_equals "2" "$rc" "Should block symlink that points outside workspace"
    else
        # Can't create symlinks in this environment, skip
        ASSERTION_COUNT=$((ASSERTION_COUNT + 1))
        echo -e "  ${GREEN}✓${NC} Symlink test skipped (cannot create symlinks)"
    fi
}

# =============================================================================
# Tests: Grep/Glob Path Validation
# =============================================================================

test_hook_blocks_grep_outside_workspace() {
    local json
    json='{"tool":"Grep","tool_input":{"pattern":"password","path":"/etc"}}'

    local rc=0
    run_validate_hook "$json" "$TEST_WORKSPACE" "" || rc=$?
    assert_equals "2" "$rc" "Should block Grep with path outside workspace"
}

test_hook_allows_grep_inside_workspace() {
    local json
    json=$(jq -n --arg path "$TEST_WORKSPACE/src" \
        '{"tool":"Grep","tool_input":{"pattern":"hello","path":$path}}')

    local rc=0
    run_validate_hook "$json" "$TEST_WORKSPACE" "" || rc=$?
    assert_equals "0" "$rc" "Should allow Grep within workspace"
}

# =============================================================================
# Tests: Full Integration Path (setup_worktree → hooks → enforcement)
# =============================================================================

test_full_integration_setup_then_enforce() {
    # Simulate what happens during worker setup:
    # 1. Write hooks config (as setup_worktree would)
    (
        export WIGGUM_HOME="$PROJECT_ROOT"
        source "$PROJECT_ROOT/lib/core/logger.sh"
        source "$PROJECT_ROOT/lib/git/worktree-helpers.sh"
        _write_workspace_hooks_config "$TEST_WORKSPACE"
    )

    # 2. Verify settings file has correct structure
    assert_file_exists "$TEST_WORKSPACE/.claude/settings.local.json" \
        "Integration: settings file created"

    # 3. Extract the validate hook command from settings
    local hook_cmd
    hook_cmd=$(jq -r '.hooks.PreToolUse[0].hooks[0].command' \
        "$TEST_WORKSPACE/.claude/settings.local.json")

    # 4. Verify the hook command script exists
    local script_path
    script_path=$(echo "$hook_cmd" | sed 's/^bash //')
    assert_file_exists "$script_path" "Integration: hook script exists at configured path"

    # 5. Run the hook as Claude would - blocking case
    local json
    json=$(tool_json "Write" "/etc/shadow")
    local rc=0
    run_validate_hook "$json" "$TEST_WORKSPACE" "" || rc=$?
    assert_equals "2" "$rc" "Integration: hook blocks write outside workspace"

    # 6. Run the hook - allowing case
    json=$(tool_json "Write" "$TEST_WORKSPACE/output.txt")
    rc=0
    run_validate_hook "$json" "$TEST_WORKSPACE" "" || rc=$?
    assert_equals "0" "$rc" "Integration: hook allows write inside workspace"
}

test_full_integration_claude_project_dir_only() {
    # Simulate Claude started in workspace directory (no WORKER_WORKSPACE)
    # CLAUDE_PROJECT_DIR is set automatically by Claude Code to the project root
    (
        export WIGGUM_HOME="$PROJECT_ROOT"
        source "$PROJECT_ROOT/lib/core/logger.sh"
        source "$PROJECT_ROOT/lib/git/worktree-helpers.sh"
        _write_workspace_hooks_config "$TEST_WORKSPACE"
    )

    # Hook uses CLAUDE_PROJECT_DIR as fallback
    local json
    json=$(tool_json "Read" "/etc/hostname")
    local rc=0
    run_validate_hook "$json" "" "$TEST_WORKSPACE" || rc=$?
    assert_equals "2" "$rc" "Integration: CLAUDE_PROJECT_DIR fallback blocks violations"

    json=$(tool_json "Read" "$TEST_WORKSPACE/src/main.py")
    rc=0
    run_validate_hook "$json" "" "$TEST_WORKSPACE" || rc=$?
    assert_equals "0" "$rc" "Integration: CLAUDE_PROJECT_DIR fallback allows workspace access"
}

# =============================================================================
# Run Tests
# =============================================================================

echo "=== Workspace Hooks Tests ==="

# Settings file generation
run_test test_write_hooks_config_creates_settings_file
run_test test_write_hooks_config_produces_valid_json
run_test test_write_hooks_config_has_pretooluse_hooks
run_test test_write_hooks_config_has_file_tool_matcher
run_test test_write_hooks_config_has_task_matcher
run_test test_write_hooks_config_has_absolute_command_paths
run_test test_write_hooks_config_preserves_permissions

# Validate hook - blocking
run_test test_hook_blocks_write_outside_workspace
run_test test_hook_blocks_read_outside_workspace
run_test test_hook_blocks_edit_outside_workspace
run_test test_hook_blocks_git_commands
run_test test_hook_blocks_git_push
run_test test_hook_blocks_git_in_pipeline
run_test test_hook_blocks_cd_escape
run_test test_hook_blocks_absolute_path_in_bash

# Validate hook - allowing
run_test test_hook_allows_write_inside_workspace
run_test test_hook_allows_read_inside_workspace
run_test test_hook_allows_bash_within_workspace
run_test test_hook_allows_safe_system_paths
run_test test_hook_allows_no_path_tools
run_test test_hook_blocks_when_no_workspace_set

# CLAUDE_PROJECT_DIR fallback
run_test test_hook_uses_claude_project_dir_fallback
run_test test_hook_allows_within_claude_project_dir
run_test test_hook_worker_workspace_takes_priority

# Inject hook
run_test test_inject_hook_adds_boundary_constraint
run_test test_inject_hook_uses_claude_project_dir
run_test test_inject_hook_passes_through_without_workspace
run_test test_inject_hook_preserves_subagent_type

# Path traversal edge cases
run_test test_hook_blocks_path_traversal_in_file_path
run_test test_hook_blocks_symlink_escape
run_test test_hook_blocks_grep_outside_workspace
run_test test_hook_allows_grep_inside_workspace

# Full integration
run_test test_full_integration_setup_then_enforce
run_test test_full_integration_claude_project_dir_only

# Summary
print_test_summary
exit_with_test_result
