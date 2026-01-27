#!/usr/bin/env bash
set -euo pipefail
# Tests for config/pipelines/fix.json pipeline configuration

TESTS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WIGGUM_HOME="$(dirname "$TESTS_DIR")"
export WIGGUM_HOME

source "$TESTS_DIR/test-framework.sh"

# Pipeline file path
PIPELINE_FILE="$WIGGUM_HOME/config/pipelines/fix.json"

# =============================================================================
# Pipeline File Tests
# =============================================================================

test_fix_pipeline_exists() {
    assert_file_exists "$PIPELINE_FILE" "Fix pipeline should exist"
}

test_fix_pipeline_valid_json() {
    local result=0
    jq . "$PIPELINE_FILE" > /dev/null 2>&1 || result=$?
    assert_equals "0" "$result" "Pipeline should be valid JSON"
}

test_fix_pipeline_has_name() {
    local name
    name=$(jq -r '.name' "$PIPELINE_FILE")
    assert_equals "fix" "$name" "Pipeline name should be 'fix'"
}

test_fix_pipeline_has_description() {
    local desc
    desc=$(jq -r '.description // ""' "$PIPELINE_FILE")
    assert_not_empty "$desc" "Pipeline should have description"
}

# =============================================================================
# Step Tests
# =============================================================================

test_fix_pipeline_has_steps() {
    local step_count
    step_count=$(jq '.steps | length' "$PIPELINE_FILE")
    assert_greater_than "$step_count" "0" "Pipeline should have steps"
}

test_fix_pipeline_has_pr_fix_step() {
    local step_id
    step_id=$(jq -r '.steps[0].id' "$PIPELINE_FILE")
    assert_equals "pr-fix" "$step_id" "First step should be pr-fix"
}

test_fix_pipeline_has_sync_main_step() {
    local has_sync
    has_sync=$(jq -r '.steps[] | select(.id == "sync-main") | .id' "$PIPELINE_FILE")
    assert_equals "sync-main" "$has_sync" "Should have sync-main step"
}

test_fix_pipeline_has_commit_push_step() {
    local has_commit
    has_commit=$(jq -r '.steps[] | select(.id == "commit-push") | .id' "$PIPELINE_FILE")
    assert_equals "commit-push" "$has_commit" "Should have commit-push step"
}

test_fix_pipeline_has_merge_step() {
    local has_merge
    has_merge=$(jq -r '.steps[] | select(.id == "merge") | .id' "$PIPELINE_FILE")
    assert_equals "merge" "$has_merge" "Should have merge step"
}

# =============================================================================
# Agent Assignment Tests
# =============================================================================

test_pr_fix_step_uses_correct_agent() {
    local agent
    agent=$(jq -r '.steps[] | select(.id == "pr-fix") | .agent' "$PIPELINE_FILE")
    assert_equals "engineering.pr-comment-fix" "$agent" "pr-fix should use engineering.pr-comment-fix"
}

test_sync_main_step_uses_correct_agent() {
    local agent
    agent=$(jq -r '.steps[] | select(.id == "sync-main") | .agent' "$PIPELINE_FILE")
    assert_equals "workflow.git-sync-main" "$agent" "sync-main should use workflow.git-sync-main"
}

test_commit_push_step_uses_correct_agent() {
    local agent
    agent=$(jq -r '.steps[] | select(.id == "commit-push") | .agent' "$PIPELINE_FILE")
    assert_equals "workflow.git-commit-push" "$agent" "commit-push should use workflow.git-commit-push"
}

test_merge_step_uses_correct_agent() {
    local agent
    agent=$(jq -r '.steps[] | select(.id == "merge") | .agent' "$PIPELINE_FILE")
    assert_equals "workflow.pr-merge" "$agent" "merge should use workflow.pr-merge"
}

# =============================================================================
# on_result Handler Tests
# =============================================================================

test_pr_fix_skip_jumps_to_sync_main() {
    local jump_target
    jump_target=$(jq -r '.steps[] | select(.id == "pr-fix") | .on_result.SKIP.jump' "$PIPELINE_FILE")
    assert_equals "sync-main" "$jump_target" "SKIP should jump to sync-main"
}

test_sync_main_fail_has_inline_resolver() {
    local inline_agent
    inline_agent=$(jq -r '.steps[] | select(.id == "sync-main") | .on_result.FAIL.agent' "$PIPELINE_FILE")
    assert_equals "workflow.git-conflict-resolver" "$inline_agent" "FAIL should spawn resolver"
}

test_resolver_pass_jumps_to_commit_push() {
    local jump_target
    jump_target=$(jq -r '.steps[] | select(.id == "sync-main") | .on_result.FAIL.on_result.PASS.jump' "$PIPELINE_FILE")
    assert_equals "commit-push" "$jump_target" "Resolver PASS should jump to commit-push"
}

test_resolver_fail_jumps_to_abort() {
    local jump_target
    jump_target=$(jq -r '.steps[] | select(.id == "sync-main") | .on_result.FAIL.on_result.FAIL.jump' "$PIPELINE_FILE")
    assert_equals "abort" "$jump_target" "Resolver FAIL should abort"
}

test_merge_fail_jumps_to_sync_main() {
    local jump_target
    jump_target=$(jq -r '.steps[] | select(.id == "merge") | .on_result.FAIL.jump' "$PIPELINE_FILE")
    assert_equals "sync-main" "$jump_target" "Merge FAIL should jump to sync-main for retry"
}

# =============================================================================
# Max Iterations Tests
# =============================================================================

test_pr_fix_has_max() {
    local max
    max=$(jq '.steps[] | select(.id == "pr-fix") | .max' "$PIPELINE_FILE")
    assert_greater_than "$max" "0" "pr-fix should have max iterations"
}

test_sync_main_has_max() {
    local max
    max=$(jq '.steps[] | select(.id == "sync-main") | .max' "$PIPELINE_FILE")
    assert_greater_than "$max" "0" "sync-main should have max iterations"
}

test_resolver_has_max() {
    local max
    max=$(jq '.steps[] | select(.id == "sync-main") | .on_result.FAIL.max' "$PIPELINE_FILE")
    assert_greater_than "$max" "0" "resolver should have max iterations"
}

test_commit_push_has_max() {
    local max
    max=$(jq '.steps[] | select(.id == "commit-push") | .max' "$PIPELINE_FILE")
    assert_greater_than "$max" "0" "commit-push should have max iterations"
}

test_merge_has_max() {
    local max
    max=$(jq '.steps[] | select(.id == "merge") | .max' "$PIPELINE_FILE")
    assert_greater_than "$max" "0" "merge should have max iterations"
}

# =============================================================================
# Pipeline Flow Tests
# =============================================================================

test_pipeline_step_order() {
    # Verify steps are in the expected order
    local step_ids
    step_ids=$(jq -r '.steps[].id' "$PIPELINE_FILE" | tr '\n' ',')

    assert_output_contains "$step_ids" "pr-fix" "Should have pr-fix"
    assert_output_contains "$step_ids" "sync-main" "Should have sync-main"
    assert_output_contains "$step_ids" "commit-push" "Should have commit-push"
    assert_output_contains "$step_ids" "merge" "Should have merge"
}

test_pipeline_has_commit_after_on_pr_fix() {
    local commit_after
    commit_after=$(jq '.steps[] | select(.id == "pr-fix") | .commit_after' "$PIPELINE_FILE")
    assert_equals "true" "$commit_after" "pr-fix should have commit_after"
}

# =============================================================================
# Integration with Pipeline Loader Tests
# =============================================================================

test_pipeline_loader_can_load_fix() {
    source "$WIGGUM_HOME/lib/pipeline/pipeline-loader.sh"

    local pipeline_path
    pipeline_path=$(pipeline_resolve "$WIGGUM_HOME" "" "fix")

    local result=0
    pipeline_load "$pipeline_path" 2>/dev/null || result=$?

    assert_equals "0" "$result" "Pipeline loader should load fix pipeline"
}

test_pipeline_loader_resolves_steps() {
    source "$WIGGUM_HOME/lib/pipeline/pipeline-loader.sh"

    local pipeline_path
    pipeline_path=$(pipeline_resolve "$WIGGUM_HOME" "" "fix")
    pipeline_load "$pipeline_path" 2>/dev/null

    local step_count
    step_count=$(pipeline_step_count)
    assert_greater_than "$step_count" "0" "Should have loaded steps"
}

# =============================================================================
# Run Tests
# =============================================================================

run_test test_fix_pipeline_exists
run_test test_fix_pipeline_valid_json
run_test test_fix_pipeline_has_name
run_test test_fix_pipeline_has_description
run_test test_fix_pipeline_has_steps
run_test test_fix_pipeline_has_pr_fix_step
run_test test_fix_pipeline_has_sync_main_step
run_test test_fix_pipeline_has_commit_push_step
run_test test_fix_pipeline_has_merge_step
run_test test_pr_fix_step_uses_correct_agent
run_test test_sync_main_step_uses_correct_agent
run_test test_commit_push_step_uses_correct_agent
run_test test_merge_step_uses_correct_agent
run_test test_pr_fix_skip_jumps_to_sync_main
run_test test_sync_main_fail_has_inline_resolver
run_test test_resolver_pass_jumps_to_commit_push
run_test test_resolver_fail_jumps_to_abort
run_test test_merge_fail_jumps_to_sync_main
run_test test_pr_fix_has_max
run_test test_sync_main_has_max
run_test test_resolver_has_max
run_test test_commit_push_has_max
run_test test_merge_has_max
run_test test_pipeline_step_order
run_test test_pipeline_has_commit_after_on_pr_fix
run_test test_pipeline_loader_can_load_fix
run_test test_pipeline_loader_resolves_steps

print_test_summary
exit_with_test_result
