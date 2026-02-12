#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: pr-merge
# AGENT_DESCRIPTION: PR merge agent that attempts to merge a pull request using
#   GitHub CLI. Pure bash, no LLM involved. Detects merge conflicts.
# REQUIRED_PATHS:
#   - workspace : Directory containing the git repository
# OUTPUT_FILES:
#   - pr-merge-result.json : Contains PASS (merged) or FAIL (conflict/error)
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "workflow.pr-merge" "Attempt to merge PR using GitHub CLI"

# Required paths before agent can run
agent_required_paths() {
    echo "workspace"
}

# Source dependencies
agent_source_core
source "$WIGGUM_HOME/lib/worker/git-state.sh"
source "$WIGGUM_HOME/lib/core/lifecycle-engine.sh"

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"

    local workspace="$worker_dir/workspace"

    if [ ! -d "$workspace" ]; then
        log_error "Workspace not found: $workspace"
        agent_write_result "$worker_dir" "FAIL" '{}' '["Workspace not found"]'
        return 1
    fi

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Set up context
    agent_setup_context "$worker_dir" "$workspace" "$project_dir"

    # Get PR number from git state or branch
    local pr_number
    pr_number=$(git_state_get_pr "$worker_dir")

    if [ "$pr_number" = "null" ] || [ -z "$pr_number" ]; then
        # Try to find PR number from workspace branch
        if [ -d "$workspace" ]; then
            local branch
            branch=$(git -C "$workspace" rev-parse --abbrev-ref HEAD 2>/dev/null || true)
            if [ -n "$branch" ] && [ "$branch" != "HEAD" ]; then
                pr_number=$(gh pr list --head "$branch" --state open --json number -q '.[0].number' 2>/dev/null || true)
                if [ -n "$pr_number" ]; then
                    git_state_set_pr "$worker_dir" "$pr_number"
                fi
            fi
        fi
    fi

    if [ -z "$pr_number" ] || [ "$pr_number" = "null" ]; then
        log_error "No PR number found - cannot attempt merge"
        agent_write_result "$worker_dir" "FAIL" '{}' '["No PR number found"]'
        return 1
    fi

    log "Attempting to merge PR #$pr_number..."

    # Use lifecycle event to track merge attempt (inc_merge_attempts effect)
    lifecycle_is_loaded || lifecycle_load
    if ! emit_event "$worker_dir" "merge.start" "workflow.pr-merge"; then
        # Fallback: direct increment if lifecycle rejects (e.g., max attempts reached)
        log_warn "merge.start rejected by lifecycle - may have exceeded max attempts"
        # Still increment for tracking (agent may want to handle the guard failure)
        git_state_inc_merge_attempts "$worker_dir"
    fi
    local merge_attempts
    merge_attempts=$(git_state_get_merge_attempts "$worker_dir")

    # Check PR status first
    local pr_state
    pr_state=$(gh pr view "$pr_number" --json state -q '.state' 2>/dev/null || echo "UNKNOWN")

    if [ "$pr_state" = "MERGED" ]; then
        log "PR #$pr_number is already merged"
        # Use merge.pr_merged (wildcard from: "*") to transition through lifecycle
        # engine, which runs effects (sync_github, cleanup_worktree, etc.)
        lifecycle_is_loaded || lifecycle_load
        emit_event "$worker_dir" "merge.pr_merged" "workflow.pr-merge" || true
        agent_write_result "$worker_dir" "PASS" \
            "{\"pr_number\":$pr_number,\"merge_status\":\"already_merged\"}"
        return 0
    fi

    if [ "$pr_state" = "CLOSED" ]; then
        log_error "PR #$pr_number is closed"
        agent_write_result "$worker_dir" "FAIL" \
            "{\"pr_number\":$pr_number,\"merge_status\":\"closed\"}" \
            '["PR is closed"]'
        return 1
    fi

    # Attempt merge via squash: each task is one logical change, so one commit on main.
    # Squash collapses intermediate commits (checkpoints, pre-conflict, sync-main merges)
    # into a clean atomic commit. GitHub preserves full PR history for forensics.
    # Don't delete branch — worktrees conflict with local branch deletion.
    local merge_output merge_exit=0
    merge_output=$(gh pr merge "$pr_number" --squash 2>&1) || merge_exit=$?

    if [ $merge_exit -eq 0 ]; then
        log "PR #$pr_number merged successfully"
        # Use merge.pr_merged (wildcard from: "*") to transition through lifecycle
        # engine, which runs effects (sync_github, cleanup_worktree, etc.)
        lifecycle_is_loaded || lifecycle_load
        emit_event "$worker_dir" "merge.pr_merged" "workflow.pr-merge" || true
        agent_write_result "$worker_dir" "PASS" \
            "{\"pr_number\":$pr_number,\"merge_status\":\"merged\",\"attempts\":$merge_attempts}"
        return 0
    fi

    # Failure paths: do NOT set lifecycle state directly. The pipeline runner
    # reads the gate result (FAIL) and the orchestrator's worker_complete_fix()
    # handles lifecycle transitions from "fixing" state. Direct git_state_set
    # here would corrupt the lifecycle state mid-pipeline.

    # Check if failure is due to merge conflict
    if echo "$merge_output" | grep -qiE "(conflict|cannot be merged|out of date|not mergeable)"; then
        log "Merge conflict detected for PR #$pr_number"
        git_state_set_error "$worker_dir" "Merge conflict: ${merge_output:0:200}"
        agent_write_result "$worker_dir" "FAIL" \
            "{\"pr_number\":$pr_number,\"merge_status\":\"conflict\",\"attempts\":$merge_attempts}"
        return 0  # FAIL is a valid gate result, not an error
    fi

    # Check if merge is blocked by checks
    if echo "$merge_output" | grep -qiE "(checks|status|required)"; then
        log "Merge blocked by checks for PR #$pr_number"
        agent_write_result "$worker_dir" "FAIL" \
            "{\"pr_number\":$pr_number,\"merge_status\":\"checks_failed\",\"attempts\":$merge_attempts}" \
            '["Merge blocked by checks"]'
        return 0
    fi

    # Other merge failure
    log_error "Merge failed for PR #$pr_number: $merge_output"
    git_state_set_error "$worker_dir" "Merge failed: ${merge_output:0:200}"
    agent_write_result "$worker_dir" "FAIL" \
        "{\"pr_number\":$pr_number,\"merge_status\":\"error\",\"attempts\":$merge_attempts}" \
        '["Merge failed: '"${merge_output:0:200}"'"]'
    return 1
}
