#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: git-commit-push
# AGENT_DESCRIPTION: Git commit and push agent that stages all changes, creates
#   a commit, and pushes to the remote branch. Pure bash, no LLM involved.
# REQUIRED_PATHS:
#   - workspace : Directory containing the git repository
# OUTPUT_FILES:
#   - commit-push-result.json : Contains PASS or FAIL with commit SHA
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "workflow.git-commit-push" "Git stage, commit and push changes"

# Required paths before agent can run
agent_required_paths() {
    echo "workspace"
}

# Source dependencies
agent_source_core

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    local commit_message="${3:-fix: Automated changes}"

    local workspace="$worker_dir/workspace"

    if [ ! -d "$workspace" ]; then
        log_error "Workspace not found: $workspace"
        agent_write_result "$worker_dir" "FAIL" '{}' '["Workspace not found"]'
        return 1
    fi

    # Verify workspace is a git repository
    if [ ! -d "$workspace/.git" ] && ! git -C "$workspace" rev-parse --git-dir &>/dev/null; then
        log_error "Workspace is not a git repository: $workspace"
        agent_write_result "$worker_dir" "FAIL" '{}' '["Not a git repository"]'
        return 1
    fi

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Set up context
    agent_setup_context "$worker_dir" "$workspace" "$project_dir"

    # Check if there are changes to commit
    local has_changes=false
    if ! git -C "$workspace" diff --quiet 2>/dev/null; then
        has_changes=true
    elif ! git -C "$workspace" diff --cached --quiet 2>/dev/null; then
        has_changes=true
    elif [ -n "$(git -C "$workspace" ls-files --others --exclude-standard 2>/dev/null)" ]; then
        has_changes=true
    fi

    if [ "$has_changes" = false ]; then
        log "No changes to commit"
        agent_write_result "$worker_dir" "PASS" '{"commit_sha":"","push_status":"no_changes"}'
        return 0
    fi

    # Get current branch
    local current_branch
    current_branch=$(git -C "$workspace" rev-parse --abbrev-ref HEAD 2>/dev/null)

    if [ "$current_branch" = "HEAD" ]; then
        log_error "Not on a branch (detached HEAD state)"
        agent_write_result "$worker_dir" "FAIL" '{}' '["Detached HEAD - not on a branch"]'
        return 1
    fi

    log "Committing changes on branch: $current_branch"

    # Stage all changes
    if ! git -C "$workspace" add -A 2>&1; then
        log_error "Failed to stage changes"
        agent_write_result "$worker_dir" "FAIL" '{}' '["Failed to stage changes"]'
        return 1
    fi

    # Set git author/committer identity
    export GIT_AUTHOR_NAME="Ralph Wiggum"
    export GIT_AUTHOR_EMAIL="ralph@wiggum.cc"
    export GIT_COMMITTER_NAME="Ralph Wiggum"
    export GIT_COMMITTER_EMAIL="ralph@wiggum.cc"

    # Check for resolution plan to customize commit message
    if [ -f "$worker_dir/resolution-plan.md" ]; then
        commit_message="fix: Resolve merge conflicts per coordination plan

Automated resolution following multi-PR coordination plan."
    fi

    # Create commit
    local commit_output
    if ! commit_output=$(git -C "$workspace" commit --no-gpg-sign -m "$commit_message" 2>&1); then
        log_error "Failed to create commit: $commit_output"
        agent_write_result "$worker_dir" "FAIL" '{}' '["Commit failed: '"${commit_output:0:200}"'"]'
        return 1
    fi

    # Get commit SHA
    local commit_sha
    commit_sha=$(git -C "$workspace" rev-parse HEAD 2>/dev/null)
    log "Created commit: $commit_sha"

    # Push to remote
    log "Pushing to remote..."
    local push_output
    if ! push_output=$(git -C "$workspace" push 2>&1); then
        # Check if push failed due to rejected (needs pull)
        if echo "$push_output" | grep -qE "(rejected|non-fast-forward)"; then
            log_error "Push rejected - remote has changes"
            agent_write_result "$worker_dir" "FAIL" \
                "{\"commit_sha\":\"$commit_sha\",\"push_status\":\"rejected\"}" \
                '["Push rejected - remote has changes"]'
            return 0  # FAIL is a valid gate result
        fi

        log_error "Failed to push: $push_output"
        agent_write_result "$worker_dir" "FAIL" \
            "{\"commit_sha\":\"$commit_sha\"}" \
            '["Push failed: '"${push_output:0:200}"'"]'
        return 1
    fi

    log "Successfully pushed to $current_branch"
    agent_write_result "$worker_dir" "PASS" \
        "{\"commit_sha\":\"$commit_sha\",\"push_status\":\"success\",\"branch\":\"$current_branch\"}"
    return 0
}
