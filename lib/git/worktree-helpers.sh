#!/usr/bin/env bash
# worktree-helpers.sh - Git worktree management for isolated agent workspaces
#
# Provides functions to setup and cleanup git worktrees for agent isolation.
# Extracted from worker.sh to be reusable across different agent types.
set -euo pipefail

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/git/git-operations.sh"

# Global variable set by setup_worktree
WORKTREE_PATH=""

# Setup a git worktree for isolated agent work
#
# Args:
#   project_dir - The project root directory (must be a git repo)
#   worker_dir  - The worker directory to create workspace in
#
# Returns: 0 on success, 1 on failure
# Sets: WORKTREE_PATH to the created workspace path
setup_worktree() {
    local project_dir="$1"
    local worker_dir="$2"

    if [ -z "$project_dir" ] || [ -z "$worker_dir" ]; then
        log_error "setup_worktree: missing required parameters"
        return 1
    fi

    cd "$project_dir" || {
        log_error "setup_worktree: cannot access project directory: $project_dir"
        return 1
    }

    local workspace="$worker_dir/workspace"

    # Check if workspace already exists (resume case)
    if [ -d "$workspace" ]; then
        log_debug "Worktree already exists at $workspace, reusing"
        WORKTREE_PATH="$workspace"
        export WORKER_WORKSPACE="$workspace"
        export CLAUDE_HOOKS_CONFIG="$WIGGUM_HOME/hooks/worker-hooks.json"
        return 0
    fi

    log_debug "Creating git worktree at $workspace"
    git worktree add "$workspace" HEAD 2>&1 | tee -a "$worker_dir/worker.log"

    if [ ! -d "$workspace" ]; then
        log_error "setup_worktree: failed to create worktree at $workspace"
        return 1
    fi

    # Setup environment for workspace boundary enforcement
    export WORKER_WORKSPACE="$workspace"
    export CLAUDE_HOOKS_CONFIG="$WIGGUM_HOME/hooks/worker-hooks.json"

    WORKTREE_PATH="$workspace"
    export WORKTREE_PATH
    log_debug "Worktree created successfully at $workspace"
    return 0
}

# Cleanup git worktree
#
# Args:
#   project_dir  - The project root directory
#   worker_dir   - The worker directory containing the workspace
#   final_status - The final task status (COMPLETE or FAILED)
#   task_id      - The task ID for push verification
#
# Returns: 0 on success
# Note: Only removes worktree if task is COMPLETE and verified pushed
cleanup_worktree() {
    local project_dir="$1"
    local worker_dir="$2"
    local final_status="$3"
    local task_id="$4"

    cd "$project_dir" || {
        log_error "cleanup_worktree: cannot access project directory: $project_dir"
        return 1
    }

    local workspace="$worker_dir/workspace"

    # Check if workspace exists
    if [ ! -d "$workspace" ]; then
        log_debug "cleanup_worktree: workspace already removed or doesn't exist"
        return 0
    fi

    local can_cleanup=false

    # Only cleanup on successful completion with verified push
    if [ "$final_status" = "COMPLETE" ]; then
        # Use shared library to verify push status
        if git_verify_pushed "$workspace" "$task_id"; then
            can_cleanup=true
        fi
    fi

    if [ "$can_cleanup" = true ]; then
        log_debug "Removing git worktree"
        git worktree remove "$workspace" --force 2>&1 | tee -a "$worker_dir/worker.log" || true
    else
        log "Preserving worktree for debugging: $workspace"
    fi

    return 0
}
