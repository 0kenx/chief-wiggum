#!/usr/bin/env bash
# worktree-helpers.sh - Git worktree management for isolated agent workspaces
#
# Provides functions to setup and cleanup git worktrees for agent isolation.
# Extracted from worker.sh to be reusable across different agent types.
set -euo pipefail

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/git/git-operations.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/safe-path.sh"

# Global variable set by setup_worktree
WORKTREE_PATH=""

# Setup a git worktree for isolated agent work
#
# Creates worktree in DETACHED HEAD state at current commit SHA, then creates
# a task-specific branch to avoid branch contention between concurrent workers.
#
# Args:
#   project_dir - The project root directory (must be a git repo)
#   worker_dir  - The worker directory to create workspace in
#   task_id     - (optional) Task ID for branch naming; extracted from worker_dir if not provided
#
# Returns: 0 on success, 1 on failure
# Sets: WORKTREE_PATH to the created workspace path
setup_worktree() {
    local project_dir="$1"
    local worker_dir="$2"
    local task_id="${3:-}"

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
        _write_workspace_hooks_config "$workspace"
        return 0
    fi

    # Extract task_id from worker dir if not provided
    if [ -z "$task_id" ]; then
        task_id=$(basename "$worker_dir" | sed -E 's/worker-([A-Za-z]{2,10}-[0-9]{1,4})-.*/\1/')
    fi

    # Get commit SHA (not branch ref) - avoids branch contention
    local commit_sha
    commit_sha=$(git rev-parse HEAD 2>/dev/null)
    if [ -z "$commit_sha" ]; then
        log_error "setup_worktree: failed to get commit SHA"
        return 1
    fi

    log_debug "Creating git worktree at $workspace (detached HEAD at $commit_sha)"

    # Create worktree with DETACHED HEAD - avoids "branch already used" errors
    if ! git worktree add --detach "$workspace" "$commit_sha" 2>&1 | tee -a "$worker_dir/worker.log"; then
        log_error "setup_worktree: failed to create detached worktree"
        return 1
    fi

    if [ ! -d "$workspace" ]; then
        log_error "setup_worktree: workspace directory not created at $workspace"
        return 1
    fi

    # Create task-specific branch in worktree (avoids branch contention)
    if [ -n "$task_id" ]; then
        local branch_name
        branch_name="task/${task_id}-$(epoch_now)"
        log_debug "Creating task branch: $branch_name"
        if ! (cd "$workspace" && git checkout -b "$branch_name" 2>&1) | tee -a "$worker_dir/worker.log"; then
            log_warn "setup_worktree: failed to create branch $branch_name, continuing with detached HEAD"
        fi
    fi

    # Enable conflict-reduction features:
    # - rerere: records resolutions so identical conflicts auto-resolve on retry.
    #   Shared across worktrees via common .git object store.
    # - diff3: includes common ancestor in conflict markers, giving the resolver
    #   context about what the original code looked like before either side changed it.
    git -C "$workspace" config rerere.enabled true
    git -C "$workspace" config merge.conflictstyle diff3

    # Pre-flight merge conflict check: detect unresolvable conflicts with
    # the default branch BEFORE the pipeline starts. Failing fast here saves
    # an entire pipeline run on work that can't be committed.
    if [ "${WIGGUM_SKIP_MERGE_CHECK:-}" != "true" ]; then
        local default_branch
        default_branch=$(get_default_branch)
        local conflict_files
        if conflict_files=$(git_worktree_check_mergeable "$workspace" "origin/$default_branch"); then
            log_debug "Pre-flight merge check passed"
        else
            log_error "Pre-flight merge conflict detected — worktree cannot merge cleanly with origin/$default_branch"
            if [ -n "$conflict_files" ]; then
                log_error "Conflicting files:"
                echo "$conflict_files" | while read -r f; do log_error "  $f"; done
            fi
            log_error "Aborting worker setup to avoid wasting pipeline stages on unresolvable conflicts"
            # Clean up the worktree we just created
            cd "$project_dir" || true
            safe_path "$workspace" "workspace" || return 1
            git worktree remove "$workspace" --force 2>/dev/null || rm -rf "$workspace"
            return 1
        fi
    fi

    # Setup environment for workspace boundary enforcement
    export WORKER_WORKSPACE="$workspace"
    _write_workspace_hooks_config "$workspace"

    WORKTREE_PATH="$workspace"
    export WORKTREE_PATH
    log_debug "Worktree created successfully at $workspace"
    return 0
}

# Write Claude hooks configuration into workspace settings
#
# Creates .claude/settings.local.json in the workspace with PreToolUse hooks
# that enforce workspace boundary constraints. This is the documented way to
# register hooks with Claude Code (via project settings files).
#
# Args:
#   workspace - Path to the workspace directory
_write_workspace_hooks_config() {
    local workspace="$1"

    mkdir -p "$workspace/.claude"

    # Write settings with hooks using resolved WIGGUM_HOME path
    local hooks_dir="$WIGGUM_HOME/hooks/callbacks"
    cat > "$workspace/.claude/settings.local.json" << EOF
{
  "permissions": {
    "allow": [
      "Bash(tail:*)"
    ]
  },
  "hooks": {
    "PreToolUse": [
      {
        "matcher": "Edit|Write|Bash|Read|Glob|Grep",
        "hooks": [
          {
            "type": "command",
            "command": "bash ${hooks_dir}/validate-workspace-path.sh"
          }
        ]
      },
      {
        "matcher": "Task",
        "hooks": [
          {
            "type": "command",
            "command": "bash ${hooks_dir}/inject-workspace-boundary.sh"
          }
        ]
      }
    ]
  }
}
EOF

    log_debug "Wrote hooks config to $workspace/.claude/settings.local.json"
}

# Setup a git worktree from a specific remote branch
#
# Used for resuming work on PRs where the local workspace was cleaned up.
# Fetches the branch from origin and creates a worktree tracking it.
#
# Args:
#   project_dir - The project root directory (must be a git repo)
#   worker_dir  - The worker directory to create workspace in
#   branch      - The remote branch name (e.g., task/TASK-001-description)
#
# Returns: 0 on success, 1 on failure
# Sets: WORKTREE_PATH to the created workspace path
setup_worktree_from_branch() {
    local project_dir="$1"
    local worker_dir="$2"
    local branch="$3"

    if [ -z "$project_dir" ] || [ -z "$worker_dir" ] || [ -z "$branch" ]; then
        log_error "setup_worktree_from_branch: missing required parameters"
        return 1
    fi

    cd "$project_dir" || {
        log_error "setup_worktree_from_branch: cannot access project directory: $project_dir"
        return 1
    }

    local workspace="$worker_dir/workspace"

    # Check if workspace already exists
    if [ -d "$workspace" ]; then
        log_debug "Worktree already exists at $workspace, reusing"
        WORKTREE_PATH="$workspace"
        export WORKER_WORKSPACE="$workspace"
        _write_workspace_hooks_config "$workspace"
        return 0
    fi

    # Fetch the branch from origin
    log_debug "Fetching branch $branch from origin"
    if ! git fetch origin "$branch" 2>&1 | tee -a "$worker_dir/worker.log"; then
        log_error "setup_worktree_from_branch: failed to fetch branch $branch"
        return 1
    fi

    # Prune stale worktrees (handles case where directory was deleted but worktree is still registered)
    git worktree prune 2>/dev/null || true

    # Create worktree tracking the remote branch
    log_debug "Creating git worktree at $workspace from origin/$branch"
    if ! git worktree add "$workspace" "origin/$branch" 2>&1 | tee -a "$worker_dir/worker.log"; then
        log_error "setup_worktree_from_branch: failed to create worktree from $branch"
        return 1
    fi

    # Setup local branch tracking remote
    (
        cd "$workspace" || exit 1
        git checkout -B "$branch" "origin/$branch" 2>&1 | tee -a "$worker_dir/worker.log"
    )

    if [ ! -d "$workspace" ]; then
        log_error "setup_worktree_from_branch: workspace not created at $workspace"
        return 1
    fi

    # Enable conflict-reduction features (same as setup_worktree)
    git -C "$workspace" config rerere.enabled true
    git -C "$workspace" config merge.conflictstyle diff3

    # Setup environment for workspace boundary enforcement
    export WORKER_WORKSPACE="$workspace"
    _write_workspace_hooks_config "$workspace"

    WORKTREE_PATH="$workspace"
    export WORKTREE_PATH
    log_debug "Worktree created successfully at $workspace from branch $branch"
    return 0
}

# Setup a worktree and recover work from a previously failed worker's branch.
#
# Creates a fresh worktree (via setup_worktree), then cherry-picks
# implementation commits from the old branch. This salvages expensive LLM
# work when a worker failed at a post-implementation stage (test, validation)
# so the new worker doesn't start from scratch.
#
# Falls back to a clean worktree if cherry-pick fails (conflicts, missing
# branch, etc.) — the caller always gets a usable worktree.
#
# Args:
#   project_dir     - The project root directory
#   worker_dir      - The NEW worker directory to create workspace in
#   task_id         - Task ID for branch naming
#   old_branch      - Branch name from the previous failed worker
#
# Returns: 0 on success (with or without recovery), 1 on worktree failure
# Sets: WORKTREE_PATH, CHERRY_PICK_RECOVERED (count or empty)
setup_worktree_with_recovery() {
    local project_dir="$1"
    local worker_dir="$2"
    local task_id="$3"
    local old_branch="$4"

    CHERRY_PICK_RECOVERED=""
    export CHERRY_PICK_RECOVERED

    # Create fresh worktree first (standard flow)
    if ! setup_worktree "$project_dir" "$worker_dir" "$task_id"; then
        return 1
    fi

    local workspace="$worker_dir/workspace"

    # Attempt cherry-pick recovery from the old branch
    if [ -n "$old_branch" ]; then
        if git_cherry_pick_recovery "$workspace" "$old_branch" 2>/dev/null; then
            CHERRY_PICK_RECOVERED="$GIT_CHERRY_PICK_COUNT"
        else
            log_debug "Cherry-pick recovery from $old_branch did not apply — starting fresh"
        fi
    fi

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
# Note: Only removes worktree if task is COMPLETE, verified pushed, AND no open PR.
#       If a PR exists, the worktree is preserved for potential PR comment fixes.
#       Worktree cleanup for PRs happens in merge-manager when the PR is merged.
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

    # Only cleanup on successful completion with verified push AND no open PR
    # If a PR exists, the worktree must be preserved for potential PR comment fixes
    # The worktree will be cleaned up by merge-manager when the PR is merged
    if [ "$final_status" = "COMPLETE" ]; then
        # Check if there's an open PR for this task
        local has_open_pr=false
        if [ -f "$worker_dir/pr_url.txt" ]; then
            local pr_url
            pr_url=$(cat "$worker_dir/pr_url.txt")
            if [ -n "$pr_url" ] && [ "$pr_url" != "N/A" ]; then
                has_open_pr=true
            fi
        fi

        if [ "$has_open_pr" = true ]; then
            # PR exists - preserve worktree for potential comment fixes
            log "Preserving worktree for PR review cycle: $workspace"
            can_cleanup=false
        elif git_verify_pushed "$workspace" "$task_id"; then
            # No PR, but changes pushed (direct commit) - safe to clean up
            can_cleanup=true
        fi
    fi

    if [ "$can_cleanup" = true ]; then
        log_debug "Removing git worktree"
        git worktree remove "$workspace" --force 2>&1 | tee -a "$worker_dir/worker.log" || true
    elif [ "$final_status" != "COMPLETE" ]; then
        log "Preserving worktree for debugging (status: $final_status): $workspace"
    fi

    return 0
}
