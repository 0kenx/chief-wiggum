#!/usr/bin/env bash
# git-operations.sh - Git commit and PR creation for workers
#
# Provides functions for creating commits and pull requests from worker workspaces.
# Used by lib/worker.sh and bin/wiggum-resume for consistent git operations.
set -euo pipefail

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/utils/calculate-cost.sh"

# =============================================================================
# READ-ONLY AGENT GIT SAFETY
# =============================================================================
# These functions provide git-based workspace protection for read-only agents.
# Before a read-only agent runs, we commit all uncommitted changes to create
# a checkpoint. After the agent exits, we revert to that checkpoint, discarding
# any changes the agent may have made (which it shouldn't have).

# List of agent types that are read-only (should not modify workspace)
_GIT_READONLY_AGENTS="security-audit validation-review plan-mode code-review"

# Check if an agent type is read-only
# Args: <agent_type>
# Returns: 0 if read-only, 1 if not
git_is_readonly_agent() {
    local agent_type="$1"
    [[ " $_GIT_READONLY_AGENTS " == *" $agent_type "* ]]
}

# Create a git checkpoint before running a read-only agent
# Commits all uncommitted changes so we can revert after the agent exits
#
# Args: <workspace>
# Sets: GIT_SAFETY_CHECKPOINT_SHA (commit SHA to revert to)
# Returns: 0 on success, 1 on failure
git_safety_checkpoint() {
    local workspace="$1"

    cd "$workspace" || {
        log_error "git_safety_checkpoint: Failed to cd to workspace: $workspace"
        GIT_SAFETY_CHECKPOINT_SHA=""
        return 1
    }

    # Store current HEAD as checkpoint (before any potential commit)
    local current_sha
    current_sha=$(git rev-parse HEAD 2>/dev/null)

    # Check if there are uncommitted changes
    if ! git diff --quiet || ! git diff --cached --quiet || [ -n "$(git ls-files --others --exclude-standard)" ]; then
        # Stage all changes
        git add -A 2>/dev/null || true

        # Check if there are staged changes to commit
        if ! git diff --staged --quiet; then
            # Set git identity for checkpoint commit
            export GIT_AUTHOR_NAME="Ralph Wiggum"
            export GIT_AUTHOR_EMAIL="ralph@wiggum.local"
            export GIT_COMMITTER_NAME="Ralph Wiggum"
            export GIT_COMMITTER_EMAIL="ralph@wiggum.local"

            # Create checkpoint commit
            if git commit --no-gpg-sign -m "chore: checkpoint before read-only agent" >/dev/null 2>&1; then
                current_sha=$(git rev-parse HEAD 2>/dev/null)
                log_debug "Created checkpoint commit: $current_sha"
            else
                log_warn "git_safety_checkpoint: Failed to create checkpoint commit"
            fi
        fi
    fi

    GIT_SAFETY_CHECKPOINT_SHA="$current_sha"
    log_debug "Git safety checkpoint set: $GIT_SAFETY_CHECKPOINT_SHA"
    return 0
}

# Restore workspace to checkpoint after read-only agent exits
# Discards any changes made by the agent (which shouldn't have made any)
#
# Args: <workspace> <checkpoint_sha>
# Returns: 0 on success, 1 on failure
git_safety_restore() {
    local workspace="$1"
    local checkpoint_sha="$2"

    if [ -z "$checkpoint_sha" ]; then
        log_warn "git_safety_restore: No checkpoint SHA provided, skipping restore"
        return 0
    fi

    cd "$workspace" || {
        log_error "git_safety_restore: Failed to cd to workspace: $workspace"
        return 1
    }

    # Check current state
    local current_sha
    current_sha=$(git rev-parse HEAD 2>/dev/null)

    # Check if there are any uncommitted changes (agent shouldn't have made any)
    local has_changes=false
    if ! git diff --quiet || ! git diff --cached --quiet || [ -n "$(git ls-files --others --exclude-standard)" ]; then
        has_changes=true
        log_warn "Read-only agent left uncommitted changes - discarding"
    fi

    # Check if HEAD moved (agent shouldn't have committed)
    if [ "$current_sha" != "$checkpoint_sha" ]; then
        log_warn "Read-only agent moved HEAD from $checkpoint_sha to $current_sha - resetting"
        has_changes=true
    fi

    # Restore to checkpoint if anything changed
    if [ "$has_changes" = true ]; then
        # Hard reset to checkpoint (discards all changes)
        if git reset --hard "$checkpoint_sha" >/dev/null 2>&1; then
            # Clean untracked files
            git clean -fd >/dev/null 2>&1 || true
            log "Restored workspace to checkpoint: $checkpoint_sha"
        else
            log_error "git_safety_restore: Failed to reset to checkpoint $checkpoint_sha"
            return 1
        fi
    else
        log_debug "Workspace unchanged, no restore needed"
    fi

    return 0
}

# Create a commit in the worker workspace
# Args: <workspace> <task_id> <task_desc> <task_priority> <worker_id>
# Sets: GIT_COMMIT_BRANCH (branch name on success, empty on failure)
# Returns: 0 on success, 1 on failure
git_create_commit() {
    local workspace="$1"
    local task_id="$2"
    local task_desc="$3"
    local task_priority="${4:-MEDIUM}"
    local worker_id="$5"

    cd "$workspace" || {
        log_error "Failed to cd to workspace: $workspace"
        GIT_COMMIT_BRANCH=""
        return 1
    }

    # Check if there are uncommitted changes
    local has_uncommitted_changes=false
    if ! git diff --quiet || ! git diff --cached --quiet || [ -n "$(git ls-files --others --exclude-standard)" ]; then
        has_uncommitted_changes=true
    fi

    # Check if already on a task branch
    local current_branch
    current_branch=$(git rev-parse --abbrev-ref HEAD 2>/dev/null)
    local branch_name

    if [[ "$current_branch" == task/* ]]; then
        # Already on a task branch - use it
        branch_name="$current_branch"
        log "Using existing branch: $branch_name"
    else
        # Create a unique branch for this task attempt
        local timestamp
        timestamp=$(date +%s)
        branch_name="task/$task_id-$timestamp"
        log "Creating new branch: $branch_name"

        if ! git checkout -b "$branch_name" 2>&1; then
            log_error "Failed to create branch $branch_name"
            GIT_COMMIT_BRANCH=""
            return 1
        fi
    fi

    # If there are uncommitted changes, stage and commit them
    if [ "$has_uncommitted_changes" = true ]; then
        # Stage all changes
        git add -A

        # Create commit message
        local commit_msg="${task_id}: ${task_desc}

Worker: $worker_id
Priority: ${task_priority}
Completed by Ralph Wiggum autonomous worker.

Co-Authored-By: Ralph Wiggum <ralph@wiggum.local>"

        # Set git author/committer identity for this commit
        export GIT_AUTHOR_NAME="Ralph Wiggum"
        export GIT_AUTHOR_EMAIL="ralph@wiggum.local"
        export GIT_COMMITTER_NAME="Ralph Wiggum"
        export GIT_COMMITTER_EMAIL="ralph@wiggum.local"

        if ! git commit --no-gpg-sign -m "$commit_msg" 2>&1; then
            log_error "Failed to create commit"
            GIT_COMMIT_BRANCH=""
            return 1
        fi

        local commit_hash
        commit_hash=$(git rev-parse HEAD)
        log "Created commit: $commit_hash on branch $branch_name"
    else
        # No uncommitted changes - sub-agents already committed everything
        log "No uncommitted changes - sub-agents already committed all work"
    fi

    GIT_COMMIT_BRANCH="$branch_name"
    return 0
}

# Create a pull request for a worker's branch
# Args: <branch_name> <task_id> <task_desc> <worker_dir> [project_dir]
# Sets: GIT_PR_URL (PR URL on success, "N/A" on failure)
# Returns: 0 on success, 1 on failure
git_create_pr() {
    local branch_name="$1"
    local task_id="$2"
    local task_desc="$3"
    local worker_dir="$4"
    local project_dir="${5:-$PROJECT_DIR}"

    GIT_PR_URL="N/A"

    # Push the branch
    if ! git push -u origin "$branch_name" 2>&1; then
        log_error "Failed to push branch $branch_name"
        return 1
    fi

    log "Pushed branch $branch_name to remote"

    # Check if gh CLI is available
    if ! command -v gh &> /dev/null; then
        log "gh CLI not found, skipping PR creation. Branch pushed: $branch_name"
        return 1
    fi

    # Build PR body
    local changes_section="This PR contains the automated implementation of the task requirements."
    if [ -f "$worker_dir/summaries/summary.txt" ]; then
        changes_section=$(cat "$worker_dir/summaries/summary.txt")
    fi

    # Calculate and include metrics if available
    local metrics_section=""
    if [ -f "$worker_dir/worker.log" ]; then
        calculate_worker_cost "$worker_dir/worker.log" > "$worker_dir/metrics.txt" 2>&1 || true
        if [ -f "$worker_dir/metrics.txt" ]; then
            metrics_section="
## Metrics

\`\`\`
$(tail -n +3 "$worker_dir/metrics.txt")
\`\`\`
"
        fi
    fi

    # Read PRD for summary
    local prd_body=""
    if [ -f "$worker_dir/prd.md" ]; then
        prd_body=$(cat "$worker_dir/prd.md")
    fi

    local pr_body="$prd_body

# Changelog

${changes_section}
${metrics_section}
---
🤖 Generated by [Chief Wiggum](https://github.com/0kenx/chief-wiggum)"

    # Create the PR with timeout
    local gh_timeout="${WIGGUM_GH_TIMEOUT:-30}"
    if timeout "$gh_timeout" gh pr create \
        --title "$task_id: $task_desc" \
        --body "$pr_body" \
        --base main \
        --head "$branch_name" 2>&1; then

        log "Created Pull Request for $task_id"

        # Get and save PR URL (with timeout)
        GIT_PR_URL=$(timeout "$gh_timeout" gh pr view "$branch_name" --json url -q .url 2>/dev/null || echo "N/A")
        echo "$GIT_PR_URL" > "$worker_dir/pr_url.txt"
        return 0
    else
        local exit_code=$?
        if [ $exit_code -eq 124 ]; then
            log_error "PR creation timed out after ${gh_timeout}s"
        else
            log_error "Failed to create PR (gh CLI error), but branch is pushed"
        fi
        return 1
    fi
}

# Verify that a commit has been pushed and PR exists on GitHub
# Args: <workspace> <task_id>
# Returns: 0 if verified, 1 if not
git_verify_pushed() {
    local workspace="$1"
    local task_id="$2"
    local gh_timeout="${WIGGUM_GH_TIMEOUT:-30}"

    # Get local commit from worktree
    local local_commit remote_commit pr_exists
    local_commit=$(git -C "$workspace" rev-parse HEAD 2>/dev/null)

    # Check if commit exists on remote branch and PR exists (with timeout)
    remote_commit=$(timeout "$gh_timeout" git ls-remote --heads origin "task/$task_id-*" 2>/dev/null | head -1 | cut -f1)
    pr_exists=$(timeout "$gh_timeout" gh pr list --head "task/$task_id-*" --json number -q '.[0].number' 2>/dev/null)

    if [ -n "$remote_commit" ] && [ "$local_commit" = "$remote_commit" ] && [ -n "$pr_exists" ]; then
        log_debug "Verified: commit $local_commit pushed and PR #$pr_exists exists on GitHub"
        return 0
    else
        log "GitHub verification failed: local=$local_commit, remote=${remote_commit:-none}, pr=$([ -n "$pr_exists" ] && echo "#$pr_exists" || echo 'no')"
        return 1
    fi
}

# Full commit and PR workflow for a completed worker
# Args: <worker_dir> <task_id> <project_dir>
# Sets: GIT_COMMIT_BRANCH, GIT_PR_URL
# Returns: 0 on success, 1 on failure
git_finalize_worker() {
    local worker_dir="$1"
    local task_id="$2"
    local project_dir="$3"

    # Convert to absolute paths before cd changes working directory
    worker_dir=$(cd "$worker_dir" && pwd)
    project_dir=$(cd "$project_dir" && pwd)

    local workspace="$worker_dir/workspace"
    local worker_id
    worker_id=$(basename "$worker_dir")

    if [ ! -d "$workspace" ]; then
        log_error "Workspace not found: $workspace"
        return 1
    fi

    cd "$workspace" || return 1

    # Get task description and priority from kanban
    local task_desc task_priority
    task_desc=$(grep -F "**[$task_id]**" "$project_dir/.ralph/kanban.md" 2>/dev/null | sed 's/.*\*\*\[.*\]\*\* //' | head -1)
    task_priority=$(grep -F -A2 "**[$task_id]**" "$project_dir/.ralph/kanban.md" 2>/dev/null | grep "Priority:" | sed 's/.*Priority: //')

    # Create commit
    if ! git_create_commit "$workspace" "$task_id" "$task_desc" "$task_priority" "$worker_id"; then
        return 1
    fi

    # Create PR
    if ! git_create_pr "$GIT_COMMIT_BRANCH" "$task_id" "$task_desc" "$worker_dir" "$project_dir"; then
        # Branch was pushed but PR creation failed - partial success
        return 1
    fi

    return 0
}
