#!/usr/bin/env bash
# git-operations.sh - Git commit and PR creation for workers
#
# Provides functions for creating commits and pull requests from worker workspaces.
# Used by lib/worker.sh and lib/worker/cmd-resume.sh for consistent git operations.
set -euo pipefail

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"
source "$WIGGUM_HOME/lib/utils/calculate-cost.sh"
source "$WIGGUM_HOME/lib/worker/git-state.sh"
source "$WIGGUM_HOME/lib/github/issue-state.sh"
source "$WIGGUM_HOME/lib/github/pr-labels.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/utils/activity-log.sh"

# =============================================================================
# CONFLICT MARKER DETECTION
# =============================================================================

# Check if staged files contain git conflict markers
#
# Scans the staged diff for standard conflict markers (<<<<<<< , =======, >>>>>>> ).
# Must be called AFTER `git add` and BEFORE `git commit`.
#
# Args:
#   workspace - Directory containing the git repository
#
# Returns: 0 if conflict markers found, 1 if clean
# Echoes: list of files with markers (one per line) when markers found
git_staged_has_conflict_markers() {
    local workspace="$1"

    # Search staged diff for added lines matching conflict markers.
    # Pattern: line starts with '+' (diff added-line prefix) followed by
    # exactly 7 marker characters and a space or end-of-line.
    local marker_files
    marker_files=$(git -C "$workspace" diff --cached --name-only \
        -G '^(<{7} |={7}$|>{7} )' 2>/dev/null || true)

    if [ -n "$marker_files" ]; then
        echo "$marker_files"
        return 0
    fi

    return 1
}

# Check if tracked files in the working tree contain conflict markers
#
# Unlike git_staged_has_conflict_markers (which requires staged files),
# this checks the working tree directly. Use when staging area may have
# been reset.
#
# Args:
#   workspace - Directory containing the git repository
#
# Returns: 0 if conflict markers found, 1 if clean
# Echoes: list of files with markers (one per line)
git_has_conflict_markers() {
    local workspace="$1"
    local marker_files
    marker_files=$(git -C "$workspace" grep -l '^<\{7\} \|^=\{7\}$\|^>\{7\} ' 2>/dev/null || true)
    if [ -n "$marker_files" ]; then
        echo "$marker_files"
        return 0
    fi
    return 1
}

# Check if conflict markers are from an active git merge/rebase (not just stale markers in code)
#
# Returns: 0 if an active merge/rebase is in progress, 1 otherwise
git_is_merge_in_progress() {
    local workspace="$1"

    # Check for active merge, rebase, or cherry-pick state
    [ -f "$workspace/.git/MERGE_HEAD" ] && return 0
    [ -d "$workspace/.git/rebase-merge" ] && return 0
    [ -d "$workspace/.git/rebase-apply" ] && return 0
    [ -f "$workspace/.git/CHERRY_PICK_HEAD" ] && return 0

    # For worktrees, .git is a file pointing to the actual gitdir
    if [ -f "$workspace/.git" ]; then
        local gitdir
        gitdir=$(git -C "$workspace" rev-parse --git-dir 2>/dev/null)
        if [ -n "$gitdir" ]; then
            [ -f "$gitdir/MERGE_HEAD" ] && return 0
            [ -d "$gitdir/rebase-merge" ] && return 0
            [ -d "$gitdir/rebase-apply" ] && return 0
            [ -f "$gitdir/CHERRY_PICK_HEAD" ] && return 0
        fi
    fi

    return 1
}

# Classify a commit failure for pipeline dispatch
#
# All commit failures with conflict markers are treated as FIX. The previous
# agent (via default_jump: prev) will be re-run and is responsible for
# resolving any conflict markers in the workspace.
#
# Args:
#   workspace - Directory containing the git repository
#
# Returns: always echoes "FIX"
git_classify_commit_failure() {
    local workspace="$1"
    # All commit failures are treated as FIX — agents are responsible for
    # resolving any conflict markers in the workspace.
    echo "FIX"
    return 0
}

# =============================================================================
# PRE-FLIGHT MERGE CONFLICT CHECK
# =============================================================================

# Check if a workspace can merge cleanly with a target branch
#
# Performs a trial merge (--no-commit) against the target branch to detect
# conflicts BEFORE starting a full pipeline. If conflicts exist, the worker
# should fail fast rather than waste pipeline stages on work that can't be
# committed.
#
# Args:
#   workspace - Directory containing the git worktree
#   target_branch - Branch to check mergeability against (default: origin/main)
#
# Returns: 0 if mergeable (no conflicts), 1 if conflicts detected
# Echoes: conflicted file list when conflicts found
git_worktree_check_mergeable() {
    local workspace="$1"
    local target_branch="${2:-origin/main}"

    if [ ! -d "$workspace" ]; then
        log_error "git_worktree_check_mergeable: workspace not found: $workspace"
        return 1
    fi

    # Fetch latest target branch state
    git -C "$workspace" fetch origin 2>/dev/null || {
        log_warn "git_worktree_check_mergeable: fetch failed, skipping check"
        return 0
    }

    # Check if target branch exists
    if ! git -C "$workspace" rev-parse --verify "$target_branch" >/dev/null 2>&1; then
        log_debug "git_worktree_check_mergeable: $target_branch not found, skipping check"
        return 0
    fi

    # Check if worktree HEAD already includes the target (no divergence)
    if git -C "$workspace" merge-base --is-ancestor "$target_branch" HEAD 2>/dev/null; then
        log_debug "git_worktree_check_mergeable: HEAD already includes $target_branch"
        return 0
    fi

    # Attempt a trial merge (--no-commit, --no-ff) to detect conflicts
    local merge_exit=0
    git -C "$workspace" merge --no-commit --no-ff "$target_branch" >/dev/null 2>&1 || merge_exit=$?

    if [ "$merge_exit" -eq 0 ]; then
        # Merge succeeded - abort the trial merge to restore original state
        git -C "$workspace" merge --abort 2>/dev/null || git -C "$workspace" reset --merge 2>/dev/null || true
        log_debug "git_worktree_check_mergeable: clean merge with $target_branch"
        return 0
    fi

    # Merge failed - extract conflicted files
    local conflict_files
    conflict_files=$(git -C "$workspace" diff --name-only --diff-filter=U 2>/dev/null || true)

    # Abort the trial merge to restore original state
    git -C "$workspace" merge --abort 2>/dev/null || git -C "$workspace" reset --merge 2>/dev/null || true

    if [ -n "$conflict_files" ]; then
        echo "$conflict_files"
    fi

    return 1
}

# =============================================================================
# GIT IDENTITY HELPER
# =============================================================================

# Set git author/committer identity from centralized config
# Loads config if not already loaded, then exports GIT_* environment variables
#
# Usage: Call before any git commit/merge operation
git_set_identity() {
    # Load config if not already loaded
    if [ -z "${WIGGUM_GIT_AUTHOR_NAME:-}" ]; then
        load_git_config
    fi

    export GIT_AUTHOR_NAME="$WIGGUM_GIT_AUTHOR_NAME"
    export GIT_AUTHOR_EMAIL="$WIGGUM_GIT_AUTHOR_EMAIL"
    export GIT_COMMITTER_NAME="$WIGGUM_GIT_AUTHOR_NAME"
    export GIT_COMMITTER_EMAIL="$WIGGUM_GIT_AUTHOR_EMAIL"
}

# =============================================================================
# READ-ONLY AGENT GIT SAFETY
# =============================================================================
# These functions provide git-based workspace protection for read-only agents.
# Before a read-only agent runs, we commit all uncommitted changes to create
# a checkpoint. After the agent exits, we revert to that checkpoint, discarding
# any changes the agent may have made (which it shouldn't have).

# List of agent types that are read-only (should not modify workspace)
_GIT_READONLY_AGENTS="engineering.security-audit engineering.validation-review product.plan-mode engineering.code-review"

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
        # Security: Unstage common sensitive file patterns
        git reset HEAD -- '.env' '.env.*' '*.pem' '*.key' 'credentials.json' '.secrets' 2>/dev/null || true

        # Check if there are staged changes to commit
        if ! git diff --staged --quiet; then
            # Set git identity for checkpoint commit
            git_set_identity

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
        timestamp=$(epoch_now)
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

        # Security: Unstage common sensitive file patterns that should never be committed
        git reset HEAD -- '.env' '.env.*' '*.pem' '*.key' 'credentials.json' '.secrets' 2>/dev/null || true

        # Guard: refuse to commit conflict markers
        local marker_files
        if marker_files=$(git_staged_has_conflict_markers "$workspace"); then
            log_error "Conflict markers detected in staged files — aborting finalization commit"
            log_error "Files with markers:"
            echo "$marker_files" | while read -r f; do log_error "  $f"; done
            git reset HEAD -- . >/dev/null 2>&1 || true
            GIT_COMMIT_BRANCH=""
            return 1
        fi

        # Create commit message
        local commit_msg="${task_id}: ${task_desc}

Worker: $worker_id
Priority: ${task_priority}
Completed by Ralph Wiggum autonomous worker."

        # Set git author/committer identity for this commit
        git_set_identity

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

    # Look up linked GitHub issue for this task
    local closes_section=""
    local ralph_dir="$project_dir/.ralph"
    if [ -f "$ralph_dir/github-sync-state.json" ]; then
        local task_entry
        task_entry=$(github_sync_state_get_task "$ralph_dir" "$task_id")
        if [ "$task_entry" != "null" ]; then
            local issue_number
            issue_number=$(echo "$task_entry" | jq -r '.issue_number // empty')
            if [ -n "$issue_number" ]; then
                closes_section="
Closes #${issue_number}
"
            fi
        fi
    fi

    local pr_body="$prd_body

# Changelog

${changes_section}
${closes_section}${metrics_section}
---
🤖 Generated by [Chief Wiggum](https://github.com/0kenx/chief-wiggum)"

    # Create the PR with timeout
    # Strip redundant task ID / "Task:" prefix from description before building title
    local clean_desc="$task_desc"
    clean_desc="${clean_desc#Task: }"
    clean_desc="${clean_desc#"$task_id"}"
    clean_desc="${clean_desc# - }"
    clean_desc="${clean_desc#: }"
    clean_desc="${clean_desc# }"

    local gh_timeout="${WIGGUM_GH_TIMEOUT:-30}"
    if timeout "$gh_timeout" gh pr create \
        --title "$task_id: $clean_desc" \
        --body "$pr_body" \
        --base main \
        --head "$branch_name" 2>&1; then

        log "Created Pull Request for $task_id"

        # Get and save PR URL and number (with timeout)
        local pr_info
        pr_info=$(timeout "$gh_timeout" gh pr view "$branch_name" --json url,number 2>/dev/null || echo '{}')
        GIT_PR_URL=$(echo "$pr_info" | jq -r '.url // "N/A"')
        local pr_number
        pr_number=$(echo "$pr_info" | jq -r '.number // empty')

        echo "$GIT_PR_URL" > "$worker_dir/pr_url.txt"

        # Save PR number to git-state.json for merge flow
        # Fallback: extract from URL if gh pr view failed
        if [ -z "$pr_number" ] && [ "$GIT_PR_URL" != "N/A" ]; then
            pr_number=$(echo "$GIT_PR_URL" | grep -oE '[0-9]+$' || true)
            [ -n "$pr_number" ] && log "Extracted PR number from URL: $pr_number"
        fi
        if [ -n "$pr_number" ]; then
            git_state_set_pr "$worker_dir" "$pr_number" 2>/dev/null || log_warn "Failed to save PR number to git-state.json"

            # Add pending-approval status label to the new PR
            local pr_status_label
            pr_status_label=$(github_sync_get_status_label "P")
            if [ -n "$pr_status_label" ]; then
                github_pr_add_label "$pr_number" "$pr_status_label" || true
            fi
        else
            log_warn "Could not determine PR number - conflict resolution may not work"
        fi

        activity_log "pr.created" "" "$task_id" "pr_url=$GIT_PR_URL" "branch=$branch_name"

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

# Verify that a commit has been pushed to GitHub
# Args: <workspace> <task_id>
# Returns: 0 if commit is pushed (regardless of PR status), 1 if not
git_verify_pushed() {
    local workspace="$1"
    local task_id="$2"
    local gh_timeout="${WIGGUM_GH_TIMEOUT:-30}"

    # Get local commit from worktree
    local local_commit remote_commit pr_exists
    local_commit=$(git -C "$workspace" rev-parse HEAD 2>/dev/null)

    # Check if commit exists on remote branch (with timeout)
    remote_commit=$(timeout "$gh_timeout" git ls-remote --heads origin "task/$task_id-*" 2>/dev/null | head -1 | cut -f1)

    # Primary verification: commit is pushed to remote
    if [ -n "$remote_commit" ] && [ "$local_commit" = "$remote_commit" ]; then
        # Optionally check PR (non-blocking, for logging only)
        pr_exists=$(timeout "$gh_timeout" gh pr list --head "task/$task_id-*" --json number -q '.[0].number' 2>/dev/null || true)
        if [ -n "$pr_exists" ]; then
            log_debug "Verified: commit $local_commit pushed and PR #$pr_exists exists on GitHub"
        else
            log_debug "Verified: commit $local_commit pushed (PR not yet visible or search pattern mismatch)"
        fi
        return 0
    else
        log "GitHub push verification failed: local=$local_commit, remote=${remote_commit:-none}"
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
    task_desc=$(grep -F "**[$task_id]**" "$RALPH_DIR/kanban.md" 2>/dev/null | sed 's/.*\*\*\[.*\]\*\* //' | head -1) || true
    task_priority=$(grep -F -A2 "**[$task_id]**" "$RALPH_DIR/kanban.md" 2>/dev/null | grep "Priority:" | sed 's/.*Priority: //') || true

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
