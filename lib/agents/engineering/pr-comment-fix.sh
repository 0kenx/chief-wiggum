#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: pr-comment-fix
# AGENT_DESCRIPTION: PR comment fix agent that addresses pull request review
#   feedback. Uses ralph loop pattern to iteratively fix issues raised by
#   reviewers. Reads comments from task-comments.md, makes code changes,
#   and tracks progress in comment-status.md. Can auto-commit and push fixes.
# REQUIRED_PATHS:
#   - task-comments.md : File containing PR review comments to address
#   - workspace        : Directory containing the code to modify
# OUTPUT_FILES:
#   - comment-status.md       : Status tracking file for addressed comments
#   - comment-fix-result.json : Contains PASS, FIX, FAIL, or SKIP
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "engineering.pr-comment-fix" "PR comment fix agent that addresses pull request review feedback"

# Required paths before agent can run
agent_required_paths() {
    echo "task-comments.md"
    echo "workspace"
}

# Source dependencies using base library helpers
agent_source_core
agent_source_ralph

# Source git state tracking
source "$WIGGUM_HOME/lib/worker/git-state.sh"

# Load review config on source
load_review_config

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    # Use config values (set by load_agent_config in agent-registry, with env var override)
    local max_iterations="${WIGGUM_COMMENT_FIX_MAX_ITERATIONS:-${AGENT_CONFIG_MAX_ITERATIONS:-10}}"
    local max_turns="${WIGGUM_COMMENT_FIX_MAX_TURNS:-${AGENT_CONFIG_MAX_TURNS:-30}}"

    local workspace="$worker_dir/workspace"
    local comments_file="$worker_dir/task-comments.md"
    local status_file="$worker_dir/reports/comment-status.md"

    # Record start time and log agent start
    local start_time
    start_time=$(date +%s)
    agent_log_start "$worker_dir" "$(basename "$worker_dir")"

    # Verify workspace exists
    if [ ! -d "$workspace" ]; then
        log_error "Workspace not found: $workspace"
        agent_log_complete "$worker_dir" 1 "$start_time"
        agent_write_result "$worker_dir" "FAIL" '{}' '["Workspace not found"]'
        return 1
    fi

    # Verify comments file exists
    if [ ! -f "$comments_file" ]; then
        log_error "Comments file not found: $comments_file"
        log_error "Run 'wiggum review task <pattern> sync' first"
        agent_log_complete "$worker_dir" 1 "$start_time"
        agent_write_result "$worker_dir" "FAIL" '{}' '["Comments file not found"]'
        return 1
    fi

    # Check if there are any comments to fix
    local comment_count
    comment_count=$(grep -c '^### ' "$comments_file" 2>/dev/null || echo "0")
    if [ "$comment_count" -eq 0 ]; then
        log "No comments found in $comments_file - nothing to fix"
        agent_setup_context "$worker_dir" "$workspace" "$project_dir"
        agent_log_complete "$worker_dir" 0 "$start_time"
        agent_write_result "$worker_dir" "SKIP" '{"comments_fixed":0,"comments_pending":0,"comments_skipped":0}'
        git_state_set "$worker_dir" "fix_completed" "engineering.pr-comment-fix" "No comments to fix"
        return 0
    fi

    log "Found $comment_count comment(s) to address"

    # Initialize status tracking if not exists or reset
    _init_comment_status "$comments_file" "$status_file"

    # Set up callback context using base library
    agent_setup_context "$worker_dir" "$workspace" "$project_dir"
    _FIX_COMMENTS_FILE="$comments_file"
    _FIX_STATUS_FILE="$status_file"

    log "Starting comment fix loop (max $max_iterations iterations, $max_turns turns/session)"

    # Use step ID from pipeline for session prefix
    local session_prefix="${WIGGUM_STEP_ID:-pr-fix}"

    # Run the fix loop
    run_ralph_loop \
        "$workspace" \
        "$(_get_system_prompt "$workspace")" \
        "_fix_user_prompt" \
        "_fix_completion_check" \
        "$max_iterations" \
        "$max_turns" \
        "$worker_dir" \
        "$session_prefix"

    local loop_result=$?

    # Auto commit and push if configured and loop succeeded
    local push_succeeded="false"
    local commit_sha=""
    local auto_commit="${WIGGUM_AUTO_COMMIT_AFTER_FIX:-${AGENT_CONFIG_AUTO_COMMIT:-true}}"
    if [ "$loop_result" -eq 0 ] && [ "$auto_commit" = "true" ]; then
        log "Auto-committing and pushing fixes..."
        if _commit_and_push_fixes "$workspace" "$worker_dir"; then
            push_succeeded="true"
            commit_sha=$(cd "$workspace" && git rev-parse HEAD 2>/dev/null || echo "")
            # Update task-comments.md with commit information
            _update_task_comments_with_commit "$comments_file" "$status_file" "$commit_sha"
        fi
    elif [ "$loop_result" -ne 0 ]; then
        log_warn "Fix loop did not complete successfully (exit code: $loop_result)"
    fi

    # Count comment statuses from status file
    local comments_fixed=0 comments_pending=0 comments_skipped=0
    if [ -f "$status_file" ]; then
        comments_fixed=$(grep -c '^\- \[x\]' "$status_file" 2>/dev/null || echo "0")
        comments_pending=$(grep -c '^\- \[ \]' "$status_file" 2>/dev/null || echo "0")
        comments_skipped=$(grep -c '^\- \[\*\]' "$status_file" 2>/dev/null || echo "0")
    fi

    # Determine gate_result
    local gate_result="FAIL"
    if [ "$loop_result" -eq 0 ] && [ "$comments_pending" -eq 0 ]; then
        gate_result="PASS"
    elif [ "$comments_fixed" -gt 0 ]; then
        gate_result="FIX"
    fi

    # Log completion and write structured result
    agent_log_complete "$worker_dir" "$loop_result" "$start_time"

    local outputs_json
    outputs_json=$(printf '{"commit_sha":"%s","push_succeeded":%s,"comments_fixed":%d,"comments_pending":%d,"comments_skipped":%d}' \
        "$commit_sha" "$push_succeeded" "$comments_fixed" "$comments_pending" "$comments_skipped")

    agent_write_result "$worker_dir" "$gate_result" "$outputs_json"

    # Update git state on success
    if [ "$gate_result" = "PASS" ]; then
        local state_reason="All comments addressed"
        if [ "$push_succeeded" = "true" ]; then
            state_reason="All comments addressed, push succeeded"
        fi
        git_state_set "$worker_dir" "fix_completed" "engineering.pr-comment-fix" "$state_reason"
    fi

    return $loop_result
}

# System prompt
_get_system_prompt() {
    local workspace="$1"

    cat << EOF
PR COMMENT FIX AGENT:

You address PR review feedback by making code changes.

WORKSPACE: $workspace
COMMENTS: ../task-comments.md (read-only)
STATUS: ../reports/comment-status.md (update as you fix)

## Fix Philosophy

* ADDRESS THE ACTUAL CONCERN - Understand what the reviewer wants, not just the literal words
* MINIMAL CHANGES - Fix the issue without unnecessary refactoring
* FOLLOW PATTERNS - Match existing code style and conventions
* ONE AT A TIME - Complete one fix fully before moving to the next

## Rules

* Read comment carefully before making changes
* Update status file AFTER each successful fix
* Stay within workspace directory
* If you disagree with feedback, still address it or explain why not
EOF
}

# User prompt callback (unified 4-arg signature)
_fix_user_prompt() {
    local iteration="$1"
    local output_dir="$2"
    # shellcheck disable=SC2034  # supervisor args unused but part of unified callback signature
    local _supervisor_dir="${3:-}"
    local _supervisor_feedback="${4:-}"

    # Always include the initial prompt to ensure full context after summarization
    cat << 'EOF'
PR COMMENT FIX TASK:

Address feedback from PR review comments.

## Process

1. **Read comments**: @../task-comments.md - understand what reviewers want
2. **Check status**: @../reports/comment-status.md - skip [x] items, fix [ ] items
3. **For each pending comment**:
   - Understand the concern (read surrounding context if needed)
   - Make the code change
   - Update status: `- [ ] Comment N` → `- [x] Comment N: <what you did>`
4. **Repeat** until no [ ] items remain

## Priority Order

1. **Bugs/Security** - Fix these first
2. **Requested Changes** - Reviewer explicitly asked for this
3. **Suggestions** - Nice-to-have improvements

## Status File Format

```markdown
- [x] Comment 123: Fixed null check as requested
- [*] Comment 456: Cannot address - requires API change outside scope
- [ ] Comment 789  ← Still needs work
```

Markers:
* `[x]` = Fixed
* `[*]` = Cannot fix (with explanation)
* `[ ]` = Pending

## Rules

* ONE comment at a time - fix completely before moving on
* Update status IMMEDIATELY after each fix
* If you can't fix something, mark [*] with clear explanation
* Stay within workspace directory
EOF

    # Add context from previous iterations if available
    if [ "$iteration" -gt 0 ]; then
        local prev_iter=$((iteration - 1))
        local run_id="${RALPH_RUN_ID:-}"
        if [ -n "$run_id" ] && [ -f "$output_dir/summaries/$run_id/fix-$prev_iter-summary.txt" ]; then
            cat << CONTEXT_EOF

CONTINUATION CONTEXT (Iteration $iteration):

To understand what has already been fixed:
- Read @../summaries/$run_id/fix-$prev_iter-summary.txt for context on previous fixes
- Check @../reports/comment-status.md to see which comments are already addressed
- Do NOT repeat work that was already completed
CONTEXT_EOF
        fi
    fi
}

# Completion check callback
_fix_completion_check() {
    local status_file="$_FIX_STATUS_FILE"

    # If status file doesn't exist, not complete
    if [ ! -f "$status_file" ]; then
        return 1
    fi

    # Check if any pending items remain (lines starting with "- [ ]")
    if grep -q '^\- \[ \]' "$status_file" 2>/dev/null; then
        return 1  # Still has pending items
    fi

    return 0  # All items checked off or marked as unable to fix
}

# Initialize comment status tracking file from comments markdown
_init_comment_status() {
    local comments_file="$1"
    local status_file="$2"

    {
        echo "# PR Comment Fix Status"
        echo ""
        echo "**Generated:** $(date -Iseconds)"
        echo ""
        echo "## Comments to Address"
        echo ""
        echo "Mark comments as fixed by changing \`[ ]\` to \`[x]\` and adding a brief description."
        echo "Mark comments that cannot be fixed with \`[*]\` and explain why."
        echo ""
    } > "$status_file"

    # Extract comment IDs from the markdown file
    # Look for patterns like "**ID:** 12345" which we added in comments_to_markdown
    grep_pcre_match '(?<=\*\*ID:\*\* )\d+' "$comments_file" | while read -r id; do
        echo "- [ ] Comment $id" >> "$status_file"
    done

    # If no IDs found, try extracting from ### headers
    if ! grep -q '^\- \[ \]' "$status_file" 2>/dev/null; then
        log_warn "No comment IDs found in standard format, creating generic checklist"
        # Count the number of ### headers that represent comments
        local count
        count=$(grep -c '^### ' "$comments_file" 2>/dev/null || echo "0")
        for i in $(seq 1 "$count"); do
            echo "- [ ] Comment item $i" >> "$status_file"
        done
    fi

    log "Initialized status file with $(grep -c '^\- \[ \]' "$status_file" 2>/dev/null || echo 0) comments to address"
}

# Update task-comments.md with commit information
_update_task_comments_with_commit() {
    local comments_file="$1"
    local status_file="$2"
    local commit_sha="$3"

    if [ ! -f "$comments_file" ]; then
        log_warn "Cannot update task-comments.md: file not found"
        return 1
    fi

    log "Updating task-comments.md with commit information"

    # Build the commit section
    local commit_section
    commit_section=$(cat << EOF

## Commit

**SHA:** ${commit_sha}
**Date:** $(date -Iseconds)

### Comments Addressed

EOF
)

    # Extract addressed comments from status file
    if [ -f "$status_file" ]; then
        # Get fixed comments [x]
        while IFS= read -r line; do
            commit_section+="$line"$'\n'
        done < <(grep '^\- \[x\]' "$status_file" 2>/dev/null || true)

        # Get skipped comments [*]
        local skipped_lines
        skipped_lines=$(grep '^\- \[\*\]' "$status_file" 2>/dev/null || true)
        if [ -n "$skipped_lines" ]; then
            commit_section+=$'\n'"### Comments Not Addressed"$'\n\n'
            while IFS= read -r line; do
                commit_section+="$line"$'\n'
            done <<< "$skipped_lines"
        fi
    fi

    # Append to task-comments.md
    echo "$commit_section" >> "$comments_file"

    log "Added ## Commit section to task-comments.md"
    return 0
}

# Commit and push fixes after successful completion
_commit_and_push_fixes() {
    local workspace="$1"
    local worker_dir="$2"

    cd "$workspace" || {
        log_error "Failed to cd to workspace: $workspace"
        return 1
    }

    # Check if there are changes to commit
    if git diff --quiet && git diff --cached --quiet && [ -z "$(git ls-files --others --exclude-standard)" ]; then
        log "No changes to commit after fix"
        return 0
    fi

    # Get the current branch
    local current_branch
    current_branch=$(git rev-parse --abbrev-ref HEAD)

    log "Committing fixes on branch: $current_branch"

    # Stage all changes
    git add -A

    # Create commit message
    local commit_msg="fix: Address PR review comments

Automated fixes for PR review feedback.
See comment-status.md for details on addressed items."

    # Set git author/committer identity
    export GIT_AUTHOR_NAME="Ralph Wiggum"
    export GIT_AUTHOR_EMAIL="ralph@wiggum.cc"
    export GIT_COMMITTER_NAME="Ralph Wiggum"
    export GIT_COMMITTER_EMAIL="ralph@wiggum.cc"

    if ! git commit --no-gpg-sign -m "$commit_msg" 2>&1; then
        log_error "Failed to create commit"
        return 1
    fi

    local commit_hash
    commit_hash=$(git rev-parse HEAD)
    log "Created commit: $commit_hash"

    # Push to remote
    log "Pushing to remote..."
    if ! git push 2>&1; then
        log_error "Failed to push to remote"
        return 1
    fi

    log "Successfully pushed fixes to $current_branch"
    return 0
}
