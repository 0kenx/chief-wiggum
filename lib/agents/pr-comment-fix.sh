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
#   - comment-fix-result.txt  : Contains PASS, FIX, FAIL, or SKIP
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "pr-comment-fix" "PR comment fix agent that addresses pull request review feedback"

# Required paths before agent can run
agent_required_paths() {
    echo "task-comments.md"
    echo "workspace"
}

# Source dependencies using base library helpers
agent_source_core
agent_source_ralph

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
        agent_write_result "$worker_dir" "failure" 1 '{}' '["Workspace not found"]'
        return 1
    fi

    # Verify comments file exists
    if [ ! -f "$comments_file" ]; then
        log_error "Comments file not found: $comments_file"
        log_error "Run 'wiggum review task <pattern> sync' first"
        agent_log_complete "$worker_dir" 1 "$start_time"
        agent_write_result "$worker_dir" "failure" 1 '{}' '["Comments file not found"]'
        return 1
    fi

    # Check if there are any comments to fix
    local comment_count
    comment_count=$(grep -c '^### ' "$comments_file" 2>/dev/null || echo "0")
    if [ "$comment_count" -eq 0 ]; then
        log "No comments found in $comments_file - nothing to fix"
        agent_setup_context "$worker_dir" "$workspace" "$project_dir"
        agent_log_complete "$worker_dir" 0 "$start_time"
        agent_write_result "$worker_dir" "success" 0 '{"gate_result":"SKIP","comments_fixed":0,"comments_pending":0,"comments_skipped":0}'
        rm -f "$worker_dir/.needs-fix"
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

    # Run the fix loop
    run_ralph_loop \
        "$workspace" \
        "$(_get_system_prompt "$workspace")" \
        "_fix_user_prompt" \
        "_fix_completion_check" \
        "$max_iterations" \
        "$max_turns" \
        "$worker_dir" \
        "fix"

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

    # Determine result status and gate_result
    local result_status="failure"
    local gate_result="FAIL"
    if [ "$loop_result" -eq 0 ] && [ "$comments_pending" -eq 0 ]; then
        result_status="success"
        gate_result="PASS"
    elif [ "$comments_fixed" -gt 0 ]; then
        result_status="partial"
        gate_result="FIX"
    fi

    # Log completion and write structured result
    agent_log_complete "$worker_dir" "$loop_result" "$start_time"

    local outputs_json
    outputs_json=$(printf '{"gate_result":"%s","commit_sha":"%s","push_succeeded":%s,"comments_fixed":%d,"comments_pending":%d,"comments_skipped":%d}' \
        "$gate_result" "$commit_sha" "$push_succeeded" "$comments_fixed" "$comments_pending" "$comments_skipped")

    agent_write_result "$worker_dir" "$result_status" "$loop_result" "$outputs_json"

    # Remove .needs-fix marker on success
    if [ "$result_status" = "success" ]; then
        rm -f "$worker_dir/.needs-fix"
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
STATUS: ../comment-status.md (update as you fix)

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

# User prompt callback
_fix_user_prompt() {
    local iteration="$1"
    local output_dir="$2"

    # Always include the initial prompt to ensure full context after summarization
    cat << 'EOF'
PR COMMENT FIX TASK:

Address feedback from PR review comments.

## Process

1. **Read comments**: @../task-comments.md - understand what reviewers want
2. **Check status**: @../comment-status.md - skip [x] items, fix [ ] items
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
        if [ -f "$output_dir/summaries/fix-$prev_iter-summary.txt" ]; then
            cat << CONTEXT_EOF

CONTINUATION CONTEXT (Iteration $iteration):

To understand what has already been fixed:
- Read @../summaries/fix-$prev_iter-summary.txt for context on previous fixes
- Check @../comment-status.md to see which comments are already addressed
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
    grep -oP '(?<=\*\*ID:\*\* )\d+' "$comments_file" 2>/dev/null | while read -r id; do
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
See comment-status.md for details on addressed items.

Co-Authored-By: Ralph Wiggum <ralph@wiggum.local>"

    # Set git author/committer identity
    export GIT_AUTHOR_NAME="Ralph Wiggum"
    export GIT_AUTHOR_EMAIL="ralph@wiggum.local"
    export GIT_COMMITTER_NAME="Ralph Wiggum"
    export GIT_COMMITTER_EMAIL="ralph@wiggum.local"

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
