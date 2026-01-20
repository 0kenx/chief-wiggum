#!/usr/bin/env bash
# pr-comment-fix.sh - Fix PR comments using ralph loop
#
# Uses the extracted ralph loop mechanism to iteratively address PR comments.
# Used by `wiggum review task <pattern> fix` command.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/logger.sh"
source "$SCRIPT_DIR/defaults.sh"
source "$SCRIPT_DIR/run-agent-ralph-loop.sh"

# Load review config on source
load_review_config

# Global variables for callbacks (set by run_comment_fix)
_FIX_COMMENTS_FILE=""
_FIX_STATUS_FILE=""
_FIX_OUTPUT_DIR=""

# Callback: Generate comment fix user prompt
# Args: <iteration> <output_dir>
_comment_fix_user_prompt() {
    local iteration="$1"
    local output_dir="$2"

    local base_prompt="PR COMMENT FIX PROTOCOL:

Your mission: Address the feedback in PR review comments.

STEP-BY-STEP PROCESS:

1. **Read Comments**: Review @../task-comments.md for all PR feedback that needs addressing
   - Each comment includes the author, file path, line number, and the feedback
   - Code review comments include the diff hunk for context

2. **Read Status**: Check @../comment-status.md to see which comments have already been addressed
   - Comments marked with [x] are already fixed - skip them
   - Comments marked with [ ] need to be addressed

3. **Prioritize**: Address comments in order of importance:
   - Critical issues (bugs, security problems) first
   - Requested changes second
   - Suggestions and improvements last

4. **Fix Issues**: For each pending comment:
   - Understand what the reviewer is asking for
   - Make the necessary code changes to address the feedback
   - Ensure your fix doesn't break other functionality
   - Follow existing code patterns and conventions

5. **Update Status**: After fixing each comment, update @../comment-status.md:
   - Change \`- [ ] Comment <id>\` to \`- [x] Comment <id>: <brief description of fix>\`
   - If a comment cannot be addressed, mark it as \`- [*] Comment <id>: <reason>\`

IMPORTANT NOTES:
- Work on ONE comment at a time
- Be thorough - partial fixes should be marked as pending
- If you disagree with a comment, still try to address it or mark it with explanation
- All changes must stay within the workspace directory"

    # Add context from previous iterations if available
    if [ $iteration -gt 0 ]; then
        local prev_iter=$((iteration - 1))
        if [ -f "$output_dir/fix-$prev_iter-summary.txt" ]; then
            base_prompt="$base_prompt

CONTEXT FROM PREVIOUS ITERATION:

This is iteration $iteration of the fix session. Previous work has been done.

To understand what has already been fixed:
- Read @../fix-$prev_iter-summary.txt for context on previous fixes
- Check @../comment-status.md to see which comments are already addressed
- Do NOT repeat work that was already completed"
        fi
    fi

    echo "$base_prompt"
}

# Callback: Check if all comments addressed
# Returns: 0 if complete, 1 if work remains
_comment_fix_completion_check() {
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
# Args: <comments_file> <status_file>
init_comment_status() {
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
        local count=$(grep -c '^### ' "$comments_file" 2>/dev/null || echo "0")
        for i in $(seq 1 $count); do
            echo "- [ ] Comment item $i" >> "$status_file"
        done
    fi

    log "Initialized status file with $(grep -c '^\- \[ \]' "$status_file" 2>/dev/null || echo 0) comments to address"
}

# Commit and push fixes after successful completion
# Args: <workspace> <task_id> <worker_dir>
commit_and_push_fixes() {
    local workspace="$1"
    local task_id="$2"
    local worker_dir="$3"

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
    local current_branch=$(git rev-parse --abbrev-ref HEAD)

    log "Committing fixes on branch: $current_branch"

    # Stage all changes
    git add -A

    # Create commit message
    local commit_msg="fix($task_id): Address PR review comments

Automated fixes for PR review feedback.
See comment-status.md for details on addressed items.

Co-Authored-By: Chief Wiggum Worker <noreply@chief-wiggum.local>"

    if ! git commit --no-gpg-sign -m "$commit_msg" 2>&1; then
        log_error "Failed to create commit"
        return 1
    fi

    local commit_hash=$(git rev-parse HEAD)
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

# Main fix function
# Args: <task_pattern> <worker_dir> [max_iterations] [max_turns]
run_comment_fix() {
    local task_pattern="$1"
    local worker_dir="$2"
    local max_iterations="${3:-$WIGGUM_COMMENT_FIX_MAX_ITERATIONS}"
    local max_turns="${4:-$WIGGUM_COMMENT_FIX_MAX_TURNS}"

    local workspace="$worker_dir/workspace"
    local comments_file="$worker_dir/task-comments.md"
    local status_file="$worker_dir/comment-status.md"

    # Verify workspace exists
    if [ ! -d "$workspace" ]; then
        log_error "Workspace not found: $workspace"
        return 1
    fi

    # Verify comments file exists
    if [ ! -f "$comments_file" ]; then
        log_error "Comments file not found: $comments_file"
        log_error "Run 'wiggum review task $task_pattern sync' first"
        return 1
    fi

    # Check if there are any comments to fix
    local comment_count=$(grep -c '^### ' "$comments_file" 2>/dev/null || echo "0")
    if [ "$comment_count" -eq 0 ]; then
        log "No comments found in $comments_file - nothing to fix"
        return 0
    fi

    log "Found $comment_count comment(s) to address"

    # Initialize status tracking if not exists or reset
    init_comment_status "$comments_file" "$status_file"

    # Set global variables for callbacks
    _FIX_COMMENTS_FILE="$comments_file"
    _FIX_STATUS_FILE="$status_file"
    _FIX_OUTPUT_DIR="$worker_dir"

    # Build system prompt
    local sys_prompt="PR COMMENT FIX AGENT:

You are fixing PR review comments for a Chief Wiggum worker task.

WORKSPACE: $workspace
COMMENTS FILE: ../task-comments.md (read-only - contains the feedback to address)
STATUS FILE: ../comment-status.md (update this to track progress)

RULES:
- Focus on making clean, focused fixes that address the reviewer's concerns
- Maintain code quality and follow existing patterns
- Update the status file as you complete each fix
- Do not modify files outside the workspace directory"

    log "Starting comment fix loop (max $max_iterations iterations, $max_turns turns/session)"

    # Run the fix loop
    run_ralph_loop \
        "$workspace" \
        "$sys_prompt" \
        "_comment_fix_user_prompt" \
        "_comment_fix_completion_check" \
        "$max_iterations" \
        "$max_turns" \
        "$worker_dir" \
        "fix"

    local loop_result=$?

    # Auto commit and push if configured and loop succeeded
    if [ "$loop_result" -eq 0 ] && [ "$WIGGUM_AUTO_COMMIT_AFTER_FIX" = "true" ]; then
        log "Auto-committing and pushing fixes..."
        commit_and_push_fixes "$workspace" "$task_pattern" "$worker_dir"
    elif [ "$loop_result" -ne 0 ]; then
        log_warn "Fix loop did not complete successfully (exit code: $loop_result)"
    fi

    return $loop_result
}
