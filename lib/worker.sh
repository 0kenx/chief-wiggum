#!/usr/bin/env bash
# Worker script - spawned by wiggum for each task

WORKER_DIR="$1"         # e.g., .ralph/workers/worker-TASK-001-12345
PROJECT_DIR="$2"        # Project root directory
WIGGUM_HOME="${WIGGUM_HOME:-$HOME/.claude/chief-wiggum}"

# Extract WORKER_ID and TASK_ID from WORKER_DIR
# WORKER_DIR format: .ralph/workers/worker-TASK-001-12345
WORKER_ID=$(basename "$WORKER_DIR")  # e.g., worker-TASK-001-12345
TASK_ID=$(echo "$WORKER_ID" | sed -E 's/worker-(TASK-[0-9]+)-.*/\1/')  # e.g., TASK-001

# Configuration for ralph loop
MAX_ITERATIONS="${WIGGUM_MAX_ITERATIONS:-20}"           # Max outer loop iterations
MAX_TURNS_PER_SESSION="${WIGGUM_MAX_TURNS:-50}"         # Max turns per Claude session (controls context window)

source "$WIGGUM_HOME/lib/ralph-loop.sh"
source "$WIGGUM_HOME/lib/logger.sh"
source "$WIGGUM_HOME/lib/file-lock.sh"
source "$WIGGUM_HOME/lib/calculate-cost.sh"
source "$WIGGUM_HOME/lib/audit-logger.sh"
source "$WIGGUM_HOME/lib/task-parser.sh"
source "$WIGGUM_HOME/lib/run-agent-once.sh"

# Save references to sourced kanban functions before defining wrapper
eval "_kanban_mark_done() $(declare -f update_kanban | sed '1d')"
eval "_kanban_mark_failed() $(declare -f update_kanban_failed | sed '1d')"

# Set log file for this worker - all log() calls will also write here
export LOG_FILE="$WORKER_DIR/worker.log"

main() {
    log "Worker starting: $WORKER_ID for task $TASK_ID"

    # Track if shutdown was requested
    local worker_interrupted=false
    local ralph_loop_pid=""

    # Setup signal handlers for graceful shutdown
    handle_worker_shutdown() {
        log "Worker $WORKER_ID received shutdown signal"
        worker_interrupted=true

        # Kill ralph_loop if it's running
        if [ -n "$ralph_loop_pid" ] && kill -0 "$ralph_loop_pid" 2>/dev/null; then
            log "Terminating ralph_loop (PID: $ralph_loop_pid)"
            kill -TERM "$ralph_loop_pid" 2>/dev/null || true
            wait "$ralph_loop_pid" 2>/dev/null || true
        fi

        # Exit immediately to stop the worker
        exit 143  # Standard exit code for SIGTERM (128 + 15)
    }
    trap handle_worker_shutdown INT TERM

    # Log worker start to audit log
    audit_log_worker_start "$TASK_ID" "$WORKER_ID"

    setup_worker

    # Handle resume mode - pass environment variables to ralph_loop
    if [ -n "${WIGGUM_RESUME_ITERATION:-}" ]; then
        log "Worker resuming from iteration $WIGGUM_RESUME_ITERATION"
        export WIGGUM_RESUME_ITERATION
        export WIGGUM_RESUME_CONTEXT
    fi

    # Start Ralph loop for this worker's task in background to capture PID
    # Params: prd_file, workspace, max_iterations, max_turns_per_session
    ralph_loop \
        "$WORKER_DIR/prd.md" \
        "$WORKER_DIR/workspace" \
        "$MAX_ITERATIONS" \
        "$MAX_TURNS_PER_SESSION" &
    ralph_loop_pid=$!

    # Wait for ralph_loop to complete
    if wait "$ralph_loop_pid"; then
        if [ "$worker_interrupted" = true ]; then
            log "Worker $WORKER_ID interrupted by signal"
        else
            log "Worker $WORKER_ID completed successfully"
        fi
    else
        if [ "$worker_interrupted" = true ]; then
            log "Worker $WORKER_ID interrupted by signal"
        else
            log_error "Worker $WORKER_ID failed or timed out"
        fi
    fi

    # Run validation review on completed work
    if [ -d "$WORKER_DIR/workspace" ]; then
        log "Running validation review on completed work"

        local review_system_prompt="VALIDATION REVIEWER ROLE:

You are a code reviewer and validation agent. Your job is to review completed work
and verify it meets the requirements specified in the PRD.

WORKSPACE: $WORKER_DIR/workspace

You have READ-ONLY intent - focus on reviewing and validating, not making changes.
If you find issues, document them clearly but do not attempt fixes."

        local review_user_prompt="VALIDATION AND REVIEW TASK:

Review the completed work in this workspace against the requirements in @../prd.md.

REVIEW CHECKLIST:

1. **Requirements Verification**
   - Read the PRD and identify all requirements
   - For each completed task, verify the implementation meets the stated requirements
   - Check for any missed requirements or partial implementations

2. **Code Quality Review**
   - Check for obvious bugs, errors, or anti-patterns
   - Verify error handling is appropriate
   - Look for potential security issues (injection, XSS, hardcoded secrets, etc.)
   - Check for proper input validation at boundaries

3. **Implementation Consistency**
   - Verify code follows existing project patterns and conventions
   - Check naming conventions are consistent
   - Verify file organization matches project structure

4. **Testing Coverage**
   - Identify what testing was performed (documented in PRD or summaries)
   - Note any gaps in test coverage
   - Check if edge cases were considered

DECISION CRITERIA:

- PASS: All requirements met, no critical issues, code is production-ready
- FAIL: Missing requirements, critical bugs, security vulnerabilities, or broken functionality

OUTPUT FORMAT:

You MUST provide your response in this EXACT structure with both tags:

<review>

## Requirements Check

| Requirement | Status | Notes |
|-------------|--------|-------|
| [requirement] | [PASS/FAIL] | [brief note] |

## Issues Found

### Critical (blocks release)
- [issue description and location]

### Warnings (should fix)
- [issue description and location]

### Suggestions (optional)
- [suggestion]

## Security Review

[Any security concerns found, or confirmation that common issues were checked]

## Summary

[Brief overall assessment]

</review>

<result>PASS</result>

OR

<result>FAIL</result>

CRITICAL: The <result> tag MUST contain exactly one word: either PASS or FAIL. No other text.
This tag is parsed programmatically to determine if the work can proceed to commit/PR creation."

        run_agent_once "$WORKER_DIR/workspace" "$review_system_prompt" "$review_user_prompt" "$WORKER_DIR/logs/validation-review.log" 5
        local validation_exit=$?
        local validation_result="UNKNOWN"

        # Extract review content between <review> tags
        if [ -f "$WORKER_DIR/logs/validation-review.log" ]; then
            if grep -q '<review>' "$WORKER_DIR/logs/validation-review.log"; then
                sed -n '/<review>/,/<\/review>/p' "$WORKER_DIR/logs/validation-review.log" | sed '1d;$d' > "$WORKER_DIR/validation-review.md"
                log "Validation review saved to validation-review.md"
            fi

            # Extract result tag (PASS or FAIL)
            validation_result=$(grep -oP '(?<=<result>)(PASS|FAIL)(?=</result>)' "$WORKER_DIR/logs/validation-review.log" | head -1)
            if [ -z "$validation_result" ]; then
                validation_result="UNKNOWN"
            fi
        fi

        if [ $validation_exit -eq 0 ]; then
            log "Validation review completed with result: $validation_result"
        else
            log_warn "Validation review failed or had issues (exit: $validation_exit)"
        fi

        # Store validation result for flow control
        echo "$validation_result" > "$WORKER_DIR/validation-result.txt"
    fi

    # Determine final status
    determine_finality
    local has_violations="$FINALITY_HAS_VIOLATIONS"
    local final_status="$FINALITY_STATUS"

    # Check validation result - override final_status if validation failed
    if [ -f "$WORKER_DIR/validation-result.txt" ]; then
        local validation_result=$(cat "$WORKER_DIR/validation-result.txt")
        if [ "$validation_result" = "FAIL" ]; then
            log_error "Validation review FAILED - marking task as failed"
            final_status="FAILED"
        elif [ "$validation_result" = "UNKNOWN" ]; then
            log_error "Validation result UNKNOWN - cannot proceed safely"
            log_error "Worker exiting without commit/PR or status update"
            return 1
        fi
    fi
    local pr_url="N/A"
    local task_desc=""

    # Only create commits and PRs if no violations and task is complete
    if [ "$has_violations" = false ] && [ "$final_status" = "COMPLETE" ]; then
        if [ -d "$WORKER_DIR/workspace" ]; then
            cd "$WORKER_DIR/workspace" || return 1

            # Get task description from kanban for commit message
            task_desc=$(grep "**\[$TASK_ID\]**" "$PROJECT_DIR/.ralph/kanban.md" | sed 's/.*\*\*\[.*\]\*\* //' | head -1)

            # Get task priority
            local task_priority=$(grep -A2 "**\[$TASK_ID\]**" "$PROJECT_DIR/.ralph/kanban.md" | grep "Priority:" | sed 's/.*Priority: //')

            # Create commit
            if git_commit "$task_desc" "$task_priority"; then
                local branch_name="$GIT_COMMIT_BRANCH"

                # Create PR
                git_pr "$branch_name" "$task_desc"
                pr_url="$GIT_PR_URL"
            else
                final_status="FAILED"
            fi
        fi
    else
        log "Skipping commit and PR creation - task status: $final_status"
    fi

    cleanup_worker "$final_status" "$task_desc" "$pr_url"
    log "Worker finished: $WORKER_ID"
}

setup_worker() {
    # Create git worktree for isolation
    cd "$PROJECT_DIR" || exit 1

    log_debug "Creating git worktree at $WORKER_DIR/workspace"
    git worktree add "$WORKER_DIR/workspace" HEAD 2>&1 | tee -a "$WORKER_DIR/worker.log"

    # Setup hooks with workspace boundary enforcement
    export CLAUDE_HOOKS_CONFIG="$WIGGUM_HOME/hooks/worker-hooks.json"
    export WORKER_ID
    export TASK_ID
    export WORKER_WORKSPACE="$WORKER_DIR/workspace"
    export WIGGUM_HOME

    # Store worker PID for tracking by orchestrator
    echo "$$" > "$WORKER_DIR/worker.pid"
    log_debug "Stored worker PID $$ in $WORKER_DIR/worker.pid"
}

detect_workspace_violations() {
    local workspace="$1"
    local project_dir="$2"

    log_debug "Checking for workspace boundary violations"

    # Check if any files outside workspace were modified in project root
    cd "$project_dir" || return 0

    # Get list of modified files in project root (excluding .ralph directory)
    local modified_files=$(git status --porcelain 2>/dev/null | grep -v "^.. .ralph/" | awk '{print $2}')

    if [[ -n "$modified_files" ]]; then
        log_error "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        log_error "⚠️  CRITICAL: Workspace boundary violation detected!"
        log_error "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        log_error ""
        log_error "Worker $WORKER_ID modified files outside its workspace:"
        echo "$modified_files" | while read -r file; do
            log_error "  - $file"
        done
        log_error ""
        log_error "Expected workspace: $workspace"
        log_error "Actual modifications: $project_dir"
        log_error ""

        # Create violations log directory if it doesn't exist
        mkdir -p "$project_dir/.ralph/logs"

        # Log violation with timestamp
        {
            echo "================================================================================"
            echo "VIOLATION: Workspace Escape"
            echo "Timestamp: $(date -Iseconds)"
            echo "Worker: $WORKER_ID"
            echo "Task: $TASK_ID"
            echo "Files modified outside workspace:"
            echo "$modified_files"
            echo "================================================================================"
            echo ""
        } >> "$project_dir/.ralph/logs/violations.log"

        log_error "NOT reverting changes - may include user edits from main repo."
        log_error "Task marked as FAILED. Please manually review the changes."
        log_error ""
        log_error "To prevent this:"
        log_error "  1. Do NOT edit files in the main repo while workers are running"
        log_error "  2. Ensure your git working directory is clean before running 'wiggum run'"
        log_error ""

        return 1
    fi

    log_debug "No workspace violations detected"
    return 0
}

determine_finality() {
    local has_violations=false
    local final_status="COMPLETE"

    # Check for workspace violations before processing results
    if ! detect_workspace_violations "$WORKER_DIR/workspace" "$PROJECT_DIR"; then
        log_error "Workspace violation detected - changes outside workspace were reverted"
        echo "WORKSPACE_VIOLATION" > "$WORKER_DIR/violation_status.txt"
        has_violations=true
        final_status="FAILED"
    fi

    # Check PRD status
    local prd_status=$(get_prd_status "$WORKER_DIR/prd.md")
    log "PRD status: $prd_status"

    # Determine final task status
    if [ "$has_violations" = true ]; then
        final_status="FAILED"
        log_error "Task marked as FAILED due to workspace violations"
    elif [ "$prd_status" = "FAILED" ]; then
        final_status="FAILED"
        log_error "Task marked as FAILED - PRD contains failed tasks"
    elif [ "$prd_status" = "INCOMPLETE" ]; then
        final_status="FAILED"
        log_error "Task marked as FAILED - PRD has incomplete tasks (timeout or error)"
    else
        final_status="COMPLETE"
        log "Task completed successfully - all PRD tasks complete"
    fi

    # Return values via global variables (bash limitation)
    FINALITY_HAS_VIOLATIONS="$has_violations"
    FINALITY_STATUS="$final_status"
}

git_commit() {
    local task_desc="$1"
    local task_priority="$2"

    # Commit any changes in the worktree
    if ! git diff --quiet || ! git diff --cached --quiet || [ -n "$(git ls-files --others --exclude-standard)" ]; then
        log "Creating branch and PR for $TASK_ID"

        # Create a unique branch for this task attempt (include timestamp to avoid conflicts)
        local timestamp=$(date +%s)
        local branch_name="task/$TASK_ID-$timestamp"

        if ! git checkout -b "$branch_name" 2>&1 | tee -a "$WORKER_DIR/worker.log"; then
            log_error "Failed to create branch $branch_name"
            GIT_COMMIT_BRANCH=""
            return 1
        fi

        # Stage all changes
        git add -A

        # Create commit
        local commit_msg="${TASK_ID}: ${task_desc}

Worker: $WORKER_ID
Priority: ${task_priority:-MEDIUM}
Completed by Chief Wiggum autonomous worker.

Co-Authored-By: Chief Wiggum Worker <noreply@chief-wiggum.local>"

        git commit --no-gpg-sign -m "$commit_msg" 2>&1 | tee -a "$WORKER_DIR/worker.log"

        local commit_hash=$(git rev-parse HEAD)
        log "Created commit: $commit_hash on branch $branch_name"

        GIT_COMMIT_BRANCH="$branch_name"
        return 0
    else
        log_error "No changes to commit for $TASK_ID - marking as FAILED"
        GIT_COMMIT_BRANCH=""
        return 1
    fi
}

git_pr() {
    local branch_name="$1"
    local task_desc="$2"

    # Push the branch
    if git push -u origin "$branch_name" 2>&1 | tee -a "$WORKER_DIR/worker.log"; then
        log "Pushed branch $branch_name to remote"

        # Create Pull Request using gh CLI
        if command -v gh &> /dev/null; then
            # Build Changes section from detailed summary if available
            local changes_section="This PR contains the automated implementation of the task requirements."
            if [ -f "$WORKER_DIR/summary.txt" ]; then
                changes_section=$(cat "$WORKER_DIR/summary.txt")
            fi

            # Calculate time and cost metrics
            calculate_worker_cost "$WORKER_DIR/worker.log" > "$WORKER_DIR/metrics.txt" 2>&1

            local metrics_section=""
            if [ -f "$WORKER_DIR/metrics.txt" ]; then
                metrics_section="
## Metrics

\`\`\`
$(tail -n +3 "$WORKER_DIR/metrics.txt")
\`\`\`
"
            fi

            # Read prd.md body for PR description
            local prd_body=""
            if [ -f "$WORKER_DIR/prd.md" ]; then
                prd_body=$(cat "$WORKER_DIR/prd.md")
            fi

            local pr_body="## Summary

$prd_body

## Changes

${changes_section}
${metrics_section}
---
🤖 Generated by [Chief Wiggum](https://github.com/0kenx/chief-wiggum)"

            if gh pr create \
                --title "$TASK_ID: $task_desc" \
                --body "$pr_body" \
                --base main \
                --head "$branch_name" 2>&1 | tee -a "$WORKER_DIR/worker.log"; then

                log "✓ Created Pull Request for $TASK_ID"

                # Save PR URL
                GIT_PR_URL=$(gh pr view "$branch_name" --json url -q .url)
                echo "$GIT_PR_URL" > "$WORKER_DIR/pr_url.txt"
                return 0
            else
                log "Failed to create PR (gh CLI error), but branch is pushed"
                GIT_PR_URL="N/A"
                return 1
            fi
        else
            log "gh CLI not found, skipping PR creation. Branch pushed: $branch_name"
            GIT_PR_URL="N/A"
            return 1
        fi
    else
        log "Failed to push branch (no remote configured?)"
        GIT_PR_URL="N/A"
        return 1
    fi
}

cleanup_worktree() {
    local final_status="$1"

    # Clean up git worktree (only on full success - verify actual GitHub state)
    cd "$PROJECT_DIR" || exit 1
    local can_cleanup=false
    if [ "$final_status" = "COMPLETE" ]; then
        # Get local commit from worktree
        local local_commit=$(git -C "$WORKER_DIR/workspace" rev-parse HEAD 2>/dev/null)

        # Check if commit exists on remote branch and PR exists
        local remote_commit=$(git ls-remote --heads origin "task/$TASK_ID-*" 2>/dev/null | head -1 | cut -f1)
        local pr_exists=$(gh pr list --head "task/$TASK_ID-*" --json number -q '.[0].number' 2>/dev/null)

        if [ -n "$remote_commit" ] && [ "$local_commit" = "$remote_commit" ] && [ -n "$pr_exists" ]; then
            can_cleanup=true
            log_debug "Verified: commit $local_commit pushed and PR #$pr_exists exists on GitHub"
        else
            log "GitHub verification failed: local=$local_commit, remote=${remote_commit:-none}, pr=$([ -n "$pr_exists" ] && echo '#'$pr_exists || echo 'no')"
        fi
    fi

    if [ "$can_cleanup" = true ]; then
        log_debug "Removing git worktree"
        git worktree remove "$WORKER_DIR/workspace" --force 2>&1 | tee -a "$WORKER_DIR/worker.log" || true
    else
        log "Preserving worktree for debugging: $WORKER_DIR/workspace"
    fi
}

update_kanban() {
    local final_status="$1"
    local task_desc="$2"
    local pr_url="$3"

    # Update kanban based on final status
    if [ "$final_status" = "COMPLETE" ]; then
        log "Marking task $TASK_ID as complete in kanban"
        if ! _kanban_mark_done "$PROJECT_DIR/.ralph/kanban.md" "$TASK_ID"; then
            log_error "Failed to update kanban.md after retries"
        fi

        # Append to changelog only on success
        log "Appending to changelog"
        # Get PR URL if it exists
        if [ -f "$WORKER_DIR/pr_url.txt" ]; then
            pr_url=$(cat "$WORKER_DIR/pr_url.txt")
        fi

        # Get detailed summary if it exists
        local summary=""
        if [ -f "$WORKER_DIR/summary.txt" ]; then
            summary=$(cat "$WORKER_DIR/summary.txt")
            log "Including detailed summary in changelog"
        fi

        if ! append_changelog "$PROJECT_DIR/.ralph/changelog.md" "$TASK_ID" "$WORKER_ID" "$task_desc" "$pr_url" "$summary"; then
            log_error "Failed to update changelog.md after retries"
        fi

        log "Worker $WORKER_ID completed task $TASK_ID"
    else
        log_error "Marking task $TASK_ID as FAILED in kanban"
        if ! _kanban_mark_failed "$PROJECT_DIR/.ralph/kanban.md" "$TASK_ID"; then
            log_error "Failed to update kanban.md after retries"
        fi
        log_error "Worker $WORKER_ID failed task $TASK_ID"
    fi

    # Log final worker status to audit log
    audit_log_worker_complete "$TASK_ID" "$WORKER_ID" "$final_status"

    # Remove worker PID file
    rm -f "$WORKER_DIR/worker.pid"
    log_debug "Removed worker PID file"
}

cleanup_worker() {
    local final_status="$1"
    local task_desc="$2"
    local pr_url="$3"

    log "Cleaning up worker $WORKER_ID"

    # Log cleanup start to audit log
    audit_log_worker_cleanup "$TASK_ID" "$WORKER_ID"

    # Clean up git worktree
    cleanup_worktree "$final_status"

    # Update kanban and finalize
    update_kanban "$final_status" "$task_desc" "$pr_url"
}

main "$@"
