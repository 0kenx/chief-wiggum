#!/usr/bin/env bash
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: task-worker
# AGENT_DESCRIPTION: Main task execution agent that manages the complete task
#   lifecycle from PRD. Handles git worktree setup, PRD task execution via
#   ralph loop pattern, validation review (via nested sub-agent), commit and
#   PR creation, kanban status updates, and worktree cleanup. The primary
#   workhorse agent for automated task completion.
# REQUIRED_PATHS:
#   - prd.md : Product Requirements Document containing tasks to execute
# NOTE: workspace is created by this agent, not required in advance
# OUTPUT_FILES:
#   - worker.log : Main worker log with agent lifecycle events
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "task-worker" "Main task execution agent that manages the complete task lifecycle from PRD"

# Required paths before agent can run
agent_required_paths() {
    echo "prd.md"
    # Note: workspace is created by this agent, not required in advance
}

# Output files that must exist (non-empty) after agent completes
agent_output_files() {
    echo "worker.log"
    # Note: logs/*.log files are created per iteration
    # Note: summaries/summary.txt is optional (only on success)
    # Note: validation-result.txt is created by validation-review sub-agent
}

# Source dependencies using base library helpers
agent_source_core
agent_source_ralph_supervised
agent_source_resume
agent_source_violations
agent_source_tasks
agent_source_git
agent_source_lock
agent_source_metrics
agent_source_registry

# Source exit codes for standardized returns
source "$WIGGUM_HOME/lib/core/exit-codes.sh"

# Save references to sourced kanban functions before defining wrappers
eval "_kanban_mark_done() $(declare -f update_kanban | sed '1d')"
eval "_kanban_mark_failed() $(declare -f update_kanban_failed | sed '1d')"
eval "_kanban_mark_pending_approval() $(declare -f update_kanban_pending_approval | sed '1d')"

# Track plan file path for user prompt callback
_TASK_PLAN_FILE=""

# Commit sub-agent changes to isolate work between phases
# This prevents one sub-agent from accidentally destroying another's work
#
# Args:
#   workspace   - The workspace directory
#   agent_name  - Name of the sub-agent (for commit message)
#   file_pattern - Optional glob pattern to add (defaults to ".")
#
# Returns: 0 on success or if nothing to commit, 1 on error
_commit_subagent_changes() {
    local workspace="$1"
    local agent_name="$2"
    local file_pattern="${3:-.}"

    cd "$workspace" || return 1

    # Check if there are any changes to commit
    if git diff --quiet && git diff --staged --quiet; then
        log_debug "No changes to commit for $agent_name"
        return 0
    fi

    # Stage changes
    git add "$file_pattern" 2>/dev/null || true

    # Check if there are staged changes
    if git diff --staged --quiet; then
        log_debug "No staged changes to commit for $agent_name"
        return 0
    fi

    # Create commit
    local commit_msg="chore($agent_name): automated changes

Co-Authored-By: Wiggum <noreply@wiggum.ai>"

    if git commit -m "$commit_msg" >/dev/null 2>&1; then
        log "Committed $agent_name changes"
        return 0
    else
        log_warn "Failed to commit $agent_name changes"
        return 1
    fi
}

# Main entry point - manages complete task lifecycle
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    # Use config values (set by load_agent_config in agent-registry)
    local max_iterations="${WIGGUM_MAX_ITERATIONS:-${AGENT_CONFIG_MAX_ITERATIONS:-20}}"
    local max_turns="${WIGGUM_MAX_TURNS:-${AGENT_CONFIG_MAX_TURNS:-50}}"

    # Resume mode support
    local resume_iteration="${WIGGUM_RESUME_ITERATION:-0}"
    local resume_context="${WIGGUM_RESUME_CONTEXT:-}"

    # Extract worker and task IDs
    local worker_id task_id
    worker_id=$(basename "$worker_dir")
    # Match any task prefix format: TASK-001, PIPELINE-001, etc.
    task_id=$(echo "$worker_id" | sed -E 's/worker-([A-Z]+-[0-9]+)-.*/\1/')

    # Setup environment
    export WORKER_ID="$worker_id"
    export TASK_ID="$task_id"
    export LOG_FILE="$worker_dir/worker.log"
    export WIGGUM_HOME

    local prd_file="$worker_dir/prd.md"

    # Record start time
    local start_time
    start_time=$(date +%s)
    agent_log_start "$worker_dir" "$task_id"

    log "Task worker agent starting for $task_id (max $max_turns turns per session)"

    # Log worker start to audit log
    audit_log_worker_start "$task_id" "$worker_id"

    # === SETUP PHASE ===
    # Create git worktree for isolation
    if ! setup_worktree "$project_dir" "$worker_dir"; then
        log_error "Failed to setup worktree"
        _task_worker_cleanup "$worker_dir" "$project_dir" "$task_id" "FAILED" "" "N/A"
        return 1
    fi
    local workspace="$WORKTREE_PATH"

    # Start violation monitoring (log-based, 100ms interval)
    # Pass: workspace, worker_dir, agent_pid ($$), project_dir
    start_violation_monitor "$workspace" "$worker_dir" "$$" "$project_dir"
    trap '_task_worker_stop_monitor' EXIT

    # Change to workspace
    cd "$workspace" || {
        log_error "Cannot access workspace: $workspace"
        _task_worker_cleanup "$worker_dir" "$project_dir" "$task_id" "FAILED" "" "N/A"
        return 1
    }

    # Create standard directories
    agent_create_directories "$worker_dir"

    # === CHECK FOR EXISTING PLAN ===
    _TASK_PLAN_FILE="$project_dir/.ralph/plans/${task_id}.md"
    if [ -f "$_TASK_PLAN_FILE" ] && [ -s "$_TASK_PLAN_FILE" ]; then
        log "Plan found at $_TASK_PLAN_FILE - will include in execution context"
    else
        log_debug "No existing plan at $_TASK_PLAN_FILE"
        _TASK_PLAN_FILE=""
    fi

    # === EXECUTION PHASE ===
    # Set up callback context using base library
    agent_setup_context "$worker_dir" "$workspace" "$project_dir" "$task_id"
    _TASK_PRD_FILE="$prd_file"
    _TASK_RESUME_ITERATION="$resume_iteration"
    _TASK_RESUME_CONTEXT="$resume_context"

    # Supervisor interval (run supervisor every N iterations)
    local supervisor_interval="${WIGGUM_SUPERVISOR_INTERVAL:-3}"

    # Run main work loop with supervision
    run_ralph_loop_supervised "$workspace" \
        "$(_get_system_prompt "$workspace")" \
        "_task_user_prompt" \
        "_task_completion_check" \
        "$max_iterations" "$max_turns" "$worker_dir" "iteration" \
        "$supervisor_interval"

    local loop_result=$?

    # Generate final summary (hardcoded prompt - not configurable)
    if [ -n "$RALPH_LOOP_LAST_SESSION_ID" ] && [ $loop_result -eq 0 ]; then
        log "Generating final summary for changelog"

        run_agent_resume "$RALPH_LOOP_LAST_SESSION_ID" \
            "$(_get_final_summary_prompt)" \
            "$worker_dir/logs/final-summary.log" 3

        # Extract to summaries/summary.txt (parse stream-JSON to get text, then extract summary tags)
        if [ -f "$worker_dir/logs/final-summary.log" ]; then
            grep '"type":"assistant"' "$worker_dir/logs/final-summary.log" | \
                jq -r 'select(.message.content[]? | .type == "text") | .message.content[] | select(.type == "text") | .text' 2>/dev/null | \
                sed -n '/<summary>/,/<\/summary>/p' | \
                sed '1d;$d' > "$worker_dir/summaries/summary.txt"
            log "Final summary saved to summaries/summary.txt"
        fi
    fi

    # === SECURITY AUDIT PHASE ===
    if [ -d "$workspace" ] && [ $loop_result -eq 0 ]; then
        log "Running security audit on completed work"
        run_sub_agent "security-audit" "$worker_dir" "$project_dir"

        # Check security audit result using reader function
        local security_result
        security_result=$(agent_read_subagent_result "$worker_dir" "SECURITY_result" "security-result.txt")
        log "Security audit result: $security_result"

        case "$security_result" in
            PASS)
                log "Security audit passed - no issues found"
                ;;
            FIX)
                log "Security audit found fixable issues - running security-fix agent"
                run_sub_agent "security-fix" "$worker_dir" "$project_dir"

                local fix_result
                fix_result=$(cat "$worker_dir/fix-result.txt" 2>/dev/null || echo "UNKNOWN")
                log "Security fix result: $fix_result"

                # Commit security fix changes to isolate work
                _commit_subagent_changes "$workspace" "security-fix"

                if [ "$fix_result" != "FIXED" ]; then
                    log_warn "Security fix incomplete (result: $fix_result) - continuing with validation"
                fi
                ;;
            STOP)
                log_error "Security audit found fundamental/architectural issues - cannot proceed"
                log_error "Review security-report.md for details"
                # Mark as failed to prevent commit/PR
                loop_result=1
                ;;
            *)
                log_warn "Security audit result unknown ($security_result) - continuing with caution"
                ;;
        esac
    fi

    # === TEST COVERAGE PHASE ===
    if [ -d "$workspace" ] && [ $loop_result -eq 0 ]; then
        log "Running test generation and execution on completed work"
        run_sub_agent "test-coverage" "$worker_dir" "$project_dir"

        # Check test result using reader function
        local test_result
        test_result=$(agent_read_subagent_result "$worker_dir" "TEST_result" "test-result.txt")
        log "Test coverage result: $test_result"

        case "$test_result" in
            PASS)
                log "Tests generated and all passed"
                # Commit test changes to isolate work
                _commit_subagent_changes "$workspace" "test-coverage"
                ;;
            FAIL)
                log_error "Tests failed - marking task as failed"
                log_error "Review test-report.md for details"
                loop_result=1
                ;;
            SKIP)
                log "Test generation skipped (no testable changes or no test infrastructure)"
                ;;
            *)
                log_warn "Test result unknown ($test_result) - continuing with caution"
                # Still try to commit any test changes made
                _commit_subagent_changes "$workspace" "test-coverage"
                ;;
        esac
    fi

    # === DOCUMENTATION WRITER PHASE ===
    # Note: documentation-writer is non-blocking and never fails
    if [ -d "$workspace" ] && [ $loop_result -eq 0 ]; then
        log "Running documentation update on completed work"
        run_sub_agent "documentation-writer" "$worker_dir" "$project_dir"

        # Check docs result using reader function (informational only - never blocks)
        local docs_result
        docs_result=$(agent_read_subagent_result "$worker_dir" "DOCS_result" "docs-result.txt")
        log "Documentation writer result: $docs_result"

        case "$docs_result" in
            PASS)
                log "Documentation updated successfully"
                # Commit documentation changes to isolate work
                _commit_subagent_changes "$workspace" "documentation"
                ;;
            SKIP)
                log "Documentation update skipped (no updates needed)"
                ;;
            *)
                log "Documentation completed with result: $docs_result"
                # Still try to commit any doc changes made
                _commit_subagent_changes "$workspace" "documentation"
                ;;
        esac
    fi

    # === VALIDATION PHASE ===
    # Stop violation monitor before validation
    stop_violation_monitor "$VIOLATION_MONITOR_PID"

    # Run validation-review as a nested sub-agent
    if [ -d "$workspace" ]; then
        log "Running validation review on completed work"
        run_sub_agent "validation-review" "$worker_dir" "$project_dir"
    fi

    # === FINALIZATION PHASE ===
    _determine_finality "$worker_dir" "$workspace" "$project_dir" "$prd_file"
    local has_violations="$FINALITY_HAS_VIOLATIONS"
    local final_status="$FINALITY_STATUS"

    # Check validation result using communication protocol
    local validation_result
    validation_result=$(agent_read_validation "$worker_dir")
    if [ "$validation_result" = "FAIL" ]; then
        log_error "Validation review FAILED - marking task as failed"
        final_status="FAILED"
    elif [ "$validation_result" = "UNKNOWN" ]; then
        log_error "Validation result UNKNOWN - cannot proceed safely"
        log_error "Worker exiting without commit/PR or status update"
        return "$EXIT_AGENT_VALIDATION_FAILED"
    fi

    local pr_url="N/A"
    local task_desc=""

    log_debug "Finalization check: has_violations=$has_violations, final_status=$final_status"

    # Only create commits and PRs if no violations and task is complete
    if [ "$has_violations" = false ] && [ "$final_status" = "COMPLETE" ]; then
        log "Creating commit and PR for task $task_id"
        if [ -d "$workspace" ]; then
            cd "$workspace" || return 1

            # Get task description from kanban for commit message
            task_desc=$(grep -F "**[$task_id]**" "$project_dir/.ralph/kanban.md" | sed 's/.*\*\*\[.*\]\*\* //' | head -1)
            log_debug "Task description: ${task_desc:-<empty>}"

            # Get task priority
            local task_priority
            task_priority=$(grep -F -A2 "**[$task_id]**" "$project_dir/.ralph/kanban.md" | grep "Priority:" | sed 's/.*Priority: //')
            log_debug "Task priority: ${task_priority:-<empty>}"

            # Create commit using shared library
            if git_create_commit "$workspace" "$task_id" "$task_desc" "$task_priority" "$worker_id"; then
                local branch_name="$GIT_COMMIT_BRANCH"
                log "Commit created on branch: $branch_name"

                # Create PR using shared library
                git_create_pr "$branch_name" "$task_id" "$task_desc" "$worker_dir" "$project_dir"
                pr_url="$GIT_PR_URL"
                log "PR created: $pr_url"
            else
                log_error "Failed to create commit"
                final_status="FAILED"
            fi
        else
            log_error "Workspace not found: $workspace"
        fi
    else
        log "Skipping commit and PR creation - has_violations=$has_violations, final_status=$final_status"
    fi

    # === CLEANUP PHASE ===
    _task_worker_cleanup "$worker_dir" "$project_dir" "$task_id" "$final_status" "$task_desc" "$pr_url"

    # Record completion
    agent_log_complete "$worker_dir" "$loop_result" "$start_time"

    # Write structured agent result
    local result_status="failure"
    local result_exit_code="$loop_result"
    if [ "$final_status" = "COMPLETE" ] && [ "$loop_result" -eq 0 ]; then
        result_status="success"
    elif [ "$final_status" = "COMPLETE" ]; then
        result_status="partial"
    fi

    # Build outputs JSON
    local outputs_json
    outputs_json=$(jq -n \
        --arg pr_url "$pr_url" \
        --arg branch "${GIT_COMMIT_BRANCH:-}" \
        --arg commit_sha "$(cd "$workspace" 2>/dev/null && git rev-parse HEAD 2>/dev/null || echo "")" \
        --arg validation_result "$validation_result" \
        '{
            pr_url: $pr_url,
            branch: $branch,
            commit_sha: $commit_sha,
            validation_result: $validation_result
        }')

    agent_write_result "$worker_dir" "$result_status" "$result_exit_code" "$outputs_json"

    log "Task worker finished: $worker_id"
    return $loop_result
}

# Internal cleanup function for violation monitor
_task_worker_stop_monitor() {
    stop_violation_monitor "$VIOLATION_MONITOR_PID" 2>/dev/null || true
}

# Determine final task status
_determine_finality() {
    local worker_dir="$1"
    local workspace="$2"
    local project_dir="$3"
    local prd_file="$4"

    local has_violations=false
    local final_status="COMPLETE"

    # Check for workspace violations before processing results
    if ! agent_runner_detect_violations "$workspace" "$project_dir"; then
        log_error "Workspace violation detected - changes outside workspace were reverted"
        echo "WORKSPACE_VIOLATION" > "$worker_dir/violation_status.txt"
        has_violations=true
        final_status="FAILED"
    fi

    # Check PRD status
    local prd_status
    prd_status=$(get_prd_status "$prd_file")
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

# Full cleanup including kanban update
_task_worker_cleanup() {
    local worker_dir="$1"
    local project_dir="$2"
    local task_id="$3"
    local final_status="$4"
    local task_desc="$5"
    local pr_url="$6"

    log "Cleaning up task worker"

    # Log cleanup start to audit log
    audit_log_worker_cleanup "$task_id" "$(basename "$worker_dir")"

    # Clean up git worktree
    cleanup_worktree "$project_dir" "$worker_dir" "$final_status" "$task_id"

    # Update kanban and finalize
    _update_kanban_status "$worker_dir" "$project_dir" "$task_id" "$final_status" "$task_desc" "$pr_url"
}

# Update kanban based on final status
_update_kanban_status() {
    local worker_dir="$1"
    local project_dir="$2"
    local task_id="$3"
    local final_status="$4"
    local task_desc="$5"
    local pr_url="$6"

    local worker_id
    worker_id=$(basename "$worker_dir")

    # Get PR URL from file if not passed
    if [ -f "$worker_dir/pr_url.txt" ]; then
        pr_url=$(cat "$worker_dir/pr_url.txt")
    fi

    if [ "$final_status" = "COMPLETE" ]; then
        # If PR was created, mark as Pending Approval [P] - wiggum review sync will mark [x] when merged
        # If no PR (gh CLI unavailable), mark as complete [x] directly
        if [ -n "$pr_url" ] && [ "$pr_url" != "N/A" ]; then
            log "Marking task $task_id as pending approval [P] in kanban (PR: $pr_url)"
            if ! _kanban_mark_pending_approval "$project_dir/.ralph/kanban.md" "$task_id"; then
                log_error "Failed to update kanban.md after retries"
            fi
        else
            log "Marking task $task_id as complete [x] in kanban (no PR created)"
            if ! _kanban_mark_done "$project_dir/.ralph/kanban.md" "$task_id"; then
                log_error "Failed to update kanban.md after retries"
            fi
        fi

        # Append to changelog
        log "Appending to changelog"

        # Get detailed summary if it exists
        local summary=""
        if [ -f "$worker_dir/summaries/summary.txt" ]; then
            summary=$(cat "$worker_dir/summaries/summary.txt")
            log "Including detailed summary in changelog"
        fi

        if ! append_changelog "$project_dir/.ralph/changelog.md" "$task_id" "$worker_id" "$task_desc" "$pr_url" "$summary"; then
            log_error "Failed to update changelog.md after retries"
        fi

        log "Task worker $worker_id completed task $task_id"
    else
        log_error "Marking task $task_id as FAILED [*] in kanban"
        if ! _kanban_mark_failed "$project_dir/.ralph/kanban.md" "$task_id"; then
            log_error "Failed to update kanban.md after retries"
        fi
        log_error "Task worker $worker_id failed task $task_id"
    fi

    # Log final worker status to audit log
    audit_log_worker_complete "$task_id" "$worker_id" "$final_status"

    # Update metrics.json with latest worker data
    log_debug "Exporting metrics to metrics.json"
    export_metrics "$project_dir/.ralph" 2>/dev/null || true
}

# System prompt - workspace boundary enforcement
_get_system_prompt() {
    local workspace="$1"
    local prd_relative="../prd.md"

    cat << EOF
SENIOR SOFTWARE ENGINEER ROLE:

You are a senior software engineer implementing a specific task from a PRD.
Your goal is to deliver production-quality code that fits naturally into the existing codebase.

WORKSPACE: $workspace
PRD: $prd_relative

## Core Principles

1. **Understand Before You Build**
   - Study the existing architecture before writing code
   - Find similar patterns in the codebase and follow them
   - Understand how your changes integrate with existing systems

2. **Write Production-Quality Code**
   - Code should be correct, secure, and maintainable
   - Handle errors appropriately - don't swallow exceptions
   - Include tests that verify the implementation works
   - Follow the project's existing conventions exactly

3. **Stay Focused**
   - Complete the PRD task fully, but don't over-engineer
   - Don't refactor unrelated code or add unrequested features
   - If blocked, document clearly and mark as incomplete

## Workspace Security

CRITICAL: You MUST NOT access files outside your workspace.
- Allowed: $workspace and $prd_relative
- Do NOT use paths like ../../ to escape
- Do NOT follow symlinks outside the workspace

For subagent prompts, prepend:
<workspace>Your allowed workspace is: $workspace. Do not read or modify files outside of this directory</workspace>
EOF
}

# User prompt callback for supervised ralph loop
# Args: iteration, output_dir, supervisor_dir, supervisor_feedback
_task_user_prompt() {
    local iteration="$1"
    local output_dir="$2"
    local _supervisor_dir="$3"  # unused but part of callback signature
    local supervisor_feedback="$4"
    local prd_relative="../prd.md"

    # Include supervisor feedback if provided
    if [ -n "$supervisor_feedback" ]; then
        cat << SUPERVISOR_EOF
SUPERVISOR GUIDANCE:

$supervisor_feedback

---

SUPERVISOR_EOF
    fi

    cat << 'PROMPT_EOF'
TASK EXECUTION PROTOCOL:

Your mission: Complete the next incomplete task from the PRD with production-quality code.

## Phase 1: Understand the Task

1. **Read the PRD** (@../prd.md)
   - Find the first incomplete task marked with `- [ ]`
   - Skip completed `- [x]` and failed `- [*]` tasks
   - Focus on ONE task only

2. **Understand the Requirements**
   - What exactly needs to be implemented?
   - What are the acceptance criteria?
   - What edge cases should be handled?

## Phase 2: Study the Architecture

Before writing ANY code, understand the existing codebase:

3. **Explore the Project Structure**
   - How is the codebase organized?
   - Where do similar features live?
   - What are the key abstractions and patterns?

4. **Find Existing Patterns**
   - Search for similar functionality already implemented
   - Note the patterns used: naming, structure, error handling
   - Identify the testing approach used in the project

5. **Understand Integration Points**
   - What existing code will you interact with?
   - What APIs or interfaces must you follow?
   - Are there shared utilities you should use?

## Phase 3: Implement with Quality

6. **Write the Implementation**
   - Follow the patterns you discovered in Phase 2
   - Match the existing code style exactly
   - Handle errors appropriately (don't swallow them)
   - Keep functions focused and readable

7. **Write Tests**
   - Add tests that verify your implementation works
   - Follow the project's existing test patterns
   - Test the happy path and key edge cases
   - If the project has no tests, at least manually verify

8. **Security Considerations**
   - Validate inputs from untrusted sources
   - Avoid injection vulnerabilities
   - Don't hardcode secrets or credentials
   - Handle sensitive data appropriately

## Phase 4: Verify and Complete

9. **Run Tests and Verification**
   - Run the test suite if one exists
   - Manually verify your implementation works
   - Check for obvious regressions

10. **Update the PRD**
    - `- [ ]` → `- [x]` if successfully completed
    - `- [ ]` → `- [*]` if blocked (explain why)

## Quality Checklist

Before marking complete, verify:
- [ ] Implementation meets all requirements
- [ ] Code follows existing patterns in the codebase
- [ ] Error cases are handled appropriately
- [ ] Tests are added (matching project conventions)
- [ ] No security vulnerabilities introduced
- [ ] Changes integrate cleanly with existing code

## Rules

- Complete ONE task fully before moving to the next
- If blocked, document clearly and mark as `- [*]`
- Don't over-engineer or add unrequested features
- Stay within the workspace directory
PROMPT_EOF

    # Add plan guidance if plan file exists
    if [ -n "$_TASK_PLAN_FILE" ] && [ -f "$_TASK_PLAN_FILE" ]; then
        cat << PLAN_EOF

IMPLEMENTATION PLAN AVAILABLE:

An implementation plan has been created for this task. Before starting:
1. Read the plan at: @$_TASK_PLAN_FILE
2. Follow the implementation approach described in the plan
3. Pay attention to the Critical Files section
4. Consider the potential challenges identified

The plan provides guidance on:
- Existing patterns in the codebase to follow
- Recommended implementation approach
- Dependencies and sequencing
- Potential challenges to watch for
PLAN_EOF
    fi

    # Add context from previous iterations if available
    if [ "$iteration" -gt 0 ]; then
        # Check if this is a resumed iteration with resume context
        if [ "$iteration" -eq "$_TASK_RESUME_ITERATION" ] && [ -n "$_TASK_RESUME_CONTEXT" ] && [ -f "$_TASK_RESUME_CONTEXT" ]; then
            cat << 'RESUME_EOF'

CONTEXT FROM PREVIOUS SESSION (RESUMED):

This worker was previously interrupted and is now resuming.

To understand what was accomplished before the interruption:
- Read the file @../resume-context.md - it contains a summary of the previous session's work

Continue from where the previous session left off:
- Do NOT repeat work that was already completed
- Pick up where the previous session stopped
- If a task was partially completed, continue from where it left off
- Use the context to maintain consistency in approach and patterns

CRITICAL: Do NOT read files in the logs/ directory - they contain full conversation JSON streams that are too large and will deplete your context window.
RESUME_EOF
        else
            # Normal iteration context - use previous iteration summaries
            local prev_iter=$((iteration - 1))
            if [ -f "$output_dir/summaries/iteration-$prev_iter-summary.txt" ]; then
                cat << CONTEXT_EOF

CONTEXT FROM PREVIOUS ITERATION:

This is iteration $iteration of a multi-iteration work session. Previous work has been completed in earlier iterations.

To understand what has already been accomplished and maintain continuity:
- Read the file @../summaries/iteration-$prev_iter-summary.txt to understand completed work and context
- This summary describes what was done, decisions made, and files modified
- Use this information to avoid duplicating work and to build upon previous progress
- Ensure your approach aligns with patterns and decisions from earlier iterations

CRITICAL: Do NOT read files in the logs/ directory - they contain full conversation JSON streams that are too large and will deplete your context window. Only read the summaries/iteration-X-summary.txt files for context.
CONTEXT_EOF
            fi
        fi
    fi
}

# Completion check - check PRD for incomplete tasks
_task_completion_check() {
    ! has_incomplete_tasks "$_TASK_PRD_FILE"
}

# Final summary prompt (not configurable per requirements)
_get_final_summary_prompt() {
    cat << 'SUMMARY_EOF'
FINAL COMPREHENSIVE SUMMARY REQUEST:

Congratulations! All tasks in this work session have been completed successfully.

Your task is to create a comprehensive summary of EVERYTHING accomplished across all iterations in this session. This summary will be used in:
1. The project changelog (for other developers to understand what changed)
2. Pull request descriptions (for code review)
3. Documentation of implementation decisions

Before providing your final summary, wrap your analysis in <analysis> tags to organize your thoughts and ensure completeness. In your analysis:

1. Review all completed tasks from the PRD
2. Examine all iterations and their summaries (if multiple iterations occurred)
3. Identify all files that were created or modified
4. Recall all technical decisions and their rationale
5. Document all testing and verification performed
6. Note any important patterns, conventions, or architectural choices
7. Consider what information would be most valuable for:
   - Future maintainers of this code
   - Code reviewers evaluating this work
   - Other developers working on related features

Your summary MUST include these sections in this exact order:

<example>
<analysis>
[Your thorough analysis ensuring all work is captured comprehensively]
</analysis>

<summary>

## TL;DR

[3-5 concise bullet points summarizing the entire session's work - write for busy developers who need the essence quickly]

## What Was Implemented

[Detailed description of all changes, new features, or fixes. Organize by:
- New features added
- Existing features modified
- Bugs fixed
- Refactoring performed
Be specific about functionality and behavior changes]

## Files Modified

[Comprehensive list of files, organized by type of change:
- **Created**: New files added to the codebase
- **Modified**: Existing files changed
- **Deleted**: Files removed (if any)

For each file, include:
- File path
- Brief description of changes
- Key functions/sections modified]

## Technical Details

[Important implementation decisions, patterns, and technical choices:
- Architecture or design patterns used
- Why specific approaches were chosen over alternatives
- Configuration changes and their purpose
- Dependencies added or updated
- Security considerations addressed
- Performance optimizations applied
- Error handling strategies
- Edge cases handled]

## Testing and Verification

[How the work was verified to be correct:
- Manual testing performed (specific test cases)
- Automated tests written or run
- Integration testing done
- Edge cases validated
- Performance benchmarks (if applicable)
- Security validation (if applicable)]

## Integration Notes

[Important information for integrating this work:
- Breaking changes (if any)
- Migration steps required (if any)
- Configuration changes needed
- Dependencies to install
- Compatibility considerations]

## Future Considerations

[Optional: Notes for future work or considerations:
- Known limitations
- Potential optimizations
- Related features that could be added
- Technical debt incurred (if any)]

</summary>
</example>

IMPORTANT GUIDELINES:
- Be specific with file paths, function names, and code patterns
- Include actual values for configurations, not placeholders
- Write for technical readers who may not have context
- Focus on WHAT was done and WHY, not just HOW
- Use proper markdown formatting for readability
- Be thorough but concise - every sentence should add value

Please provide your comprehensive summary following this structure.
SUMMARY_EOF
}
