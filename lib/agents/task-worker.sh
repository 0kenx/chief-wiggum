#!/usr/bin/env bash
# task-worker.sh - Main task execution agent
#
# Self-contained agent for executing tasks from a PRD.
# Uses ralph loop pattern with violation monitoring.
#
# Required paths: prd.md, workspace

AGENT_TYPE="task-worker"

# Source dependencies
source "$WIGGUM_HOME/lib/run-agent-ralph-loop.sh"
source "$WIGGUM_HOME/lib/run-agent-resume.sh"
source "$WIGGUM_HOME/lib/violation-monitor.sh"
source "$WIGGUM_HOME/lib/task-parser.sh"
source "$WIGGUM_HOME/lib/logger.sh"

# Required paths before agent can run
agent_required_paths() {
    echo "prd.md"
    echo "workspace"
}

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    local max_iterations="${WIGGUM_MAX_ITERATIONS:-20}"
    local max_turns="${WIGGUM_MAX_TURNS:-50}"

    # Resume mode support
    local resume_iteration="${WIGGUM_RESUME_ITERATION:-0}"
    local resume_context="${WIGGUM_RESUME_CONTEXT:-}"

    local workspace="$worker_dir/workspace"
    local prd_file="$worker_dir/prd.md"

    # Record start time
    local start_time=$(date +%s)
    echo "[$(date -Iseconds)] AGENT_STARTED agent=task-worker start_time=$start_time" >> "$worker_dir/worker.log"

    log "Task worker agent starting for $prd_file (max $max_turns turns per session)"

    # Start violation monitoring
    start_violation_monitor "$project_dir" "$worker_dir" 30
    trap '_stop_and_cleanup' EXIT

    # Change to workspace
    cd "$workspace" || {
        log_error "Cannot access workspace: $workspace"
        return 1
    }

    # Create logs subdirectory
    mkdir -p "$worker_dir/logs"

    # Set up callback context
    _TASK_WORKER_DIR="$worker_dir"
    _TASK_WORKSPACE="$workspace"
    _TASK_PRD_FILE="$prd_file"
    _TASK_RESUME_ITERATION="$resume_iteration"
    _TASK_RESUME_CONTEXT="$resume_context"

    # Run main work loop
    run_ralph_loop "$workspace" \
        "$(_get_system_prompt "$workspace")" \
        "_task_user_prompt" \
        "_task_completion_check" \
        "$max_iterations" "$max_turns" "$worker_dir" "iteration"

    local loop_result=$?

    # Generate final summary (hardcoded prompt - not configurable)
    if [ -n "$RALPH_LOOP_LAST_SESSION_ID" ] && [ $loop_result -eq 0 ]; then
        log "Generating final summary for changelog"

        run_agent_resume "$RALPH_LOOP_LAST_SESSION_ID" \
            "$(_get_final_summary_prompt)" \
            "$worker_dir/logs/final-summary.log" 3

        # Extract to summary.txt
        if [ -f "$worker_dir/logs/final-summary.log" ]; then
            sed -n '/<summary>/,/<\/summary>/p' "$worker_dir/logs/final-summary.log" | \
                sed '1d;$d' > "$worker_dir/summary.txt"
            log "Final summary saved to summary.txt"
        fi
    fi

    # Record end time
    local end_time=$(date +%s)
    local duration=$((end_time - start_time))
    echo "[$(date -Iseconds)] AGENT_COMPLETED agent=task-worker duration_sec=$duration exit_code=$loop_result" >> "$worker_dir/worker.log"

    return $loop_result
}

# Internal cleanup function
_stop_and_cleanup() {
    stop_violation_monitor "$VIOLATION_MONITOR_PID"
}

# System prompt - workspace boundary enforcement
_get_system_prompt() {
    local workspace="$1"
    local prd_relative="../prd.md"

    cat << EOF
WORKSPACE BOUNDARY ENFORCEMENT:

Your allowed workspace is: $workspace and $prd_relative

CRITICAL SECURITY RULE:
- You MUST NOT cd into, read, or modify files outside this workspace
- You MUST NOT use relative paths that escape this workspace (e.g., ../../)
- You MUST NOT follow symlinks that point outside this workspace
- You MUST NOT execute commands that affect files outside this workspace

All file operations must remain within the workspace boundary. Violations will cause validation to fail.
EOF
}

# User prompt callback for ralph loop
_task_user_prompt() {
    local iteration="$1"
    local output_dir="$2"
    local prd_relative="../prd.md"

    cat << 'PROMPT_EOF'
TASK EXECUTION PROTOCOL:

Your mission: Complete the next incomplete task from the Product Requirements Document (PRD).

STEP-BY-STEP PROCESS:

1. **Read the PRD**: Examine @../prd.md to understand all tasks and requirements

2. **Identify Next Task**: Find the first incomplete task marked with (- [ ])
   - Tasks marked (- [x]) are complete - skip them
   - Tasks marked (- [*]) are failed - skip them
   - Focus on the first (- [ ]) task only

3. **Understand Requirements**: Before starting, ensure you understand:
   - What the task is asking for
   - What files need to be modified or created
   - What the acceptance criteria are
   - Any dependencies or constraints

4. **Execute the Task**: Implement the solution completely within your workspace
   - Write clean, secure, and maintainable code
   - Follow existing code patterns and conventions
   - Add appropriate error handling
   - Include comments where logic is complex

5. **Verify Your Work**: Before marking complete, verify:
   - The implementation meets all requirements
   - Code works as expected (test if applicable)
   - No breaking changes to existing functionality

6. **Update PRD**: Mark the task status in @../prd.md:
   - Change (- [ ]) to (- [x]) if successfully completed
   - Change (- [ ]) to (- [*]) if unable to complete (explain why in PRD)

IMPORTANT NOTES:
- Work on ONE task at a time - do not skip ahead
- Be thorough - partial implementations should be marked as (- [*])
- If you encounter blockers, document them clearly in the PRD
- All work must stay within the workspace directory
PROMPT_EOF

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

CRITICAL: Do NOT read files in the logs/ directory - they contain full conversation JSON streams that are too large (100KB-500KB each) and will deplete your context window.
RESUME_EOF
        else
            # Normal iteration context - use previous iteration summaries
            local prev_iter=$((iteration - 1))
            if [ -f "$output_dir/iteration-$prev_iter-summary.txt" ]; then
                cat << CONTEXT_EOF

CONTEXT FROM PREVIOUS ITERATION:

This is iteration $iteration of a multi-iteration work session. Previous work has been completed in earlier iterations.

To understand what has already been accomplished and maintain continuity:
- Read the file @../iteration-$prev_iter-summary.txt to understand completed work and context
- This summary describes what was done, decisions made, and files modified
- Use this information to avoid duplicating work and to build upon previous progress
- Ensure your approach aligns with patterns and decisions from earlier iterations

CRITICAL: Do NOT read files in the logs/ directory - they contain full conversation JSON streams that are too large (100KB-500KB each) and will deplete your context window. Only read the iteration-X-summary.txt files for context.
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
