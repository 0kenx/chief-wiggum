#!/usr/bin/env bash
# Ralph Wiggum Loop - Self-prompting execution pattern with controlled context

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/task-parser.sh"
source "$SCRIPT_DIR/logger.sh"

# Extract clean text from Claude CLI stream-JSON output
# Filters out JSON and returns only assistant text responses
extract_summary_text() {
    local input="$1"

    # Extract text from JSON lines with type:"assistant" and text content
    echo "$input" | grep '"type":"assistant"' | \
        jq -r 'select(.message.content[]? | .type == "text") | .message.content[] | select(.type == "text") | .text' 2>/dev/null | \
        grep -v '^$'
}

ralph_loop() {
    local prd_file="$1"                    # Worker's PRD file (absolute path)
    local agent_file="$2"                  # Agent definition
    local workspace="$3"                   # Worker's git worktree
    local max_iterations="${4:-20}"
    local max_turns_per_session="${5:-50}" # Limit turns to control context window
    local iteration=0

    # Record start time
    local start_time=$(date +%s)
    {
        echo ""
        echo "=== WORKER STARTED ==="
        echo "Start time: $(date -Iseconds)"
        echo "WORKER_START_TIME=$start_time"
        echo ""
    } >> "../worker.log"

    log "Ralph loop starting for $prd_file (max $max_turns_per_session turns per session)"

    # Change to workspace BEFORE the loop
    cd "$workspace" || exit 1

    # Create logs subdirectory for detailed iteration logs
    mkdir -p "../logs"

    # Convert PRD file to relative path from workspace
    local prd_relative="../prd.md"

    # Track the last session ID for final summary
    local last_session_id=""

    while [ $iteration -lt $max_iterations ]; do
        # Exit if all tasks complete
        if ! has_incomplete_tasks "$prd_file"; then
            log "Worker completed all tasks in $prd_file"
            break
        fi

        # Generate unique session ID for this iteration
        local session_id=$(uuidgen)
        last_session_id="$session_id"

        local sys_prompt="WORKSPACE BOUNDARY ENFORCEMENT:

Your working directory is: $workspace

CRITICAL SECURITY RULE: You MUST NOT directly or indirectly:
- cd into, read, or modify files outside this directory
- Use relative paths that escape this directory (e.g., ../../)
- Follow symlinks that point outside this directory
- Execute commands that affect files outside this directory

All file operations must remain within the workspace boundary. Violations will be logged and blocked by system hooks."

        local user_prompt="TASK EXECUTION PROTOCOL:

Your mission: Complete the next incomplete task from the Product Requirements Document (PRD).

STEP-BY-STEP PROCESS:

1. **Read the PRD**: Examine @$prd_relative to understand all tasks and requirements

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

6. **Update PRD**: Mark the task status in @$prd_relative:
   - Change (- [ ]) to (- [x]) if successfully completed
   - Change (- [ ]) to (- [*]) if unable to complete (explain why in PRD)

IMPORTANT NOTES:
- Work on ONE task at a time - do not skip ahead
- Be thorough - partial implementations should be marked as (- [*])
- If you encounter blockers, document them clearly in the PRD
- All work must stay within the workspace directory"

        # Add context from previous iterations if available
        if [ $iteration -gt 0 ]; then
            # Build list of summary files to read
            local summary_files=""
            for ((i=0; i<iteration; i++)); do
                if [ -f "../iteration-$i-summary.txt" ]; then
                    if [ -z "$summary_files" ]; then
                        summary_files="iteration-$i-summary.txt"
                    else
                        summary_files="$summary_files, iteration-$i-summary.txt"
                    fi
                fi
            done

            user_prompt="$user_prompt

CONTEXT FROM PREVIOUS ITERATIONS:

This is iteration $iteration of a multi-iteration work session. Previous work has been completed in earlier iterations.

To understand what has already been accomplished and maintain continuity:
- Read the following summary files (in order) to understand completed work and context:
  $summary_files
- These summaries are located in the parent directory (../iteration-X-summary.txt)
- Each summary describes what was done in that iteration, decisions made, and files modified
- Use this information to avoid duplicating work and to build upon previous progress
- Ensure your approach aligns with patterns and decisions from earlier iterations

CRITICAL: Do NOT read files in the logs/ directory - they contain full conversation JSON streams that are too large (100KB-500KB each) and will deplete your context window. Only read the iteration-X-summary.txt files for context."
        fi

        log_debug "Iteration $iteration: Session $session_id (max $max_turns_per_session turns)"

        # Log iteration start to worker.log (clean format)
        {
            echo ""
            echo "=== ITERATION $iteration ==="
            echo "Session ID: $session_id"
            echo "Max turns: $max_turns_per_session"
            echo "PWD: $(pwd)"
            echo "=== WORK PHASE ==="
        } >> "../worker.log"

        log "Work phase starting (see logs/iteration-$iteration.log for details)"

        # PHASE 1: Work session with turn limit
        # Use --dangerously-skip-permissions to allow PRD edits (hooks still enforce workspace boundaries)
        # Redirect verbose output to iteration-specific file
        claude --verbose \
            --output-format stream-json \
            --plugin-dir "$WIGGUM_HOME/skills" \
            --append-system-prompt "$sys_prompt" \
            --session-id "$session_id" \
            --max-turns "$max_turns_per_session" \
            --dangerously-skip-permissions \
            -p "$user_prompt" > "../logs/iteration-$iteration.log" 2>&1

        local exit_code=$?
        log "Work phase completed (exit code: $exit_code)"

        # PHASE 2: ALWAYS generate summary for context continuity (not conditional)
        log "Generating summary for iteration $iteration"

        {
            echo "=== SUMMARY PHASE ==="
        } >> "../worker.log"

            local summary_prompt="Your task is to create a detailed summary of the conversation so far, paying close attention to the user's explicit requests and your previous actions.
This summary should be thorough in capturing technical details, code patterns, and architectural decisions that would be essential for continuing development work without losing context.

Before providing your final summary, wrap your analysis in <analysis> tags to organize your thoughts and ensure you've covered all necessary points. In your analysis process:

1. Chronologically analyze each message and section of the conversation. For each section thoroughly identify:
   - The user's explicit requests and intents
   - Your approach to addressing the user's requests
   - Key decisions, technical concepts and code patterns
   - Specific details like file names, full code snippets, function signatures, file edits, etc
2. Double-check for technical accuracy and completeness, addressing each required element thoroughly.

Your summary should include the following sections:

1. Primary Request and Intent: Capture all of the user's explicit requests and intents in detail
2. Key Technical Concepts: List all important technical concepts, technologies, and frameworks discussed.
3. Files and Code Sections: Enumerate specific files and code sections examined, modified, or created. Pay special attention to the most recent messages and include full code snippets where applicable and include a summary of why this file read or edit is important.
4. Problem Solving: Document problems solved and any ongoing troubleshooting efforts.
5. Pending Tasks: Outline any pending tasks that you have explicitly been asked to work on.
6. Current Work: Describe in detail precisely what was being worked on immediately before this summary request, paying special attention to the most recent messages from both user and assistant. Include file names and code snippets where applicable.
7. Optional Next Step: List the next step that you will take that is related to the most recent work you were doing. IMPORTANT: ensure that this step is DIRECTLY in line with the user's explicit requests, and the task you were working on immediately before this summary request. If your last task was concluded, then only list next steps if they are explicitly in line with the users request. Do not start on tangential requests without confirming with the user first.
8. If there is a next step, include direct quotes from the most recent conversation showing exactly what task you were working on and where you left off. This should be verbatim to ensure there's no drift in task interpretation.

Here's an example of how your output should be structured:

<example>
<analysis>
[Your thought process, ensuring all points are covered thoroughly and accurately]
</analysis>

<summary>
1. Primary Request and Intent:
   [Detailed description]

2. Key Technical Concepts:
   - [Concept 1]
   - [Concept 2]
   - [...]

3. Files and Code Sections:
   - [File Name 1]
      - [Summary of why this file is important]
      - [Summary of the changes made to this file, if any]
      - [Important Code Snippet]
   - [File Name 2]
      - [Important Code Snippet]
   - [...]

4. Problem Solving:
   [Description of solved problems and ongoing troubleshooting]

5. Pending Tasks:
   - [Task 1]
   - [Task 2]
   - [...]

6. Current Work:
   [Precise description of current work]

7. Optional Next Step:
   [Optional Next step to take]

</summary>
</example>

Please provide your summary based on the conversation so far, following this structure and ensuring precision and thoroughness in your response. "

            log "Requesting summary for session $session_id"

            # Capture full output to iteration summary file (in worker root, not logs/)
            local summary_full=$(claude --resume "$session_id" --max-turns 2 \
                --dangerously-skip-permissions -p "$summary_prompt" 2>&1 | \
                tee "../iteration-$iteration-summary.txt")

            # Extract clean text from JSON stream
            local summary=$(extract_summary_text "$summary_full")

            # Append clean summary to worker.log
            {
                echo "--- Session $iteration Summary ---"
                echo "$summary"
                echo "--- End Summary ---"
                echo ""
            } >> "../worker.log"

            # Append summary to PRD changelog section
            {
                echo ""
                echo "## Session $iteration Changelog ($(date -u +"%Y-%m-%d %H:%M:%S UTC"))"
                echo ""
                echo "$summary"
                echo ""
            } >> "$prd_file"

            log "Summary appended to PRD and worker.log"

        iteration=$((iteration + 1))
        sleep 2  # Prevent tight loop
    done

    if [ $iteration -ge $max_iterations ]; then
        log_error "Worker reached max iterations ($max_iterations) without completing all tasks"

        local end_time=$(date +%s)
        local duration=$((end_time - start_time))
        {
            echo ""
            echo "=== WORKER STATUS: INCOMPLETE ==="
            echo "End time: $(date -Iseconds)"
            echo "WORKER_END_TIME=$end_time"
            echo "Total duration: $duration seconds ($((duration / 60)) minutes)"
            echo "Status: Reached max iterations ($max_iterations) without completing all tasks"
        } >> "../worker.log"

        return 1
    fi

    # PHASE 3: Generate final comprehensive summary for changelog
    if [ -n "$last_session_id" ]; then
        log "Generating final summary for changelog"

        {
            echo ""
            echo "=== FINAL SUMMARY PHASE ==="
        } >> "../worker.log"

        local summary_prompt="FINAL COMPREHENSIVE SUMMARY REQUEST:

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

Please provide your comprehensive summary following this structure."

        # Capture full output to final summary log
        local summary_full=$(claude --resume "$last_session_id" --max-turns 3 \
            --dangerously-skip-permissions -p "$summary_prompt" 2>&1 | \
            tee "../logs/final-summary.log")

        # Extract clean text from JSON stream
        local final_summary=$(extract_summary_text "$summary_full")

        # Append clean summary to worker.log
        {
            echo "--- Final Summary ---"
            echo "$final_summary"
            echo "--- End Final Summary ---"
            echo ""
        } >> "../worker.log"

        # Save to summary.txt (for PR description)
        echo "$final_summary" > "../summary.txt"

        log "Final summary saved to summary.txt and worker.log"
    fi

    # Record end time
    local end_time=$(date +%s)
    local duration=$((end_time - start_time))
    {
        echo ""
        echo "=== WORKER COMPLETED ==="
        echo "End time: $(date -Iseconds)"
        echo "WORKER_END_TIME=$end_time"
        echo "Total duration: $duration seconds ($((duration / 60)) minutes)"
        echo "Status: All tasks completed successfully"
    } >> "../worker.log"

    log "Worker finished after $iteration iterations (duration: $duration seconds)"
    return 0
}
