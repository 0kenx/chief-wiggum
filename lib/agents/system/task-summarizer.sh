#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: task-summarizer
# AGENT_DESCRIPTION: Generates final task summary by resuming a prior agent's
#   Claude session. Produces a comprehensive summary for changelogs and PRs
#   by extracting structured content from the resumed session output.
#   The session source is configurable via step-config.json (resume_from key),
#   defaulting to task-executor for backwards compatibility.
# REQUIRED_PATHS:
#   - workspace : Directory containing the code (for context)
# OUTPUT_FILES:
#   - summaries/summary.txt : Final task summary
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "system.task-summarizer" "Generates final task summary by resuming the executor session"

# Required paths before agent can run
agent_required_paths() {
    echo "workspace"
}

# Source dependencies using base library helpers
agent_source_core
agent_source_resume

# Main entry point
agent_run() {
    local worker_dir="$1"
    # shellcheck disable=SC2034  # project_dir is part of agent_run interface
    local project_dir="$2"
    local max_turns="${AGENT_CONFIG_MAX_TURNS:-3}"

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Determine which agent to read session_id from.
    # Check step-config.json for optional "resume_from" key, default to task-executor.
    local step_config resume_from_agent
    step_config=$(agent_read_step_config "$worker_dir")
    resume_from_agent=$(echo "$step_config" | jq -r '.resume_from // "task-executor"')

    # Find session_id from the configured agent's result
    local source_result_file session_id
    source_result_file=$(agent_find_latest_result "$worker_dir" "$resume_from_agent")

    if [ -z "$source_result_file" ] || [ ! -f "$source_result_file" ]; then
        log_warn "No $resume_from_agent result found - skipping summary generation"
        local outputs_json
        outputs_json=$(jq -n '{gate_result: "SKIP", summary_file: ""}')
        agent_write_result "$worker_dir" "success" 0 "$outputs_json"
        return 0
    fi

    session_id=$(jq -r '.outputs.session_id // ""' "$source_result_file")

    if [ -z "$session_id" ]; then
        log_warn "No session_id in $resume_from_agent result - skipping summary generation"
        local outputs_json
        outputs_json=$(jq -n '{gate_result: "SKIP", summary_file: ""}')
        agent_write_result "$worker_dir" "success" 0 "$outputs_json"
        return 0
    fi

    log "Generating final summary by resuming $resume_from_agent session: $session_id"

    # Resume the executor's session with summary prompt
    run_agent_resume "$session_id" \
        "$(_get_final_summary_prompt)" \
        "$worker_dir/logs/iteration-summary.log" "$max_turns"

    # Extract to summaries/summary.txt (parse stream-JSON to get text, then extract summary tags)
    if [ -f "$worker_dir/logs/iteration-summary.log" ]; then
        grep '"type":"assistant"' "$worker_dir/logs/iteration-summary.log" | \
            jq -r 'select(.message.content[]? | .type == "text") | .message.content[] | select(.type == "text") | .text' 2>/dev/null | \
            sed -n '/<summary>/,/<\/summary>/p' | \
            sed '1d;$d' > "$worker_dir/summaries/summary.txt"
        log "Final summary saved to summaries/summary.txt"
    fi

    # Write structured agent result
    local gate_result="PASS"
    if [ ! -s "$worker_dir/summaries/summary.txt" ]; then
        gate_result="SKIP"
        log_warn "Summary file is empty - marking as SKIP"
    fi

    local outputs_json
    outputs_json=$(jq -n \
        --arg gate_result "$gate_result" \
        --arg summary_file "summaries/summary.txt" \
        '{
            gate_result: $gate_result,
            summary_file: $summary_file
        }')

    agent_write_result "$worker_dir" "success" 0 "$outputs_json"

    return 0
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
