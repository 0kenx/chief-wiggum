---
type: general.task-summarizer
description: Generates final task summary by resuming the executor session
required_paths: [workspace]
valid_results: [PASS, SKIP]
mode: resume
session_from: parent
output_path: summaries/summary.txt
outputs: [summary_file]
---

<WIGGUM_USER_PROMPT>
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
</WIGGUM_USER_PROMPT>
