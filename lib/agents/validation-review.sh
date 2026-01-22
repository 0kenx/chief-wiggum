#!/usr/bin/env bash
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: validation-review
# AGENT_DESCRIPTION: Code review and validation agent that reviews completed
#   work against PRD requirements. Uses ralph loop pattern with summaries.
#   Performs requirements verification, code quality review, implementation
#   consistency checks, and testing coverage analysis. Returns PASS/FAIL result.
# REQUIRED_PATHS:
#   - prd.md      : Product Requirements Document to validate against
#   - workspace   : Directory containing the completed work to review
# OUTPUT_FILES:
#   - validation-result.txt : Contains PASS, FAIL, or UNKNOWN
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "validation-review" "Code review and validation agent that reviews completed work against PRD requirements"

# Required paths before agent can run
agent_required_paths() {
    echo "prd.md"
    echo "workspace"
}

# Output files that must exist (non-empty) after agent completes
agent_output_files() {
    echo "validation-result.txt"
}

# Source dependencies using base library helpers
agent_source_core
agent_source_ralph

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    # Use config values (set by load_agent_config in agent-registry, with env var override)
    local max_turns="${WIGGUM_VALIDATION_MAX_TURNS:-${AGENT_CONFIG_MAX_TURNS:-50}}"
    local max_iterations="${WIGGUM_VALIDATION_MAX_ITERATIONS:-${AGENT_CONFIG_MAX_ITERATIONS:-5}}"

    local workspace="$worker_dir/workspace"

    if [ ! -d "$workspace" ]; then
        log_error "Workspace not found: $workspace"
        VALIDATION_RESULT="UNKNOWN"
        return 1
    fi

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Clean up old validation files before re-running
    rm -f "$worker_dir/validation-result.txt" "$worker_dir/validation-review.md"
    rm -f "$worker_dir/logs/validation-"*.log
    rm -f "$worker_dir/summaries/validation-"*.txt

    log "Running validation review..."

    # Set up callback context using base library
    agent_setup_context "$worker_dir" "$workspace" "$project_dir"

    # Run validation loop
    run_ralph_loop "$workspace" \
        "$(_get_system_prompt "$workspace")" \
        "_validation_user_prompt" \
        "_validation_completion_check" \
        "$max_iterations" "$max_turns" "$worker_dir" "validation"

    local agent_exit=$?

    # Parse result from the latest validation log
    _extract_validation_result "$worker_dir"

    if [ $agent_exit -eq 0 ]; then
        log "Validation review completed with result: $VALIDATION_RESULT"
    else
        log_warn "Validation review had issues (exit: $agent_exit)"
    fi

    return $agent_exit
}

# User prompt callback for ralph loop
_validation_user_prompt() {
    local iteration="$1"
    local output_dir="$2"

    # Always include the initial prompt to ensure full context after summarization
    _get_user_prompt

    if [ "$iteration" -gt 0 ]; then
        # Add continuation context for subsequent iterations
        local prev_iter=$((iteration - 1))
        cat << CONTINUE_EOF

CONTINUATION CONTEXT (Iteration $iteration):

Your previous review work is summarized in @../summaries/validation-$prev_iter-summary.txt.

Please continue your review:
1. If you haven't completed all review sections, continue from where you left off
2. If you found issues that need deeper investigation, investigate them now
3. When your review is complete, provide the final <review> and <result> tags

Remember: The <result> tag must contain exactly PASS or FAIL.
CONTINUE_EOF
    fi
}

# Completion check callback - returns 0 if review is complete
_validation_completion_check() {
    # Check if any validation log contains a result tag
    local worker_dir
    worker_dir=$(agent_get_worker_dir)
    local latest_log
    latest_log=$(find "$worker_dir/logs" -maxdepth 1 -name "validation-*.log" ! -name "*summary*" -printf '%T@ %p\n' 2>/dev/null | sort -rn | head -1 | cut -d' ' -f2-)

    if [ -n "$latest_log" ] && [ -f "$latest_log" ]; then
        if grep -qP '<result>(PASS|FAIL)</result>' "$latest_log" 2>/dev/null; then
            return 0  # Complete
        fi
    fi

    return 1  # Not complete
}

# System prompt
_get_system_prompt() {
    local workspace="$1"

    cat << EOF
VALIDATION REVIEWER ROLE:

You are a code reviewer and validation agent. Your job is to review completed work
and verify it meets the requirements specified in the PRD.

WORKSPACE: $workspace

You have READ-ONLY intent - focus on reviewing and validating, not making changes.
If you find issues, document them clearly but do not attempt fixes.
EOF
}

# User prompt
_get_user_prompt() {
    cat << 'EOF'
VALIDATION AND REVIEW TASK:

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
This tag is parsed programmatically to determine if the work can proceed to commit/PR creation.
EOF
}

# Extract validation result from log files
_extract_validation_result() {
    local worker_dir="$1"

    VALIDATION_RESULT="UNKNOWN"

    # Find the latest validation log (excluding summary logs)
    local log_file
    log_file=$(find "$worker_dir/logs" -maxdepth 1 -name "validation-*.log" ! -name "*summary*" -printf '%T@ %p\n' 2>/dev/null | sort -rn | head -1 | cut -d' ' -f2-)

    if [ -n "$log_file" ] && [ -f "$log_file" ]; then
        # Extract review content between <review> tags
        local review_path
        review_path=$(agent_comm_path "$worker_dir" "validation-review")
        if grep -q '<review>' "$log_file"; then
            sed -n '/<review>/,/<\/review>/p' "$log_file" | sed '1d;$d' > "$review_path"
            log "Validation review saved to validation-review.md"
        fi

        # Extract result tag (PASS or FAIL)
        VALIDATION_RESULT=$(grep -oP '(?<=<result>)(PASS|FAIL)(?=</result>)' "$log_file" | head -1)
        if [ -z "$VALIDATION_RESULT" ]; then
            VALIDATION_RESULT="UNKNOWN"
        fi
    fi

    # Store result using communication protocol
    agent_write_validation "$worker_dir" "$VALIDATION_RESULT"
}

# Check validation result from a worker directory (utility for callers)
# Returns: 0 if PASS, 1 if FAIL or UNKNOWN
check_validation_result() {
    local worker_dir="$1"
    local result
    result=$(agent_read_validation "$worker_dir")

    if [ "$result" = "PASS" ]; then
        return 0
    else
        return 1
    fi
}
