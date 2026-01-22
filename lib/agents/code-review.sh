#!/usr/bin/env bash
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: code-review
# AGENT_DESCRIPTION: Code review agent that reviews code changes for bugs,
#   code smells, and best practices. Uses ralph loop pattern with summaries.
#   Reviews staged changes, specific commits, or branch differences based on
#   REVIEW_SCOPE env var. Returns APPROVE/REQUEST_CHANGES/COMMENT result.
# REQUIRED_PATHS:
#   - workspace : Directory containing the code to review
# OUTPUT_FILES:
#   - review-report.md  : Detailed code review findings
#   - review-result.txt : Contains APPROVE, REQUEST_CHANGES, or COMMENT
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "code-review" "Code review agent that reviews changes for bugs, code smells, and best practices"

# Required paths before agent can run
agent_required_paths() {
    echo "workspace"
}

# Output files that must exist (non-empty) after agent completes
agent_output_files() {
    echo "review-result.txt"
}

# Source dependencies using base library helpers
agent_source_core
agent_source_ralph

# Global for result tracking
REVIEW_RESULT="UNKNOWN"

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    # Use config values (set by load_agent_config in agent-registry, with env var override)
    local max_turns="${WIGGUM_CODE_REVIEW_MAX_TURNS:-${AGENT_CONFIG_MAX_TURNS:-50}}"
    local max_iterations="${WIGGUM_CODE_REVIEW_MAX_ITERATIONS:-${AGENT_CONFIG_MAX_ITERATIONS:-6}}"

    local workspace="$worker_dir/workspace"

    if [ ! -d "$workspace" ]; then
        log_error "Workspace not found: $workspace"
        REVIEW_RESULT="UNKNOWN"
        return 1
    fi

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Clean up old review files before re-running
    rm -f "$worker_dir/review-result.txt" "$worker_dir/review-report.md"
    rm -f "$worker_dir/logs/review-"*.log
    rm -f "$worker_dir/summaries/review-"*.txt

    log "Running code review..."

    # Determine review scope
    local review_scope="${REVIEW_SCOPE:-staged}"
    log "Review scope: $review_scope"

    # Set up callback context using base library
    agent_setup_context "$worker_dir" "$workspace" "$project_dir"
    _REVIEW_SCOPE="$review_scope"

    # Run review loop
    run_ralph_loop "$workspace" \
        "$(_get_system_prompt "$workspace" "$review_scope")" \
        "_review_user_prompt" \
        "_review_completion_check" \
        "$max_iterations" "$max_turns" "$worker_dir" "review"

    local agent_exit=$?

    # Parse result from the latest review log
    _extract_review_result "$worker_dir"

    if [ $agent_exit -eq 0 ]; then
        log "Code review completed with result: $REVIEW_RESULT"
    else
        log_warn "Code review had issues (exit: $agent_exit)"
    fi

    return $agent_exit
}

# User prompt callback for ralph loop
_review_user_prompt() {
    local iteration="$1"
    local output_dir="$2"

    # Always include the initial prompt to ensure full context after summarization
    _get_user_prompt "$_REVIEW_SCOPE"

    if [ "$iteration" -gt 0 ]; then
        # Add continuation context for subsequent iterations
        local prev_iter=$((iteration - 1))
        cat << CONTINUE_EOF

CONTINUATION CONTEXT (Iteration $iteration):

Your previous review work is summarized in @../summaries/review-$prev_iter-summary.txt.

Please continue your review:
1. If you haven't completed all review categories, continue from where you left off
2. If you found issues that need deeper investigation, investigate them now
3. When your review is complete, provide the final <review> and <result> tags

Remember: The <result> tag must contain exactly APPROVE, REQUEST_CHANGES, or COMMENT.
CONTINUE_EOF
    fi
}

# Completion check callback - returns 0 if review is complete
_review_completion_check() {
    # Check if any review log contains a result tag
    local worker_dir
    worker_dir=$(agent_get_worker_dir)
    local latest_log
    latest_log=$(find "$worker_dir/logs" -maxdepth 1 -name "review-*.log" ! -name "*summary*" -printf '%T@ %p\n' 2>/dev/null | sort -rn | head -1 | cut -d' ' -f2-)

    if [ -n "$latest_log" ] && [ -f "$latest_log" ]; then
        if grep -qP '<result>(APPROVE|REQUEST_CHANGES|COMMENT)</result>' "$latest_log" 2>/dev/null; then
            return 0  # Complete
        fi
    fi

    return 1  # Not complete
}

# System prompt
_get_system_prompt() {
    local workspace="$1"
    local review_scope="$2"

    cat << EOF
CODE REVIEWER ROLE:

You are a code review agent. Your job is to review code changes for bugs,
security issues, code smells, and best practices violations.

WORKSPACE: $workspace
REVIEW SCOPE: $review_scope

You have READ-ONLY intent - focus on reviewing and analyzing, not making changes.
Document all findings clearly with file paths, line numbers, and severity levels.
EOF
}

# User prompt
_get_user_prompt() {
    local review_scope="$1"
    local scope_instructions

    case "$review_scope" in
        staged)
            scope_instructions="Review the staged changes using 'git diff --cached'."
            ;;
        commit:*)
            local sha="${review_scope#commit:}"
            scope_instructions="Review the specific commit $sha using 'git show $sha'."
            ;;
        branch:*)
            local branch="${review_scope#branch:}"
            scope_instructions="Review all changes in branch $branch compared to main using 'git diff main...$branch'."
            ;;
        *)
            scope_instructions="Review all uncommitted changes using 'git diff'."
            ;;
    esac

    cat << EOF
CODE REVIEW TASK:

$scope_instructions

REVIEW CATEGORIES:

1. **Bugs and Logic Errors** (BLOCKER)
   - Off-by-one errors, null pointer dereferences
   - Race conditions, deadlocks
   - Incorrect algorithm implementations
   - Broken edge cases

2. **Security Issues** (BLOCKER/CRITICAL)
   - Injection vulnerabilities (SQL, command, XSS)
   - Hardcoded credentials or secrets
   - Insecure deserialization
   - Missing input validation at boundaries
   - Authentication/authorization flaws

3. **Code Smells** (MAJOR/MINOR)
   - Duplicated code
   - Overly complex methods (high cyclomatic complexity)
   - Dead code or unused variables
   - Poor naming conventions
   - Missing error handling

4. **Best Practices** (MAJOR/MINOR)
   - Not following project conventions
   - Breaking SOLID principles
   - Missing documentation for public APIs
   - Improper use of language features

5. **Performance Issues** (MAJOR/MINOR)
   - N+1 query patterns
   - Unnecessary loops or allocations
   - Missing caching opportunities
   - Blocking operations in async code

SEVERITY DEFINITIONS:

- BLOCKER: Must be fixed before merge, causes crashes/data loss/security breach
- CRITICAL: Should be fixed before merge, significant functionality impact
- MAJOR: Should be addressed, impacts maintainability/performance
- MINOR: Nice to fix, minor improvements
- INFO: Suggestions or observations

DECISION CRITERIA:

- REQUEST_CHANGES: Any BLOCKER or CRITICAL issues found
- APPROVE: No blockers, may have MAJOR/MINOR issues (note them for follow-up)
- COMMENT: Only INFO-level suggestions, no real issues

OUTPUT FORMAT:

You MUST provide your response in this EXACT structure with both tags:

<review>

## Summary

[1-2 sentence overview of the changes reviewed]

## Findings

### BLOCKER

- **[File:Line]** [Issue description]
  - **Why:** [Explanation of impact]
  - **Fix:** [Suggested remediation]

### CRITICAL

- **[File:Line]** [Issue description]
  - **Why:** [Explanation of impact]
  - **Fix:** [Suggested remediation]

### MAJOR

- **[File:Line]** [Issue description]

### MINOR

- **[File:Line]** [Issue description]

### INFO

- [Suggestions or observations]

## Statistics

- Files reviewed: [N]
- Lines changed: [+X/-Y]
- Issues found: [N BLOCKER, N CRITICAL, N MAJOR, N MINOR]

## Recommendation

[Brief statement of your recommendation]

</review>

<result>APPROVE</result>

OR

<result>REQUEST_CHANGES</result>

OR

<result>COMMENT</result>

CRITICAL: The <result> tag MUST contain exactly one of: APPROVE, REQUEST_CHANGES, or COMMENT.
This tag is parsed programmatically to determine if the changes can proceed.
EOF
}

# Extract review result from log files
_extract_review_result() {
    local worker_dir="$1"

    REVIEW_RESULT="UNKNOWN"

    # Find the latest review log (excluding summary logs)
    local log_file
    log_file=$(find "$worker_dir/logs" -maxdepth 1 -name "review-*.log" ! -name "*summary*" -printf '%T@ %p\n' 2>/dev/null | sort -rn | head -1 | cut -d' ' -f2-)

    if [ -n "$log_file" ] && [ -f "$log_file" ]; then
        # Extract review content between <review> tags
        local review_path="$worker_dir/review-report.md"
        if grep -q '<review>' "$log_file"; then
            sed -n '/<review>/,/<\/review>/p' "$log_file" | sed '1d;$d' > "$review_path"
            log "Code review report saved to review-report.md"
        fi

        # Extract result tag (APPROVE, REQUEST_CHANGES, or COMMENT)
        REVIEW_RESULT=$(grep -oP '(?<=<result>)(APPROVE|REQUEST_CHANGES|COMMENT)(?=</result>)' "$log_file" | head -1)
        if [ -z "$REVIEW_RESULT" ]; then
            REVIEW_RESULT="UNKNOWN"
        fi
    fi

    # Store result in standard location
    echo "$REVIEW_RESULT" > "$worker_dir/review-result.txt"
}

# Check review result from a worker directory (utility for callers)
# Returns: 0 if APPROVE, 1 if REQUEST_CHANGES/COMMENT/UNKNOWN
check_review_result() {
    local worker_dir="$1"
    local result_file="$worker_dir/review-result.txt"

    if [ -f "$result_file" ]; then
        local result
        result=$(cat "$result_file")
        if [ "$result" = "APPROVE" ]; then
            return 0
        fi
    fi

    return 1
}
