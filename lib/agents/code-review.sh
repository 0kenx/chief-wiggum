#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: code-review
# AGENT_DESCRIPTION: Code review agent that reviews code changes for bugs,
#   code smells, and best practices. Uses ralph loop pattern with summaries.
#   Reviews staged changes, specific commits, or branch differences based on
#   REVIEW_SCOPE env var. Returns PASS/FAIL/FIX result.
# REQUIRED_PATHS:
#   - workspace : Directory containing the code to review
# OUTPUT_FILES:
#   - review-report.md  : Detailed code review findings
#   - review-result.txt : Contains PASS, FAIL, or FIX
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "code-review" "Code review agent that reviews changes for bugs, code smells, and best practices"

# Required paths before agent can run
agent_required_paths() {
    echo "workspace"
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

Remember: The <result> tag must contain exactly PASS, FAIL, or FIX.
CONTINUE_EOF
    fi
}

# Completion check callback - returns 0 if review is complete
_review_completion_check() {
    # Check if any review log contains a result tag
    local worker_dir
    worker_dir=$(agent_get_worker_dir)
    local latest_log
    latest_log=$(find "$worker_dir/logs" -name "review-*.log" ! -name "*summary*" -printf '%T@ %p\n' 2>/dev/null | sort -rn | head -1 | cut -d' ' -f2-)

    if [ -n "$latest_log" ] && [ -f "$latest_log" ]; then
        if grep -qP '<result>(PASS|FAIL|FIX)</result>' "$latest_log" 2>/dev/null; then
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

You are a senior code reviewer. Your job is to catch real issues that would
cause problems in production - not to nitpick style or make suggestions.

WORKSPACE: $workspace
REVIEW SCOPE: $review_scope

You have READ-ONLY intent - focus on reviewing and analyzing, not making changes.

## Review Philosophy

* Only comment when you have HIGH CONFIDENCE (>80%) that an issue exists
* Be concise: one sentence per comment when possible
* Focus on actionable feedback, not observations or suggestions
* Prioritize issues by actual impact, not theoretical concerns
* If you're uncertain whether something is wrong, DON'T COMMENT
* Assume CI handles linting, formatting, and test failures - don't duplicate
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

## Priority Areas (Review These)

### Security & Safety (BLOCKER/CRITICAL)

* Injection vulnerabilities (SQL, command, XSS)
* Path traversal or directory escape
* Hardcoded credentials or secrets
* Missing input validation on untrusted data
* Authentication/authorization flaws
* Insecure deserialization
* Unsafe use of eval, exec, or shell commands
* Memory leaks or resource exhaustion

### Correctness Issues (BLOCKER/CRITICAL)

* Logic errors that cause incorrect behavior
* Null/undefined dereferences or unhandled edge cases
* Race conditions in concurrent code
* Resource leaks (files, connections, memory)
* Incorrect error propagation

### Reliability Issues (MAJOR)

* Missing error handling for operations that can fail
* Broken error recovery paths
* Unhandled edge cases that will occur in production
* State corruption possibilities

### Architecture Issues (MAJOR)

* Code that violates existing patterns in the codebase
* Breaking public API contracts
* Missing cleanup/disposal of resources

## Skip These (Low Value - DO NOT Comment)

* Style/formatting (linters handle this)
* Minor naming suggestions
* Suggestions to add comments or documentation
* Refactoring ideas unless fixing a real bug
* "Consider using X instead of Y" without a concrete problem
* Theoretical performance concerns without evidence
* Test coverage suggestions
* Type annotation suggestions

## When to Stay Silent

If you're uncertain whether something is an issue, DON'T COMMENT.
The goal is HIGH SIGNAL comments only. A review with zero comments is
perfectly fine if the code is good.

## Severity Definitions

* BLOCKER: Causes crashes, data loss, security breach. Must fix before merge.
* CRITICAL: Significant functionality impact. Should fix before merge.
* MAJOR: Impacts maintainability or reliability. Note for follow-up.
* MINOR: Small improvements. Optional.

## Decision Criteria

* FAIL: Any BLOCKER or CRITICAL issues
* FIX: MAJOR issues worth addressing but not blocking
* PASS: No blockers, no major issues (may have MINOR notes)

## Response Format

Be concise. For each issue:
1. State the problem (1 sentence)
2. Why it matters (1 sentence, only if not obvious)
3. Suggested fix (code snippet or specific action)

<review>

## Summary
[1-2 sentences: what changed and overall assessment]

## Findings

### BLOCKER
- **file:line** - Problem statement. Fix: \`suggested code\`

### CRITICAL
- **file:line** - Problem statement. Fix: \`suggested code\`

### MAJOR
- **file:line** - Problem statement

### MINOR
- **file:line** - Problem statement

(Omit empty sections entirely)

## Stats
Files: N | Lines: +X/-Y | Issues: N blocker, N critical, N major, N minor

</review>

<result>PASS</result>
OR
<result>FAIL</result>
OR
<result>FIX</result>

The <result> tag is parsed programmatically. It MUST be exactly one of: PASS, FAIL, FIX.
EOF
}

# Extract review result from log files
_extract_review_result() {
    local worker_dir="$1"

    # Use unified extraction function (5-arg: worker_dir, name, log_prefix, report_tag, valid_values)
    agent_extract_and_write_result "$worker_dir" "REVIEW" "review" "review" "PASS|FAIL|FIX"
    REVIEW_RESULT="$REVIEW_RESULT"
}

# Check review result from a worker directory (utility for callers)
# Returns: 0 if PASS, 1 if FAIL/FIX/UNKNOWN
check_review_result() {
    local worker_dir="$1"
    local result
    result=$(agent_read_subagent_result "$worker_dir" "code-review")
    [ "$result" = "PASS" ]
}
