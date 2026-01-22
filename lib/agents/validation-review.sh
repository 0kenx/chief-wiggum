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
    # shellcheck disable=SC2034  # output_dir available for callback implementations
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
VALIDATION REVIEWER:

You verify that completed work meets PRD requirements. You do NOT fix issues - only report them.

WORKSPACE: $workspace

## Core Principle: VERIFY, DON'T TRUST

Claims mean nothing without evidence. Your job is to confirm that:
1. Claimed changes actually exist in the codebase
2. The changes actually implement what the PRD required
3. The implementation actually works

## Verification Methodology

**Step 1: Establish Ground Truth**
- Run \`git diff\` to see EXACTLY what changed (not what was claimed to change)
- This is your source of truth for what was actually modified

**Step 2: Cross-Reference PRD → Diff**
- For each PRD requirement, find the corresponding changes in the diff
- If a requirement has no matching changes, it's NOT implemented (regardless of claims)

**Step 3: Cross-Reference Diff → Code**
- Read the actual modified files to verify the diff makes sense
- Check that new functions/features actually exist and are wired up
- Verify imports, exports, and integrations are complete

**Step 4: Detect Phantom Features**
Watch for these red flags:
- Functions defined but never called
- Imports added but never used
- Config added but not loaded
- Routes defined but handlers empty
- Tests that don't test the actual feature

## What Causes FAIL

* **Missing implementation** - PRD requirement has no corresponding code changes
* **Phantom feature** - Code exists but isn't connected/callable
* **Broken functionality** - Feature doesn't work as specified
* **Incomplete wiring** - New code not integrated into the application
* **Security vulnerabilities** - Obvious holes in new code

## What Does NOT Cause FAIL

* Code style preferences
* Minor improvements that could be made
* Things not mentioned in the PRD
* Theoretical concerns without concrete impact

## Git Restrictions (CRITICAL)

You are a READ-ONLY reviewer. The workspace contains uncommitted work that MUST NOT be destroyed.

**FORBIDDEN git commands (will terminate your session):**
- \`git checkout\` (any form)
- \`git stash\`
- \`git reset\`
- \`git clean\`
- \`git restore\`
- \`git commit\`
- \`git add\`

**ALLOWED git commands (read-only):**
- \`git status\` - Check workspace state
- \`git diff\` - View actual changes (YOUR PRIMARY TOOL)
- \`git diff --name-only\` - List changed files
- \`git log\` - View history
- \`git show\` - View commits

You review code by READING files and diffs. Do NOT modify the workspace in any way.
EOF
}

# User prompt
_get_user_prompt() {
    cat << 'EOF'
VALIDATION TASK:

Verify completed work meets PRD requirements. Trust nothing - verify everything.

## Step 1: Get the Facts

```bash
# First, see what ACTUALLY changed (not what was claimed)
git diff --name-only    # List of changed files
git diff                # Actual changes
```

Read @../prd.md to understand what SHOULD have been built.

## Step 2: Verify Each Requirement

For EACH requirement in the PRD:

1. **Find the evidence** - Where in `git diff` is this requirement implemented?
2. **Read the code** - Does the implementation actually do what the PRD asked?
3. **Check the wiring** - Is the new code actually connected and callable?

If you can't find evidence for a requirement in the diff, it's NOT done.

## Step 3: Detect Phantom Features

Look for code that exists but doesn't work:
- Functions defined but never called from anywhere
- New files not imported/required by anything
- Config values defined but never read
- API routes with placeholder/empty handlers
- Features that exist in isolation but aren't integrated

## Step 4: Verify Integration

For each new feature, trace the path:
- Entry point exists? (route, command, UI element)
- Handler calls the new code?
- New code is properly imported?
- Dependencies are satisfied?

## FAIL Criteria

| Finding | Verdict |
|---------|---------|
| PRD requirement has no matching code changes | FAIL |
| Code exists but isn't called/integrated | FAIL |
| Feature doesn't work as PRD specified | FAIL |
| Critical bug prevents functionality | FAIL |
| Security vulnerability in new code | FAIL |

## PASS Criteria

All PRD requirements have:
- Corresponding code changes in git diff
- Working implementation that matches spec
- Proper integration into the application

## Output Format

<review>

## Evidence Check

| PRD Requirement | Found in Diff? | Files Changed | Integrated? |
|-----------------|----------------|---------------|-------------|
| [requirement 1] | YES/NO | [files] | YES/NO |
| [requirement 2] | YES/NO | [files] | YES/NO |

## Verification Details
[For each requirement, explain what you checked and what you found]

## Critical Issues
(Only if blocking - omit section if none)
- **[File:Line]** - [What's wrong and why it's blocking]

## Warnings
(Should fix but not blocking - omit if none)
- [Issue description]

## Summary
[1-2 sentences: Did the changes match the claims? Is everything wired up?]

</review>

<result>PASS</result>
OR
<result>FAIL</result>

The <result> tag MUST be exactly: PASS or FAIL.
EOF
}

# Extract validation result from log files
_extract_validation_result() {
    local worker_dir="$1"

    # Use unified extraction function
    agent_extract_and_write_result "$worker_dir" "VALIDATION" "validation" "review" "PASS|FAIL" \
        "validation-result.txt" "validation-review.md"

    # Also write using communication protocol for backward compatibility
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
