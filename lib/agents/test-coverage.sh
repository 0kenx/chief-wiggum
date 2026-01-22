#!/usr/bin/env bash
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: test-coverage
# AGENT_DESCRIPTION: Test generation agent that writes tests for modified code
#   using the project's existing test framework. Scoped to current task changes
#   only. Does NOT introduce new test frameworks or dependencies. Adds tests to
#   existing test files or creates new test files following project conventions.
#   Returns PASS/FAIL/SKIP result.
# REQUIRED_PATHS:
#   - workspace : Directory containing the code to test
# OUTPUT_FILES:
#   - test-result.txt : Contains PASS, FAIL, or SKIP
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "test-coverage" "Test generation agent for modified code using existing framework"

# Required paths before agent can run
agent_required_paths() {
    echo "workspace"
}

# Output files that must exist (non-empty) after agent completes
agent_output_files() {
    echo "test-result.txt"
}

# Source dependencies using base library helpers
agent_source_core
agent_source_ralph

# Global for result tracking
TEST_RESULT="UNKNOWN"

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    # Use config values (set by load_agent_config in agent-registry, with env var override)
    local max_turns="${WIGGUM_TEST_COVERAGE_MAX_TURNS:-${AGENT_CONFIG_MAX_TURNS:-60}}"
    local max_iterations="${WIGGUM_TEST_COVERAGE_MAX_ITERATIONS:-${AGENT_CONFIG_MAX_ITERATIONS:-8}}"

    local workspace="$worker_dir/workspace"

    if [ ! -d "$workspace" ]; then
        log_error "Workspace not found: $workspace"
        TEST_RESULT="UNKNOWN"
        return 1
    fi

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Clean up old test files before re-running
    rm -f "$worker_dir/test-result.txt" "$worker_dir/test-report.md"
    rm -f "$worker_dir/logs/test-"*.log
    rm -f "$worker_dir/summaries/test-"*.txt

    log "Running test generation..."

    # Set up callback context using base library
    agent_setup_context "$worker_dir" "$workspace" "$project_dir"

    # Run test loop
    run_ralph_loop "$workspace" \
        "$(_get_system_prompt "$workspace")" \
        "_test_user_prompt" \
        "_test_completion_check" \
        "$max_iterations" "$max_turns" "$worker_dir" "test"

    local agent_exit=$?

    # Parse result from the latest test log
    _extract_test_result "$worker_dir"

    if [ $agent_exit -eq 0 ]; then
        log "Test generation completed with result: $TEST_RESULT"
    else
        log_warn "Test generation had issues (exit: $agent_exit)"
    fi

    return $agent_exit
}

# User prompt callback for ralph loop
_test_user_prompt() {
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

Your previous test work is summarized in @../summaries/test-$prev_iter-summary.txt.

Please continue:
1. If you haven't finished writing tests, continue from where you left off
2. If tests are written but not run, run them now
3. If tests failed due to test bugs, fix the tests and re-run
4. When complete, provide the final <report> and <result> tags

Remember: The <result> tag must contain exactly PASS, FAIL, or SKIP.
CONTINUE_EOF
    fi
}

# Completion check callback - returns 0 if test run is complete
_test_completion_check() {
    # Check if any test log contains a result tag
    local worker_dir
    worker_dir=$(agent_get_worker_dir)
    local latest_log
    latest_log=$(find "$worker_dir/logs" -maxdepth 1 -name "test-*.log" ! -name "*summary*" -printf '%T@ %p\n' 2>/dev/null | sort -rn | head -1 | cut -d' ' -f2-)

    if [ -n "$latest_log" ] && [ -f "$latest_log" ]; then
        if grep -qP '<result>(PASS|FAIL|SKIP)</result>' "$latest_log" 2>/dev/null; then
            return 0  # Complete
        fi
    fi

    return 1  # Not complete
}

# System prompt
_get_system_prompt() {
    local workspace="$1"

    cat << EOF
TEST COVERAGE AGENT:

You write tests for code that was modified in this task. You do NOT introduce new frameworks.

WORKSPACE: $workspace

## Testing Philosophy

* USE EXISTING FRAMEWORK ONLY - Find what test framework the project uses; use that
* SCOPE TO CHANGES - Only test code that was added or modified in this task
* FOLLOW PROJECT PATTERNS - Match existing test file structure, naming, and style
* MEANINGFUL TESTS - Write tests that verify behavior, not just coverage

## What You MUST Do

* Find the project's existing test framework (jest, pytest, go test, etc.)
* Study existing test files to understand patterns and conventions
* Write tests using ONLY the existing framework and test utilities
* Place tests in the correct location following project structure

## What You MUST NOT Do

* Install new test frameworks or dependencies
* Add new testing libraries (no adding jest if project uses mocha)
* Create test infrastructure that doesn't exist
* Write tests for code you didn't modify
* Change existing tests unless they test modified code

## Git Restrictions (CRITICAL)

The workspace contains uncommitted work from other agents. You MUST NOT destroy it.

**FORBIDDEN git commands (will terminate your session):**
- \`git checkout -- <file>\` - DESTROYS uncommitted file changes
- \`git checkout .\` - DESTROYS all uncommitted changes
- \`git stash\` - Hides uncommitted changes
- \`git reset --hard\` - DESTROYS uncommitted changes
- \`git clean\` - DELETES untracked files
- \`git restore\` - DESTROYS uncommitted changes

**ALLOWED git commands:**
- \`git status\`, \`git diff\`, \`git log\`, \`git show\` (read-only)
- \`git add <your-test-files>\` (stage your test changes)
- \`git commit -m "..."\` (commit your work)

**IMPORTANT:** Commit your test changes before completing. Use a descriptive commit message.
Do NOT revert, stash, or reset files - the workspace contains other agents' work.
EOF
}

# Get context files section for user prompt
_get_context_section() {
    local worker_dir
    worker_dir=$(agent_get_worker_dir)

    cat << 'EOF'
## Context

Before writing tests, understand what was implemented:

EOF

    # Check for PRD
    if [ -f "$worker_dir/prd.md" ]; then
        cat << 'EOF'
1. **Read the PRD** (@../prd.md) - Understand requirements and acceptance criteria
EOF
    fi

    # Check for implementation summary
    if [ -f "$worker_dir/summaries/summary.txt" ]; then
        cat << 'EOF'
2. **Read the Implementation Summary** (@../summaries/summary.txt) - Understand what was built
EOF
    fi

    echo ""
}

# User prompt
_get_user_prompt() {
    # Include context section first
    _get_context_section

    cat << 'EOF'
TEST GENERATION TASK:

Write tests for the code changes made in this task, using the project's existing test framework.

## Step 1: Discover Test Framework

Find what the project uses:
- `package.json` → look for jest, mocha, vitest, ava in devDependencies
- `pytest.ini`, `pyproject.toml` → pytest
- `*_test.go` files → go test
- `Cargo.toml` with `[dev-dependencies]` → cargo test
- Existing test files → follow their patterns exactly

**If no test framework exists → SKIP** (do not install one)

## Step 2: Identify What to Test

From the implementation summary, identify:
- New functions/methods that were added
- Modified functions with changed behavior
- New API endpoints or commands
- Edge cases and error handling in new code

**Only test code from this task's changes.**

## Step 3: Write Tests

### Location
- Find where existing tests live (test/, tests/, __tests__/, *_test.*, *.spec.*)
- Add tests in the same structure
- If testing new file `src/foo.js`, create `test/foo.test.js` (or match existing pattern)

### Content
- Import/require using project's existing patterns
- Use the same assertion style as existing tests
- Follow naming conventions from existing tests
- Include: happy path, edge cases, error cases for new code

### Quality
- Arrange-Act-Assert structure
- Descriptive test names
- Independent tests (no shared state)
- Test behavior, not implementation details

## Step 4: Run Tests

1. Run the project's test command (npm test, pytest, go test, etc.)
2. If tests fail due to test bugs → fix the tests and re-run
3. If tests fail due to implementation bugs → report as FAIL
4. Ensure existing tests still pass (no regressions)

## Result Criteria

* **PASS**: Tests written for new code, all tests pass
* **FAIL**: Tests reveal implementation bugs that need fixing
* **SKIP**: No test framework exists, or no testable code changes

## Output Format

<report>

## Summary
[1-2 sentences: what was tested]

## Framework Used
[e.g., "jest (existing)" or "pytest (existing)"]

## Tests Added

| File | Tests | Description |
|------|-------|-------------|
| [path] | N | [what it tests] |

## Test Execution

| Suite | Passed | Failed | Skipped |
|-------|--------|--------|---------|
| [name] | N | N | N |

## Failures
(Only if implementation bugs found - omit if all pass)

### [Test Name]
- **Error**: [message]
- **Analysis**: [why this is an implementation bug, not test bug]

</report>

<result>PASS</result>
OR
<result>FAIL</result>
OR
<result>SKIP</result>

The <result> tag MUST be exactly: PASS, FAIL, or SKIP.
EOF
}

# Extract test result from log files
_extract_test_result() {
    local worker_dir="$1"

    # Use unified extraction function
    agent_extract_and_write_result "$worker_dir" "TEST" "test" "report" "PASS|FAIL|SKIP" \
        "test-result.txt" "test-report.md"
}

# Check test result from a worker directory (utility for callers)
# Returns: 0 if PASS, 1 if FAIL, 2 if SKIP/UNKNOWN
check_test_result() {
    local worker_dir="$1"
    local result_file="$worker_dir/test-result.txt"

    if [ -f "$result_file" ]; then
        local result
        result=$(cat "$result_file")
        case "$result" in
            PASS)
                return 0
                ;;
            FAIL)
                return 1
                ;;
            SKIP|UNKNOWN|*)
                return 2
                ;;
        esac
    fi

    return 2
}
