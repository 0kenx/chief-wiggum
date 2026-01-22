#!/usr/bin/env bash
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: documentation-writer
# AGENT_DESCRIPTION: Documentation update agent that updates existing markdown
#   files to document code changes. Scoped to current task changes only. Updates
#   README, inline comments, and docstrings. Does NOT create new markdown files.
#   Non-blocking agent that returns PASS/SKIP (never fails the workflow).
# REQUIRED_PATHS:
#   - workspace : Directory containing the code to document
# OUTPUT_FILES:
#   - docs-result.txt : Contains PASS, FAIL, or SKIP
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "documentation-writer" "Documentation update agent for code changes"

# Required paths before agent can run
agent_required_paths() {
    echo "workspace"
}

# Output files that must exist (non-empty) after agent completes
agent_output_files() {
    echo "docs-result.txt"
}

# Source dependencies using base library helpers
agent_source_core
agent_source_once

# Global for result tracking
DOCS_RESULT="UNKNOWN"

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    # Use config values (set by load_agent_config in agent-registry, with env var override)
    # Documentation uses a single run with high max_turns (no iteration loop)
    local max_turns="${WIGGUM_DOCS_WRITER_MAX_TURNS:-${AGENT_CONFIG_MAX_TURNS:-100}}"

    local workspace="$worker_dir/workspace"

    if [ ! -d "$workspace" ]; then
        log_error "Workspace not found: $workspace"
        DOCS_RESULT="SKIP"
        echo "SKIP" > "$worker_dir/docs-result.txt"
        return 0
    fi

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Clean up old docs files before re-running
    rm -f "$worker_dir/docs-result.txt" "$worker_dir/docs-report.md"
    rm -f "$worker_dir/logs/docs-"*.log

    log "Running documentation update..."

    # Set up callback context using base library
    agent_setup_context "$worker_dir" "$workspace" "$project_dir"

    # Build prompts
    local system_prompt user_prompt
    system_prompt=$(_get_system_prompt "$workspace")
    user_prompt=$(_get_user_prompt)

    local log_file
    log_file="$worker_dir/logs/docs-$(date +%Y%m%d-%H%M%S).log"

    # Run once with high max_turns (no iteration loop needed for docs)
    run_agent_once "$workspace" "$system_prompt" "$user_prompt" "$log_file" "$max_turns"
    # Exit code intentionally ignored - documentation is non-blocking

    # Parse result from the log
    _extract_docs_result "$worker_dir"

    # Documentation agent never fails - ensure we return PASS or SKIP
    if [ "$DOCS_RESULT" != "PASS" ] && [ "$DOCS_RESULT" != "SKIP" ]; then
        DOCS_RESULT="PASS"
        echo "PASS" > "$worker_dir/docs-result.txt"
    fi

    log "Documentation update completed with result: $DOCS_RESULT"

    # Always return success - documentation is non-blocking
    return 0
}

# System prompt
_get_system_prompt() {
    local workspace="$1"

    cat << EOF
DOCUMENTATION WRITER:

You update existing documentation to reflect code changes made in this task. You do NOT create new files.

WORKSPACE: $workspace

## Documentation Philosophy

* UPDATE EXISTING ONLY - Modify existing markdown files; never create new ones
* SCOPE TO CHANGES - Only document code that was added or modified in this task
* MINIMAL CHANGES - Change only what's necessary; don't rewrite sections unnecessarily
* MATCH STYLE - Follow the existing documentation tone and format exactly

## What You MUST Do

* Find existing documentation (README.md, docs/*.md, inline comments)
* Update only the sections relevant to the code changes
* Add docstrings/comments to new functions in source files
* Keep changes minimal and focused

## What You MUST NOT Do

* Create new markdown files (no new README sections as separate files)
* Rewrite existing documentation that isn't affected by changes
* Add documentation infrastructure (no mkdocs, docusaurus, etc.)
* Document code that wasn't modified in this task
* Change documentation style or formatting conventions

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
- \`git add <your-doc-files>\` (stage your documentation changes)
- \`git commit -m "..."\` (commit your work)

**IMPORTANT:** Commit your documentation changes before completing. Use a descriptive commit message.
Do NOT revert, stash, or reset files - the workspace contains other agents' work.
EOF
}

# Get context files section for user prompt
_get_context_section() {
    local worker_dir
    worker_dir=$(agent_get_worker_dir)

    cat << 'EOF'
## Context

Before updating documentation, understand what was implemented:

EOF

    # Check for PRD
    if [ -f "$worker_dir/prd.md" ]; then
        cat << 'EOF'
1. **Read the PRD** (@../prd.md) - Understand what feature/fix was requested
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
DOCUMENTATION UPDATE TASK:

Update existing documentation to reflect the code changes made in this task.

## Step 1: Identify What Changed

From the implementation summary, identify:
- New public functions/APIs that need docstrings
- New CLI commands/flags that need README updates
- New configuration options that need documentation
- Changed behavior that affects existing documentation

## Step 2: Find Existing Documentation

Look for:
- `README.md` - main project documentation
- `docs/` directory - additional documentation
- Inline comments and docstrings in modified source files
- Configuration file comments

**If no documentation exists → SKIP** (do not create new files)

## Step 3: Update Documentation

### What to Update

| Change Type | Documentation Update |
|-------------|---------------------|
| New public function | Add docstring in source file |
| New CLI command | Update existing README.md section |
| New config option | Update existing config docs or README |
| Changed behavior | Update affected sections in existing docs |
| New API endpoint | Update existing API docs |

### Update Guidelines

* **Minimal changes** - Only modify what's necessary
* **Match style** - Copy the existing format exactly
* **Be accurate** - Documentation must match implementation
* **Add examples** - If existing docs have examples, add examples for new features

### What NOT to Do

* Create new .md files
* Restructure existing documentation
* Add documentation tooling or generators
* Document internal implementation details
* Update docs for unchanged code

## Step 4: Add Inline Documentation

For new functions/methods in source files:
- Add docstrings following project conventions
- Document parameters, return values, exceptions
- Keep comments concise and useful

## Result Criteria

* **PASS**: Documentation updated, or attempted update with best effort
* **SKIP**: No documentation exists to update, or no user-facing changes

Note: This agent never returns FAIL. Documentation is best-effort and non-blocking.

## Output Format

<report>

## Summary
[1-2 sentences: what documentation was updated]

## Files Updated

| File | Change Type | Description |
|------|-------------|-------------|
| [path] | README/docstring/inline | [what was updated] |

## Changes Made
(Brief description of each update)

- **[file]**: [what was added/changed]

## Skipped
(If any documentation was intentionally not updated - omit if none)

- [reason for skipping]

</report>

<result>PASS</result>
OR
<result>SKIP</result>

The <result> tag MUST be exactly: PASS or SKIP.
EOF
}

# Extract docs result from log files
_extract_docs_result() {
    local worker_dir="$1"

    # Use unified extraction function
    agent_extract_and_write_result "$worker_dir" "DOCS" "docs" "report" "PASS|SKIP" \
        "docs-result.txt" "docs-report.md"
}

# Check docs result from a worker directory (utility for callers)
# Returns: 0 if PASS, 1 if FAIL, 2 if SKIP/UNKNOWN
check_docs_result() {
    local worker_dir="$1"
    local result_file="$worker_dir/docs-result.txt"

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
