#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: git-conflict-resolver
# AGENT_DESCRIPTION: Git merge conflict resolver agent that detects and resolves
#   merge conflicts in the workspace. Uses ralph loop pattern with summaries.
#   Parses conflict markers, applies intelligent resolution strategies, and
#   stages resolved files. Does NOT commit - only resolves and stages.
# REQUIRED_PATHS:
#   - workspace : Directory containing the git repository with conflicts
# OUTPUT_FILES:
#   - resolution-summary.md : Documentation of conflict resolutions applied
#   - resolve-result.json   : Contains PASS, FAIL, or SKIP
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "engineering.git-conflict-resolver" "Git merge conflict resolver that detects and resolves conflicts in the workspace"

# Required paths before agent can run
agent_required_paths() {
    echo "workspace"
}

# Source dependencies using base library helpers
agent_source_core
agent_source_ralph

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    # Use config values (set by load_agent_config in agent-registry, with env var override)
    local max_turns="${WIGGUM_CONFLICT_RESOLVER_MAX_TURNS:-${AGENT_CONFIG_MAX_TURNS:-40}}"
    local max_iterations="${WIGGUM_CONFLICT_RESOLVER_MAX_ITERATIONS:-${AGENT_CONFIG_MAX_ITERATIONS:-10}}"

    local workspace="$worker_dir/workspace"

    if [ ! -d "$workspace" ]; then
        log_error "Workspace not found: $workspace"
        return 1
    fi

    # Verify workspace is a git repository
    if [ ! -d "$workspace/.git" ] && ! git -C "$workspace" rev-parse --git-dir &>/dev/null; then
        log_error "Workspace is not a git repository: $workspace"
        return 1
    fi

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Clean up old resolution files before re-running
    rm -f "$worker_dir/reports/resolution-summary.md"
    find "$worker_dir/logs" -name "resolve-*.log" -delete 2>/dev/null || true
    rm -f "$worker_dir/summaries/resolve-"*.txt

    # Check for conflicts
    local conflicted_files
    conflicted_files=$(git -C "$workspace" diff --name-only --diff-filter=U 2>/dev/null)

    if [ -z "$conflicted_files" ]; then
        log "No merge conflicts detected in workspace"
        agent_setup_context "$worker_dir" "$workspace" "$project_dir"
        agent_write_report "$worker_dir" "# Conflict Resolution Summary

**Status:** No conflicts detected

No merge conflicts were found in the workspace. The repository is in a clean state."
        agent_write_result "$worker_dir" "success" 0 '{"gate_result":"SKIP"}'
        return 0
    fi

    local conflict_count
    conflict_count=$(echo "$conflicted_files" | wc -l)
    log "Found $conflict_count file(s) with merge conflicts"

    # Set up callback context using base library
    agent_setup_context "$worker_dir" "$workspace" "$project_dir"

    log "Starting conflict resolution..."

    # Run resolution loop
    run_ralph_loop "$workspace" \
        "$(_get_system_prompt "$workspace")" \
        "_conflict_user_prompt" \
        "_conflict_completion_check" \
        "$max_iterations" "$max_turns" "$worker_dir" "resolve"

    local agent_exit=$?

    # Extract and save resolution summary
    _extract_resolution_summary "$worker_dir"

    # Determine gate result based on remaining conflicts
    local remaining
    remaining=$(git -C "$workspace" diff --name-only --diff-filter=U 2>/dev/null | wc -l)
    if [ "$remaining" -eq 0 ]; then
        agent_write_result "$worker_dir" "success" 0 '{"gate_result":"PASS"}'
        log "Conflict resolution completed successfully"
    else
        agent_write_result "$worker_dir" "failure" 1 "$(printf '{"gate_result":"FAIL","unresolved_files":%d}' "$remaining")"
        log_warn "Conflict resolution incomplete ($remaining file(s) unresolved)"
    fi

    return $agent_exit
}

# User prompt callback for ralph loop
_conflict_user_prompt() {
    local iteration="$1"
    # shellcheck disable=SC2034  # output_dir available for future use
    local output_dir="$2"

    # Always include the initial prompt to ensure full context after summarization
    _get_user_prompt

    if [ "$iteration" -gt 0 ]; then
        # Add continuation context for subsequent iterations
        local prev_iter=$((iteration - 1))
        cat << CONTINUE_EOF

CONTINUATION CONTEXT (Iteration $iteration):

Your previous work is summarized in @../summaries/resolve-$prev_iter-summary.txt.

Please continue resolving conflicts:
1. Check which files still have unresolved conflicts using 'git diff --name-only --diff-filter=U'
2. Continue resolving remaining conflicts
3. Stage resolved files with 'git add'
4. When all conflicts are resolved, provide the final <summary> tag

Run 'git diff --name-only --diff-filter=U' to see remaining conflicts.
CONTINUE_EOF
    fi
}

# Completion check callback - returns 0 if all conflicts are resolved
_conflict_completion_check() {
    local workspace
    workspace=$(agent_get_workspace)

    # Check if any unresolved conflicts remain
    local unresolved
    unresolved=$(git -C "$workspace" diff --name-only --diff-filter=U 2>/dev/null)

    if [ -z "$unresolved" ]; then
        return 0  # All conflicts resolved
    fi

    return 1  # Still has conflicts
}

# System prompt
_get_system_prompt() {
    local workspace="$1"

    cat << EOF
GIT CONFLICT RESOLVER:

You resolve merge conflicts. Your job is to produce correct, working code - not to guess.

WORKSPACE: $workspace

## Resolution Philosophy

* UNDERSTAND BEFORE RESOLVING - Read surrounding code to understand intent
* PRESERVE FUNCTIONALITY - Don't lose features from either side
* VERIFY SYNTAX - Ensure resolved files are syntactically valid
* ONE FILE AT A TIME - Resolve completely, then stage, then move on

## Rules

* You MUST edit files to remove conflict markers and create correct merged content
* You MUST stage resolved files with 'git add <file>'
* You must NOT commit - only resolve and stage
* If unsure about intent, preserve BOTH sides rather than dropping code
EOF
}

# User prompt
_get_user_prompt() {
    cat << 'EOF'
CONFLICT RESOLUTION TASK:

Resolve all merge conflicts in this workspace.

## Process

1. **List conflicts**: `git diff --name-only --diff-filter=U`
2. **For each file**:
   - Read the file to see conflict markers (<<<<<<< / ======= / >>>>>>>)
   - Read surrounding context to understand what both sides intended
   - Determine the correct resolution
   - Edit file to remove markers and produce correct merged code
   - Verify file is syntactically valid
   - Stage with `git add <file>`
3. **Verify**: `git diff --name-only --diff-filter=U` should show no remaining conflicts

## Resolution Strategies

| Strategy | When to Use |
|----------|-------------|
| **Keep Both** | Both sides add different, non-overlapping content |
| **Accept Ours** | Our version is clearly correct or more complete |
| **Accept Theirs** | Their version is clearly correct or more complete |
| **Semantic Merge** | Both sides modify same logic - combine intelligently |

## Critical Rules

* Leave conflict markers in files when in doubt
* ALWAYS verify syntax after resolution (no broken code)
* If both sides add imports/dependencies, keep ALL of them
* DO NOT commit - only resolve and stage

## Output Format

<summary>

# Conflict Resolution Summary

## Resolved Files

| File | Strategy | Reason |
|------|----------|-------|
| path/file.ext | Keep Both | Combined imports from both branches |

## Stats
- Files resolved: N
- Remaining conflicts: M (list files with conflicts)

</summary>

<result>PASS</result>
OR
<result>FAIL</result>

The <result> tag MUST be exactly: PASS or FAIL.
EOF
}

# Extract resolution summary from log files
_extract_resolution_summary() {
    local worker_dir="$1"

    # Find the latest resolve log (excluding summary logs)
    local log_file
    log_file=$(find "$worker_dir/logs" -name "resolve-*.log" ! -name "*summary*" -printf '%T@ %p\n' 2>/dev/null | sort -rn | head -1 | cut -d' ' -f2-)

    local report_content=""

    if [ -n "$log_file" ] && [ -f "$log_file" ]; then
        # Extract summary content between <summary> tags
        local extracted
        extracted=$(_extract_tag_content_from_stream_json "$log_file" "summary") || true
        if [ -n "$extracted" ]; then
            report_content="$extracted"
        fi
    fi

    # If no summary tag found, create a basic summary
    if [ -z "$report_content" ]; then
        local workspace
        workspace=$(agent_get_workspace)
        local remaining
        remaining=$(git -C "$workspace" diff --name-only --diff-filter=U 2>/dev/null | wc -l)

        report_content="# Conflict Resolution Summary

**Status:** $([ "$remaining" -eq 0 ] && echo "Completed" || echo "Incomplete")

## Result

$(if [ "$remaining" -eq 0 ]; then
    echo "All merge conflicts have been resolved and staged."
else
    echo "**Warning:** $remaining file(s) still have unresolved conflicts."
    echo ""
    echo "Remaining conflicts:"
    git -C "$workspace" diff --name-only --diff-filter=U 2>/dev/null | sed 's/^/- /'
fi)

## Next Steps

$(if [ "$remaining" -eq 0 ]; then
    echo "- Review the staged changes with 'git diff --cached'"
    echo "- Commit the merge when ready"
else
    echo "- Manually resolve remaining conflicts"
    echo "- Stage resolved files with 'git add'"
fi)"
    fi

    agent_write_report "$worker_dir" "$report_content"
    log "Resolution summary saved"
}

# Check if workspace has unresolved conflicts (utility for callers)
# Returns: 0 if no conflicts, 1 if conflicts exist
check_conflicts_resolved() {
    local workspace="$1"

    local unresolved
    unresolved=$(git -C "$workspace" diff --name-only --diff-filter=U 2>/dev/null)

    [ -z "$unresolved" ]
}
