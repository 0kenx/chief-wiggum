#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: git-sync-main
# AGENT_DESCRIPTION: Git sync agent that fetches and merges the default branch into
#   the current branch. Pure bash, no LLM involved. Detects merge conflicts.
# REQUIRED_PATHS:
#   - workspace : Directory containing the git repository
# OUTPUT_FILES:
#   - sync-result.json : Contains PASS (clean merge) or FAIL (conflicts)
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "workflow.git-sync-main" "Git fetch and merge from origin default branch"

# Required paths before agent can run
agent_required_paths() {
    echo "workspace"
}

# Source dependencies
agent_source_core
source "$WIGGUM_HOME/lib/git/git-operations.sh"

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"

    local workspace="$worker_dir/workspace"

    if [ ! -d "$workspace" ]; then
        log_error "Workspace not found: $workspace"
        agent_write_result "$worker_dir" "FAIL" '{}' '["Workspace not found"]'
        return 1
    fi

    # Verify workspace is a git repository
    if [ ! -d "$workspace/.git" ] && ! git -C "$workspace" rev-parse --git-dir &>/dev/null; then
        log_error "Workspace is not a git repository: $workspace"
        agent_write_result "$worker_dir" "FAIL" '{}' '["Not a git repository"]'
        return 1
    fi

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Set up context
    agent_setup_context "$worker_dir" "$workspace" "$project_dir"

    local default_branch
    default_branch=$(get_default_branch)
    log "Syncing workspace with origin/$default_branch..."

    # Use shared advance function (fetch → ff → rebase → merge)
    local advance_exit=0
    git_advance_to_main "$workspace" || advance_exit=$?

    if [ $advance_exit -eq 0 ]; then
        log "Successfully synced with origin/$default_branch"
        agent_write_result "$worker_dir" "PASS" '{"merge_status":"synced","conflicts":0}'
        return 0
    fi

    # Advance failed — workspace left clean (merge aborted).
    # Could be a conflict or a fetch failure; either way the pipeline
    # should treat it as FAIL and let downstream steps handle it.
    log_error "Failed to sync with origin/$default_branch"
    agent_write_result "$worker_dir" "FAIL" '{"merge_status":"failed"}' '["Sync with origin/'"$default_branch"' failed"]'
    return 0  # FAIL is a valid gate result, not an error
}
