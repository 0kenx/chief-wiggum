#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: git-sync-main
# AGENT_DESCRIPTION: Git sync agent that fetches and merges origin/main into
#   the current branch. Pure bash, no LLM involved. Detects merge conflicts.
# REQUIRED_PATHS:
#   - workspace : Directory containing the git repository
# OUTPUT_FILES:
#   - sync-result.json : Contains PASS (clean merge) or FAIL (conflicts)
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "workflow.git-sync-main" "Git fetch and merge from origin/main"

# Required paths before agent can run
agent_required_paths() {
    echo "workspace"
}

# Source dependencies
agent_source_core

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

    log "Fetching origin/main..."

    # Fetch origin/main
    local fetch_output
    if ! fetch_output=$(git -C "$workspace" fetch origin main 2>&1); then
        log_error "Failed to fetch origin/main: $fetch_output"
        agent_write_result "$worker_dir" "FAIL" '{}' '["Fetch failed: '"${fetch_output:0:200}"'"]'
        return 1
    fi

    log "Merging origin/main into current branch..."

    # Attempt to merge origin/main
    local merge_output merge_exit=0
    merge_output=$(git -C "$workspace" merge origin/main --no-edit 2>&1) || merge_exit=$?

    if [ $merge_exit -eq 0 ]; then
        # Clean merge - check if we're up to date or actually merged
        if echo "$merge_output" | grep -q "Already up to date"; then
            log "Already up to date with origin/main"
            agent_write_result "$worker_dir" "PASS" '{"merge_status":"up_to_date","conflicts":0}'
        else
            log "Successfully merged origin/main"
            agent_write_result "$worker_dir" "PASS" '{"merge_status":"merged","conflicts":0}'
        fi
        return 0
    fi

    # Check if merge failed due to conflicts
    local conflicted_files
    conflicted_files=$(git -C "$workspace" diff --name-only --diff-filter=U 2>/dev/null || true)

    if [ -n "$conflicted_files" ]; then
        local conflict_count
        conflict_count=$(echo "$conflicted_files" | wc -l)
        log "Merge conflict detected: $conflict_count file(s)"

        # Build list of conflicted files for output
        local files_json
        files_json=$(echo "$conflicted_files" | jq -R -s 'split("\n") | map(select(length > 0))')

        agent_write_result "$worker_dir" "FAIL" \
            "{\"merge_status\":\"conflict\",\"conflicts\":$conflict_count,\"conflicted_files\":$files_json}"
        return 0  # Return 0 because FAIL is a valid gate result, not an error
    fi

    # Some other merge failure
    log_error "Merge failed: $merge_output"
    agent_write_result "$worker_dir" "FAIL" '{}' '["Merge failed: '"${merge_output:0:200}"'"]'
    return 1
}
