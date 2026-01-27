#!/usr/bin/env bash
# priority-workers.sh - Fix and resolve worker management
#
# Consolidates check_and_spawn_fixes() and check_and_spawn_resolvers() into
# a unified interface for spawning and managing priority workers (fix/resolve).
# These workers handle PR comment fixes and merge conflict resolution.
set -euo pipefail

[ -n "${_PRIORITY_WORKERS_LOADED:-}" ] && return 0
_PRIORITY_WORKERS_LOADED=1

# Source dependencies
source "$WIGGUM_HOME/lib/scheduler/worker-pool.sh"
source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"
source "$WIGGUM_HOME/lib/worker/git-state.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/scheduler/conflict-queue.sh"

# Check for tasks needing fixes and spawn fix workers
#
# Reads from .tasks-needing-fix.txt (populated by wiggum-review sync),
# checks git state for needs_fix status, and spawns fix workers up to limit.
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
#   limit       - Maximum total priority workers (fix + resolve combined)
#
# Requires:
#   - pool_* functions from worker-pool.sh
#   - git_state_* functions from git-state.sh
#   - WIGGUM_HOME environment variable
spawn_fix_workers() {
    local ralph_dir="$1"
    local project_dir="$2"
    local limit="$3"

    local tasks_needing_fix="$ralph_dir/.tasks-needing-fix.txt"

    if [ ! -s "$tasks_needing_fix" ]; then
        return 0
    fi

    # Check total priority worker capacity (fix + resolve share the limit)
    local fix_count resolve_count total_priority
    fix_count=$(pool_count "fix")
    resolve_count=$(pool_count "resolve")
    total_priority=$((fix_count + resolve_count))

    if [ "$total_priority" -ge "$limit" ]; then
        log "Fix worker limit reached ($total_priority/$limit) - deferring new fixes"
        return 0
    fi

    log "Checking for tasks needing PR comment fixes..."

    while read -r task_id; do
        [ -z "$task_id" ] && continue

        # Re-check capacity inside loop
        fix_count=$(pool_count "fix")
        resolve_count=$(pool_count "resolve")
        total_priority=$((fix_count + resolve_count))
        if [ "$total_priority" -ge "$limit" ]; then
            break
        fi

        local worker_dir
        worker_dir=$(find_worker_by_task_id "$ralph_dir" "$task_id" 2>/dev/null)

        if [ -z "$worker_dir" ] || [ ! -d "$worker_dir" ]; then
            continue
        fi

        # Check for needs_fix state
        if git_state_is "$worker_dir" "needs_fix"; then
            # Guard: skip if agent is already running for this worker
            if [ -f "$worker_dir/agent.pid" ]; then
                local existing_pid
                existing_pid=$(cat "$worker_dir/agent.pid")
                if kill -0 "$existing_pid" 2>/dev/null; then
                    log "Fix agent already running for $task_id (PID: $existing_pid) - skipping"
                    continue
                fi
            fi

            # Transition state to fixing
            git_state_set "$worker_dir" "fixing" "priority-workers.spawn_fix_workers" "Fix worker spawned"

            log "Spawning fix worker for $task_id..."

            # Call wiggum-review task fix synchronously (it returns immediately after async launch)
            (
                cd "$project_dir" || exit 1
                "$WIGGUM_HOME/bin/wiggum-review" task "$task_id" fix 2>&1 | \
                    sed "s/^/  [fix-$task_id] /"
            )

            # Read the agent PID from the worker directory
            if [ -f "$worker_dir/agent.pid" ]; then
                local agent_pid
                agent_pid=$(cat "$worker_dir/agent.pid")
                pool_add "$agent_pid" "fix" "$task_id"
                log "Fix worker spawned for $task_id (PID: $agent_pid)"
            else
                log "Warning: Fix agent for $task_id did not produce agent.pid"
            fi
        fi
    done < "$tasks_needing_fix"

    # Clear the tasks needing fix file after processing
    : > "$tasks_needing_fix"
}

# Check for workers needing conflict resolution and spawn resolver workers
#
# Scans worker directories for needs_resolve state and spawns resolver
# workers up to the combined priority worker limit.
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
#   limit       - Maximum total priority workers (fix + resolve combined)
#
# Requires:
#   - pool_* functions from worker-pool.sh
#   - git_state_* functions from git-state.sh
#   - WIGGUM_HOME environment variable
spawn_resolve_workers() {
    local ralph_dir="$1"
    local project_dir="$2"
    local limit="$3"

    [ -d "$ralph_dir/workers" ] || return 0

    # Check total priority worker capacity
    local fix_count resolve_count total_priority
    fix_count=$(pool_count "fix")
    resolve_count=$(pool_count "resolve")
    total_priority=$((fix_count + resolve_count))

    if [ "$total_priority" -ge "$limit" ]; then
        return 0
    fi

    for worker_dir in "$ralph_dir/workers"/worker-*; do
        [ -d "$worker_dir" ] || continue

        # Re-check capacity
        fix_count=$(pool_count "fix")
        resolve_count=$(pool_count "resolve")
        total_priority=$((fix_count + resolve_count))
        if [ "$total_priority" -ge "$limit" ]; then
            break
        fi

        # Check for needs_resolve state
        git_state_is "$worker_dir" "needs_resolve" || continue

        local worker_id
        worker_id=$(basename "$worker_dir")
        local task_id
        task_id=$(get_task_id_from_worker "$worker_id")

        # Guard: skip if agent is already running
        if [ -f "$worker_dir/agent.pid" ]; then
            local existing_pid
            existing_pid=$(cat "$worker_dir/agent.pid")
            if kill -0 "$existing_pid" 2>/dev/null; then
                log "Resolver already running for $task_id (PID: $existing_pid) - skipping"
                continue
            fi
        fi

        # Transition state
        git_state_set "$worker_dir" "resolving" "priority-workers.spawn_resolve_workers" "Resolver spawned"

        log "Spawning conflict resolver for $task_id..."

        # Call wiggum-review task resolve asynchronously
        (
            cd "$project_dir" || exit 1
            "$WIGGUM_HOME/bin/wiggum-review" task "$task_id" resolve 2>&1 | \
                sed "s/^/  [resolve-$task_id] /"
        ) &
        local resolver_pid=$!

        pool_add "$resolver_pid" "resolve" "$task_id"
        log "Resolver spawned for $task_id (PID: $resolver_pid)"
    done
}

# Create workspaces for orphaned PRs (PRs with comments but no local workspace)
# Then queue them for fix processing
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
#
# Requires:
#   - git_state_* functions
#   - setup_worktree_from_branch from worktree-helpers.sh
#   - WIGGUM_HOME environment variable
create_orphan_pr_workspaces() {
    local ralph_dir="$1"
    local project_dir="$2"

    local orphan_file="$ralph_dir/.prs-needing-workspace.jsonl"

    if [ ! -s "$orphan_file" ]; then
        return 0
    fi

    log "Processing orphaned PRs needing workspace creation..."

    local processed=()
    while IFS= read -r line; do
        [ -z "$line" ] && continue

        local task_id pr_number branch
        task_id=$(echo "$line" | jq -r '.task_id')
        pr_number=$(echo "$line" | jq -r '.pr_number')
        branch=$(echo "$line" | jq -r '.branch')

        if [ -z "$task_id" ] || [ "$task_id" = "null" ]; then
            continue
        fi

        # Check if workspace already exists now (might have been created elsewhere)
        local existing_worker
        existing_worker=$(find_worker_by_task_id "$ralph_dir" "$task_id" 2>/dev/null)
        if [ -n "$existing_worker" ] && [ -d "$existing_worker/workspace" ]; then
            log "  $task_id: workspace already exists, skipping"
            processed+=("$task_id")
            continue
        fi

        # Create worker directory
        local timestamp worker_id worker_dir
        timestamp=$(date +%s)
        worker_id="worker-${task_id}-fix-${timestamp}"
        worker_dir="$ralph_dir/workers/$worker_id"

        mkdir -p "$worker_dir"
        log "  $task_id: Creating workspace from branch $branch"

        # Create worktree from PR branch
        if ! setup_worktree_from_branch "$project_dir" "$worker_dir" "$branch"; then
            log_error "  $task_id: Failed to create workspace from branch $branch"
            rm -rf "$worker_dir"
            continue
        fi

        # Record branch and PR info
        echo "$branch" > "$worker_dir/branch.txt"
        git_state_set_pr "$worker_dir" "$pr_number"

        # Sync comments from review directory if they exist
        local review_comments="$ralph_dir/review/${task_id}-comments.json"
        if [ -f "$review_comments" ]; then
            cp "$review_comments" "$worker_dir/${task_id}-comments.json"
        fi

        # Also fetch fresh comments
        "$WIGGUM_HOME/bin/wiggum-review" task "$task_id" sync 2>/dev/null || true

        # Queue for fix processing
        echo "$task_id" >> "$ralph_dir/.tasks-needing-fix.txt"
        git_state_set "$worker_dir" "needs_fix" "priority-workers.create_orphan_pr_workspaces" "Workspace created from PR branch"

        log "  $task_id: Workspace created, queued for fix"
        processed+=("$task_id")
    done < "$orphan_file"

    # Remove processed entries from orphan file
    if [ ${#processed[@]} -gt 0 ]; then
        local temp_file
        temp_file=$(mktemp)
        while IFS= read -r line; do
            local task_id
            task_id=$(echo "$line" | jq -r '.task_id')
            local skip=false
            for p in "${processed[@]}"; do
                if [ "$task_id" = "$p" ]; then
                    skip=true
                    break
                fi
            done
            if [ "$skip" = false ]; then
                echo "$line" >> "$temp_file"
            fi
        done < "$orphan_file"
        mv "$temp_file" "$orphan_file"
    fi
}

# Handle fix worker completion - verify push and transition state for merge
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier
#
# Returns: 0 on success, 1 on failure
handle_fix_worker_completion() {
    local worker_dir="$1"
    local task_id="$2"

    # Read the most recent agent result to check push status
    local result_file
    result_file=$(find_newest "$worker_dir/results" -maxdepth 1 -name "*-result.json")
    if [ -z "$result_file" ] || [ ! -f "$result_file" ]; then
        log_warn "No result file for $task_id - cannot verify fix completion"
        return 1
    fi

    local gate_result push_succeeded
    gate_result=$(jq -r '.outputs.gate_result // "FAIL"' "$result_file" 2>/dev/null)
    push_succeeded=$(jq -r '.outputs.push_succeeded // false' "$result_file" 2>/dev/null)

    if [ "$gate_result" = "PASS" ] && [ "$push_succeeded" = "true" ]; then
        git_state_set "$worker_dir" "fix_completed" "priority-workers.handle_fix_worker_completion" "Push verified"
        git_state_set "$worker_dir" "needs_merge" "priority-workers.handle_fix_worker_completion" "Ready for merge attempt"
        log "Fix completed for $task_id - ready for merge"
        return 0
    elif [ "$gate_result" = "PASS" ]; then
        # Fix succeeded but push didn't - still mark as completed
        git_state_set "$worker_dir" "fix_completed" "priority-workers.handle_fix_worker_completion" "Fix passed but push failed"
        log_warn "Fix completed for $task_id but push failed"
        return 0
    else
        git_state_set "$worker_dir" "failed" "priority-workers.handle_fix_worker_completion" "Fix agent returned: $gate_result"
        log_error "Fix failed for $task_id (result: $gate_result)"
        return 1
    fi
}

# Handle resolver completion - check result and transition state
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier
#
# Returns: 0 on success, 1 on failure
handle_resolve_worker_completion() {
    local worker_dir="$1"
    local task_id="$2"

    # Check if conflicts are resolved
    local workspace="$worker_dir/workspace"
    if [ ! -d "$workspace" ]; then
        git_state_set "$worker_dir" "failed" "priority-workers.handle_resolve_worker_completion" "Workspace not found"
        return 1
    fi

    local remaining_conflicts
    remaining_conflicts=$(git -C "$workspace" diff --name-only --diff-filter=U 2>/dev/null || true)

    if [ -z "$remaining_conflicts" ]; then
        git_state_set "$worker_dir" "resolved" "priority-workers.handle_resolve_worker_completion" "All conflicts resolved"

        # Need to commit and push the resolution
        log "Conflicts resolved for $task_id - committing resolution..."

        local project_dir
        project_dir=$(cd "$workspace" && git rev-parse --show-toplevel 2>/dev/null || pwd)

        (
            cd "$project_dir" || exit 1
            "$WIGGUM_HOME/bin/wiggum-review" task "$task_id" commit 2>&1 | sed "s/^/  [commit-$task_id] /"
            "$WIGGUM_HOME/bin/wiggum-review" task "$task_id" push 2>&1 | sed "s/^/  [push-$task_id] /"
        )

        # Remove from conflict queue
        local ralph_dir
        ralph_dir=$(dirname "$(dirname "$worker_dir")")
        conflict_queue_remove "$ralph_dir" "$task_id"

        # Ready for another merge attempt
        git_state_set "$worker_dir" "needs_merge" "priority-workers.handle_resolve_worker_completion" "Ready for merge retry"
        return 0
    else
        local count
        count=$(echo "$remaining_conflicts" | wc -l)
        git_state_set "$worker_dir" "failed" "priority-workers.handle_resolve_worker_completion" "$count files still have conflicts"
        log_error "Resolver failed for $task_id - $count files still have conflicts"
        return 1
    fi
}

# Handle timeout for fix workers
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier
#   timeout    - Timeout value in seconds (for logging)
handle_fix_worker_timeout() {
    local worker_dir="$1"
    local task_id="$2"
    local timeout="${3:-1800}"

    log_warn "Fix worker for $task_id timed out after ${timeout}s"
    git_state_set "$worker_dir" "failed" "priority-workers" "Fix worker timed out after ${timeout}s"
}

# Handle timeout for resolve workers
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier
#   timeout    - Timeout value in seconds (for logging)
handle_resolve_worker_timeout() {
    local worker_dir="$1"
    local task_id="$2"
    local timeout="${3:-1800}"

    log_warn "Resolve worker for $task_id timed out after ${timeout}s"
    git_state_set "$worker_dir" "failed" "priority-workers" "Resolve worker timed out after ${timeout}s"
}
