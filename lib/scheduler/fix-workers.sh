#!/usr/bin/env bash
# fix-workers.sh - Fix worker spawning and lifecycle management
#
# Handles PR comment fix workers: spawning, completion, and timeout handling.
# Extracted from priority-workers.sh to reduce module size.
#
# State transitions are driven by the lifecycle engine (emit_event).
# See config/worker-lifecycle.json for the spec.
set -euo pipefail

[ -n "${_FIX_WORKERS_LOADED:-}" ] && return 0
_FIX_WORKERS_LOADED=1

# Source shared priority worker functions
source "$WIGGUM_HOME/lib/scheduler/priority-workers.sh"
source "$WIGGUM_HOME/lib/core/lifecycle-engine.sh"

# Check for tasks needing fixes and spawn fix workers
#
# Collects tasks from two sources:
# 1. orchestrator/tasks-needing-fix.txt (populated by wiggum pr sync for fresh comments)
# 2. Worker directories with needs_fix git state (fallback for stuck tasks)
#
# Tasks are sorted by dependency depth (descending) so that tasks which
# unblock the most downstream work are fixed first.
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
#   limit       - Maximum total priority workers (fix + resolve combined)
#
# Requires:
#   - pool_* functions from worker-pool.sh
#   - git_state_* functions from git-state.sh
#   - get_dependency_depth from task-parser.sh
#   - WIGGUM_HOME environment variable
spawn_fix_workers() {
    local ralph_dir="$1"
    local project_dir="$2"
    local limit="$3"

    local tasks_needing_fix="$ralph_dir/orchestrator/tasks-needing-fix.txt"
    local kanban_file="$ralph_dir/kanban.md"

    [ -d "$ralph_dir/workers" ] || return 0

    # Ensure lifecycle spec is loaded
    lifecycle_is_loaded || lifecycle_load

    # Sync file-based capacity tracking with actual pool state
    # This handles cases where workers exited unexpectedly
    _priority_capacity_sync "$ralph_dir"

    # Collect tasks from both sources into a deduplicated list
    # Use associative array for deduplication
    local -A task_set=()

    # Source 1: tasks-needing-fix.txt (fresh comments from sync)
    if [ -s "$tasks_needing_fix" ]; then
        while read -r task_id; do
            [ -n "$task_id" ] && task_set["$task_id"]=1
        done < "$tasks_needing_fix"
    fi

    # Source 2: scan workers for needs_fix state (fallback for stuck tasks)
    for worker_dir in "$ralph_dir/workers"/worker-*; do
        [ -d "$worker_dir" ] || continue
        git_state_is "$worker_dir" "needs_fix" || continue

        local worker_id task_id
        worker_id=$(basename "$worker_dir")
        task_id=$(get_task_id_from_worker "$worker_id")

        if [ -n "$task_id" ] && [ -z "${task_set[$task_id]:-}" ]; then
            task_set["$task_id"]=1
            log_debug "Found stuck needs_fix task: $task_id"
        fi
    done

    # Exit early if no tasks
    if [ ${#task_set[@]} -eq 0 ]; then
        return 0
    fi

    log "Checking for tasks needing PR comment fixes..."

    # Sort tasks by dependency depth (descending) - tasks that unblock more work go first
    local -a sorted_tasks=()
    local -a task_scores=()
    for task_id in "${!task_set[@]}"; do
        local dep_depth=0
        if [ -f "$kanban_file" ]; then
            dep_depth=$(get_dependency_depth "$kanban_file" "$task_id" 2>/dev/null || echo "0")
        fi
        task_scores+=("$dep_depth|$task_id")
    done

    # Sort by depth descending (higher depth first = unblocks more tasks)
    while IFS= read -r entry; do
        [ -n "$entry" ] || continue
        sorted_tasks+=("${entry#*|}")
    done < <(printf '%s\n' "${task_scores[@]}" | sort -t'|' -k1 -rn)

    for task_id in "${sorted_tasks[@]}"; do
        [ -z "$task_id" ] && continue

        local worker_dir
        worker_dir=$(find_worker_by_task_id "$ralph_dir" "$task_id" 2>/dev/null)

        if [ -z "$worker_dir" ] || [ ! -d "$worker_dir" ]; then
            continue
        fi

        # Verify needs_fix state (may have changed since collection)
        if ! git_state_is "$worker_dir" "needs_fix"; then
            continue
        fi

        # Skip tasks with terminal kanban status — don't fix a task that's
        # already complete, failed, or not planned
        if [ -f "$kanban_file" ]; then
            local _task_status
            _task_status=$(get_task_status "$kanban_file" "$task_id" 2>/dev/null) || true
            case "${_task_status:-}" in
                x|"*"|N)
                    log "Skipping fix for $task_id (kanban status [$_task_status])"
                    continue
                    ;;
            esac
        fi

        # Guard: skip if agent is already running for this worker
        if [ -f "$worker_dir/agent.pid" ]; then
            local existing_pid
            existing_pid=$(cat "$worker_dir/agent.pid")
            if kill -0 "$existing_pid" 2>/dev/null; then
                log "Fix agent already running for $task_id (PID: $existing_pid) - skipping"
                continue
            fi
        fi

        # Atomically reserve capacity slot (prevents race with resolve-workers)
        if ! _priority_capacity_reserve "$ralph_dir" "$limit"; then
            log "Fix worker limit reached ($limit) - deferring remaining fixes"
            break
        fi

        # Ensure workspace exists (reconstruct from PR branch if missing)
        if ! ensure_workspace_from_pr "$worker_dir" "$project_dir" "$task_id"; then
            # Reconstruction failed - check if PR is already merged (branch deleted)
            local merge_status
            merge_status=$(_verify_task_merged "$ralph_dir" "$task_id" "$worker_dir")

            if [ "$merge_status" = "merged" ]; then
                log "Fix worker not needed for $task_id - PR is already merged (workspace cleaned up)"
                emit_event "$worker_dir" "fix.already_merged" "fix-workers.spawn_fix_workers"
            else
                log_error "Cannot spawn fix worker for $task_id: workspace missing and reconstruction failed (PR status: $merge_status)"
            fi
            _priority_capacity_release "$ralph_dir"
            continue
        fi

        # Transition state to fixing
        emit_event "$worker_dir" "fix.started" "fix-workers.spawn_fix_workers"

        log "Spawning fix worker for $task_id..."

        # Call wiggum worker fix synchronously (it returns immediately after async launch)
        (
            cd "$project_dir" || exit 1
            "$WIGGUM_HOME/bin/wiggum-worker" fix "$task_id" 2>&1 | \
                sed "s/^/  [fix-$task_id] /"
        )

        # Wait briefly for agent.pid to appear (async launch race condition)
        local wait_count=0
        while [ ! -f "$worker_dir/agent.pid" ] && [ $wait_count -lt 20 ]; do
            sleep 0.1
            ((++wait_count)) || true
        done

        # Read the agent PID from the worker directory
        if [ -f "$worker_dir/agent.pid" ]; then
            local agent_pid
            agent_pid=$(cat "$worker_dir/agent.pid")
            pool_add "$agent_pid" "fix" "$task_id"
            log "Fix worker spawned for $task_id (PID: $agent_pid)"
        else
            log_warn "Fix agent for $task_id did not produce agent.pid after 2s wait"
            # Revert state so it can be retried
            emit_event "$worker_dir" "fix.timeout" "fix-workers.spawn_fix_workers"
            _priority_capacity_release "$ralph_dir"
        fi
    done

    # Clear the tasks needing fix file after processing
    : > "$tasks_needing_fix"
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

    # Ensure lifecycle spec is loaded
    lifecycle_is_loaded || lifecycle_load

    # Find the fix agent result. Try specific pipeline step results first,
    # then fall back to generic search for backward compatibility.
    local result_file=""

    # 1. Try pr-fix result (has gate_result + push_succeeded)
    result_file=$(find_newest "$worker_dir/results" -maxdepth 1 -name "*-pr-fix-result.json")

    # 2. Fall back to generic search: newest result with gate_result field
    if [ -z "$result_file" ]; then
        local candidate
        while read -r candidate; do
            [ -f "$candidate" ] || continue
            if jq -e '.outputs.gate_result // .gate_result' "$candidate" &>/dev/null; then
                result_file="$candidate"
                break
            fi
        done < <(find "$worker_dir/results" -maxdepth 1 -name "*-result.json" -type f 2>/dev/null | sort -r)
    fi

    if [ -z "$result_file" ]; then
        log_warn "No fix agent result for $task_id - fix agent may not have run"
        emit_event "$worker_dir" "fix.timeout" "fix-workers.handle_fix_worker_completion"
        return 1
    fi

    local gate_result push_succeeded
    gate_result=$(jq -r '.outputs.gate_result // .gate_result // "FAIL"' "$result_file" 2>/dev/null)
    push_succeeded=$(jq -r '.outputs.push_succeeded // "false"' "$result_file" 2>/dev/null)

    # If pr-fix didn't report push success, check commit-push result for push_status
    if [ "$push_succeeded" != "true" ]; then
        local commit_push_result
        commit_push_result=$(find_newest "$worker_dir/results" -maxdepth 1 -name "*-commit-push-result.json")
        if [ -n "$commit_push_result" ] && [ -f "$commit_push_result" ]; then
            local push_status
            push_status=$(jq -r '.outputs.push_status // .push_status // ""' "$commit_push_result" 2>/dev/null)
            if [ "$push_status" = "success" ]; then
                push_succeeded="true"
            fi
        fi
    fi

    if [ "$gate_result" = "PASS" ] && [ "$push_succeeded" = "true" ]; then
        emit_event "$worker_dir" "fix.pass" "fix-workers.handle_fix_worker_completion"
        log "Fix completed for $task_id - ready for merge"
        return 0
    elif [ "$gate_result" = "PASS" ]; then
        # Fix succeeded but push status unclear - proceed to merge anyway.
        # attempt_pr_merge handles failures gracefully with proper state transitions.
        emit_event "$worker_dir" "fix.pass" "fix-workers.handle_fix_worker_completion"
        log_warn "Fix completed for $task_id - push status unclear, proceeding to merge"
        return 0
    elif [ "$gate_result" = "SKIP" ]; then
        # No comments to fix - transition to merge
        emit_event "$worker_dir" "fix.skip" "fix-workers.handle_fix_worker_completion"
        log "Fix skipped for $task_id (no comments) - ready for merge"
        return 0
    elif [ "$gate_result" = "FIX" ]; then
        # Partial fix - some comments addressed but not all
        emit_event "$worker_dir" "fix.partial" "fix-workers.handle_fix_worker_completion"
        log_warn "Partial fix for $task_id - will retry"
        return 1
    else
        emit_event "$worker_dir" "fix.fail" "fix-workers.handle_fix_worker_completion"
        log_error "Fix failed for $task_id (result: $gate_result)"
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
    local timeout="${3:-3600}"

    # Ensure lifecycle spec is loaded
    lifecycle_is_loaded || lifecycle_load

    # Don't clobber terminal/completed states - the fix may have finished
    # before the timeout fired
    local current_state
    current_state=$(git_state_get "$worker_dir")
    case "$current_state" in
        fix_completed|needs_merge|merged|resolved)
            log "Fix worker for $task_id timed out but state is already $current_state - treating as completed"
            return 0
            ;;
    esac

    log_warn "Fix worker for $task_id timed out after ${timeout}s - resetting to needs_fix for retry"
    emit_event "$worker_dir" "fix.timeout" "fix-workers.handle_fix_worker_timeout"
}
