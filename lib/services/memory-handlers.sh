#!/usr/bin/env bash
# =============================================================================
# memory-handlers.sh - Service handlers for the memory system
#
# Provides svc_* functions called by the service scheduler for:
#   - memory-load: Initialize memory directory structure on startup
#   - memory-extract: Dispatch pending workers for analysis (writes context)
#   - memory-analyze-complete: Post-analysis cleanup and index rebuild
#
# Service chain pattern:
#   memory-extract (function, interval 300s)
#     -> writes .ralph/memory/.current-analysis.json
#     -> on success triggers memory-analyze (pipeline, event-triggered)
#     -> on pipeline completion triggers memory-analyze-complete (function)
#
# Naming convention: svc_memory_* for memory-related handlers
# =============================================================================

# Prevent double-sourcing
[ -n "${_SERVICE_HANDLERS_MEMORY_LOADED:-}" ] && return 0
_SERVICE_HANDLERS_MEMORY_LOADED=1

source "$WIGGUM_HOME/lib/memory/memory.sh"

# Initialize memory directory structure on startup
#
# Creates directory tree and scaffold INDEX.md files if missing.
# Safe to call multiple times (idempotent).
svc_memory_load() {
    memory_init "$RALPH_DIR"
    log_debug "memory: Directory structure initialized"
}

# Dispatch pending workers for memory analysis
#
# Pops one worker from pending.list and writes context to
# .ralph/memory/.current-analysis.json for the downstream
# memory-analyze pipeline service. Returns 0 on success
# (triggering the downstream service) or 0 with no context file
# (downstream skips via condition).
#
# This function is the first half of a two-service chain:
#   memory-extract (function, interval) -> memory-analyze (pipeline, triggered)
svc_memory_extract() {
    local memory_dir="$RALPH_DIR/memory"
    local pending_list="$memory_dir/pending.list"
    local context_file="$memory_dir/.current-analysis.json"

    # Clean up stale context from previous runs
    rm -f "$context_file"

    # Skip if no pending work
    if [ ! -f "$pending_list" ] || [ ! -s "$pending_list" ]; then
        return 0
    fi

    local pending_count
    pending_count=$(wc -l < "$pending_list" 2>/dev/null | tr -d '[:space:]')
    pending_count="${pending_count:-0}"

    if [ "$pending_count" -eq 0 ]; then
        return 0
    fi

    log "memory: Dispatching pending analysis ($pending_count workers queued)"

    # Pop first entry atomically
    local worker_dir=""
    (
        flock -w 5 200 || return 1

        worker_dir=$(head -1 "$pending_list" 2>/dev/null || true)
        if [ -n "$worker_dir" ]; then
            local tmp
            tmp=$(tail -n +2 "$pending_list" 2>/dev/null || true)
            echo "$tmp" > "$pending_list"
        fi

        echo "$worker_dir" > "$pending_list.current"
    ) 200>"$pending_list.lock"

    worker_dir=$(cat "$pending_list.current" 2>/dev/null || true)
    rm -f "$pending_list.current"

    [ -n "$worker_dir" ] || return 0
    [ -d "$worker_dir" ] || return 0

    # Extract task ID
    local worker_id task_id
    worker_id=$(basename "$worker_dir")
    task_id=""
    if [[ "$worker_id" =~ ^worker-([A-Za-z]{2,10}-[0-9]{1,4})- ]]; then
        task_id="${BASH_REMATCH[1]}"
    fi

    if [ -z "$task_id" ]; then
        log_warn "memory: Could not extract task ID from $worker_id"
        return 0
    fi

    # Skip if already analyzed
    if memory_is_analyzed "$memory_dir" "$task_id"; then
        log_debug "memory: Task $task_id already analyzed, skipping"
        return 0
    fi

    # Write context file for downstream pipeline service
    local project_dir
    project_dir=$(realpath "$RALPH_DIR/.." 2>/dev/null || echo "")

    cat > "$context_file" << EOF
{
    "task_id": "$task_id",
    "worker_dir": "$worker_dir",
    "memory_dir": "$memory_dir",
    "project_dir": "$project_dir",
    "timestamp": $(date +%s)
}
EOF

    log "memory: Dispatched analysis context for $task_id"
    return 0
}

# Handle completion of memory-analyze pipeline service
#
# Called after the memory-analyze pipeline finishes. Rebuilds memory
# indexes if analysis succeeded, or re-queues the worker for retry.
svc_memory_analyze_complete() {
    local memory_dir="$RALPH_DIR/memory"
    local context_file="$memory_dir/.current-analysis.json"

    [ -f "$context_file" ] || return 0

    local task_id worker_dir
    task_id=$(jq -r '.task_id // ""' "$context_file" 2>/dev/null)
    worker_dir=$(jq -r '.worker_dir // ""' "$context_file" 2>/dev/null)

    # Clean up context file
    rm -f "$context_file"

    if [ -z "$task_id" ]; then
        log_warn "memory: No task_id in analysis context"
        return 0
    fi

    # Check if analysis produced output (agent marks task as analyzed)
    if memory_is_analyzed "$memory_dir" "$task_id"; then
        log "memory: Analysis complete for $task_id, rebuilding indexes"
        memory_rebuild_indexes "$memory_dir"
    else
        log_warn "memory: Analysis incomplete for $task_id"
        # Re-queue for retry if worker dir still exists
        if [ -n "$worker_dir" ] && [ -d "$worker_dir" ]; then
            memory_queue_worker "$worker_dir"
        fi
    fi
}
