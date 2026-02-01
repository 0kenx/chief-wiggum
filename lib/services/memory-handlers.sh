#!/usr/bin/env bash
# =============================================================================
# memory-handlers.sh - Service handlers for the memory system
#
# Provides svc_* functions called by the service scheduler for:
#   - memory-load: Initialize memory directory structure on startup
#   - memory-extract: Run LLM analysis on completed workers
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

# Run LLM analysis on completed workers to update project memory
#
# Processes one pending worker per invocation. The service scheduler
# calls this periodically (every 300s). Concurrency is limited to 1
# instance via services.json config.
svc_memory_extract() {
    local pending_list="$RALPH_DIR/memory/pending.list"

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

    log "memory: Processing pending analysis ($pending_count workers queued)"

    # Process one worker per cycle
    memory_process_pending "$RALPH_DIR" || true
}
