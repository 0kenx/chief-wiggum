#!/usr/bin/env bash
# worker-pool.sh - Unified worker pool management
#
# Replaces separate active_workers, active_fix_workers, and active_resolve_workers
# arrays with a single unified pool abstraction. Supports three worker types:
#   - main:    Primary task workers
#   - fix:     PR comment fix workers
#   - resolve: Merge conflict resolution workers
#
# Worker entries are stored as: "type|task_id|start_time|last_checked"
#
# shellcheck disable=SC2034  # Variables are used externally (POOL_CLEANUP_*)
# shellcheck disable=SC2153  # RALPH_DIR is set by caller (documented requirement)
set -euo pipefail

[ -n "${_WORKER_POOL_LOADED:-}" ] && return 0
_WORKER_POOL_LOADED=1
source "$WIGGUM_HOME/lib/core/platform.sh"

# Pool storage - PID -> "type|task_id|start_time|last_checked"
declare -gA _WORKER_POOL=()

# Minimum seconds between kill -0 checks per worker
_POOL_PID_CHECK_INTERVAL="${WIGGUM_PID_CHECK_INTERVAL:-5}"

# Detect worker type from git-state, pipeline config, and directory name
#
# Checks sources in priority order:
#   1. git-state.json current_state (most current - reflects lifecycle transitions)
#   2. pipeline-config.json pipeline.name (for ambiguous states like "none", "failed")
#   3. Worker directory name pattern (-fix-, -resolve-)
#
# A fix/resolve worker that transitions to needs_merge/merging/merged is
# reclassified as "main" — it has exited the fix/resolve cycle and should
# not count toward priority worker limits.
#
# Args:
#   worker_dir - Full path to worker directory
#
# Returns: echoes "main", "fix", or "resolve"
_detect_worker_type() {
    local worker_dir="$1"

    # Source 1: git-state.json current_state (most current indicator)
    if [ -f "$worker_dir/git-state.json" ]; then
        local git_state
        git_state=$(jq -r '.current_state // ""' "$worker_dir/git-state.json" 2>/dev/null)
        case "$git_state" in
            fixing|needs_fix)
                echo "fix"
                return 0
                ;;
            resolving|needs_resolve|needs_multi_resolve)
                echo "resolve"
                return 0
                ;;
            needs_merge|merging|merged)
                echo "main"
                return 0
                ;;
        esac
    fi

    # Source 2: pipeline-config.json (for ambiguous states: none, failed, etc.)
    if [ -f "$worker_dir/pipeline-config.json" ]; then
        local pipeline_name
        pipeline_name=$(jq -r '.pipeline.name // ""' "$worker_dir/pipeline-config.json" 2>/dev/null)
        case "$pipeline_name" in
            fix)
                echo "fix"
                return 0
                ;;
            *resolve*)
                echo "resolve"
                return 0
                ;;
        esac
    fi

    # Source 3: directory name pattern
    local worker_name
    worker_name=$(basename "$worker_dir")
    if [[ "$worker_name" == *"-fix-"* ]]; then
        echo "fix"
        return 0
    elif [[ "$worker_name" == *"-resolve-"* ]]; then
        echo "resolve"
        return 0
    fi

    echo "main"
}

# Initialize the worker pool (clears any existing state)
pool_init() {
    _WORKER_POOL=()
}

# Add a worker to the pool
#
# Args:
#   pid     - Process ID
#   type    - Worker type (main|fix|resolve)
#   task_id - Task identifier
#
# Returns: 0 on success, 1 if PID already exists
pool_add() {
    local pid="$1"
    local type="$2"
    local task_id="$3"
    local start_time
    start_time=$(epoch_now)

    # Validate type
    case "$type" in
        main|fix|resolve) ;;
        *)
            echo "pool_add: invalid type '$type'" >&2
            return 1
            ;;
    esac

    # Check for duplicate
    if [ -n "${_WORKER_POOL[$pid]+x}" ]; then
        return 1
    fi

    _WORKER_POOL[$pid]="$type|$task_id|$start_time|0"

    # Persist to disk so subshell callers are visible to the main process
    if [ -n "${RALPH_DIR:-}" ]; then
        local pending_file="$RALPH_DIR/orchestrator/pool-pending"
        (
            flock -x 200
            echo "$pid|$type|$task_id|$start_time" >> "$pending_file"
        ) 200>"$pending_file.lock"
    fi

    return 0
}

# Ingest pending pool entries written to disk by subshells
#
# Reads $ralph_dir/orchestrator/pool-pending under flock, adds each entry to
# _WORKER_POOL (skipping duplicates), then truncates the file.
#
# Args:
#   ralph_dir - Ralph directory path
pool_ingest_pending() {
    local ralph_dir="$1"
    local pending_file="$ralph_dir/orchestrator/pool-pending"

    [ -s "$pending_file" ] || return 0

    local lines=""
    {
        flock -x 200
        lines=$(cat "$pending_file")
        : > "$pending_file"
    } 200>"$pending_file.lock"

    local line
    while IFS= read -r line; do
        [ -n "$line" ] || continue
        local pid type task_id start_time
        IFS='|' read -r pid type task_id start_time <<< "$line"
        # Skip if already in pool
        [ -z "${_WORKER_POOL[$pid]+x}" ] || continue
        _WORKER_POOL[$pid]="$type|$task_id|$start_time|0"
    done <<< "$lines"
}

# Persist cleanup event to disk for cross-subprocess communication
#
# In Python orchestrator mode, pre-phase and post-phase run in separate
# bash-bridge subprocesses. POOL_CLEANUP_EVENT set in pre-phase is lost
# before post-phase runs. This function persists the event to disk.
#
# Args:
#   ralph_dir - Ralph directory path
pool_persist_cleanup_event() {
    local ralph_dir="$1"
    local event_file="$ralph_dir/orchestrator/cleanup-event"
    touch "$event_file"
}

# Ingest cleanup event persisted to disk by a previous subprocess
#
# Reads and clears the cleanup-event file, setting POOL_CLEANUP_EVENT=true
# if it existed. Call at the start of post-phase to restore state from
# pre-phase in Python orchestrator mode.
#
# Args:
#   ralph_dir - Ralph directory path
pool_ingest_cleanup_event() {
    local ralph_dir="$1"
    local event_file="$ralph_dir/orchestrator/cleanup-event"

    if [ -f "$event_file" ]; then
        rm -f "$event_file"
        POOL_CLEANUP_EVENT=true
    fi
}

# Remove a worker from the pool
#
# Args:
#   pid - Process ID
#
# Returns: 0 on success, 1 if not found
pool_remove() {
    local pid="$1"

    if [ -z "${_WORKER_POOL[$pid]+x}" ]; then
        return 1
    fi

    unset "_WORKER_POOL[$pid]"
    return 0
}

# Get worker info from the pool
#
# Args:
#   pid - Process ID
#
# Returns: echoes "type|task_id|start_time" or empty if not found
# Exit: 0 if found, 1 if not found
pool_get() {
    local pid="$1"

    if [ -z "${_WORKER_POOL[$pid]+x}" ]; then
        return 1
    fi

    echo "${_WORKER_POOL[$pid]}"
    return 0
}

# Get worker type from the pool
#
# Args:
#   pid - Process ID
#
# Returns: echoes type (main|fix|resolve) or empty if not found
pool_get_type() {
    local pid="$1"
    local info

    if ! info=$(pool_get "$pid"); then
        return 1
    fi

    echo "${info%%|*}"
}

# Get task_id for a worker
#
# Args:
#   pid - Process ID
#
# Returns: echoes task_id or empty if not found
pool_get_task_id() {
    local pid="$1"
    local info

    if ! info=$(pool_get "$pid"); then
        return 1
    fi

    local rest="${info#*|}"
    echo "${rest%%|*}"
}

# Get start time for a worker
#
# Args:
#   pid - Process ID
#
# Returns: echoes start_time (epoch seconds) or empty if not found
pool_get_start_time() {
    local pid="$1"
    local info

    if ! info=$(pool_get "$pid"); then
        return 1
    fi

    # Format: type|task_id|start_time|last_checked — extract field 3
    local rest="${info#*|}"       # task_id|start_time|last_checked
    rest="${rest#*|}"             # start_time|last_checked
    echo "${rest%%|*}"
}

# Find worker PID by task_id
#
# Args:
#   task_id - Task identifier to search for
#
# Returns: echoes PID if found, empty otherwise
# Exit: 0 if found, 1 if not found
pool_find_by_task() {
    local search_task_id="$1"

    for pid in "${!_WORKER_POOL[@]}"; do
        local info="${_WORKER_POOL[$pid]}"
        local rest="${info#*|}"
        local task_id="${rest%%|*}"
        if [ "$task_id" = "$search_task_id" ]; then
            echo "$pid"
            return 0
        fi
    done

    return 1
}

# Count workers in the pool
#
# Args:
#   type - Optional: filter by type (main|fix|resolve). If omitted, counts all.
#
# Returns: echoes count
pool_count() {
    local filter_type="${1:-}"
    local count=0

    for pid in "${!_WORKER_POOL[@]}"; do
        if [ -z "$filter_type" ]; then
            ((++count))
        else
            local info="${_WORKER_POOL[$pid]}"
            local type="${info%%|*}"
            if [ "$type" = "$filter_type" ]; then
                ((++count))
            fi
        fi
    done

    echo "$count"
}

# Check if pool has capacity for a worker type
#
# Args:
#   type  - Worker type (main|fix|resolve)
#   limit - Maximum allowed for this type
#
# Returns: 0 if has capacity, 1 if at limit
pool_has_capacity() {
    local type="$1"
    local limit="$2"
    local current

    current=$(pool_count "$type")
    [ "$current" -lt "$limit" ]
}

# Iterate over workers with a callback
#
# Args:
#   type     - Worker type filter (main|fix|resolve) or "all"
#   callback - Function name to call with (pid, type, task_id, start_time)
#
# The callback receives:
#   $1 - pid
#   $2 - type
#   $3 - task_id
#   $4 - start_time
pool_foreach() {
    local filter_type="$1"
    local callback="$2"

    for pid in "${!_WORKER_POOL[@]}"; do
        local info="${_WORKER_POOL[$pid]}"
        local type="${info%%|*}"
        local rest="${info#*|}"
        local task_id="${rest%%|*}"
        rest="${rest#*|}"
        local start_time="${rest%%|*}"

        if [ "$filter_type" = "all" ] || [ "$filter_type" = "$type" ]; then
            "$callback" "$pid" "$type" "$task_id" "$start_time"
        fi
    done
}

# Get all PIDs in the pool
#
# Args:
#   type - Optional: filter by type (main|fix|resolve). If omitted, returns all.
#
# Returns: space-separated list of PIDs
pool_pids() {
    local filter_type="${1:-}"
    local pids=""

    for pid in "${!_WORKER_POOL[@]}"; do
        if [ -z "$filter_type" ]; then
            pids="${pids:+$pids }$pid"
        else
            local info="${_WORKER_POOL[$pid]}"
            local type="${info%%|*}"
            if [ "$type" = "$filter_type" ]; then
                pids="${pids:+$pids }$pid"
            fi
        fi
    done

    echo "$pids"
}

# Check if a task is already in the pool (any type)
#
# Args:
#   task_id - Task identifier to check
#
# Returns: 0 if found, 1 if not found
# Echoes: PID if found
pool_has_task() {
    local needle="$1"

    for pid in "${!_WORKER_POOL[@]}"; do
        local info="${_WORKER_POOL[$pid]}"
        local rest="${info#*|}"
        local task_id="${rest%%|*}"

        if [ "$task_id" = "$needle" ]; then
            echo "$pid"
            return 0
        fi
    done

    return 1
}

# Clean up finished workers and invoke callbacks
#
# Args:
#   type         - Worker type to check (main|fix|resolve) or "all"
#   timeout      - Timeout in seconds (0 = no timeout). Workers exceeding this are killed.
#   on_complete  - Callback function for completed workers: fn(worker_dir, task_id)
#   on_timeout   - Callback function for timed-out workers: fn(worker_dir, task_id)
#
# Requires: RALPH_DIR and find_worker_by_task_id to be available
#
# Returns:
#   Sets POOL_CLEANUP_COUNT to number of workers cleaned up
#   Sets POOL_CLEANUP_EVENT to "true" if any workers were cleaned up
pool_cleanup_finished() {
    local filter_type="$1"
    local timeout="${2:-0}"
    local on_complete="${3:-}"
    local on_timeout="${4:-}"
    local now
    now=$(epoch_tick)

    POOL_CLEANUP_COUNT=0
    POOL_CLEANUP_EVENT=false

    # Collect PIDs to process (avoid modifying array while iterating)
    local pids_to_check
    pids_to_check=$(pool_pids "$filter_type")

    for pid in $pids_to_check; do
        local info="${_WORKER_POOL[$pid]}"
        local type="${info%%|*}"
        local rest="${info#*|}"
        local task_id="${rest%%|*}"
        rest="${rest#*|}"
        local start_time="${rest%%|*}"
        local last_checked="${rest##*|}"
        last_checked="${last_checked:-0}"

        # Throttle kill -0 checks: skip if checked recently
        if (( now - last_checked < _POOL_PID_CHECK_INTERVAL )); then
            # Still check timeout without PID check (uses cached time)
            if [ "$timeout" -gt 0 ] && [ $((now - start_time)) -ge "$timeout" ]; then
                # Timed out — do a real check and kill
                POOL_CLEANUP_EVENT=true
                ((++POOL_CLEANUP_COUNT)) || true
                kill "$pid" 2>/dev/null || true
                if [ -n "$on_timeout" ]; then
                    local worker_dir
                    worker_dir=$(find_worker_by_task_id "$RALPH_DIR" "$task_id" 2>/dev/null || true)
                    if [ -n "$worker_dir" ]; then
                        "$on_timeout" "$worker_dir" "$task_id" || true
                    fi
                fi
                pool_remove "$pid"
            fi
            continue
        fi

        # Update last_checked timestamp
        _WORKER_POOL[$pid]="$type|$task_id|$start_time|$now"

        if ! kill -0 "$pid" 2>/dev/null; then
            # Worker finished
            POOL_CLEANUP_EVENT=true
            ((++POOL_CLEANUP_COUNT)) || true

            if [ -n "$on_complete" ]; then
                local worker_dir
                worker_dir=$(find_worker_by_task_id "$RALPH_DIR" "$task_id" 2>/dev/null || true)
                if [ -n "$worker_dir" ]; then
                    "$on_complete" "$worker_dir" "$task_id" || true
                fi
            fi

            pool_remove "$pid"

        elif [ "$timeout" -gt 0 ] && [ $((now - start_time)) -ge "$timeout" ]; then
            # Worker timed out
            POOL_CLEANUP_EVENT=true
            ((++POOL_CLEANUP_COUNT)) || true

            # Kill the timed-out worker
            kill "$pid" 2>/dev/null || true

            if [ -n "$on_timeout" ]; then
                local worker_dir
                worker_dir=$(find_worker_by_task_id "$RALPH_DIR" "$task_id" 2>/dev/null || true)
                if [ -n "$worker_dir" ]; then
                    "$on_timeout" "$worker_dir" "$task_id" || true
                fi
            fi

            pool_remove "$pid"
        fi
    done

    # Persist cleanup event to disk for Python mode cross-subprocess communication
    if [[ "${POOL_CLEANUP_EVENT:-false}" == "true" ]] && [[ -n "${RALPH_DIR:-}" ]]; then
        pool_persist_cleanup_event "$RALPH_DIR"
    fi
}

# Restore pool state from existing worker directories
#
# Scans worker directories for running agents and adds them to the pool.
# Used when orchestrator restarts to recover tracking state.
#
# Args:
#   ralph_dir - Ralph directory path
#
# Requires: scan_active_workers from worker-lifecycle.sh
pool_restore_from_workers() {
    local ralph_dir="$1"

    [ -d "$ralph_dir/workers" ] || return 0

    local scan_output
    scan_output=$(scan_active_workers "$ralph_dir") || {
        local scan_rc=$?
        if [ "$scan_rc" -eq 2 ]; then
            log_warn "pool_restore: Worker scan encountered lock contention"
        fi
    }

    while read -r worker_pid task_id _worker_id _pid_type; do
        [ -n "$worker_pid" ] || continue

        # Get worker creation time from directory
        local worker_dir="$ralph_dir/workers/$_worker_id"

        # Determine worker type from pipeline config, name pattern, and git-state
        local type
        type=$(_detect_worker_type "$worker_dir")
        local start_time
        if [ -d "$worker_dir" ]; then
            # Use directory mtime as approximate start time
            start_time=$(stat -c %Y "$worker_dir" 2>/dev/null || epoch_now)
        else
            start_time=$(epoch_now)
        fi

        # Add to pool (skip if already exists)
        _WORKER_POOL[$worker_pid]="$type|$task_id|$start_time|0" 2>/dev/null || true
    done <<< "$scan_output"
}

# Dump pool state for debugging
#
# Returns: echoes pool contents as JSON-like output
pool_dump() {
    echo "{"
    local first=true
    for pid in "${!_WORKER_POOL[@]}"; do
        local info="${_WORKER_POOL[$pid]}"
        local type="${info%%|*}"
        local rest="${info#*|}"
        local task_id="${rest%%|*}"
        rest="${rest#*|}"
        local start_time="${rest%%|*}"

        if [ "$first" = true ]; then
            first=false
        else
            echo ","
        fi
        echo "  \"$pid\": {\"type\": \"$type\", \"task_id\": \"$task_id\", \"start_time\": $start_time}"
    done
    echo "}"
}

# Save worker pool state to JSON file
#
# Writes _WORKER_POOL to pool.json for file-based state sharing.
#
# Args:
#   state_dir - Directory to write pool.json (e.g., $RALPH_DIR/orchestrator)
pool_save() {
    local state_dir="$1"
    local pool_file="$state_dir/pool.json"

    local json='{"workers":{'
    local first=true
    for pid in "${!_WORKER_POOL[@]}"; do
        local info="${_WORKER_POOL[$pid]}"
        local type="${info%%|*}"
        local rest="${info#*|}"
        local task_id="${rest%%|*}"
        rest="${rest#*|}"
        local start_time="${rest%%|*}"

        if [ "$first" = true ]; then
            first=false
        else
            json+=","
        fi
        json+="\"$pid\":{\"type\":\"$type\",\"task_id\":\"$task_id\",\"start_time\":$start_time}"
    done
    json+='}}'

    echo "$json" > "$pool_file"
}

# Load worker pool state from JSON file
#
# Reads pool.json into _WORKER_POOL, merging with any existing entries.
# Existing entries take precedence (in-memory is more current).
#
# Args:
#   state_dir - Directory containing pool.json
#
# Returns: 0 on success, 1 if file not found
pool_load() {
    local state_dir="$1"
    local pool_file="$state_dir/pool.json"

    [ -f "$pool_file" ] || return 1

    local entries
    entries=$(jq -r '.workers | to_entries[] | "\(.key)|\(.value.type)|\(.value.task_id)|\(.value.start_time)"' "$pool_file" 2>/dev/null) || return 1

    while IFS='|' read -r pid type task_id start_time; do
        [ -n "$pid" ] || continue
        # Don't overwrite existing in-memory entries
        [ -z "${_WORKER_POOL[$pid]+x}" ] || continue
        _WORKER_POOL[$pid]="$type|$task_id|$start_time|0"
    done <<< "$entries"

    return 0
}
