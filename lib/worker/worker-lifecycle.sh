#!/usr/bin/env bash
# worker-lifecycle.sh - Agent/worker discovery and PID management
#
# Provides functions for finding workers/agents, validating PIDs, and managing
# lifecycle. Used by wiggum-run, wiggum-start, wiggum-stop, etc.
#
# Note: All agents use agent.pid for their PID file. Process validation uses
# the "bash" pattern since agents run via run_agent() in subshells.
#
# shellcheck disable=SC2034  # Variables are exported for caller use (TERMINATE_*)
set -euo pipefail

source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"

# Global lock file for PID operations (prevents race conditions)
_PID_OPS_LOCK_FILE=""

# Get the PID operations lock file path for a ralph directory
# Args: <ralph_dir>
# Returns: lock file path
_get_pid_ops_lock() {
    local ralph_dir="$1"
    echo "$ralph_dir/.pid-ops.lock"
}

# Find the newest worker directory for a task
# Args: <ralph_dir> <task_id>
# Returns: worker directory path on stdout, or empty if not found
find_worker_by_task_id() {
    local ralph_dir="$1"
    local task_id="$2"

    find_newest "$ralph_dir/workers" -maxdepth 1 -type d -name "worker-$task_id-*"
}

# Find any worker directory matching a task ID (for checking if one exists)
# Args: <ralph_dir> <task_id>
# Returns: first matching worker directory path on stdout, or empty if not found
find_any_worker_by_task_id() {
    local ralph_dir="$1"
    local task_id="$2"

    find "$ralph_dir/workers" -maxdepth 1 -type d -name "worker-$task_id-*" 2>/dev/null | head -1
}

# Resolve a partial worker ID to full worker directory path
# Args: <ralph_dir> <partial_id>
# Returns: worker_dir path on stdout, or error message on stderr
# Exit: 0 on exact match, 1 on no match or multiple matches
resolve_worker_id() {
    local ralph_dir="$1"
    local partial="$2"
    local matches=()

    if [ ! -d "$ralph_dir/workers" ]; then
        echo "Error: No workers directory found at $ralph_dir/workers" >&2
        return 1
    fi

    for worker_dir in "$ralph_dir/workers"/worker-*; do
        [ -d "$worker_dir" ] || continue
        local worker_id
        worker_id=$(basename "$worker_dir")

        # Check if partial matches any part of worker_id
        if [[ "$worker_id" == *"$partial"* ]]; then
            matches+=("$worker_dir")
        fi
    done

    case ${#matches[@]} in
        0)
            echo "Error: No worker matches '$partial'" >&2
            echo "Use 'wiggum status' to see available workers." >&2
            return 1
            ;;
        1)
            echo "${matches[0]}"
            return 0
            ;;
        *)
            # If multiple match, try narrowing to only running workers
            local running_matches=()
            for m in "${matches[@]}"; do
                if is_worker_running "$m"; then
                    running_matches+=("$m")
                fi
            done

            if [[ ${#running_matches[@]} -eq 1 ]]; then
                echo "${running_matches[0]}"
                return 0
            fi

            echo "Error: Multiple workers match '$partial':" >&2
            for m in "${matches[@]}"; do
                local status="stopped"
                is_worker_running "$m" && status="running"
                echo "  - $(basename "$m") ($status)" >&2
            done
            echo "Please be more specific." >&2
            return 1
            ;;
    esac
}

# Validate that a PID file contains a valid, running worker process
# Args: <pid_file> [process_pattern]
# Returns: PID on stdout if valid, empty if invalid
# Exit: 0 if valid and running, 1 otherwise
get_valid_worker_pid() {
    local pid_file="$1"
    local process_pattern="${2:-wiggum}"

    if [ ! -f "$pid_file" ]; then
        return 1
    fi

    local pid
    pid=$(cat "$pid_file" 2>/dev/null)

    # Validate PID is a number
    if ! [[ "$pid" =~ ^[0-9]+$ ]]; then
        return 1
    fi

    # Check if process is running
    if ! kill -0 "$pid" 2>/dev/null; then
        return 1
    fi

    # Verify it's a wiggum-related process
    # Check process args for wiggum patterns or bash (for agent subshells)
    if [ -n "$process_pattern" ]; then
        local cmdline
        cmdline=$(ps -p "$pid" -o args= 2>/dev/null)
        # Accept wiggum commands, bash subshells, or explicit pattern
        if ! echo "$cmdline" | grep -qE "(wiggum|$process_pattern|/bin/bash|\.ralph/)"; then
            return 1
        fi
    fi

    echo "$pid"
    return 0
}

# Check if a worker is currently running
# Args: <worker_dir>
# Returns: 0 if running, 1 if not
is_worker_running() {
    local worker_dir="$1"
    local pid_file="$worker_dir/agent.pid"

    get_valid_worker_pid "$pid_file" "bash" > /dev/null 2>&1
}

# Get worker PID or return error
# Args: <worker_dir>
# Returns: PID on stdout, error message on stderr
# Exit: 0 if found and valid, 1 otherwise
get_worker_pid() {
    local worker_dir="$1"
    local pid_file="$worker_dir/agent.pid"

    if [ ! -f "$pid_file" ]; then
        echo "Error: No PID file found for agent (not running?)" >&2
        return 1
    fi

    local pid
    pid=$(cat "$pid_file" 2>/dev/null)

    # Validate PID is a number
    if ! [[ "$pid" =~ ^[0-9]+$ ]]; then
        echo "Error: Invalid PID in agent.pid file" >&2
        return 1
    fi

    # Check if process is running AND is a bash process (agent subshell)
    if kill -0 "$pid" 2>/dev/null; then
        if ps -p "$pid" -o args= 2>/dev/null | grep -q "bash"; then
            echo "$pid"
            return 0
        else
            echo "Error: PID $pid exists but is not an agent process (PID reused?)" >&2
            return 1
        fi
    else
        echo "Error: Agent process $pid is not running" >&2
        return 1
    fi
}

# Clean up stale PID file if process is no longer running
# Args: <pid_file> [process_pattern]
# Returns: 0 if cleaned or already clean, 1 if still running
cleanup_stale_pid() {
    local pid_file="$1"
    local process_pattern="${2:-}"

    if [ ! -f "$pid_file" ]; then
        return 0
    fi

    if get_valid_worker_pid "$pid_file" "$process_pattern" > /dev/null 2>&1; then
        # Process is still running
        return 1
    fi

    # Process not running, clean up
    rm -f "$pid_file"
    return 0
}

# Extract task ID from worker ID
# Args: <worker_id>
# Returns: task ID (e.g., TASK-001)
get_task_id_from_worker() {
    local worker_id="$1"
    echo "$worker_id" | sed -E 's/worker-([A-Za-z]{2,10}-[0-9]{1,4})-.*/\1/'
}

# Scan for active workers and return their info
# Args: <ralph_dir>
# Outputs lines of: <pid> <task_id> <worker_id>
# Uses file locking to prevent race conditions during PID cleanup
scan_active_workers() {
    local ralph_dir="$1"
    local lock_file

    [ -d "$ralph_dir/workers" ] || return 0

    lock_file=$(_get_pid_ops_lock "$ralph_dir")

    # Use flock for atomic PID operations
    (
        flock -w 10 200 || {
            log_warn "scan_active_workers: Failed to acquire lock after 10s"
            exit 2  # Distinguishable exit code for lock failure
        }

        for worker_dir in "$ralph_dir/workers"/worker-*; do
            [ -d "$worker_dir" ] || continue

            local pid_file="$worker_dir/agent.pid"
            [ -f "$pid_file" ] || continue

            local worker_id
            worker_id=$(basename "$worker_dir")
            local task_id
            task_id=$(get_task_id_from_worker "$worker_id")

            local pid
            pid=$(get_valid_worker_pid "$pid_file" "bash") || true
            if [ -n "$pid" ]; then
                echo "$pid $task_id $worker_id"
            else
                # Clean up stale PID file (atomic within lock)
                rm -f "$pid_file"
            fi
        done

    ) 200>"$lock_file"
}

# Atomically write a PID file
# Args: <pid_file> <pid>
# Uses file locking to prevent race conditions
# Security: Creates PID file with restricted permissions (owner read/write only)
write_pid_file() {
    local pid_file="$1"
    local pid="$2"
    local ralph_dir

    # Extract ralph_dir from pid_file path (workers are in .ralph/workers/)
    ralph_dir=$(dirname "$(dirname "$pid_file")")

    local lock_file
    lock_file=$(_get_pid_ops_lock "$ralph_dir")

    (
        flock -w 5 200 || {
            log_warn "write_pid_file: Failed to acquire lock"
            # Security: Use umask to restrict PID file permissions
            umask 077
            echo "$pid" > "$pid_file"
            exit 0
        }

        # Security: Use umask to restrict PID file permissions (owner only)
        umask 077
        echo "$pid" > "$pid_file"

    ) 200>"$lock_file"
}

# Atomically remove a PID file
# Args: <pid_file>
# Uses file locking to prevent race conditions
remove_pid_file() {
    local pid_file="$1"
    local ralph_dir

    # Extract ralph_dir from pid_file path
    ralph_dir=$(dirname "$(dirname "$pid_file")")

    local lock_file
    lock_file=$(_get_pid_ops_lock "$ralph_dir")

    (
        flock -w 5 200 || {
            log_warn "remove_pid_file: Failed to acquire lock"
            rm -f "$pid_file"
            exit 0
        }

        rm -f "$pid_file"

    ) 200>"$lock_file"
}

# Kill a process and all its descendants (children, grandchildren, etc.)
# Args: <pid> [signal]
# Signal can be: TERM, KILL, or a number (default: KILL/9)
# Kills children first (bottom-up) to avoid orphan processes
kill_process_tree() {
    local pid="$1"
    local signal="${2:-KILL}"

    # Validate PID
    if ! [[ "$pid" =~ ^[0-9]+$ ]]; then
        return 1
    fi

    # Don't kill ourselves or init
    if [ "$pid" -eq $$ ] || [ "$pid" -eq 1 ]; then
        return 1
    fi

    # Get all child PIDs
    local children
    children=$(pgrep -P "$pid" 2>/dev/null) || true

    # Recursively kill children first (depth-first)
    for child in $children; do
        kill_process_tree "$child" "$signal"
    done

    # Now kill the parent
    kill -"$signal" "$pid" 2>/dev/null || true
}

# Wait for worker PID file to be created
# Args: <worker_dir> [timeout_deciseconds]
# Returns: 0 if PID file created, 1 if timeout
wait_for_worker_pid() {
    local worker_dir="$1"
    local timeout="${2:-300}"  # Default 30 seconds (300 * 0.1s)

    local wait_count=0
    while [ ! -f "$worker_dir/agent.pid" ] && [ $wait_count -lt "$timeout" ]; do
        sleep 0.1
        ((wait_count++)) || true
    done

    [ -f "$worker_dir/agent.pid" ]
}

# List all worker directory names in ralph_dir
#
# Args:
#   ralph_dir - Ralph directory path
#
# Returns: worker directory names (one per line)
list_all_workers() {
    local ralph_dir="$1"

    [ -d "$ralph_dir/workers" ] || return 0

    for dir in "$ralph_dir/workers"/worker-*; do
        [ -d "$dir" ] && basename "$dir"
    done
}

# Find workers matching a pattern
#
# Args:
#   ralph_dir - Ralph directory path
#   pattern   - Pattern to match
#
# Returns: matching worker names (one per line)
find_workers_by_pattern() {
    local ralph_dir="$1"
    local pattern="$2"

    [ -d "$ralph_dir/workers" ] || return 0

    for dir in "$ralph_dir/workers"/worker-*; do
        [ -d "$dir" ] || continue
        local dirname
        dirname=$(basename "$dir")
        if [[ "$dirname" =~ $pattern ]]; then
            echo "$dirname"
        fi
    done
}

# Terminate a single worker with optional grace period
#
# Args:
#   worker_dir - Worker directory path
#   signal     - Signal to send (TERM for graceful, KILL for force)
#   timeout    - Seconds to wait for graceful shutdown (only for TERM)
#
# Returns: 0 on success, 1 on failure
# Sets: TERMINATE_WORKER_PID, TERMINATE_WORKER_ID for caller use
terminate_single_worker() {
    local worker_dir="$1"
    local signal="${2:-TERM}"
    local timeout="${3:-30}"

    TERMINATE_WORKER_ID=$(basename "$worker_dir")
    TERMINATE_WORKER_PID=""

    local pid
    pid=$(get_worker_pid "$worker_dir") || return 1
    TERMINATE_WORKER_PID="$pid"

    echo "Stopping worker $TERMINATE_WORKER_ID (PID: $pid)..."
    kill_process_tree "$pid" "$signal"

    if [ "$signal" = "KILL" ]; then
        sleep 1
    else
        # Wait for graceful shutdown
        local elapsed=0
        while kill -0 "$pid" 2>/dev/null && [ $elapsed -lt "$timeout" ]; do
            sleep 1
            ((elapsed++)) || true
        done
    fi

    if kill -0 "$pid" 2>/dev/null; then
        return 1
    fi

    rm -f "$worker_dir/agent.pid"
    return 0
}

# Terminate all workers with a given signal
#
# Args:
#   ralph_dir - Ralph directory path
#   signal    - Signal to send (TERM for graceful, KILL for force)
#   timeout   - Seconds to wait for graceful shutdown (only for TERM)
#
# Returns: 0 on success
# Sets: TERMINATE_ALL_COUNT (number of workers terminated)
#       TERMINATE_ALL_FAILED (number that failed to terminate)
terminate_all_workers() {
    local ralph_dir="$1"
    local signal="${2:-TERM}"
    local timeout="${3:-10}"

    TERMINATE_ALL_COUNT=0
    TERMINATE_ALL_FAILED=0

    if [ ! -d "$ralph_dir/workers" ]; then
        return 0
    fi

    # Collect active workers
    local -A worker_pids_map=()
    local scan_output
    scan_output=$(scan_active_workers "$ralph_dir") || {
        local scan_rc=$?
        if [ "$scan_rc" -eq 2 ]; then
            echo "Warning: Worker scan encountered lock contention" >&2
        fi
    }

    while read -r pid _task_id worker_id; do
        [ -n "$pid" ] || continue
        worker_pids_map[$pid]="$worker_id"
    done <<< "$scan_output"

    if [ "${#worker_pids_map[@]}" -eq 0 ]; then
        return 0
    fi

    # Get running PIDs
    local -a all_pids=()
    for pid in "${!worker_pids_map[@]}"; do
        if kill -0 "$pid" 2>/dev/null; then
            all_pids+=("$pid")
        fi
    done

    # Send signal to all workers
    for pid in "${all_pids[@]}"; do
        if kill -0 "$pid" 2>/dev/null; then
            echo "Stopping ${worker_pids_map[$pid]} (PID $pid)"
            kill_process_tree "$pid" "$signal"
        fi
    done

    # Wait for workers to stop
    if [ "$signal" != "KILL" ]; then
        local elapsed=0
        while [ $elapsed -lt "$timeout" ]; do
            local all_stopped=true
            for pid in "${all_pids[@]}"; do
                if kill -0 "$pid" 2>/dev/null; then
                    all_stopped=false
                    break
                fi
            done
            [ "$all_stopped" = true ] && break
            sleep 1
            ((elapsed++)) || true
        done
    else
        sleep 1
    fi

    # Count results and clean up PID files
    for pid in "${all_pids[@]}"; do
        local worker_id="${worker_pids_map[$pid]}"
        local worker_dir="$ralph_dir/workers/$worker_id"

        if ! kill -0 "$pid" 2>/dev/null; then
            ((++TERMINATE_ALL_COUNT)) || true
            [ -f "$worker_dir/agent.pid" ] && rm -f "$worker_dir/agent.pid"
        else
            ((++TERMINATE_ALL_FAILED)) || true
        fi
    done

    return 0
}

# Force kill remaining workers after graceful termination failed
#
# Args:
#   ralph_dir - Ralph directory path
#
# Returns: number of workers force-killed
force_kill_remaining_workers() {
    local ralph_dir="$1"
    local killed=0

    local scan_output
    scan_output=$(scan_active_workers "$ralph_dir" 2>/dev/null) || true

    while read -r pid _task_id worker_id; do
        [ -n "$pid" ] || continue
        if kill -0 "$pid" 2>/dev/null; then
            echo "Force killing $worker_id (PID $pid)"
            kill_process_tree "$pid" KILL
            ((++killed)) || true
        fi
    done <<< "$scan_output"

    sleep 1
    echo "$killed"
}
