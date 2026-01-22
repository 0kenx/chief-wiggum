#!/usr/bin/env bash
# worker-lifecycle.sh - Agent/worker discovery and PID management
#
# Provides functions for finding workers/agents, validating PIDs, and managing
# lifecycle. Used by wiggum-run, wiggum-start, wiggum-stop, etc.
#
# Note: All agents use agent.pid for their PID file. Process validation uses
# the "bash" pattern since agents run via run_agent() in subshells.
set -euo pipefail

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

    find "$ralph_dir/workers" -maxdepth 1 -type d -name "worker-$task_id-*" \
        -printf '%T@ %p\n' 2>/dev/null | sort -rn | head -1 | cut -d' ' -f2-
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
            echo "Error: Multiple workers match '$partial':" >&2
            for m in "${matches[@]}"; do
                echo "  - $(basename "$m")" >&2
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
    local process_pattern="${2:-bash}"

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

    # Verify it's the expected process type (bash for agent subshells)
    if [ -n "$process_pattern" ]; then
        if ! ps -p "$pid" -o args= 2>/dev/null | grep -q "$process_pattern"; then
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
    echo "$worker_id" | sed -E 's/worker-(TASK-[0-9]+)-.*/\1/'
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

    # Collect results in a variable to output after releasing lock
    local results=""

    # Use flock for atomic PID operations
    (
        flock -w 5 200 || {
            log_warn "scan_active_workers: Failed to acquire lock, proceeding without lock"
            exit 0
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
            pid=$(get_valid_worker_pid "$pid_file" "bash")
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
            echo "$pid" > "$pid_file"
            exit 0
        }

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

# Wait for worker PID file to be created
# Args: <worker_dir> [timeout_deciseconds]
# Returns: 0 if PID file created, 1 if timeout
wait_for_worker_pid() {
    local worker_dir="$1"
    local timeout="${2:-30}"  # Default 3 seconds (30 * 0.1s)

    local wait_count=0
    while [ ! -f "$worker_dir/agent.pid" ] && [ $wait_count -lt "$timeout" ]; do
        sleep 0.1
        ((wait_count++)) || true
    done

    [ -f "$worker_dir/agent.pid" ]
}
