#!/usr/bin/env bash
# violation-monitor.sh - Background monitor for workspace boundary violations
#
# Monitors iteration logs in real-time (100ms intervals) for violations:
# - Edit tool calls with file_path outside workspace directory
# - Bash commands that operate on git main repo
#
# On violation: immediately terminates agent and creates violation flag.
set -euo pipefail

source "$WIGGUM_HOME/lib/core/logger.sh"

# Global variable for violation monitor PID (needed for cleanup from signal handler)
VIOLATION_MONITOR_PID=""

# Check if a command is a destructive git command that sub-agents should not run
# These commands can destroy uncommitted work in the workspace
#
# Args:
#   command - The bash command to check
#
# Returns: 0 if destructive, 1 if safe
_is_destructive_git_command() {
    local command="$1"

    # Only check git commands
    if ! echo "$command" | grep -qE '\bgit\b'; then
        return 1  # Not a git command - safe
    fi

    # Safe git commands (read-only operations)
    # git status, git diff, git log, git show, git branch (without -d/-D)
    # git checkout <branch> (switching branches, no --)
    # git add, git commit (allowed for sub-agents that commit)
    if echo "$command" | grep -qE '\bgit\s+(status|diff|log|show|rev-parse|ls-files|describe|tag|remote|fetch)\b'; then
        return 1  # Safe read-only commands
    fi

    # Allow git branch without delete flags
    if echo "$command" | grep -qE '\bgit\s+branch\b' && ! echo "$command" | grep -qE '\bgit\s+branch\s+.*-[dD]'; then
        return 1  # Safe branch listing
    fi

    # Allow git add and git commit (sub-agents need to commit their work)
    if echo "$command" | grep -qE '\bgit\s+(add|commit)\b'; then
        return 1  # Safe - sub-agents can stage and commit their own work
    fi

    # DESTRUCTIVE: git checkout -- <file> (reverts file changes)
    # Note: "git checkout -- ." or "git checkout -- file.txt" destroys uncommitted changes
    if echo "$command" | grep -qE '\bgit\s+checkout\s+.*--'; then
        return 0  # Destructive - reverts file changes
    fi

    # DESTRUCTIVE: git checkout . (reverts all changes in current directory)
    if echo "$command" | grep -qE '\bgit\s+checkout\s+\.$'; then
        return 0  # Destructive - reverts all changes
    fi

    # DESTRUCTIVE: git stash (hides uncommitted changes)
    if echo "$command" | grep -qE '\bgit\s+stash\b'; then
        return 0  # Destructive - hides changes
    fi

    # DESTRUCTIVE: git reset --hard (destroys uncommitted changes)
    if echo "$command" | grep -qE '\bgit\s+reset\s+--hard'; then
        return 0  # Destructive - hard reset
    fi

    # DESTRUCTIVE: git reset HEAD~ or similar (can lose commits)
    if echo "$command" | grep -qE '\bgit\s+reset\s+(HEAD|[a-f0-9]+)'; then
        return 0  # Destructive - can lose commits
    fi

    # DESTRUCTIVE: git clean (deletes untracked files)
    if echo "$command" | grep -qE '\bgit\s+clean\b'; then
        return 0  # Destructive - deletes files
    fi

    # DESTRUCTIVE: git restore (reverts changes - modern replacement for checkout --)
    if echo "$command" | grep -qE '\bgit\s+restore\b'; then
        return 0  # Destructive - reverts changes
    fi

    # DESTRUCTIVE: git revert (creates revert commits - can be confusing in shared workspace)
    if echo "$command" | grep -qE '\bgit\s+revert\b'; then
        return 0  # Destructive - modifies history
    fi

    # Allow safe git checkout <branch> (switching branches without --)
    if echo "$command" | grep -qE '\bgit\s+checkout\s+[a-zA-Z0-9_/-]+$'; then
        return 1  # Safe branch switching
    fi

    # Default: allow other git commands
    return 1
}

# Start real-time violation monitor
#
# Args:
#   workspace       - The allowed workspace directory
#   worker_dir      - Worker directory (for logs and violation flag)
#   agent_pid       - PID of the agent to kill on violation
#   project_dir     - The main project directory (for detecting git commands there)
#
# Returns: The PID of the background monitor process (also sets VIOLATION_MONITOR_PID)
start_violation_monitor() {
    local workspace="$1"
    local worker_dir="$2"
    local agent_pid="$3"
    local project_dir="$4"

    local logs_dir="$worker_dir/logs"
    local monitor_log="$worker_dir/violation-monitor.log"

    (
        local last_size=0
        local current_log=""
        local iteration=0

        while kill -0 "$agent_pid" 2>/dev/null; do
            sleep 0.1

            # Find the current iteration log file (filenames are predictable)
            local new_log
            # shellcheck disable=SC2012
            new_log=$(ls -t "$logs_dir"/iteration-*.log 2>/dev/null | head -1)

            # If log file changed, reset position
            if [[ "$new_log" != "$current_log" ]]; then
                current_log="$new_log"
                last_size=0
                ((iteration++)) || true
            fi

            # Skip if no log file yet
            [[ -z "$current_log" ]] && continue
            [[ ! -f "$current_log" ]] && continue

            # Get current file size
            local current_size
            current_size=$(stat -c%s "$current_log" 2>/dev/null || echo 0)

            # Skip if no new content
            [[ "$current_size" -le "$last_size" ]] && continue

            # Read new content and check for violations
            local new_content
            new_content=$(tail -c +$((last_size + 1)) "$current_log" 2>/dev/null)
            last_size=$current_size

            # Parse each line of new content
            while IFS= read -r line; do
                [[ -z "$line" ]] && continue

                # Check for Edit tool violations
                if echo "$line" | grep -q '"name":"Edit"'; then
                    local file_path
                    file_path=$(echo "$line" | grep -oP '"file_path"\s*:\s*"\K[^"]+' 2>/dev/null || true)

                    if [[ -n "$file_path" ]]; then
                        # Allow: workspace paths and ../prd.md
                        if [[ "$file_path" != "$workspace"* ]] && \
                           [[ "$file_path" != "../prd.md" ]] && \
                           [[ "$file_path" != "$worker_dir/prd.md" ]]; then
                            # VIOLATION: Edit outside workspace
                            _log_violation "$monitor_log" "Edit" "$file_path" "$workspace"
                            _create_violation_flag "$worker_dir" "EDIT_OUTSIDE_WORKSPACE" "$file_path"
                            _terminate_agent "$agent_pid" "$worker_dir"
                            exit 1
                        fi
                    fi
                fi

                # Check for Write tool violations
                if echo "$line" | grep -q '"name":"Write"'; then
                    local file_path
                    file_path=$(echo "$line" | grep -oP '"file_path"\s*:\s*"\K[^"]+' 2>/dev/null || true)

                    if [[ -n "$file_path" ]]; then
                        if [[ "$file_path" != "$workspace"* ]] && \
                           [[ "$file_path" != "../prd.md" ]] && \
                           [[ "$file_path" != "$worker_dir/prd.md" ]]; then
                            # VIOLATION: Write outside workspace
                            _log_violation "$monitor_log" "Write" "$file_path" "$workspace"
                            _create_violation_flag "$worker_dir" "WRITE_OUTSIDE_WORKSPACE" "$file_path"
                            _terminate_agent "$agent_pid" "$worker_dir"
                            exit 1
                        fi
                    fi
                fi

                # Check for Bash commands that operate on main repo
                if echo "$line" | grep -q '"name":"Bash"'; then
                    local command
                    command=$(echo "$line" | grep -oP '"command"\s*:\s*"\K[^"]+' 2>/dev/null || true)

                    if [[ -n "$command" ]]; then
                        # Decode JSON escape sequences
                        command=$(echo -e "$command")

                        # Check for destructive git commands (for sub-agents only)
                        # Task-worker is exempt as it owns the workspace
                        if [[ "${WIGGUM_CURRENT_AGENT_TYPE:-}" != "task-worker" ]]; then
                            if _is_destructive_git_command "$command"; then
                                # VIOLATION: Destructive git command from sub-agent
                                _log_violation "$monitor_log" "Bash/DestructiveGit" "$command" "$workspace"
                                _create_violation_flag "$worker_dir" "DESTRUCTIVE_GIT_COMMAND" "$command"
                                _terminate_agent "$agent_pid" "$worker_dir"
                                exit 1
                            fi
                        fi

                        # Check for git commands in project_dir (not workspace)
                        if echo "$command" | grep -qE "cd\s+['\"]?$project_dir" || \
                           echo "$command" | grep -qE "git\s+(add|commit|push|checkout|branch|merge|rebase|reset)" | grep -v "$workspace"; then
                            # Check if command explicitly targets main repo
                            if [[ "$command" == *"$project_dir"* ]] && [[ "$command" != *"$workspace"* ]]; then
                                # VIOLATION: Git command on main repo
                                _log_violation "$monitor_log" "Bash/Git" "$command" "$workspace"
                                _create_violation_flag "$worker_dir" "GIT_COMMAND_ON_MAIN_REPO" "$command"
                                _terminate_agent "$agent_pid" "$worker_dir"
                                exit 1
                            fi
                        fi
                    fi
                fi

            done <<< "$new_content"
        done
    ) &

    VIOLATION_MONITOR_PID=$!
    log_debug "Violation monitor started with PID: $VIOLATION_MONITOR_PID (watching agent PID: $agent_pid)"
    echo "$VIOLATION_MONITOR_PID"
}

# Internal: Log a violation
_log_violation() {
    local log_file="$1"
    local tool="$2"
    local target="$3"
    local workspace="$4"
    local timestamp
    timestamp=$(date -Iseconds)

    {
        echo "[$timestamp] VIOLATION DETECTED"
        echo "Tool: $tool"
        echo "Target: $target"
        echo "Allowed workspace: $workspace"
        echo "---"
    } >> "$log_file" 2>/dev/null || true

    echo "[VIOLATION MONITOR] $tool violation detected: $target" >&2
}

# Internal: Create violation flag file
_create_violation_flag() {
    local worker_dir="$1"
    local violation_type="$2"
    local details="$3"
    local timestamp
    timestamp=$(date -Iseconds)

    {
        echo "VIOLATION_DETECTED"
        echo "$timestamp"
        echo "Type: $violation_type"
        echo "Details: $details"
    } > "$worker_dir/violation_flag.txt" 2>/dev/null || true
}

# Internal: Terminate the agent process
_terminate_agent() {
    local agent_pid="$1"
    local worker_dir="$2"

    echo "[VIOLATION MONITOR] Terminating agent (PID: $agent_pid) due to violation" >&2

    # Try graceful termination first
    kill -TERM "$agent_pid" 2>/dev/null || true
    sleep 0.5

    # Force kill if still running
    if kill -0 "$agent_pid" 2>/dev/null; then
        kill -9 "$agent_pid" 2>/dev/null || true
    fi
}

# Stop the violation monitor
#
# Args:
#   monitor_pid - The PID of the monitor to stop (optional, uses VIOLATION_MONITOR_PID if not provided)
stop_violation_monitor() {
    local monitor_pid="${1:-$VIOLATION_MONITOR_PID}"

    if [[ -n "$monitor_pid" ]] && kill -0 "$monitor_pid" 2>/dev/null; then
        kill "$monitor_pid" 2>/dev/null || true
        wait "$monitor_pid" 2>/dev/null || true
        log_debug "Violation monitor stopped (PID: $monitor_pid)"
    fi

    # Clear global if we stopped it
    if [[ "$monitor_pid" == "$VIOLATION_MONITOR_PID" ]]; then
        VIOLATION_MONITOR_PID=""
    fi
}

# Check if a violation has been detected
#
# Args:
#   worker_dir - Worker directory to check
#
# Returns: 0 if violation detected, 1 otherwise
has_violation() {
    local worker_dir="$1"
    [[ -f "$worker_dir/violation_flag.txt" ]]
}
