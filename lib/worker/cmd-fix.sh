#!/usr/bin/env bash
# lib/worker/cmd-fix.sh - Fix command logic for wiggum worker
#
# Provides: do_worker_fix()
# Sourced by: bin/wiggum-worker
#
# Merged from wiggum-start/do_start_fix() + wiggum-review/cmd_task_fix()
# - Base: wiggum-start version (git state mgmt, env var security, usage tracker)
# - Added: review-dir fallback from wiggum-review version

[ -n "${_CMD_FIX_LOADED:-}" ] && return 0
_CMD_FIX_LOADED=1

source "$WIGGUM_HOME/lib/core/exit-codes.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/tasks/task-parser.sh"
source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"
source "$WIGGUM_HOME/lib/worker/git-state.sh"
source "$WIGGUM_HOME/lib/git/pr-comments.sh"
source "$WIGGUM_HOME/lib/backend/claude/usage-tracker.sh"

source "$WIGGUM_HOME/lib/core/safe-path.sh"
# Output message respecting quiet mode
_msg() {
    [ "$QUIET_MODE" = "true" ] || echo "$@"
}

# Fix PR review comments for a task
#
# Uses outer-scope: PROJECT_DIR, RALPH_DIR, WIGGUM_HOME,
#                   QUIET_MODE, FOREGROUND_MODE, QUICK_MODE
#
# Args:
#   input_id - Task ID (partial or full)
do_worker_fix() {
    local input_id="$1"

    # Check .ralph directory exists
    if [ ! -d "$RALPH_DIR" ]; then
        echo "Error: No .ralph directory found. Run 'wiggum init' first."
        exit $EXIT_WORKER_NO_RALPH_DIR
    fi

    safe_path "$RALPH_DIR" "RALPH_DIR" || return 1
    mkdir -p "$RALPH_DIR/logs"

    if [ -z "$input_id" ]; then
        echo "Error: Task ID required"
        echo "Usage: wiggum worker fix <TASK-ID> [--quick]"
        exit $EXIT_USAGE
    fi

    # Check if kanban exists
    if [ ! -f "$RALPH_DIR/kanban.md" ]; then
        echo "Error: No kanban.md found at $RALPH_DIR/kanban.md"
        exit $EXIT_WORKER_NO_KANBAN
    fi

    # Resolve partial task ID to full task ID
    local task_id
    task_id=$(resolve_task_id "$RALPH_DIR/kanban.md" "$input_id") || exit $EXIT_WORKER_TASK_NOT_FOUND

    # Find existing worker directory for this task
    local worker_dir
    worker_dir=$(find_worker_by_task_id "$RALPH_DIR" "$task_id")

    if [ -z "$worker_dir" ] || [ ! -d "$worker_dir" ]; then
        # Fallback: try the review directory (from wiggum-review's cmd_task_fix)
        worker_dir="$RALPH_DIR/review"
        if [ ! -f "$worker_dir/task-comments.md" ]; then
            echo "Error: No worker or review directory found for $task_id"
            echo "Ensure a worker exists for this task or run sync first:"
            echo "  wiggum pr comments $task_id sync"
            exit $EXIT_ERROR
        fi
        log_debug "Using review directory: $worker_dir"
    fi

    # Validate workspace exists (skip for review-dir fallback)
    if [ "$worker_dir" != "$RALPH_DIR/review" ] && [ ! -d "$worker_dir/workspace" ]; then
        echo "Error: Workspace not found at $worker_dir/workspace"
        exit $EXIT_ERROR
    fi

    # Guard: check if agent is already running
    if [ -f "$worker_dir/agent.pid" ]; then
        local existing_pid
        existing_pid=$(cat "$worker_dir/agent.pid")
        if kill -0 "$existing_pid" 2>/dev/null; then
            echo "Agent already running for $(basename "$worker_dir") (PID: $existing_pid)"
            exit $EXIT_ERROR
        fi
        # Stale PID file - remove it
        rm -f "$worker_dir/agent.pid"
    fi

    # Auto-sync PR comments if task-comments.md missing
    if [ ! -f "$worker_dir/task-comments.md" ]; then
        _msg "Syncing PR comments for $task_id..."
        sync_pr_comments "$task_id" "$worker_dir" > /dev/null || true
    fi

    # Verify comments file exists after sync attempt
    if [ ! -f "$worker_dir/task-comments.md" ]; then
        echo "Error: No PR comments found for $task_id"
        echo "Ensure a PR exists and has review comments, then try:"
        echo "  wiggum pr comments $task_id sync"
        exit $EXIT_ERROR
    fi

    # Set git state: fixing
    git_state_set "$worker_dir" "fixing" "wiggum-worker.do_worker_fix" "Manual fix via 'wiggum worker fix $task_id'"

    # Determine which agent/pipeline to use
    # Default: full fix pipeline with test verification
    # --quick: standalone agent without tests (faster but risky)
    local agent_type="system.task-worker"
    local pipeline_name="fix"
    if [ "$QUICK_MODE" = "true" ]; then
        agent_type="engineering.pr-comment-fix"
        pipeline_name=""
        _msg "Starting quick fix for $task_id (no test verification)"
    else
        _msg "Starting fix pipeline for $task_id (with test verification)"
    fi

    # Recompute usage before starting
    usage_tracker_write_shared "$RALPH_DIR" > /dev/null 2>&1 || true

    if [ "$FOREGROUND_MODE" = "true" ]; then
        _msg "Running fix agent in foreground..."
        [ -n "$pipeline_name" ] && export WIGGUM_PIPELINE="$pipeline_name"
        source "$WIGGUM_HOME/lib/worker/agent-registry.sh"
        run_agent "$agent_type" "$worker_dir" "$PROJECT_DIR"
    else
        # Export variables for the setsid subprocess (security: no string interpolation)
        export _WORKER_WIGGUM_HOME="$WIGGUM_HOME"
        export _WORKER_DIR="$worker_dir"
        export _WORKER_AGENT_TYPE="$agent_type"
        export _WORKER_PROJECT_DIR="$PROJECT_DIR"
        export _WORKER_PIPELINE="$pipeline_name"
        export _WORKER_RALPH_DIR="$RALPH_DIR"
        export _WORKER_TASK_ID="$task_id"

        # shellcheck disable=SC2016
        setsid bash -c '
            set -euo pipefail
            _log_ts() { echo "[$(date -Iseconds)] $*"; }
            _log_ts "INFO: Fix agent subprocess starting for task $_WORKER_TASK_ID"

            export WIGGUM_HOME="$_WORKER_WIGGUM_HOME"
            [ -n "$_WORKER_PIPELINE" ] && export WIGGUM_PIPELINE="$_WORKER_PIPELINE"

            if ! source "$WIGGUM_HOME/lib/worker/agent-registry.sh" 2>&1; then
                _log_ts "ERROR: Failed to source agent-registry.sh"
                exit 1
            fi

            _log_ts "INFO: Running agent $_WORKER_AGENT_TYPE"
            _exit_code=0
            run_agent "$_WORKER_AGENT_TYPE" "$_WORKER_DIR" "$_WORKER_PROJECT_DIR" || _exit_code=$?
            if [ $_exit_code -ne 0 ]; then
                _log_ts "ERROR: run_agent failed with exit code $_exit_code"
                exit 1
            fi
            _log_ts "INFO: Fix agent completed successfully"
        ' >> "$RALPH_DIR/logs/fix-workers.log" 2>&1 &

        # Clean up exported worker variables from parent environment
        unset _WORKER_WIGGUM_HOME _WORKER_DIR _WORKER_AGENT_TYPE _WORKER_PROJECT_DIR \
              _WORKER_PIPELINE _WORKER_RALPH_DIR _WORKER_TASK_ID

        # Poll for agent.pid creation (10 × 0.1s)
        local wait_count=0
        while [ ! -f "$worker_dir/agent.pid" ] && [ $wait_count -lt 10 ]; do
            sleep 0.1
            ((++wait_count))
        done

        if [ -f "$worker_dir/agent.pid" ]; then
            local agent_pid
            agent_pid=$(cat "$worker_dir/agent.pid")
            _msg "Fix agent running (PID: $agent_pid)"
        else
            sleep 0.3
            if tail -5 "$RALPH_DIR/logs/fix-workers.log" 2>/dev/null | grep -q "ERROR:"; then
                echo "ERROR: Fix agent failed to start. Check .ralph/logs/fix-workers.log" >&2
            else
                _msg "Fix agent started (PID file pending)"
            fi
        fi
        _msg "Use 'wiggum monitor' to follow progress"
    fi
}
