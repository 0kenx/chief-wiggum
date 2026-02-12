#!/usr/bin/env bash
# lib/worker/cmd-start.sh - Start command logic for wiggum worker
#
# Provides: do_start()
# Sourced by: bin/wiggum-worker

[ -n "${_CMD_START_LOADED:-}" ] && return 0
_CMD_START_LOADED=1

WIGGUM_HOME="${WIGGUM_HOME:-$HOME/.claude/chief-wiggum}"

source "$WIGGUM_HOME/lib/core/exit-codes.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"
source "$WIGGUM_HOME/lib/tasks/task-parser.sh"
source "$WIGGUM_HOME/lib/utils/audit-logger.sh"
source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"
source "$WIGGUM_HOME/lib/worker/agent-registry.sh"
source "$WIGGUM_HOME/lib/runtime/runtime.sh"
source "$WIGGUM_HOME/lib/backend/claude/usage-tracker.sh"
source "$WIGGUM_HOME/lib/github/issue-sync.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"
source "$WIGGUM_HOME/lib/core/safe-path.sh"

# Output message respecting quiet mode
_msg() {
    [ "$QUIET_MODE" = "true" ] || echo "$@"
}

# Start a new worker for a task
do_start() {
    local input_id="$1"
    local worker_dir=""
    local task_id=""

    # Check .ralph directory exists
    if [ ! -d "$RALPH_DIR" ]; then
        echo "Error: No .ralph directory found. Run 'wiggum init' first."
        exit $EXIT_WORKER_NO_RALPH_DIR
    fi

    safe_path "$RALPH_DIR" "RALPH_DIR" || return 1
    mkdir -p "$RALPH_DIR/logs"

    # Handle --worker-dir mode (run pipeline on existing worker)
    if [ -n "$WORKER_DIR" ]; then
        worker_dir="$WORKER_DIR"

        # Validate worker directory exists
        if [ ! -d "$worker_dir" ]; then
            echo "Error: Worker directory not found: $worker_dir"
            exit $EXIT_ERROR
        fi

        # Validate workspace exists
        if [ ! -d "$worker_dir/workspace" ]; then
            echo "Error: Workspace not found at $worker_dir/workspace"
            exit $EXIT_ERROR
        fi

        # Validate PRD exists
        if [ ! -f "$worker_dir/prd.md" ]; then
            echo "Error: PRD not found at $worker_dir/prd.md"
            exit $EXIT_ERROR
        fi

        # Extract task_id from worker directory name
        local worker_id
        worker_id=$(basename "$worker_dir")
        task_id=$(echo "$worker_id" | sed -E 's/worker-([A-Za-z]{2,10}-[0-9]{1,4})-.*/\1/')

        _msg "Starting pipeline on existing worker $worker_id (task: $task_id)"
    else
        # Normal mode: create new worker

        if [ -z "$input_id" ]; then
            echo "Error: Task ID required"
            echo "Usage: wiggum worker start <TASK-ID>"
            exit $EXIT_WORKER_MISSING_TASK_ID
        fi

        # Check if kanban exists
        if [ ! -f "$RALPH_DIR/kanban.md" ]; then
            echo "Error: No kanban.md found at $RALPH_DIR/kanban.md"
            exit $EXIT_WORKER_NO_KANBAN
        fi

        # Resolve partial task ID to full task ID
        task_id=$(resolve_task_id "$RALPH_DIR/kanban.md" "$input_id") || exit $EXIT_WORKER_TASK_NOT_FOUND

        # Check if a worker already exists for this task (using shared library)
        # Exclude plan workers (worker-TASK-xxx-plan-*) - those are read-only planning sessions
        local existing
        existing=$(find_any_worker_by_task_id "$RALPH_DIR" "$task_id" | grep -v -- '-plan-' || true)
        if [ -n "$existing" ]; then
            echo "Warning: Worker already exists for $task_id: $(basename "$existing")"
            echo "Use 'wiggum worker resume $task_id' to resume it, or 'wiggum clean $task_id' first."
            exit $EXIT_WORKER_ALREADY_EXISTS
        fi

        # Create worker directory with unique timestamp
        local timestamp
        timestamp=$(date +%s)
        local worker_id="worker-${task_id}-${timestamp}"
        worker_dir="$RALPH_DIR/workers/$worker_id"

        mkdir -p "$worker_dir"

        # Extract task from kanban and create worker PRD
        extract_task "$task_id" "$RALPH_DIR/kanban.md" > "$worker_dir/prd.md"

        # Emit worker.spawned event via lifecycle engine
        # This atomically: sets git state to needs_merge, kanban to "="
        source "$WIGGUM_HOME/lib/core/lifecycle-engine.sh"
        lifecycle_is_loaded || lifecycle_load
        if ! emit_event "$worker_dir" "worker.spawned" "cmd-start.do_start"; then
            # Fallback: lifecycle not loaded or event failed — use direct update
            # This preserves backward compatibility during transition
            log_warn "worker.spawned event failed, falling back to direct kanban update"
            update_kanban_status "$RALPH_DIR/kanban.md" "$task_id" "=" || true
            github_issue_sync_task_status "$RALPH_DIR" "$task_id" "=" || true
        fi

        _msg "Starting worker $worker_id for task $task_id"
    fi

    # Recompute usage before starting (ensures rate limit checks use fresh data)
    usage_tracker_write_shared "$RALPH_DIR" > /dev/null 2>&1 || true

    # Security: Pass variables via environment exports, not string interpolation.
    # This prevents command injection if any variable contains shell metacharacters.
    export _WORKER_WIGGUM_HOME="$WIGGUM_HOME"
    export _WORKER_DIR="$worker_dir"
    export _WORKER_AGENT_TYPE="$AGENT_TYPE"
    export _WORKER_PROJECT_DIR="$PROJECT_DIR"
    export _WORKER_MAX_ITERATIONS="$MAX_ITERATIONS"
    export _WORKER_MAX_TURNS="$MAX_TURNS"
    export _WORKER_PIPELINE="${WIGGUM_PIPELINE:-}"
    export _WORKER_RALPH_DIR="$RALPH_DIR"
    export _WORKER_TASK_ID="$task_id"

    if [ "$FOREGROUND_MODE" = "true" ]; then
        # Run in foreground (blocking) - used by orchestrator for proper PID tracking
        _msg "Running worker in foreground..."

        export WIGGUM_HOME="$_WORKER_WIGGUM_HOME"
        [ -n "$_WORKER_PIPELINE" ] && export WIGGUM_PIPELINE="$_WORKER_PIPELINE"

        source "$WIGGUM_HOME/lib/worker/agent-registry.sh"
        run_agent "$_WORKER_AGENT_TYPE" "$_WORKER_DIR" "$_WORKER_PROJECT_DIR" 30 "$_WORKER_MAX_ITERATIONS" "$_WORKER_MAX_TURNS"
    else
        # Launch agent in background (daemonize)
        # run_agent writes PID to agent.pid - orchestrator can poll for it
        # Use setsid to create a new session/process group for the worker
        # This prevents SIGINT from the orchestrator from killing workers

        # shellcheck disable=SC2016
        setsid bash -c '
            set -euo pipefail

            # Initialize logging early using proper logger infrastructure
            export WIGGUM_HOME="$_WORKER_WIGGUM_HOME"
            export LOG_FILE="$_WORKER_RALPH_DIR/logs/worker-bootstrap.log"
            source "$WIGGUM_HOME/lib/core/logger.sh"
            source "$WIGGUM_HOME/lib/utils/activity-log.sh"
            activity_init "$_WORKER_PROJECT_DIR"

            log "Worker bootstrap starting for task $_WORKER_TASK_ID"
            log_debug "worker_dir=$_WORKER_DIR"
            log_debug "agent_type=$_WORKER_AGENT_TYPE"
            log_debug "pipeline=${_WORKER_PIPELINE:-default}"
            log_debug "max_iterations=$_WORKER_MAX_ITERATIONS"
            log_debug "max_turns=$_WORKER_MAX_TURNS"

            activity_log "worker.bootstrap" "" "$_WORKER_TASK_ID" "agent=$_WORKER_AGENT_TYPE"

            [ -n "$_WORKER_PIPELINE" ] && export WIGGUM_PIPELINE="$_WORKER_PIPELINE"

            if ! source "$WIGGUM_HOME/lib/worker/agent-registry.sh" 2>&1; then
                log_error "Failed to source agent-registry.sh"
                exit 1
            fi

            log "Running agent $_WORKER_AGENT_TYPE"
            run_agent "$_WORKER_AGENT_TYPE" "$_WORKER_DIR" "$_WORKER_PROJECT_DIR" 30 "$_WORKER_MAX_ITERATIONS" "$_WORKER_MAX_TURNS"
            _exit_code=$?
            if [ $_exit_code -ne 0 ]; then
                log_error "run_agent failed with exit code $_exit_code"
                exit 1
            fi
            log "Worker bootstrap completed successfully"
        ' >> "$RALPH_DIR/logs/workers.log" 2>&1 &

        # Clean up exported worker variables from parent environment
        unset _WORKER_WIGGUM_HOME _WORKER_DIR _WORKER_AGENT_TYPE _WORKER_PROJECT_DIR \
              _WORKER_MAX_ITERATIONS _WORKER_MAX_TURNS _WORKER_PIPELINE _WORKER_RALPH_DIR \
              _WORKER_TASK_ID

        # Wait briefly for agent.pid to be created
        local wait_count=0
        while [ ! -f "$worker_dir/agent.pid" ] && [ $wait_count -lt 10 ]; do
            sleep 0.1
            ((++wait_count))
        done

        if [ -f "$worker_dir/agent.pid" ]; then
            local worker_pid
            worker_pid=$(cat "$worker_dir/agent.pid")
            _msg "Worker running (PID: $worker_pid)"
        else
            # Brief wait then check if agent failed
            sleep 0.3
            if tail -5 "$RALPH_DIR/logs/workers.log" 2>/dev/null | grep -q "ERROR:"; then
                echo "ERROR: Worker failed to start. Check .ralph/logs/workers.log" >&2
            else
                _msg "Worker started (PID file pending)"
            fi
        fi
        _msg "Use 'wiggum monitor' to follow progress"
    fi
}
