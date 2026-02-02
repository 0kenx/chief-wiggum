#!/usr/bin/env bash
# =============================================================================
# service-runner.sh - Execute services based on type
#
# Handles the actual execution of services based on their execution type:
# - command: Shell commands
# - function: Bash functions
# - pipeline: Pipeline definitions
# - agent: Agent execution (runs agents directly)
#
# Provides:
#   service_runner_init(ralph_dir, project_dir) - Initialize runner
#   service_run(id, args...)                    - Execute a service
#   service_run_command(cmd, timeout)           - Run shell command
#   service_run_function(func, args...)         - Call bash function
#   service_handle_result(id, exit_code)        - Process result
#
# New in v1.1:
#   - Resource limits support (memory, CPU/nice)
#   - Execution metrics tracking
#   - Pipeline execution type
#
# New in v1.2:
#   - Agent execution type for running agents directly
# =============================================================================

# Prevent double-sourcing
[ -n "${_SERVICE_RUNNER_LOADED:-}" ] && return 0
_SERVICE_RUNNER_LOADED=1
source "$WIGGUM_HOME/lib/core/platform.sh"

# Source dependencies (careful of circular deps - loader must be loaded first)
# service-state.sh should already be loaded by scheduler

# Runner configuration
_RUNNER_RALPH_DIR=""
_RUNNER_PROJECT_DIR=""

# Initialize the service runner
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
service_runner_init() {
    _RUNNER_RALPH_DIR="$1"
    _RUNNER_PROJECT_DIR="$2"
}

# Run a service by ID
#
# Determines execution type and dispatches to appropriate handler.
#
# Args:
#   id   - Service identifier
#   args - Additional arguments to pass
#
# Returns: 0 on success (or background started), non-zero on failure
service_run() {
    local id="$1"
    shift
    local extra_args=("$@")

    # Get execution config from cache (avoids jq for common function/command types)
    local exec_type="${_SVC_CACHE["exec_type:${id}"]:-}"

    if [ -z "$exec_type" ]; then
        log_error "No execution config for service: $id"
        return 1
    fi

    local timeout
    timeout=$(service_get_timeout "$id")

    # Get resource limits
    local limits
    limits=$(service_get_limits "$id")

    # Mark as started
    log_debug "Running service: $id (type: $exec_type)"

    case "$exec_type" in
        command)
            local command="${_SVC_CACHE["exec_cmd:${id}"]:-}"
            local working_dir
            working_dir=$(service_get_field "$id" ".execution.working_dir" "")

            if [ -z "$command" ]; then
                log_error "Service $id has no command defined"
                return 1
            fi

            _run_service_command "$id" "$command" "$timeout" "$working_dir" "$limits" "${extra_args[@]}"
            ;;

        function)
            local func="${_SVC_CACHE["exec_func:${id}"]:-}"
            local args_json="[]"

            if [ -z "$func" ]; then
                log_error "Service $id has no function defined"
                return 1
            fi

            _run_service_function "$id" "$func" "$timeout" "$args_json" "$limits" "${extra_args[@]}"
            ;;

        pipeline)
            local pipeline_name
            pipeline_name=$(service_get_field "$id" ".execution.pipeline" "")

            if [ -z "$pipeline_name" ]; then
                log_error "Service $id has no pipeline defined"
                return 1
            fi

            _run_service_pipeline "$id" "$pipeline_name" "$timeout" "$limits" "${extra_args[@]}"
            ;;

        agent)
            local agent_type
            agent_type=$(service_get_field "$id" ".execution.agent" "")

            if [ -z "$agent_type" ]; then
                log_error "Service $id has no agent defined"
                return 1
            fi

            # Agent type needs full execution JSON for config pass-through
            local execution
            execution=$(service_get_execution "$id")
            _run_service_agent "$id" "$agent_type" "$timeout" "$execution" "$limits" "${extra_args[@]}"
            ;;

        *)
            log_error "Unknown execution type for service $id: $exec_type"
            return 1
            ;;
    esac
}

# Build resource limit command prefix
#
# Creates a command prefix that applies resource limits using
# available system tools (ulimit, nice, timeout).
#
# Args:
#   limits  - JSON limits config or "null"
#   timeout - Timeout in seconds
#
# Returns: Command prefix string via stdout
_build_limits_prefix() {
    local limits="$1"
    local timeout="$2"

    local prefix=""

    # Skip if no limits configured
    if [ "$limits" = "null" ] || [ -z "$limits" ]; then
        # Just use timeout if available
        if command -v timeout &>/dev/null && [ "$timeout" -gt 0 ]; then
            prefix="timeout $timeout "
        fi
        echo "$prefix"
        return
    fi

    # Parse limit values
    local memory_limit nice_value timeout_kill
    memory_limit=$(echo "$limits" | jq -r '.memory // empty')
    nice_value=$(echo "$limits" | jq -r '.nice // empty')
    timeout_kill=$(echo "$limits" | jq -r '.timeout_kill // true')

    # Build the command prefix
    local limit_cmds=""

    # Add nice if specified
    if [ -n "$nice_value" ]; then
        limit_cmds="nice -n $nice_value "
    fi

    # Add memory limit via ulimit (if we can parse it)
    if [ -n "$memory_limit" ]; then
        local mem_bytes
        mem_bytes=$(service_parse_memory_limit "$memory_limit")
        # Convert to KB for ulimit -v
        local mem_kb=$((mem_bytes / 1024))
        # ulimit must be in a subshell, so we'll use a wrapper
        limit_cmds="${limit_cmds}bash -c 'ulimit -v $mem_kb 2>/dev/null; exec \"\$@\"' -- "
    fi

    # Add timeout
    if command -v timeout &>/dev/null && [ "$timeout" -gt 0 ]; then
        local timeout_flag=""
        if [ "$timeout_kill" = "true" ]; then
            timeout_flag="--kill-after=5"
        fi
        prefix="timeout $timeout_flag $timeout "
    fi

    echo "${prefix}${limit_cmds}"
}

# Run a command-type service
#
# Args:
#   id          - Service identifier
#   command     - Command to run
#   timeout     - Timeout in seconds
#   working_dir - Working directory (optional)
#   limits      - JSON limits config
#   args        - Extra arguments
_run_service_command() {
    local id="$1"
    local command="$2"
    local timeout="$3"
    local working_dir="$4"
    local limits="$5"
    shift 5
    local extra_args=("$@")

    # Append extra args to command if provided
    if [ ${#extra_args[@]} -gt 0 ]; then
        command="$command ${extra_args[*]}"
    fi

    # Set working directory
    local dir="${working_dir:-$_RUNNER_PROJECT_DIR}"

    # Get limits prefix
    local limits_prefix
    limits_prefix=$(_build_limits_prefix "$limits" "$timeout")

    # Record start time for metrics
    local start_time
    start_time=$(date +%s%3N 2>/dev/null || echo "$(( $(epoch_now) * 1000 ))")

    # Run in background
    (
        cd "$dir" || exit 1

        # Initialize logging for service
        export LOG_FILE="$_RUNNER_RALPH_DIR/logs/service-${id}.log"
        source "$WIGGUM_HOME/lib/core/logger.sh"
        source "$WIGGUM_HOME/lib/utils/activity-log.sh"
        activity_init "$_RUNNER_PROJECT_DIR"

        log "Service $id starting (type: command)"
        log_debug "command=$command"
        log_debug "working_dir=$dir"

        # Add WIGGUM_HOME to path for commands
        export PATH="$WIGGUM_HOME/bin:$PATH"
        export RALPH_DIR="$_RUNNER_RALPH_DIR"
        export PROJECT_DIR="$_RUNNER_PROJECT_DIR"
        export SERVICE_ID="$id"
        export SERVICE_START_TIME="$start_time"

        activity_log "service.started" "" "" "service=$id" "type=command"

        # Run with limits prefix
        local _exit_code=0
        if [ -n "$limits_prefix" ]; then
            eval "${limits_prefix}bash -c $(printf '%q' "$command")" || _exit_code=$?
        else
            bash -c "$command" || _exit_code=$?
        fi

        log "Service $id completed (exit_code=$_exit_code)"
        activity_log "service.completed" "" "" "service=$id" "exit_code=$_exit_code"
        exit $_exit_code
    ) &

    local pid=$!
    service_state_mark_started "$id" "$pid"

    log_debug "Service $id started (PID: $pid)"
    return 0
}

# Required prefix for service handler functions
# Only functions with this prefix can be invoked via services.json
# This prevents arbitrary function execution if services.json is compromised
_SERVICE_FUNCTION_PREFIX="svc_"

# Run a function-type service
#
# Args:
#   id        - Service identifier
#   func      - Function name
#   timeout   - Timeout in seconds
#   args_json - JSON array of arguments
#   limits    - JSON limits config
#   extra     - Extra arguments
_run_service_function() {
    local id="$1"
    local func="$2"
    local timeout="$3"
    local args_json="$4"
    local limits="$5"
    shift 5
    local extra_args=("$@")

    # Security: Validate function name starts with required prefix
    # This ensures only explicitly registered service handlers can be called
    if [[ "$func" != "${_SERVICE_FUNCTION_PREFIX}"* ]]; then
        log_error "Service $id: function '$func' rejected - must start with '${_SERVICE_FUNCTION_PREFIX}'"
        log_error "Service handlers must be defined in lib/services/ with svc_* prefix"
        service_state_mark_failed "$id"
        return 1
    fi

    # Check if function exists
    if ! declare -F "$func" &>/dev/null; then
        log_error "Function not found for service $id: $func"
        service_state_mark_failed "$id"
        return 1
    fi

    # Parse JSON args
    local -a func_args=()
    if [ "$args_json" != "[]" ] && [ -n "$args_json" ]; then
        while IFS= read -r arg; do
            func_args+=("$arg")
        done < <(echo "$args_json" | jq -r '.[]')
    fi

    # Add extra args
    func_args+=("${extra_args[@]}")

    # Get limits (nice only for functions, as they run in current process)
    local nice_value=""
    if [ "$limits" != "null" ] && [ -n "$limits" ]; then
        nice_value=$(echo "$limits" | jq -r '.nice // empty')
    fi

    # Record start time for metrics
    local start_time
    start_time=$(date +%s%3N 2>/dev/null || echo "$(( $(epoch_now) * 1000 ))")

    # Run in background
    (
        # Initialize logging for service
        export LOG_FILE="$_RUNNER_RALPH_DIR/logs/service-${id}.log"
        source "$WIGGUM_HOME/lib/core/logger.sh"
        source "$WIGGUM_HOME/lib/utils/activity-log.sh"
        activity_init "$_RUNNER_PROJECT_DIR"

        log "Service $id starting (type: function)"
        log_debug "function=$func"
        log_debug "args=${func_args[*]:-}"

        export RALPH_DIR="$_RUNNER_RALPH_DIR"
        export PROJECT_DIR="$_RUNNER_PROJECT_DIR"
        export SERVICE_ID="$id"
        export SERVICE_START_TIME="$start_time"

        activity_log "service.started" "" "" "service=$id" "type=function"

        # Apply nice if configured
        if [ -n "$nice_value" ]; then
            renice -n "$nice_value" $$ 2>/dev/null || true
        fi

        # Call the function with args
        # Note: We run the function directly (not via bash -c) to preserve
        # access to all inherited function definitions from the parent shell.
        # For timeout, we use background process monitoring instead of the
        # 'timeout' command which would spawn a new bash losing context.
        local _exit_code=0
        if [ "$timeout" -gt 0 ]; then
            # Run function in nested background for timeout handling
            "$func" "${func_args[@]}" &
            local func_pid=$!

            # Monitor for timeout
            local waited=0
            while kill -0 "$func_pid" 2>/dev/null && [ "$waited" -lt "$timeout" ]; do
                sleep 1
                ((++waited))
            done

            if kill -0 "$func_pid" 2>/dev/null; then
                # Timed out - kill the process
                kill -TERM "$func_pid" 2>/dev/null || true
                sleep 1
                kill -9 "$func_pid" 2>/dev/null || true
                log "Service $id timed out after ${timeout}s"
                activity_log "service.completed" "" "" "service=$id" "exit_code=124" "timeout=true"
                exit 124  # Standard timeout exit code
            fi

            wait "$func_pid"
            _exit_code=$?
        else
            "$func" "${func_args[@]}" || _exit_code=$?
        fi

        log "Service $id completed (exit_code=$_exit_code)"
        activity_log "service.completed" "" "" "service=$id" "exit_code=$_exit_code"
        exit $_exit_code
    ) &

    local pid=$!
    service_state_mark_started "$id" "$pid"

    log_debug "Service $id (function: $func) started (PID: $pid)"
    return 0
}

# Run a pipeline-type service
#
# Executes a named pipeline using the pipeline runner.
#
# Args:
#   id            - Service identifier
#   pipeline_name - Pipeline name to execute
#   timeout       - Timeout in seconds
#   limits        - JSON limits config
#   extra         - Extra arguments
_run_service_pipeline() {
    local id="$1"
    local pipeline_name="$2"
    local timeout="$3"
    local limits="$4"
    shift 4
    local extra_args=("$@")

    # Check if pipeline runner is available
    if [ ! -f "$WIGGUM_HOME/lib/pipeline/pipeline-runner.sh" ]; then
        log_error "Pipeline runner not available for service $id"
        service_state_mark_failed "$id"
        return 1
    fi

    # Look for pipeline config
    local pipeline_config=""
    local search_paths=(
        "$_RUNNER_RALPH_DIR/pipelines/${pipeline_name}.json"
        "$_RUNNER_RALPH_DIR/pipeline.json"
        "$WIGGUM_HOME/config/pipelines/${pipeline_name}.json"
        "$WIGGUM_HOME/config/pipelines/default.json"
    )

    for path in "${search_paths[@]}"; do
        if [ -f "$path" ]; then
            pipeline_config="$path"
            break
        fi
    done

    if [ -z "$pipeline_config" ]; then
        log_error "Pipeline config not found for service $id: $pipeline_name"
        service_state_mark_failed "$id"
        return 1
    fi

    # Get limits prefix
    local limits_prefix
    limits_prefix=$(_build_limits_prefix "$limits" "$timeout")

    # Record start time
    local start_time
    start_time=$(date +%s%3N 2>/dev/null || echo "$(( $(epoch_now) * 1000 ))")

    # Run pipeline in background
    (
        # Initialize logging for service
        export LOG_FILE="$_RUNNER_RALPH_DIR/logs/service-${id}.log"
        source "$WIGGUM_HOME/lib/core/logger.sh"
        source "$WIGGUM_HOME/lib/utils/activity-log.sh"
        activity_init "$_RUNNER_PROJECT_DIR"

        log "Service $id starting (type: pipeline)"
        log_debug "pipeline=$pipeline_name"
        log_debug "config=$pipeline_config"

        export RALPH_DIR="$_RUNNER_RALPH_DIR"
        export PROJECT_DIR="$_RUNNER_PROJECT_DIR"
        export SERVICE_ID="$id"
        export SERVICE_START_TIME="$start_time"

        activity_log "service.started" "" "" "service=$id" "type=pipeline" "pipeline=$pipeline_name"

        # Source pipeline runner
        source "$WIGGUM_HOME/lib/pipeline/pipeline-runner.sh"

        # Run the pipeline
        local _exit_code=0
        if [ -n "$limits_prefix" ]; then
            eval "${limits_prefix}pipeline_run '$pipeline_config' '${extra_args[*]}'" || _exit_code=$?
        else
            pipeline_run "$pipeline_config" "${extra_args[@]}" || _exit_code=$?
        fi

        log "Service $id completed (exit_code=$_exit_code)"
        activity_log "service.completed" "" "" "service=$id" "exit_code=$_exit_code"
        exit $_exit_code
    ) &

    local pid=$!
    service_state_mark_started "$id" "$pid"

    log_debug "Service $id (pipeline: $pipeline_name) started (PID: $pid)"
    return 0
}

# Run an agent-type service
#
# Executes an agent using the agent registry.
#
# Args:
#   id         - Service identifier
#   agent_type - Agent type to execute (e.g., "system.task-worker")
#   timeout    - Timeout in seconds
#   execution  - Full execution JSON config
#   limits     - JSON limits config
#   extra      - Extra arguments
_run_service_agent() {
    local id="$1"
    local agent_type="$2"
    local timeout="$3"
    local execution="$4"
    local limits="$5"
    shift 5
    local extra_args=("$@")

    # Extract agent config from execution
    local worker_dir max_iterations max_turns monitor_interval
    worker_dir=$(echo "$execution" | jq -r '.worker_dir // ""')
    max_iterations=$(echo "$execution" | jq -r '.max_iterations // 20')
    max_turns=$(echo "$execution" | jq -r '.max_turns // 50')
    monitor_interval=$(echo "$execution" | jq -r '.monitor_interval // 30')

    # If no worker_dir specified, create a service-specific worker directory
    if [ -z "$worker_dir" ]; then
        local timestamp
        timestamp=$(epoch_now)
        worker_dir="$_RUNNER_RALPH_DIR/workers/service-${id}-${timestamp}"
        mkdir -p "$worker_dir/logs" "$worker_dir/results"
    fi

    # Get limits prefix
    local limits_prefix
    limits_prefix=$(_build_limits_prefix "$limits" "$timeout")

    # Record start time
    local start_time
    start_time=$(date +%s%3N 2>/dev/null || echo "$(( $(epoch_now) * 1000 ))")

    # Run agent in background
    (
        # Initialize logging for service
        export LOG_FILE="$_RUNNER_RALPH_DIR/logs/service-${id}.log"
        source "$WIGGUM_HOME/lib/core/logger.sh"
        source "$WIGGUM_HOME/lib/utils/activity-log.sh"
        activity_init "$_RUNNER_PROJECT_DIR"

        log "Service $id starting (type: agent)"
        log_debug "agent=$agent_type"
        log_debug "worker_dir=$worker_dir"
        log_debug "max_iterations=$max_iterations"
        log_debug "max_turns=$max_turns"

        export RALPH_DIR="$_RUNNER_RALPH_DIR"
        export PROJECT_DIR="$_RUNNER_PROJECT_DIR"
        export SERVICE_ID="$id"
        export SERVICE_START_TIME="$start_time"
        export WIGGUM_HOME

        activity_log "service.started" "" "" "service=$id" "type=agent" "agent=$agent_type"

        # Source agent registry
        source "$WIGGUM_HOME/lib/worker/agent-registry.sh"

        # Run the agent
        local _exit_code=0
        if [ -n "$limits_prefix" ]; then
            eval "${limits_prefix}run_agent '$agent_type' '$worker_dir' '$_RUNNER_PROJECT_DIR' '$monitor_interval' '$max_iterations' '$max_turns' ${extra_args[*]}" || _exit_code=$?
        else
            run_agent "$agent_type" "$worker_dir" "$_RUNNER_PROJECT_DIR" "$monitor_interval" "$max_iterations" "$max_turns" "${extra_args[@]}" || _exit_code=$?
        fi

        log "Service $id completed (exit_code=$_exit_code)"
        activity_log "service.completed" "" "" "service=$id" "exit_code=$_exit_code"
        exit $_exit_code
    ) &

    local pid=$!
    service_state_mark_started "$id" "$pid"

    log_debug "Service $id (agent: $agent_type) started (PID: $pid, worker: $worker_dir)"
    return 0
}

# Run a service synchronously (blocking)
#
# Useful for testing or when caller needs result immediately.
#
# Args:
#   id   - Service identifier
#   args - Additional arguments
#
# Returns: Exit code from service execution
service_run_sync() {
    local id="$1"
    shift
    local extra_args=("$@")

    local exec_type="${_SVC_CACHE["exec_type:${id}"]:-}"

    local timeout
    timeout=$(service_get_timeout "$id")

    local limits
    limits=$(service_get_limits "$id")

    # Record start time
    local start_time
    start_time=$(date +%s%3N 2>/dev/null || echo "$(( $(epoch_now) * 1000 ))")

    service_state_mark_started "$id"

    local exit_code=0

    case "$exec_type" in
        command)
            local command="${_SVC_CACHE["exec_cmd:${id}"]:-}"
            local working_dir
            working_dir=$(service_get_field "$id" ".execution.working_dir" "")

            local dir="${working_dir:-$_RUNNER_PROJECT_DIR}"

            local limits_prefix
            limits_prefix=$(_build_limits_prefix "$limits" "$timeout")

            (
                cd "$dir" || exit 1
                export PATH="$WIGGUM_HOME/bin:$PATH"
                export RALPH_DIR="$_RUNNER_RALPH_DIR"
                export PROJECT_DIR="$_RUNNER_PROJECT_DIR"
                export SERVICE_ID="$id"

                if [ ${#extra_args[@]} -gt 0 ]; then
                    command="$command ${extra_args[*]}"
                fi

                if [ -n "$limits_prefix" ]; then
                    eval "${limits_prefix}bash -c $(printf '%q' "$command")"
                else
                    bash -c "$command"
                fi
            )
            exit_code=$?
            ;;

        function)
            local func="${_SVC_CACHE["exec_func:${id}"]:-}"
            local args_json="[]"

            # Security: Validate function name starts with required prefix
            if [[ "$func" != "${_SERVICE_FUNCTION_PREFIX}"* ]]; then
                log_error "Service $id: function '$func' rejected - must start with '${_SERVICE_FUNCTION_PREFIX}'"
                exit_code=1
            elif ! declare -F "$func" &>/dev/null; then
                log_error "Function not found: $func"
                exit_code=1
            else
                local -a func_args=()
                if [ "$args_json" != "[]" ] && [ -n "$args_json" ]; then
                    while IFS= read -r arg; do
                        func_args+=("$arg")
                    done < <(echo "$args_json" | jq -r '.[]')
                fi
                func_args+=("${extra_args[@]}")

                export RALPH_DIR="$_RUNNER_RALPH_DIR"
                export PROJECT_DIR="$_RUNNER_PROJECT_DIR"
                export SERVICE_ID="$id"

                # Run function directly to preserve inherited function definitions.
                # For timeout, use background process monitoring.
                if [ "$timeout" -gt 0 ]; then
                    "$func" "${func_args[@]}" &
                    local func_pid=$!

                    local waited=0
                    while kill -0 "$func_pid" 2>/dev/null && [ "$waited" -lt "$timeout" ]; do
                        sleep 1
                        ((++waited))
                    done

                    if kill -0 "$func_pid" 2>/dev/null; then
                        kill -TERM "$func_pid" 2>/dev/null || true
                        sleep 1
                        kill -9 "$func_pid" 2>/dev/null || true
                        exit_code=124
                    else
                        wait "$func_pid"
                        exit_code=$?
                    fi
                else
                    "$func" "${func_args[@]}"
                    exit_code=$?
                fi
            fi
            ;;

        pipeline)
            local pipeline_name
            pipeline_name=$(service_get_field "$id" ".execution.pipeline" "")

            # Find pipeline config
            local pipeline_config=""
            for path in "$_RUNNER_RALPH_DIR/pipelines/${pipeline_name}.json" \
                        "$WIGGUM_HOME/config/pipelines/${pipeline_name}.json"; do
                if [ -f "$path" ]; then
                    pipeline_config="$path"
                    break
                fi
            done

            if [ -z "$pipeline_config" ]; then
                log_error "Pipeline config not found: $pipeline_name"
                exit_code=1
            else
                source "$WIGGUM_HOME/lib/pipeline/pipeline-runner.sh" 2>/dev/null || true
                if declare -F pipeline_run &>/dev/null; then
                    pipeline_run "$pipeline_config" "${extra_args[@]}"
                    exit_code=$?
                else
                    log_error "Pipeline runner not available"
                    exit_code=1
                fi
            fi
            ;;

        agent)
            local agent_type worker_dir max_iterations max_turns monitor_interval
            agent_type=$(service_get_field "$id" ".execution.agent" "")
            worker_dir=$(service_get_field "$id" ".execution.worker_dir" "")
            max_iterations=$(service_get_field "$id" ".execution.max_iterations" "20")
            max_turns=$(service_get_field "$id" ".execution.max_turns" "50")
            monitor_interval=$(service_get_field "$id" ".execution.monitor_interval" "30")

            if [ -z "$agent_type" ]; then
                log_error "Service $id has no agent defined"
                exit_code=1
            else
                # Create worker directory if not specified
                if [ -z "$worker_dir" ]; then
                    local timestamp
                    timestamp=$(epoch_now)
                    worker_dir="$_RUNNER_RALPH_DIR/workers/service-${id}-${timestamp}"
                    mkdir -p "$worker_dir/logs" "$worker_dir/results"
                fi

                export RALPH_DIR="$_RUNNER_RALPH_DIR"
                export PROJECT_DIR="$_RUNNER_PROJECT_DIR"
                export SERVICE_ID="$id"

                # Source agent registry and run
                source "$WIGGUM_HOME/lib/worker/agent-registry.sh" 2>/dev/null || true
                if declare -F run_agent &>/dev/null; then
                    run_agent "$agent_type" "$worker_dir" "$_RUNNER_PROJECT_DIR" \
                        "$monitor_interval" "$max_iterations" "$max_turns" "${extra_args[@]}"
                    exit_code=$?
                else
                    log_error "Agent registry not available"
                    exit_code=1
                fi
            fi
            ;;

        *)
            log_error "Unknown execution type: $exec_type"
            exit_code=1
            ;;
    esac

    # Calculate duration and record metrics
    local end_time
    end_time=$(date +%s%3N 2>/dev/null || echo "$(( $(epoch_now) * 1000 ))")
    local duration_ms=$((end_time - start_time))
    service_state_record_execution "$id" "$duration_ms" "$exit_code"

    # Update state based on result
    if [ "$exit_code" -eq 0 ]; then
        service_state_mark_completed "$id"
    else
        service_state_mark_failed "$id"
    fi

    return "$exit_code"
}

# Wait for a background service to complete
#
# Args:
#   id      - Service identifier
#   timeout - Max time to wait in seconds (0 = forever)
#
# Returns: Exit code from service, or 124 on timeout
service_wait() {
    local id="$1"
    local timeout="${2:-0}"

    local pid
    pid=$(service_state_get_pid "$id")

    if [ -z "$pid" ]; then
        log_debug "Service $id not running (no PID)"
        return 0
    fi

    if [ "$timeout" -gt 0 ]; then
        local waited=0
        while kill -0 "$pid" 2>/dev/null && [ "$waited" -lt "$timeout" ]; do
            sleep 1
            ((++waited))
        done

        if kill -0 "$pid" 2>/dev/null; then
            log_warn "Service $id timed out, killing"
            kill "$pid" 2>/dev/null || true
            service_state_mark_failed "$id"
            return 124
        fi
    fi

    wait "$pid" 2>/dev/null
    local exit_code=$?

    # Record metrics
    local start_time end_time duration_ms
    start_time=$(service_state_get_last_run "$id")
    end_time=$(epoch_now)
    duration_ms=$(( (end_time - start_time) * 1000 ))
    service_state_record_execution "$id" "$duration_ms" "$exit_code"

    if [ "$exit_code" -eq 0 ]; then
        service_state_mark_completed "$id"
    else
        service_state_mark_failed "$id"
    fi

    return "$exit_code"
}

# Stop a running service
#
# Args:
#   id     - Service identifier
#   signal - Signal to send (default: TERM)
#
# Returns: 0 if stopped, 1 if not running
service_stop() {
    local id="$1"
    local signal="${2:-TERM}"

    local pid
    pid=$(service_state_get_pid "$id")

    if [ -z "$pid" ]; then
        log_debug "Service $id not running (no PID)"
        return 1
    fi

    if ! kill -0 "$pid" 2>/dev/null; then
        log_debug "Service $id not running (PID $pid dead)"
        service_state_mark_completed "$id"
        return 1
    fi

    log_debug "Stopping service $id (PID: $pid, signal: $signal)"
    kill "-$signal" "$pid" 2>/dev/null || true

    # Wait briefly for clean shutdown
    local waited=0
    while kill -0 "$pid" 2>/dev/null && [ "$waited" -lt 5 ]; do
        sleep 1
        ((++waited))
    done

    # Force kill if still running
    if kill -0 "$pid" 2>/dev/null; then
        log_warn "Service $id did not stop gracefully, force killing"
        kill -9 "$pid" 2>/dev/null || true
    fi

    service_state_mark_completed "$id"
    return 0
}

# Stop all running services
#
# Sends TERM signal to all running services, waits briefly,
# then sends KILL to any remaining.
service_stop_all() {
    local enabled_services
    enabled_services=$(service_get_enabled)

    # First pass: send TERM
    for id in $enabled_services; do
        if service_state_is_running "$id"; then
            local pid
            pid=$(service_state_get_pid "$id")
            if [ -n "$pid" ]; then
                log_debug "Stopping service $id (PID: $pid)"
                kill -TERM "$pid" 2>/dev/null || true
            fi
        fi
    done

    # Wait for graceful shutdown
    sleep 2

    # Second pass: force kill any remaining
    for id in $enabled_services; do
        if service_state_is_running "$id"; then
            local pid
            pid=$(service_state_get_pid "$id")
            if [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null; then
                log_warn "Force killing service $id (PID: $pid)"
                kill -9 "$pid" 2>/dev/null || true
            fi
            service_state_mark_completed "$id"
        fi
    done
}

# Get service output/logs (if captured)
#
# Note: This is a placeholder for future implementation
# where service output could be captured to files.
#
# Args:
#   id    - Service identifier
#   lines - Number of lines to return (default: 100)
#
# Returns: Last N lines of service output
service_get_output() {
    local id="$1"
    local lines="${2:-100}"

    local output_file="$_RUNNER_RALPH_DIR/logs/service-${id}.log"

    if [ -f "$output_file" ]; then
        tail -n "$lines" "$output_file"
    else
        echo "No output captured for service $id"
    fi
}
