#!/usr/bin/env bash
# =============================================================================
# service-runner.sh - Execute services based on type
#
# Handles the actual execution of services based on their execution type:
# - command: Shell commands
# - function: Bash functions
# - pipeline: Pipeline definitions (future)
#
# Provides:
#   service_runner_init(ralph_dir, project_dir) - Initialize runner
#   service_run(id, args...)                    - Execute a service
#   service_run_command(cmd, timeout)           - Run shell command
#   service_run_function(func, args...)         - Call bash function
#   service_handle_result(id, exit_code)        - Process result
# =============================================================================

# Prevent double-sourcing
[ -n "${_SERVICE_RUNNER_LOADED:-}" ] && return 0
_SERVICE_RUNNER_LOADED=1

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

    # Get execution config
    local execution
    execution=$(service_get_execution "$id")

    if [ -z "$execution" ] || [ "$execution" = "null" ]; then
        log_error "No execution config for service: $id"
        return 1
    fi

    local exec_type
    exec_type=$(echo "$execution" | jq -r '.type // "unknown"')

    local timeout
    timeout=$(service_get_timeout "$id")

    # Mark as started
    log_debug "Running service: $id (type: $exec_type)"

    case "$exec_type" in
        command)
            local command working_dir
            command=$(echo "$execution" | jq -r '.command // ""')
            working_dir=$(echo "$execution" | jq -r '.working_dir // ""')

            if [ -z "$command" ]; then
                log_error "Service $id has no command defined"
                return 1
            fi

            _run_service_command "$id" "$command" "$timeout" "$working_dir" "${extra_args[@]}"
            ;;

        function)
            local func args_json
            func=$(echo "$execution" | jq -r '.function // ""')
            args_json=$(echo "$execution" | jq -c '.args // []')

            if [ -z "$func" ]; then
                log_error "Service $id has no function defined"
                return 1
            fi

            _run_service_function "$id" "$func" "$timeout" "$args_json" "${extra_args[@]}"
            ;;

        pipeline)
            local pipeline_name
            pipeline_name=$(echo "$execution" | jq -r '.pipeline // ""')

            if [ -z "$pipeline_name" ]; then
                log_error "Service $id has no pipeline defined"
                return 1
            fi

            log_warn "Pipeline execution not yet implemented for service: $id"
            return 1
            ;;

        *)
            log_error "Unknown execution type for service $id: $exec_type"
            return 1
            ;;
    esac
}

# Run a command-type service
#
# Args:
#   id          - Service identifier
#   command     - Command to run
#   timeout     - Timeout in seconds
#   working_dir - Working directory (optional)
#   args        - Extra arguments
_run_service_command() {
    local id="$1"
    local command="$2"
    local timeout="$3"
    local working_dir="$4"
    shift 4
    local extra_args=("$@")

    # Append extra args to command if provided
    if [ ${#extra_args[@]} -gt 0 ]; then
        command="$command ${extra_args[*]}"
    fi

    # Set working directory
    local dir="${working_dir:-$_RUNNER_PROJECT_DIR}"

    # Run in background
    (
        cd "$dir" || exit 1

        # Add WIGGUM_HOME to path for commands
        export PATH="$WIGGUM_HOME/bin:$PATH"
        export RALPH_DIR="$_RUNNER_RALPH_DIR"
        export PROJECT_DIR="$_RUNNER_PROJECT_DIR"

        # Run with timeout if available
        if command -v timeout &>/dev/null && [ "$timeout" -gt 0 ]; then
            timeout "$timeout" bash -c "$command"
        else
            bash -c "$command"
        fi
    ) &

    local pid=$!
    service_state_mark_started "$id" "$pid"

    log_debug "Service $id started (PID: $pid)"
    return 0
}

# Run a function-type service
#
# Args:
#   id        - Service identifier
#   func      - Function name
#   timeout   - Timeout in seconds
#   args_json - JSON array of arguments
#   extra     - Extra arguments
_run_service_function() {
    local id="$1"
    local func="$2"
    local timeout="$3"
    local args_json="$4"
    shift 4
    local extra_args=("$@")

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

    # Run in background
    (
        export RALPH_DIR="$_RUNNER_RALPH_DIR"
        export PROJECT_DIR="$_RUNNER_PROJECT_DIR"

        # Call the function with args
        "$func" "${func_args[@]}"
    ) &

    local pid=$!
    service_state_mark_started "$id" "$pid"

    log_debug "Service $id (function: $func) started (PID: $pid)"
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

    local execution
    execution=$(service_get_execution "$id")

    local exec_type
    exec_type=$(echo "$execution" | jq -r '.type // "unknown"')

    local timeout
    timeout=$(service_get_timeout "$id")

    service_state_mark_started "$id"

    local exit_code=0

    case "$exec_type" in
        command)
            local command working_dir
            command=$(echo "$execution" | jq -r '.command // ""')
            working_dir=$(echo "$execution" | jq -r '.working_dir // ""')

            local dir="${working_dir:-$_RUNNER_PROJECT_DIR}"

            (
                cd "$dir" || exit 1
                export PATH="$WIGGUM_HOME/bin:$PATH"
                export RALPH_DIR="$_RUNNER_RALPH_DIR"
                export PROJECT_DIR="$_RUNNER_PROJECT_DIR"

                if [ ${#extra_args[@]} -gt 0 ]; then
                    command="$command ${extra_args[*]}"
                fi

                if command -v timeout &>/dev/null && [ "$timeout" -gt 0 ]; then
                    timeout "$timeout" bash -c "$command"
                else
                    bash -c "$command"
                fi
            )
            exit_code=$?
            ;;

        function)
            local func args_json
            func=$(echo "$execution" | jq -r '.function // ""')
            args_json=$(echo "$execution" | jq -c '.args // []')

            if ! declare -F "$func" &>/dev/null; then
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

                "$func" "${func_args[@]}"
                exit_code=$?
            fi
            ;;

        *)
            log_error "Unknown execution type: $exec_type"
            exit_code=1
            ;;
    esac

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
