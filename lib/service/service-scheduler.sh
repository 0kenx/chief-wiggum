#!/usr/bin/env bash
# =============================================================================
# service-scheduler.sh - Service timing and execution management
#
# Manages the scheduling loop for declaratively-configured services.
#
# Provides:
#   service_scheduler_init()          - Initialize scheduler state
#   service_scheduler_tick()          - Check and run due services
#   service_scheduler_shutdown()      - Clean shutdown
#   service_is_due(id)                - Check if service should run
#   service_mark_run(id)              - Record execution timestamp
#   service_trigger_event(event)      - Trigger event-based services
# =============================================================================

# Prevent double-sourcing
[ -n "${_SERVICE_SCHEDULER_LOADED:-}" ] && return 0
_SERVICE_SCHEDULER_LOADED=1

# Source dependencies
source "$WIGGUM_HOME/lib/service/service-loader.sh"
source "$WIGGUM_HOME/lib/service/service-state.sh"
source "$WIGGUM_HOME/lib/service/service-runner.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"

# Scheduler configuration
_SCHED_RALPH_DIR=""
_SCHED_PROJECT_DIR=""
_SCHED_INITIALIZED=false
_SCHED_STARTUP_COMPLETE=false

# Initialize the service scheduler
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
service_scheduler_init() {
    local ralph_dir="$1"
    local project_dir="$2"

    _SCHED_RALPH_DIR="$ralph_dir"
    _SCHED_PROJECT_DIR="$project_dir"

    # Initialize state tracking
    service_state_init "$ralph_dir"

    # Try to restore previous state
    if service_state_restore; then
        log_debug "Restored previous service scheduler state"
    fi

    # Load service configuration
    local config_file="$WIGGUM_HOME/config/services.json"
    if [ -f "$config_file" ]; then
        if ! service_load "$config_file"; then
            log_warn "Failed to load service config, using built-in defaults"
            service_load_builtin_defaults
        fi
    else
        service_load_builtin_defaults
    fi

    # Load project overrides if present
    local override_file="$ralph_dir/services.json"
    if [ -f "$override_file" ]; then
        service_load_override "$override_file"
    fi

    # Initialize runner
    service_runner_init "$ralph_dir" "$project_dir"

    _SCHED_INITIALIZED=true
    _SCHED_STARTUP_COMPLETE=false

    log "Service scheduler initialized with $(service_count) services"
}

# Run startup services (those with run_on_startup: true)
#
# Called once after initialization to run services immediately.
service_scheduler_run_startup() {
    [ "$_SCHED_INITIALIZED" = true ] || return 1
    [ "$_SCHED_STARTUP_COMPLETE" = false ] || return 0

    log_debug "Running startup services..."

    local enabled_services
    enabled_services=$(service_get_enabled)

    for id in $enabled_services; do
        if service_runs_on_startup "$id"; then
            local schedule_type
            schedule_type=$(service_get_field "$id" ".schedule.type" "interval")

            # Only run interval services on startup (event services need triggers)
            if [ "$schedule_type" = "interval" ]; then
                log_debug "Running startup service: $id"
                _run_service_if_allowed "$id"
            fi
        fi
    done

    _SCHED_STARTUP_COMPLETE=true
}

# One tick of the service scheduler
#
# Checks all enabled services and runs those that are due.
# Should be called periodically (e.g., every second in main loop).
service_scheduler_tick() {
    [ "$_SCHED_INITIALIZED" = true ] || return 1

    # Run startup services on first tick
    if [ "$_SCHED_STARTUP_COMPLETE" = false ]; then
        service_scheduler_run_startup
    fi

    local enabled_services
    enabled_services=$(service_get_enabled)

    for id in $enabled_services; do
        local schedule_type
        schedule_type=$(service_get_field "$id" ".schedule.type" "interval")

        case "$schedule_type" in
            interval)
                if service_is_due "$id"; then
                    _run_service_if_allowed "$id"
                fi
                ;;
            continuous)
                # Continuous services restart automatically when stopped
                if ! service_state_is_running "$id"; then
                    local restart_delay
                    restart_delay=$(service_get_field "$id" ".schedule.restart_delay" "5")
                    local last_run
                    last_run=$(service_state_get_last_run "$id")
                    local now
                    now=$(date +%s)

                    if [ $((now - last_run)) -ge "$restart_delay" ]; then
                        _run_service_if_allowed "$id"
                    fi
                fi
                ;;
            event)
                # Event services are triggered by service_trigger_event
                ;;
        esac
    done

    # Check for completed background services
    _check_completed_services

    # Periodically save state
    service_state_save
}

# Check if an interval service is due to run
#
# Args:
#   id - Service identifier
#
# Returns: 0 if due, 1 if not due
service_is_due() {
    local id="$1"

    local interval
    interval=$(service_get_interval "$id")
    [ "$interval" -gt 0 ] || return 1

    local last_run
    last_run=$(service_state_get_last_run "$id")

    local now
    now=$(date +%s)

    local elapsed=$((now - last_run))

    [ "$elapsed" -ge "$interval" ]
}

# Trigger event-based services
#
# Args:
#   event - Event name (e.g., "worker.completed", "scheduling_event")
#   args  - Optional arguments to pass to service
service_trigger_event() {
    local event="$1"
    shift
    local args=("$@")

    [ "$_SCHED_INITIALIZED" = true ] || return 1

    local enabled_services
    enabled_services=$(service_get_enabled)

    for id in $enabled_services; do
        local schedule_type trigger
        schedule_type=$(service_get_field "$id" ".schedule.type" "interval")
        [ "$schedule_type" = "event" ] || continue

        trigger=$(service_get_field "$id" ".schedule.trigger" "")
        if [ "$trigger" = "$event" ]; then
            log_debug "Event '$event' triggered service: $id"
            _run_service_if_allowed "$id" "${args[@]}"
        fi
    done
}

# Run a service if concurrency rules allow
#
# Args:
#   id   - Service identifier
#   args - Additional arguments to pass to service
_run_service_if_allowed() {
    local id="$1"
    shift
    local args=("$@")

    # Check concurrency
    local concurrency
    concurrency=$(service_get_concurrency "$id")

    local if_running
    # Note: max_instances is available in concurrency but not yet implemented
    if_running=$(echo "$concurrency" | jq -r '.if_running // "skip"')

    if service_state_is_running "$id"; then
        case "$if_running" in
            skip)
                log_debug "Skipping $id - already running"
                service_state_mark_skipped "$id"
                return 0
                ;;
            queue)
                # TODO: Implement queueing
                log_debug "Queueing $id - already running"
                return 0
                ;;
            kill)
                # Stop the running instance
                local pid
                pid=$(service_state_get_pid "$id")
                if [ -n "$pid" ]; then
                    log_debug "Killing previous instance of $id (PID: $pid)"
                    kill "$pid" 2>/dev/null || true
                fi
                ;;
        esac
    fi

    # Run the service
    service_run "$id" "${args[@]}"
}

# Check for completed background services and update their state
_check_completed_services() {
    local enabled_services
    enabled_services=$(service_get_enabled)

    for id in $enabled_services; do
        local status
        status=$(service_state_get_status "$id")

        if [ "$status" = "running" ]; then
            local pid
            pid=$(service_state_get_pid "$id")

            if [ -n "$pid" ] && ! kill -0 "$pid" 2>/dev/null; then
                # Process has exited
                # Check exit code from wait (if possible)
                wait "$pid" 2>/dev/null
                local exit_code=$?

                if [ "$exit_code" -eq 0 ]; then
                    service_state_mark_completed "$id"
                    log_debug "Service $id completed successfully"
                else
                    service_state_mark_failed "$id"
                    log_debug "Service $id failed (exit code: $exit_code)"
                    _handle_service_failure "$id"
                fi
            fi
        fi
    done
}

# Handle service failure according to restart policy
_handle_service_failure() {
    local id="$1"

    local restart_policy
    restart_policy=$(service_get_field "$id" ".restart_policy.on_failure" "skip")

    local max_retries
    max_retries=$(service_get_field "$id" ".restart_policy.max_retries" "2")

    local fail_count
    fail_count=$(service_state_get_fail_count "$id")

    case "$restart_policy" in
        retry)
            if [ "$fail_count" -lt "$max_retries" ]; then
                log_debug "Retrying service $id (attempt $((fail_count + 1))/$max_retries)"
                service_run "$id"
            else
                log_warn "Service $id failed $fail_count times, giving up"
            fi
            ;;
        skip)
            log_debug "Skipping retry for failed service $id"
            ;;
        abort)
            log_error "Service $id failed with abort policy"
            # Could signal scheduler to stop
            ;;
    esac
}

# Clean shutdown of the scheduler
service_scheduler_shutdown() {
    [ "$_SCHED_INITIALIZED" = true ] || return 0

    log_debug "Shutting down service scheduler..."

    # Save final state
    service_state_save

    _SCHED_INITIALIZED=false
}

# Get scheduler status summary
#
# Returns: JSON object with scheduler status
service_scheduler_status() {
    local enabled_count running_count failed_count

    enabled_count=0
    running_count=0
    failed_count=0

    local enabled_services
    enabled_services=$(service_get_enabled)

    for id in $enabled_services; do
        ((++enabled_count))

        local status
        status=$(service_state_get_status "$id")

        case "$status" in
            running) ((++running_count)) ;;
            failed) ((++failed_count)) ;;
        esac
    done

    jq -n \
        --argjson enabled "$enabled_count" \
        --argjson running "$running_count" \
        --argjson failed "$failed_count" \
        --argjson initialized "$([[ "$_SCHED_INITIALIZED" = true ]] && echo true || echo false)" \
        '{
            "initialized": $initialized,
            "enabled_services": $enabled,
            "running_services": $running,
            "failed_services": $failed
        }'
}

# Get detailed status for a specific service
#
# Args:
#   id - Service identifier
#
# Returns: JSON object with service status
service_scheduler_service_status() {
    local id="$1"

    local status last_run run_count fail_count interval
    status=$(service_state_get_status "$id")
    last_run=$(service_state_get_last_run "$id")
    run_count=$(service_state_get_run_count "$id")
    fail_count=$(service_state_get_fail_count "$id")
    interval=$(service_get_interval "$id")

    local now
    now=$(date +%s)

    local next_run_in=""
    if [ "$interval" -gt 0 ]; then
        local elapsed=$((now - last_run))
        local remaining=$((interval - elapsed))
        [ "$remaining" -lt 0 ] && remaining=0
        next_run_in="$remaining"
    fi

    local schedule_type
    schedule_type=$(service_get_field "$id" ".schedule.type" "interval")

    local description
    description=$(service_get_field "$id" ".description" "")

    jq -n \
        --arg id "$id" \
        --arg status "$status" \
        --arg schedule_type "$schedule_type" \
        --argjson last_run "$last_run" \
        --argjson run_count "$run_count" \
        --argjson fail_count "$fail_count" \
        --argjson interval "$interval" \
        --arg next_run_in "${next_run_in:-null}" \
        --arg description "$description" \
        '{
            "id": $id,
            "description": $description,
            "status": $status,
            "schedule_type": $schedule_type,
            "last_run": $last_run,
            "run_count": $run_count,
            "fail_count": $fail_count,
            "interval": $interval,
            "next_run_in": (if $next_run_in == "null" then null else ($next_run_in | tonumber) end)
        }'
}

# Check if scheduler has completed (all services stopped, continuous tasks done)
#
# Returns: 0 if complete (can exit), 1 if still running
service_scheduler_is_complete() {
    # For now, always return 1 (never complete on its own)
    # The orchestrator handles completion logic
    return 1
}
