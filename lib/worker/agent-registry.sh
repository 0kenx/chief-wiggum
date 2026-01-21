#!/usr/bin/env bash
# agent-registry.sh - Agent discovery, validation, and invocation
#
# Provides functions to load and run agents from lib/agents/.
# Each agent is a self-contained script that defines:
#   - agent_required_paths()  - List of paths that must exist before running
#   - agent_output_files()    - List of files that must exist (non-empty) after running
#   - agent_run()             - Main entry point
#   - agent_cleanup()         - Optional cleanup after completion
#
# Lifecycle hooks (optional, defined in agent or defaulted from agent-base.sh):
#   - agent_on_init(worker_dir, project_dir)   - Before PID file creation
#   - agent_on_ready(worker_dir, project_dir)  - After init, before agent_run
#   - agent_on_error(worker_dir, exit_code, error_type) - On validation/prereq failure
#   - agent_on_signal(signal)                  - On INT/TERM before cleanup
#
# Two invocation modes:
#   - run_agent()     - Full lifecycle (PID, signals, violation monitor) for top-level agents
#   - run_sub_agent() - Execution only, for nested agents (no lifecycle management)

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/exit-codes.sh"
source "$WIGGUM_HOME/lib/core/agent-base.sh"
source "$WIGGUM_HOME/lib/worker/agent-runner.sh"

# Track currently loaded agent to prevent re-sourcing
_LOADED_AGENT=""

# Global state for agent lifecycle
_AGENT_REGISTRY_IS_TOP_LEVEL=false
_AGENT_REGISTRY_PROJECT_DIR=""
_AGENT_REGISTRY_WORKER_DIR=""

# Load an agent by type
#
# Args:
#   agent_type - The agent type name (e.g., "task-worker")
#
# Returns: 0 on success, 1 if agent not found
load_agent() {
    local agent_type="$1"
    local agent_file="$WIGGUM_HOME/lib/agents/${agent_type}.sh"

    if [ ! -f "$agent_file" ]; then
        log_error "Unknown agent type: $agent_type"
        log_error "Available agents: $(list_agents | tr '\n' ' ')"
        return 1
    fi

    # Clear previous agent functions to avoid conflicts
    if [ -n "$_LOADED_AGENT" ] && [ "$_LOADED_AGENT" != "$agent_type" ]; then
        unset -f agent_required_paths agent_run agent_cleanup 2>/dev/null || true
    fi

    # shellcheck source=/dev/null
    source "$agent_file"
    _LOADED_AGENT="$agent_type"

    # Verify required functions exist
    if ! type agent_required_paths &>/dev/null; then
        log_error "Agent $agent_type missing required function: agent_required_paths"
        return 1
    fi

    if ! type agent_run &>/dev/null; then
        log_error "Agent $agent_type missing required function: agent_run"
        return 1
    fi

    # Check for optional agent_output_files function
    if type agent_output_files &>/dev/null; then
        log_debug "Agent $agent_type defines output files"
    else
        log_debug "Agent $agent_type has no agent_output_files (outputs not validated)"
    fi

    log_debug "Loaded agent: $agent_type"
    return 0
}

# Validate agent prerequisites before running
#
# Args:
#   worker_dir - The worker directory containing required paths
#
# Returns: 0 if all prerequisites exist, 1 otherwise
validate_agent_prerequisites() {
    local worker_dir="$1"

    if ! type agent_required_paths &>/dev/null; then
        log_error "No agent loaded - call load_agent first"
        return 1
    fi

    local paths
    paths=$(agent_required_paths)

    local missing=0
    for path in $paths; do
        local full_path="$worker_dir/$path"
        if [ ! -e "$full_path" ]; then
            log_error "Agent prerequisite missing: $full_path"
            missing=1
        fi
    done

    return $missing
}

# Validate agent output files after running
#
# Args:
#   worker_dir - The worker directory containing output files
#
# Returns: 0 if all output files exist and are non-empty, 1 otherwise
validate_agent_outputs() {
    local worker_dir="$1"

    # If agent doesn't define output files, skip validation
    if ! type agent_output_files &>/dev/null; then
        log_debug "No agent_output_files defined - skipping output validation"
        return 0
    fi

    local files
    files=$(agent_output_files)

    local missing=0
    for file in $files; do
        local full_path="$worker_dir/$file"
        if [ ! -f "$full_path" ]; then
            log_error "Agent output file missing: $full_path"
            missing=1
        elif [ ! -s "$full_path" ]; then
            log_error "Agent output file is empty: $full_path"
            missing=1
        fi
    done

    if [ $missing -eq 0 ]; then
        log_debug "All agent output files validated successfully"
    fi

    return $missing
}

# Run a top-level agent with full lifecycle management
#
# This is for top-level agents that need:
# - PID file recording
# - Signal handlers for graceful shutdown
# - Violation monitoring
#
# Args:
#   agent_type       - The agent type to run
#   worker_dir       - Worker directory
#   project_dir      - Project root directory
#   monitor_interval - Violation monitor interval in seconds (default: 30, 0 to disable)
#   ...              - Additional args passed to agent_run
#
# Returns: Exit code from agent_run
run_agent() {
    local agent_type="$1"
    local worker_dir="$2"
    local project_dir="$3"
    local monitor_interval="${4:-30}"
    shift 4 2>/dev/null || shift 3

    log "Running top-level agent: $agent_type"

    # Store globals for sub-agents to inherit
    _AGENT_REGISTRY_IS_TOP_LEVEL=true
    _AGENT_REGISTRY_PROJECT_DIR="$project_dir"
    _AGENT_REGISTRY_WORKER_DIR="$worker_dir"

    # Load agent first (needed for hooks)
    if ! load_agent "$agent_type"; then
        return 1
    fi

    # Load agent configuration
    load_agent_config "$agent_type"

    # Call on_init hook before PID file creation
    if type agent_on_init &>/dev/null; then
        log_debug "Calling agent_on_init hook"
        if ! agent_on_init "$worker_dir" "$project_dir"; then
            log_error "agent_on_init hook failed"
            if type agent_on_error &>/dev/null; then
                agent_on_error "$worker_dir" "$EXIT_AGENT_INIT_FAILED" "init"
            fi
            return "$EXIT_AGENT_INIT_FAILED"
        fi
    fi

    # Initialize agent lifecycle (PID, signals, violation monitor)
    if ! agent_runner_init "$worker_dir" "$project_dir" "$monitor_interval"; then
        log_error "Failed to initialize agent lifecycle"
        if type agent_on_error &>/dev/null; then
            agent_on_error "$worker_dir" "$EXIT_AGENT_INIT_FAILED" "init"
        fi
        return "$EXIT_AGENT_INIT_FAILED"
    fi

    # Setup cleanup on exit with signal handling
    trap '_agent_registry_handle_signal INT' INT
    trap '_agent_registry_handle_signal TERM' TERM
    trap '_agent_registry_cleanup' EXIT

    # Validate prerequisites
    if ! validate_agent_prerequisites "$worker_dir"; then
        log_error "Agent prerequisites not met"
        if type agent_on_error &>/dev/null; then
            agent_on_error "$worker_dir" "$EXIT_AGENT_PREREQ_FAILED" "prereq"
        fi
        return "$EXIT_AGENT_PREREQ_FAILED"
    fi

    # Call on_ready hook before agent_run
    if type agent_on_ready &>/dev/null; then
        log_debug "Calling agent_on_ready hook"
        if ! agent_on_ready "$worker_dir" "$project_dir"; then
            log_error "agent_on_ready hook failed"
            if type agent_on_error &>/dev/null; then
                agent_on_error "$worker_dir" "$EXIT_AGENT_READY_FAILED" "ready"
            fi
            return "$EXIT_AGENT_READY_FAILED"
        fi
    fi

    # Run the agent
    agent_run "$worker_dir" "$project_dir" "$@"
    local exit_code=$?

    # Validate output files exist and are non-empty
    if ! validate_agent_outputs "$worker_dir"; then
        log_error "Agent output validation failed"
        if type agent_on_error &>/dev/null; then
            agent_on_error "$worker_dir" "$EXIT_AGENT_OUTPUT_MISSING" "output"
        fi
        if [ $exit_code -eq 0 ]; then
            exit_code="$EXIT_AGENT_OUTPUT_MISSING"
        fi
    fi

    # Call agent-specific cleanup if defined
    if type agent_cleanup &>/dev/null; then
        log_debug "Running agent cleanup"
        agent_cleanup "$worker_dir" "$exit_code"
    fi

    log "Agent $agent_type completed with exit code: $exit_code"
    return $exit_code
}

# Internal cleanup function called on exit
_agent_registry_cleanup() {
    if [ "$_AGENT_REGISTRY_IS_TOP_LEVEL" = true ]; then
        agent_runner_cleanup
        _AGENT_REGISTRY_IS_TOP_LEVEL=false
        _AGENT_REGISTRY_PROJECT_DIR=""
        _AGENT_REGISTRY_WORKER_DIR=""
    fi
}

# Internal signal handler
_agent_registry_handle_signal() {
    local signal="$1"
    log_debug "Received signal: $signal"

    # Call agent's signal hook if defined
    if type agent_on_signal &>/dev/null; then
        agent_on_signal "$signal"
    fi

    # Re-raise the signal after hook completes
    # This allows the EXIT trap to still fire
    trap - "$signal"
    kill -s "$signal" $$
}

# Run a nested sub-agent without lifecycle management
#
# This is for agents that are spawned by other agents (nested execution).
# Sub-agents inherit the lifecycle from their parent:
# - No PID file (parent owns the PID)
# - No signal handlers (signals propagate naturally)
# - No violation monitor (parent's monitor covers the workspace)
#
# Args:
#   agent_type  - The agent type to run
#   worker_dir  - Worker directory (optional, inherits from parent if not specified)
#   project_dir - Project root directory (optional, inherits from parent if not specified)
#   ...         - Additional args passed to agent_run
#
# Returns: Exit code from agent_run
run_sub_agent() {
    local agent_type="$1"
    local worker_dir="${2:-$_AGENT_REGISTRY_WORKER_DIR}"
    local project_dir="${3:-$_AGENT_REGISTRY_PROJECT_DIR}"
    shift 3 2>/dev/null || shift 1

    log "Running sub-agent: $agent_type"

    # Validate we have required directories
    if [ -z "$worker_dir" ] || [ -z "$project_dir" ]; then
        log_error "run_sub_agent: worker_dir and project_dir required (not inherited from parent)"
        return 1
    fi

    # Load agent
    if ! load_agent "$agent_type"; then
        return 1
    fi

    # Load agent configuration
    load_agent_config "$agent_type"

    # Call on_init hook (lighter-weight for sub-agents)
    if type agent_on_init &>/dev/null; then
        log_debug "Calling sub-agent agent_on_init hook"
        if ! agent_on_init "$worker_dir" "$project_dir"; then
            log_error "Sub-agent agent_on_init hook failed"
            if type agent_on_error &>/dev/null; then
                agent_on_error "$worker_dir" "$EXIT_AGENT_INIT_FAILED" "init"
            fi
            return "$EXIT_AGENT_INIT_FAILED"
        fi
    fi

    # Validate prerequisites
    if ! validate_agent_prerequisites "$worker_dir"; then
        log_error "Agent prerequisites not met"
        if type agent_on_error &>/dev/null; then
            agent_on_error "$worker_dir" "$EXIT_AGENT_PREREQ_FAILED" "prereq"
        fi
        return "$EXIT_AGENT_PREREQ_FAILED"
    fi

    # Call on_ready hook before agent_run
    if type agent_on_ready &>/dev/null; then
        log_debug "Calling sub-agent agent_on_ready hook"
        if ! agent_on_ready "$worker_dir" "$project_dir"; then
            log_error "Sub-agent agent_on_ready hook failed"
            if type agent_on_error &>/dev/null; then
                agent_on_error "$worker_dir" "$EXIT_AGENT_READY_FAILED" "ready"
            fi
            return "$EXIT_AGENT_READY_FAILED"
        fi
    fi

    # Run the agent (no lifecycle management)
    agent_run "$worker_dir" "$project_dir" "$@"
    local exit_code=$?

    # Validate output files exist and are non-empty
    if ! validate_agent_outputs "$worker_dir"; then
        log_error "Sub-agent output validation failed"
        if type agent_on_error &>/dev/null; then
            agent_on_error "$worker_dir" "$EXIT_AGENT_OUTPUT_MISSING" "output"
        fi
        if [ $exit_code -eq 0 ]; then
            exit_code="$EXIT_AGENT_OUTPUT_MISSING"
        fi
    fi

    # Call agent-specific cleanup if defined
    if type agent_cleanup &>/dev/null; then
        log_debug "Running agent cleanup"
        agent_cleanup "$worker_dir" "$exit_code"
    fi

    log "Sub-agent $agent_type completed with exit code: $exit_code"
    return $exit_code
}

# List available agents
#
# Returns: List of agent names (one per line)
list_agents() {
    local agents_dir="$WIGGUM_HOME/lib/agents"

    if [ ! -d "$agents_dir" ]; then
        return 0
    fi

    for f in "$agents_dir"/*.sh; do
        if [ -f "$f" ]; then
            basename "$f" .sh
        fi
    done
}

# Get information about an agent
#
# Args:
#   agent_type - The agent type
#
# Returns: Agent info (type, required paths, output files)
get_agent_info() {
    local agent_type="$1"

    if ! load_agent "$agent_type"; then
        return 1
    fi

    echo "Agent: $agent_type"
    echo "Required paths:"
    agent_required_paths | while read -r path; do
        echo "  - $path"
    done

    echo "Output files:"
    if type agent_output_files &>/dev/null; then
        agent_output_files | while read -r file; do
            echo "  - $file"
        done
    else
        echo "  (none defined)"
    fi

    if type agent_cleanup &>/dev/null; then
        echo "Has cleanup: yes"
    else
        echo "Has cleanup: no"
    fi
}
