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
set -euo pipefail

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/exit-codes.sh"
source "$WIGGUM_HOME/lib/core/agent-base.sh"
source "$WIGGUM_HOME/lib/worker/agent-runner.sh"
source "$WIGGUM_HOME/lib/git/git-operations.sh"

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
        agent_file="$WIGGUM_HOME/lib/agents/pipeline/${agent_type}.sh"
    fi

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
# For agents with agent_output_files() defined (legacy), checks those specific files.
# Otherwise, verifies that agent_find_latest_result returns a valid parseable JSON file.
#
# Args:
#   worker_dir - The worker directory containing output files
#
# Returns: 0 if validation passes, 1 otherwise
validate_agent_outputs() {
    local worker_dir="$1"

    # If agent defines legacy output files, validate those
    if type agent_output_files &>/dev/null; then
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
    fi

    # Default: check for valid epoch-named result JSON
    local agent_type="${AGENT_TYPE:-unknown}"
    local result_file
    result_file=$(agent_find_latest_result "$worker_dir" "$agent_type")

    if [ -z "$result_file" ] || [ ! -f "$result_file" ]; then
        log_debug "No epoch-named result file found for $agent_type - skipping output validation"
        return 0
    fi

    if ! jq '.' "$result_file" > /dev/null 2>&1; then
        log_error "Agent result file is not valid JSON: $result_file"
        return 1
    fi

    log_debug "Agent result file validated: $(basename "$result_file")"
    return 0
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
#   max_iterations   - Maximum outer loop iterations (default: 20)
#   max_turns        - Maximum turns per Claude session (default: 50)
#   ...              - Additional args passed to agent_run
#
# Returns: Exit code from agent_run
run_agent() {
    local agent_type="$1"
    local worker_dir="$2"
    local project_dir="$3"
    local monitor_interval="${4:-30}"
    local max_iterations="${5:-20}"
    local max_turns="${6:-50}"
    shift 6 2>/dev/null || shift 4 2>/dev/null || shift 3

    log "Running top-level agent: $agent_type"

    # Store globals for sub-agents to inherit
    _AGENT_REGISTRY_IS_TOP_LEVEL=true
    _AGENT_REGISTRY_PROJECT_DIR="$project_dir"
    _AGENT_REGISTRY_WORKER_DIR="$worker_dir"

    # Export log directory so all Claude primitives know where to write logs
    export WIGGUM_LOG_DIR="$worker_dir/logs"

    # Export agent type for violation monitor
    # Task-worker is exempt from destructive git command restrictions
    export WIGGUM_CURRENT_AGENT_TYPE="$agent_type"

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
    agent_run "$worker_dir" "$project_dir" "$max_iterations" "$max_turns" "$@"
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
        unset WIGGUM_CURRENT_AGENT_TYPE
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

    # Save parent agent type to restore after sub-agent completes
    local parent_agent_type="${WIGGUM_CURRENT_AGENT_TYPE:-}"

    # Export agent type for violation monitor to detect destructive git commands
    # Sub-agents are blocked from destructive git operations; task-worker is exempt
    export WIGGUM_CURRENT_AGENT_TYPE="$agent_type"

    # Validate we have required directories
    if [ -z "$worker_dir" ] || [ -z "$project_dir" ]; then
        log_error "run_sub_agent: worker_dir and project_dir required (not inherited from parent)"
        # Restore parent agent type before returning
        export WIGGUM_CURRENT_AGENT_TYPE="$parent_agent_type"
        return 1
    fi

    # Ensure log directory is set for Claude primitives
    export WIGGUM_LOG_DIR="$worker_dir/logs"

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

    # For read-only agents, create a git checkpoint before running
    # This allows us to discard any accidental changes after the agent exits
    local workspace="$worker_dir/workspace"
    local git_checkpoint=""
    if git_is_readonly_agent "$agent_type" && [ -d "$workspace" ]; then
        log_debug "Creating git safety checkpoint for read-only agent: $agent_type"
        if git_safety_checkpoint "$workspace"; then
            git_checkpoint="$GIT_SAFETY_CHECKPOINT_SHA"
        else
            log_warn "Failed to create git checkpoint, proceeding without safety net"
        fi
    fi

    # Run the agent (no lifecycle management)
    agent_run "$worker_dir" "$project_dir" "$@"
    local exit_code=$?

    # For read-only agents, restore to checkpoint (discard any changes)
    if [ -n "$git_checkpoint" ] && [ -d "$workspace" ]; then
        log_debug "Restoring git safety checkpoint for read-only agent: $agent_type"
        git_safety_restore "$workspace" "$git_checkpoint"
    fi

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

    # Restore parent agent type for violation monitor
    export WIGGUM_CURRENT_AGENT_TYPE="$parent_agent_type"

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
    for f in "$agents_dir"/pipeline/*.sh; do
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
