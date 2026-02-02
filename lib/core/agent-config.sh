#!/usr/bin/env bash
# =============================================================================
# agent-config.sh - Agent configuration loading and result mappings
#
# Provides:
#   - Agent configuration loading (load_agent_config)
#   - Result mappings (config-driven gate results)
#   - Pipeline config access
#
# Split from agent-base.sh for maintainability.
# =============================================================================
set -euo pipefail

[ -n "${_AGENT_CONFIG_LOADED:-}" ] && return 0
_AGENT_CONFIG_LOADED=1

# =============================================================================
# AGENT CONFIGURATION
# =============================================================================

# Load agent-specific configuration from config/agents.json
#
# Args:
#   agent_type - The agent type to load config for
#
# Sets global variables based on config (with env var overrides):
#   AGENT_CONFIG_MAX_ITERATIONS
#   AGENT_CONFIG_MAX_TURNS
#   AGENT_CONFIG_TIMEOUT_SECONDS
#   AGENT_CONFIG_AUTO_COMMIT
#   AGENT_CONFIG_SUPERVISOR_INTERVAL
#   AGENT_CONFIG_MAX_RESTARTS
load_agent_config() {
    local agent_type="$1"
    local config_file="$WIGGUM_HOME/config/agents.json"

    # Initialize with defaults
    AGENT_CONFIG_MAX_ITERATIONS=10
    AGENT_CONFIG_MAX_TURNS=30
    AGENT_CONFIG_TIMEOUT_SECONDS=3600
    AGENT_CONFIG_AUTO_COMMIT=false
    AGENT_CONFIG_SUPERVISOR_INTERVAL=2
    AGENT_CONFIG_MAX_RESTARTS=2

    # Load from config file if it exists
    if [ -f "$config_file" ]; then
        # Load agent-specific config, falling back to defaults
        local agent_config default_config

        # Get defaults section (single jq call for all values)
        default_config=$(jq -r '.defaults // {}' "$config_file" 2>/dev/null)
        if [ -n "$default_config" ] && [ "$default_config" != "null" ]; then
            read -r AGENT_CONFIG_MAX_ITERATIONS AGENT_CONFIG_MAX_TURNS AGENT_CONFIG_TIMEOUT_SECONDS \
                    AGENT_CONFIG_AUTO_COMMIT AGENT_CONFIG_SUPERVISOR_INTERVAL AGENT_CONFIG_MAX_RESTARTS \
                < <(echo "$default_config" | jq -r '[
                    .max_iterations // 10,
                    .max_turns // 30,
                    .timeout_seconds // 3600,
                    .auto_commit // false,
                    .supervisor_interval // 2,
                    .max_restarts // 2
                ] | @tsv')
        fi

        # Override with agent-specific config
        # Note: We read each field individually to avoid TSV parsing issues where
        # bash's read collapses consecutive delimiters (empty fields)
        agent_config=$(jq -r ".agents.\"$agent_type\" // {}" "$config_file" 2>/dev/null)
        if [ -n "$agent_config" ] && [ "$agent_config" != "null" ] && [ "$agent_config" != "{}" ]; then
            local v
            v=$(echo "$agent_config" | jq -r '.max_iterations // empty') && [ -n "$v" ] && AGENT_CONFIG_MAX_ITERATIONS="$v"
            v=$(echo "$agent_config" | jq -r '.max_turns // empty') && [ -n "$v" ] && AGENT_CONFIG_MAX_TURNS="$v"
            v=$(echo "$agent_config" | jq -r '.timeout_seconds // empty') && [ -n "$v" ] && AGENT_CONFIG_TIMEOUT_SECONDS="$v"
            v=$(echo "$agent_config" | jq -r '.auto_commit // empty') && [ -n "$v" ] && AGENT_CONFIG_AUTO_COMMIT="$v"
            v=$(echo "$agent_config" | jq -r '.supervisor_interval // empty') && [ -n "$v" ] && AGENT_CONFIG_SUPERVISOR_INTERVAL="$v"
            v=$(echo "$agent_config" | jq -r '.max_restarts // empty') && [ -n "$v" ] && AGENT_CONFIG_MAX_RESTARTS="$v"
        fi
    fi

    # Export for use by agent
    export AGENT_CONFIG_MAX_ITERATIONS
    export AGENT_CONFIG_MAX_TURNS
    export AGENT_CONFIG_TIMEOUT_SECONDS
    export AGENT_CONFIG_AUTO_COMMIT
    export AGENT_CONFIG_SUPERVISOR_INTERVAL
    export AGENT_CONFIG_MAX_RESTARTS
}

# =============================================================================
# RESULT MAPPINGS (Config-Driven Gate Results)
# =============================================================================
# Result mappings define the status, exit_code, and default_jump for each
# gate result value. This allows custom results beyond the built-in PASS/FAIL/FIX/SKIP.
#
# Resolution order (per-agent):
#   1. Per-agent result_mappings in config/agents.json (highest priority)
#   2. defaults.result_mappings in config/agents.json (lowest priority)
#
# Can be overridden per-pipeline in pipeline.json "result_mappings" (handled by pipeline-loader).

# Global associative arrays for result mappings (loaded once per agent)
declare -gA _RESULT_STATUS=()
declare -gA _RESULT_EXIT_CODE=()
declare -gA _RESULT_DEFAULT_JUMP=()
_RESULT_MAPPINGS_LOADED=""
_RESULT_MAPPINGS_AGENT=""

# Load result mappings from config/agents.json
#
# Resolution order:
#   1. Per-agent result_mappings (from AGENT_TYPE)
#   2. defaults.result_mappings
#
# Populates:
#   _RESULT_STATUS[result]       - Status string (success, failure, partial, unknown)
#   _RESULT_EXIT_CODE[result]    - Exit code (integer)
#   _RESULT_DEFAULT_JUMP[result] - Default jump target (next, prev, abort, self, or step ID)
#
# Sets: _RESULT_MAPPINGS_LOADED=1 when complete
load_result_mappings() {
    local agent_type="${AGENT_TYPE:-}"

    # Return early if already loaded for this agent
    if [ -n "$_RESULT_MAPPINGS_LOADED" ] && [ "$_RESULT_MAPPINGS_AGENT" = "$agent_type" ]; then
        return 0
    fi

    local config_file="$WIGGUM_HOME/config/agents.json"

    # Initialize with hardcoded defaults in case config is missing
    _RESULT_STATUS=([PASS]="success" [FAIL]="failure" [FIX]="partial" [SKIP]="success" [UNKNOWN]="failure")
    _RESULT_EXIT_CODE=([PASS]=0 [FAIL]=10 [FIX]=0 [SKIP]=0 [UNKNOWN]=1)
    _RESULT_DEFAULT_JUMP=([PASS]="next" [FAIL]="abort" [FIX]="prev" [SKIP]="next" [UNKNOWN]="abort")

    if [ -f "$config_file" ]; then
        # Helper function to load mappings from a JSON object
        _load_mappings_from_json() {
            local mappings_json="$1"
            if [ -n "$mappings_json" ] && [ "$mappings_json" != "{}" ] && [ "$mappings_json" != "null" ]; then
                local result_keys
                result_keys=$(echo "$mappings_json" | jq -r 'keys[]' 2>/dev/null)

                while IFS= read -r result; do
                    [ -z "$result" ] && continue
                    local status exit_code default_jump
                    status=$(echo "$mappings_json" | jq -r ".\"$result\".status // \"unknown\"")
                    exit_code=$(echo "$mappings_json" | jq -r ".\"$result\".exit_code // 1")
                    default_jump=$(echo "$mappings_json" | jq -r ".\"$result\".default_jump // \"next\"")

                    _RESULT_STATUS[$result]="$status"
                    _RESULT_EXIT_CODE[$result]="$exit_code"
                    _RESULT_DEFAULT_JUMP[$result]="$default_jump"
                done <<< "$result_keys"
            fi
        }

        # 1. Load defaults.result_mappings first (base layer)
        local defaults_json
        defaults_json=$(jq -c '.defaults.result_mappings // {}' "$config_file" 2>/dev/null)
        _load_mappings_from_json "$defaults_json"

        # 2. Override with per-agent result_mappings (if agent type is set)
        if [ -n "$agent_type" ]; then
            local agent_json
            agent_json=$(jq -c ".agents.\"$agent_type\".result_mappings // {}" "$config_file" 2>/dev/null)
            _load_mappings_from_json "$agent_json"
        fi
    fi

    _RESULT_MAPPINGS_LOADED=1
    _RESULT_MAPPINGS_AGENT="$agent_type"
}

# Get the status string for a gate result
#
# Args:
#   gate_result - The gate result value (e.g., PASS, FAIL, FIX)
#
# Returns: Status string (success, failure, partial, unknown)
get_result_status() {
    local gate_result="$1"
    [ -z "$_RESULT_MAPPINGS_LOADED" ] && load_result_mappings
    echo "${_RESULT_STATUS[$gate_result]:-unknown}"
}

# Get the exit code for a gate result
#
# Args:
#   gate_result - The gate result value (e.g., PASS, FAIL, FIX)
#
# Returns: Exit code (integer)
get_result_exit_code() {
    local gate_result="$1"
    [ -z "$_RESULT_MAPPINGS_LOADED" ] && load_result_mappings
    echo "${_RESULT_EXIT_CODE[$gate_result]:-1}"
}

# Get the default jump target for a gate result
#
# Args:
#   gate_result - The gate result value (e.g., PASS, FAIL, FIX)
#
# Returns: Jump target (next, prev, abort, self, or step ID), empty if unknown
get_result_default_jump() {
    local gate_result="$1"
    [ -z "$_RESULT_MAPPINGS_LOADED" ] && load_result_mappings
    echo "${_RESULT_DEFAULT_JUMP[$gate_result]:-}"
}

# Check if a gate result is defined in the mappings
#
# Args:
#   gate_result - The gate result value to check
#
# Returns: 0 if defined, 1 if not
is_result_defined() {
    local gate_result="$1"
    [ -z "$_RESULT_MAPPINGS_LOADED" ] && load_result_mappings
    [ -n "${_RESULT_DEFAULT_JUMP[$gate_result]:-}" ]
}

# =============================================================================
# PIPELINE CONFIG ACCESS
# =============================================================================

# Read the full pipeline-config.json from worker directory
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: Full JSON content of pipeline-config.json, or "{}" if not found
agent_read_pipeline_config() {
    local worker_dir="$1"
    local config_file="$worker_dir/pipeline-config.json"

    if [ -f "$config_file" ]; then
        cat "$config_file"
    else
        echo "{}"
    fi
}

# Get config for the current step from pipeline-config.json
#
# Args:
#   worker_dir - Worker directory path
#   step_id    - Optional step ID (defaults to WIGGUM_STEP_ID)
#
# Returns: JSON config object for the step, or "{}" if not found
agent_get_step_config() {
    local worker_dir="$1"
    local step_id="${2:-${WIGGUM_STEP_ID:-}}"

    if [ -z "$step_id" ]; then
        echo "{}"
        return 0
    fi

    local config_file="$worker_dir/pipeline-config.json"
    if [ -f "$config_file" ]; then
        jq -r --arg id "$step_id" '.steps[$id].config // {}' "$config_file" 2>/dev/null || echo "{}"
    else
        echo "{}"
    fi
}

# Get runtime context from pipeline-config.json
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: JSON runtime object containing plan_file, resume_instructions, etc.
agent_get_runtime_config() {
    local worker_dir="$1"
    local config_file="$worker_dir/pipeline-config.json"

    if [ -f "$config_file" ]; then
        jq -r '.runtime // {}' "$config_file" 2>/dev/null || echo "{}"
    else
        echo "{}"
    fi
}

# Read step config from pipeline-config.json
# DEPRECATED: Use agent_get_step_config instead
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: JSON content of step config, or "{}" if not found
agent_read_step_config() {
    local worker_dir="$1"
    agent_get_step_config "$worker_dir"
}
