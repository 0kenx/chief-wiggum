#!/usr/bin/env bash
# =============================================================================
# service-loader.sh - Load and query service JSON on-demand via jq
#
# Provides:
#   service_load(file)                - Load and validate service configuration
#   service_load_override(file)       - Merge project-level service overrides
#   service_get_enabled()             - List enabled services
#   service_get_by_id(id)             - Get service definition as JSON
#   service_get_schedule(id)          - Get schedule config for a service
#   service_get_execution(id)         - Get execution config for a service
#   service_get_field(id, field, default) - Get a specific field from a service
#   service_count()                   - Return number of services
# =============================================================================

# Prevent double-sourcing
[ -n "${_SERVICE_LOADER_LOADED:-}" ] && return 0
_SERVICE_LOADER_LOADED=1

# Service state
_SERVICE_JSON_FILE=""        # Path to loaded JSON file
_SERVICE_JSON=""             # Merged JSON string (after overrides)
_SERVICE_COUNT=0
_SERVICE_VERSION=""

# Internal: run jq against the service source
#
# Usage: _service_jq [jq-options...] filter
# Filter must be the LAST argument
_service_jq() {
    # Extract all arguments
    local args=("$@")
    local num_args=${#args[@]}

    # Filter is the last argument
    local filter="${args[$((num_args - 1))]}"

    # All other arguments are jq options
    local jq_opts=()
    for ((i = 0; i < num_args - 1; i++)); do
        jq_opts+=("${args[$i]}")
    done

    if [ -n "$_SERVICE_JSON" ]; then
        echo "$_SERVICE_JSON" | jq "${jq_opts[@]}" "$filter"
    elif [ -n "$_SERVICE_JSON_FILE" ]; then
        jq "${jq_opts[@]}" "$filter" "$_SERVICE_JSON_FILE"
    else
        echo "null"
    fi
}

# Load service configuration from a JSON file
#
# Validates JSON structure and required fields.
#
# Args:
#   file - Path to services JSON file
#
# Returns: 0 on success, 1 on error
service_load() {
    local file="$1"

    if [ ! -f "$file" ]; then
        log_error "Service config not found: $file"
        return 1
    fi

    # Validate JSON
    if ! jq empty "$file" 2>/dev/null; then
        log_error "Invalid JSON in service config: $file"
        return 1
    fi

    # Read version
    _SERVICE_VERSION=$(jq -r '.version // "1.0"' "$file")

    # Get service count
    local service_count
    service_count=$(jq '.services | length' "$file")

    if [ "$service_count" -eq 0 ]; then
        log_error "Service config has no services: $file"
        return 1
    fi

    # Validate unique IDs
    local dup_check
    dup_check=$(jq -r '[.services[].id] | group_by(.) | map(select(length > 1)) | .[0][0] // empty' "$file")
    if [ -n "$dup_check" ]; then
        log_error "Duplicate service ID: $dup_check"
        return 1
    fi

    # Validate all services have required fields
    local missing_id
    missing_id=$(jq -r '.services | to_entries[] | select(.value.id == null or .value.id == "") | .key' "$file" | head -1)
    if [ -n "$missing_id" ]; then
        log_error "Service missing required 'id' field (index $missing_id)"
        return 1
    fi

    # Validate schedule config exists
    local missing_schedule
    missing_schedule=$(jq -r '.services | to_entries[] | select(.value.schedule == null) | .value.id // .key' "$file" | head -1)
    if [ -n "$missing_schedule" ]; then
        log_error "Service '$missing_schedule' missing required 'schedule' field"
        return 1
    fi

    # Validate execution config exists
    local missing_execution
    missing_execution=$(jq -r '.services | to_entries[] | select(.value.execution == null) | .value.id // .key' "$file" | head -1)
    if [ -n "$missing_execution" ]; then
        log_error "Service '$missing_execution' missing required 'execution' field"
        return 1
    fi

    # Validate schedule types
    local bad_schedule
    bad_schedule=$(jq -r '.services[] | select(.schedule.type | . != "interval" and . != "event" and . != "continuous") | .id' "$file" | head -1)
    if [ -n "$bad_schedule" ]; then
        local sched_type
        sched_type=$(jq -r --arg id "$bad_schedule" '.services[] | select(.id == $id) | .schedule.type' "$file")
        log_error "Service '$bad_schedule' has invalid schedule type: '$sched_type' (must be interval, event, or continuous)"
        return 1
    fi

    # Validate execution types
    local bad_execution
    bad_execution=$(jq -r '.services[] | select(.execution.type | . != "command" and . != "function" and . != "pipeline") | .id' "$file" | head -1)
    if [ -n "$bad_execution" ]; then
        local exec_type
        exec_type=$(jq -r --arg id "$bad_execution" '.services[] | select(.id == $id) | .execution.type' "$file")
        log_error "Service '$bad_execution' has invalid execution type: '$exec_type' (must be command, function, or pipeline)"
        return 1
    fi

    # Store source
    _SERVICE_JSON_FILE="$file"
    _SERVICE_JSON=""
    _SERVICE_COUNT="$service_count"

    log "Loaded service config with $service_count services"
    return 0
}

# Load and merge project-level service overrides
#
# Overrides are merged into the base configuration:
# - Services with matching IDs are replaced
# - New services are added
# - Services can be disabled by setting enabled: false
#
# Args:
#   file - Path to override services JSON file
#
# Returns: 0 on success, 1 on error
service_load_override() {
    local file="$1"

    if [ ! -f "$file" ]; then
        log_debug "No service override file: $file"
        return 0
    fi

    # Validate JSON
    if ! jq empty "$file" 2>/dev/null; then
        log_error "Invalid JSON in service override: $file"
        return 1
    fi

    # Merge the configurations
    # Override services replace base services with same ID
    # This requires reading the base config first
    local base_json
    if [ -n "$_SERVICE_JSON" ]; then
        base_json="$_SERVICE_JSON"
    elif [ -n "$_SERVICE_JSON_FILE" ]; then
        base_json=$(cat "$_SERVICE_JSON_FILE")
    else
        log_error "No base service config loaded"
        return 1
    fi

    local override_json
    override_json=$(cat "$file")

    # Merge: override services replace base by ID, new ones are added
    _SERVICE_JSON=$(jq -s '
        .[0] as $base | .[1] as $override |
        $base | .services = (
            # Get IDs from override
            ($override.services // []) | map(.id) as $override_ids |
            # Keep base services not in override
            ($base.services // [] | map(select(.id as $id | $override_ids | index($id) | not))) +
            # Add all override services
            ($override.services // [])
        ) |
        # Merge defaults if present
        .defaults = (($base.defaults // {}) * ($override.defaults // {}))
    ' <<< "$base_json"$'\n'"$override_json")

    # Update count (excluding disabled services)
    _SERVICE_COUNT=$(echo "$_SERVICE_JSON" | jq '[.services[] | select(.enabled != false)] | length')

    log "Merged service overrides from $file (now $_SERVICE_COUNT enabled services)"
    return 0
}

# Get list of enabled service IDs
#
# Returns: Space-separated list of service IDs via stdout
service_get_enabled() {
    _service_jq '[.services[] | select(.enabled != false) | .id] | .[]' -r
}

# Get a service definition by ID
#
# Args:
#   id - Service identifier
#
# Returns: Compact JSON of service definition via stdout
service_get_by_id() {
    local id="$1"
    _service_jq --arg id "$id" '.services[] | select(.id == $id)' -c
}

# Get schedule configuration for a service
#
# Args:
#   id - Service identifier
#
# Returns: Compact JSON of schedule config via stdout
service_get_schedule() {
    local id="$1"
    _service_jq --arg id "$id" '.services[] | select(.id == $id) | .schedule' -c
}

# Get execution configuration for a service
#
# Args:
#   id - Service identifier
#
# Returns: Compact JSON of execution config via stdout
service_get_execution() {
    local id="$1"
    _service_jq --arg id "$id" '.services[] | select(.id == $id) | .execution' -c
}

# Get a specific field from a service
#
# Args:
#   id      - Service identifier
#   field   - jq field path (e.g., ".schedule.interval", ".enabled")
#   default - Default value if field is null/missing (default: "")
#
# Returns: Field value via stdout
service_get_field() {
    local id="$1"
    local field="$2"
    local default="${3:-}"

    local result
    result=$(_service_jq --arg id "$id" '.services[] | select(.id == $id) | '"$field"' // null' -r)

    if [ "$result" = "null" ] || [ -z "$result" ]; then
        echo "$default"
    else
        echo "$result"
    fi
}

# Get the interval for an interval-type service
#
# Args:
#   id - Service identifier
#
# Returns: Interval in seconds (0 if not interval type)
service_get_interval() {
    local id="$1"
    local interval
    interval=$(service_get_field "$id" ".schedule.interval" "0")
    echo "$interval"
}

# Check if a service should run on startup
#
# Args:
#   id - Service identifier
#
# Returns: 0 if should run on startup, 1 otherwise
service_runs_on_startup() {
    local id="$1"
    local run_on_startup
    run_on_startup=$(service_get_field "$id" ".schedule.run_on_startup" "false")
    [ "$run_on_startup" = "true" ]
}

# Get concurrency config for a service
#
# Args:
#   id - Service identifier
#
# Returns: Compact JSON of concurrency config via stdout
service_get_concurrency() {
    local id="$1"
    _service_jq --arg id "$id" '.services[] | select(.id == $id) | .concurrency // {"max_instances": 1, "if_running": "skip"}' -c
}

# Get default timeout from config
#
# Returns: Default timeout in seconds
service_get_default_timeout() {
    _service_jq '.defaults.timeout // 300' -r
}

# Get timeout for a specific service
#
# Args:
#   id - Service identifier
#
# Returns: Timeout in seconds
service_get_timeout() {
    local id="$1"
    local default_timeout
    default_timeout=$(service_get_default_timeout)
    service_get_field "$id" ".timeout" "$default_timeout"
}

# Get the number of services
service_count() {
    echo "$_SERVICE_COUNT"
}

# Get service config version
service_version() {
    echo "$_SERVICE_VERSION"
}

# Check if a service exists
#
# Args:
#   id - Service identifier
#
# Returns: 0 if exists, 1 otherwise
service_exists() {
    local id="$1"
    local result
    result=$(_service_jq --arg id "$id" '.services[] | select(.id == $id) | .id' -r)
    [ -n "$result" ]
}

# Load built-in defaults (fallback when no config file exists)
service_load_builtin_defaults() {
    _SERVICE_VERSION="1.0"
    _SERVICE_JSON_FILE=""
    _SERVICE_JSON='{
  "version": "1.0",
  "defaults": {
    "timeout": 300,
    "restart_policy": { "on_failure": "skip", "max_retries": 2 }
  },
  "services": [
    {
      "id": "pr-sync",
      "schedule": { "type": "interval", "interval": 180, "run_on_startup": true },
      "execution": { "type": "command", "command": "wiggum-review sync" }
    },
    {
      "id": "pr-optimizer",
      "schedule": { "type": "interval", "interval": 900 },
      "execution": { "type": "function", "function": "pr_merge_spawn_background" },
      "concurrency": { "max_instances": 1, "if_running": "skip" }
    },
    {
      "id": "fix-workers",
      "schedule": { "type": "interval", "interval": 60 },
      "execution": { "type": "function", "function": "spawn_fix_workers" }
    },
    {
      "id": "resolve-workers",
      "schedule": { "type": "interval", "interval": 60 },
      "execution": { "type": "function", "function": "spawn_resolve_workers" }
    },
    {
      "id": "task-spawner",
      "schedule": { "type": "interval", "interval": 60 },
      "execution": { "type": "function", "function": "spawn_ready_tasks" }
    },
    {
      "id": "worker-cleanup",
      "schedule": { "type": "interval", "interval": 60 },
      "execution": { "type": "function", "function": "cleanup_all_workers" }
    },
    {
      "id": "scheduler-tick",
      "schedule": { "type": "interval", "interval": 60, "run_on_startup": true },
      "execution": { "type": "function", "function": "scheduler_tick" }
    }
  ]
}'
    _SERVICE_COUNT=7

    log "Loaded built-in default services with $_SERVICE_COUNT services"
}
