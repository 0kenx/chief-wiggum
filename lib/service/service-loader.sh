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
#
# New in v1.1:
#   service_get_dependencies(id)      - Get service dependencies
#   service_get_condition(id)         - Get conditional execution rules
#   service_get_health_check(id)      - Get health check config
#   service_get_limits(id)            - Get resource limits
#   service_get_circuit_breaker(id)   - Get circuit breaker config
#   service_get_groups(id)            - Get groups a service belongs to
#   service_get_services_in_group(group) - Get all services in a group
#   service_is_group_enabled(group)   - Check if a group is enabled
#   service_get_jitter(id)            - Get jitter for interval scheduling
#   service_get_backoff(id)           - Get backoff config for retries
# =============================================================================

# Prevent double-sourcing
[ -n "${_SERVICE_LOADER_LOADED:-}" ] && return 0
_SERVICE_LOADER_LOADED=1

# Service state
_SERVICE_JSON_FILE=""        # Path to loaded JSON file
_SERVICE_JSON=""             # Merged JSON string (after overrides)
_SERVICE_COUNT=0
_SERVICE_VERSION=""

# Service config cache (populated at load time, avoids per-tick jq calls)
# All service config is static after load/override — cache once, read forever.
declare -gA _SVC_CACHE=()       # Flat cache: "key_type:service_id" -> value
_SVC_CACHE_ENABLED=""            # Space-separated enabled service IDs (cached)
_SVC_CACHE_VALID=false           # Whether cache is populated

# Clear all cached service config (called on load/override)
_service_cache_clear() {
    _SVC_CACHE=()
    _SVC_CACHE_ENABLED=""
    _SVC_CACHE_VALID=false
}

# Populate service config cache with a single jq call
#
# Extracts all frequently-accessed fields for all enabled services into
# bash associative arrays. Reduces per-tick jq calls from ~300 to 0.
_service_populate_cache() {
    _service_cache_clear

    # Nothing to cache if no config loaded
    if [ -z "$_SERVICE_JSON" ] && [ -z "$_SERVICE_JSON_FILE" ]; then
        return
    fi

    # shellcheck disable=SC2034
    local -A phase_lists=()

    # Single jq call: extract all cacheable fields for all enabled services
    while IFS=$'\x1e' read -r id exec_type exec_func exec_cmd sched_type \
            sched_interval sched_jitter run_on_startup phase order timeout \
            cb_enabled cb_cooldown cb_half_open cb_threshold depends_on conc_max \
            conc_if_running conc_priority conc_queue_max cond_file_exists \
            cond_file_not_exists cond_env_set cond_command has_condition \
            sched_triggers exec_workspace; do
        [ -n "$id" ] || continue

        _SVC_CACHE_ENABLED+="${_SVC_CACHE_ENABLED:+ }${id}"
        phase_lists[$phase]+="${phase_lists[$phase]:+ }${id}"

        _SVC_CACHE["exec_type:${id}"]="$exec_type"
        _SVC_CACHE["exec_func:${id}"]="$exec_func"
        _SVC_CACHE["exec_cmd:${id}"]="$exec_cmd"
        _SVC_CACHE["field:${id}:.schedule.type"]="$sched_type"
        _SVC_CACHE["field:${id}:.schedule.interval"]="$sched_interval"
        _SVC_CACHE["field:${id}:.schedule.jitter"]="$sched_jitter"
        _SVC_CACHE["field:${id}:.schedule.run_on_startup"]="$run_on_startup"
        _SVC_CACHE["field:${id}:.phase"]="$phase"
        _SVC_CACHE["field:${id}:.order"]="$order"
        _SVC_CACHE["field:${id}:.timeout"]="$timeout"
        _SVC_CACHE["cb_enabled:${id}"]="$cb_enabled"
        _SVC_CACHE["cb_cooldown:${id}"]="$cb_cooldown"
        _SVC_CACHE["cb_half_open:${id}"]="$cb_half_open"
        _SVC_CACHE["cb_threshold:${id}"]="$cb_threshold"
        _SVC_CACHE["depends_on:${id}"]="$depends_on"
        _SVC_CACHE["conc_max:${id}"]="$conc_max"
        _SVC_CACHE["conc_if_running:${id}"]="$conc_if_running"
        _SVC_CACHE["conc_priority:${id}"]="$conc_priority"
        _SVC_CACHE["conc_queue_max:${id}"]="$conc_queue_max"
        _SVC_CACHE["has_condition:${id}"]="$has_condition"
        _SVC_CACHE["cond_fe:${id}"]="$cond_file_exists"
        _SVC_CACHE["cond_fne:${id}"]="$cond_file_not_exists"
        _SVC_CACHE["cond_es:${id}"]="$cond_env_set"
        _SVC_CACHE["cond_cmd:${id}"]="$cond_command"

        # Cache trigger patterns as newline-separated list for efficient iteration
        # Supports both single string trigger and JSON array triggers
        if [ -n "$sched_triggers" ]; then
            # Convert space-separated to newline-separated for cache
            _SVC_CACHE["triggers:${id}"]="${sched_triggers// /$'\n'}"
        fi

        # Cache workspace flag for execution
        _SVC_CACHE["exec_workspace:${id}"]="$exec_workspace"
    done < <(_service_jq -r '
        .groups as $groups |
        (.defaults.circuit_breaker.enabled // false) as $default_cb |
        (.defaults.timeout // 300) as $default_timeout |
        [.services[] |
            select(.enabled != false) |
            select(
                (.groups // []) as $svc_groups |
                ($svc_groups | length == 0) or
                ($svc_groups | map(. as $g | $groups[$g].enabled // true) | all)
            )
        ] | sort_by(.phase // "periodic", .order // 50) | .[] |
        [
            .id,
            (.execution.type // "function"),
            (.execution.function // ""),
            (.execution.command // ""),
            (.schedule.type // "interval"),
            (.schedule.interval // 0 | tostring),
            (.schedule.jitter // 0 | tostring),
            (.schedule.run_on_startup // false | tostring),
            (.phase // "periodic"),
            (.order // 50 | tostring),
            (.timeout // $default_timeout | tostring),
            ((.circuit_breaker.enabled // $default_cb) | tostring),
            (.circuit_breaker.cooldown // 300 | tostring),
            (.circuit_breaker.half_open_requests // 1 | tostring),
            (.circuit_breaker.threshold // 5 | tostring),
            (.depends_on // [] | map(tostring) | join(" ")),
            (.concurrency.max_instances // 1 | tostring),
            (.concurrency.if_running // "skip"),
            (.concurrency.priority // "normal"),
            (.concurrency.queue_max // 10 | tostring),
            (.condition.file_exists // ""),
            (.condition.file_not_exists // ""),
            (.condition.env_set // ""),
            (.condition.command // ""),
            (if .condition != null then "true" else "false" end),
            (if .schedule.trigger then
                (.schedule.trigger | if type == "array" then join(" ") else . end)
             else "" end),
            (.execution.workspace // false | tostring)
        ] | join("\u001e")
    ')

    for phase in "${!phase_lists[@]}"; do
        _SVC_CACHE["phase_ids:${phase}"]="${phase_lists[$phase]}"
    done

    _SVC_CACHE_VALID=true
}

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

    # Get service count (excluding disabled services)
    local service_count
    service_count=$(jq '[.services[] | select(.enabled != false)] | length' "$file")
    service_count="${service_count:-0}"

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

    # Store source for normalization (triggers may replace schedule)
    _SERVICE_JSON_FILE="$file"
    _SERVICE_JSON=""

    # Normalize triggers convenience field before validation
    # Services with `triggers` field get schedule auto-generated
    _normalize_service_triggers

    # After normalization, validate from the effective config (_SERVICE_JSON or file)
    # Use _service_jq to query the (possibly normalized) config
    local missing_schedule
    missing_schedule=$(_service_jq -r '.services | to_entries[] | select(.value.schedule == null and .value.triggers == null) | .value.id // .key' | head -1)
    if [ -n "$missing_schedule" ]; then
        log_error "Service '$missing_schedule' missing required 'schedule' field"
        return 1
    fi

    # Validate execution config exists
    local missing_execution
    missing_execution=$(_service_jq -r '.services | to_entries[] | select(.value.execution == null) | .value.id // .key' | head -1)
    if [ -n "$missing_execution" ]; then
        log_error "Service '$missing_execution' missing required 'execution' field"
        return 1
    fi

    # Validate schedule types (now includes cron)
    local bad_schedule
    bad_schedule=$(_service_jq -r '.services[] | select(.schedule.type | . != "interval" and . != "event" and . != "continuous" and . != "cron" and . != "tick") | .id' | head -1)
    if [ -n "$bad_schedule" ]; then
        local sched_type
        sched_type=$(_service_jq -r --arg id "$bad_schedule" '.services[] | select(.id == $id) | .schedule.type')
        log_error "Service '$bad_schedule' has invalid schedule type: '$sched_type' (must be interval, event, continuous, cron, or tick)"
        return 1
    fi

    # Validate execution types
    local bad_execution
    bad_execution=$(_service_jq -r '.services[] | select(.execution.type | . != "command" and . != "function" and . != "pipeline") | .id' | head -1)
    if [ -n "$bad_execution" ]; then
        local exec_type
        exec_type=$(_service_jq -r --arg id "$bad_execution" '.services[] | select(.id == $id) | .execution.type')
        log_error "Service '$bad_execution' has invalid execution type: '$exec_type' (must be command, function, or pipeline)"
        return 1
    fi

    # Validate dependencies reference existing services
    local bad_dep
    bad_dep=$(_service_jq -r '
        .services | map(.id) as $ids |
        .[] | select(.depends_on != null) |
        .id as $svc | .depends_on[] |
        select(. as $dep | $ids | index($dep) | not) |
        "\($svc) -> \(.)"
    ' | head -1)
    if [ -n "$bad_dep" ]; then
        log_error "Service has invalid dependency: $bad_dep"
        return 1
    fi

    # Recount after normalization (triggers may have changed services)
    service_count=$(_service_jq -r '[.services[] | select(.enabled != false)] | length')
    service_count="${service_count:-0}"
    _SERVICE_COUNT="$service_count"

    log "Loaded service config with $service_count services"
    _service_populate_cache
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
    # Also merge groups definitions
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
        .defaults = (($base.defaults // {}) * ($override.defaults // {})) |
        # Merge groups if present
        .groups = (($base.groups // {}) * ($override.groups // {}))
    ' <<< "$base_json"$'\n'"$override_json")

    # Clear file source since we're now using _SERVICE_JSON
    _SERVICE_JSON_FILE=""

    # Normalize triggers in overridden config
    _normalize_service_triggers

    # Update count (excluding disabled services and disabled groups)
    _SERVICE_COUNT=$(echo "$_SERVICE_JSON" | jq '
        .groups as $groups |
        [.services[] |
            select(.enabled != false) |
            select(
                (.groups // []) as $svc_groups |
                ($svc_groups | length == 0) or
                ($svc_groups | map(. as $g | $groups[$g].enabled // true) | all)
            )
        ] | length
    ')

    log "Merged service overrides from $file (now $_SERVICE_COUNT enabled services)"
    _service_populate_cache
    return 0
}

# Get list of enabled service IDs
#
# Takes into account both service-level enabled flag and group-level enabled flag.
#
# Returns: Space-separated list of service IDs via stdout
service_get_enabled() {
    if [ "$_SVC_CACHE_VALID" = true ]; then
        echo "$_SVC_CACHE_ENABLED"
        return
    fi
    _service_jq -r '
        .groups as $groups |
        [.services[] |
            select(.enabled != false) |
            select(
                (.groups // []) as $svc_groups |
                ($svc_groups | length == 0) or
                ($svc_groups | map(. as $g | $groups[$g].enabled // true) | all)
            ) |
            .id
        ] | .[]
    '
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

    # Check cache first (populated at load time or lazily)
    local cache_key="field:${id}:${field}"
    if [ -n "${_SVC_CACHE[$cache_key]+x}" ]; then
        local cached="${_SVC_CACHE[$cache_key]}"
        if [ -z "$cached" ]; then
            echo "$default"
        else
            echo "$cached"
        fi
        return
    fi

    # Fallback to jq (caches result for next call)
    local result
    result=$(_service_jq --arg id "$id" '.services[] | select(.id == $id) | '"$field"' // null' -r)

    if [ "$result" = "null" ] || [ -z "$result" ]; then
        _SVC_CACHE[$cache_key]=""
        echo "$default"
    else
        _SVC_CACHE[$cache_key]="$result"
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
    if [ -n "${_SVC_CACHE["field:${id}:.schedule.interval"]+x}" ]; then
        echo "${_SVC_CACHE["field:${id}:.schedule.interval"]}"
        return
    fi
    local interval
    interval=$(service_get_field "$id" ".schedule.interval" "0")
    echo "$interval"
}

# Get jitter for an interval-type service
#
# Args:
#   id - Service identifier
#
# Returns: Jitter in seconds (0 if not configured)
service_get_jitter() {
    local id="$1"
    if [ -n "${_SVC_CACHE["field:${id}:.schedule.jitter"]+x}" ]; then
        echo "${_SVC_CACHE["field:${id}:.schedule.jitter"]}"
        return
    fi
    service_get_field "$id" ".schedule.jitter" "0"
}

# Check if a service should run on startup
#
# Args:
#   id - Service identifier
#
# Returns: 0 if should run on startup, 1 otherwise
service_runs_on_startup() {
    local id="$1"
    if [ -n "${_SVC_CACHE["field:${id}:.schedule.run_on_startup"]+x}" ]; then
        [ "${_SVC_CACHE["field:${id}:.schedule.run_on_startup"]}" = "true" ]
        return
    fi
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
    _service_jq --arg id "$id" '.services[] | select(.id == $id) | .concurrency // {"max_instances": 1, "if_running": "skip", "priority": "normal"}' -c
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

# =============================================================================
# Dependency Functions
# =============================================================================

# Get dependencies for a service
#
# Args:
#   id - Service identifier
#
# Returns: Space-separated list of dependency service IDs
service_get_dependencies() {
    local id="$1"
    if [ -n "${_SVC_CACHE["depends_on:${id}"]+x}" ]; then
        echo "${_SVC_CACHE["depends_on:${id}"]}"
        return
    fi
    _service_jq --arg id "$id" -r '.services[] | select(.id == $id) | .depends_on // [] | .[]'
}

# Check if all dependencies for a service are satisfied
#
# A dependency is satisfied if the dependent service has run successfully
# within its interval period (or within a reasonable time window for
# event-based services).
#
# Args:
#   id - Service identifier
#
# Returns: 0 if all dependencies satisfied, 1 otherwise
service_dependencies_satisfied() {
    local id="$1"

    local deps
    deps=$(service_get_dependencies "$id")

    [ -z "$deps" ] && return 0

    for dep_id in $deps; do
        # Get the dependency's interval (or use 300s default for non-interval)
        local dep_interval
        dep_interval=$(service_get_interval "$dep_id")
        [ "$dep_interval" -eq 0 ] && dep_interval=300

        # Check if dependency ran successfully within its interval
        if ! service_state_succeeded_within "$dep_id" "$dep_interval"; then
            log_debug "Service $id dependency '$dep_id' not satisfied"
            return 1
        fi
    done

    return 0
}

# =============================================================================
# Condition Functions
# =============================================================================

# Get condition config for a service
#
# Args:
#   id - Service identifier
#
# Returns: Compact JSON of condition config, or "null" if none
service_get_condition() {
    local id="$1"
    _service_jq --arg id "$id" '.services[] | select(.id == $id) | .condition // null' -c
}

# Check if conditions are met for a service to run
#
# Evaluates all configured conditions:
# - file_exists: Glob pattern must match at least one file
# - file_not_exists: Glob pattern must match no files
# - env_set: Environment variable must be set and non-empty
# - env_equals: Environment variables must equal specified values
# - command: Shell command must exit with code 0
#
# Args:
#   id - Service identifier
#
# Returns: 0 if all conditions met, 1 otherwise
service_conditions_met() {
    local id="$1"

    # Fast path: use pre-parsed condition fields from cache
    if [ -n "${_SVC_CACHE["has_condition:${id}"]+x}" ]; then
        [ "${_SVC_CACHE["has_condition:${id}"]}" = "true" ] || return 0

        # Check file_exists
        local file_exists_pattern="${_SVC_CACHE["cond_fe:${id}"]:-}"
        if [ -n "$file_exists_pattern" ]; then
            # Reject patterns with path traversal or command substitution
            if [[ "$file_exists_pattern" == *".."* ]] || [[ "$file_exists_pattern" == *'$('* ]] || [[ "$file_exists_pattern" == *'`'* ]]; then
                log_warn "Service $id condition file_exists rejected: unsafe pattern '$file_exists_pattern'"
                return 1
            fi
            # shellcheck disable=SC2086
            if ! compgen -G $file_exists_pattern > /dev/null 2>&1; then
                log_debug "Service $id condition file_exists '$file_exists_pattern' not met"
                return 1
            fi
        fi

        # Check file_not_exists
        local file_not_exists_pattern="${_SVC_CACHE["cond_fne:${id}"]:-}"
        if [ -n "$file_not_exists_pattern" ]; then
            # Reject patterns with path traversal or command substitution
            if [[ "$file_not_exists_pattern" == *".."* ]] || [[ "$file_not_exists_pattern" == *'$('* ]] || [[ "$file_not_exists_pattern" == *'`'* ]]; then
                log_warn "Service $id condition file_not_exists rejected: unsafe pattern '$file_not_exists_pattern'"
                return 1
            fi
            # shellcheck disable=SC2086
            if compgen -G $file_not_exists_pattern > /dev/null 2>&1; then
                log_debug "Service $id condition file_not_exists '$file_not_exists_pattern' not met"
                return 1
            fi
        fi

        # Check env_set
        local env_set_var="${_SVC_CACHE["cond_es:${id}"]:-}"
        if [ -n "$env_set_var" ]; then
            if [ -z "${!env_set_var:-}" ]; then
                log_debug "Service $id condition env_set '$env_set_var' not met"
                return 1
            fi
        fi

        # Check command
        local check_command="${_SVC_CACHE["cond_cmd:${id}"]:-}"
        if [ -n "$check_command" ]; then
            if ! bash -c "$check_command" > /dev/null 2>&1; then
                log_debug "Service $id condition command '$check_command' not met"
                return 1
            fi
        fi

        # env_equals/env_not_equals are rare — fall through to jq only if needed
        local condition
        condition=$(service_get_condition "$id")
        if [ "$condition" != "null" ]; then
            local env_equals
            env_equals=$(echo "$condition" | jq -c '.env_equals // null')
            if [ "$env_equals" != "null" ]; then
                local env_vars
                env_vars=$(echo "$env_equals" | jq -r 'keys[]')
                for var in $env_vars; do
                    local expected_value
                    expected_value=$(echo "$env_equals" | jq -r --arg v "$var" '.[$v]')
                    local actual_value="${!var:-}"
                    if [ "$actual_value" != "$expected_value" ]; then
                        log_debug "Service $id condition env_equals '$var=$expected_value' not met (actual: '$actual_value')"
                        return 1
                    fi
                done
            fi

            local env_not_equals
            env_not_equals=$(echo "$condition" | jq -c '.env_not_equals // null')
            if [ "$env_not_equals" != "null" ]; then
                local env_ne_vars
                env_ne_vars=$(echo "$env_not_equals" | jq -r 'keys[]')
                for var in $env_ne_vars; do
                    local excluded_value
                    excluded_value=$(echo "$env_not_equals" | jq -r --arg v "$var" '.[$v]')
                    local actual_value="${!var:-}"
                    if [ "$actual_value" = "$excluded_value" ]; then
                        log_debug "Service $id condition env_not_equals '$var!=$excluded_value' not met (actual: '$actual_value')"
                        return 1
                    fi
                done
            fi
        fi

        return 0
    fi

    # Fallback: original jq-based path (for uncached services)
    local condition
    condition=$(service_get_condition "$id")

    [ "$condition" = "null" ] && return 0

    local file_exists_pattern
    file_exists_pattern=$(echo "$condition" | jq -r '.file_exists // empty')
    if [ -n "$file_exists_pattern" ]; then
        # Reject patterns with path traversal or command substitution
        if [[ "$file_exists_pattern" == *".."* ]] || [[ "$file_exists_pattern" == *'$('* ]] || [[ "$file_exists_pattern" == *'`'* ]]; then
            log_warn "Service $id condition file_exists rejected: unsafe pattern '$file_exists_pattern'"
            return 1
        fi
        # shellcheck disable=SC2086
        if ! compgen -G $file_exists_pattern > /dev/null 2>&1; then
            log_debug "Service $id condition file_exists '$file_exists_pattern' not met"
            return 1
        fi
    fi

    local file_not_exists_pattern
    file_not_exists_pattern=$(echo "$condition" | jq -r '.file_not_exists // empty')
    if [ -n "$file_not_exists_pattern" ]; then
        # Reject patterns with path traversal or command substitution
        if [[ "$file_not_exists_pattern" == *".."* ]] || [[ "$file_not_exists_pattern" == *'$('* ]] || [[ "$file_not_exists_pattern" == *'`'* ]]; then
            log_warn "Service $id condition file_not_exists rejected: unsafe pattern '$file_not_exists_pattern'"
            return 1
        fi
        # shellcheck disable=SC2086
        if compgen -G $file_not_exists_pattern > /dev/null 2>&1; then
            log_debug "Service $id condition file_not_exists '$file_not_exists_pattern' not met"
            return 1
        fi
    fi

    local env_set_var
    env_set_var=$(echo "$condition" | jq -r '.env_set // empty')
    if [ -n "$env_set_var" ]; then
        if [ -z "${!env_set_var:-}" ]; then
            log_debug "Service $id condition env_set '$env_set_var' not met"
            return 1
        fi
    fi

    local env_equals
    env_equals=$(echo "$condition" | jq -c '.env_equals // null')
    if [ "$env_equals" != "null" ]; then
        local env_vars
        env_vars=$(echo "$env_equals" | jq -r 'keys[]')
        for var in $env_vars; do
            local expected_value
            expected_value=$(echo "$env_equals" | jq -r --arg v "$var" '.[$v]')
            local actual_value="${!var:-}"
            if [ "$actual_value" != "$expected_value" ]; then
                log_debug "Service $id condition env_equals '$var=$expected_value' not met (actual: '$actual_value')"
                return 1
            fi
        done
    fi

    local env_not_equals
    env_not_equals=$(echo "$condition" | jq -c '.env_not_equals // null')
    if [ "$env_not_equals" != "null" ]; then
        local env_ne_vars
        env_ne_vars=$(echo "$env_not_equals" | jq -r 'keys[]')
        for var in $env_ne_vars; do
            local excluded_value
            excluded_value=$(echo "$env_not_equals" | jq -r --arg v "$var" '.[$v]')
            local actual_value="${!var:-}"
            if [ "$actual_value" = "$excluded_value" ]; then
                log_debug "Service $id condition env_not_equals '$var!=$excluded_value' not met (actual: '$actual_value')"
                return 1
            fi
        done
    fi

    local check_command
    check_command=$(echo "$condition" | jq -r '.command // empty')
    if [ -n "$check_command" ]; then
        if ! bash -c "$check_command" > /dev/null 2>&1; then
            log_debug "Service $id condition command '$check_command' not met"
            return 1
        fi
    fi

    return 0
}

# =============================================================================
# Health Check Functions
# =============================================================================

# Get health check config for a service
#
# Args:
#   id - Service identifier
#
# Returns: Compact JSON of health config, or "null" if none
service_get_health_check() {
    local id="$1"
    _service_jq --arg id "$id" '.services[] | select(.id == $id) | .health // null' -c
}

# Check if a service has health checks configured
#
# Args:
#   id - Service identifier
#
# Returns: 0 if health checks configured, 1 otherwise
service_has_health_check() {
    local id="$1"
    local health
    health=$(service_get_health_check "$id")
    [ "$health" != "null" ]
}

# =============================================================================
# Resource Limits Functions
# =============================================================================

# Get resource limits for a service
#
# Args:
#   id - Service identifier
#
# Returns: Compact JSON of limits config, or "null" if none
service_get_limits() {
    local id="$1"
    _service_jq --arg id "$id" '.services[] | select(.id == $id) | .limits // null' -c
}

# Parse memory limit to bytes
#
# Args:
#   limit - Memory limit string (e.g., "512M", "1G", "1024K")
#
# Returns: Memory limit in bytes
service_parse_memory_limit() {
    local limit="$1"

    # Extract number and unit
    local number="${limit%[KMG]}"
    local unit="${limit: -1}"

    case "$unit" in
        K) echo $((number * 1024)) ;;
        M) echo $((number * 1024 * 1024)) ;;
        G) echo $((number * 1024 * 1024 * 1024)) ;;
        *) echo "$limit" ;;  # Assume bytes if no unit
    esac
}

# =============================================================================
# Circuit Breaker Functions
# =============================================================================

# Get circuit breaker config for a service
#
# Checks service-level config first, then falls back to defaults.
#
# Args:
#   id - Service identifier
#
# Returns: Compact JSON of circuit breaker config
service_get_circuit_breaker() {
    local id="$1"

    local service_cb
    service_cb=$(_service_jq --arg id "$id" '.services[] | select(.id == $id) | .circuit_breaker // null' -c)

    if [ "$service_cb" != "null" ]; then
        echo "$service_cb"
        return
    fi

    # Fall back to defaults
    _service_jq '.defaults.circuit_breaker // {"enabled": false, "threshold": 5, "cooldown": 300, "half_open_requests": 1}' -c
}

# Check if circuit breaker is enabled for a service
#
# Args:
#   id - Service identifier
#
# Returns: 0 if enabled, 1 otherwise
service_circuit_breaker_enabled() {
    local id="$1"
    if [ -n "${_SVC_CACHE["cb_enabled:${id}"]+x}" ]; then
        [ "${_SVC_CACHE["cb_enabled:${id}"]}" = "true" ]
        return
    fi
    local cb
    cb=$(service_get_circuit_breaker "$id")
    local enabled
    enabled=$(echo "$cb" | jq -r '.enabled // false')
    [ "$enabled" = "true" ]
}

# =============================================================================
# Backoff Functions
# =============================================================================

# Get backoff config for a service
#
# Args:
#   id - Service identifier
#
# Returns: Compact JSON of backoff config
service_get_backoff() {
    local id="$1"

    local service_backoff
    service_backoff=$(_service_jq --arg id "$id" '.services[] | select(.id == $id) | .restart_policy.backoff // null' -c)

    if [ "$service_backoff" != "null" ]; then
        echo "$service_backoff"
        return
    fi

    # Fall back to defaults
    _service_jq '.defaults.restart_policy.backoff // {"initial": 5, "multiplier": 2, "max": 300}' -c
}

# Calculate backoff delay for a retry
#
# Args:
#   id          - Service identifier
#   retry_count - Current retry count (0-based)
#
# Returns: Backoff delay in seconds
service_calculate_backoff() {
    local id="$1"
    local retry_count="$2"

    local backoff
    backoff=$(service_get_backoff "$id")

    local initial multiplier max_backoff
    initial=$(echo "$backoff" | jq -r '.initial // 5')
    multiplier=$(echo "$backoff" | jq -r '.multiplier // 2')
    max_backoff=$(echo "$backoff" | jq -r '.max // 300')

    # Calculate: initial * (multiplier ^ retry_count)
    local delay="$initial"
    for ((i = 0; i < retry_count; i++)); do
        delay=$((delay * multiplier))
        if [ "$delay" -gt "$max_backoff" ]; then
            delay="$max_backoff"
            break
        fi
    done

    echo "$delay"
}

# =============================================================================
# Group Functions
# =============================================================================

# Get groups a service belongs to
#
# Args:
#   id - Service identifier
#
# Returns: Space-separated list of group names
service_get_groups() {
    local id="$1"
    _service_jq --arg id "$id" -r '.services[] | select(.id == $id) | .groups // [] | .[]'
}

# Get all services in a group
#
# Args:
#   group - Group name
#
# Returns: Space-separated list of service IDs
service_get_services_in_group() {
    local group="$1"
    _service_jq --arg group "$group" -r '.services[] | select(.groups // [] | index($group)) | .id'
}

# Check if a group is enabled
#
# Args:
#   group - Group name
#
# Returns: 0 if enabled, 1 if disabled
service_is_group_enabled() {
    local group="$1"
    local enabled
    enabled=$(_service_jq --arg group "$group" -r '.groups[$group].enabled // true')
    [ "$enabled" = "true" ]
}

# Get all defined groups
#
# Returns: Space-separated list of group names
service_get_all_groups() {
    _service_jq -r '.groups // {} | keys[]'
}

# =============================================================================
# Cron Functions
# =============================================================================

# Get cron expression for a cron-scheduled service
#
# Args:
#   id - Service identifier
#
# Returns: Cron expression string, or empty if not cron-scheduled
service_get_cron_expression() {
    local id="$1"
    service_get_field "$id" ".schedule.cron" ""
}

# Check if a cron expression matches the current time
#
# Args:
#   cron_expr - Cron expression (minute hour day month weekday)
#   timezone  - Timezone (default: UTC)
#
# Returns: 0 if matches, 1 otherwise
service_cron_matches_now() {
    local cron_expr="$1"
    local timezone="${2:-UTC}"

    # Parse cron expression
    local minute hour day month weekday
    read -r minute hour day month weekday <<< "$cron_expr"

    # Get current time in specified timezone
    local now_minute now_hour now_day now_month now_weekday
    now_minute=$(TZ="$timezone" date +%M | sed 's/^0//')
    now_hour=$(TZ="$timezone" date +%H | sed 's/^0//')
    now_day=$(TZ="$timezone" date +%d | sed 's/^0//')
    now_month=$(TZ="$timezone" date +%m | sed 's/^0//')
    now_weekday=$(TZ="$timezone" date +%u)  # 1=Monday, 7=Sunday

    # Convert Sunday from 7 to 0 for cron compatibility
    [ "$now_weekday" -eq 7 ] && now_weekday=0

    # Check each field
    _cron_field_matches "$minute" "$now_minute" 0 59 || return 1
    _cron_field_matches "$hour" "$now_hour" 0 23 || return 1
    _cron_field_matches "$day" "$now_day" 1 31 || return 1
    _cron_field_matches "$month" "$now_month" 1 12 || return 1
    _cron_field_matches "$weekday" "$now_weekday" 0 6 || return 1

    return 0
}

# Check if a cron field matches a value
#
# Args:
#   field - Cron field expression (*, number, range, list, or step)
#   value - Current value to match
#   min   - Minimum allowed value
#   max   - Maximum allowed value
#
# Returns: 0 if matches, 1 otherwise
_cron_field_matches() {
    local field="$1"
    local value="$2"
    local min="$3"
    local max="$4"

    # Wildcard matches everything
    [ "$field" = "*" ] && return 0

    # Handle step values (*/5 or 1-10/2)
    if [[ "$field" == *"/"* ]]; then
        local base="${field%/*}"
        local step="${field#*/}"

        if [ "$base" = "*" ]; then
            [ $((value % step)) -eq 0 ] && return 0
        else
            # Range with step
            local range_start range_end
            range_start="${base%-*}"
            range_end="${base#*-}"
            [ "$range_start" = "$base" ] && range_end="$max"

            if [ "$value" -ge "$range_start" ] && [ "$value" -le "$range_end" ]; then
                [ $(((value - range_start) % step)) -eq 0 ] && return 0
            fi
        fi
        return 1
    fi

    # Handle lists (1,5,10)
    if [[ "$field" == *","* ]]; then
        local IFS=','
        for item in $field; do
            _cron_field_matches "$item" "$value" "$min" "$max" && return 0
        done
        return 1
    fi

    # Handle ranges (1-5)
    if [[ "$field" == *"-"* ]]; then
        local range_start="${field%-*}"
        local range_end="${field#*-}"
        [ "$value" -ge "$range_start" ] && [ "$value" -le "$range_end" ] && return 0
        return 1
    fi

    # Simple number match
    [ "$field" -eq "$value" ] 2>/dev/null && return 0

    return 1
}

# =============================================================================
# Metrics Config Functions
# =============================================================================

# Get metrics config for a service
#
# Args:
#   id - Service identifier
#
# Returns: Compact JSON of metrics config
service_get_metrics_config() {
    local id="$1"
    _service_jq --arg id "$id" '.services[] | select(.id == $id) | .metrics // {"enabled": true, "emit_to": "activity", "include_output": false}' -c
}

# Check if metrics are enabled for a service
#
# Args:
#   id - Service identifier
#
# Returns: 0 if enabled, 1 otherwise
service_metrics_enabled() {
    local id="$1"
    local config
    config=$(service_get_metrics_config "$id")
    local enabled
    enabled=$(echo "$config" | jq -r '.enabled // true')
    [ "$enabled" = "true" ]
}

# =============================================================================
# Triggers Normalization
# =============================================================================

# Normalize `triggers` convenience field into schedule.type=event + trigger array
#
# Converts:
#   "triggers": { "on_complete": ["X"], "on_failure": ["Y"], "on_finish": ["Z"] }
# Into:
#   "schedule": { "type": "event", "trigger": ["service.succeeded:X", "service.failed:Y", "service.completed:Z"] }
#
# The `triggers` field is only valid when `schedule` is absent or `schedule.type=event`.
# After normalization, the `triggers` field is removed from the service definition.
#
# Args: none (operates on _SERVICE_JSON or _SERVICE_JSON_FILE)
#
# Side effects: Updates _SERVICE_JSON with normalized services
_normalize_service_triggers() {
    local json
    if [ -n "$_SERVICE_JSON" ]; then
        json="$_SERVICE_JSON"
    elif [ -n "$_SERVICE_JSON_FILE" ]; then
        json=$(cat "$_SERVICE_JSON_FILE")
    else
        return 0
    fi

    # Check if any service has a triggers field
    local has_triggers
    has_triggers=$(echo "$json" | jq '[.services[] | select(.triggers != null)] | length')
    has_triggers="${has_triggers:-0}"

    [ "$has_triggers" -gt 0 ] || return 0

    # Normalize: convert triggers into schedule.trigger array, remove triggers field
    _SERVICE_JSON=$(echo "$json" | jq '
        .services = [.services[] |
            if .triggers != null then
                # Build trigger array from on_complete/on_failure/on_finish
                (.triggers.on_complete // []) as $on_complete |
                (.triggers.on_failure // []) as $on_failure |
                (.triggers.on_finish // []) as $on_finish |
                (
                    [$on_complete[] | "service.succeeded:\(.)"] +
                    [$on_failure[] | "service.failed:\(.)"] +
                    [$on_finish[] | "service.completed:\(.)"]
                ) as $trigger_list |
                # Set schedule to event type with trigger array
                .schedule = {
                    "type": "event",
                    "trigger": $trigger_list
                } |
                # Remove triggers field
                del(.triggers)
            else
                .
            end
        ]
    ')
    _SERVICE_JSON_FILE=""
}

# =============================================================================
# Built-in Defaults
# =============================================================================

# Load built-in defaults (fallback when no config file exists)
service_load_builtin_defaults() {
    _SERVICE_VERSION="1.0"
    _SERVICE_JSON_FILE=""
    _SERVICE_JSON='{
  "version": "1.0",
  "defaults": {
    "timeout": 300,
    "restart_policy": {
      "on_failure": "skip",
      "max_retries": 2,
      "backoff": { "initial": 5, "multiplier": 2, "max": 300 }
    },
    "circuit_breaker": { "enabled": false, "threshold": 5, "cooldown": 300 }
  },
  "groups": {
    "pr-management": { "description": "PR-related services", "enabled": true },
    "workers": { "description": "Worker management services", "enabled": true }
  },
  "services": [
    {
      "id": "pr-sync",
      "groups": ["pr-management"],
      "schedule": { "type": "interval", "interval": 180, "jitter": 30, "run_on_startup": true },
      "execution": { "type": "command", "command": "wiggum-pr sync" }
    },
    {
      "id": "pr-optimizer",
      "groups": ["pr-management"],
      "schedule": { "type": "interval", "interval": 900 },
      "execution": { "type": "function", "function": "svc_orch_spawn_pr_optimizer" },
      "concurrency": { "max_instances": 1, "if_running": "skip" }
    },
    {
      "id": "fix-workers",
      "groups": ["workers"],
      "schedule": { "type": "interval", "interval": 60, "run_on_startup": true },
      "execution": { "type": "function", "function": "svc_orch_spawn_fix_workers" }
    },
    {
      "id": "resolve-workers",
      "groups": ["workers"],
      "schedule": { "type": "interval", "interval": 60, "run_on_startup": true },
      "execution": { "type": "function", "function": "svc_orch_spawn_resolve_workers" }
    },
    {
      "id": "task-spawner",
      "groups": ["workers"],
      "schedule": { "type": "interval", "interval": 60, "run_on_startup": true },
      "execution": { "type": "function", "function": "svc_orch_spawn_ready_tasks" }
    },
    {
      "id": "worker-cleanup",
      "groups": ["workers"],
      "schedule": { "type": "interval", "interval": 60, "run_on_startup": true },
      "execution": { "type": "function", "function": "svc_orch_cleanup_all_workers" }
    }
  ]
}'
    _SERVICE_COUNT=6

    log "Loaded built-in default services with $_SERVICE_COUNT services"
    _service_populate_cache
}

# =============================================================================
# Phase Functions (v2.0)
# =============================================================================

# Get phase for a service
#
# Args:
#   id - Service identifier
#
# Returns: Phase string (startup|pre|periodic|post|shutdown), default: periodic
service_get_phase() {
    local id="$1"
    service_get_field "$id" ".phase" "periodic"
}

# Get execution order within phase
#
# Args:
#   id - Service identifier
#
# Returns: Order integer, default: 50
service_get_order() {
    local id="$1"
    service_get_field "$id" ".order" "50"
}

# Get all services for a given phase, sorted by order
#
# Args:
#   phase - Phase name (startup|pre|periodic|post|shutdown)
#
# Returns: Space-separated list of service IDs, sorted by order
service_get_phase_services() {
    local phase="$1"

    if [ "$_SVC_CACHE_VALID" = true ] && [ -n "${_SVC_CACHE["phase_ids:${phase}"]+x}" ]; then
        echo "${_SVC_CACHE["phase_ids:${phase}"]}"
        return
    fi

    _service_jq -r --arg phase "$phase" '
        .groups as $groups |
        [.services[] |
            select(.enabled != false) |
            select(
                (.groups // []) as $svc_groups |
                ($svc_groups | length == 0) or
                ($svc_groups | map(. as $g | $groups[$g].enabled // true) | all)
            ) |
            select((.phase // "periodic") == $phase)
        ] | sort_by(.order // 50) | .[].id
    '
}
