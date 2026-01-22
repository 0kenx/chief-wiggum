#!/usr/bin/env bash
# config-validator.sh - JSON schema validation for configuration files
#
# Provides validation functions for config.json and agents.json files
# using jq for JSON parsing. Reports helpful error messages for invalid config.
set -euo pipefail

source "$WIGGUM_HOME/lib/core/logger.sh"

# Validate a JSON file exists and is valid JSON
#
# Args:
#   config_file - Path to JSON file to validate
#
# Returns: 0 if valid, 1 if invalid
validate_json_file() {
    local config_file="$1"

    if [ ! -f "$config_file" ]; then
        log_error "Config file not found: $config_file"
        return 1
    fi

    if ! jq empty "$config_file" 2>/dev/null; then
        log_error "Invalid JSON syntax in: $config_file"
        log_error "Run 'jq . $config_file' to see the error"
        return 1
    fi

    return 0
}

# Validate config.json against schema
#
# Args:
#   config_file - Path to config.json (defaults to $WIGGUM_HOME/config/config.json)
#
# Returns: 0 if valid, 1 if invalid
validate_config() {
    local config_file="${1:-$WIGGUM_HOME/config/config.json}"
    local errors=0

    log_debug "Validating config: $config_file"

    # First check JSON is valid
    if ! validate_json_file "$config_file"; then
        return 1
    fi

    # Check required sections exist
    local sections=("workers" "hooks" "paths" "review")
    for section in "${sections[@]}"; do
        if ! jq -e ".$section" "$config_file" > /dev/null 2>&1; then
            log_warn "Missing optional section: $section"
        fi
    done

    # Validate workers section
    if jq -e '.workers' "$config_file" > /dev/null 2>&1; then
        local max_iter
        max_iter=$(jq -r '.workers.max_iterations // 50' "$config_file")
        if [ "$max_iter" -lt 1 ] || [ "$max_iter" -gt 100 ]; then
            log_error "workers.max_iterations must be between 1 and 100 (got: $max_iter)"
            ((++errors))
        fi

        local sleep_sec
        sleep_sec=$(jq -r '.workers.sleep_seconds // 2' "$config_file")
        if [ "$sleep_sec" -lt 0 ] || [ "$sleep_sec" -gt 60 ]; then
            log_error "workers.sleep_seconds must be between 0 and 60 (got: $sleep_sec)"
            ((++errors))
        fi
    fi

    # Validate hooks section
    if jq -e '.hooks' "$config_file" > /dev/null 2>&1; then
        local hooks_enabled
        hooks_enabled=$(jq -r '.hooks.enabled // "true"' "$config_file")
        if [ "$hooks_enabled" != "true" ] && [ "$hooks_enabled" != "false" ]; then
            log_error "hooks.enabled must be boolean (got: $hooks_enabled)"
            ((++errors))
        fi
    fi

    # Validate review section
    if jq -e '.review' "$config_file" > /dev/null 2>&1; then
        local fix_max_iter
        fix_max_iter=$(jq -r '.review.fix_max_iterations // 10' "$config_file")
        if [ "$fix_max_iter" -lt 1 ] || [ "$fix_max_iter" -gt 50 ]; then
            log_error "review.fix_max_iterations must be between 1 and 50 (got: $fix_max_iter)"
            ((++errors))
        fi

        local fix_max_turns
        fix_max_turns=$(jq -r '.review.fix_max_turns // 30' "$config_file")
        if [ "$fix_max_turns" -lt 1 ] || [ "$fix_max_turns" -gt 100 ]; then
            log_error "review.fix_max_turns must be between 1 and 100 (got: $fix_max_turns)"
            ((++errors))
        fi

        # Validate approved_authors is an array if present
        if jq -e '.review.approved_authors' "$config_file" > /dev/null 2>&1; then
            if ! jq -e '.review.approved_authors | type == "array"' "$config_file" > /dev/null 2>&1; then
                log_error "review.approved_authors must be an array"
                ((++errors))
            fi
        fi
    fi

    # Check for unknown top-level keys
    local known_keys=("workers" "hooks" "paths" "review" "github")
    local actual_keys
    actual_keys=$(jq -r 'keys[]' "$config_file")

    while IFS= read -r key; do
        local found=false
        for known in "${known_keys[@]}"; do
            if [ "$key" = "$known" ]; then
                found=true
                break
            fi
        done
        if [ "$found" = false ]; then
            log_warn "Unknown config key: $key (will be ignored)"
        fi
    done <<< "$actual_keys"

    if [ $errors -gt 0 ]; then
        log_error "Config validation failed with $errors error(s)"
        return 1
    fi

    log_debug "Config validation passed: $config_file"
    return 0
}

# Validate agents.json against schema
#
# Args:
#   agents_file - Path to agents.json (defaults to $WIGGUM_HOME/config/agents.json)
#
# Returns: 0 if valid, 1 if invalid
validate_agents_config() {
    local agents_file="${1:-$WIGGUM_HOME/config/agents.json}"
    local errors=0

    log_debug "Validating agents config: $agents_file"

    # First check JSON is valid
    if ! validate_json_file "$agents_file"; then
        return 1
    fi

    # Check required sections exist
    if ! jq -e '.agents' "$agents_file" > /dev/null 2>&1; then
        log_error "Missing required section: agents"
        ((++errors))
    fi

    if ! jq -e '.defaults' "$agents_file" > /dev/null 2>&1; then
        log_error "Missing required section: defaults"
        ((++errors))
    fi

    # Validate each agent definition
    local agent_names
    agent_names=$(jq -r '.agents | keys[]' "$agents_file" 2>/dev/null || echo "")

    while IFS= read -r agent_name; do
        [ -z "$agent_name" ] && continue

        # Validate agent name format
        if ! [[ "$agent_name" =~ ^[a-z][a-z0-9-]*$ ]]; then
            log_error "Invalid agent name: '$agent_name' (must be lowercase with hyphens)"
            ((++errors))
            continue
        fi

        # Validate agent parameters
        _validate_agent_params "$agents_file" ".agents[\"$agent_name\"]" "$agent_name" || ((++errors))
    done <<< "$agent_names"

    # Validate defaults section
    _validate_agent_params "$agents_file" ".defaults" "defaults" || ((++errors))

    if [ $errors -gt 0 ]; then
        log_error "Agents config validation failed with $errors error(s)"
        return 1
    fi

    log_debug "Agents config validation passed: $agents_file"
    return 0
}

# Internal: Validate agent parameter values
#
# Args:
#   file    - JSON file path
#   path    - jq path to agent config
#   name    - Display name for error messages
#
# Returns: 0 if valid, 1 if invalid
_validate_agent_params() {
    local file="$1"
    local path="$2"
    local name="$3"
    local errors=0

    # Check max_iterations
    local max_iter
    max_iter=$(jq -r "$path.max_iterations // \"null\"" "$file")
    if [ "$max_iter" != "null" ]; then
        if ! [[ "$max_iter" =~ ^[0-9]+$ ]] || [ "$max_iter" -lt 1 ] || [ "$max_iter" -gt 100 ]; then
            log_error "$name: max_iterations must be between 1 and 100 (got: $max_iter)"
            ((++errors))
        fi
    fi

    # Check max_turns
    local max_turns
    max_turns=$(jq -r "$path.max_turns // \"null\"" "$file")
    if [ "$max_turns" != "null" ]; then
        if ! [[ "$max_turns" =~ ^[0-9]+$ ]] || [ "$max_turns" -lt 1 ] || [ "$max_turns" -gt 200 ]; then
            log_error "$name: max_turns must be between 1 and 200 (got: $max_turns)"
            ((++errors))
        fi
    fi

    # Check timeout_seconds
    local timeout
    timeout=$(jq -r "$path.timeout_seconds // \"null\"" "$file")
    if [ "$timeout" != "null" ]; then
        if ! [[ "$timeout" =~ ^[0-9]+$ ]] || [ "$timeout" -lt 60 ] || [ "$timeout" -gt 86400 ]; then
            log_error "$name: timeout_seconds must be between 60 and 86400 (got: $timeout)"
            ((++errors))
        fi
    fi

    # Check supervisor_interval
    local interval
    interval=$(jq -r "$path.supervisor_interval // \"null\"" "$file")
    if [ "$interval" != "null" ]; then
        if ! [[ "$interval" =~ ^[0-9]+$ ]] || [ "$interval" -lt 1 ] || [ "$interval" -gt 20 ]; then
            log_error "$name: supervisor_interval must be between 1 and 20 (got: $interval)"
            ((++errors))
        fi
    fi

    # Check max_restarts
    local restarts
    restarts=$(jq -r "$path.max_restarts // \"null\"" "$file")
    if [ "$restarts" != "null" ]; then
        if ! [[ "$restarts" =~ ^[0-9]+$ ]] || [ "$restarts" -gt 10 ]; then
            log_error "$name: max_restarts must be between 0 and 10 (got: $restarts)"
            ((++errors))
        fi
    fi

    # Check auto_commit is boolean
    local auto_commit
    auto_commit=$(jq -r "$path.auto_commit // \"null\"" "$file")
    if [ "$auto_commit" != "null" ] && [ "$auto_commit" != "true" ] && [ "$auto_commit" != "false" ]; then
        log_error "$name: auto_commit must be boolean (got: $auto_commit)"
        ((++errors))
    fi

    return $errors
}

# Validate all configuration files
#
# Returns: 0 if all valid, 1 if any invalid
validate_all_config() {
    local errors=0

    log_info "Validating configuration files..."

    if ! validate_config; then
        ((++errors))
    fi

    if ! validate_agents_config; then
        ((++errors))
    fi

    if [ $errors -gt 0 ]; then
        log_error "Configuration validation failed"
        return 1
    fi

    log_info "All configuration files valid"
    return 0
}
