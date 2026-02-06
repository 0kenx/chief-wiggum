#!/usr/bin/env bash
# =============================================================================
# server-identity.sh - Distributed server identity management
#
# Generates and manages unique server identifiers for distributed task claiming.
# Each server instance gets a unique ID for coordination with other servers.
#
# Identity format: wiggum-{hostname}-{timestamp}-{random}
#
# Storage: .ralph/server/identity.json
# =============================================================================
set -euo pipefail

[ -n "${_SERVER_IDENTITY_LOADED:-}" ] && return 0
_SERVER_IDENTITY_LOADED=1

# Source dependencies
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"

# =============================================================================
# Configuration
# =============================================================================

# Server identity file name
_SERVER_IDENTITY_FILE="identity.json"

# Server config file name
_SERVER_CONFIG_FILE="config.json"

# Default heartbeat interval (seconds)
_SERVER_DEFAULT_HEARTBEAT_INTERVAL=180

# Default sync interval (seconds)
_SERVER_DEFAULT_SYNC_INTERVAL=300

# Default stale threshold (seconds)
_SERVER_DEFAULT_STALE_THRESHOLD=600

# Default max concurrent tasks
_SERVER_DEFAULT_MAX_CONCURRENT=4

# =============================================================================
# Identity Generation
# =============================================================================

# Generate a unique server ID
#
# Format: wiggum-{hostname}-{timestamp}-{random}
# Example: wiggum-myserver-1707235200-a1b2c3d4
#
# Returns: server_id on stdout
server_identity_generate() {
    local hostname
    hostname=$(hostname -s 2>/dev/null || hostname 2>/dev/null || echo "unknown")
    # Sanitize hostname: lowercase, replace non-alphanumeric with dash
    hostname=$(echo "$hostname" | tr '[:upper:]' '[:lower:]' | sed 's/[^a-z0-9]/-/g')

    local timestamp
    timestamp=$(epoch_now)

    local random
    random=$(head -c 4 /dev/urandom 2>/dev/null | od -An -tx1 | tr -d ' \n' || echo "$(date +%N)")

    echo "wiggum-${hostname}-${timestamp}-${random}"
}

# =============================================================================
# Identity Persistence
# =============================================================================

# Get or create server identity
#
# If an identity file exists and is valid, returns the existing ID.
# Otherwise, generates a new identity and saves it.
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: server_id on stdout
server_identity_get_or_create() {
    local ralph_dir="$1"
    local server_dir="$ralph_dir/server"
    local identity_file="$server_dir/$_SERVER_IDENTITY_FILE"

    # Create server directory if needed
    mkdir -p "$server_dir"

    # Check for override from environment
    if [ -n "${WIGGUM_SERVER_ID:-}" ]; then
        echo "$WIGGUM_SERVER_ID"
        return 0
    fi

    # Check for existing identity
    if [ -f "$identity_file" ]; then
        local existing_id
        existing_id=$(jq -r '.server_id // ""' "$identity_file" 2>/dev/null)
        if [ -n "$existing_id" ]; then
            echo "$existing_id"
            return 0
        fi
    fi

    # Generate new identity
    local server_id
    server_id=$(server_identity_generate)

    local started_at
    started_at=$(iso_now)

    local hostname
    hostname=$(hostname -f 2>/dev/null || hostname 2>/dev/null || echo "unknown")

    # Save identity
    jq -n \
        --arg server_id "$server_id" \
        --arg started_at "$started_at" \
        --arg hostname "$hostname" \
        --arg pid "$$" \
        '{
            server_id: $server_id,
            started_at: $started_at,
            hostname: $hostname,
            pid: ($pid | tonumber),
            version: 1
        }' > "$identity_file"

    log_debug "Generated server identity: $server_id"
    echo "$server_id"
}

# Get existing server identity (without creating)
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: server_id on stdout, or empty if none exists
server_identity_get() {
    local ralph_dir="$1"
    local identity_file="$ralph_dir/server/$_SERVER_IDENTITY_FILE"

    if [ -f "$identity_file" ]; then
        jq -r '.server_id // ""' "$identity_file" 2>/dev/null
    fi
}

# Reset server identity (generates new ID)
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: new server_id on stdout
server_identity_reset() {
    local ralph_dir="$1"
    local identity_file="$ralph_dir/server/$_SERVER_IDENTITY_FILE"

    rm -f "$identity_file"
    server_identity_get_or_create "$ralph_dir"
}

# Update server identity PID (for process restart detection)
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: 0 on success
server_identity_update_pid() {
    local ralph_dir="$1"
    local identity_file="$ralph_dir/server/$_SERVER_IDENTITY_FILE"

    [ -f "$identity_file" ] || return 1

    local tmp_file
    tmp_file=$(mktemp "${identity_file}.XXXXXX")
    jq --arg pid "$$" '.pid = ($pid | tonumber)' "$identity_file" > "$tmp_file"
    mv "$tmp_file" "$identity_file"
}

# =============================================================================
# Server Configuration
# =============================================================================

# Load server configuration with defaults
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: Sets global config variables
server_config_load() {
    local ralph_dir="$1"
    local config_file="$ralph_dir/server/$_SERVER_CONFIG_FILE"

    # Set defaults
    SERVER_HEARTBEAT_INTERVAL=$_SERVER_DEFAULT_HEARTBEAT_INTERVAL
    SERVER_SYNC_INTERVAL=$_SERVER_DEFAULT_SYNC_INTERVAL
    SERVER_STALE_THRESHOLD=$_SERVER_DEFAULT_STALE_THRESHOLD
    SERVER_MAX_CONCURRENT=$_SERVER_DEFAULT_MAX_CONCURRENT

    # Override from config file if present
    if [ -f "$config_file" ]; then
        local val

        val=$(jq -r '.polling.heartbeat_interval_seconds // 0' "$config_file" 2>/dev/null)
        [ "$val" -gt 0 ] 2>/dev/null && SERVER_HEARTBEAT_INTERVAL=$val

        val=$(jq -r '.polling.sync_interval_seconds // 0' "$config_file" 2>/dev/null)
        [ "$val" -gt 0 ] 2>/dev/null && SERVER_SYNC_INTERVAL=$val

        val=$(jq -r '.claims.stale_threshold_seconds // 0' "$config_file" 2>/dev/null)
        [ "$val" -gt 0 ] 2>/dev/null && SERVER_STALE_THRESHOLD=$val

        val=$(jq -r '.claims.max_concurrent_tasks // 0' "$config_file" 2>/dev/null)
        [ "$val" -gt 0 ] 2>/dev/null && SERVER_MAX_CONCURRENT=$val
    fi

    # Export for use in other modules
    export SERVER_HEARTBEAT_INTERVAL SERVER_SYNC_INTERVAL
    export SERVER_STALE_THRESHOLD SERVER_MAX_CONCURRENT
}

# Save server configuration
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: 0 on success
server_config_save() {
    local ralph_dir="$1"
    local server_dir="$ralph_dir/server"
    local config_file="$server_dir/$_SERVER_CONFIG_FILE"

    mkdir -p "$server_dir"

    # Get server_id from identity
    local server_id
    server_id=$(server_identity_get "$ralph_dir")

    jq -n \
        --arg server_id "$server_id" \
        --arg mode "${WIGGUM_TASK_SOURCE_MODE:-local}" \
        --argjson heartbeat "${SERVER_HEARTBEAT_INTERVAL:-$_SERVER_DEFAULT_HEARTBEAT_INTERVAL}" \
        --argjson sync "${SERVER_SYNC_INTERVAL:-$_SERVER_DEFAULT_SYNC_INTERVAL}" \
        --argjson stale "${SERVER_STALE_THRESHOLD:-$_SERVER_DEFAULT_STALE_THRESHOLD}" \
        --argjson max_tasks "${SERVER_MAX_CONCURRENT:-$_SERVER_DEFAULT_MAX_CONCURRENT}" \
        '{
            server_id: $server_id,
            mode: $mode,
            polling: {
                heartbeat_interval_seconds: $heartbeat,
                sync_interval_seconds: $sync
            },
            claims: {
                stale_threshold_seconds: $stale,
                max_concurrent_tasks: $max_tasks
            }
        }' > "$config_file"
}

# =============================================================================
# Claims Cache
# =============================================================================

# Get path to local claims cache
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: path on stdout
_server_claims_file() {
    echo "$1/server/claims.json"
}

# Update local claims cache
#
# Records which tasks this server currently owns.
#
# Args:
#   ralph_dir - Path to .ralph directory
#   task_id   - Task ID to add/update
#   action    - "add" or "remove"
#
# Returns: 0 on success
server_claims_update() {
    local ralph_dir="$1"
    local task_id="$2"
    local action="$3"
    local claims_file
    claims_file=$(_server_claims_file "$ralph_dir")

    mkdir -p "$(dirname "$claims_file")"

    # Initialize if doesn't exist
    if [ ! -f "$claims_file" ]; then
        echo '{"tasks":{}}' > "$claims_file"
    fi

    local tmp_file
    tmp_file=$(mktemp "${claims_file}.XXXXXX")

    case "$action" in
        add)
            local now
            now=$(epoch_now)
            jq --arg tid "$task_id" --argjson claimed_at "$now" \
                '.tasks[$tid] = {claimed_at: $claimed_at}' "$claims_file" > "$tmp_file"
            ;;
        remove)
            jq --arg tid "$task_id" 'del(.tasks[$tid])' "$claims_file" > "$tmp_file"
            ;;
        *)
            rm -f "$tmp_file"
            return 1
            ;;
    esac

    mv "$tmp_file" "$claims_file"
}

# List claimed tasks from local cache
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: Lines of task_id on stdout
server_claims_list() {
    local ralph_dir="$1"
    local claims_file
    claims_file=$(_server_claims_file "$ralph_dir")

    [ -f "$claims_file" ] || return 0

    jq -r '.tasks | keys[]' "$claims_file" 2>/dev/null
}

# Check if task is in local claims cache
#
# Args:
#   ralph_dir - Path to .ralph directory
#   task_id   - Task ID to check
#
# Returns: 0 if claimed, 1 if not
server_claims_has() {
    local ralph_dir="$1"
    local task_id="$2"
    local claims_file
    claims_file=$(_server_claims_file "$ralph_dir")

    [ -f "$claims_file" ] || return 1

    jq -e --arg tid "$task_id" '.tasks | has($tid)' "$claims_file" > /dev/null 2>&1
}

# =============================================================================
# Heartbeat Log
# =============================================================================

# Append to heartbeat log
#
# Args:
#   ralph_dir - Path to .ralph directory
#   task_id   - Task ID
#   action    - Action type (start, heartbeat, complete, release)
#
# Returns: 0 on success
server_heartbeat_log() {
    local ralph_dir="$1"
    local task_id="$2"
    local action="$3"
    local heartbeat_log="$ralph_dir/server/heartbeat.log"

    # Security: Validate task_id format to prevent log injection
    if ! [[ "$task_id" =~ ^[A-Za-z]{2,10}-[0-9]{1,4}$ ]]; then
        log_warn "server_heartbeat_log: Invalid task_id format: $(printf '%q' "$task_id")"
        return 1
    fi

    # Security: Validate action (alphanumeric + underscore/hyphen only)
    if ! [[ "$action" =~ ^[a-z][a-z0-9_-]*$ ]]; then
        log_warn "server_heartbeat_log: Invalid action format: $(printf '%q' "$action")"
        return 1
    fi

    mkdir -p "$(dirname "$heartbeat_log")"

    local timestamp
    timestamp=$(iso_now)

    local server_id
    server_id=$(server_identity_get "$ralph_dir")

    echo "$timestamp|$server_id|$task_id|$action" >> "$heartbeat_log"
}
