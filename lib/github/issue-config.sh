#!/usr/bin/env bash
# issue-config.sh - Load and validate GitHub issue sync configuration
#
# Provides functions to read GitHub sync settings from config files
# with environment variable overrides.
#
# Configuration sources (priority order):
#   1. Environment variables (WIGGUM_GITHUB_*)
#   2. .ralph/config.json (project-specific)
#   3. config/config.json (global defaults)
#   4. Hardcoded fallback defaults
set -euo pipefail

# Prevent double-sourcing
[ -n "${_GITHUB_ISSUE_CONFIG_LOADED:-}" ] && return 0
_GITHUB_ISSUE_CONFIG_LOADED=1

# =============================================================================
# Configuration Variables (set after load_github_sync_config)
# =============================================================================

GITHUB_SYNC_ENABLED="${WIGGUM_GITHUB_ISSUE_SYNC:-}"
GITHUB_SYNC_ALLOWED_USER_IDS="${WIGGUM_GITHUB_ALLOWED_USER_IDS:-}"
GITHUB_SYNC_LABEL_FILTER="${WIGGUM_GITHUB_LABEL_FILTER:-}"
GITHUB_SYNC_DEFAULT_PRIORITY="${WIGGUM_GITHUB_DEFAULT_PRIORITY:-}"
GITHUB_SYNC_CLOSE_ON=""
GITHUB_SYNC_COMPLEXITY_LABELS=""
GITHUB_SYNC_CONTEXT_EVENTS="${WIGGUM_CONTEXT_EVENTS:-}"

# =============================================================================
# Internal: Extract config from JSON files
# =============================================================================

# Extract github sync config from a JSON config file
#
# Args:
#   config_file - Path to JSON config file
#
# Returns: tab-separated values on stdout:
#   enabled|user_ids|label_filter|default_priority|priority_labels_json|status_labels_json|close_on
_extract_github_sync_config() {
    local config_file="$1"

    [ -f "$config_file" ] || return 1

    # Use unit separator (\x1f) instead of @tsv — bash IFS=$'\t' collapses
    # consecutive tabs, losing empty fields and shifting all subsequent values.
    # Non-whitespace IFS characters preserve empty fields.
    jq -r '[
        (.github.issue_sync.enabled // ""),
        (.github.issue_sync.allowed_user_ids // [] | map(tostring) | join(",")),
        (.github.issue_sync.label_filter // ""),
        (.github.issue_sync.default_priority // ""),
        (.github.issue_sync.priority_labels // {} | tojson),
        (.github.issue_sync.status_labels // {} | tojson),
        (.github.issue_sync.close_on // [] | join(",")),
        (.github.issue_sync.context_events // ""),
        (.github.issue_sync.complexity_labels // {} | tojson)
    ] | join("\u001f")' "$config_file" 2>/dev/null || return 1
}

# =============================================================================
# Public API
# =============================================================================

# Load GitHub issue sync configuration
#
# Reads from config files and applies environment variable overrides.
# Must be called before using any github sync functions.
#
# Globals set:
#   GITHUB_SYNC_ENABLED          - "true" or "false"
#   GITHUB_SYNC_ALLOWED_USER_IDS - Comma-separated GitHub user IDs
#   GITHUB_SYNC_LABEL_FILTER     - Required issue label
#   GITHUB_SYNC_DEFAULT_PRIORITY - Default priority for new tasks
#   GITHUB_SYNC_PRIORITY_LABELS  - JSON object mapping label -> priority
#   GITHUB_SYNC_STATUS_LABELS    - JSON object mapping label -> status char
#   GITHUB_SYNC_CLOSE_ON         - Comma-separated kanban status chars that close issues
#
# Returns: 0 always
load_github_sync_config() {
    local _cfg_enabled="" _cfg_user_ids=""
    local _cfg_label_filter="" _cfg_default_priority=""
    local _cfg_priority_labels="" _cfg_status_labels="" _cfg_close_on=""
    local _cfg_context_events="" _cfg_complexity_labels=""

    # Try project-specific config first, then global
    local extracted=""
    local wiggum_home="${WIGGUM_HOME:-$HOME/.claude/chief-wiggum}"
    local ralph_dir="${RALPH_DIR:-$(pwd)/.ralph}"

    if [ -f "$ralph_dir/config.json" ]; then
        extracted=$(_extract_github_sync_config "$ralph_dir/config.json") || true
    fi

    # If project config didn't have github section, try global
    if [ -z "$extracted" ] && [ -f "$wiggum_home/config/config.json" ]; then
        extracted=$(_extract_github_sync_config "$wiggum_home/config/config.json") || true
    fi

    if [ -n "$extracted" ]; then
        IFS=$'\x1f' read -r _cfg_enabled _cfg_user_ids \
                         _cfg_label_filter _cfg_default_priority \
                         _cfg_priority_labels _cfg_status_labels _cfg_close_on \
                         _cfg_context_events _cfg_complexity_labels \
                         <<< "$extracted"
    fi

    # Apply env var overrides (env wins over config file)
    GITHUB_SYNC_ENABLED="${WIGGUM_GITHUB_ISSUE_SYNC:-${_cfg_enabled:-false}}"
    GITHUB_SYNC_ALLOWED_USER_IDS="${WIGGUM_GITHUB_ALLOWED_USER_IDS:-${_cfg_user_ids:-}}"
    GITHUB_SYNC_LABEL_FILTER="${WIGGUM_GITHUB_LABEL_FILTER:-${_cfg_label_filter:-wiggum}}"
    GITHUB_SYNC_DEFAULT_PRIORITY="${WIGGUM_GITHUB_DEFAULT_PRIORITY:-${_cfg_default_priority:-MEDIUM}}"

    # Priority labels (JSON object, no env override)
    GITHUB_SYNC_PRIORITY_LABELS="${_cfg_priority_labels:-}"
    if [ -z "$GITHUB_SYNC_PRIORITY_LABELS" ] || [ "$GITHUB_SYNC_PRIORITY_LABELS" = "{}" ]; then
        # shellcheck disable=SC2089
        GITHUB_SYNC_PRIORITY_LABELS='{"priority:critical":"CRITICAL","priority:high":"HIGH","priority:medium":"MEDIUM","priority:low":"LOW"}'
    fi

    # Status labels: maps GitHub label name -> kanban status char
    # Uses wiggum: prefix to signal machine-managed labels
    GITHUB_SYNC_STATUS_LABELS="${_cfg_status_labels:-}"
    if [ -z "$GITHUB_SYNC_STATUS_LABELS" ] || [ "$GITHUB_SYNC_STATUS_LABELS" = "{}" ]; then
        # shellcheck disable=SC2089
        GITHUB_SYNC_STATUS_LABELS='{"wiggum:in-progress":"=","wiggum:pending-approval":"P","wiggum:completed":"x","wiggum:failed":"*","wiggum:not-planned":"N"}'
    fi

    # Complexity labels (JSON object, no env override)
    GITHUB_SYNC_COMPLEXITY_LABELS="${_cfg_complexity_labels:-}"
    if [ -z "$GITHUB_SYNC_COMPLEXITY_LABELS" ] || [ "$GITHUB_SYNC_COMPLEXITY_LABELS" = "{}" ]; then
        # shellcheck disable=SC2089
        GITHUB_SYNC_COMPLEXITY_LABELS='{"complexity:high":"HIGH","complexity:medium":"MEDIUM","complexity:low":"LOW"}'
    fi

    # Status chars that close the issue (default: only "x" = completed)
    GITHUB_SYNC_CLOSE_ON="${_cfg_close_on:-x}"

    # Context events: emit events when in-progress task content changes on GitHub
    GITHUB_SYNC_CONTEXT_EVENTS="${WIGGUM_CONTEXT_EVENTS:-${_cfg_context_events:-false}}"

    export GITHUB_SYNC_ENABLED
    export GITHUB_SYNC_ALLOWED_USER_IDS
    export GITHUB_SYNC_LABEL_FILTER
    export GITHUB_SYNC_DEFAULT_PRIORITY
    # shellcheck disable=SC2090
    export GITHUB_SYNC_PRIORITY_LABELS
    # shellcheck disable=SC2090
    export GITHUB_SYNC_STATUS_LABELS
    # shellcheck disable=SC2090
    export GITHUB_SYNC_COMPLEXITY_LABELS
    export GITHUB_SYNC_CLOSE_ON
    export GITHUB_SYNC_CONTEXT_EVENTS
}

# Check if GitHub issue sync is enabled
#
# Returns: 0 if enabled, 1 if disabled
github_sync_is_enabled() {
    [[ "$GITHUB_SYNC_ENABLED" == "true" ]]
}

# Validate that the sync configuration is usable
#
# Checks:
#   - gh CLI is available
#   - At least one allowed user is configured
#   - Label filter is set
#
# Returns: 0 if valid, 1 if invalid (logs errors to stderr)
github_sync_validate_config() {
    local errors=0

    if ! command -v gh &>/dev/null; then
        log_error "GitHub CLI (gh) not found in PATH"
        ((++errors)) || true
    fi

    if [ -z "$GITHUB_SYNC_ALLOWED_USER_IDS" ]; then
        log_error "GitHub sync: no allowed users configured (set allowed_user_ids)"
        ((++errors)) || true
    fi

    if [ -z "$GITHUB_SYNC_LABEL_FILTER" ]; then
        log_error "GitHub sync: label_filter is required"
        ((++errors)) || true
    fi

    [ "$errors" -eq 0 ]
}

# Get the status label name for a kanban status character
#
# Args:
#   status_char - Single kanban status character (e.g., "=", "x", "*")
#
# Returns: label name on stdout, or empty if no mapping
github_sync_get_status_label() {
    local status_char="$1"

    echo "$GITHUB_SYNC_STATUS_LABELS" | \
        jq -r --arg char "$status_char" \
        'to_entries[] | select(.value == $char) | .key // empty' 2>/dev/null || true
}

# Get the kanban status char for a GitHub label
#
# Args:
#   label - GitHub label name (e.g., "wiggum:in-progress")
#
# Returns: status char on stdout (e.g., "="), or empty if no mapping
github_sync_get_status_char() {
    local label="$1"

    echo "$GITHUB_SYNC_STATUS_LABELS" | \
        jq -r --arg label "$label" '.[$label] // empty' 2>/dev/null || true
}

# Check if a kanban status char should close the GitHub issue
#
# Args:
#   status_char - Single kanban status character (e.g., "x", "N")
#
# Returns: 0 if this status should close the issue, 1 otherwise
github_sync_should_close() {
    local status_char="$1"
    local IFS=','
    local char
    for char in $GITHUB_SYNC_CLOSE_ON; do
        [[ "$char" == "$status_char" ]] && return 0
    done
    return 1
}

# Get the priority from GitHub issue labels
#
# Checks labels against GITHUB_SYNC_PRIORITY_LABELS mapping.
# If multiple priority labels exist, returns the highest priority.
#
# Args:
#   labels_json - JSON array of label objects (each with "name" field)
#
# Returns: priority string on stdout (e.g., "HIGH"), or empty if no match
github_sync_get_priority_from_labels() {
    local labels_json="$1"

    # Extract priority from labels using the mapping
    # Priority order: CRITICAL > HIGH > MEDIUM > LOW
    local priority=""
    priority=$(echo "$labels_json" | jq -r --argjson mapping "$GITHUB_SYNC_PRIORITY_LABELS" '
        [.[] | .name as $name | $mapping | to_entries[] | select(.key == $name) | .value] |
        if length == 0 then empty
        else
            # Sort by priority order (CRITICAL=0, HIGH=1, MEDIUM=2, LOW=3)
            map(
                if . == "CRITICAL" then {p: 0, v: .}
                elif . == "HIGH" then {p: 1, v: .}
                elif . == "MEDIUM" then {p: 2, v: .}
                elif . == "LOW" then {p: 3, v: .}
                else {p: 99, v: .}
                end
            ) | sort_by(.p) | .[0].v
        end
    ' 2>/dev/null) || true

    echo "$priority"
}

# Get the complexity from GitHub issue labels
#
# Checks labels against GITHUB_SYNC_COMPLEXITY_LABELS mapping.
# Takes the first match (no ranking — complexity values are not ordered).
#
# Args:
#   labels_json - JSON array of label objects (each with "name" field)
#
# Returns: complexity string on stdout (e.g., "HIGH"), or empty if no match
github_sync_get_complexity_from_labels() {
    local labels_json="$1"

    local complexity=""
    complexity=$(echo "$labels_json" | jq -r --argjson mapping "$GITHUB_SYNC_COMPLEXITY_LABELS" '
        [.[] | .name as $name | $mapping | to_entries[] | select(.key == $name) | .value] |
        if length == 0 then empty
        else .[0]
        end
    ' 2>/dev/null) || true

    echo "$complexity"
}

# Check if a GitHub user is allowed to sync issues
#
# Args:
#   author_id - Numeric GitHub user ID (from issue JSON)
#
# Returns: 0 if allowed, 1 if not
github_sync_is_author_allowed() {
    local author_id="$1"

    # Check user ID (stable across username changes)
    if [ -n "$GITHUB_SYNC_ALLOWED_USER_IDS" ] && [ -n "$author_id" ]; then
        local IFS=','
        local uid
        for uid in $GITHUB_SYNC_ALLOWED_USER_IDS; do
            [[ "$uid" == "$author_id" ]] && return 0
        done
    fi

    return 1
}
