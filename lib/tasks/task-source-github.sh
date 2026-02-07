#!/usr/bin/env bash
# =============================================================================
# task-source-github.sh - GitHub Issues task source adapter
#
# Implements the task-source interface for GitHub Issues as the source of truth.
# Uses gh CLI for all GitHub interactions.
#
# Label conventions:
#   wiggum:task           - Gate label: issue is a Wiggum task
#   wiggum:pending        - Status: pending [ ]
#   wiggum:in-progress    - Status: in-progress [=]
#   wiggum:pending-review - Status: pending approval [P]
#   wiggum:complete       - Status: complete [x]
#   wiggum:failed         - Status: failed [*]
#   wiggum:not-planned    - Status: not planned [N]
#   wiggum:server:$ID     - Ownership: claimed by server $ID
#   priority:critical     - Priority mapping
#   priority:high
#   priority:medium
#   priority:low
#
# This adapter is for WIGGUM_TASK_SOURCE_MODE=github or hybrid.
# =============================================================================
set -euo pipefail

[ -n "${_TASK_SOURCE_GITHUB_LOADED:-}" ] && return 0
_TASK_SOURCE_GITHUB_LOADED=1

# Source dependencies
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/gh-error.sh"

# =============================================================================
# Configuration
# =============================================================================

# Label prefix for Wiggum-specific labels
_GH_LABEL_PREFIX="wiggum:"

# Gate label (required for tasks)
_GH_GATE_LABEL="wiggum:task"

# Status label mappings (status_char -> label)
declare -gA _GH_STATUS_LABELS=(
    [" "]="wiggum:pending"
    ["="]="wiggum:in-progress"
    ["P"]="wiggum:pending-review"
    ["x"]="wiggum:complete"
    ["*"]="wiggum:failed"
    ["N"]="wiggum:not-planned"
)

# Priority label mappings (priority -> label)
declare -gA _GH_PRIORITY_LABELS=(
    ["CRITICAL"]="priority:critical"
    ["HIGH"]="priority:high"
    ["MEDIUM"]="priority:medium"
    ["LOW"]="priority:low"
)

# Reverse priority mapping (label -> priority)
declare -gA _GH_LABEL_PRIORITIES=(
    ["priority:critical"]="CRITICAL"
    ["priority:high"]="HIGH"
    ["priority:medium"]="MEDIUM"
    ["priority:low"]="LOW"
)

# Server label prefix
_GH_SERVER_LABEL_PREFIX="wiggum:server:"

# GitHub API timeout (seconds)
_GH_TIMEOUT="${WIGGUM_GH_TIMEOUT:-30}"

# Cache for issue data (issue_number -> json)
declare -gA _GH_ISSUE_CACHE=()
_GH_CACHE_TIMESTAMP=0
_GH_CACHE_TTL=60  # Cache TTL in seconds

# =============================================================================
# Adapter Initialization
# =============================================================================

# Initialize the GitHub adapter
#
# Verifies gh CLI is available and authenticated.
#
# Args:
#   ralph_dir   - Path to .ralph directory
#   project_dir - Path to project directory
#   server_id   - Server identifier
#
# Returns: 0 on success
_task_source_adapter_init() {
    local ralph_dir="$1"
    # shellcheck disable=SC2034  # Interface parameter, reserved for future use
    local project_dir="$2"
    local server_id="$3"

    # Verify gh CLI
    if ! command -v gh &> /dev/null; then
        log_error "gh CLI not found. Install GitHub CLI: https://cli.github.com/"
        return 1
    fi

    # Verify authentication
    if ! gh auth status &> /dev/null; then
        log_error "gh CLI not authenticated. Run 'gh auth login'"
        return 1
    fi

    log_debug "GitHub adapter initialized: server_id=$server_id"
    return 0
}

# =============================================================================
# Internal: GitHub API Helpers
# =============================================================================

# Fetch issues with the gate label
#
# Args:
#   state - "open", "closed", or "all"
#
# Returns: JSON array on stdout
# Sets: GH_LAST_WAS_NETWORK_ERROR if network error
_github_fetch_issues() {
    local state="${1:-open}"

    GH_LAST_WAS_NETWORK_ERROR=false
    local result exit_code=0
    result=$(timeout "$_GH_TIMEOUT" gh issue list \
        --label "$_GH_GATE_LABEL" \
        --state "$state" \
        --json number,title,body,labels,assignees,state,updatedAt \
        --limit 100 \
        2>&1) || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        if gh_is_network_error "$exit_code" "$result"; then
            # shellcheck disable=SC2034  # Global state for callers to check network errors
            GH_LAST_WAS_NETWORK_ERROR=true
            log_error "$(gh_format_error "$exit_code" "$result" "fetching issues")"
        elif [ "$exit_code" -eq 124 ]; then
            log_error "GitHub issue list timeout"
        else
            log_error "GitHub issue list failed (exit: $exit_code): $result"
        fi
        echo "[]"
        return 1
    fi

    echo "$result"
}

# Refresh issue cache
_github_refresh_cache() {
    local now
    now=$(epoch_now)

    # Check if cache is still valid
    if [ "$_GH_CACHE_TIMESTAMP" -gt 0 ] && \
       [ $((now - _GH_CACHE_TIMESTAMP)) -lt "$_GH_CACHE_TTL" ]; then
        return 0
    fi

    log_debug "Refreshing GitHub issue cache..."
    local issues
    issues=$(_github_fetch_issues "open") || return 1

    # Clear old cache
    _GH_ISSUE_CACHE=()

    # Populate cache
    local count
    count=$(echo "$issues" | jq 'length')
    local i=0
    while [ "$i" -lt "$count" ]; do
        local issue_json number
        issue_json=$(echo "$issues" | jq ".[$i]")
        number=$(echo "$issue_json" | jq -r '.number')
        _GH_ISSUE_CACHE[$number]="$issue_json"
        ((++i))
    done

    _GH_CACHE_TIMESTAMP=$now
    log_debug "Cached $count issues"
}

# Invalidate cache
_github_invalidate_cache() {
    _GH_CACHE_TIMESTAMP=0
}

# Warm a single issue into the cache by number
#
# Fetches the issue from the API and inserts it into the cache so that
# subsequent lookups (e.g. _github_find_issue_by_task_id) can find it
# without waiting for a full cache refresh.
#
# Args:
#   issue_number - GitHub issue number
#
# Returns: 0 on success, 1 on fetch failure
_github_warm_issue() {
    local issue_number="$1"

    local result exit_code=0
    result=$(timeout "$_GH_TIMEOUT" gh issue view "$issue_number" \
        --json number,title,body,labels,assignees,state,updatedAt \
        2>&1) || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        log_debug "Failed to warm issue #$issue_number into cache: $result"
        return 1
    fi

    _GH_ISSUE_CACHE[$issue_number]="$result"
    return 0
}

# Get issue from cache or fetch
#
# Args:
#   issue_number - Issue number
#
# Returns: JSON on stdout
_github_get_issue() {
    local issue_number="$1"

    _github_refresh_cache || true

    if [ -n "${_GH_ISSUE_CACHE[$issue_number]+x}" ]; then
        echo "${_GH_ISSUE_CACHE[$issue_number]}"
        return 0
    fi

    # Fetch single issue if not in cache
    local result exit_code=0
    result=$(timeout "$_GH_TIMEOUT" gh issue view "$issue_number" \
        --json number,title,body,labels,assignees,state,updatedAt \
        2>&1) || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        log_error "Failed to fetch issue #$issue_number: $result"
        echo "null"
        return 1
    fi

    # Add to cache
    _GH_ISSUE_CACHE[$issue_number]="$result"
    echo "$result"
}

# Parse task ID from issue
#
# Looks for pattern **[TASK-ID]** in title or body, or GH-{number}
#
# Args:
#   issue_json - Issue JSON
#
# Returns: task_id on stdout
_github_parse_task_id() {
    local issue_json="$1"

    local number title body
    number=$(echo "$issue_json" | jq -r '.number')
    title=$(echo "$issue_json" | jq -r '.title // ""')
    body=$(echo "$issue_json" | jq -r '.body // ""')

    # Check title for **[TASK-ID]** pattern
    local task_id
    task_id=$(echo "$title" | grep -oE '\*\*\[[A-Za-z]{2,10}-[0-9]{1,4}\]\*\*' | \
              sed 's/\*\*\[\(.*\)\]\*\*/\1/' | head -1)

    if [ -n "$task_id" ]; then
        echo "$task_id"
        return 0
    fi

    # Check body first line for [TASK-ID] pattern
    task_id=$(echo "$body" | head -1 | grep -oE '\[[A-Za-z]{2,10}-[0-9]{1,4}\]' | \
              sed 's/\[\(.*\)\]/\1/' | head -1)

    if [ -n "$task_id" ]; then
        echo "$task_id"
        return 0
    fi

    # Default: use GH-{number}
    echo "GH-$number"
}

# Get status from issue labels
#
# Args:
#   labels_json - Labels JSON array
#
# Returns: status char on stdout
_github_get_status_from_labels() {
    local labels_json="$1"

    # Check each status label
    local status label_name
    for status in " " "=" "P" "x" "*" "N"; do
        label_name="${_GH_STATUS_LABELS[$status]}"
        if echo "$labels_json" | jq -e --arg name "$label_name" \
            'any(.[]; .name == $name)' > /dev/null 2>&1; then
            echo "$status"
            return 0
        fi
    done

    # Default to pending
    echo " "
}

# Get priority from issue labels
#
# Args:
#   labels_json - Labels JSON array
#
# Returns: priority string on stdout (CRITICAL|HIGH|MEDIUM|LOW)
_github_get_priority_from_labels() {
    local labels_json="$1"

    # Check each priority label
    local priority label_name
    for priority in "CRITICAL" "HIGH" "MEDIUM" "LOW"; do
        label_name="${_GH_PRIORITY_LABELS[$priority]}"
        if echo "$labels_json" | jq -e --arg name "$label_name" \
            'any(.[]; .name == $name)' > /dev/null 2>&1; then
            echo "$priority"
            return 0
        fi
    done

    # Default to MEDIUM
    echo "MEDIUM"
}

# Get server owner from labels
#
# Args:
#   labels_json - Labels JSON array
#
# Returns: server_id on stdout, or empty if unclaimed
_github_get_owner_from_labels() {
    local labels_json="$1"

    # Find wiggum:server:* label
    local server_label
    server_label=$(echo "$labels_json" | jq -r \
        --arg prefix "$_GH_SERVER_LABEL_PREFIX" \
        '[.[].name | select(startswith($prefix))] | .[0] // ""')

    if [ -n "$server_label" ]; then
        # Extract server ID from label
        echo "${server_label#"$_GH_SERVER_LABEL_PREFIX"}"
    fi
}

# Parse dependencies from issue body
#
# Looks for "Dependencies: ..." or "Depends on: ..." line
#
# Args:
#   body - Issue body text
#
# Returns: comma-separated deps on stdout, or "none"
_github_parse_dependencies() {
    local body="$1"

    local deps
    deps=$(echo "$body" | grep -iE '^(##\s*)?Dependencies?:|Depends on:' | \
           sed 's/^.*:\s*//' | head -1)

    if [ -z "$deps" ] || [ "$deps" = "none" ] || [ "$deps" = "None" ]; then
        echo "none"
    else
        # Clean up: remove spaces around commas, trim
        echo "$deps" | sed 's/[[:space:]]*,[[:space:]]*/,/g; s/^[[:space:]]*//; s/[[:space:]]*$//'
    fi
}

# =============================================================================
# Core Interface Implementation
# =============================================================================

# Get all tasks with metadata
#
# Returns: Lines of "task_id|status|priority|dependencies|owner" on stdout
_task_source_github_get_all_tasks() {
    local ralph_dir="$1"

    _github_refresh_cache || return 1

    local number issue_json
    for number in "${!_GH_ISSUE_CACHE[@]}"; do
        issue_json="${_GH_ISSUE_CACHE[$number]}"

        local task_id labels_json body
        task_id=$(_github_parse_task_id "$issue_json")
        labels_json=$(echo "$issue_json" | jq '.labels')
        body=$(echo "$issue_json" | jq -r '.body // ""')

        local status priority deps owner
        status=$(_github_get_status_from_labels "$labels_json")
        priority=$(_github_get_priority_from_labels "$labels_json")
        deps=$(_github_parse_dependencies "$body")
        owner=$(_github_get_owner_from_labels "$labels_json")

        echo "$task_id|$status|$priority|$deps|$owner"
    done
}

# Claim a task
#
# Uses assignee + server label for claiming. Verifies ownership after.
#
# Args:
#   task_id   - Task identifier (GH-{number} or custom)
#   server_id - Server identifier
#
# Returns: 0 if claimed, 1 if already claimed or error
_task_source_github_claim_task() {
    local task_id="$1"
    local server_id="$2"

    # Extract issue number from task_id
    local issue_number
    if [[ "$task_id" =~ ^GH-([0-9]+)$ ]]; then
        issue_number="${BASH_REMATCH[1]}"
    else
        # Look up issue number from cache
        issue_number=$(_github_find_issue_by_task_id "$task_id")
        if [ -z "$issue_number" ]; then
            log_error "Cannot find issue for task $task_id"
            return 1
        fi
    fi

    # Check if already claimed by another server
    local current_owner
    current_owner=$(_task_source_github_get_owner "$task_id")
    if [ -n "$current_owner" ] && [ "$current_owner" != "$server_id" ]; then
        log_debug "Task $task_id already claimed by $current_owner"
        return 1
    fi

    log_debug "Claiming task $task_id (issue #$issue_number) for server $server_id"

    # Add assignee
    local result exit_code=0
    result=$(timeout "$_GH_TIMEOUT" gh issue edit "$issue_number" \
        --add-assignee "@me" 2>&1) || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        log_error "Failed to add assignee to issue #$issue_number: $result"
        return 1
    fi

    # Add server label
    local server_label="${_GH_SERVER_LABEL_PREFIX}${server_id}"
    result=$(timeout "$_GH_TIMEOUT" gh issue edit "$issue_number" \
        --add-label "$server_label" 2>&1) || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        log_error "Failed to add server label to issue #$issue_number: $result"
        # Try to rollback assignee
        gh issue edit "$issue_number" --remove-assignee "@me" 2>/dev/null || true
        return 1
    fi

    # Verify we own the task
    _github_invalidate_cache
    sleep 1  # Brief pause for GitHub to update

    local new_owner
    new_owner=$(_task_source_github_get_owner "$task_id")
    if [ "$new_owner" != "$server_id" ]; then
        log_warn "Claim verification failed for $task_id (owner: $new_owner, expected: $server_id)"
        # Concurrent claim - release ours
        gh issue edit "$issue_number" --remove-label "$server_label" 2>/dev/null || true
        return 1
    fi

    log "Claimed task $task_id for server $server_id"

    # Update local claims cache
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
    server_claims_update "$(dirname "$ralph_dir")/.ralph" "$task_id" "add" 2>/dev/null || true
    server_heartbeat_log "$(dirname "$ralph_dir")/.ralph" "$task_id" "claim" 2>/dev/null || true

    return 0
}

# Release a task
#
# Args:
#   task_id   - Task identifier
#   server_id - Server identifier (must match current owner)
#
# Returns: 0 on success
_task_source_github_release_task() {
    local task_id="$1"
    local server_id="$2"

    # Extract issue number
    local issue_number
    if [[ "$task_id" =~ ^GH-([0-9]+)$ ]]; then
        issue_number="${BASH_REMATCH[1]}"
    else
        issue_number=$(_github_find_issue_by_task_id "$task_id")
        [ -n "$issue_number" ] || return 1
    fi

    # Verify we own it
    local current_owner
    current_owner=$(_task_source_github_get_owner "$task_id")
    if [ "$current_owner" != "$server_id" ]; then
        log_debug "Cannot release task $task_id - owned by $current_owner, not $server_id"
        return 1
    fi

    log_debug "Releasing task $task_id"

    # Remove server label
    local server_label="${_GH_SERVER_LABEL_PREFIX}${server_id}"
    gh issue edit "$issue_number" --remove-label "$server_label" 2>/dev/null || true

    # Remove assignee
    gh issue edit "$issue_number" --remove-assignee "@me" 2>/dev/null || true

    # Post release comment
    gh issue comment "$issue_number" \
        --body "<!-- wiggum:release -->
**Server:** $server_id
**Action:** Released task
**Time:** $(iso_now)" 2>/dev/null || true

    _github_invalidate_cache

    # Update local cache
    source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
    server_claims_update "$(dirname "$ralph_dir")/.ralph" "$task_id" "remove" 2>/dev/null || true
    server_heartbeat_log "$(dirname "$ralph_dir")/.ralph" "$task_id" "release" 2>/dev/null || true

    return 0
}

# Set task status
#
# Updates status labels on the issue.
#
# Args:
#   task_id - Task identifier
#   status  - New status character
#
# Returns: 0 on success
_task_source_github_set_status() {
    local task_id="$1"
    local status="$2"

    # Extract issue number
    local issue_number
    if [[ "$task_id" =~ ^GH-([0-9]+)$ ]]; then
        issue_number="${BASH_REMATCH[1]}"
    else
        issue_number=$(_github_find_issue_by_task_id "$task_id")
        [ -n "$issue_number" ] || return 1
    fi

    # Get new status label
    local new_label="${_GH_STATUS_LABELS[$status]:-}"
    if [ -z "$new_label" ]; then
        log_error "Invalid status character: $status"
        return 1
    fi

    log_debug "Setting status of $task_id to '$status' ($new_label)"

    # Remove all existing status labels
    local old_label
    for old_label in "${_GH_STATUS_LABELS[@]}"; do
        gh issue edit "$issue_number" --remove-label "$old_label" 2>/dev/null || true
    done

    # Add new status label
    gh issue edit "$issue_number" --add-label "$new_label" 2>/dev/null || true

    # Close/reopen based on status
    case "$status" in
        "x"|"*"|"N")
            gh issue close "$issue_number" 2>/dev/null || true
            ;;
        " "|"="|"P")
            # Reopen if closed
            local state
            state=$(gh issue view "$issue_number" --json state -q '.state' 2>/dev/null || echo "OPEN")
            if [ "$state" = "CLOSED" ]; then
                gh issue reopen "$issue_number" 2>/dev/null || true
            fi
            ;;
    esac

    _github_invalidate_cache
    return 0
}

# Get task owner
#
# Args:
#   task_id - Task identifier
#
# Returns: server_id on stdout, or empty
_task_source_github_get_owner() {
    local task_id="$1"

    # Extract issue number
    local issue_number
    if [[ "$task_id" =~ ^GH-([0-9]+)$ ]]; then
        issue_number="${BASH_REMATCH[1]}"
    else
        issue_number=$(_github_find_issue_by_task_id "$task_id")
        [ -n "$issue_number" ] || return 0
    fi

    local issue_json
    issue_json=$(_github_get_issue "$issue_number")
    [ "$issue_json" != "null" ] || return 0

    local labels_json
    labels_json=$(echo "$issue_json" | jq '.labels')

    _github_get_owner_from_labels "$labels_json"
}

# Get single task details
#
# Args:
#   task_id - Task identifier
#
# Returns: JSON object on stdout
_task_source_github_get_task() {
    local task_id="$1"

    # Extract issue number
    local issue_number
    if [[ "$task_id" =~ ^GH-([0-9]+)$ ]]; then
        issue_number="${BASH_REMATCH[1]}"
    else
        issue_number=$(_github_find_issue_by_task_id "$task_id")
        [ -n "$issue_number" ] || { echo "null"; return 1; }
    fi

    local issue_json
    issue_json=$(_github_get_issue "$issue_number")
    [ "$issue_json" != "null" ] || { echo "null"; return 1; }

    local labels_json body title
    labels_json=$(echo "$issue_json" | jq '.labels')
    body=$(echo "$issue_json" | jq -r '.body // ""')
    title=$(echo "$issue_json" | jq -r '.title // ""')

    local status priority deps owner
    status=$(_github_get_status_from_labels "$labels_json")
    priority=$(_github_get_priority_from_labels "$labels_json")
    deps=$(_github_parse_dependencies "$body")
    owner=$(_github_get_owner_from_labels "$labels_json")

    # Convert status char to string
    local status_str
    case "$status" in
        " ") status_str="pending" ;;
        "=") status_str="in_progress" ;;
        "P") status_str="pending_approval" ;;
        "x") status_str="complete" ;;
        "*") status_str="failed" ;;
        "N") status_str="not_planned" ;;
        *)   status_str="unknown" ;;
    esac

    jq -n \
        --arg task_id "$task_id" \
        --arg issue_number "$issue_number" \
        --arg status "$status_str" \
        --arg status_char "$status" \
        --arg priority "$priority" \
        --arg dependencies "$deps" \
        --arg title "$title" \
        --arg body "$body" \
        --arg owner "$owner" \
        '{
            task_id: $task_id,
            issue_number: ($issue_number | tonumber),
            status: $status,
            status_char: $status_char,
            priority: $priority,
            dependencies: $dependencies,
            title: $title,
            description: $body,
            owner: (if $owner == "" then null else $owner end)
        }'
}

# Find issue number by task ID
#
# Args:
#   task_id - Task identifier
#
# Returns: issue number on stdout
_github_find_issue_by_task_id() {
    local task_id="$1"

    _github_refresh_cache || return 1

    local number issue_json found_task_id
    for number in "${!_GH_ISSUE_CACHE[@]}"; do
        issue_json="${_GH_ISSUE_CACHE[$number]}"
        found_task_id=$(_github_parse_task_id "$issue_json")
        if [ "$found_task_id" = "$task_id" ]; then
            echo "$number"
            return 0
        fi
    done

    return 1
}

# Check if task is claimable
#
# Args:
#   task_id - Task identifier
#
# Returns: 0 if claimable, 1 if not
_task_source_github_is_claimable() {
    local task_id="$1"

    local task_json
    task_json=$(_task_source_github_get_task "$task_id")
    [ "$task_json" != "null" ] || return 1

    local status owner
    status=$(echo "$task_json" | jq -r '.status_char')
    owner=$(echo "$task_json" | jq -r '.owner // ""')

    # Claimable if pending and no owner
    [ "$status" = " " ] && [ -z "$owner" ]
}

# Get ready tasks
#
# Returns tasks that are pending, have satisfied dependencies, and are not
# claimed by another server.
#
# Args:
#   server_id        - Our server ID
#   ready_since_file - Path to ready-since tracking file
#   aging_factor     - Aging factor for priority calculation
#   sibling_penalty  - Penalty for sibling tasks in progress
#   plan_bonus       - Bonus for tasks with implementation plans
#   dep_bonus        - Bonus per dependent task
#
# Returns: Lines of "effective_pri|task_id" on stdout
_task_source_github_get_ready_tasks() {
    local server_id="$1"
    local ready_since_file="${2:-}"
    local aging_factor="${3:-7}"
    local sibling_penalty="${4:-20000}"
    local plan_bonus="${5:-15000}"
    local dep_bonus="${6:-7000}"

    _github_refresh_cache || return 1

    # Build dependency graph
    declare -A task_deps=()
    declare -A task_status=()
    declare -A task_priority=()
    declare -A task_owner=()

    local number issue_json task_id labels_json body
    for number in "${!_GH_ISSUE_CACHE[@]}"; do
        issue_json="${_GH_ISSUE_CACHE[$number]}"
        task_id=$(_github_parse_task_id "$issue_json")
        labels_json=$(echo "$issue_json" | jq '.labels')
        body=$(echo "$issue_json" | jq -r '.body // ""')

        task_status[$task_id]=$(_github_get_status_from_labels "$labels_json")
        task_priority[$task_id]=$(_github_get_priority_from_labels "$labels_json")
        task_deps[$task_id]=$(_github_parse_dependencies "$body")
        task_owner[$task_id]=$(_github_get_owner_from_labels "$labels_json")
    done

    # Find ready tasks
    for task_id in "${!task_status[@]}"; do
        local status="${task_status[$task_id]}"
        local owner="${task_owner[$task_id]}"

        # Must be pending
        [ "$status" = " " ] || continue

        # Must not be owned by another server
        if [ -n "$owner" ] && [ "$owner" != "$server_id" ]; then
            continue
        fi

        # Check dependencies
        local deps="${task_deps[$task_id]}"
        local deps_satisfied=true
        if [ "$deps" != "none" ] && [ -n "$deps" ]; then
            local remaining="$deps"
            while [ -n "$remaining" ]; do
                local dep="${remaining%%,*}"
                if [ "$dep" = "$remaining" ]; then
                    remaining=""
                else
                    remaining="${remaining#*,}"
                fi
                dep=$(echo "$dep" | xargs)
                [ -z "$dep" ] && continue

                # Check if dep is complete
                local dep_status="${task_status[$dep]:-}"
                if [ "$dep_status" != "x" ]; then
                    deps_satisfied=false
                    break
                fi
            done
        fi

        $deps_satisfied || continue

        # Calculate priority
        local priority="${task_priority[$task_id]}"
        local effective_pri
        case "$priority" in
            CRITICAL) effective_pri=0 ;;
            HIGH)     effective_pri=10000 ;;
            MEDIUM)   effective_pri=20000 ;;
            LOW)      effective_pri=30000 ;;
            *)        effective_pri=20000 ;;
        esac

        # Apply aging if ready-since file provided
        if [ -n "$ready_since_file" ] && [ -f "$ready_since_file" ]; then
            local iters_waiting
            iters_waiting=$(awk -F'|' -v t="$task_id" '$1 == t { print $2 }' "$ready_since_file")
            iters_waiting=${iters_waiting:-0}
            if [ "$aging_factor" -gt 0 ] && [ "$iters_waiting" -gt 0 ]; then
                local aging_bonus=$(( (iters_waiting * 8000) / aging_factor ))
                effective_pri=$(( effective_pri - aging_bonus ))
            fi
        fi

        # Floor at 0
        [ "$effective_pri" -lt 0 ] && effective_pri=0

        echo "$effective_pri|$task_id"
    done | LC_ALL=C sort -t'|' -k1,1n
}

# =============================================================================
# Hybrid Mode Support
# =============================================================================

# Get all tasks (hybrid: merge GitHub + kanban)
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: Lines of "task_id|status|priority|dependencies|owner" on stdout
_task_source_hybrid_get_all_tasks() {
    local ralph_dir="$1"

    # GitHub is authoritative - just use its data
    _task_source_github_get_all_tasks "$ralph_dir"
}

# Get ready tasks (hybrid: use GitHub data with local priority enhancements)
#
# Args:
#   ralph_dir        - Path to .ralph directory
#   server_id        - Our server ID
#   ready_since_file - Path to ready-since tracking file
#   aging_factor     - Aging factor
#   sibling_penalty  - Sibling penalty
#   plan_bonus       - Plan bonus
#   dep_bonus        - Dependency bonus
#
# Returns: Lines of "effective_pri|task_id" on stdout
_task_source_hybrid_get_ready_tasks() {
    local ralph_dir="$1"
    local server_id="$2"
    local ready_since_file="${3:-}"
    local aging_factor="${4:-7}"
    local sibling_penalty="${5:-20000}"
    local plan_bonus="${6:-15000}"
    local dep_bonus="${7:-7000}"

    # Use GitHub for ready tasks
    local github_ready
    github_ready=$(_task_source_github_get_ready_tasks "$server_id" \
        "$ready_since_file" "$aging_factor" "$sibling_penalty" \
        "$plan_bonus" "$dep_bonus")

    # Apply local plan bonus if task has .ralph/plans/<task_id>.md
    echo "$github_ready" | while IFS='|' read -r pri task_id; do
        [ -n "$task_id" ] || continue

        local adjusted_pri="$pri"

        # Check for local implementation plan
        if [ -f "$ralph_dir/plans/${task_id}.md" ]; then
            adjusted_pri=$((adjusted_pri - plan_bonus))
            [ "$adjusted_pri" -lt 0 ] && adjusted_pri=0
        fi

        echo "$adjusted_pri|$task_id"
    done | LC_ALL=C sort -t'|' -k1,1n
}
