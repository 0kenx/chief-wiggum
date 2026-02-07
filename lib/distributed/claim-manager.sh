#!/usr/bin/env bash
# =============================================================================
# claim-manager.sh - Distributed task claiming protocol
#
# Manages atomic task claiming across multiple server instances using GitHub's
# native features for distributed locking:
#   - Issue assignee: Signals "task is being worked on" in GitHub UI
#   - Server label: Identifies which specific server instance owns task
#   - Heartbeat comment: Liveness detection for stale claims
#
# Protocol:
#   1. Check task is unclaimed (no wiggum:server:* label)
#   2. Atomic claim: add assignee + server label
#   3. Verify ownership (re-read issue, confirm server label matches)
#   4. Start heartbeat updates
#
# Recovery:
#   - If heartbeat >threshold old, task considered stale
#   - Any server can reclaim after posting release comment
# =============================================================================
set -euo pipefail

[ -n "${_CLAIM_MANAGER_LOADED:-}" ] && return 0
_CLAIM_MANAGER_LOADED=1

# Source dependencies
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/gh-error.sh"
source "$WIGGUM_HOME/lib/distributed/server-identity.sh"

# =============================================================================
# Configuration
# =============================================================================

# Server label prefix
_CLAIM_SERVER_LABEL_PREFIX="wiggum:server:"

# Heartbeat comment marker
_CLAIM_HEARTBEAT_MARKER="<!-- wiggum:heartbeat -->"

# Default stale threshold (seconds) - 10 minutes
_CLAIM_STALE_THRESHOLD="${SERVER_STALE_THRESHOLD:-600}"

# Claim verification retry delay (seconds)
_CLAIM_VERIFY_DELAY=2

# Claim verification max attempts
_CLAIM_VERIFY_MAX_ATTEMPTS=3

# GitHub API timeout
_CLAIM_GH_TIMEOUT="${WIGGUM_GH_TIMEOUT:-30}"

# =============================================================================
# Core Claiming Functions
# =============================================================================

# Attempt to claim a task
#
# Atomically claims a task using GitHub assignee + server label.
# Verifies ownership after claiming to detect concurrent claims.
#
# Args:
#   issue_number - GitHub issue number
#   server_id    - Server identifier
#   ralph_dir    - Path to .ralph directory (for local state)
#
# Returns: 0 if claimed successfully, 1 if failed
claim_task() {
    local issue_number="$1"
    local server_id="$2"
    local ralph_dir="${3:-}"

    # Check if already claimed by another server
    local current_owner
    current_owner=$(claim_get_owner "$issue_number")
    if [ -n "$current_owner" ]; then
        if [ "$current_owner" = "$server_id" ]; then
            log_debug "Task #$issue_number already claimed by us"
            return 0
        fi
        log_debug "Task #$issue_number already claimed by $current_owner"
        return 1
    fi

    log_debug "Claiming issue #$issue_number for server $server_id"

    # Step 1: Add assignee (signals "claimed" in UI)
    local result exit_code=0
    result=$(timeout "$_CLAIM_GH_TIMEOUT" gh issue edit "$issue_number" \
        --add-assignee "@me" 2>&1) || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        if gh_is_network_error "$exit_code" "$result"; then
            log_warn "Network error claiming issue #$issue_number - will retry"
        else
            log_error "Failed to add assignee to issue #$issue_number: $result"
        fi
        return 1
    fi

    # Step 2: Add server label (identifies which server)
    local server_label="${_CLAIM_SERVER_LABEL_PREFIX}${server_id}"
    exit_code=0
    result=$(timeout "$_CLAIM_GH_TIMEOUT" gh issue edit "$issue_number" \
        --add-label "$server_label" 2>&1) || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        log_error "Failed to add server label to issue #$issue_number: $result"
        # Rollback assignee
        gh issue edit "$issue_number" --remove-assignee "@me" 2>/dev/null || true
        return 1
    fi

    # Step 3: Verify ownership (handle concurrent claims)
    local attempt=1
    while [ "$attempt" -le "$_CLAIM_VERIFY_MAX_ATTEMPTS" ]; do
        sleep "$_CLAIM_VERIFY_DELAY"

        current_owner=$(claim_get_owner "$issue_number")
        if [ "$current_owner" = "$server_id" ]; then
            log "Successfully claimed issue #$issue_number"

            # Update local claims cache
            if [ -n "$ralph_dir" ]; then
                server_claims_update "$ralph_dir" "GH-$issue_number" "add" || true
                server_heartbeat_log "$ralph_dir" "GH-$issue_number" "claim" || true
            fi

            # Post initial heartbeat
            claim_update_heartbeat "$issue_number" "$server_id" "claimed" "" || true

            return 0
        fi

        ((++attempt))
        log_debug "Claim verification attempt $attempt for #$issue_number"
    done

    # Verification failed - concurrent claim detected
    log_warn "Claim verification failed for #$issue_number (owner: $current_owner)"

    # Clean up our label
    gh issue edit "$issue_number" --remove-label "$server_label" 2>/dev/null || true

    return 1
}

# Release a claimed task
#
# Removes ownership labels and posts release comment.
#
# Args:
#   issue_number - GitHub issue number
#   server_id    - Server identifier (must match current owner)
#   ralph_dir    - Path to .ralph directory (optional)
#   reason       - Release reason (optional)
#
# Returns: 0 on success, 1 if not owner
claim_release_task() {
    local issue_number="$1"
    local server_id="$2"
    local ralph_dir="${3:-}"
    local reason="${4:-Released by server}"

    # Verify we own it
    local current_owner
    current_owner=$(claim_get_owner "$issue_number")
    if [ "$current_owner" != "$server_id" ]; then
        log_debug "Cannot release #$issue_number - owned by $current_owner, not $server_id"
        return 1
    fi

    log_debug "Releasing issue #$issue_number"

    # Remove server label
    local server_label="${_CLAIM_SERVER_LABEL_PREFIX}${server_id}"
    gh issue edit "$issue_number" --remove-label "$server_label" 2>/dev/null || true

    # Remove assignee
    gh issue edit "$issue_number" --remove-assignee "@me" 2>/dev/null || true

    # Post release comment
    local release_comment
    release_comment="$_CLAIM_HEARTBEAT_MARKER
**Server:** $server_id
**Action:** Released
**Reason:** $reason
**Time:** $(iso_now)"

    gh issue comment "$issue_number" --body "$release_comment" 2>/dev/null || true

    # Update local cache
    if [ -n "$ralph_dir" ]; then
        server_claims_update "$ralph_dir" "GH-$issue_number" "remove" || true
        server_heartbeat_log "$ralph_dir" "GH-$issue_number" "release" || true
    fi

    log "Released issue #$issue_number"
    return 0
}

# Get current owner of a task
#
# Args:
#   issue_number - GitHub issue number
#
# Returns: server_id on stdout, or empty if unclaimed
claim_get_owner() {
    local issue_number="$1"

    local labels
    labels=$(timeout "$_CLAIM_GH_TIMEOUT" gh issue view "$issue_number" \
        --json labels -q '.labels[].name' 2>/dev/null) || return 0

    # Find server label
    local label
    while IFS= read -r label; do
        if [[ "$label" == "$_CLAIM_SERVER_LABEL_PREFIX"* ]]; then
            echo "${label#"$_CLAIM_SERVER_LABEL_PREFIX"}"
            return 0
        fi
    done <<< "$labels"

    return 0
}

# Check if task is claimed by any server
#
# Args:
#   issue_number - GitHub issue number
#
# Returns: 0 if claimed, 1 if unclaimed
claim_is_claimed() {
    local issue_number="$1"

    local owner
    owner=$(claim_get_owner "$issue_number")
    [ -n "$owner" ]
}

# Verify this server still owns a task
#
# Args:
#   issue_number - GitHub issue number
#   server_id    - Expected server ID
#
# Returns: 0 if we own it, 1 if not
claim_verify_ownership() {
    local issue_number="$1"
    local server_id="$2"

    local current_owner
    current_owner=$(claim_get_owner "$issue_number")
    [ "$current_owner" = "$server_id" ]
}

# =============================================================================
# Heartbeat Functions
# =============================================================================

# Update heartbeat comment on an issue
#
# Creates or updates a pinned comment with server status and pipeline progress.
#
# Args:
#   issue_number   - GitHub issue number
#   server_id      - Server identifier
#   pipeline_step  - Current pipeline step (optional)
#   progress_table - Progress table markdown (optional)
#
# Returns: 0 on success
claim_update_heartbeat() {
    local issue_number="$1"
    local server_id="$2"
    local pipeline_step="${3:-unknown}"
    local progress_table="${4:-}"

    local timestamp
    timestamp=$(iso_now)

    # Build heartbeat comment
    local heartbeat_body
    heartbeat_body="$_CLAIM_HEARTBEAT_MARKER
**Server:** $server_id
**Last Update:** $timestamp
**Pipeline Step:** $pipeline_step"

    if [ -n "$progress_table" ]; then
        heartbeat_body="$heartbeat_body

$progress_table"
    fi

    # Find last heartbeat comment: update only if it belongs to this server
    local last_comment=""
    last_comment=$(timeout "$_CLAIM_GH_TIMEOUT" gh issue view "$issue_number" \
        --json comments \
        --jq '[.comments[] | select(.body | contains("<!-- wiggum:heartbeat -->"))] | last // empty' \
        2>/dev/null) || true

    local comment_id=""
    if [ -n "$last_comment" ]; then
        local comment_server=""
        comment_server=$(echo "$last_comment" | jq -r \
            '.body | capture("\\*\\*Server:\\*\\* (?<s>[^\\n]*)") | .s // empty' 2>/dev/null) || true
        if [ "$comment_server" = "$server_id" ]; then
            comment_id=$(echo "$last_comment" | jq -r '.databaseId // empty' 2>/dev/null) || true
        fi
    fi

    if [ -n "$comment_id" ]; then
        gh api \
            --method PATCH \
            "/repos/{owner}/{repo}/issues/comments/$comment_id" \
            -f body="$heartbeat_body" 2>/dev/null || true
    else
        gh issue comment "$issue_number" --body "$heartbeat_body" 2>/dev/null || true
    fi

    log_debug "Updated heartbeat for issue #$issue_number"
    return 0
}

# Get last heartbeat timestamp for an issue
#
# Args:
#   issue_number - GitHub issue number
#
# Returns: epoch timestamp on stdout, or 0 if no heartbeat
claim_get_heartbeat_time() {
    local issue_number="$1"

    # Get heartbeat comment
    local comment_body
    comment_body=$(timeout "$_CLAIM_GH_TIMEOUT" gh issue view "$issue_number" \
        --json comments \
        --jq '.comments[] | select(.body | contains("<!-- wiggum:heartbeat -->")) | .body' \
        2>/dev/null | tail -1) || true

    [ -n "$comment_body" ] || { echo "0"; return 0; }

    # Extract timestamp
    local timestamp
    timestamp=$(echo "$comment_body" | grep -oE '\*\*Last Update:\*\* [0-9T:+-]+' | \
                sed 's/.*: //' | head -1)

    if [ -n "$timestamp" ]; then
        # Convert ISO to epoch
        epoch_from_iso "$timestamp"
    else
        echo "0"
    fi
}

# Check if a claim is stale (heartbeat too old)
#
# Args:
#   issue_number - GitHub issue number
#   threshold    - Stale threshold in seconds (optional, uses default)
#
# Returns: 0 if stale, 1 if fresh or no heartbeat
claim_is_stale() {
    local issue_number="$1"
    local threshold="${2:-$_CLAIM_STALE_THRESHOLD}"

    local last_heartbeat
    last_heartbeat=$(claim_get_heartbeat_time "$issue_number")
    last_heartbeat="${last_heartbeat:-0}"

    [ "$last_heartbeat" -eq 0 ] && return 1  # No heartbeat = fresh claim (just started)

    local now age
    now=$(epoch_now)
    age=$((now - last_heartbeat))

    [ "$age" -gt "$threshold" ]
}

# =============================================================================
# Batch Operations
# =============================================================================

# Get all claimed tasks for a server
#
# Args:
#   server_id - Server identifier
#
# Returns: Lines of issue numbers on stdout
claim_list_owned() {
    local server_id="$1"

    local server_label="${_CLAIM_SERVER_LABEL_PREFIX}${server_id}"

    timeout "$_CLAIM_GH_TIMEOUT" gh issue list \
        --label "$server_label" \
        --state open \
        --json number \
        --jq '.[].number' 2>/dev/null || true
}

# Release all tasks owned by a server
#
# Useful for graceful shutdown or crash recovery.
#
# Args:
#   server_id - Server identifier
#   ralph_dir - Path to .ralph directory (optional)
#   reason    - Release reason
#
# Returns: 0 on success
claim_release_all() {
    local server_id="$1"
    local ralph_dir="${2:-}"
    local reason="${3:-Server shutdown}"

    local issues
    issues=$(claim_list_owned "$server_id")

    local issue_number
    while IFS= read -r issue_number; do
        [ -n "$issue_number" ] || continue
        claim_release_task "$issue_number" "$server_id" "$ralph_dir" "$reason" || true
    done <<< "$issues"

    log "Released all tasks for server $server_id"
}

# Find stale claims (any server)
#
# Args:
#   threshold - Stale threshold in seconds (optional)
#
# Returns: Lines of "issue_number|owner|age" on stdout
claim_find_stale() {
    local threshold="${1:-$_CLAIM_STALE_THRESHOLD}"

    local gate_label="wiggum:task"
    local issues
    issues=$(timeout "$_CLAIM_GH_TIMEOUT" gh issue list \
        --label "$gate_label" \
        --state open \
        --json number,labels \
        --limit 100 2>/dev/null) || return 0

    local count i
    count=$(echo "$issues" | jq 'length')

    for ((i=0; i<count; i++)); do
        local number labels owner
        number=$(echo "$issues" | jq -r ".[$i].number")
        labels=$(echo "$issues" | jq ".[$i].labels")

        # Find server label
        owner=$(echo "$labels" | jq -r \
            --arg prefix "$_CLAIM_SERVER_LABEL_PREFIX" \
            '[.[].name | select(startswith($prefix))] | .[0] // ""' | \
            sed "s/^$_CLAIM_SERVER_LABEL_PREFIX//")

        [ -n "$owner" ] || continue

        # Check if stale
        if claim_is_stale "$number" "$threshold"; then
            local heartbeat_time now age
            heartbeat_time=$(claim_get_heartbeat_time "$number")
            now=$(epoch_now)
            age=$((now - heartbeat_time))
            echo "$number|$owner|$age"
        fi
    done
}

# =============================================================================
# Recovery Functions
# =============================================================================

# Reclaim a stale task
#
# Forces release of a stale claim and claims for new server.
#
# Args:
#   issue_number  - GitHub issue number
#   old_owner     - Previous owner (for logging)
#   new_server_id - New server to claim
#   ralph_dir     - Path to .ralph directory (optional)
#
# Returns: 0 on success, 1 on failure
claim_force_reclaim() {
    local issue_number="$1"
    local old_owner="$2"
    local new_server_id="$3"
    local ralph_dir="${4:-}"

    log "Force reclaiming stale issue #$issue_number from $old_owner"

    # Remove old server label
    local old_label="${_CLAIM_SERVER_LABEL_PREFIX}${old_owner}"
    gh issue edit "$issue_number" --remove-label "$old_label" 2>/dev/null || true

    # Remove old assignee (can't know who, just remove all)
    # Note: This might remove legitimate assignees - but stale claims need cleanup
    local assignees
    assignees=$(gh issue view "$issue_number" --json assignees --jq '.assignees[].login' 2>/dev/null) || true
    while IFS= read -r assignee; do
        [ -n "$assignee" ] || continue
        gh issue edit "$issue_number" --remove-assignee "$assignee" 2>/dev/null || true
    done <<< "$assignees"

    # Post takeover comment
    gh issue comment "$issue_number" --body \
"$_CLAIM_HEARTBEAT_MARKER
**Action:** Stale claim recovery
**Previous Owner:** $old_owner
**New Owner:** $new_server_id
**Time:** $(iso_now)

Previous claim was stale (no heartbeat). Reclaiming for new server." 2>/dev/null || true

    # Claim for new server
    claim_task "$issue_number" "$new_server_id" "$ralph_dir"
}
