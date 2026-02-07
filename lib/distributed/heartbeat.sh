#!/usr/bin/env bash
# =============================================================================
# heartbeat.sh - Distributed worker heartbeat service
#
# Manages heartbeat updates for claimed tasks to indicate liveness.
# Other servers use heartbeat age to detect stale claims.
#
# Heartbeat comment format:
#   <!-- wiggum:heartbeat -->
#   **Server:** $SERVER_ID
#   **Last Update:** 2026-02-06T10:30:00Z
#   **Pipeline:** default | **Step:** software-engineer (3/8)
#   **Task:** TASK-001
#
#   | Step | Duration | Result |
#   |------|----------|--------|
#   | plan-mode | 2m 15s | PASS |
#   | software-engineer | 5m 32s | running... |
#
# Service integration:
#   - Called periodically by orchestrator (default: every 3 minutes)
#   - Updates heartbeat for all tasks this server owns
#   - Includes pipeline progress for visibility
# =============================================================================
set -euo pipefail

[ -n "${_HEARTBEAT_LOADED:-}" ] && return 0
_HEARTBEAT_LOADED=1

# Source dependencies
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/distributed/server-identity.sh"
source "$WIGGUM_HOME/lib/distributed/claim-manager.sh"

# =============================================================================
# Configuration
# =============================================================================

# Default heartbeat interval (seconds)
_HEARTBEAT_INTERVAL="${SERVER_HEARTBEAT_INTERVAL:-180}"

# Heartbeat comment marker
_HEARTBEAT_MARKER="<!-- wiggum:heartbeat -->"

# Last heartbeat timestamp (per task)
declare -gA _HEARTBEAT_LAST=()

# =============================================================================
# Core Functions
# =============================================================================

# Update heartbeat for a specific task
#
# Args:
#   issue_number  - GitHub issue number
#   server_id     - Server identifier
#   ralph_dir     - Path to .ralph directory
#   task_id       - Task ID (for worker lookup)
#
# Returns: 0 on success
heartbeat_update_task() {
    local issue_number="$1"
    local server_id="$2"
    local ralph_dir="$3"
    local task_id="$4"

    # Skip if server_id is empty (prevents ghost heartbeats)
    if [ -z "$server_id" ]; then
        log_warn "heartbeat: skipping #$issue_number - empty server_id (pid=$$ ppid=$PPID caller=${FUNCNAME[1]:-?})"
        return 1
    fi

    # Find worker directory for this task
    local worker_dir=""
    if [ -d "$ralph_dir/workers" ]; then
        worker_dir=$(find "$ralph_dir/workers" -maxdepth 1 -type d -name "worker-${task_id}-*" 2>/dev/null | head -1)
    fi

    # Get pipeline status
    local pipeline_name="default"
    local step_id="unknown"
    local step_idx=0
    local step_count=1
    local progress_table=""

    if [ -n "$worker_dir" ] && [ -f "$worker_dir/pipeline-config.json" ]; then
        pipeline_name=$(jq -r '.pipeline.name // "default"' "$worker_dir/pipeline-config.json" 2>/dev/null)
        step_id=$(jq -r '.current.step_id // "unknown"' "$worker_dir/pipeline-config.json" 2>/dev/null)
        step_idx=$(jq -r '.current.step_idx // 0' "$worker_dir/pipeline-config.json" 2>/dev/null)
        step_count=$(jq -r '.steps | length' "$worker_dir/pipeline-config.json" 2>/dev/null)

        [ "$pipeline_name" = "null" ] && pipeline_name="default"
        [ "$step_id" = "null" ] && step_id="unknown"
        step_idx="${step_idx:-0}"
        step_count="${step_count:-1}"

        # Build progress table from results
        progress_table=$(heartbeat_build_progress_table "$worker_dir")
    fi

    local timestamp
    timestamp=$(iso_now)

    # Build heartbeat comment
    local heartbeat_body
    heartbeat_body="$_HEARTBEAT_MARKER
**Server:** $server_id
**Last Update:** $timestamp
**Pipeline:** $pipeline_name | **Step:** $step_id ($((step_idx + 1))/$step_count)
**Task:** $task_id"

    if [ -n "$progress_table" ]; then
        heartbeat_body="$heartbeat_body

$progress_table"
    fi

    # Find last heartbeat comment: update only if it belongs to this server,
    # otherwise create a new one (don't overwrite another server's heartbeat)
    local last_comment=""
    last_comment=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh issue view "$issue_number" \
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

            # Skip if this server's last heartbeat was within 60 seconds (server-side dedup)
            local comment_updated_at=""
            comment_updated_at=$(echo "$last_comment" | jq -r '.updatedAt // empty' 2>/dev/null) || true
            if [ -n "$comment_updated_at" ]; then
                local comment_epoch=0
                comment_epoch=$(date -d "$comment_updated_at" +%s 2>/dev/null) || \
                    comment_epoch=$(date -jf "%Y-%m-%dT%H:%M:%SZ" "$comment_updated_at" +%s 2>/dev/null) || true
                comment_epoch="${comment_epoch:-0}"
                local now_epoch
                now_epoch=$(epoch_now)
                if [ "$comment_epoch" -gt 0 ] && [ $((now_epoch - comment_epoch)) -lt 60 ]; then
                    log_debug "heartbeat: skipping #$issue_number - last update ${comment_updated_at} was <60s ago (pid=$$)"
                    return 0
                fi
            fi
        fi
    fi

    if [ -n "$comment_id" ]; then
        gh api \
            --method PATCH \
            "/repos/{owner}/{repo}/issues/comments/$comment_id" \
            -f body="$heartbeat_body" 2>/dev/null || {
            log_warn "Failed to update heartbeat comment for #$issue_number"
            return 1
        }
    else
        gh issue comment "$issue_number" --body "$heartbeat_body" 2>/dev/null || {
            log_warn "Failed to create heartbeat comment for #$issue_number"
            return 1
        }
    fi

    _HEARTBEAT_LAST[$issue_number]=$(epoch_now)
    log_debug "Updated heartbeat for issue #$issue_number (step: $step_id)"
    return 0
}

# Build progress table from worker results
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: markdown table on stdout
heartbeat_build_progress_table() {
    local worker_dir="$1"

    [ -d "$worker_dir/results" ] || return 0

    local table="| Step | Duration | Result |
|------|----------|--------|"

    # Get pipeline steps (steps is an object keyed by step_id, not an array)
    local steps
    steps=$(jq -r '.steps | keys_unsorted[]' "$worker_dir/pipeline-config.json" 2>/dev/null) || return 0

    local current_step
    current_step=$(jq -r '.current.step_id // ""' "$worker_dir/pipeline-config.json" 2>/dev/null)

    while IFS= read -r step; do
        [ -n "$step" ] || continue

        # Find result file for this step
        local result_file
        result_file=$(find "$worker_dir/results" -name "*-${step}-result.json" 2>/dev/null | sort -r | head -1)

        local duration="--"
        local result="pending"

        if [ "$step" = "$current_step" ]; then
            # Currently running
            local start_time
            if [ -f "$worker_dir/step-start-time" ]; then
                start_time=$(cat "$worker_dir/step-start-time" 2>/dev/null)
                start_time="${start_time:-0}"
                if [ "$start_time" -gt 0 ]; then
                    local elapsed=$(( $(epoch_now) - start_time ))
                    duration=$(heartbeat_format_duration "$elapsed")
                fi
            fi
            result="running..."
        elif [ -f "$result_file" ]; then
            # Completed
            result=$(jq -r '.outputs.gate_result // "UNKNOWN"' "$result_file" 2>/dev/null)
            local elapsed_ms
            elapsed_ms=$(jq -r '.elapsed_ms // 0' "$result_file" 2>/dev/null)
            elapsed_ms="${elapsed_ms:-0}"
            duration=$(heartbeat_format_duration $((elapsed_ms / 1000)))
        fi

        table="$table
| $step | $duration | $result |"
    done <<< "$steps"

    echo "$table"
}

# Format duration in human-readable form
#
# Args:
#   seconds - Duration in seconds
#
# Returns: formatted string (e.g., "5m 32s")
heartbeat_format_duration() {
    local seconds="$1"
    seconds="${seconds:-0}"

    if [ "$seconds" -lt 60 ]; then
        echo "${seconds}s"
    elif [ "$seconds" -lt 3600 ]; then
        local min=$((seconds / 60))
        local sec=$((seconds % 60))
        echo "${min}m ${sec}s"
    else
        local hrs=$((seconds / 3600))
        local min=$(( (seconds % 3600) / 60 ))
        echo "${hrs}h ${min}m"
    fi
}

# =============================================================================
# Service Functions
# =============================================================================

# Update heartbeats for all owned tasks
#
# Called by orchestrator periodic service.
#
# Args:
#   ralph_dir - Path to .ralph directory
#   server_id - Server identifier
#
# Returns: 0 on success
heartbeat_update_all() {
    local ralph_dir="$1"
    local server_id="$2"

    log_debug "heartbeat_update_all: pid=$$ server_id='$server_id' caller=${FUNCNAME[1]:-?}"

    # Get all tasks we own
    local owned_issues
    owned_issues=$(claim_list_owned "$server_id")

    local updated=0
    local -A _processed_issues=()
    local issue_number
    while IFS= read -r issue_number; do
        [ -n "$issue_number" ] || continue

        # Derive task_id from issue
        local task_id="GH-$issue_number"

        # Check for step-completed event to force immediate update
        local worker_dir=""
        if [ -d "$ralph_dir/workers" ]; then
            worker_dir=$(find "$ralph_dir/workers" -maxdepth 1 -type d \
                -name "worker-${task_id}-*" 2>/dev/null | head -1)
        fi
        if [ -n "$worker_dir" ] && [ -f "$worker_dir/step-completed-event" ]; then
            _HEARTBEAT_LAST[$issue_number]=0
            rm -f "$worker_dir/step-completed-event"
        fi

        # Check if we need to update (throttle to avoid API spam)
        local last="${_HEARTBEAT_LAST[$issue_number]:-0}"
        local now
        now=$(epoch_now)

        if [ $((now - last)) -lt "$_HEARTBEAT_INTERVAL" ]; then
            continue
        fi

        if heartbeat_update_task "$issue_number" "$server_id" "$ralph_dir" "$task_id"; then
            ((++updated))
        fi
        _processed_issues[$issue_number]=1
    done <<< "$owned_issues"

    # Also cover workers in failure-recovery (issues are closed, so
    # claim_list_owned misses them since it filters --state open)
    if [ -d "$ralph_dir/workers" ] && [ -f "$ralph_dir/github-sync-state.json" ]; then
        local recovery_dir
        while IFS= read -r recovery_dir; do
            [ -n "$recovery_dir" ] || continue
            [ -d "$recovery_dir" ] || continue

            # Extract task_id from worker directory name (worker-GH-42-1234567890 → GH-42)
            local dir_name
            dir_name=$(basename "$recovery_dir")
            local recovery_task_id
            recovery_task_id=$(echo "$dir_name" | sed -E 's/^worker-([A-Za-z]+-[0-9]+)-.+$/\1/')
            [ -n "$recovery_task_id" ] || continue

            # Look up issue number from sync state
            local entry
            entry=$(jq -r --arg tid "$recovery_task_id" \
                '.issues[$tid] // null' "$ralph_dir/github-sync-state.json" 2>/dev/null)
            [ "$entry" != "null" ] && [ -n "$entry" ] || continue

            local recovery_issue
            recovery_issue=$(echo "$entry" | jq -r '.issue_number')
            [ -n "$recovery_issue" ] && [ "$recovery_issue" != "null" ] || continue

            # Skip if already processed by the claim loop above
            [ -z "${_processed_issues[$recovery_issue]+x}" ] || continue

            # Check for step-completed event
            if [ -f "$recovery_dir/step-completed-event" ]; then
                _HEARTBEAT_LAST[$recovery_issue]=0
                rm -f "$recovery_dir/step-completed-event"
            fi

            # Throttle check
            local rlast="${_HEARTBEAT_LAST[$recovery_issue]:-0}"
            local rnow
            rnow=$(epoch_now)
            if [ $((rnow - rlast)) -lt "$_HEARTBEAT_INTERVAL" ]; then
                continue
            fi

            if heartbeat_update_task "$recovery_issue" "$server_id" "$ralph_dir" "$recovery_task_id"; then
                ((++updated))
            fi
        done < <(find "$ralph_dir/workers" -maxdepth 2 -name "recovery-in-progress" -exec dirname {} \; 2>/dev/null)
    fi

    if [ "$updated" -gt 0 ]; then
        log_debug "Updated $updated heartbeat(s)"
    fi

    return 0
}

# Check if heartbeat is needed for a task
#
# Args:
#   issue_number - GitHub issue number
#
# Returns: 0 if update needed, 1 if recent
heartbeat_needs_update() {
    local issue_number="$1"

    local last="${_HEARTBEAT_LAST[$issue_number]:-0}"
    local now
    now=$(epoch_now)

    [ $((now - last)) -ge "$_HEARTBEAT_INTERVAL" ]
}

# Force heartbeat update for a specific task
#
# Use when significant events occur (step change, completion).
#
# Args:
#   issue_number - GitHub issue number
#   server_id    - Server identifier
#   ralph_dir    - Path to .ralph directory
#   task_id      - Task ID
#
# Returns: 0 on success
heartbeat_force_update() {
    local issue_number="$1"
    local server_id="$2"
    local ralph_dir="$3"
    local task_id="$4"

    # Clear last update time to force update
    _HEARTBEAT_LAST[$issue_number]=0

    heartbeat_update_task "$issue_number" "$server_id" "$ralph_dir" "$task_id"
}

# =============================================================================
# Startup/Shutdown
# =============================================================================

# Initialize heartbeat tracking for existing claims
#
# Called at orchestrator startup to resume heartbeats.
#
# Args:
#   ralph_dir - Path to .ralph directory
#   server_id - Server identifier
#
# Returns: 0 on success
heartbeat_init() {
    local ralph_dir="$1"
    local server_id="$2"

    _HEARTBEAT_LAST=()

    # Update heartbeat immediately for all owned tasks
    heartbeat_update_all "$ralph_dir" "$server_id"

    log "Heartbeat service initialized for server $server_id"
}

# Cleanup heartbeats on shutdown
#
# Posts final heartbeat with shutdown notice.
#
# Args:
#   ralph_dir - Path to .ralph directory
#   server_id - Server identifier
#
# Returns: 0 on success
heartbeat_shutdown() {
    local ralph_dir="$1"
    local server_id="$2"

    local owned_issues
    owned_issues=$(claim_list_owned "$server_id")

    while IFS= read -r issue_number; do
        [ -n "$issue_number" ] || continue

        # Post shutdown notice
        local shutdown_body
        shutdown_body="$_HEARTBEAT_MARKER
**Server:** $server_id
**Last Update:** $(iso_now)
**Status:** Server shutting down

Tasks will be released. Other servers may claim after stale threshold."

        gh issue comment "$issue_number" --body "$shutdown_body" 2>/dev/null || true
    done <<< "$owned_issues"

    log "Heartbeat shutdown complete"
}
