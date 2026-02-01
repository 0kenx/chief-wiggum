#!/usr/bin/env bash
# resume-state.sh - Per-worker resume state tracking
#
# Tracks resume attempts, cooldown periods, and terminal states for each worker.
# State file: $worker_dir/resume-state.json
#
# Used by:
#   - bin/wiggum-resume: updates state after each resume decision
#   - lib/scheduler/scheduler.sh: filters workers by state (terminal, cooling, max attempts)
set -euo pipefail

# Prevent double-sourcing
[ -n "${_RESUME_STATE_LOADED:-}" ] && return 0
_RESUME_STATE_LOADED=1

source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"

# Read resume state JSON from worker directory
#
# Creates default state if file doesn't exist.
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: JSON string on stdout
resume_state_read() {
    local worker_dir="$1"
    local state_file="$worker_dir/resume-state.json"

    if [ -f "$state_file" ]; then
        cat "$state_file"
    else
        # Return default state
        jq -n '{
            attempt_count: 0,
            max_attempts: 5,
            last_attempt_at: 0,
            cooldown_until: 0,
            terminal: false,
            terminal_reason: "",
            history: []
        }'
    fi
}

# Write resume state JSON to worker directory (atomic)
#
# Args:
#   worker_dir  - Worker directory path
#   json_string - JSON content to write
resume_state_write() {
    local worker_dir="$1"
    local json_string="$2"
    local state_file="$worker_dir/resume-state.json"
    local tmp_file="${state_file}.tmp"

    echo "$json_string" > "$tmp_file"
    mv "$tmp_file" "$state_file"
}

# Increment attempt count and append to history
#
# Args:
#   worker_dir - Worker directory path
#   decision   - Decision string (COMPLETE, RETRY, ABORT, DEFER)
#   pipeline   - Pipeline name (or empty)
#   step       - Step ID (or empty)
#   reason     - Human-readable reason
resume_state_increment() {
    local worker_dir="$1"
    local decision="$2"
    local pipeline="${3:-}"
    local step="${4:-}"
    local reason="${5:-}"

    local now
    now=$(epoch_now)

    load_resume_config

    local state
    state=$(resume_state_read "$worker_dir")

    state=$(echo "$state" | jq \
        --arg decision "$decision" \
        --arg pipeline "$pipeline" \
        --arg step "$step" \
        --arg reason "$reason" \
        --argjson now "$now" \
        --argjson max_attempts "${MAX_RESUME_ATTEMPTS:-5}" \
        '.attempt_count += 1
        | .last_attempt_at = $now
        | .max_attempts = $max_attempts
        | .history += [{
            at: $now,
            decision: $decision,
            pipeline: (if $pipeline == "" then null else $pipeline end),
            step: (if $step == "" then null else $step end),
            reason: (if $reason == "" then null else $reason end)
        }]')

    resume_state_write "$worker_dir" "$state"
}

# Set terminal state (COMPLETE or ABORT finalized)
#
# Args:
#   worker_dir - Worker directory path
#   reason     - Why the state is terminal
resume_state_set_terminal() {
    local worker_dir="$1"
    local reason="${2:-}"

    local state
    state=$(resume_state_read "$worker_dir")

    state=$(echo "$state" | jq \
        --arg reason "$reason" \
        '.terminal = true | .terminal_reason = $reason')

    resume_state_write "$worker_dir" "$state"
}

# Set cooldown period (DEFER)
#
# Args:
#   worker_dir - Worker directory path
#   seconds    - Cooldown duration in seconds
resume_state_set_cooldown() {
    local worker_dir="$1"
    local seconds="$2"

    local now
    now=$(epoch_now)
    local until=$((now + seconds))

    local state
    state=$(resume_state_read "$worker_dir")

    state=$(echo "$state" | jq \
        --argjson until "$until" \
        '.cooldown_until = $until')

    resume_state_write "$worker_dir" "$state"
}

# Check if worker is in terminal state
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: 0 if terminal, 1 if not (or file missing)
resume_state_is_terminal() {
    local worker_dir="$1"
    local state_file="$worker_dir/resume-state.json"

    [ -f "$state_file" ] || return 1

    local terminal
    terminal=$(jq -r '.terminal // false' "$state_file" 2>/dev/null)
    [ "$terminal" = "true" ]
}

# Check if worker is in cooldown period
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: 0 if cooling down, 1 if not (or file missing/expired)
resume_state_is_cooling() {
    local worker_dir="$1"
    local state_file="$worker_dir/resume-state.json"

    [ -f "$state_file" ] || return 1

    local cooldown_until
    cooldown_until=$(jq -r '.cooldown_until // 0' "$state_file" 2>/dev/null)
    cooldown_until="${cooldown_until:-0}"

    local now
    now=$(epoch_now)

    [ "$cooldown_until" -gt "$now" ]
}

# Get resume attempt count
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: attempt count on stdout (0 if no file)
resume_state_attempts() {
    local worker_dir="$1"
    local state_file="$worker_dir/resume-state.json"

    if [ -f "$state_file" ]; then
        local count
        count=$(jq -r '.attempt_count // 0' "$state_file" 2>/dev/null)
        count="${count:-0}"
        echo "$count"
    else
        echo "0"
    fi
}

# Check if max resume attempts exceeded
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: 0 if attempts >= max_attempts, 1 otherwise
resume_state_max_exceeded() {
    local worker_dir="$1"
    local state_file="$worker_dir/resume-state.json"

    [ -f "$state_file" ] || return 1

    load_resume_config

    local attempts max
    attempts=$(jq -r '.attempt_count // 0' "$state_file" 2>/dev/null)
    attempts="${attempts:-0}"
    max=$(jq -r '.max_attempts // 5' "$state_file" 2>/dev/null)
    max="${max:-${MAX_RESUME_ATTEMPTS:-5}}"

    [ "$attempts" -ge "$max" ]
}
