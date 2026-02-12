#!/usr/bin/env bash
# effect-outbox.sh - Durable effect tracking for crash-safe transitions
#
# Implements an "outbox pattern" for lifecycle effects. Before executing effects,
# record them as pending; after successful execution, mark complete. On restart,
# replay any pending effects to achieve eventual consistency.
#
# This addresses the TLA+ model's identification of mid-transition crash windows
# where state is updated but effects are not applied (MidCrashMergeSucceeded,
# MidCrashMergeConflict, MidCrashFixPass).
#
# File: worker_dir/pending-effects.json
# Format:
# {
#   "pending": [
#     {"id": "uuid", "effect": "sync_github", "args": [...], "recorded_at": "..."}
#   ],
#   "completed": ["uuid1", "uuid2"]
# }
set -euo pipefail

[ -n "${_EFFECT_OUTBOX_LOADED:-}" ] && return 0
_EFFECT_OUTBOX_LOADED=1

source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"

# Record effects as pending before execution
#
# Args:
#   worker_dir  - Worker directory path
#   effects_csv - Comma-separated list of effect names
#   args_json   - JSON object with effect arguments
#
# Returns: echoes batch_id for completion tracking
outbox_record_pending() {
    local worker_dir="$1"
    local effects_csv="$2"
    local args_json="${3:-'{}'}"

    local outbox_file="$worker_dir/pending-effects.json"
    local batch_id
    batch_id="batch-$(epoch_now)-$$"

    # Initialize outbox if needed
    if [ ! -f "$outbox_file" ]; then
        echo '{"pending":[],"completed":[]}' > "$outbox_file"
    fi

    # Parse effects and create pending entries
    local timestamp
    timestamp=$(iso_now)

    IFS=',' read -ra effect_list <<< "$effects_csv"
    for effect_name in "${effect_list[@]}"; do
        [ -z "$effect_name" ] && continue

        local entry_id="${batch_id}-${effect_name}"

        jq --arg id "$entry_id" \
           --arg effect "$effect_name" \
           --arg batch "$batch_id" \
           --argjson args "$args_json" \
           --arg ts "$timestamp" \
           '.pending += [{id: $id, batch: $batch, effect: $effect, args: $args, recorded_at: $ts}]' \
           "$outbox_file" > "$outbox_file.tmp" && mv "$outbox_file.tmp" "$outbox_file"
    done

    echo "$batch_id"
}

# Mark a single effect as completed
#
# Args:
#   worker_dir - Worker directory path
#   entry_id   - Effect entry ID from pending list
outbox_mark_completed() {
    local worker_dir="$1"
    local entry_id="$2"

    local outbox_file="$worker_dir/pending-effects.json"
    [ -f "$outbox_file" ] || return 0

    jq --arg id "$entry_id" '
        .pending = [.pending[] | select(.id != $id)] |
        .completed += [$id]
    ' "$outbox_file" > "$outbox_file.tmp" && mv "$outbox_file.tmp" "$outbox_file"
}

# Mark all effects in a batch as completed
#
# Args:
#   worker_dir - Worker directory path
#   batch_id   - Batch ID from outbox_record_pending
outbox_mark_batch_completed() {
    local worker_dir="$1"
    local batch_id="$2"

    local outbox_file="$worker_dir/pending-effects.json"
    [ -f "$outbox_file" ] || return 0

    jq --arg batch "$batch_id" '
        (.pending | map(select(.batch == $batch) | .id)) as $ids |
        .pending = [.pending[] | select(.batch != $batch)] |
        .completed += $ids
    ' "$outbox_file" > "$outbox_file.tmp" && mv "$outbox_file.tmp" "$outbox_file"
}

# Get pending effects for replay
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: JSON array of pending effect entries
outbox_get_pending() {
    local worker_dir="$1"

    local outbox_file="$worker_dir/pending-effects.json"
    [ -f "$outbox_file" ] || { echo "[]"; return 0; }

    jq '.pending // []' "$outbox_file"
}

# Check if there are pending effects
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: 0 if pending effects exist, 1 otherwise
outbox_has_pending() {
    local worker_dir="$1"

    local outbox_file="$worker_dir/pending-effects.json"
    [ -f "$outbox_file" ] || return 1

    local count
    count=$(jq '.pending | length' "$outbox_file" 2>/dev/null)
    count="${count:-0}"

    [ "$count" -gt 0 ]
}

# Replay pending effects for a worker
#
# Executes all pending effects that were recorded but not completed.
# Effects are executed via the lifecycle effect runner.
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: Number of effects replayed
outbox_replay_pending() {
    local worker_dir="$1"

    local outbox_file="$worker_dir/pending-effects.json"
    [ -f "$outbox_file" ] || return 0

    local pending
    pending=$(jq -c '.pending[]' "$outbox_file" 2>/dev/null) || return 0

    local replayed=0
    while IFS= read -r entry; do
        [ -z "$entry" ] && continue

        local entry_id effect_name args_json
        entry_id=$(echo "$entry" | jq -r '.id')
        effect_name=$(echo "$entry" | jq -r '.effect')
        args_json=$(echo "$entry" | jq -c '.args // {}')

        log_debug "outbox: replaying effect '$effect_name' (id: $entry_id)"

        # Execute the effect via lifecycle runner if available
        if declare -F _lifecycle_run_single_effect &>/dev/null; then
            if _lifecycle_run_single_effect "$effect_name" "$worker_dir" "$args_json"; then
                outbox_mark_completed "$worker_dir" "$entry_id"
                ((++replayed)) || true
            else
                log_warn "outbox: failed to replay effect '$effect_name' for $entry_id"
            fi
        else
            # Runner unavailable — leave effect pending for future replay.
            # Don't mark complete: the runner may recover on next restart.
            # Replay only runs at startup so this won't cause a tight loop.
            log_warn "outbox: no effect runner available, skipping '$effect_name' (stays pending)"
        fi
    done <<< "$pending"

    echo "$replayed"
}

# Clean up completed entries to prevent unbounded growth
#
# Keeps only the most recent 100 completed entries.
#
# Args:
#   worker_dir - Worker directory path
outbox_cleanup_completed() {
    local worker_dir="$1"

    local outbox_file="$worker_dir/pending-effects.json"
    [ -f "$outbox_file" ] || return 0

    # Keep only recent completed entries (limit to 100)
    jq '.completed = (.completed | .[-100:])' "$outbox_file" > "$outbox_file.tmp" \
        && mv "$outbox_file.tmp" "$outbox_file"
}

# Clear the outbox entirely (for testing or terminal state cleanup)
#
# Args:
#   worker_dir - Worker directory path
outbox_clear() {
    local worker_dir="$1"

    rm -f "$worker_dir/pending-effects.json"
}
