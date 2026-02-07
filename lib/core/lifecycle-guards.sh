#!/usr/bin/env bash
# lifecycle-guards.sh - Guard predicate functions for lifecycle transitions
#
# Each guard returns 0 (pass) or 1 (fail). When multiple transitions share
# the same event+from state, the engine evaluates guards in spec order.
# The first transition whose guard passes wins; the last transition
# (no guard) acts as the default/fallback.
set -euo pipefail

[ -n "${_LIFECYCLE_GUARDS_LOADED:-}" ] && return 0
_LIFECYCLE_GUARDS_LOADED=1

source "$WIGGUM_HOME/lib/worker/git-state.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"

# Guard: merge attempts below maximum
#
# Args:
#   worker_dir - Worker directory path
#   data_json  - Event data (unused)
#
# Returns: 0 if merge_attempts < MAX_MERGE_ATTEMPTS, 1 otherwise
_guard_merge_attempts_lt_max() {
    local worker_dir="$1"
    local attempts
    attempts=$(git_state_get_merge_attempts "$worker_dir")
    attempts="${attempts:-0}"
    [ "$attempts" -lt "${MAX_MERGE_ATTEMPTS:-3}" ]
}

# Guard: recovery attempts below maximum
#
# Args:
#   worker_dir - Worker directory path
#   data_json  - Event data (unused)
#
# Returns: 0 if recovery_attempts < WIGGUM_MAX_RECOVERY_ATTEMPTS, 1 otherwise
_guard_recovery_attempts_lt_max() {
    local worker_dir="$1"
    local recovery
    recovery=$(git_state_get_recovery_attempts "$worker_dir")
    recovery="${recovery:-0}"
    [ "$recovery" -lt "${WIGGUM_MAX_RECOVERY_ATTEMPTS:-2}" ]
}

# Guard: rebase onto origin/main succeeds
#
# Attempts to rebase the workspace branch onto origin/main and force-push.
# This guard has a side effect (the rebase+push), which is intentional:
# if the guard passes, the branch is updated and ready for merge retry.
# If it fails, the rebase is aborted and no changes persist.
#
# Args:
#   worker_dir - Worker directory path
#   data_json  - Event data (expects .workspace field)
#
# Returns: 0 if rebase+push succeeded, 1 otherwise
_guard_rebase_succeeded() {
    local worker_dir="$1"
    local data_json="${2:-'{}'}"

    local workspace=""
    if [ "$data_json" != "'{}'" ] && [ "$data_json" != "{}" ]; then
        workspace=$(echo "$data_json" | jq -r '.workspace // empty' 2>/dev/null)
    fi
    [ -n "$workspace" ] || workspace="$worker_dir/workspace"
    [ -d "$workspace" ] || return 1

    # Fetch latest main
    git -C "$workspace" fetch origin main 2>/dev/null || return 1

    # Attempt rebase
    local rebase_exit=0
    git -C "$workspace" rebase origin/main 2>/dev/null || rebase_exit=$?

    if [ $rebase_exit -ne 0 ]; then
        git -C "$workspace" rebase --abort 2>/dev/null || true
        return 1
    fi

    # Force-push with lease (safe: single-owner branch)
    local push_exit=0
    git -C "$workspace" push --force-with-lease 2>/dev/null || push_exit=$?

    [ $push_exit -eq 0 ]
}
