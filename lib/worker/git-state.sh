#!/usr/bin/env bash
# git-state.sh - Unified git state tracking for worker directories
#
# Provides state management functions for tracking worker lifecycle through
# fix, merge, and conflict resolution workflows. State is stored in git-state.json
# with full audit trail of state transitions.
#
# States:
#   needs_fix         - New PR comments detected, needs fix worker
#   fixing            - Fix worker is running
#   fix_completed     - Fix completed, push succeeded
#   needs_merge       - Ready for merge attempt
#   merging           - Merge in progress
#   merge_conflict    - Merge failed due to conflict
#   needs_resolve     - Single-PR conflict resolver required
#   needs_multi_resolve - Multi-PR conflict (same files in multiple PRs)
#   resolving         - Resolver is running
#   resolved          - Conflicts resolved, ready for retry
#   merged            - PR merged successfully
#   failed            - Unrecoverable error
set -euo pipefail

[ -n "${_GIT_STATE_LOADED:-}" ] && return 0
_GIT_STATE_LOADED=1

# Get current state from git-state.json
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: state name or "none" if no state file exists
git_state_get() {
    local worker_dir="$1"
    local state_file="$worker_dir/git-state.json"

    [ -f "$state_file" ] || { echo "none"; return 0; }
    jq -r '.current_state // "none"' "$state_file"
}

# Set state with transition record for audit trail
#
# Args:
#   worker_dir - Worker directory path
#   new_state  - Target state
#   agent      - Agent/component making the change
#   reason     - Optional reason for the transition
#
# Creates git-state.json if it doesn't exist, otherwise updates it
# with the new state and appends to the transitions array.
git_state_set() {
    local worker_dir="$1"
    local new_state="$2"
    local agent="$3"
    local reason="${4:-}"
    local state_file="$worker_dir/git-state.json"
    local timestamp
    timestamp=$(date -Iseconds)

    # Ensure worker directory exists
    if [ ! -d "$worker_dir" ]; then
        echo "git_state_set: worker_dir does not exist: $worker_dir" >&2
        return 1
    fi

    # Initialize or update
    if [ ! -f "$state_file" ]; then
        jq -n \
            --arg s "$new_state" \
            --arg t "$timestamp" \
            --arg a "$agent" \
            --arg r "$reason" \
            '{
                current_state: $s,
                pr_number: null,
                merge_attempts: 0,
                last_error: null,
                transitions: [{
                    from: null,
                    to: $s,
                    timestamp: $t,
                    agent: $a,
                    reason: $r
                }]
            }' > "$state_file"
    else
        local old_state
        old_state=$(jq -r '.current_state' "$state_file")
        jq \
            --arg os "$old_state" \
            --arg ns "$new_state" \
            --arg t "$timestamp" \
            --arg a "$agent" \
            --arg r "$reason" \
            '.current_state = $ns | .transitions += [{
                from: $os,
                to: $ns,
                timestamp: $t,
                agent: $a,
                reason: $r
            }]' "$state_file" > "$state_file.tmp" && mv "$state_file.tmp" "$state_file"
    fi
}

# Set PR number in git-state.json
#
# Args:
#   worker_dir - Worker directory path
#   pr_number  - PR number (integer)
#
# Returns: 1 if state file doesn't exist
git_state_set_pr() {
    local worker_dir="$1"
    local pr_number="$2"
    local state_file="$worker_dir/git-state.json"

    [ -f "$state_file" ] || return 1

    jq --argjson pr "$pr_number" '.pr_number = $pr' "$state_file" > "$state_file.tmp" \
        && mv "$state_file.tmp" "$state_file"
}

# Get PR number from git-state.json
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: PR number or "null" if not set
git_state_get_pr() {
    local worker_dir="$1"
    local state_file="$worker_dir/git-state.json"

    [ -f "$state_file" ] || { echo "null"; return 0; }
    jq -r '.pr_number // "null"' "$state_file"
}

# Increment merge attempts counter
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: 1 if state file doesn't exist
git_state_inc_merge_attempts() {
    local worker_dir="$1"
    local state_file="$worker_dir/git-state.json"

    [ -f "$state_file" ] || return 1

    jq '.merge_attempts += 1' "$state_file" > "$state_file.tmp" \
        && mv "$state_file.tmp" "$state_file"
}

# Get merge attempts count
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: merge attempts count (0 if not set or file missing)
git_state_get_merge_attempts() {
    local worker_dir="$1"
    local state_file="$worker_dir/git-state.json"

    [ -f "$state_file" ] || { echo "0"; return 0; }
    jq -r '.merge_attempts // 0' "$state_file"
}

# Set last error message
#
# Args:
#   worker_dir - Worker directory path
#   error      - Error message
#
# Returns: 1 if state file doesn't exist
git_state_set_error() {
    local worker_dir="$1"
    local error="$2"
    local state_file="$worker_dir/git-state.json"

    [ -f "$state_file" ] || return 1

    jq --arg e "$error" '.last_error = $e' "$state_file" > "$state_file.tmp" \
        && mv "$state_file.tmp" "$state_file"
}

# Get last error message
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: error message or "null" if not set
git_state_get_error() {
    local worker_dir="$1"
    local state_file="$worker_dir/git-state.json"

    [ -f "$state_file" ] || { echo "null"; return 0; }
    jq -r '.last_error // "null"' "$state_file"
}

# Check if current state matches expected state
#
# Args:
#   worker_dir - Worker directory path
#   expected   - Expected state name
#
# Returns: 0 if matches, 1 otherwise
git_state_is() {
    local worker_dir="$1"
    local expected="$2"

    [ "$(git_state_get "$worker_dir")" = "$expected" ]
}

# Check if current state is one of the given states
#
# Args:
#   worker_dir - Worker directory path
#   states...  - List of acceptable states
#
# Returns: 0 if current state matches any, 1 otherwise
git_state_is_any() {
    local worker_dir="$1"
    shift
    local current
    current=$(git_state_get "$worker_dir")

    for state in "$@"; do
        [ "$current" = "$state" ] && return 0
    done
    return 1
}

# Get full state object as JSON
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: JSON object or empty object if not found
git_state_dump() {
    local worker_dir="$1"
    local state_file="$worker_dir/git-state.json"

    [ -f "$state_file" ] || { echo "{}"; return 0; }
    cat "$state_file"
}

# Get transition history
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: JSON array of transitions
git_state_transitions() {
    local worker_dir="$1"
    local state_file="$worker_dir/git-state.json"

    [ -f "$state_file" ] || { echo "[]"; return 0; }
    jq '.transitions // []' "$state_file"
}

# Set last push timestamp
#
# Args:
#   worker_dir - Worker directory path
#   timestamp  - ISO timestamp (optional, defaults to now)
#
# Returns: 1 if state file doesn't exist
git_state_set_last_push() {
    local worker_dir="$1"
    local timestamp="${2:-$(date -Iseconds)}"
    local state_file="$worker_dir/git-state.json"

    [ -f "$state_file" ] || return 1

    jq --arg t "$timestamp" '.last_push_at = $t' "$state_file" > "$state_file.tmp" \
        && mv "$state_file.tmp" "$state_file"
}

# Get last push timestamp
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: ISO timestamp or "null" if not set
git_state_get_last_push() {
    local worker_dir="$1"
    local state_file="$worker_dir/git-state.json"

    [ -f "$state_file" ] || { echo "null"; return 0; }
    jq -r '.last_push_at // "null"' "$state_file"
}

# Clear/reset state file (for testing or recovery)
#
# Args:
#   worker_dir - Worker directory path
git_state_clear() {
    local worker_dir="$1"
    local state_file="$worker_dir/git-state.json"

    rm -f "$state_file"
}
