#!/usr/bin/env bash
# pr-merge-optimizer.sh - Optimized PR merge strategy for multiple conflicting PRs
#
# This module implements a global optimization approach to merging multiple PRs:
#
# 1. GATHER: Collect data on all pending PRs (files modified, merge status)
# 2. ANALYZE: Build conflict graph showing which PRs conflict with each other
# 3. OPTIMIZE: Find optimal merge order to maximize successful merges
# 4. EXECUTE: Merge in order with re-evaluation after each merge
# 5. RESOLVE: Handle remaining conflicts (single-PR vs multi-PR)
#
# Data file: .ralph/pr-merge-state.json
# Format:
# {
#   "prs": {
#     "TASK-001": {
#       "pr_number": 20,
#       "worker_dir": "/path/to/worker",
#       "branch": "task-001-feature",
#       "files_modified": ["src/api.ts", "src/utils.ts"],
#       "base_commit": "abc123",
#       "has_new_comments": false,
#       "copilot_reviewed": true,
#       "mergeable_to_main": true,
#       "conflict_files_with_main": []
#     }
#   },
#   "conflict_graph": {
#     "TASK-001": ["TASK-002", "TASK-003"],
#     "TASK-002": ["TASK-001"],
#     "TASK-003": ["TASK-001"]
#   },
#   "merge_order": ["TASK-004", "TASK-005", "TASK-002", ...],
#   "last_updated": "2024-01-27T12:00:00Z"
# }

set -euo pipefail

[ -n "${_PR_MERGE_OPTIMIZER_LOADED:-}" ] && return 0
_PR_MERGE_OPTIMIZER_LOADED=1

# Source dependencies
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"
source "$WIGGUM_HOME/lib/worker/git-state.sh"
source "$WIGGUM_HOME/lib/scheduler/conflict-queue.sh"
source "$WIGGUM_HOME/lib/scheduler/conflict-registry.sh"

# State file path
_pr_merge_state_file() {
    echo "$1/pr-merge-state.json"
}

# Clean up worktree after PR is merged (keeps logs/results/reports)
#
# Args:
#   worker_dir - Worker directory path
_cleanup_merged_worktree() {
    local worker_dir="$1"
    local workspace="$worker_dir/workspace"

    [ -d "$workspace" ] || return 0

    log "      Cleaning up worktree..."

    # Get the worktree path for git worktree remove
    local repo_root
    repo_root=$(git -C "$workspace" rev-parse --show-toplevel 2>/dev/null || echo "")

    if [ -n "$repo_root" ]; then
        # Try to remove via git worktree (cleanest method)
        # Need to run from the main repo, not the worktree itself
        local main_repo
        main_repo=$(git -C "$workspace" worktree list --porcelain 2>/dev/null | head -1 | sed 's/^worktree //')

        if [ -n "$main_repo" ] && [ -d "$main_repo" ]; then
            git -C "$main_repo" worktree remove --force "$workspace" 2>/dev/null || true
        fi
    fi

    # If worktree remove didn't work, just remove the directory
    if [ -d "$workspace" ]; then
        rm -rf "$workspace"
    fi

    # Mark cleanup in worker state
    if [ -d "$worker_dir" ]; then
        echo "merged_and_cleaned" > "$worker_dir/.cleanup_status"
    fi

    log "      Worktree removed (logs preserved)"
}

# Check if pr-comment-fix agent completed successfully (PASS)
# Looks for the most recent result file from the fix agent
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: 0 if PASS found, 1 otherwise
_check_fix_agent_passed() {
    local worker_dir="$1"
    local results_dir="$worker_dir/results"

    [ -d "$results_dir" ] || return 1

    # Find the most recent pr-comment-fix result file
    local latest_result
    latest_result=$(find "$results_dir" -name "*pr-comment-fix*.json" -type f 2>/dev/null | sort -r | head -1)

    [ -n "$latest_result" ] && [ -f "$latest_result" ] || return 1

    # Check if gate_result is PASS
    local gate_result
    gate_result=$(jq -r '.gate_result // empty' "$latest_result" 2>/dev/null)

    [ "$gate_result" = "PASS" ]
}

# Check if there are new comments since the last fix commit
# Compares comment IDs in the main section vs those listed in ## Commit section
#
# Args:
#   task_comments_file - Path to task-comments.md
#
# Returns: "true" if new comments exist, "false" otherwise
_check_for_new_comments_since_commit() {
    local task_comments_file="$1"

    # Extract comment IDs from the main content (before ## Commit section)
    # Look for **ID:** patterns
    local main_content
    main_content=$(sed -n '1,/^## Commit$/p' "$task_comments_file" 2>/dev/null | head -n -1)

    local current_ids
    current_ids=$(echo "$main_content" | grep -oE '\*\*ID:\*\* [0-9]+' | grep -oE '[0-9]+' | sort -u)

    if [ -z "$current_ids" ]; then
        # No comment IDs found in main content
        echo "false"
        return
    fi

    # Extract addressed comment IDs from ## Commit section
    # Look for "Comment NNNN" patterns in the addressed list
    local commit_section
    commit_section=$(sed -n '/^## Commit$/,$ p' "$task_comments_file" 2>/dev/null)

    local addressed_ids
    addressed_ids=$(echo "$commit_section" | grep -oE 'Comment [0-9]+' | grep -oE '[0-9]+' | sort -u)

    if [ -z "$addressed_ids" ]; then
        # Commit section exists but no addressed IDs found - assume comments need fixing
        echo "true"
        return
    fi

    # Check if all current comment IDs are in the addressed list
    local new_comments="false"
    while IFS= read -r id; do
        [ -z "$id" ] && continue
        if ! echo "$addressed_ids" | grep -q "^${id}$"; then
            # Found a comment ID not in addressed list
            new_comments="true"
            break
        fi
    done <<< "$current_ids"

    echo "$new_comments"
}

# Initialize or reset the PR merge state
#
# Args:
#   ralph_dir - Ralph directory path
pr_merge_init() {
    local ralph_dir="$1"
    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    jq -n '{
        prs: {},
        conflict_graph: {},
        merge_order: [],
        merged_this_cycle: [],
        last_updated: now | strftime("%Y-%m-%dT%H:%M:%SZ")
    }' > "$state_file"
}

# =============================================================================
# PHASE 1: GATHER - Collect data on all pending PRs
# =============================================================================

# Get list of files modified by a PR branch compared to main
#
# Args:
#   workspace - Path to git workspace
#
# Returns: JSON array of file paths
_get_files_modified() {
    local workspace="$1"

    cd "$workspace" || return 1

    # Fetch latest main
    git fetch origin main 2>/dev/null || true

    # Get merge base
    local merge_base
    merge_base=$(git merge-base HEAD origin/main 2>/dev/null || echo "")

    if [ -z "$merge_base" ]; then
        echo "[]"
        return 0
    fi

    # Get files changed between merge-base and HEAD
    local files
    files=$(git diff --name-only "$merge_base" HEAD 2>/dev/null || echo "")

    if [ -z "$files" ]; then
        echo "[]"
    else
        echo "$files" | jq -R -s 'split("\n") | map(select(length > 0))'
    fi
}

# Check if PR can merge cleanly into current main
#
# Args:
#   workspace - Path to git workspace
#
# Returns: 0 if mergeable, 1 if conflicts
# Outputs: List of conflicting files (if any)
_check_mergeable_to_main() {
    local workspace="$1"

    cd "$workspace" || return 1

    # Fetch latest
    git fetch origin main 2>/dev/null || true

    # Try merge-tree for conflict detection (non-destructive)
    local merge_base head_commit main_commit
    merge_base=$(git merge-base HEAD origin/main 2>/dev/null || echo "")
    head_commit=$(git rev-parse HEAD 2>/dev/null)
    main_commit=$(git rev-parse origin/main 2>/dev/null)

    if [ -z "$merge_base" ]; then
        return 1
    fi

    # Use git merge-tree to detect conflicts without modifying working tree
    local merge_output
    merge_output=$(git merge-tree "$merge_base" "$head_commit" "$main_commit" 2>&1 || true)

    # Check for conflict markers
    if echo "$merge_output" | grep -q '^<<<<<<<\|^=======\|^>>>>>>>'; then
        # Extract conflicting files
        echo "$merge_output" | grep -E '^\+\+\+ |^changed in' | \
            sed 's/^+++ //' | sed 's/^changed in .* //' | \
            sort -u
        return 1
    fi

    # Alternative: try actual merge with abort
    local stash_result
    stash_result=$(git stash -q 2>&1 || echo "no_stash")

    if git merge --no-commit --no-ff origin/main 2>/dev/null; then
        git merge --abort 2>/dev/null || true
        [ "$stash_result" != "no_stash" ] && git stash pop -q 2>/dev/null || true
        return 0
    else
        # Get conflicting files
        git diff --name-only --diff-filter=U 2>/dev/null || true
        git merge --abort 2>/dev/null || true
        [ "$stash_result" != "no_stash" ] && git stash pop -q 2>/dev/null || true
        return 1
    fi
}

# Gather data for a single PR
#
# Args:
#   ralph_dir  - Ralph directory path
#   task_id    - Task identifier
#   worker_dir - Worker directory path
#   pr_number  - PR number
#
# Returns: JSON object with PR data
_gather_pr_data() {
    local ralph_dir="$1"
    local task_id="$2"
    local worker_dir="$3"
    local pr_number="$4"

    local workspace="$worker_dir/workspace"

    # Get branch name
    local branch=""
    if [ -d "$workspace" ]; then
        branch=$(git -C "$workspace" rev-parse --abbrev-ref HEAD 2>/dev/null || echo "")
    fi

    # Get base commit (merge-base with main)
    local base_commit=""
    if [ -d "$workspace" ]; then
        base_commit=$(git -C "$workspace" merge-base HEAD origin/main 2>/dev/null || echo "")
    fi

    # Get files modified
    local files_modified="[]"
    if [ -d "$workspace" ]; then
        files_modified=$(_get_files_modified "$workspace")
    fi

    # Check for new comments
    local has_new_comments="false"
    if [ -f "$worker_dir/task-comments.md" ]; then
        # Check if there are unaddressed comments
        local comment_count
        comment_count=$(grep -c '^### ' "$worker_dir/task-comments.md" 2>/dev/null | head -1 || echo "0")
        comment_count="${comment_count:-0}"
        if [[ "$comment_count" =~ ^[0-9]+$ ]] && [ "$comment_count" -gt 0 ]; then
            # Check 1: is there a ## Commit section indicating comments were addressed?
            if grep -q '^## Commit$' "$worker_dir/task-comments.md" 2>/dev/null; then
                # Comments were addressed by a previous fix commit
                # Check if there are NEW comments since the commit (comments not in the addressed list)
                has_new_comments=$(_check_for_new_comments_since_commit "$worker_dir/task-comments.md")
            # Check 2: did pr-comment-fix agent complete successfully (PASS)?
            elif _check_fix_agent_passed "$worker_dir"; then
                # Agent reported PASS - all comments were addressed
                has_new_comments="false"
            # Check 3: check status file for pending items
            elif [ -f "$worker_dir/reports/comment-status.md" ]; then
                local pending
                pending=$(grep -c '^\- \[ \]' "$worker_dir/reports/comment-status.md" 2>/dev/null | head -1 || echo "0")
                pending="${pending:-0}"
                [[ "$pending" =~ ^[0-9]+$ ]] && [ "$pending" -gt 0 ] && has_new_comments="true"
            else
                has_new_comments="true"
            fi
        fi
    fi

    # Check for Copilot review
    # If no reviews file exists, assume PR is ready (don't block on missing review data)
    # Only block if we have review data showing the PR needs attention
    local copilot_reviewed="true"
    if [ -f "$worker_dir/pr-reviews.json" ]; then
        # Check if there's a "changes_requested" review that hasn't been addressed
        local changes_requested
        changes_requested=$(jq -r '[.[] | select(.state == "CHANGES_REQUESTED")] | length' "$worker_dir/pr-reviews.json" 2>/dev/null || echo "0")
        if [ "$changes_requested" -gt 0 ]; then
            # Check if there's a more recent approval or if comments were addressed
            local latest_state
            latest_state=$(jq -r 'sort_by(.submitted_at) | last | .state // "NONE"' "$worker_dir/pr-reviews.json" 2>/dev/null || echo "NONE")
            if [ "$latest_state" = "CHANGES_REQUESTED" ]; then
                copilot_reviewed="false"
            fi
        fi
    fi

    # Check merge-ability and get conflict files
    local mergeable_to_main="true"
    local conflict_files_with_main="[]"
    if [ -d "$workspace" ]; then
        local conflicts
        if conflicts=$(_check_mergeable_to_main "$workspace"); then
            mergeable_to_main="true"
            conflict_files_with_main="[]"
        else
            mergeable_to_main="false"
            if [ -n "$conflicts" ]; then
                conflict_files_with_main=$(echo "$conflicts" | jq -R -s 'split("\n") | map(select(length > 0))')
            fi
        fi
    fi

    # Build JSON
    jq -n \
        --arg task_id "$task_id" \
        --argjson pr_number "$pr_number" \
        --arg worker_dir "$worker_dir" \
        --arg branch "$branch" \
        --arg base_commit "$base_commit" \
        --argjson files_modified "$files_modified" \
        --argjson has_new_comments "$has_new_comments" \
        --argjson copilot_reviewed "$copilot_reviewed" \
        --argjson mergeable_to_main "$mergeable_to_main" \
        --argjson conflict_files_with_main "$conflict_files_with_main" \
        '{
            pr_number: $pr_number,
            worker_dir: $worker_dir,
            branch: $branch,
            base_commit: $base_commit,
            files_modified: $files_modified,
            has_new_comments: $has_new_comments,
            copilot_reviewed: $copilot_reviewed,
            mergeable_to_main: $mergeable_to_main,
            conflict_files_with_main: $conflict_files_with_main
        }'
}

# Gather data for all pending PRs
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
#
# Populates the prs object in pr-merge-state.json
pr_merge_gather_all() {
    local ralph_dir="$1"
    local project_dir="$2"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    # Initialize state
    pr_merge_init "$ralph_dir"

    log "Phase 1: Gathering PR data..."

    local count=0

    # Find all 'P' tasks with PRs
    for worker_dir in "$ralph_dir/workers"/worker-*; do
        [ -d "$worker_dir" ] || continue

        # Skip plan workers
        [[ "$(basename "$worker_dir")" == *"-plan-"* ]] && continue

        # Must have workspace
        [ -d "$worker_dir/workspace" ] || continue

        # Skip if running
        if [ -f "$worker_dir/worker.pid" ]; then
            local pid
            pid=$(cat "$worker_dir/worker.pid")
            if ps -p "$pid" >/dev/null 2>&1; then
                continue
            fi
        fi

        local task_id
        task_id=$(basename "$worker_dir" | sed 's/worker-\([A-Za-z]*-[0-9]*\)-.*/\1/')

        # Check if task is pending approval
        local task_status
        task_status=$(grep -E "^\- \[.\] \*\*\[$task_id\]" "$ralph_dir/kanban.md" 2>/dev/null | \
            sed 's/^- \[\(.\)\].*/\1/' || echo "")
        [ "$task_status" = "P" ] || continue

        # Get PR number (with backfill)
        local pr_number
        pr_number=$(git_state_get_pr "$worker_dir" 2>/dev/null || echo "")
        if { [ -z "$pr_number" ] || [ "$pr_number" = "null" ]; } && [ -f "$worker_dir/pr_url.txt" ]; then
            local pr_url
            pr_url=$(cat "$worker_dir/pr_url.txt")
            pr_number=$(echo "$pr_url" | grep -oE '[0-9]+$' || true)
            if [ -n "$pr_number" ]; then
                git_state_set_pr "$worker_dir" "$pr_number" 2>/dev/null || true
            fi
        fi
        [ -n "$pr_number" ] && [ "$pr_number" != "null" ] || continue

        # Sync PR comments
        "$WIGGUM_HOME/bin/wiggum-review" task "$task_id" sync 2>/dev/null || true

        # Check if PR is already merged on GitHub (sync may have detected this)
        local pr_state
        pr_state=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh pr view "$pr_number" --json state -q '.state' 2>/dev/null || echo "UNKNOWN")
        if [ "$pr_state" = "MERGED" ]; then
            log "  $task_id (PR #$pr_number): Already merged - cleaning up"
            # Update kanban to complete
            update_kanban_status "$ralph_dir/kanban.md" "$task_id" "x" 2>/dev/null || true
            # Clean up worktree
            _cleanup_merged_worktree "$worker_dir"
            continue
        fi

        # Gather PR data
        log "  Gathering data for $task_id (PR #$pr_number)..."
        local pr_data
        pr_data=$(_gather_pr_data "$ralph_dir" "$task_id" "$worker_dir" "$pr_number")

        # Add to state
        jq --arg task_id "$task_id" --argjson pr_data "$pr_data" \
            '.prs[$task_id] = $pr_data' "$state_file" > "$state_file.tmp"
        mv "$state_file.tmp" "$state_file"

        ((++count))
    done

    log "  Gathered data for $count PR(s)"

    # Update timestamp
    jq '.last_updated = (now | strftime("%Y-%m-%dT%H:%M:%SZ"))' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"
}

# =============================================================================
# PHASE 2: ANALYZE - Build conflict graph
# =============================================================================

# Check if two PRs have file-level conflicts (overlapping modified files)
#
# Args:
#   files_a - JSON array of files from PR A
#   files_b - JSON array of files from PR B
#
# Returns: 0 if overlap exists, 1 otherwise
# Outputs: JSON array of overlapping files
_check_file_overlap() {
    local files_a="$1"
    local files_b="$2"

    local overlap
    overlap=$(jq -n --argjson a "$files_a" --argjson b "$files_b" \
        '($a + $b) | group_by(.) | map(select(length > 1) | .[0])')

    local count
    count=$(echo "$overlap" | jq 'length')

    echo "$overlap"
    [ "$count" -gt 0 ]
}

# Build the conflict graph from gathered PR data
#
# The conflict graph shows which PRs conflict with each other based on:
# 1. File-level overlap (same files modified)
# 2. Actual merge conflicts (if we have that data)
#
# Args:
#   ralph_dir - Ralph directory path
pr_merge_build_conflict_graph() {
    local ralph_dir="$1"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    log "Phase 2: Building conflict graph..."

    # Get all task IDs
    local task_ids
    task_ids=$(jq -r '.prs | keys[]' "$state_file")

    # Initialize empty conflict graph
    jq '.conflict_graph = {}' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    # For each pair of PRs, check for conflicts
    local task_array=()
    while IFS= read -r task_id; do
        [ -n "$task_id" ] && task_array+=("$task_id")
    done <<< "$task_ids"

    local conflict_count=0
    local i j
    for ((i=0; i<${#task_array[@]}; i++)); do
        local task_a="${task_array[$i]}"
        local files_a
        files_a=$(jq -r --arg t "$task_a" '.prs[$t].files_modified' "$state_file")

        for ((j=i+1; j<${#task_array[@]}; j++)); do
            local task_b="${task_array[$j]}"
            local files_b
            files_b=$(jq -r --arg t "$task_b" '.prs[$t].files_modified' "$state_file")

            # Check for overlap
            local overlap
            if overlap=$(_check_file_overlap "$files_a" "$files_b"); then
                log "  Conflict: $task_a ↔ $task_b (files: $(echo "$overlap" | jq -r 'join(", ")'))"

                # Add to both sides of the graph
                jq --arg a "$task_a" --arg b "$task_b" '
                    .conflict_graph[$a] = ((.conflict_graph[$a] // []) + [$b] | unique) |
                    .conflict_graph[$b] = ((.conflict_graph[$b] // []) + [$a] | unique)
                ' "$state_file" > "$state_file.tmp"
                mv "$state_file.tmp" "$state_file"

                ((++conflict_count))
            fi
        done
    done

    log "  Found $conflict_count conflict pair(s)"

    # Identify PRs with no conflicts (independent)
    local independent_count=0
    for task_id in "${task_array[@]}"; do
        local conflicts
        conflicts=$(jq -r --arg t "$task_id" '.conflict_graph[$t] // [] | length' "$state_file")
        if [ "$conflicts" -eq 0 ]; then
            ((++independent_count))
        fi
    done

    log "  Independent PRs (no conflicts): $independent_count"
}

# =============================================================================
# PHASE 3: OPTIMIZE - Find optimal merge order using Dynamic Programming
# =============================================================================
#
# This is the Maximum Independent Set (MIS) problem on the conflict graph.
# We want to find the largest set of PRs that can be merged without conflicts.
#
# Algorithm: Bitmask DP for exact solution (feasible for n < 20 PRs)
# - State: dp[mask] = 1 if subset represented by mask has no internal conflicts
# - Find maximum |mask| where dp[mask] = 1 AND all PRs in mask are mergeable
#
# For larger n, we fall back to a greedy approximation.

# Build adjacency matrix for conflict graph
#
# Args:
#   ralph_dir - Ralph directory path
#   task_ids  - Array of task IDs (passed by name)
#
# Sets global: _CONFLICT_MATRIX[i*n+j] = 1 if tasks i and j conflict
_build_conflict_matrix() {
    local ralph_dir="$1"
    local -n _task_array="$2"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    local n=${#_task_array[@]}
    _CONFLICT_MATRIX=()

    # Initialize matrix to 0
    local i j
    for ((i=0; i<n; i++)); do
        for ((j=0; j<n; j++)); do
            _CONFLICT_MATRIX[i*n+j]=0
        done
    done

    # Fill in conflicts
    for ((i=0; i<n; i++)); do
        local task_i="${_task_array[$i]}"
        local conflicts
        conflicts=$(jq -r --arg t "$task_i" '.conflict_graph[$t] // [] | .[]' "$state_file")

        while IFS= read -r conflict_task; do
            [ -n "$conflict_task" ] || continue
            # Find index of conflict_task
            for ((j=0; j<n; j++)); do
                if [ "${_task_array[$j]}" = "$conflict_task" ]; then
                    _CONFLICT_MATRIX[i*n+j]=1
                    _CONFLICT_MATRIX[j*n+i]=1
                    break
                fi
            done
        done <<< "$conflicts"
    done
}

# Check if a subset (bitmask) is an independent set (no internal conflicts)
#
# Args:
#   mask - Bitmask representing subset
#   n    - Number of tasks
#
# Returns: 0 if independent set, 1 otherwise
_is_independent_set() {
    local mask="$1"
    local n="$2"

    local i j
    for ((i=0; i<n; i++)); do
        # Skip if i not in mask
        (( (mask >> i) & 1 )) || continue

        for ((j=i+1; j<n; j++)); do
            # Skip if j not in mask
            (( (mask >> j) & 1 )) || continue

            # Check if i and j conflict
            if [ "${_CONFLICT_MATRIX[i*n+j]}" = "1" ]; then
                return 1  # Not independent
            fi
        done
    done

    return 0  # Is independent
}

# Count bits set in a number (population count)
_popcount() {
    local n="$1"
    local count=0
    while [ "$n" -gt 0 ]; do
        ((count += n & 1))
        ((n >>= 1))
    done
    echo "$count"
}

# Find Maximum Independent Set using bitmask DP
#
# Args:
#   ralph_dir    - Ralph directory path
#   task_ids     - Array of task IDs (passed by name)
#   mergeable    - Array of 0/1 indicating if task is currently mergeable (passed by name)
#
# Returns: JSON array of task IDs in the maximum independent set
_find_maximum_independent_set() {
    local ralph_dir="$1"
    local -n _tasks="$2"
    local -n _mergeable="$3"

    local n=${#_tasks[@]}

    # For n > 20, use greedy fallback (2^20 = 1M iterations is borderline)
    if [ "$n" -gt 18 ]; then
        log "  Using greedy approximation (n=$n > 18)"
        _find_mis_greedy "$ralph_dir" _tasks _mergeable
        return
    fi

    # Build conflict matrix
    _build_conflict_matrix "$ralph_dir" _tasks

    local max_mask=0
    local max_mergeable_count=0
    local max_total_count=0

    # Iterate through all subsets
    local total=$((1 << n))
    local mask

    for ((mask=1; mask<total; mask++)); do
        # Quick filter: skip if this mask has fewer mergeable than current best
        local mergeable_count=0
        local total_count=0
        local i

        for ((i=0; i<n; i++)); do
            if (( (mask >> i) & 1 )); then
                ((++total_count))
                if [ "${_mergeable[$i]}" = "1" ]; then
                    ((++mergeable_count))
                fi
            fi
        done

        # Skip if can't beat current best
        # Primary: maximize mergeable count
        # Secondary: maximize total count
        if [ "$mergeable_count" -lt "$max_mergeable_count" ]; then
            continue
        fi
        if [ "$mergeable_count" -eq "$max_mergeable_count" ] && [ "$total_count" -le "$max_total_count" ]; then
            continue
        fi

        # Check if this is a valid independent set
        if _is_independent_set "$mask" "$n"; then
            max_mask=$mask
            max_mergeable_count=$mergeable_count
            max_total_count=$total_count
        fi
    done

    # Convert mask to task IDs
    local result="[]"
    for ((i=0; i<n; i++)); do
        if (( (max_mask >> i) & 1 )); then
            result=$(echo "$result" | jq --arg t "${_tasks[$i]}" '. + [$t]')
        fi
    done

    echo "$result"
}

# Greedy approximation for Maximum Independent Set (for large n)
#
# Strategy: Repeatedly pick the vertex with minimum degree, add to set, remove neighbors
#
# Args:
#   ralph_dir    - Ralph directory path
#   task_ids     - Array of task IDs (passed by name)
#   mergeable    - Array of 0/1 indicating if task is currently mergeable (passed by name)
#
# Returns: JSON array of task IDs in the independent set
_find_mis_greedy() {
    local ralph_dir="$1"
    local -n _tasks_g="$2"
    local -n _mergeable_g="$3"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    local n=${#_tasks_g[@]}
    local -a removed=()
    local -a in_set=()

    # Initialize
    for ((i=0; i<n; i++)); do
        removed[$i]=0
        in_set[$i]=0
    done

    # Build conflict matrix if not already built
    _build_conflict_matrix "$ralph_dir" _tasks_g

    # Greedy: prioritize mergeable PRs, then minimum degree
    while true; do
        local best_idx=-1
        local best_degree=999999
        local best_mergeable=0

        for ((i=0; i<n; i++)); do
            [ "${removed[$i]}" = "1" ] && continue

            # Calculate current degree (conflicts with non-removed nodes)
            local degree=0
            for ((j=0; j<n; j++)); do
                [ "${removed[$j]}" = "1" ] && continue
                [ "$i" = "$j" ] && continue
                if [ "${_CONFLICT_MATRIX[i*n+j]}" = "1" ]; then
                    ((++degree))
                fi
            done

            local is_mergeable="${_mergeable_g[$i]}"

            # Prefer: mergeable > non-mergeable, then lower degree
            if [ "$best_idx" = "-1" ]; then
                best_idx=$i
                best_degree=$degree
                best_mergeable=$is_mergeable
            elif [ "$is_mergeable" = "1" ] && [ "$best_mergeable" = "0" ]; then
                best_idx=$i
                best_degree=$degree
                best_mergeable=$is_mergeable
            elif [ "$is_mergeable" = "$best_mergeable" ] && [ "$degree" -lt "$best_degree" ]; then
                best_idx=$i
                best_degree=$degree
                best_mergeable=$is_mergeable
            fi
        done

        # No more nodes to add
        [ "$best_idx" = "-1" ] && break

        # Add best to set
        in_set[$best_idx]=1
        removed[$best_idx]=1

        # Remove all neighbors
        for ((j=0; j<n; j++)); do
            if [ "${_CONFLICT_MATRIX[best_idx*n+j]}" = "1" ]; then
                removed[$j]=1
            fi
        done
    done

    # Convert to JSON
    local result="[]"
    for ((i=0; i<n; i++)); do
        if [ "${in_set[$i]}" = "1" ]; then
            result=$(echo "$result" | jq --arg t "${_tasks_g[$i]}" '. + [$t]')
        fi
    done

    echo "$result"
}

# Calculate priority score for tiebreaking within independent set
# Used to order PRs within a merge batch
#
# Args:
#   ralph_dir - Ralph directory path
#   task_id   - Task identifier
#
# Returns: Integer priority score (higher = merge first)
_calculate_merge_priority() {
    local ralph_dir="$1"
    local task_id="$2"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    # Fewer files = simpler PR = merge first
    local files_count
    files_count=$(jq -r --arg t "$task_id" '.prs[$t].files_modified | length' "$state_file")

    # Fewer conflicts = less likely to cause issues
    local conflict_count
    conflict_count=$(jq -r --arg t "$task_id" '.conflict_graph[$t] // [] | length' "$state_file")

    # Score: higher = merge first
    local score=1000
    ((score -= files_count * 10)) || true
    ((score -= conflict_count * 50)) || true

    echo "$score"
}

# Find optimal merge order using Maximum Independent Set DP
#
# Strategy:
# 1. Find MIS among currently-mergeable PRs (maximize merge batch)
# 2. Order batch by tiebreaker priority (simpler PRs first)
# 3. Remaining PRs ordered by conflict count (for future passes)
#
# Args:
#   ralph_dir - Ralph directory path
pr_merge_find_optimal_order() {
    local ralph_dir="$1"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    log "Phase 3: Finding optimal merge order (Maximum Independent Set DP)..."

    # Get all task IDs and build arrays
    local -a task_array=()
    local -a mergeable_array=()

    local task_ids
    task_ids=$(jq -r '.prs | keys[]' "$state_file")

    while IFS= read -r task_id; do
        [ -n "$task_id" ] || continue
        task_array+=("$task_id")

        local is_mergeable
        is_mergeable=$(jq -r --arg t "$task_id" '.prs[$t].mergeable_to_main' "$state_file")
        if [ "$is_mergeable" = "true" ]; then
            mergeable_array+=(1)
        else
            mergeable_array+=(0)
        fi
    done <<< "$task_ids"

    local n=${#task_array[@]}

    if [ "$n" -eq 0 ]; then
        jq '.merge_order = []' "$state_file" > "$state_file.tmp"
        mv "$state_file.tmp" "$state_file"
        log "  No PRs to order"
        return
    fi

    log "  Processing $n PRs..."

    # Find Maximum Independent Set
    local mis_json
    mis_json=$(_find_maximum_independent_set "$ralph_dir" task_array mergeable_array)

    local mis_count
    mis_count=$(echo "$mis_json" | jq 'length')
    log "  Maximum Independent Set size: $mis_count"

    # Sort MIS by priority for merge order
    local -A priorities
    local task_id
    while IFS= read -r task_id; do
        [ -n "$task_id" ] || continue
        priorities[$task_id]=$(_calculate_merge_priority "$ralph_dir" "$task_id")
    done < <(echo "$mis_json" | jq -r '.[]')

    local sorted_mis=()
    for task_id in "${!priorities[@]}"; do
        sorted_mis+=("${priorities[$task_id]}|$task_id")
    done

    local merge_order=()
    while IFS= read -r entry; do
        [ -n "$entry" ] || continue
        local tid
        tid=$(echo "$entry" | cut -d'|' -f2)
        merge_order+=("$tid")
    done < <(printf '%s\n' "${sorted_mis[@]}" | sort -t'|' -k1 -rn)

    # Add remaining PRs (not in MIS) ordered by conflict count
    local -A remaining_priorities
    for task_id in "${task_array[@]}"; do
        # Skip if in MIS
        if echo "$mis_json" | jq -e --arg t "$task_id" 'index($t)' >/dev/null 2>&1; then
            continue
        fi
        remaining_priorities[$task_id]=$(_calculate_merge_priority "$ralph_dir" "$task_id")
    done

    local sorted_remaining=()
    for task_id in "${!remaining_priorities[@]}"; do
        sorted_remaining+=("${remaining_priorities[$task_id]}|$task_id")
    done

    while IFS= read -r entry; do
        [ -n "$entry" ] || continue
        local tid
        tid=$(echo "$entry" | cut -d'|' -f2)
        merge_order+=("$tid")
    done < <(printf '%s\n' "${sorted_remaining[@]}" | sort -t'|' -k1 -rn)

    # Build JSON array
    local order_json="[]"
    for task_id in "${merge_order[@]}"; do
        order_json=$(echo "$order_json" | jq --arg t "$task_id" '. + [$t]')
    done

    # Save to state with MIS info
    jq --argjson order "$order_json" --argjson mis "$mis_json" '
        .merge_order = $order |
        .optimal_batch = $mis
    ' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    log "  Optimal batch (MIS): $(echo "$mis_json" | jq -r 'join(", ")')"
    log "  Full merge order: $(echo "$order_json" | jq -r 'join(" → ")')"
}

# =============================================================================
# PHASE 4: EXECUTE - Merge PRs in order with re-evaluation
# =============================================================================

# Attempt to merge a single PR
#
# Args:
#   ralph_dir - Ralph directory path
#   task_id   - Task identifier
#
# Returns: 0 on success, 1 on failure
_attempt_merge() {
    local ralph_dir="$1"
    local task_id="$2"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    local pr_number
    pr_number=$(jq -r --arg t "$task_id" '.prs[$t].pr_number' "$state_file")

    local gh_timeout="${WIGGUM_GH_TIMEOUT:-30}"

    # Try to merge via gh CLI
    # Note: --delete-branch may fail for worktree branches (can't delete local branch in use)
    # but the merge itself may have succeeded. Check PR state afterward.
    local merge_output
    merge_output=$(timeout "$gh_timeout" gh pr merge "$pr_number" --merge --delete-branch 2>&1) || true

    # Check if PR is now merged (handles case where merge succeeded but branch delete failed)
    local pr_state
    pr_state=$(timeout "$gh_timeout" gh pr view "$pr_number" --json state -q '.state' 2>/dev/null || echo "UNKNOWN")

    if [ "$pr_state" = "MERGED" ]; then
        log "    ✓ Merged PR #$pr_number"

        # Update kanban status to complete
        local kanban_file
        kanban_file=$(dirname "$state_file")/kanban.md
        if [ -f "$kanban_file" ]; then
            update_kanban_status "$kanban_file" "$task_id" "x" 2>/dev/null || true
            log "      Kanban: [$task_id] → [x]"
        fi

        # Clean up worktree now that PR is merged (keep logs/results)
        local worker_dir
        worker_dir=$(jq -r --arg t "$task_id" '.prs[$t].worker_dir' "$state_file")
        if [ -n "$worker_dir" ] && [ -d "$worker_dir/workspace" ]; then
            _cleanup_merged_worktree "$worker_dir"
        fi

        return 0
    else
        log "    ✗ Failed to merge PR #$pr_number"
        log "      $merge_output"
        return 1
    fi
}

# Re-check merge-ability for remaining PRs after a successful merge
#
# Args:
#   ralph_dir - Ralph directory path
_refresh_merge_status() {
    local ralph_dir="$1"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    # Get remaining task IDs (not yet merged)
    local merged
    merged=$(jq -r '.merged_this_cycle[]' "$state_file" 2>/dev/null || echo "")

    local task_ids
    task_ids=$(jq -r '.prs | keys[]' "$state_file")

    while IFS= read -r task_id; do
        [ -n "$task_id" ] || continue

        # Skip if already merged
        if echo "$merged" | grep -q "^${task_id}$"; then
            continue
        fi

        local worker_dir
        worker_dir=$(jq -r --arg t "$task_id" '.prs[$t].worker_dir' "$state_file")

        if [ -d "$worker_dir/workspace" ]; then
            # Fetch latest main
            git -C "$worker_dir/workspace" fetch origin main 2>/dev/null || true

            # Re-check merge-ability
            local mergeable="true"
            local conflict_files="[]"
            local conflicts
            if conflicts=$(_check_mergeable_to_main "$worker_dir/workspace"); then
                mergeable="true"
            else
                mergeable="false"
                if [ -n "$conflicts" ]; then
                    conflict_files=$(echo "$conflicts" | jq -R -s 'split("\n") | map(select(length > 0))')
                fi
            fi

            # Update state
            jq --arg t "$task_id" --argjson m "$mergeable" --argjson cf "$conflict_files" '
                .prs[$t].mergeable_to_main = $m |
                .prs[$t].conflict_files_with_main = $cf
            ' "$state_file" > "$state_file.tmp"
            mv "$state_file.tmp" "$state_file"
        fi
    done <<< "$task_ids"
}

# Execute merges in optimal order
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
#
# Returns: Number of successfully merged PRs
pr_merge_execute() {
    local ralph_dir="$1"
    local project_dir="$2"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    log "Phase 4: Executing merges..."

    # Reset merged list
    jq '.merged_this_cycle = []' "$state_file" > "$state_file.tmp"
    mv "$state_file.tmp" "$state_file"

    local merged_count=0
    local max_passes=10  # Prevent infinite loops
    local pass=0

    while [ $pass -lt $max_passes ]; do
        ((++pass))
        local merged_this_pass=0

        log "  Pass $pass:"

        # Get merge order
        local merge_order
        merge_order=$(jq -r '.merge_order[]' "$state_file")

        while IFS= read -r task_id; do
            [ -n "$task_id" ] || continue

            # Skip if already merged
            if jq -e --arg t "$task_id" '.merged_this_cycle | index($t)' "$state_file" >/dev/null 2>&1; then
                continue
            fi

            # Skip if has new comments
            local has_comments
            has_comments=$(jq -r --arg t "$task_id" '.prs[$t].has_new_comments' "$state_file")
            if [ "$has_comments" = "true" ]; then
                log "    $task_id: Skipped (has new comments)"
                continue
            fi

            # Skip if changes were requested and not yet addressed
            local reviewed
            reviewed=$(jq -r --arg t "$task_id" '.prs[$t].copilot_reviewed' "$state_file")
            if [ "$reviewed" != "true" ]; then
                log "    $task_id: Skipped (has unaddressed review requests)"
                continue
            fi

            # Check if currently mergeable
            local mergeable
            mergeable=$(jq -r --arg t "$task_id" '.prs[$t].mergeable_to_main' "$state_file")

            if [ "$mergeable" = "true" ]; then
                log "    $task_id: Attempting merge..."

                if _attempt_merge "$ralph_dir" "$task_id"; then
                    # Mark as merged
                    jq --arg t "$task_id" '.merged_this_cycle += [$t]' "$state_file" > "$state_file.tmp"
                    mv "$state_file.tmp" "$state_file"

                    ((++merged_count))
                    ((++merged_this_pass))

                    # Refresh merge status for remaining PRs
                    _refresh_merge_status "$ralph_dir"
                fi
            else
                log "    $task_id: Not mergeable (has conflicts with main)"
            fi
        done <<< "$merge_order"

        # If no merges this pass, we're done
        if [ $merged_this_pass -eq 0 ]; then
            log "  No more PRs mergeable"
            break
        fi

        log "  Merged $merged_this_pass PR(s) this pass, refreshing..."
    done

    log "  Total merged: $merged_count PR(s)"
    echo "$merged_count"
}

# =============================================================================
# PHASE 5: RESOLVE - Handle remaining conflicts
# =============================================================================

# Categorize remaining PRs and queue for appropriate resolution
#
# Categories:
# - needs_fix: Has new comments that need addressing
# - needs_resolve: Single-PR conflict (only conflicts with main, not other PRs)
# - needs_multi_resolve: Multi-PR conflict (conflicts with other unmerged PRs)
#
# Args:
#   ralph_dir - Ralph directory path
pr_merge_handle_remaining() {
    local ralph_dir="$1"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    log "Phase 5: Handling remaining PRs..."

    # Initialize conflict queue
    conflict_queue_init "$ralph_dir"
    conflict_registry_init "$ralph_dir"

    # Get task IDs that weren't merged
    local merged
    merged=$(jq -r '.merged_this_cycle[]' "$state_file" 2>/dev/null || echo "")

    local task_ids
    task_ids=$(jq -r '.prs | keys[]' "$state_file")

    local needs_fix=0
    local needs_resolve=0
    local needs_multi_resolve=0
    local waiting=0

    while IFS= read -r task_id; do
        [ -n "$task_id" ] || continue

        # Skip if merged
        if echo "$merged" | grep -q "^${task_id}$"; then
            continue
        fi

        local worker_dir pr_number has_comments reviewed mergeable conflict_files
        worker_dir=$(jq -r --arg t "$task_id" '.prs[$t].worker_dir' "$state_file")
        pr_number=$(jq -r --arg t "$task_id" '.prs[$t].pr_number' "$state_file")
        has_comments=$(jq -r --arg t "$task_id" '.prs[$t].has_new_comments' "$state_file")
        reviewed=$(jq -r --arg t "$task_id" '.prs[$t].copilot_reviewed' "$state_file")
        mergeable=$(jq -r --arg t "$task_id" '.prs[$t].mergeable_to_main' "$state_file")
        conflict_files=$(jq -r --arg t "$task_id" '.prs[$t].conflict_files_with_main' "$state_file")

        # Case 1: Has new comments → needs_fix
        if [ "$has_comments" = "true" ]; then
            log "  $task_id: needs_fix (has new comments)"
            git_state_set "$worker_dir" "needs_fix" "pr-merge-optimizer" "New comments need addressing"
            echo "$task_id" >> "$ralph_dir/.tasks-needing-fix.txt"
            ((++needs_fix))
            continue
        fi

        # Case 2: Has unaddressed review requests → waiting
        if [ "$reviewed" != "true" ]; then
            log "  $task_id: waiting (has unaddressed review requests)"
            ((++waiting))
            continue
        fi

        # Case 3: Mergeable but wasn't merged (shouldn't happen, but handle it)
        if [ "$mergeable" = "true" ]; then
            log "  $task_id: will retry merge next cycle"
            continue
        fi

        # Case 4: Has conflicts → check if single or multi-PR
        # Check if this PR conflicts with any OTHER unmerged PR
        local conflicts_with_prs
        conflicts_with_prs=$(jq -r --arg t "$task_id" '.conflict_graph[$t] // []' "$state_file")

        local has_multi_conflict="false"
        while IFS= read -r other_task; do
            [ -n "$other_task" ] || continue
            # Check if other task is also unmerged
            if ! echo "$merged" | grep -q "^${other_task}$"; then
                has_multi_conflict="true"
                break
            fi
        done < <(echo "$conflicts_with_prs" | jq -r '.[]')

        if [ "$has_multi_conflict" = "true" ]; then
            log "  $task_id: needs_multi_resolve (conflicts with other PRs)"

            # Add to conflict registry and queue
            # Use files_modified (not conflict_files_with_main) for grouping - this is
            # what determines PR-to-PR conflicts (same as Phase 2 conflict graph)
            local files_modified
            files_modified=$(jq -r --arg t "$task_id" '.prs[$t].files_modified' "$state_file")
            conflict_registry_add "$ralph_dir" "$task_id" "$pr_number" "$(echo "$files_modified" | jq -r '.[]')"
            conflict_queue_add "$ralph_dir" "$task_id" "$worker_dir" "$pr_number" "$files_modified"

            git_state_set "$worker_dir" "needs_multi_resolve" "pr-merge-optimizer" "Multi-PR conflict detected"
            ((++needs_multi_resolve))
        else
            log "  $task_id: needs_resolve (single-PR conflict with main)"

            git_state_set "$worker_dir" "needs_resolve" "pr-merge-optimizer" "Merge conflict with main"
            ((++needs_resolve))
        fi
    done <<< "$task_ids"

    log "  Summary: $needs_fix need fixes, $needs_resolve need simple resolve, $needs_multi_resolve need multi-PR resolve, $waiting waiting for review"

    # If we have multi-resolve tasks, create a batch using the merge_order from Phase 3
    if [ "$needs_multi_resolve" -gt 1 ]; then
        _create_multi_resolve_batch "$ralph_dir" "$state_file"
    fi
}

# Create a batch for multi-resolve tasks using merge_order from Phase 3
#
# This ensures we use the optimal order computed by the MIS algorithm rather
# than the conflict queue's grouping logic.
#
# Args:
#   ralph_dir  - Ralph directory path
#   state_file - PR merge state file path
_create_multi_resolve_batch() {
    local ralph_dir="$1"
    local state_file="$2"

    local queue_file="$ralph_dir/conflict-queue.json"
    [ -f "$queue_file" ] || return 0

    # Get unbatched tasks from the conflict queue
    local unbatched_ids
    unbatched_ids=$(jq -r '[.queue[] | select(.batch_id == null) | .task_id]' "$queue_file")

    local unbatched_count
    unbatched_count=$(echo "$unbatched_ids" | jq 'length')

    if [ "$unbatched_count" -lt 2 ]; then
        return 0
    fi

    # Get merge_order from Phase 3 and filter to unbatched tasks only
    local merge_order
    merge_order=$(jq -r '.merge_order[]' "$state_file" 2>/dev/null || echo "")

    # Build ordered array of unbatched tasks (preserving merge_order sequence)
    local ordered_task_ids='[]'
    while IFS= read -r task_id; do
        [ -n "$task_id" ] || continue
        # Check if this task is in the unbatched set
        if echo "$unbatched_ids" | jq -e ". | index(\"$task_id\")" >/dev/null 2>&1; then
            ordered_task_ids=$(echo "$ordered_task_ids" | jq --arg t "$task_id" '. + [$t]')
        fi
    done <<< "$merge_order"

    local ordered_count
    ordered_count=$(echo "$ordered_task_ids" | jq 'length')

    if [ "$ordered_count" -lt 2 ]; then
        return 0
    fi

    log "  Creating batch for $ordered_count multi-resolve tasks (using Phase 3 merge order)"

    # Create batch using conflict_queue_create_batch
    local batch_id
    batch_id=$(conflict_queue_create_batch "$ralph_dir" "$ordered_task_ids")

    log "  Created batch $batch_id with order: $(echo "$ordered_task_ids" | jq -r 'join(" → ")')"
}

# =============================================================================
# MAIN ORCHESTRATION
# =============================================================================

# Run the complete PR merge optimization flow
#
# Args:
#   ralph_dir   - Ralph directory path
#   project_dir - Project directory path
#
# Returns: 0 on success
pr_merge_optimize_and_execute() {
    local ralph_dir="$1"
    local project_dir="$2"

    log "Starting PR merge optimization..."
    echo ""

    # Phase 1: Gather
    pr_merge_gather_all "$ralph_dir" "$project_dir"
    echo ""

    # Check if we have any PRs to process
    local pr_count
    pr_count=$(jq '.prs | length' "$(_pr_merge_state_file "$ralph_dir")")

    if [ "$pr_count" -eq 0 ]; then
        log "No pending PRs to process"
        return 0
    fi

    # Phase 2: Analyze
    pr_merge_build_conflict_graph "$ralph_dir"
    echo ""

    # Phase 3: Optimize
    pr_merge_find_optimal_order "$ralph_dir"
    echo ""

    # Phase 4: Execute
    local merged
    merged=$(pr_merge_execute "$ralph_dir" "$project_dir")
    echo ""

    # Phase 5: Handle remaining
    pr_merge_handle_remaining "$ralph_dir"
    echo ""

    log "PR merge optimization complete (merged $merged PRs)"
}

# Get statistics from the current state
#
# Args:
#   ralph_dir - Ralph directory path
#
# Returns: JSON object with stats
pr_merge_stats() {
    local ralph_dir="$1"

    local state_file
    state_file=$(_pr_merge_state_file "$ralph_dir")

    [ -f "$state_file" ] || { echo '{}'; return 0; }

    jq '{
        total_prs: (.prs | length),
        merged: (.merged_this_cycle | length),
        mergeable: [.prs | to_entries[] | select(.value.mergeable_to_main == true)] | length,
        with_conflicts: [.prs | to_entries[] | select(.value.mergeable_to_main == false)] | length,
        with_comments: [.prs | to_entries[] | select(.value.has_new_comments == true)] | length,
        conflict_pairs: ([.conflict_graph | to_entries[] | .value | length] | add // 0) / 2
    }' "$state_file"
}
