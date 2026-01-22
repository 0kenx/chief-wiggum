#!/usr/bin/env bash
# pr-comments.sh - PR comment fetching and filtering
#
# Provides functions for syncing and filtering PR comments for review.
# Used by `wiggum review task <patterns> sync` command.
set -euo pipefail

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"

# Load review config on source
load_review_config

# GitHub API timeout (can be overridden by environment)
WIGGUM_GH_TIMEOUT="${WIGGUM_GH_TIMEOUT:-30}"

# Execute gh API command with timeout and error handling
#
# Args:
#   endpoint    - The API endpoint (e.g., "repos/owner/repo/pulls/123/comments")
#   jq_filter   - Optional jq filter to apply (defaults to ".")
#   timeout_sec - Optional timeout in seconds (defaults to WIGGUM_GH_TIMEOUT)
#
# Returns:
#   0 on success, 1 on failure
#   Outputs JSON result on success, "[]" on failure
#   Logs errors to stderr
_gh_api_with_error_handling() {
    local endpoint="$1"
    local jq_filter="${2:-.}"
    local timeout_sec="${3:-$WIGGUM_GH_TIMEOUT}"

    local result exit_code

    # Run gh api with timeout
    if result=$(timeout "$timeout_sec" gh api "$endpoint" --jq "$jq_filter" 2>&1); then
        exit_code=$?
        if [ $exit_code -eq 0 ]; then
            echo "$result"
            return 0
        fi
    else
        exit_code=$?
    fi

    # Handle timeout specifically
    if [ $exit_code -eq 124 ]; then
        log_error "GitHub API timeout after ${timeout_sec}s: $endpoint"
        echo "[]"
        return 1
    fi

    # Handle other errors
    log_error "GitHub API failed (exit: $exit_code): $endpoint"
    if [ -n "$result" ]; then
        log_debug "API error response: $result"
    fi
    echo "[]"
    return 1
}

# Execute gh pr list with timeout and error handling
#
# Args:
#   search_query - The search query for gh pr list
#   json_fields  - Fields to return (e.g., "number,headRefName,url")
#   timeout_sec  - Optional timeout in seconds (defaults to WIGGUM_GH_TIMEOUT)
#
# Returns:
#   0 on success, 1 on failure
#   Outputs JSON array on success, "[]" on failure
_gh_pr_list_with_error_handling() {
    local search_query="$1"
    local json_fields="$2"
    local timeout_sec="${3:-$WIGGUM_GH_TIMEOUT}"
    local extra_args="${4:-}"

    local result exit_code

    # Run gh pr list with timeout
    if result=$(timeout "$timeout_sec" gh pr list --search "$search_query" --json "$json_fields" $extra_args 2>&1); then
        exit_code=$?
        if [ $exit_code -eq 0 ]; then
            echo "$result"
            return 0
        fi
    else
        exit_code=$?
    fi

    # Handle timeout
    if [ $exit_code -eq 124 ]; then
        log_error "GitHub PR list timeout after ${timeout_sec}s: $search_query"
        echo "[]"
        return 1
    fi

    # Handle other errors
    log_error "GitHub PR list failed (exit: $exit_code): $search_query"
    if [ -n "$result" ]; then
        log_debug "PR list error: $result"
    fi
    echo "[]"
    return 1
}

# Get current GitHub user
get_current_github_user() {
    timeout "${WIGGUM_GH_TIMEOUT:-30}" gh api user --jq '.login' 2>/dev/null
}

# Find PRs matching task regex patterns
# Args: <comma-separated-patterns>
# Output: JSON array of PR info (number, headRefName, url)
# Supports:
#   - Full task ID: PIPELINE-001, TASK-030
#   - Partial number: 001, 030 (searches for branches containing the pattern)
find_prs_by_task_patterns() {
    local patterns="$1"

    # Convert comma-separated patterns to array
    IFS=',' read -ra pattern_array <<< "$patterns"

    local results="[]"
    for pattern in "${pattern_array[@]}"; do
        # Trim whitespace
        pattern=$(echo "$pattern" | xargs)

        local prs="[]"

        # Try exact match first: head:task/$pattern
        prs=$(_gh_pr_list_with_error_handling "head:task/$pattern" "number,headRefName,url" "$WIGGUM_GH_TIMEOUT" "--state open")

        # If not found, try partial match by listing all task/* branches and filtering
        if [ "$(echo "$prs" | jq 'length')" -eq 0 ]; then
            # Get all PRs with task/ branches and filter locally for pattern match
            local all_task_prs
            all_task_prs=$(_gh_pr_list_with_error_handling "head:task/" "number,headRefName,url" "$WIGGUM_GH_TIMEOUT" "--state open")
            prs=$(echo "$all_task_prs" | jq --arg pat "$pattern" '[.[] | select(.headRefName | contains($pat))]')
        fi

        # If still not found, try without state filter (might be merged/closed)
        if [ "$(echo "$prs" | jq 'length')" -eq 0 ]; then
            prs=$(_gh_pr_list_with_error_handling "head:task/$pattern" "number,headRefName,url")

            if [ "$(echo "$prs" | jq 'length')" -eq 0 ]; then
                local all_task_prs
                all_task_prs=$(_gh_pr_list_with_error_handling "head:task/" "number,headRefName,url")
                prs=$(echo "$all_task_prs" | jq --arg pat "$pattern" '[.[] | select(.headRefName | contains($pat))]')
            fi
        fi

        # Merge results, keeping unique by PR number
        results=$(echo "$results" "$prs" | jq -s 'add | unique_by(.number)')
    done

    echo "$results"
}

# Fetch all comments for a PR (regular and review comments)
# Args: <pr_number>
# Output: JSON array of comments with author, body, path, line info
fetch_pr_comments() {
    local pr_number="$1"

    # Get repository info
    local repo
    repo=$(timeout "$WIGGUM_GH_TIMEOUT" gh repo view --json nameWithOwner -q '.nameWithOwner' 2>/dev/null)
    if [ -z "$repo" ]; then
        log_error "Could not determine repository (gh repo view failed or timed out)"
        echo "[]"
        return 1
    fi

    # Fetch regular PR comments (issue comments)
    local issue_comments
    issue_comments=$(_gh_api_with_error_handling "repos/$repo/issues/$pr_number/comments" '[.[] | {
        type: "issue_comment",
        id: .id,
        author: .user.login,
        body: .body,
        created_at: .created_at,
        url: .html_url
    }]')

    # Fetch review comments (inline code comments)
    local review_comments
    review_comments=$(_gh_api_with_error_handling "repos/$repo/pulls/$pr_number/comments" '[.[] | {
        type: "review_comment",
        id: .id,
        author: .user.login,
        body: .body,
        path: .path,
        line: .line,
        original_line: .original_line,
        side: .side,
        created_at: .created_at,
        url: .html_url,
        diff_hunk: .diff_hunk
    }]')

    # Fetch PR reviews (approve/request changes with body)
    local reviews
    reviews=$(_gh_api_with_error_handling "repos/$repo/pulls/$pr_number/reviews" '[.[] | select(.body != null and .body != "") | {
        type: "review",
        id: .id,
        author: .user.login,
        body: .body,
        state: .state,
        created_at: .submitted_at,
        url: .html_url
    }]')

    # Merge all comments and sort by created_at
    echo "$issue_comments" "$review_comments" "$reviews" | jq -s 'add | sort_by(.created_at)'
}

# Filter comments by approved authors
# Args: <comments_json> <approved_authors_csv> <current_user>
# Output: Filtered JSON array
filter_comments_by_authors() {
    local comments="$1"
    local approved_authors="$2"
    local current_user="$3"

    # Build the full author list including current user
    local all_authors="$approved_authors"
    if [ -n "$current_user" ]; then
        all_authors="$all_authors,$current_user"
    fi

    # Filter using jq - case-insensitive matching
    echo "$comments" | jq --arg authors "$all_authors" '
        ($authors | split(",") | map(gsub("^\\s+|\\s+$"; "") | ascii_downcase)) as $approved |
        [.[] | select((.author | ascii_downcase) as $a | $approved | any(. == $a))]
    '
}

# Convert comments to markdown format
# Args: <comments_json> <pr_number> <pr_url> <branch_name>
# Output: Markdown string
comments_to_markdown() {
    local comments="$1"
    local pr_number="$2"
    local pr_url="$3"
    local branch_name="$4"

    # Generate markdown using jq
    echo "$comments" | jq -r --arg pr_number "$pr_number" --arg pr_url "$pr_url" --arg branch "$branch_name" '
        "## PR #" + $pr_number + " (" + $branch + ")\n\n" +
        "**URL:** " + $pr_url + "\n\n" +
        "---\n\n" +
        (. | map(
            "### " +
            (if .type == "review_comment" then
                "Code Review: `" + .path + "`" + (if .line then " (line " + (.line|tostring) + ")" else "" end)
            elif .type == "review" then
                "Review (" + .state + ")"
            else
                "Comment"
            end) + "\n\n" +
            "**Author:** " + .author + "  \n" +
            "**Date:** " + .created_at + "  \n" +
            "**ID:** " + (.id|tostring) + "\n\n" +
            (if .diff_hunk then "```diff\n" + .diff_hunk + "\n```\n\n" else "" end) +
            .body + "\n\n---\n"
        ) | join("\n"))
    '
}

# Find worker directory by task ID pattern
# Args: <ralph_dir> <task_pattern>
# Output: Worker directory path or empty string
# Supports:
#   - Full task ID: PIPELINE-001, TASK-030
#   - Partial number: 001, 030 (matches *-001-*, *-030-*)
find_worker_by_task_id() {
    local ralph_dir="$1"
    local task_pattern="$2"
    local workers_dir="$ralph_dir/workers"

    if [ ! -d "$workers_dir" ]; then
        return
    fi

    local worker_dir

    # Try exact prefix match first: worker-PIPELINE-001-*
    worker_dir=$(find "$workers_dir" -maxdepth 1 -type d -name "worker-$task_pattern-*" 2>/dev/null | sort -r | head -1)

    # If not found, try matching pattern anywhere (e.g., "001" matches "worker-PIPELINE-001-*")
    if [ -z "$worker_dir" ]; then
        worker_dir=$(find "$workers_dir" -maxdepth 1 -type d -name "worker-*$task_pattern*" 2>/dev/null | sort -r | head -1)
    fi

    if [ -n "$worker_dir" ] && [ -d "$worker_dir" ]; then
        echo "$worker_dir"
    fi
}

# Check if a PR has new comments since last sync
# Args: <pr_number> <sync_state_file>
# Returns: 0 if new comments exist, 1 otherwise
# Side effect: Updates sync state file with current comment IDs
_check_for_new_comments() {
    local pr_number="$1"
    local sync_state_file="$2"

    # Get repository info
    local repo
    repo=$(timeout "$WIGGUM_GH_TIMEOUT" gh repo view --json nameWithOwner -q '.nameWithOwner' 2>/dev/null)
    if [ -z "$repo" ]; then
        log_error "Could not determine repository for comment check"
        return 1
    fi

    # Fetch current comment IDs (all types) with error handling
    local current_ids issue_ids review_comment_ids review_ids
    issue_ids=$(_gh_api_with_error_handling "repos/$repo/issues/$pr_number/comments" '.[].id')
    review_comment_ids=$(_gh_api_with_error_handling "repos/$repo/pulls/$pr_number/comments" '.[].id')
    review_ids=$(_gh_api_with_error_handling "repos/$repo/pulls/$pr_number/reviews" '.[].id')

    current_ids=$(
        {
            echo "$issue_ids"
            echo "$review_comment_ids"
            echo "$review_ids"
        } | grep -v '^\[\]$' | sort -n | tr '\n' ',' | sed 's/,$//'
    )

    # Get stored comment IDs for this PR
    local stored_ids
    stored_ids=$(jq -r --arg pr "$pr_number" '.[$pr] // ""' "$sync_state_file" 2>/dev/null)

    # Compare
    if [ "$current_ids" != "$stored_ids" ]; then
        # New comments detected - update state
        _update_sync_state "$pr_number" "$current_ids" "$sync_state_file"
        return 0
    fi

    return 1
}

# Update sync state file with current comment IDs
# Args: <pr_number> <comment_ids_csv> <sync_state_file>
_update_sync_state() {
    local pr_number="$1"
    local comment_ids="$2"
    local sync_state_file="$3"

    local temp_file
    temp_file=$(mktemp)

    jq --arg pr "$pr_number" --arg ids "$comment_ids" \
        '.[$pr] = $ids' "$sync_state_file" > "$temp_file" 2>/dev/null

    if [ -s "$temp_file" ]; then
        mv "$temp_file" "$sync_state_file"
    else
        rm -f "$temp_file"
    fi
}

# Main sync function
# Args: <task_patterns> <output_dir>
# Creates: <output_dir>/task-comments.md
sync_pr_comments() {
    local patterns="$1"
    local output_dir="$2"

    # Get current GitHub user
    local current_user
    current_user=$(get_current_github_user)
    if [ -z "$current_user" ]; then
        log_error "Could not determine current GitHub user. Are you logged in with 'gh auth login'?"
        return 1
    fi

    log "Current GitHub user: $current_user"
    log "Approved authors: $WIGGUM_APPROVED_AUTHORS"

    # Find matching PRs
    local prs pr_count
    prs=$(find_prs_by_task_patterns "$patterns")
    pr_count=$(echo "$prs" | jq 'length')

    if [ "$pr_count" -eq 0 ]; then
        log "No PRs found matching patterns: $patterns"
        return 0
    fi

    log "Found $pr_count PR(s) matching patterns"

    # Ensure output directory exists
    mkdir -p "$output_dir"
    local output_file="$output_dir/task-comments.md"

    # Write header
    {
        echo "# PR Comments for Tasks: $patterns"
        echo ""
        echo "**Synced at:** $(date -Iseconds)"
        echo "**Approved authors:** $WIGGUM_APPROVED_AUTHORS, $current_user"
        echo ""
        echo "---"
        echo ""
    } > "$output_file"

    local total_comments=0

    # Process each PR
    echo "$prs" | jq -c '.[]' | while read -r pr; do
        local pr_number pr_url branch
        pr_number=$(echo "$pr" | jq -r '.number')
        pr_url=$(echo "$pr" | jq -r '.url')
        branch=$(echo "$pr" | jq -r '.headRefName')

        log "Fetching comments for PR #$pr_number ($branch)..."

        local comments filtered comment_count
        comments=$(fetch_pr_comments "$pr_number")
        filtered=$(filter_comments_by_authors "$comments" "$WIGGUM_APPROVED_AUTHORS" "$current_user")
        comment_count=$(echo "$filtered" | jq 'length')

        log "  Found $comment_count relevant comment(s) from approved authors"

        if [ "$comment_count" -gt 0 ]; then
            comments_to_markdown "$filtered" "$pr_number" "$pr_url" "$branch" >> "$output_file"
            total_comments=$((total_comments + comment_count))
        fi
    done

    log "Comments synced to: $output_file"
    echo "$output_file"
}
