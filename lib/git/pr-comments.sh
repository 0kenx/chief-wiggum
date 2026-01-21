#!/usr/bin/env bash
# pr-comments.sh - PR comment fetching and filtering
#
# Provides functions for syncing and filtering PR comments for review.
# Used by `wiggum review task <patterns> sync` command.

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"

# Load review config on source
load_review_config

# Get current GitHub user
get_current_github_user() {
    gh api user --jq '.login' 2>/dev/null
}

# Find PRs matching task regex patterns
# Args: <comma-separated-patterns>
# Output: JSON array of PR info (number, headRefName, url)
find_prs_by_task_patterns() {
    local patterns="$1"

    # Convert comma-separated patterns to array
    IFS=',' read -ra pattern_array <<< "$patterns"

    local results="[]"
    for pattern in "${pattern_array[@]}"; do
        # Trim whitespace
        pattern=$(echo "$pattern" | xargs)

        # Search for PRs with branches matching task/$pattern*
        # Try open PRs first, then all PRs if nothing found
        local prs
        prs=$(gh pr list --search "head:task/$pattern" --state open --json number,headRefName,url 2>/dev/null || echo "[]")

        if [ "$(echo "$prs" | jq 'length')" -eq 0 ]; then
            # Try without state filter (might be merged/closed)
            prs=$(gh pr list --search "head:task/$pattern" --json number,headRefName,url 2>/dev/null || echo "[]")
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
    repo=$(gh repo view --json nameWithOwner -q '.nameWithOwner' 2>/dev/null)
    if [ -z "$repo" ]; then
        log_error "Could not determine repository"
        echo "[]"
        return 1
    fi

    # Fetch regular PR comments (issue comments)
    local issue_comments
    issue_comments=$(gh api "repos/$repo/issues/$pr_number/comments" --jq '[.[] | {
        type: "issue_comment",
        id: .id,
        author: .user.login,
        body: .body,
        created_at: .created_at,
        url: .html_url
    }]' 2>/dev/null || echo "[]")

    # Fetch review comments (inline code comments)
    local review_comments
    review_comments=$(gh api "repos/$repo/pulls/$pr_number/comments" --jq '[.[] | {
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
    }]' 2>/dev/null || echo "[]")

    # Fetch PR reviews (approve/request changes with body)
    local reviews
    reviews=$(gh api "repos/$repo/pulls/$pr_number/reviews" --jq '[.[] | select(.body != null and .body != "") | {
        type: "review",
        id: .id,
        author: .user.login,
        body: .body,
        state: .state,
        created_at: .submitted_at,
        url: .html_url
    }]' 2>/dev/null || echo "[]")

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
