#!/usr/bin/env bash
# issue-sync.sh - Core GitHub issue sync engine
#
# Two-way sync between GitHub Issues and .ralph/kanban.md:
#   - Down sync (GitHub -> kanban): Creates/updates kanban tasks from issues
#   - Up sync (kanban -> GitHub): Updates issue labels/state from kanban status
#
# Authority model:
#   - Pending tasks [ ]: remote-authoritative (content updates accepted)
#   - In-progress+ [=]/[P]/[x]/[*]/[N]: local-authoritative (content frozen)
set -euo pipefail

# Prevent double-sourcing
[ -n "${_GITHUB_ISSUE_SYNC_LOADED:-}" ] && return 0
_GITHUB_ISSUE_SYNC_LOADED=1

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"
source "$WIGGUM_HOME/lib/github/issue-config.sh"
source "$WIGGUM_HOME/lib/github/issue-state.sh"
source "$WIGGUM_HOME/lib/github/issue-parser.sh"
source "$WIGGUM_HOME/lib/github/issue-writer.sh"

# =============================================================================
# Internal: GitHub API Helpers
# =============================================================================

# Fetch open issues with the gate label
#
# Args:
#   label_filter - Required label name
#
# Returns: JSON array on stdout, "[]" on failure
_github_fetch_open_issues() {
    local label_filter="$1"

    local result exit_code=0
    result=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh issue list \
        --label "$label_filter" \
        --state open \
        --json number,title,body,labels,author,state,updatedAt \
        --limit 100 \
        2>&1) || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        if [ "$exit_code" -eq 124 ]; then
            log_error "GitHub issue list timeout"
        else
            log_error "GitHub issue list failed (exit: $exit_code)"
            log_debug "Output: $result"
        fi
        echo "[]"
        return 1
    fi

    echo "$result"
}

# Fetch recently closed issues with the gate label
#
# Args:
#   label_filter - Required label name
#
# Returns: JSON array on stdout, "[]" on failure
_github_fetch_closed_issues() {
    local label_filter="$1"

    local result exit_code=0
    result=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh issue list \
        --label "$label_filter" \
        --state closed \
        --json number,title,state,updatedAt \
        --limit 100 \
        2>&1) || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        if [ "$exit_code" -eq 124 ]; then
            log_error "GitHub closed issue list timeout"
        else
            log_error "GitHub closed issue list failed (exit: $exit_code)"
        fi
        echo "[]"
        return 1
    fi

    echo "$result"
}

# =============================================================================
# Internal: Kanban Helpers
# =============================================================================

# Get the current kanban status for a task
#
# Args:
#   kanban_file - Path to kanban.md
#   task_id     - Task ID (e.g., "GH-42")
#
# Returns: status char on stdout (" ", "=", "P", "x", "*", "N"), or empty if not found
_get_kanban_status() {
    local kanban_file="$1"
    local task_id="$2"

    # Use awk to find task and extract status char
    awk -v tid="$task_id" '
        $0 ~ "\\*\\*\\[" tid "\\]\\*\\*" {
            match($0, /\[.\]/)
            print substr($0, RSTART+1, 1)
            exit
        }
    ' "$kanban_file"
}

# Check if a task exists in the kanban
#
# Args:
#   kanban_file - Path to kanban.md
#   task_id     - Task ID
#
# Returns: 0 if exists, 1 if not
_kanban_task_exists() {
    local kanban_file="$1"
    local task_id="$2"

    grep -qF "**[$task_id]**" "$kanban_file" 2>/dev/null
}

# Build extra fields string for add_kanban_task
#
# Args:
#   complexity          - Complexity value (optional)
#   scope               - Scope text (optional)
#   out_of_scope        - Out of scope text (optional)
#   acceptance_criteria  - Acceptance criteria text (optional)
#
# Returns: newline-separated field lines on stdout
_build_extra_fields() {
    local complexity="${1:-}"
    local scope="${2:-}"
    local out_of_scope="${3:-}"
    local acceptance_criteria="${4:-}"
    local result=""

    if [ -n "$complexity" ]; then
        result="Complexity: $complexity"
    fi
    if [ -n "$scope" ]; then
        [ -n "$result" ] && result="$result"$'\n'
        result="${result}Scope: $scope"
    fi
    if [ -n "$out_of_scope" ]; then
        [ -n "$result" ] && result="$result"$'\n'
        result="${result}Out of Scope: $out_of_scope"
    fi
    if [ -n "$acceptance_criteria" ]; then
        [ -n "$result" ] && result="$result"$'\n'
        result="${result}Acceptance Criteria: $acceptance_criteria"
    fi

    echo "$result"
}

# =============================================================================
# Internal: Kanban Task Enumeration
# =============================================================================

# List all task IDs in the kanban file
#
# Args:
#   kanban_file - Path to kanban.md
#
# Returns: newline-separated task IDs on stdout
_list_all_kanban_task_ids() {
    local kanban_file="$1"

    awk '/^- \[.\] \*\*\[[A-Za-z]{2,10}-[0-9]{1,4}\]\*\*/ {
        match($0, /\*\*\[[A-Za-z]{2,10}-[0-9]{1,4}\]\*\*/)
        print substr($0, RSTART+3, RLENGTH-6)
    }' "$kanban_file"
}

# Parse kanban task fields into a JSON object
#
# Args:
#   kanban_file - Path to kanban.md
#   task_id     - Task ID to extract
#
# Returns: JSON object on stdout with brief, description, priority,
#          dependencies, status fields. Empty string if task not found.
_parse_kanban_task_fields() {
    local kanban_file="$1"
    local task_id="$2"

    # Extract raw tab-separated values via awk, then build JSON safely with jq
    local raw
    raw=$(awk -v tid="$task_id" '
    BEGIN { found = 0; brief = ""; desc = ""; pri = "MEDIUM"; deps = "none"; status = " " }

    # Match the task line
    $0 ~ "^- \\[.\\] \\*\\*\\[" tid "\\]\\*\\*" {
        found = 1
        # Extract status char
        match($0, /\[.\]/)
        status = substr($0, RSTART+1, 1)
        # Extract brief: everything after **[TASK-ID]**
        match($0, /\*\*\[[A-Za-z]{2,10}-[0-9]{1,4}\]\*\*/)
        if (RSTART > 0) {
            brief = substr($0, RSTART + RLENGTH)
            gsub(/^[[:space:]]+/, "", brief)
            gsub(/[[:space:]]+$/, "", brief)
        }
        next
    }

    # Inside the found task, parse indented fields
    found && /^  - Description:/ {
        sub(/^  - Description:[[:space:]]*/, "")
        desc = $0
        next
    }
    found && /^  - Priority:/ {
        sub(/^  - Priority:[[:space:]]*/, "")
        gsub(/[[:space:]]+$/, "")
        pri = $0
        next
    }
    found && /^  - Dependencies:/ {
        sub(/^  - Dependencies:[[:space:]]*/, "")
        gsub(/[[:space:]]+$/, "")
        deps = $0
        next
    }

    # Next task or section ends the current task
    found && /^- \[/ { found = 0 }
    found && /^## / { found = 0 }

    END {
        if (brief != "" || desc != "") {
            print brief "\t" desc "\t" pri "\t" deps "\t" status
        }
    }
    ' "$kanban_file")

    [ -n "$raw" ] || return 0

    local _brief _desc _pri _deps _status
    IFS=$'\t' read -r _brief _desc _pri _deps _status <<< "$raw"

    jq -n \
        --arg brief "${_brief:-}" \
        --arg description "${_desc:-}" \
        --arg priority "${_pri:-MEDIUM}" \
        --arg dependencies "${_deps:-none}" \
        --arg status "${_status:- }" \
        '{
            brief: $brief,
            description: $description,
            priority: $priority,
            dependencies: $dependencies,
            status: $status
        }'
}

# Get task IDs present in kanban but not tracked in sync state
#
# Args:
#   kanban_file - Path to kanban.md
#   ralph_dir   - Path to .ralph directory
#
# Returns: newline-separated untracked task IDs on stdout
_get_untracked_task_ids() {
    local kanban_file="$1"
    local ralph_dir="$2"

    local all_task_ids tracked_task_ids

    all_task_ids=$(_list_all_kanban_task_ids "$kanban_file")
    [ -n "$all_task_ids" ] || return 0

    # Build set of tracked task IDs from state file
    tracked_task_ids=$(github_sync_state_list_issues "$ralph_dir" | while IFS= read -r issue_num; do
        [ -n "$issue_num" ] || continue
        local entry
        entry=$(github_sync_state_get_issue "$ralph_dir" "$issue_num")
        [ "$entry" != "null" ] && echo "$entry" | jq -r '.task_id // empty'
    done)

    # Output task IDs not in tracked set
    local task_id
    while IFS= read -r task_id; do
        [ -n "$task_id" ] || continue
        if ! echo "$tracked_task_ids" | grep -qxF "$task_id"; then
            echo "$task_id"
        fi
    done <<< "$all_task_ids"
}

# =============================================================================
# Down Sync (GitHub -> Local)
# =============================================================================

# Sync open GitHub issues to local kanban
#
# Args:
#   ralph_dir - Path to .ralph directory
#   dry_run   - "true" to only show planned changes
#
# Returns: 0 on success, 1 on failure
github_issue_sync_down() {
    local ralph_dir="$1"
    local dry_run="${2:-false}"

    local kanban_file="$ralph_dir/kanban.md"
    if [ ! -f "$kanban_file" ]; then
        log_error "Kanban file not found: $kanban_file"
        return 1
    fi

    # Ensure sync state exists
    github_sync_state_init "$ralph_dir"

    local added=0
    local updated=0
    local skipped=0
    local closed_handled=0

    # --- Process OPEN issues ---
    log_debug "Fetching open issues with label '$GITHUB_SYNC_LABEL_FILTER'..."
    local open_issues
    open_issues=$(_github_fetch_open_issues "$GITHUB_SYNC_LABEL_FILTER") || return 1

    local issue_count
    issue_count=$(echo "$open_issues" | jq 'length')
    log_debug "Found $issue_count open issue(s)"

    local i=0
    while [ "$i" -lt "$issue_count" ]; do
        local issue_json
        issue_json=$(echo "$open_issues" | jq ".[$i]")
        ((++i))

        # Parse issue
        local parsed
        parsed=$(github_issue_parse "$issue_json") || {
            ((++skipped))
            continue
        }

        local number task_id brief description priority complexity dependencies
        local scope out_of_scope acceptance_criteria updated_at author_login author_id labels_json
        number=$(echo "$parsed" | jq -r '.number')
        task_id=$(echo "$parsed" | jq -r '.task_id')
        brief=$(echo "$parsed" | jq -r '.brief')
        description=$(echo "$parsed" | jq -r '.description')
        priority=$(echo "$parsed" | jq -r '.priority')
        complexity=$(echo "$parsed" | jq -r '.complexity')
        dependencies=$(echo "$parsed" | jq -r '.dependencies')
        scope=$(echo "$parsed" | jq -r '.scope')
        out_of_scope=$(echo "$parsed" | jq -r '.out_of_scope')
        acceptance_criteria=$(echo "$parsed" | jq -r '.acceptance_criteria')
        updated_at=$(echo "$parsed" | jq -r '.updated_at')
        author_login=$(echo "$parsed" | jq -r '.author_login')
        author_id=$(echo "$parsed" | jq -r '.author_id')
        labels_json=$(echo "$parsed" | jq '.labels')

        # Validate author
        if ! github_sync_is_author_allowed "$author_id" "$author_login"; then
            log_debug "Skipping issue #$number - author '$author_login' not allowed"
            ((++skipped))
            continue
        fi

        # Priority from labels takes precedence over body
        local label_priority
        label_priority=$(github_sync_get_priority_from_labels "$labels_json")
        if [ -n "$label_priority" ]; then
            priority="$label_priority"
        fi
        # Fallback to default if still empty
        priority="${priority:-$GITHUB_SYNC_DEFAULT_PRIORITY}"

        # Check kanban status
        if _kanban_task_exists "$kanban_file" "$task_id"; then
            local current_status
            current_status=$(_get_kanban_status "$kanban_file" "$task_id")

            # Only update pending tasks (remote-authoritative)
            if [ "$current_status" = " " ]; then
                # Check if content changed (compare description hash)
                local existing_entry
                existing_entry=$(github_sync_state_get_issue "$ralph_dir" "$number")
                local new_hash
                new_hash=$(github_sync_hash_content "$description")

                if [ "$existing_entry" != "null" ]; then
                    local old_hash
                    old_hash=$(echo "$existing_entry" | jq -r '.description_hash // ""')
                    local old_updated
                    old_updated=$(echo "$existing_entry" | jq -r '.last_remote_updated_at // ""')

                    if [ "$old_hash" != "$new_hash" ] && [ "$updated_at" != "$old_updated" ]; then
                        if [ "$dry_run" = "true" ]; then
                            echo "[dry-run] Update task $task_id (issue #$number) - content changed"
                        else
                            update_kanban_task_fields "$kanban_file" "$task_id" \
                                "$description" "$priority" "$dependencies" || true
                            log_debug "Updated task $task_id from issue #$number"
                        fi
                        ((++updated))
                    fi
                fi
            else
                log_debug "Task $task_id is $current_status - skipping content update (local-authoritative)"
            fi
        else
            # New task — add to kanban
            if [ "$dry_run" = "true" ]; then
                echo "[dry-run] Add task $task_id (issue #$number): $brief"
            else
                local extra_fields
                extra_fields=$(_build_extra_fields "$complexity" "$scope" "$out_of_scope" "$acceptance_criteria")

                if add_kanban_task "$kanban_file" "$task_id" "$brief" \
                        "$description" "$priority" "$dependencies" "$extra_fields"; then
                    log "Added task $task_id from issue #$number"
                else
                    log_debug "Task $task_id already exists (race condition) - skipping"
                fi
            fi
            ((++added))
        fi

        # Update sync state for this issue
        if [ "$dry_run" != "true" ]; then
            local desc_hash
            desc_hash=$(github_sync_hash_content "$description")
            local entry
            entry=$(github_sync_state_create_entry "$task_id" "$updated_at" " " "open" "$desc_hash")
            github_sync_state_set_issue "$ralph_dir" "$number" "$entry"
        fi
    done

    # --- Process CLOSED issues ---
    log_debug "Fetching closed issues with label '$GITHUB_SYNC_LABEL_FILTER'..."
    local closed_issues
    closed_issues=$(_github_fetch_closed_issues "$GITHUB_SYNC_LABEL_FILTER") || true

    local closed_count
    closed_count=$(echo "$closed_issues" | jq 'length' 2>/dev/null || echo 0)
    log_debug "Found $closed_count closed issue(s)"

    local j=0
    while [ "$j" -lt "$closed_count" ]; do
        local closed_json
        closed_json=$(echo "$closed_issues" | jq ".[$j]")
        ((++j))

        local closed_number
        closed_number=$(echo "$closed_json" | jq -r '.number')

        # Only process issues we're tracking
        local tracked
        tracked=$(github_sync_state_get_issue "$ralph_dir" "$closed_number")
        [ "$tracked" != "null" ] || continue

        local tracked_task_id
        tracked_task_id=$(echo "$tracked" | jq -r '.task_id')

        # Get current kanban status
        local current_status=""
        if _kanban_task_exists "$kanban_file" "$tracked_task_id"; then
            current_status=$(_get_kanban_status "$kanban_file" "$tracked_task_id")
        fi

        # Apply close rules per the authority model
        case "$current_status" in
            " ")
                # Pending task, human closed = won't do
                if [ "$dry_run" = "true" ]; then
                    echo "[dry-run] Mark $tracked_task_id as [N] (issue #$closed_number closed by human)"
                else
                    update_kanban_status "$kanban_file" "$tracked_task_id" "N"
                    log "Marked $tracked_task_id as [N] (issue #$closed_number closed)"
                fi
                ((++closed_handled))
                ;;
            "*")
                # Failed task, human closed = won't retry
                if [ "$dry_run" = "true" ]; then
                    echo "[dry-run] Mark $tracked_task_id as [N] (issue #$closed_number closed, was failed)"
                else
                    update_kanban_status "$kanban_file" "$tracked_task_id" "N"
                    log "Marked $tracked_task_id as [N] (issue #$closed_number closed, was failed)"
                fi
                ((++closed_handled))
                ;;
            *)
                # In-progress, pending-approval, completed, not-planned: no change
                log_debug "Issue #$closed_number closed but task $tracked_task_id is '$current_status' - no change"
                ;;
        esac

        # Update sync state
        if [ "$dry_run" != "true" ]; then
            local updated_entry
            updated_entry=$(echo "$tracked" | jq '.last_remote_state = "closed"')
            github_sync_state_set_issue "$ralph_dir" "$closed_number" "$updated_entry"
        fi
    done

    # Update down-sync timestamp
    if [ "$dry_run" != "true" ]; then
        github_sync_state_set_down_sync_time "$ralph_dir"
    fi

    log "Down-sync: added=$added updated=$updated skipped=$skipped closed_handled=$closed_handled"
}

# =============================================================================
# Up Sync (Local -> GitHub)
# =============================================================================

# Push local kanban status changes to GitHub issues
#
# Args:
#   ralph_dir - Path to .ralph directory
#   dry_run   - "true" to only show planned changes
#
# Returns: 0 on success
github_issue_sync_up() {
    local ralph_dir="$1"
    local dry_run="${2:-false}"

    local kanban_file="$ralph_dir/kanban.md"
    if [ ! -f "$kanban_file" ]; then
        log_error "Kanban file not found: $kanban_file"
        return 1
    fi

    # Ensure sync state exists
    github_sync_state_init "$ralph_dir"

    local synced=0
    local unchanged=0

    # Iterate over all tracked issues
    local issue_numbers
    issue_numbers=$(github_sync_state_list_issues "$ralph_dir")

    while IFS= read -r issue_number; do
        [ -n "$issue_number" ] || continue

        local entry
        entry=$(github_sync_state_get_issue "$ralph_dir" "$issue_number")
        [ "$entry" != "null" ] || continue

        local task_id last_synced_status last_remote_state pr_linked
        task_id=$(echo "$entry" | jq -r '.task_id')
        last_synced_status=$(echo "$entry" | jq -r '.last_synced_status // " "')
        last_remote_state=$(echo "$entry" | jq -r '.last_remote_state // "open"')
        pr_linked=$(echo "$entry" | jq -r '.pr_linked // false')

        # Get current kanban status
        local current_status=""
        if _kanban_task_exists "$kanban_file" "$task_id"; then
            current_status=$(_get_kanban_status "$kanban_file" "$task_id")
        else
            log_debug "Task $task_id not found in kanban - skipping up-sync"
            continue
        fi

        # Skip if status hasn't changed
        if [ "$current_status" = "$last_synced_status" ]; then
            ((++unchanged))
            continue
        fi

        # Perform the update
        github_issue_update_status "$issue_number" "$current_status" "$last_synced_status" \
            "$last_remote_state" "$dry_run"

        # Determine new remote state after our update
        local new_remote_state="$last_remote_state"
        if github_sync_should_close "$current_status"; then
            new_remote_state="closed"
        elif [ "$last_remote_state" = "closed" ] && github_sync_should_close "$last_synced_status"; then
            new_remote_state="open"
        fi

        # Check for PR link
        if [ "$pr_linked" = "false" ] && [ "$dry_run" != "true" ]; then
            # Look for PR URL in worker state
            local worker_dir pr_url=""
            worker_dir=$(find "$ralph_dir/workers" -maxdepth 1 -type d -name "worker-${task_id}-*" 2>/dev/null | head -1)
            if [ -n "$worker_dir" ] && [ -f "$worker_dir/pr_url" ]; then
                pr_url=$(cat "$worker_dir/pr_url" 2>/dev/null || true)
            fi
            if [ -n "$pr_url" ]; then
                github_issue_post_pr_link "$issue_number" "$pr_url"
                pr_linked="true"
            fi
        fi

        # Update sync state
        if [ "$dry_run" != "true" ]; then
            local updated_entry
            updated_entry=$(echo "$entry" | jq \
                --arg status "$current_status" \
                --arg state "$new_remote_state" \
                --arg linked "$pr_linked" \
                '.last_synced_status = $status |
                 .last_remote_state = $state |
                 .pr_linked = ($linked == "true")')
            github_sync_state_set_issue "$ralph_dir" "$issue_number" "$updated_entry"
        fi

        ((++synced))
    done <<< "$issue_numbers"

    # Update up-sync timestamp
    if [ "$dry_run" != "true" ]; then
        github_sync_state_set_up_sync_time "$ralph_dir"
    fi

    log "Up-sync: synced=$synced unchanged=$unchanged"
}

# =============================================================================
# Up Sync: Create Issues for Untracked Tasks
# =============================================================================

# Build a GitHub issue body from kanban task fields
#
# Args:
#   description  - Task description
#   priority     - Priority string (e.g., "HIGH")
#   dependencies - Dependency string (e.g., "TASK-001, TASK-002" or "none")
#
# Returns: formatted body text on stdout
_build_issue_body() {
    local description="$1"
    local priority="${2:-MEDIUM}"
    local dependencies="${3:-none}"

    local body=""
    [ -n "$description" ] && body="$description"$'\n\n'
    body="${body}Priority: $priority"$'\n'
    body="${body}Dependencies: $dependencies"
    echo "$body"
}

# Get the priority label name for a priority string
#
# Args:
#   priority - Priority string (e.g., "HIGH")
#
# Returns: label name on stdout (e.g., "priority:high"), or empty
_get_priority_label() {
    local priority="$1"
    local mapping="${GITHUB_SYNC_PRIORITY_LABELS:-}"

    # Guard: need a non-trivial JSON object
    [[ -n "$mapping" && "$mapping" != "{}" ]] || return 0

    local result
    result=$(echo "$mapping" | \
        jq -r --arg pri "$priority" \
        'to_entries[] | select(.value == $pri) | .key' 2>/dev/null) || true

    # Only output valid label names (must contain a letter)
    if [[ -n "$result" && "$result" =~ [a-zA-Z] ]]; then
        echo "$result"
    fi
}

# Create GitHub issues for untracked kanban tasks and sync them
#
# Args:
#   ralph_dir    - Path to .ralph directory
#   task_filter  - Specific task ID or "all"
#   dry_run      - "true" to only show planned changes
#   skip_confirm - "true" to skip confirmation prompt
#
# Returns: 0 on success, 1 on failure
github_issue_sync_up_create() {
    local ralph_dir="$1"
    local task_filter="$2"
    local dry_run="${3:-false}"
    local skip_confirm="${4:-false}"

    local kanban_file="$ralph_dir/kanban.md"
    if [ ! -f "$kanban_file" ]; then
        log_error "Kanban file not found: $kanban_file"
        return 1
    fi

    # Ensure sync state exists
    github_sync_state_init "$ralph_dir"

    # Determine which tasks to process
    local untracked_ids
    if [ "$task_filter" = "all" ]; then
        untracked_ids=$(_get_untracked_task_ids "$kanban_file" "$ralph_dir")
    else
        # Verify specific task exists in kanban
        if ! _kanban_task_exists "$kanban_file" "$task_filter"; then
            log_error "Task $task_filter not found in kanban"
            return 1
        fi
        # Check if already tracked
        local tracked_ids
        tracked_ids=$(_get_untracked_task_ids "$kanban_file" "$ralph_dir")
        if [ -n "$tracked_ids" ] && echo "$tracked_ids" | grep -qxF "$task_filter"; then
            untracked_ids="$task_filter"
        else
            echo "Task $task_filter is already tracked by a GitHub issue."
            return 0
        fi
    fi

    if [ -z "$untracked_ids" ]; then
        echo "No untracked tasks to create issues for."
        return 0
    fi

    # Count tasks
    local task_count
    task_count=$(echo "$untracked_ids" | wc -l | tr -d ' ')

    # Dry-run mode: show what would be created
    if [ "$dry_run" = "true" ]; then
        echo "[dry-run] Would create GitHub issues for $task_count untracked task(s):"
        local tid
        while IFS= read -r tid; do
            [ -n "$tid" ] || continue
            local fields
            fields=$(_parse_kanban_task_fields "$kanban_file" "$tid")
            if [ -n "$fields" ]; then
                local brief priority
                brief=$(echo "$fields" | jq -r '.brief // ""')
                priority=$(echo "$fields" | jq -r '.priority // "MEDIUM"')
                echo "  $tid: $brief (Priority: $priority)"
            else
                echo "  $tid: (could not parse fields)"
            fi
        done <<< "$untracked_ids"
        return 0
    fi

    # Confirmation prompt
    if [ "$skip_confirm" != "true" ]; then
        if [ "$task_filter" = "all" ]; then
            printf 'Create GitHub issues for %d untracked task(s)? [y/N] ' "$task_count"
        else
            printf 'Create GitHub issue for %s? [y/N] ' "$task_filter"
        fi
        local answer
        read -r answer
        case "$answer" in
            [yY]|[yY][eE][sS]) ;;
            *)
                echo "Aborted."
                return 0
                ;;
        esac
    fi

    # Create issues
    local created=0
    local failed=0
    local task_id
    while IFS= read -r task_id; do
        [ -n "$task_id" ] || continue

        local fields
        fields=$(_parse_kanban_task_fields "$kanban_file" "$task_id")
        if [ -z "$fields" ]; then
            log_warn "Could not parse fields for $task_id - skipping"
            ((++failed))
            continue
        fi

        local brief description priority dependencies status
        brief=$(echo "$fields" | jq -r '.brief // ""')
        description=$(echo "$fields" | jq -r '.description // ""')
        priority=$(echo "$fields" | jq -r '.priority // "MEDIUM"')
        dependencies=$(echo "$fields" | jq -r '.dependencies // "none"')
        status=$(echo "$fields" | jq -r '.status // " "')

        # Build issue body
        local body
        body=$(_build_issue_body "$description" "$priority" "$dependencies")

        # Determine priority label
        local priority_label
        priority_label=$(_get_priority_label "$priority")

        # Create the issue
        local issue_number
        if issue_number=$(github_issue_create "$task_id" "$brief" "$body" "$priority_label"); then
            echo "Created issue #$issue_number for $task_id"

            # Add state entry
            local desc_hash entry
            desc_hash=$(github_sync_hash_content "$description")
            entry=$(github_sync_state_create_entry "$task_id" "" "$status" "open" "$desc_hash")
            github_sync_state_set_issue "$ralph_dir" "$issue_number" "$entry"

            # Apply current status label if not pending
            if [ "$status" != " " ]; then
                local status_label
                status_label=$(github_sync_get_status_label "$status")
                if [ -n "$status_label" ]; then
                    github_issue_add_label "$issue_number" "$status_label"
                fi
                # Close if status warrants it
                if github_sync_should_close "$status"; then
                    github_issue_close "$issue_number"
                fi
            fi

            ((++created))
        else
            log_error "Failed to create issue for $task_id"
            ((++failed))
        fi
    done <<< "$untracked_ids"

    log "Sync up create: created=$created failed=$failed"

    # Run normal up-sync for all tracked issues (including newly created)
    if [ "$created" -gt 0 ]; then
        log_debug "Running up-sync for newly created issues..."
        github_issue_sync_up "$ralph_dir" "false"
    fi
}

# =============================================================================
# Combined Sync
# =============================================================================

# Run a full sync cycle (down + up)
#
# Args:
#   ralph_dir - Path to .ralph directory
#   dry_run   - "true" to only show planned changes
#
# Returns: 0 on success
github_issue_sync() {
    local ralph_dir="$1"
    local dry_run="${2:-false}"

    log_debug "Starting GitHub issue sync cycle..."

    # Down sync first (new issues -> kanban)
    github_issue_sync_down "$ralph_dir" "$dry_run" || {
        log_error "Down-sync failed"
        return 1
    }

    # Up sync (kanban status -> GitHub)
    github_issue_sync_up "$ralph_dir" "$dry_run" || {
        log_error "Up-sync failed"
        return 1
    }

    log_debug "GitHub issue sync cycle complete"
}

# =============================================================================
# Status Report
# =============================================================================

# Print a summary of sync state
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: 0 always (outputs to stdout)
github_issue_sync_status() {
    local ralph_dir="$1"

    local state_file="$ralph_dir/github-sync-state.json"
    if [ ! -f "$state_file" ]; then
        echo "GitHub issue sync: not initialized (no state file)"
        return 0
    fi

    local state
    state=$(cat "$state_file")

    local version last_down last_up issue_count
    version=$(echo "$state" | jq -r '.version // "unknown"')
    last_down=$(echo "$state" | jq -r '.last_down_sync_at // 0')
    last_up=$(echo "$state" | jq -r '.last_up_sync_at // 0')
    issue_count=$(echo "$state" | jq '.issues | length')

    echo "GitHub Issue Sync Status"
    echo "========================"
    echo "  State version: $version"
    echo "  Tracked issues: $issue_count"

    if [ "$last_down" -gt 0 ]; then
        local down_date
        down_date=$(date -d "@$last_down" -Iseconds 2>/dev/null || date -r "$last_down" -Iseconds 2>/dev/null || echo "epoch:$last_down")
        echo "  Last down-sync: $down_date"
    else
        echo "  Last down-sync: never"
    fi

    if [ "$last_up" -gt 0 ]; then
        local up_date
        up_date=$(date -d "@$last_up" -Iseconds 2>/dev/null || date -r "$last_up" -Iseconds 2>/dev/null || echo "epoch:$last_up")
        echo "  Last up-sync: $up_date"
    else
        echo "  Last up-sync: never"
    fi

    if [ "$issue_count" -gt 0 ]; then
        echo ""
        echo "  Tracked Issues:"
        echo "$state" | jq -r '.issues | to_entries[] | "    #\(.key): \(.value.task_id) (status: \(.value.last_synced_status), remote: \(.value.last_remote_state))"'
    fi
}
