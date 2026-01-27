#!/usr/bin/env bash
# conflict-queue.sh - Multi-PR conflict queue management
#
# Manages a queue of PRs that failed to merge due to conflicts. Groups related
# conflicts by shared files and coordinates batch resolution via LLM planner.
#
# Queue file: .ralph/conflict-queue.json
# Format:
# {
#   "queue": [
#     {"task_id": "FEAT-001", "worker_dir": "...", "pr_number": 42, "affected_files": ["src/api.ts"], "batch_id": null}
#   ],
#   "batches": {
#     "batch-123": {"status": "planning", "task_ids": ["FEAT-001", "FEAT-002"], "common_files": ["src/api.ts"]}
#   }
# }
set -euo pipefail

[ -n "${_CONFLICT_QUEUE_LOADED:-}" ] && return 0
_CONFLICT_QUEUE_LOADED=1

# Source dependencies
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"

# Initialize conflict queue if it doesn't exist
#
# Args:
#   ralph_dir - Ralph directory path
conflict_queue_init() {
    local ralph_dir="$1"
    local queue_file="$ralph_dir/conflict-queue.json"

    if [ ! -f "$queue_file" ]; then
        echo '{"queue":[],"batches":{}}' > "$queue_file"
    fi
}

# Add a task to the conflict queue
#
# Args:
#   ralph_dir      - Ralph directory path
#   task_id        - Task identifier
#   worker_dir     - Worker directory path
#   pr_number      - PR number
#   affected_files - JSON array of affected file paths
#
# Returns: 0 on success
conflict_queue_add() {
    local ralph_dir="$1"
    local task_id="$2"
    local worker_dir="$3"
    local pr_number="$4"
    local affected_files="$5"

    local queue_file="$ralph_dir/conflict-queue.json"
    conflict_queue_init "$ralph_dir"

    # Use file lock for concurrent access
    local lock_file="$ralph_dir/.conflict-queue.lock"

    (
        flock -x 200

        # Check if task already in queue
        if jq -e ".queue[] | select(.task_id == \"$task_id\")" "$queue_file" >/dev/null 2>&1; then
            log "Task $task_id already in conflict queue"
            return 0
        fi

        # Add to queue
        local timestamp
        timestamp=$(date -Iseconds)

        local entry
        entry=$(jq -n \
            --arg task_id "$task_id" \
            --arg worker_dir "$worker_dir" \
            --argjson pr_number "$pr_number" \
            --argjson affected_files "$affected_files" \
            --arg added_at "$timestamp" \
            '{
                task_id: $task_id,
                worker_dir: $worker_dir,
                pr_number: $pr_number,
                affected_files: $affected_files,
                added_at: $added_at,
                batch_id: null
            }')

        jq --argjson entry "$entry" '.queue += [$entry]' "$queue_file" > "$queue_file.tmp"
        mv "$queue_file.tmp" "$queue_file"

        log "Added $task_id to conflict queue (PR #$pr_number)"
    ) 200>"$lock_file"
}

# Remove a task from the conflict queue
#
# Args:
#   ralph_dir - Ralph directory path
#   task_id   - Task identifier
conflict_queue_remove() {
    local ralph_dir="$1"
    local task_id="$2"

    local queue_file="$ralph_dir/conflict-queue.json"
    [ -f "$queue_file" ] || return 0

    local lock_file="$ralph_dir/.conflict-queue.lock"

    (
        flock -x 200

        jq --arg task_id "$task_id" '.queue = [.queue[] | select(.task_id != $task_id)]' \
            "$queue_file" > "$queue_file.tmp"
        mv "$queue_file.tmp" "$queue_file"
    ) 200>"$lock_file"
}

# Group related conflicts by shared files
#
# Scans the queue and identifies tasks that have overlapping affected files.
# Tasks with common files should be resolved together.
#
# Args:
#   ralph_dir - Ralph directory path
#
# Returns: JSON array of groups, each with task_ids and common_files
conflict_queue_group_related() {
    local ralph_dir="$1"

    local queue_file="$ralph_dir/conflict-queue.json"
    [ -f "$queue_file" ] || { echo "[]"; return 0; }

    # Get unbatched queue entries
    local unbatched
    unbatched=$(jq '[.queue[] | select(.batch_id == null)]' "$queue_file")

    local count
    count=$(echo "$unbatched" | jq 'length')

    if [ "$count" -lt 2 ]; then
        echo "[]"
        return 0
    fi

    # Build file -> tasks mapping and find overlaps
    # This is a simplified grouping - tasks share a group if they have any common file
    local groups='[]'
    local processed='[]'

    while read -r task_json; do
        local task_id
        task_id=$(echo "$task_json" | jq -r '.task_id')

        # Skip if already processed
        if echo "$processed" | jq -e ". | index(\"$task_id\")" >/dev/null 2>&1; then
            continue
        fi

        local task_files
        task_files=$(echo "$task_json" | jq '.affected_files')

        # Find all tasks with overlapping files
        local group_tasks='["'$task_id'"]'
        local common_files="$task_files"

        while read -r other_json; do
            local other_id
            other_id=$(echo "$other_json" | jq -r '.task_id')

            [ "$other_id" = "$task_id" ] && continue

            # Skip if already processed
            if echo "$processed" | jq -e ". | index(\"$other_id\")" >/dev/null 2>&1; then
                continue
            fi

            local other_files
            other_files=$(echo "$other_json" | jq '.affected_files')

            # Check for file overlap
            local overlap
            overlap=$(jq -n --argjson a "$task_files" --argjson b "$other_files" \
                '[$a[], $b[]] | group_by(.) | map(select(length > 1) | .[0]) | unique')

            if [ "$(echo "$overlap" | jq 'length')" -gt 0 ]; then
                group_tasks=$(echo "$group_tasks" | jq --arg id "$other_id" '. += [$id]')
                common_files=$(echo "$overlap" | jq '.')
            fi
        done < <(echo "$unbatched" | jq -c '.[]')

        # Only create group if multiple tasks
        local group_size
        group_size=$(echo "$group_tasks" | jq 'length')

        if [ "$group_size" -ge 2 ]; then
            local group
            group=$(jq -n \
                --argjson task_ids "$group_tasks" \
                --argjson common_files "$common_files" \
                '{task_ids: $task_ids, common_files: $common_files}')
            groups=$(echo "$groups" | jq --argjson g "$group" '. += [$g]')
        fi

        # Mark all tasks in group as processed
        processed=$(echo "$processed" | jq --argjson g "$group_tasks" '. + $g | unique')
    done < <(echo "$unbatched" | jq -c '.[]')

    echo "$groups"
}

# Check if batch threshold is met
#
# Args:
#   ralph_dir - Ralph directory path
#
# Returns: 0 if batch is ready, 1 otherwise
conflict_queue_batch_ready() {
    local ralph_dir="$1"

    local groups
    groups=$(conflict_queue_group_related "$ralph_dir")

    local count
    count=$(echo "$groups" | jq 'length')

    [ "$count" -gt 0 ]
}

# Create a batch from grouped conflicts
#
# Args:
#   ralph_dir - Ralph directory path
#   task_ids  - JSON array of task IDs to batch
#
# Returns: batch_id
conflict_queue_create_batch() {
    local ralph_dir="$1"
    local task_ids="$2"

    local queue_file="$ralph_dir/conflict-queue.json"
    local lock_file="$ralph_dir/.conflict-queue.lock"

    local batch_id
    batch_id="batch-$(date +%s)"

    (
        flock -x 200

        # Get common files for these tasks
        local common_files='[]'
        while read -r task_id; do
            local files
            files=$(jq -r --arg id "$task_id" '.queue[] | select(.task_id == $id) | .affected_files' "$queue_file")
            if [ -n "$files" ] && [ "$files" != "null" ]; then
                common_files=$(jq -n --argjson a "$common_files" --argjson b "$files" \
                    '[$a[], $b[]] | unique')
            fi
        done < <(echo "$task_ids" | jq -r '.[]')

        # Create batch entry
        local batch
        batch=$(jq -n \
            --arg batch_id "$batch_id" \
            --argjson task_ids "$task_ids" \
            --argjson common_files "$common_files" \
            --arg created_at "$(date -Iseconds)" \
            '{
                status: "pending",
                task_ids: $task_ids,
                common_files: $common_files,
                created_at: $created_at
            }')

        # Update queue: add batch and mark tasks
        jq --arg batch_id "$batch_id" --argjson batch "$batch" --argjson task_ids "$task_ids" '
            .batches[$batch_id] = $batch |
            .queue = [.queue[] | if (.task_id | IN($task_ids[])) then .batch_id = $batch_id else . end]
        ' "$queue_file" > "$queue_file.tmp"
        mv "$queue_file.tmp" "$queue_file"
    ) 200>"$lock_file"

    local task_count
    task_count=$(echo "$task_ids" | jq 'length')
    echo "$batch_id"
    log "Created conflict batch $batch_id with $task_count tasks"
}

# Update batch status
#
# Args:
#   ralph_dir - Ralph directory path
#   batch_id  - Batch identifier
#   status    - New status (pending, planning, planned, resolving, resolved, failed)
conflict_queue_update_batch_status() {
    local ralph_dir="$1"
    local batch_id="$2"
    local status="$3"

    local queue_file="$ralph_dir/conflict-queue.json"
    local lock_file="$ralph_dir/.conflict-queue.lock"

    (
        flock -x 200

        jq --arg batch_id "$batch_id" --arg status "$status" \
            '.batches[$batch_id].status = $status' \
            "$queue_file" > "$queue_file.tmp"
        mv "$queue_file.tmp" "$queue_file"
    ) 200>"$lock_file"
}

# Get batch info
#
# Args:
#   ralph_dir - Ralph directory path
#   batch_id  - Batch identifier
#
# Returns: JSON object with batch info
conflict_queue_get_batch() {
    local ralph_dir="$1"
    local batch_id="$2"

    local queue_file="$ralph_dir/conflict-queue.json"
    [ -f "$queue_file" ] || { echo "null"; return 1; }

    jq --arg batch_id "$batch_id" '.batches[$batch_id]' "$queue_file"
}

# Get pending batches that need planning
#
# Args:
#   ralph_dir - Ralph directory path
#
# Returns: JSON array of batch_ids
conflict_queue_get_pending_batches() {
    local ralph_dir="$1"

    local queue_file="$ralph_dir/conflict-queue.json"
    [ -f "$queue_file" ] || { echo "[]"; return 0; }

    jq '[.batches | to_entries[] | select(.value.status == "pending") | .key]' "$queue_file"
}

# Build conflict-batch.json for the multi-pr-planner agent
#
# Args:
#   ralph_dir - Ralph directory path
#   batch_id  - Batch identifier
#   output_file - Path to write the batch file
#
# Returns: 0 on success
conflict_queue_build_batch_file() {
    local ralph_dir="$1"
    local batch_id="$2"
    local output_file="$3"

    local queue_file="$ralph_dir/conflict-queue.json"

    local batch
    batch=$(jq --arg batch_id "$batch_id" '.batches[$batch_id]' "$queue_file")

    if [ "$batch" = "null" ]; then
        log_error "Batch $batch_id not found"
        return 1
    fi

    local task_ids common_files
    task_ids=$(echo "$batch" | jq '.task_ids')
    common_files=$(echo "$batch" | jq '.common_files')

    # Build tasks array with full details
    local tasks='[]'
    while read -r task_id; do
        local task_entry
        task_entry=$(jq --arg task_id "$task_id" '.queue[] | select(.task_id == $task_id)' "$queue_file")

        if [ -n "$task_entry" ] && [ "$task_entry" != "null" ]; then
            local worker_dir pr_number affected_files
            worker_dir=$(echo "$task_entry" | jq -r '.worker_dir')
            pr_number=$(echo "$task_entry" | jq '.pr_number')
            affected_files=$(echo "$task_entry" | jq '.affected_files')

            # Get branch name from worker
            local branch=""
            if [ -f "$worker_dir/branch.txt" ]; then
                branch=$(cat "$worker_dir/branch.txt")
            fi

            # Determine which files have conflicts (intersection with common_files)
            local conflict_files
            conflict_files=$(jq -n --argjson a "$affected_files" --argjson b "$common_files" \
                '[$a[], $b[]] | group_by(.) | map(select(length > 1) | .[0])')

            local task
            task=$(jq -n \
                --arg task_id "$task_id" \
                --arg worker_dir "$worker_dir" \
                --argjson pr_number "$pr_number" \
                --arg branch "$branch" \
                --argjson affected_files "$affected_files" \
                --argjson conflict_files "$conflict_files" \
                '{
                    task_id: $task_id,
                    worker_dir: $worker_dir,
                    pr_number: $pr_number,
                    branch: $branch,
                    affected_files: $affected_files,
                    conflict_files: $conflict_files
                }')

            tasks=$(echo "$tasks" | jq --argjson t "$task" '. += [$t]')
        fi
    done < <(echo "$task_ids" | jq -r '.[]')

    # Write batch file
    jq -n \
        --arg batch_id "$batch_id" \
        --arg created_at "$(date -Iseconds)" \
        --argjson common_files "$common_files" \
        --argjson tasks "$tasks" \
        '{
            batch_id: $batch_id,
            created_at: $created_at,
            common_files: $common_files,
            tasks: $tasks
        }' > "$output_file"

    log "Built batch file: $output_file"
}

# Remove resolved tasks from queue and cleanup batch
#
# Args:
#   ralph_dir - Ralph directory path
#   batch_id  - Batch identifier
conflict_queue_cleanup_batch() {
    local ralph_dir="$1"
    local batch_id="$2"

    local queue_file="$ralph_dir/conflict-queue.json"
    local lock_file="$ralph_dir/.conflict-queue.lock"

    (
        flock -x 200

        # Remove tasks in this batch from queue
        jq --arg batch_id "$batch_id" '
            .queue = [.queue[] | select(.batch_id != $batch_id)] |
            del(.batches[$batch_id])
        ' "$queue_file" > "$queue_file.tmp"
        mv "$queue_file.tmp" "$queue_file"

        log "Cleaned up batch $batch_id"
    ) 200>"$lock_file"
}

# Get queue statistics
#
# Args:
#   ralph_dir - Ralph directory path
#
# Returns: JSON object with queue stats
conflict_queue_stats() {
    local ralph_dir="$1"

    local queue_file="$ralph_dir/conflict-queue.json"
    [ -f "$queue_file" ] || { echo '{"queued":0,"batched":0,"batches":0}'; return 0; }

    jq '{
        queued: [.queue[] | select(.batch_id == null)] | length,
        batched: [.queue[] | select(.batch_id != null)] | length,
        batches: .batches | length,
        by_status: (.batches | to_entries | group_by(.value.status) | map({key: .[0].value.status, value: length}) | from_entries)
    }' "$queue_file"
}
