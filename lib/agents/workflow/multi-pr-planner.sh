#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: multi-pr-planner
# AGENT_DESCRIPTION: LLM agent that creates coordinated resolution plans for
#   multiple PRs with conflicting changes. Analyzes all conflicts in a batch
#   and produces per-PR resolution instructions to ensure compatibility.
# REQUIRED_PATHS:
#   - conflict-batch.json : Batch info with all conflicting PRs
# OUTPUT_FILES:
#   - planner-result.json : Contains PASS or FAIL
#   - resolution-plan.md  : Written to each task's worker directory
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "workflow.multi-pr-planner" "Multi-PR conflict resolution planner"

# Required paths before agent can run
agent_required_paths() {
    echo "conflict-batch.json"
}

# Source dependencies
agent_source_core
agent_source_once

# Source batch coordination for multi-PR workflow
source "$WIGGUM_HOME/lib/scheduler/batch-coordination.sh"

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    local max_turns="${WIGGUM_MULTI_PR_PLANNER_MAX_TURNS:-${AGENT_CONFIG_MAX_TURNS:-50}}"

    local batch_file="$worker_dir/conflict-batch.json"

    if [ ! -f "$batch_file" ]; then
        log_error "Batch file not found: $batch_file"
        agent_write_result "$worker_dir" "FAIL" '{}' '["Batch file not found"]'
        return 1
    fi

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Set up context
    agent_setup_context "$worker_dir" "$project_dir" "$project_dir"

    # Parse batch info
    local batch_id common_files task_count
    batch_id=$(jq -r '.batch_id' "$batch_file")
    common_files=$(jq -r '.common_files | join(", ")' "$batch_file")
    task_count=$(jq -r '.tasks | length' "$batch_file")

    log "Planning resolution for batch $batch_id"
    log "Common conflict files: $common_files"
    log "Tasks in batch: $task_count"

    # Build context for each task's changes
    local task_contexts=""
    while read -r task_json; do
        local task_id task_worker_dir branch conflict_files
        task_id=$(echo "$task_json" | jq -r '.task_id')
        task_worker_dir=$(echo "$task_json" | jq -r '.worker_dir')
        branch=$(echo "$task_json" | jq -r '.branch')
        conflict_files=$(echo "$task_json" | jq -r '.conflict_files | join(", ")')

        # Resolve relative path if needed
        if [[ ! "$task_worker_dir" = /* ]]; then
            task_worker_dir="$project_dir/$task_worker_dir"
        fi

        local workspace="$task_worker_dir/workspace"

        task_contexts+="
## Task: $task_id (Branch: $branch)

**Conflict files**: $conflict_files
**Worker**: $(basename "$task_worker_dir")

"
        # Get diff for each conflict file
        for file in $(echo "$task_json" | jq -r '.conflict_files[]'); do
            if [ -d "$workspace" ]; then
                local diff_output
                diff_output=$(git -C "$workspace" diff origin/main -- "$file" 2>/dev/null | head -100) || true
                if [ -n "$diff_output" ]; then
                    task_contexts+="### Changes to $file:

\`\`\`diff
${diff_output}
\`\`\`

"
                fi
            fi
        done
    done < <(jq -c '.tasks[]' "$batch_file")

    # Build system prompt
    local system_prompt
    system_prompt=$(_get_system_prompt)

    # Build user prompt
    local user_prompt
    user_prompt=$(_get_user_prompt "$batch_file" "$task_contexts" "$project_dir")

    # Use step ID from pipeline for log naming
    local step_id="${WIGGUM_STEP_ID:-planner}"
    local log_file
    log_file="$worker_dir/logs/${step_id}-$(date +%s).log"
    mkdir -p "$(dirname "$log_file")"

    log "Running planner (max $max_turns turns)..."

    # Run one-shot Claude call
    run_agent_once "$project_dir" "$system_prompt" "$user_prompt" "$log_file" "$max_turns"
    local agent_exit=$?

    if [ $agent_exit -ne 0 ]; then
        log_error "Planner agent failed with exit code $agent_exit"
        agent_write_result "$worker_dir" "FAIL" '{}' '["Agent execution failed"]'
        return $agent_exit
    fi

    # Extract and distribute plans
    local plans_created=0
    local plans_failed=0

    while read -r task_json; do
        local task_id task_worker_dir
        task_id=$(echo "$task_json" | jq -r '.task_id')
        task_worker_dir=$(echo "$task_json" | jq -r '.worker_dir')

        # Resolve relative path if needed
        if [[ ! "$task_worker_dir" = /* ]]; then
            task_worker_dir="$project_dir/$task_worker_dir"
        fi

        # Extract plan for this task from log
        local plan_content
        plan_content=$(_extract_plan_for_task "$log_file" "$task_id")

        if [ -n "$plan_content" ]; then
            echo "$plan_content" > "$task_worker_dir/resolution-plan.md"
            log "Created resolution plan for $task_id"
            ((++plans_created)) || true
        else
            log_warn "No plan extracted for $task_id"
            ((++plans_failed)) || true
        fi
    done < <(jq -c '.tasks[]' "$batch_file")

    # Determine result
    local result_value="PASS"
    if [ "$plans_failed" -gt 0 ] && [ "$plans_created" -eq 0 ]; then
        result_value="FAIL"
    fi

    # If plans were created successfully, set up batch coordination
    if [ "$plans_created" -gt 0 ]; then
        log "Setting up batch coordination for $plans_created tasks..."
        _setup_batch_coordination "$batch_file" "$log_file" "$project_dir"
    fi

    agent_write_result "$worker_dir" "$result_value" \
        "{\"plans_created\":$plans_created,\"plans_failed\":$plans_failed,\"batch_id\":\"$batch_id\"}"

    log "Planning complete: $plans_created plans created, $plans_failed failed"
    return 0
}

# System prompt for the planner
_get_system_prompt() {
    cat << 'EOF'
MULTI-PR CONFLICT RESOLUTION PLANNER:

You coordinate the resolution of multiple PRs that have conflicting changes on
the same files. Your job is to create a resolution plan for each PR that ensures
all PRs can merge successfully without causing new conflicts.

## Your Goal

Create specific, actionable resolution plans that:
1. Are internally consistent (if PR A keeps change X, PR B accounts for it)
2. Consider merge order (later PRs see earlier PR's merged changes)
3. Preserve the semantic intent of each PR's changes
4. Result in working, conflict-free code

## Critical Rules

* Be SPECIFIC - don't just say "merge both", specify exactly what to keep
* Include RATIONALE - explain why the resolution strategy is correct
* Consider DEPENDENCIES - some changes logically depend on others
* Define MERGE ORDER - specify which PR should merge first and why

## Output Format

For each task, output a plan in this format:

<plan task_id="TASK-ID">
# Resolution Plan for TASK-ID

**Batch ID**: {batch_id}
**Generated**: {timestamp}
**Merge Order**: N of M

## Overview

Brief description of what this PR does and why it conflicts.

## Resolution Strategy

### {filename}

**Conflict Region**: Description of where conflict occurs

**Resolution**: Specific instructions for resolving

1. Step by step resolution instructions
2. What to keep from each side
3. How to combine changes

**Rationale**: Why this resolution is correct

## Merge Order Notes

Why this PR should merge at position N.

## Verification

- [ ] Verification checklist items
</plan>

After all plans, provide the result:

<result>PASS</result>

If changes are fundamentally incompatible:

<result>FAIL</result>

With explanation of why they cannot be coordinated.
EOF
}

# User prompt with batch context
_get_user_prompt() {
    local batch_file="$1"
    local task_contexts="$2"
    local project_dir="$3"

    local batch_id common_files
    batch_id=$(jq -r '.batch_id' "$batch_file")
    common_files=$(jq -r '.common_files | @json' "$batch_file")

    cat << EOF
CONFLICT BATCH RESOLUTION REQUEST:

**Batch ID**: $batch_id
**Common Conflict Files**: $common_files

Create coordinated resolution plans for the following PRs:

$task_contexts

## Instructions

1. Analyze each PR's changes to understand their semantic intent
2. Identify any dependencies between the changes
3. Determine the optimal merge order
4. Create a resolution-plan.md for each task with specific instructions

For each task, output a <plan task_id="TASK-ID"> block with the full plan content.

Important: The plans must be CONSISTENT - they should work together so that
when executed in order, all PRs merge successfully.
EOF
}

# Extract plan for a specific task from log file
_extract_plan_for_task() {
    local log_file="$1"
    local task_id="$2"

    if [ ! -f "$log_file" ]; then
        return 1
    fi

    # Extract text content from stream-JSON
    local text_content
    text_content=$(_extract_text_from_stream_json "$log_file") || return 1

    # Extract plan content for this task using awk
    echo "$text_content" | awk -v task="$task_id" '
        BEGIN { in_plan = 0; content = "" }
        /<plan task_id="[^"]*'$task_id'[^"]*">/ {
            in_plan = 1
            # Extract content after opening tag on same line
            line = $0
            sub(/.*<plan task_id="[^"]*">/, "", line)
            if (line !~ /<\/plan>/) {
                content = line
            } else {
                sub(/<\/plan>.*/, "", line)
                print line
                exit
            }
            next
        }
        /<\/plan>/ && in_plan {
            sub(/<\/plan>.*/, "", $0)
            if ($0 != "") content = content "\n" $0
            print content
            exit
        }
        in_plan {
            content = content "\n" $0
        }
    '
}

# Setup batch coordination files after plans are created
#
# Creates:
#   - .ralph/batch-coordination-{batch_id}.json : Shared coordination file
#   - {worker_dir}/batch-context.json : Per-worker context
#
# Args:
#   batch_file  - Path to conflict-batch.json
#   log_file    - Path to planner log file (for extracting merge order)
#   project_dir - Project root directory
_setup_batch_coordination() {
    local batch_file="$1"
    local log_file="$2"
    local project_dir="$3"

    local batch_id
    batch_id=$(jq -r '.batch_id' "$batch_file")

    # Extract merge order from planner output
    # Look for "Merge Order: N of M" patterns in each plan
    local -A task_positions=()

    # Extract text from log and find merge order
    local text_content
    text_content=$(_extract_text_from_stream_json "$log_file") || true

    if [ -n "$text_content" ]; then
        # Parse merge order from plans - look for "Merge Order: N of M" or "**Merge Order**: N of M"
        while IFS= read -r line; do
            # Match patterns like "Merge Order: 1 of 3" or "**Merge Order**: 2 of 3"
            if [[ "$line" =~ [Mm]erge[[:space:]]*[Oo]rder.*:.*([0-9]+)[[:space:]]*of[[:space:]]*([0-9]+) ]]; then
                local position="${BASH_REMATCH[1]}"
                # Get the task_id from the most recent plan tag
                local recent_task
                recent_task=$(echo "$text_content" | grep -oP '<plan task_id="\K[^"]+' | tail -1) || true
                if [ -n "$recent_task" ] && [ -z "${task_positions[$recent_task]:-}" ]; then
                    task_positions[$recent_task]=$((position - 1))  # 0-indexed
                fi
            fi
        done <<< "$text_content"
    fi

    # Build task order list from batch file
    local task_count task_order_list=""
    task_count=$(jq -r '.tasks | length' "$batch_file")

    # Priority 1: Use merge_order from batch file if present (computed by Phase 3 MIS algorithm)
    local batch_merge_order
    batch_merge_order=$(jq -r '.merge_order // empty | join(",")' "$batch_file" 2>/dev/null || echo "")
    if [ -n "$batch_merge_order" ]; then
        log "Using merge_order from batch file (Phase 3 MIS algorithm)"
        task_order_list="$batch_merge_order"
    # Priority 2: Use merge order extracted from LLM plans
    elif [ ${#task_positions[@]} -gt 0 ]; then
        # Sort tasks by their position
        local -a sorted_tasks=()
        for task in "${!task_positions[@]}"; do
            sorted_tasks+=("${task_positions[$task]}:$task")
        done
        # shellcheck disable=SC2207  # mapfile not needed for simple colon-delimited entries
        IFS=$'\n' sorted_tasks=($(sort -t: -k1 -n <<< "${sorted_tasks[*]}")); unset IFS

        for entry in "${sorted_tasks[@]}"; do
            local task_id="${entry#*:}"
            if [ -n "$task_order_list" ]; then
                task_order_list+=","
            fi
            task_order_list+="$task_id"
        done

        # Add any tasks not in the order (shouldn't happen if planner worked correctly)
        while read -r task_json; do
            local task_id
            task_id=$(echo "$task_json" | jq -r '.task_id')
            if [ -z "${task_positions[$task_id]:-}" ]; then
                if [ -n "$task_order_list" ]; then
                    task_order_list+=","
                fi
                task_order_list+="$task_id"
                log_warn "Task $task_id not in merge order - appending to end"
            fi
        done < <(jq -c '.tasks[]' "$batch_file")
    else
        # Fall back to batch file order
        log "No explicit merge order found in plans - using batch file order"
        while read -r task_json; do
            local task_id
            task_id=$(echo "$task_json" | jq -r '.task_id')
            if [ -n "$task_order_list" ]; then
                task_order_list+=","
            fi
            task_order_list+="$task_id"
        done < <(jq -c '.tasks[]' "$batch_file")
    fi

    log "Batch task order: $task_order_list"

    # Initialize coordination file
    batch_coord_init "$batch_id" "$task_order_list" "$project_dir"
    log "Created coordination file for batch $batch_id"

    # Create batch-context.json in each worker directory
    local position=0
    for task_id in ${task_order_list//,/ }; do
        # Find this task's worker directory from batch file
        local task_worker_dir
        task_worker_dir=$(jq -r --arg tid "$task_id" '.tasks[] | select(.task_id == $tid) | .worker_dir' "$batch_file")

        if [ -n "$task_worker_dir" ]; then
            # Resolve relative path if needed
            if [[ ! "$task_worker_dir" = /* ]]; then
                task_worker_dir="$project_dir/$task_worker_dir"
            fi

            batch_coord_write_worker_context "$task_worker_dir" "$batch_id" "$task_id" "$position" "$task_count"
            log "Created batch context for $task_id (position $((position + 1)))"
        fi
        ((++position)) || true
    done
}
