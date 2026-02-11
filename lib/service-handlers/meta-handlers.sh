#!/usr/bin/env bash
# =============================================================================
# meta-handlers.sh - Service handlers for the meta-agent system
#
# Provides svc_* functions called by the service scheduler for:
#   - meta-init: Initialize meta-agent state directory on startup
#   - meta-dispatch: Track worker completions and dispatch meta-agent analysis
#   - meta-complete: Post-process meta-agent results (create tasks, PRs)
#
# Service chain pattern:
#   worker.completed event
#     -> svc_meta_count_completion (function, event-triggered)
#     -> when threshold reached, writes .ralph/meta/.current-meta-context.json
#     -> copies selected pipeline to .ralph/pipelines/meta-active.json
#     -> meta-pipeline (pipeline service, triggered on_complete)
#     -> svc_meta_complete (function, triggered on_finish)
#     -> parses <tasks> from agent output, appends to kanban.md
#
# Round-robin rotation: codebase-health -> todo-hunter -> self-improver
#
# Naming convention: svc_meta_* for meta-agent handlers
# =============================================================================
set -euo pipefail

# Prevent double-sourcing
[ -n "${_SERVICE_HANDLERS_META_LOADED:-}" ] && return 0
_SERVICE_HANDLERS_META_LOADED=1

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"
source "$WIGGUM_HOME/lib/core/safe-path.sh"

# =============================================================================
# CONFIGURATION
# =============================================================================

# Worker completions before triggering a meta-agent (default: 5)
_META_THRESHOLD="${WIGGUM_META_THRESHOLD:-5}"

# Master toggle (default: true)
_META_ENABLED="${WIGGUM_META_ENABLED:-true}"

# Agent rotation order
_META_AGENTS=("codebase-health" "todo-hunter" "self-improver")

# Map agent names to pipeline config files
_META_PIPELINE_MAP_codebase_health="meta-codebase-health"
_META_PIPELINE_MAP_todo_hunter="meta-todo-hunter"
_META_PIPELINE_MAP_self_improver="meta-self-improve"

# Per-agent toggles
_META_AGENT_ENABLED_codebase_health="${WIGGUM_META_CODEBASE_HEALTH_ENABLED:-true}"
_META_AGENT_ENABLED_todo_hunter="${WIGGUM_META_TODO_HUNTER_ENABLED:-true}"
_META_AGENT_ENABLED_self_improver="${WIGGUM_META_SELF_IMPROVER_ENABLED:-true}"

# =============================================================================
# STATE MANAGEMENT
# =============================================================================

# Get the meta state directory path
_meta_state_dir() {
    echo "$RALPH_DIR/meta"
}

# Get the meta state file path
_meta_state_file() {
    echo "$RALPH_DIR/meta/state.json"
}

# Read a value from state.json safely
#
# Args:
#   key - jq expression to extract
#   default - Default value if key missing or file unreadable
#
# Returns: The value (echoed)
_meta_state_get() {
    local key="$1"
    local default="$2"
    local state_file
    state_file=$(_meta_state_file)

    if [ ! -f "$state_file" ]; then
        echo "$default"
        return
    fi

    local value
    value=$(jq -r "$key // \"$default\"" "$state_file" 2>/dev/null)
    value="${value:-$default}"
    echo "$value"
}

# Update state.json atomically using flock
#
# Args:
#   jq_expr - jq expression to apply to the state
_meta_state_update() {
    local jq_expr="$1"
    local state_file
    state_file=$(_meta_state_file)
    local lock_file="${state_file}.lock"

    (
        flock -w 5 200 || {
            log_warn "meta: Could not acquire state lock"
            return 1
        }

        local tmp="${state_file}.tmp"
        if [ -f "$state_file" ]; then
            jq "$jq_expr" "$state_file" > "$tmp" 2>/dev/null && mv "$tmp" "$state_file"
        fi
    ) 200>"$lock_file"
}

# =============================================================================
# SERVICE HANDLERS
# =============================================================================

# Initialize meta-agent state directory and state.json
#
# Called during startup phase. Creates directory structure and initial state
# file if missing. Safe to call multiple times (idempotent).
svc_meta_init() {
    if [ "$_META_ENABLED" != "true" ]; then
        log_debug "meta: Disabled via WIGGUM_META_ENABLED"
        return 0
    fi

    local meta_dir
    meta_dir=$(_meta_state_dir)
    local state_file
    state_file=$(_meta_state_file)

    mkdir -p "$meta_dir"

    if [ ! -f "$state_file" ]; then
        cat > "$state_file" << 'EOF'
{
    "completion_count": 0,
    "last_dispatch": 0,
    "next_agent_index": 0,
    "agent_rotation": ["codebase-health", "todo-hunter", "self-improver"],
    "running": false,
    "history": []
}
EOF
        log_debug "meta: Initialized state at $state_file"
    fi

    log_debug "meta: State directory initialized"
}

# Track worker completions and dispatch meta-agent analysis
#
# Called on worker.completed event. Increments the completion counter in
# state.json. When the counter reaches the threshold (WIGGUM_META_THRESHOLD),
# selects the next agent via round-robin, writes a context file, and copies
# the corresponding pipeline config for the pipeline service to pick up.
svc_meta_count_completion() {
    if [ "$_META_ENABLED" != "true" ]; then
        return 0
    fi
    safe_path "$RALPH_DIR" "RALPH_DIR" || return 1

    local state_file
    state_file=$(_meta_state_file)
    local context_file="$RALPH_DIR/meta/.current-meta-context.json"

    # Clean up stale context from previous runs
    rm -f "$context_file"

    if [ ! -f "$state_file" ]; then
        log_warn "meta: State file missing, running init"
        svc_meta_init
    fi

    # Check if a meta-agent is already running
    local running
    running=$(_meta_state_get '.running' 'false')
    if [ "$running" = "true" ]; then
        log_debug "meta: Agent already running, skipping dispatch"
        return 0
    fi

    # Increment completion counter
    _meta_state_update '.completion_count = (.completion_count + 1)'

    local count
    count=$(_meta_state_get '.completion_count' '0')
    count="${count:-0}"

    log_debug "meta: Completion count: $count / $_META_THRESHOLD"

    # Check threshold
    if [ "$count" -lt "$_META_THRESHOLD" ]; then
        return 0
    fi

    # Threshold reached - dispatch next agent
    log "meta: Threshold reached ($count completions), dispatching meta-agent"

    # Find next enabled agent via round-robin
    local agent_index
    agent_index=$(_meta_state_get '.next_agent_index' '0')
    agent_index="${agent_index:-0}"

    local agent_name=""
    local pipeline_name=""
    local attempts=0
    local max_attempts=${#_META_AGENTS[@]}

    while [ "$attempts" -lt "$max_attempts" ]; do
        local candidate="${_META_AGENTS[$agent_index]}"
        local enabled_var="_META_AGENT_ENABLED_${candidate//-/_}"
        local enabled="${!enabled_var:-true}"

        if [ "$enabled" = "true" ]; then
            agent_name="$candidate"
            local pipeline_var="_META_PIPELINE_MAP_${candidate//-/_}"
            pipeline_name="${!pipeline_var:-}"
            break
        fi

        # Skip disabled agent, try next
        agent_index=$(( (agent_index + 1) % ${#_META_AGENTS[@]} ))
        ((++attempts))
    done

    if [ -z "$agent_name" ] || [ -z "$pipeline_name" ]; then
        log_warn "meta: No enabled meta-agents found, skipping"
        _meta_state_update '.completion_count = 0'
        return 0
    fi

    # Advance rotation for next dispatch
    local next_index=$(( (agent_index + 1) % ${#_META_AGENTS[@]} ))

    # Reset counter, mark running, advance rotation
    _meta_state_update "
        .completion_count = 0 |
        .running = true |
        .last_dispatch = $(date +%s) |
        .next_agent_index = $next_index
    "

    # Copy pipeline config to .ralph/pipelines/meta-active.json
    local source_pipeline="$WIGGUM_HOME/config/pipelines/${pipeline_name}.json"
    local target_pipeline="$RALPH_DIR/pipelines/meta-active.json"

    if [ ! -f "$source_pipeline" ]; then
        log_error "meta: Pipeline config not found: $source_pipeline"
        _meta_state_update '.running = false'
        return 1
    fi

    mkdir -p "$RALPH_DIR/pipelines"
    cp "$source_pipeline" "$target_pipeline"

    # Write context file for downstream pipeline service
    local project_dir
    # shellcheck disable=SC2153  # PROJECT_DIR is a global from defaults.sh
    project_dir=$(realpath "$RALPH_DIR/.." 2>/dev/null || echo "$PROJECT_DIR")
    local memory_dir="$RALPH_DIR/memory"

    cat > "$context_file" << EOF
{
    "agent_type": "$agent_name",
    "pipeline_name": "$pipeline_name",
    "project_dir": "$project_dir",
    "memory_dir": "$memory_dir",
    "timestamp": $(date +%s)
}
EOF

    log "meta: Dispatched $agent_name (pipeline: $pipeline_name)"
    return 0
}

# Post-process meta-agent results
#
# Triggered after the meta-pipeline finishes. Parses agent output for <tasks>
# tag content, validates and appends tasks to kanban.md with flock, checks
# for commits made by the agent, and cleans up state.
svc_meta_complete() {
    local context_file="$RALPH_DIR/meta/.current-meta-context.json"

    if [ ! -f "$context_file" ]; then
        log_debug "meta: No context file, nothing to process"
        _meta_state_update '.running = false' 2>/dev/null || true
        return 0
    fi

    local agent_type timestamp
    agent_type=$(jq -r '.agent_type // ""' "$context_file" 2>/dev/null)
    timestamp=$(jq -r '.timestamp // 0' "$context_file" 2>/dev/null)

    log "meta: Processing results for $agent_type"

    # Find the meta-pipeline worker directory
    local worker_dir=""
    worker_dir=$(_meta_find_worker_dir "$timestamp")

    if [ -n "$worker_dir" ] && [ -d "$worker_dir" ]; then
        # Extract and process tasks from agent output
        _meta_extract_and_create_tasks "$worker_dir"

        # Check if agent made commits and create PR if so
        _meta_check_and_create_pr "$worker_dir" "$agent_type"
    else
        log_warn "meta: Could not find worker directory for agent run"
    fi

    # Record in history
    _meta_state_update "
        .running = false |
        .history += [{
            \"agent_type\": \"$agent_type\",
            \"timestamp\": $timestamp,
            \"completed\": $(date +%s)
        }] |
        .history = (.history | .[-20:])
    "

    # Clean up context file
    rm -f "$context_file"

    log "meta: Completed processing for $agent_type"
    return 0
}

# =============================================================================
# INTERNAL HELPERS
# =============================================================================

# Find the worker directory created by the meta-pipeline service
#
# Args:
#   dispatch_timestamp - Epoch timestamp of the dispatch (for future filtering)
#
# Returns: Worker directory path (echoed), or empty string
_meta_find_worker_dir() {
    # shellcheck disable=SC2034  # dispatch_timestamp reserved for future filtering
    local dispatch_timestamp="$1"
    local workers_dir="$RALPH_DIR/workers"

    if [ ! -d "$workers_dir" ]; then
        return 0
    fi

    # Look for service-meta-pipeline-* worker directories created after dispatch
    local candidate
    candidate=$(find_newest "$workers_dir" -maxdepth 1 -name "service-meta-pipeline-*" -type d 2>/dev/null || true)

    if [ -n "$candidate" ] && [ -d "$candidate" ]; then
        echo "$candidate"
    fi
}

# Extract <tasks> tag content from agent output and create kanban tasks
#
# Args:
#   worker_dir - Worker directory containing agent output
_meta_extract_and_create_tasks() {
    local worker_dir="$1"

    # Find agent output logs
    local tasks_content=""
    local log_dir="$worker_dir/logs"

    if [ ! -d "$log_dir" ]; then
        log_debug "meta: No logs directory in worker"
        return 0
    fi

    # Search through log files for <tasks> tag in assistant messages
    local log_file
    while IFS= read -r log_file; do
        [ -f "$log_file" ] || continue

        local extracted
        extracted=$(grep '"type":"assistant"' "$log_file" 2>/dev/null | \
            grep -oP '(?<=<tasks>)[\s\S]*?(?=</tasks>)' 2>/dev/null || true)

        if [ -n "$extracted" ]; then
            tasks_content="$extracted"
        fi
    done < <(find "$log_dir" -name "*.log" -type f 2>/dev/null | sort)

    # Also check report files
    local report_dir="$worker_dir/reports"
    if [ -d "$report_dir" ]; then
        local report_file
        while IFS= read -r report_file; do
            [ -f "$report_file" ] || continue

            local extracted
            extracted=$(sed -n '/<tasks>/,/<\/tasks>/p' "$report_file" 2>/dev/null | \
                sed '1d;$d' 2>/dev/null || true)

            if [ -n "$extracted" ]; then
                tasks_content="$extracted"
            fi
        done < <(find "$report_dir" -name "*.md" -type f 2>/dev/null | sort)
    fi

    if [ -z "$tasks_content" ]; then
        log_debug "meta: No <tasks> content found in agent output"
        return 0
    fi

    # Parse and validate task lines, then append to kanban
    _meta_append_tasks_to_kanban "$tasks_content"
}

# Parse task content and append valid tasks to kanban.md
#
# Expected format (inside <tasks> tag):
#   - **[META-001]** Brief description
#     - Description: Detailed explanation
#     - Priority: CRITICAL|HIGH|MEDIUM|LOW
#     - Dependencies: TASK-002 | none
#
# Args:
#   tasks_content - Raw task content from agent output
_meta_append_tasks_to_kanban() {
    local tasks_content="$1"
    local kanban_file="$RALPH_DIR/kanban.md"

    if [ ! -f "$kanban_file" ]; then
        log_warn "meta: kanban.md not found at $kanban_file"
        return 0
    fi

    # Generate unique task IDs with META- prefix using epoch
    local epoch_suffix
    epoch_suffix=$(date +%s)
    local task_counter=1

    # Collect validated task blocks
    local tasks_to_append=""
    local current_task=""
    local in_task=false
    local has_description=false
    local has_priority=false

    while IFS= read -r line || [ -n "$line" ]; do
        # Detect task header: - **[SOMETHING]** description
        if [[ "$line" =~ ^-\ \*\*\[([A-Za-z]+-[0-9]+)\]\*\*\ .+ ]]; then
            # Process previous task if valid
            if [ "$in_task" = true ] && [ "$has_description" = true ] && [ "$has_priority" = true ]; then
                tasks_to_append+="$current_task"$'\n'
            fi

            # Start new task with unique META- ID
            local new_id="META-${epoch_suffix}${task_counter}"
            local desc_part="${line#*\]\*\* }"
            current_task="- [ ] **[${new_id}]** ${desc_part}"
            in_task=true
            has_description=false
            has_priority=false
            ((++task_counter))

        elif [ "$in_task" = true ]; then
            # Validate and collect task fields
            if [[ "$line" =~ ^[[:space:]]+-\ Description: ]]; then
                has_description=true
                current_task+=$'\n'"  ${line#"${line%%[![:space:]]*}"}"
            elif [[ "$line" =~ ^[[:space:]]+-\ Priority:\ (CRITICAL|HIGH|MEDIUM|LOW) ]]; then
                has_priority=true
                current_task+=$'\n'"  ${line#"${line%%[![:space:]]*}"}"
            elif [[ "$line" =~ ^[[:space:]]+-\ Dependencies: ]]; then
                current_task+=$'\n'"  ${line#"${line%%[![:space:]]*}"}"
            fi
        fi
    done <<< "$tasks_content"

    # Process last task
    if [ "$in_task" = true ] && [ "$has_description" = true ] && [ "$has_priority" = true ]; then
        tasks_to_append+="$current_task"$'\n'
    fi

    if [ -z "$tasks_to_append" ]; then
        log_debug "meta: No valid tasks found in agent output"
        return 0
    fi

    # Count tasks for logging
    local task_count
    task_count=$(echo "$tasks_to_append" | grep -c '^\- \[ \]' 2>/dev/null || true)
    task_count="${task_count:-0}"

    # Append to kanban.md under ## Pending section using flock
    local lock_file="${kanban_file}.lock"
    (
        flock -w 10 200 || {
            log_warn "meta: Could not acquire kanban lock"
            return 1
        }

        # Find the ## Pending section and append after it
        if grep -q "^## Pending" "$kanban_file" 2>/dev/null; then
            # Append after the last task in the Pending section
            # Find the line number of ## Pending, then find the next ## section
            local pending_line
            pending_line=$(grep -n "^## Pending" "$kanban_file" | head -1 | cut -d: -f1)
            pending_line="${pending_line:-0}"

            if [ "$pending_line" -gt 0 ]; then
                local next_section_line
                next_section_line=$(tail -n +"$((pending_line + 1))" "$kanban_file" | \
                    grep -n "^## " | head -1 | cut -d: -f1 || true)

                local insert_line
                if [ -n "$next_section_line" ]; then
                    # Insert before the next section
                    insert_line=$((pending_line + next_section_line - 1))
                else
                    # No next section, append to end
                    insert_line=$(wc -l < "$kanban_file")
                    insert_line="${insert_line:-0}"
                fi

                # Create temp file with inserted tasks
                local tmp="${kanban_file}.tmp"
                {
                    head -n "$insert_line" "$kanban_file"
                    echo "$tasks_to_append"
                    tail -n +"$((insert_line + 1))" "$kanban_file"
                } > "$tmp"
                mv "$tmp" "$kanban_file"
            fi
        else
            # No Pending section found, append to end of file
            echo "" >> "$kanban_file"
            echo "$tasks_to_append" >> "$kanban_file"
        fi
    ) 200>"$lock_file"

    log "meta: Appended $task_count tasks to kanban.md"
}

# Check if the meta-agent made commits and create a PR if so
#
# Args:
#   worker_dir - Worker directory with workspace
#   agent_type - Name of the meta-agent that ran
_meta_check_and_create_pr() {
    local worker_dir="$1"
    local agent_type="$2"
    local workspace="$worker_dir/workspace"

    if [ ! -d "$workspace/.git" ] && [ ! -f "$workspace/.git" ]; then
        log_debug "meta: No git workspace found"
        return 0
    fi

    # Check for commits made by the agent (on the current branch, not on default branch)
    local main_branch
    main_branch=$(get_default_branch)

    local commit_count
    commit_count=$(git -C "$workspace" rev-list --count "${main_branch}..HEAD" 2>/dev/null || true)
    commit_count="${commit_count:-0}"

    if [ "$commit_count" -eq 0 ]; then
        log_debug "meta: No new commits from $agent_type"
        return 0
    fi

    log "meta: $agent_type made $commit_count commits, creating PR"

    # Push and create PR
    local branch_name
    branch_name=$(git -C "$workspace" rev-parse --abbrev-ref HEAD 2>/dev/null || true)

    if [ -z "$branch_name" ] || [ "$branch_name" = "HEAD" ]; then
        log_warn "meta: Could not determine branch name"
        return 0
    fi

    local exit_code=0
    git -C "$workspace" push -u origin "$branch_name" 2>/dev/null || exit_code=$?

    if [ "$exit_code" -ne 0 ]; then
        log_warn "meta: Failed to push branch $branch_name"
        return 0
    fi

    # Create PR via gh CLI
    local pr_title="meta($agent_type): automated improvements"
    local pr_body="## Summary

Automated improvements from meta-agent: **${agent_type}**

This PR was created by the Chief Wiggum meta-agent system.

## Changes

See commit messages for details."

    exit_code=0
    gh pr create \
        --repo "$(git -C "$workspace" remote get-url origin 2>/dev/null)" \
        --head "$branch_name" \
        --title "$pr_title" \
        --body "$pr_body" \
        2>/dev/null || exit_code=$?

    if [ "$exit_code" -eq 0 ]; then
        log "meta: PR created for $agent_type changes"
    else
        log_warn "meta: Failed to create PR (exit $exit_code)"
    fi
}
