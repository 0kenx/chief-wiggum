#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: task-worker
# AGENT_DESCRIPTION: Main task execution agent that manages the complete task
#   lifecycle from PRD. Handles git worktree setup, plan-mode (optional),
#   task execution via software-engineer sub-agent, summary generation via
#   task-summarizer sub-agent, quality gates (security, tests, docs),
#   validation review, commit/PR creation, kanban status updates, and
#   worktree cleanup. The primary workhorse agent for automated task completion.
# REQUIRED_PATHS:
#   - prd.md : Product Requirements Document containing tasks to execute
# NOTE: workspace is created by this agent, not required in advance
# OUTPUT_FILES:
#   - worker.log : Main worker log with agent lifecycle events
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "system.task-worker" "Main task execution agent that manages the complete task lifecycle from PRD"

# Required paths before agent can run
agent_required_paths() {
    echo "prd.md"
    # Note: workspace is created by this agent, not required in advance
}

# Output files that must exist (non-empty) after agent completes
agent_output_files() {
    echo "worker.log"
    # Note: logs/*.log files are created per iteration
    # Note: summaries/summary.txt is optional (only on success)
    # Note: epoch-named results are created by sub-agents in results/
}

# Source dependencies using base library helpers
agent_source_core
agent_source_tasks
agent_source_git
agent_source_lock
agent_source_metrics
agent_source_registry

# Source exit codes for standardized returns
source "$WIGGUM_HOME/lib/core/exit-codes.sh"

# Source pipeline libraries
source "$WIGGUM_HOME/lib/pipeline/pipeline-loader.sh"
source "$WIGGUM_HOME/lib/pipeline/pipeline-runner.sh"

# Phase timing tracking
declare -gA PHASE_TIMINGS=()

_phase_start() {
    local phase="$1"
    PHASE_TIMINGS["${phase}_start"]=$(date +%s)
}

_phase_end() {
    local phase="$1"
    PHASE_TIMINGS["${phase}_end"]=$(date +%s)
}

_build_phase_timings_json() {
    local json="{"
    local first=true
    local count
    count=$(pipeline_step_count)
    local p=0
    while [ "$p" -lt "$count" ]; do
        local phase
        phase=$(pipeline_get "$p" ".id")
        local start="${PHASE_TIMINGS[${phase}_start]:-0}"
        local end="${PHASE_TIMINGS[${phase}_end]:-0}"
        if [ "$start" -gt 0 ]; then
            local duration=$((end - start))
            [ "$first" = true ] || json+=","
            json+="\"$phase\":{\"start\":$start,\"end\":$end,\"duration_s\":$duration}"
            first=false
        fi
        ((++p))
    done
    # Also include finalization phase
    local start="${PHASE_TIMINGS[finalization_start]:-0}"
    local end="${PHASE_TIMINGS[finalization_end]:-0}"
    if [ "$start" -gt 0 ]; then
        local duration=$((end - start))
        [ "$first" = true ] || json+=","
        json+="\"finalization\":{\"start\":$start,\"end\":$end,\"duration_s\":$duration}"
    fi
    json+="}"
    echo "$json"
}

# Commit sub-agent changes to isolate work between phases
# This prevents one sub-agent from accidentally destroying another's work
#
# Args:
#   workspace   - The workspace directory
#   agent_name  - Name of the sub-agent (for commit message)
#
# Returns: 0 on success or if nothing to commit, 1 on error
_commit_subagent_changes() {
    local workspace="$1"
    local agent_name="$2"

    cd "$workspace" || return 1

    # Check if there are any changes to commit
    if git diff --quiet && git diff --staged --quiet; then
        log_debug "No changes to commit for $agent_name"
        return 0
    fi

    # Stage all changes
    git add . 2>/dev/null || true

    # Check if there are staged changes
    if git diff --staged --quiet; then
        log_debug "No staged changes to commit for $agent_name"
        return 0
    fi

    local commit_msg="chore($agent_name): automated changes"

    # Set git author/committer identity
    export GIT_AUTHOR_NAME="Ralph Wiggum"
    export GIT_AUTHOR_EMAIL="ralph@wiggum.cc"
    export GIT_COMMITTER_NAME="Ralph Wiggum"
    export GIT_COMMITTER_EMAIL="ralph@wiggum.cc"

    if git commit -m "$commit_msg" >/dev/null 2>&1; then
        log "Committed $agent_name changes"
        return 0
    else
        log_warn "Failed to commit $agent_name changes"
        return 1
    fi
}

# Main entry point - manages complete task lifecycle
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    # shellcheck disable=SC2034  # max_iterations reserved for future use
    local max_iterations="${3:-${AGENT_CONFIG_MAX_ITERATIONS:-20}}"
    local max_turns="${4:-${AGENT_CONFIG_MAX_TURNS:-50}}"
    local start_from_step="${5:-}"
    local resume_instructions="${6:-}"

    # Determine plan mode from config or environment
    local plan_mode="${WIGGUM_PLAN_MODE:-${AGENT_CONFIG_PLAN_MODE:-false}}"

    # Extract worker and task IDs
    local worker_id task_id
    worker_id=$(basename "$worker_dir")
    # Match any task prefix format: TASK-001, PIPELINE-001, etc.
    task_id=$(echo "$worker_id" | sed -E 's/worker-([A-Za-z]{2,10}-[0-9]{1,4})-.*/\1/')

    # Security: Validate extracted task ID against expected pattern
    # Prevents empty/malformed IDs from being used in file paths
    if [[ ! "$task_id" =~ ^[A-Za-z]{2,10}-[0-9]{1,4}$ ]]; then
        log_error "Invalid task ID extracted from worker directory: '$task_id' (from $worker_id)"
        return "$EXIT_USAGE"
    fi

    # Setup logging
    export LOG_FILE="$worker_dir/worker.log"

    local prd_file="$worker_dir/prd.md"

    # Record start time
    local start_time
    start_time=$(date +%s)
    agent_log_start "$worker_dir" "$task_id"

    log "Task worker agent starting for $task_id (max $max_turns turns per session, plan_mode=$plan_mode)"
    if [ -n "$start_from_step" ]; then
        log "Resuming from step: $start_from_step (skipping earlier phases)"
    fi

    # Log worker start to audit log
    audit_log_worker_start "$task_id" "$worker_id"

    # === SETUP PHASE ===
    # Create git worktree for isolation
    if ! setup_worktree "$project_dir" "$worker_dir"; then
        log_error "Failed to setup worktree"
        _task_worker_cleanup "$worker_dir" "$project_dir" "$task_id" "FAILED" "" "N/A"
        return 1
    fi
    local workspace="$WORKTREE_PATH"

    # Change to workspace
    cd "$workspace" || {
        log_error "Cannot access workspace: $workspace"
        _task_worker_cleanup "$worker_dir" "$project_dir" "$task_id" "FAILED" "" "N/A"
        return 1
    }

    # Create standard directories
    agent_create_directories "$worker_dir"

    # === PIPELINE PHASE ===
    # Load pipeline configuration
    local plan_file="$RALPH_DIR/plans/${task_id}.md"
    if [ ! -f "$plan_file" ] || [ ! -s "$plan_file" ]; then
        plan_file=""
    else
        # Plan already exists - skip planning phase even if plan mode was requested
        if [ "${WIGGUM_PLAN_MODE:-false}" = "true" ]; then
            log "Plan already exists at $plan_file - skipping planning phase"
            export WIGGUM_PLAN_MODE=false
        fi
    fi

    log "DEBUG: Resolving pipeline (WIGGUM_PIPELINE=${WIGGUM_PIPELINE:-unset})"
    local pipeline_file
    pipeline_file=$(pipeline_resolve "$project_dir" "$task_id" "${WIGGUM_PIPELINE:-}") || {
        log_error "pipeline_resolve failed with exit code $?"
    }
    log "DEBUG: Pipeline resolved to: ${pipeline_file:-builtin}"
    log "DEBUG: About to load pipeline..."
    if [ -n "$pipeline_file" ]; then
        pipeline_load "$pipeline_file" || {
            log_error "pipeline_load failed with exit code $?"
            return 1
        }
    else
        pipeline_load_builtin_defaults || {
            log_error "pipeline_load_builtin_defaults failed with exit code $?"
            return 1
        }
    fi
    log "DEBUG: Pipeline loaded successfully, step count=$(pipeline_step_count)"

    # Set context for pipeline steps
    export PIPELINE_PLAN_FILE="${plan_file:-}"
    export PIPELINE_RESUME_INSTRUCTIONS="$resume_instructions"

    # Run pipeline (skip if resuming directly to finalization)
    local loop_result=0
    if [ "$start_from_step" != "finalization" ]; then
        pipeline_run_all "$worker_dir" "$project_dir" "$workspace" "$start_from_step"
        loop_result=$?
    else
        log "Skipping pipeline (resuming directly to finalization)"
    fi

    # === FINALIZATION PHASE ===
    _phase_start "finalization"

    _determine_finality "$worker_dir" "$workspace" "$project_dir" "$prd_file"
    local has_violations="$FINALITY_HAS_VIOLATIONS"
    local final_status="$FINALITY_STATUS"

    # Check validation result from pipeline step
    local validation_result
    validation_result=$(agent_read_step_result "$worker_dir" "validation")
    if [ "$validation_result" = "FAIL" ]; then
        log_error "Validation review FAILED - marking task as failed"
        final_status="FAILED"
    elif [ "$validation_result" = "UNKNOWN" ]; then
        log_error "Validation result UNKNOWN - cannot proceed safely"
        log_error "Worker exiting without commit/PR or status update"
        return "$EXIT_AGENT_VALIDATION_FAILED"
    fi

    local pr_url="N/A"
    local task_desc=""

    log_debug "Finalization check: has_violations=$has_violations, final_status=$final_status"

    # Only create commits and PRs if no violations and task is complete
    if [ "$has_violations" = false ] && [ "$final_status" = "COMPLETE" ]; then
        log "Creating commit and PR for task $task_id"
        if [ -d "$workspace" ]; then
            cd "$workspace" || return 1

            # Get task description from kanban for commit message
            task_desc=$(grep -F "**[$task_id]**" "$RALPH_DIR/kanban.md" | sed 's/.*\*\*\[.*\]\*\* //' | head -1) || true
            log_debug "Task description: ${task_desc:-<empty>}"

            # Get task priority
            local task_priority
            task_priority=$(grep -F -A2 "**[$task_id]**" "$RALPH_DIR/kanban.md" | grep "Priority:" | sed 's/.*Priority: //') || true
            log_debug "Task priority: ${task_priority:-<empty>}"

            # Create commit using shared library
            if git_create_commit "$workspace" "$task_id" "$task_desc" "$task_priority" "$worker_id"; then
                local branch_name="$GIT_COMMIT_BRANCH"
                log "Commit created on branch: $branch_name"

                # Create PR using shared library
                git_create_pr "$branch_name" "$task_id" "$task_desc" "$worker_dir" "$project_dir"
                pr_url="$GIT_PR_URL"
                log "PR created: $pr_url"
            else
                log_error "Failed to create commit"
                final_status="FAILED"
            fi
        else
            log_error "Workspace not found: $workspace"
        fi
    else
        log "Skipping commit and PR creation - has_violations=$has_violations, final_status=$final_status"
    fi

    _phase_end "finalization"

    # === CLEANUP PHASE ===
    _task_worker_cleanup "$worker_dir" "$project_dir" "$task_id" "$final_status" "$task_desc" "$pr_url"

    # Record completion
    agent_log_complete "$worker_dir" "$loop_result" "$start_time"

    # Determine gate_result from final status
    local gate_result="FAIL"
    if [ "$final_status" = "COMPLETE" ] && [ "$loop_result" -eq 0 ]; then
        gate_result="PASS"
    elif [ "$final_status" = "COMPLETE" ]; then
        gate_result="FIX"
    fi

    # Read violation details if present
    local violation_type="" violation_details=""
    if [ -f "$worker_dir/violation_flag.txt" ]; then
        violation_type=$(sed -n '3s/^Type: //p' "$worker_dir/violation_flag.txt")
        violation_details=$(sed -n '4s/^Details: //p' "$worker_dir/violation_flag.txt")
    fi

    # Build outputs JSON
    local phase_timings_json
    phase_timings_json=$(_build_phase_timings_json)

    local outputs_json
    outputs_json=$(jq -n \
        --arg pr_url "$pr_url" \
        --arg branch "${GIT_COMMIT_BRANCH:-}" \
        --arg commit_sha "$(cd "$workspace" 2>/dev/null && git rev-parse HEAD 2>/dev/null || echo "")" \
        --arg validation_result "$validation_result" \
        --arg violation_type "$violation_type" \
        --arg violation_details "$violation_details" \
        --arg plan_file "${plan_file:-}" \
        --argjson phases "$phase_timings_json" \
        '{
            pr_url: $pr_url,
            branch: $branch,
            commit_sha: $commit_sha,
            validation_result: $validation_result,
            violation_type: $violation_type,
            violation_details: $violation_details,
            plan_file: $plan_file,
            phases: $phases
        }')

    agent_write_result "$worker_dir" "$gate_result" "$outputs_json"

    log "Task worker finished: $worker_id"
    return $loop_result
}

# Determine final task status
_determine_finality() {
    local worker_dir="$1"
    local workspace="$2"
    local project_dir="$3"
    local prd_file="$4"

    local has_violations=false
    local final_status="COMPLETE"

    # Check for workspace violations before processing results
    if ! agent_runner_detect_violations "$workspace" "$project_dir"; then
        log_error "Workspace violation detected - changes outside workspace were reverted"
        echo "WORKSPACE_VIOLATION" > "$worker_dir/violation_status.txt"
        has_violations=true
        final_status="FAILED"
    fi

    # Check PRD status
    local prd_status
    prd_status=$(get_prd_status "$prd_file")
    log "PRD status: $prd_status"

    # Determine final task status
    if [ "$has_violations" = true ]; then
        final_status="FAILED"
        log_error "Task marked as FAILED due to workspace violations"
    elif [ "$prd_status" = "FAILED" ]; then
        final_status="FAILED"
        log_error "Task marked as FAILED - PRD contains failed tasks"
    elif [ "$prd_status" = "INCOMPLETE" ]; then
        final_status="FAILED"
        log_error "Task marked as FAILED - PRD has incomplete tasks (timeout or error)"
    else
        final_status="COMPLETE"
        log "Task completed successfully - all PRD tasks complete"
    fi

    # Return values via global variables (bash limitation)
    FINALITY_HAS_VIOLATIONS="$has_violations"
    FINALITY_STATUS="$final_status"
}

# Full cleanup including kanban update
_task_worker_cleanup() {
    local worker_dir="$1"
    local project_dir="$2"
    local task_id="$3"
    local final_status="$4"
    local task_desc="$5"
    local pr_url="$6"

    log "Cleaning up task worker"

    # Log cleanup start to audit log
    audit_log_worker_cleanup "$task_id" "$(basename "$worker_dir")"

    # Clean up git worktree
    cleanup_worktree "$project_dir" "$worker_dir" "$final_status" "$task_id"

    # Update kanban and finalize
    _update_kanban_status "$worker_dir" "$project_dir" "$task_id" "$final_status" "$task_desc" "$pr_url"
}

# Update kanban based on final status
_update_kanban_status() {
    local worker_dir="$1"
    local project_dir="$2"
    local task_id="$3"
    local final_status="$4"
    local task_desc="$5"
    local pr_url="$6"

    local worker_id
    worker_id=$(basename "$worker_dir")

    # Get PR URL from file if not passed
    if [ -f "$worker_dir/pr_url.txt" ]; then
        pr_url=$(cat "$worker_dir/pr_url.txt")
    fi

    if [ "$final_status" = "COMPLETE" ]; then
        # If PR was created, mark as Pending Approval [P] - wiggum review sync will mark [x] when merged
        # If no PR (gh CLI unavailable), mark as complete [x] directly
        if [ -n "$pr_url" ] && [ "$pr_url" != "N/A" ]; then
            log "Marking task $task_id as pending approval [P] in kanban (PR: $pr_url)"
            if ! update_kanban_pending_approval "$RALPH_DIR/kanban.md" "$task_id"; then
                log_error "Failed to update kanban.md after retries"
            fi
        else
            log "Marking task $task_id as complete [x] in kanban (no PR created)"
            if ! update_kanban "$RALPH_DIR/kanban.md" "$task_id"; then
                log_error "Failed to update kanban.md after retries"
            fi
        fi

        # Append to changelog
        log "Appending to changelog"

        # Get detailed summary if it exists
        local summary=""
        if [ -f "$worker_dir/summaries/summary.txt" ]; then
            summary=$(cat "$worker_dir/summaries/summary.txt")
            log "Including detailed summary in changelog"
        fi

        if ! append_changelog "$RALPH_DIR/changelog.md" "$task_id" "$worker_id" "$task_desc" "$pr_url" "$summary"; then
            log_error "Failed to update changelog.md after retries"
        fi

        log "Task worker $worker_id completed task $task_id"
    else
        log_error "Marking task $task_id as FAILED [*] in kanban"
        if ! update_kanban_failed "$RALPH_DIR/kanban.md" "$task_id"; then
            log_error "Failed to update kanban.md after retries"
        fi
        log_error "Task worker $worker_id failed task $task_id"
    fi

    # Log final worker status to audit log
    audit_log_worker_complete "$task_id" "$worker_id" "$final_status"

    # Update metrics.json with latest worker data
    log_debug "Exporting metrics to metrics.json"
    export_metrics "$RALPH_DIR" 2>/dev/null || true
}
