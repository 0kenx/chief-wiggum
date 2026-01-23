#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: task-worker
# AGENT_DESCRIPTION: Main task execution agent that manages the complete task
#   lifecycle from PRD. Handles git worktree setup, plan-mode (optional),
#   task execution via task-executor sub-agent, summary generation via
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
agent_init_metadata "task-worker" "Main task execution agent that manages the complete task lifecycle from PRD"

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
agent_source_violations
agent_source_tasks
agent_source_git
agent_source_lock
agent_source_metrics
agent_source_registry

# Source exit codes for standardized returns
source "$WIGGUM_HOME/lib/core/exit-codes.sh"

# Ordered pipeline phases
TASK_PIPELINE=(execution audit test docs validation finalization)

_index_of() {
    local target="$1"
    shift
    local i=0
    for item in "$@"; do
        [ "$item" = "$target" ] && { echo $i; return 0; }
        ((i++))
    done
    echo 0  # default to first
}

_should_run_step() {
    local current="$1"
    local start="$2"
    local current_idx start_idx
    current_idx=$(_index_of "$current" "${TASK_PIPELINE[@]}")
    start_idx=$(_index_of "$start" "${TASK_PIPELINE[@]}")
    [ "$current_idx" -ge "$start_idx" ]
}

# Phase timing tracking
declare -A PHASE_TIMINGS

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
    for phase in "${TASK_PIPELINE[@]}"; do
        local start="${PHASE_TIMINGS[${phase}_start]:-0}"
        local end="${PHASE_TIMINGS[${phase}_end]:-0}"
        if [ "$start" -gt 0 ]; then
            local duration=$((end - start))
            [ "$first" = true ] || json+=","
            json+="\"$phase\":{\"start\":$start,\"end\":$end,\"duration_s\":$duration}"
            first=false
        fi
    done
    json+="}"
    echo "$json"
}

# Write executor configuration file for the task-executor sub-agent
#
# Args:
#   worker_dir           - Worker directory
#   max_iterations       - Max iterations for the ralph loop
#   max_turns            - Max turns per Claude session
#   supervisor_interval  - Run supervisor every N iterations
#   plan_file            - Path to plan file (empty if none)
#   resume_instructions  - Path to resume instructions file (empty if none)
_write_executor_config() {
    local worker_dir="$1"
    local max_iterations="$2"
    local max_turns="$3"
    local supervisor_interval="$4"
    local plan_file="${5:-}"
    local resume_instructions="${6:-}"

    jq -n \
        --argjson max_iterations "$max_iterations" \
        --argjson max_turns "$max_turns" \
        --argjson supervisor_interval "$supervisor_interval" \
        --arg plan_file "$plan_file" \
        --arg resume_instructions "$resume_instructions" \
        '{
            max_iterations: $max_iterations,
            max_turns: $max_turns,
            supervisor_interval: $supervisor_interval,
            plan_file: $plan_file,
            resume_instructions: $resume_instructions
        }' > "$worker_dir/executor-config.json"
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

    local commit_msg="chore($agent_name): automated changes

Co-Authored-By: Ralph Wiggum <ralph@wiggum.local>"

    # Set git author/committer identity
    export GIT_AUTHOR_NAME="Ralph Wiggum"
    export GIT_AUTHOR_EMAIL="ralph@wiggum.local"
    export GIT_COMMITTER_NAME="Ralph Wiggum"
    export GIT_COMMITTER_EMAIL="ralph@wiggum.local"

    if git commit -m "$commit_msg" >/dev/null 2>&1; then
        log "Committed $agent_name changes"
        return 0
    else
        log_warn "Failed to commit $agent_name changes"
        return 1
    fi
}

# Run a quality gate sub-agent with standardized result handling
#
# Args:
#   agent_name   - Sub-agent to run (e.g., "security-audit")
#   blocking     - "true" if FAIL/STOP should fail the task (default: true)
#   workspace    - Workspace directory for committing changes
#
# Sets:
#   GATE_RESULT  - The result string (PASS/FAIL/STOP/SKIP/FIX)
#
# Returns: 0 if gate passed/skipped, 1 if gate blocked (only when blocking=true)
_run_quality_gate() {
    local agent_name="$1"
    local blocking="${2:-true}"
    local workspace="$3"

    log "Running $agent_name on completed work"
    run_sub_agent "$agent_name" "$worker_dir" "$project_dir"

    GATE_RESULT=$(agent_read_subagent_result "$worker_dir" "$agent_name")
    log "$agent_name result: $GATE_RESULT"

    case "$GATE_RESULT" in
        PASS)
            log "$agent_name passed"
            _commit_subagent_changes "$workspace" "$agent_name"
            return 0
            ;;
        SKIP)
            log "$agent_name skipped (not applicable)"
            return 0
            ;;
        FAIL|STOP|FIX)
            if [ "$blocking" = "true" ]; then
                log_error "$agent_name failed - blocking task completion"
                return 1
            fi
            _commit_subagent_changes "$workspace" "$agent_name"
            return 0
            ;;
        *)
            log_warn "$agent_name result unknown ($GATE_RESULT) - continuing"
            _commit_subagent_changes "$workspace" "$agent_name"
            return 0
            ;;
    esac
}

# Main entry point - manages complete task lifecycle
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    local max_iterations="${3:-${AGENT_CONFIG_MAX_ITERATIONS:-20}}"
    local max_turns="${4:-${AGENT_CONFIG_MAX_TURNS:-50}}"
    local start_from_step="${5:-execution}"
    local resume_instructions="${6:-}"

    # Determine plan mode from config or environment
    local plan_mode="${WIGGUM_PLAN_MODE:-${AGENT_CONFIG_PLAN_MODE:-false}}"

    # Extract worker and task IDs
    local worker_id task_id
    worker_id=$(basename "$worker_dir")
    # Match any task prefix format: TASK-001, PIPELINE-001, etc.
    task_id=$(echo "$worker_id" | sed -E 's/worker-([A-Z]+-[0-9]+)-.*/\1/')

    # Setup logging
    export LOG_FILE="$worker_dir/worker.log"

    local prd_file="$worker_dir/prd.md"

    # Record start time
    local start_time
    start_time=$(date +%s)
    agent_log_start "$worker_dir" "$task_id"

    log "Task worker agent starting for $task_id (max $max_turns turns per session, plan_mode=$plan_mode)"
    if [ "$start_from_step" != "execution" ]; then
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

    # Start violation monitoring (log-based, 100ms interval)
    # Pass: workspace, worker_dir, agent_pid ($$), project_dir
    start_violation_monitor "$workspace" "$worker_dir" "$$" "$project_dir"
    trap '_task_worker_stop_monitor' EXIT

    # Change to workspace
    cd "$workspace" || {
        log_error "Cannot access workspace: $workspace"
        _task_worker_cleanup "$worker_dir" "$project_dir" "$task_id" "FAILED" "" "N/A"
        return 1
    }

    # Create standard directories
    agent_create_directories "$worker_dir"

    # === PLANNING PHASE (optional) ===
    local plan_file="$project_dir/.ralph/plans/${task_id}.md"

    if _should_run_step "execution" "$start_from_step"; then
        if [ "$plan_mode" = "true" ]; then
            if [ -f "$plan_file" ] && [ -s "$plan_file" ]; then
                log "Plan already exists at $plan_file - skipping planning phase"
            else
                log "Running implementation planning phase"
                run_sub_agent "plan-mode" "$worker_dir" "$project_dir"
                local plan_result=$?

                if [ $plan_result -eq 0 ] && [ -f "$plan_file" ]; then
                    log "Plan created at $plan_file"
                else
                    log_warn "Planning did not complete (exit: ${plan_result:-0}) - continuing without plan"
                    plan_file=""
                fi
            fi
        else
            # Non-plan mode: check for existing plan
            if [ -f "$plan_file" ] && [ -s "$plan_file" ]; then
                log "Plan found at $plan_file - will include in execution context"
            else
                log_debug "No existing plan at $plan_file"
                plan_file=""
            fi
        fi
    else
        # Resuming past execution - check for existing plan
        if [ -f "$plan_file" ] && [ -s "$plan_file" ]; then
            log "Plan found at $plan_file (resuming past planning phase)"
        else
            plan_file=""
        fi
    fi

    # === EXECUTION PHASE ===
    local loop_result=0

    if _should_run_step "execution" "$start_from_step"; then
        _phase_start "execution"

        # Supervisor interval (run supervisor every N iterations)
        local supervisor_interval="${WIGGUM_SUPERVISOR_INTERVAL:-2}"

        # Write executor config
        _write_executor_config "$worker_dir" "$max_iterations" "$max_turns" \
            "$supervisor_interval" "${plan_file:-}" "$resume_instructions"

        # Run execution via sub-agent
        run_sub_agent "task-executor" "$worker_dir" "$project_dir"
        loop_result=$?

        _phase_end "execution"
    else
        log "Skipping execution phase (resuming from $start_from_step)"
    fi

    # === SUMMARY PHASE ===
    if [ $loop_result -eq 0 ]; then
        run_sub_agent "task-summarizer" "$worker_dir" "$project_dir"
    fi

    # === SECURITY AUDIT PHASE ===
    if [ -d "$workspace" ] && [ $loop_result -eq 0 ] && _should_run_step "audit" "$start_from_step"; then
        _phase_start "audit"
        if ! _run_quality_gate "security-audit" "true" "$workspace"; then
            if [ "$GATE_RESULT" = "FIX" ]; then
                log "Security audit found fixable issues - running security-fix agent"
                run_sub_agent "security-fix" "$worker_dir" "$project_dir"

                local fix_result
                fix_result=$(agent_read_subagent_result "$worker_dir" "security-fix")
                log "Security fix result: $fix_result"
                _commit_subagent_changes "$workspace" "security-fix"

                if [ "$fix_result" != "PASS" ]; then
                    log_warn "Security fix incomplete (result: $fix_result) - continuing with validation"
                fi
            else
                loop_result=1
            fi
        fi
        _phase_end "audit"
    fi

    # === TEST COVERAGE PHASE ===
    if [ -d "$workspace" ] && [ $loop_result -eq 0 ] && _should_run_step "test" "$start_from_step"; then
        _phase_start "test"
        if ! _run_quality_gate "test-coverage" "true" "$workspace"; then
            loop_result=1
        fi
        _phase_end "test"
    fi

    # === DOCUMENTATION WRITER PHASE ===
    if [ -d "$workspace" ] && [ $loop_result -eq 0 ] && _should_run_step "docs" "$start_from_step"; then
        _phase_start "docs"
        _run_quality_gate "documentation-writer" "false" "$workspace"
        _phase_end "docs"
    fi

    # === VALIDATION PHASE ===
    # Stop violation monitor before validation
    stop_violation_monitor "$VIOLATION_MONITOR_PID"

    if _should_run_step "validation" "$start_from_step"; then
        _phase_start "validation"
        # Run validation-review as a nested sub-agent
        if [ -d "$workspace" ]; then
            log "Running validation review on completed work"
            run_sub_agent "validation-review" "$worker_dir" "$project_dir"
        fi
        _phase_end "validation"
    else
        log "Skipping validation phase (resuming from $start_from_step)"
    fi

    # === FINALIZATION PHASE ===
    if ! _should_run_step "finalization" "$start_from_step"; then
        log "Skipping finalization phase (resuming from $start_from_step)"
        agent_log_complete "$worker_dir" "$loop_result" "$start_time"
        return $loop_result
    fi
    _phase_start "finalization"

    _determine_finality "$worker_dir" "$workspace" "$project_dir" "$prd_file"
    local has_violations="$FINALITY_HAS_VIOLATIONS"
    local final_status="$FINALITY_STATUS"

    # Check validation result from sub-agent
    local validation_result
    validation_result=$(agent_read_subagent_result "$worker_dir" "validation-review")
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
            task_desc=$(grep -F "**[$task_id]**" "$project_dir/.ralph/kanban.md" | sed 's/.*\*\*\[.*\]\*\* //' | head -1)
            log_debug "Task description: ${task_desc:-<empty>}"

            # Get task priority
            local task_priority
            task_priority=$(grep -F -A2 "**[$task_id]**" "$project_dir/.ralph/kanban.md" | grep "Priority:" | sed 's/.*Priority: //')
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

    # Write structured agent result
    local result_status="failure"
    local result_exit_code="$loop_result"
    if [ "$final_status" = "COMPLETE" ] && [ "$loop_result" -eq 0 ]; then
        result_status="success"
    elif [ "$final_status" = "COMPLETE" ]; then
        result_status="partial"
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

    agent_write_result "$worker_dir" "$result_status" "$result_exit_code" "$outputs_json"

    log "Task worker finished: $worker_id"
    return $loop_result
}

# Internal cleanup function for violation monitor
_task_worker_stop_monitor() {
    stop_violation_monitor "$VIOLATION_MONITOR_PID" 2>/dev/null || true
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
            if ! update_kanban_pending_approval "$project_dir/.ralph/kanban.md" "$task_id"; then
                log_error "Failed to update kanban.md after retries"
            fi
        else
            log "Marking task $task_id as complete [x] in kanban (no PR created)"
            if ! update_kanban "$project_dir/.ralph/kanban.md" "$task_id"; then
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

        if ! append_changelog "$project_dir/.ralph/changelog.md" "$task_id" "$worker_id" "$task_desc" "$pr_url" "$summary"; then
            log_error "Failed to update changelog.md after retries"
        fi

        log "Task worker $worker_id completed task $task_id"
    else
        log_error "Marking task $task_id as FAILED [*] in kanban"
        if ! update_kanban_failed "$project_dir/.ralph/kanban.md" "$task_id"; then
            log_error "Failed to update kanban.md after retries"
        fi
        log_error "Task worker $worker_id failed task $task_id"
    fi

    # Log final worker status to audit log
    audit_log_worker_complete "$task_id" "$worker_id" "$final_status"

    # Update metrics.json with latest worker data
    log_debug "Exporting metrics to metrics.json"
    export_metrics "$project_dir/.ralph" 2>/dev/null || true
}
