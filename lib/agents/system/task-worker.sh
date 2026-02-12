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
source "$WIGGUM_HOME/lib/core/platform.sh"
source "$WIGGUM_HOME/lib/core/lifecycle-engine.sh"

# Source pipeline libraries
source "$WIGGUM_HOME/lib/pipeline/pipeline-loader.sh"
source "$WIGGUM_HOME/lib/pipeline/pipeline-runner.sh"

# Source GitHub issue sync and PR label sync for status updates
source "$WIGGUM_HOME/lib/github/issue-sync.sh"
source "$WIGGUM_HOME/lib/github/pr-labels.sh"

# Phase timing tracking
declare -gA PHASE_TIMINGS=()

_phase_start() {
    local phase="$1"
    PHASE_TIMINGS["${phase}_start"]=$(epoch_now)
}

_phase_end() {
    local phase="$1"
    PHASE_TIMINGS["${phase}_end"]=$(epoch_now)
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
    # Security: Unstage common sensitive file patterns
    git reset HEAD -- '.env' '.env.*' '*.pem' '*.key' 'credentials.json' '.secrets' 2>/dev/null || true

    # Check if there are staged changes
    if git diff --staged --quiet; then
        log_debug "No staged changes to commit for $agent_name"
        return 0
    fi

    # Guard: refuse to commit conflict markers
    local marker_files
    if marker_files=$(git_staged_has_conflict_markers "$workspace"); then
        log_error "Conflict markers detected after $agent_name — aborting sub-agent commit"
        log_error "Files with markers:"
        echo "$marker_files" | while read -r f; do log_error "  $f"; done
        git reset HEAD -- . >/dev/null 2>&1 || true
        return 1
    fi

    local commit_msg="${WIGGUM_TASK_ID:+${WIGGUM_TASK_ID}: }${WIGGUM_STEP_ID:-unknown} - ${agent_name}"

    # Set git author/committer identity
    git_set_identity

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
    start_time=$(epoch_now)
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

    # Advance workspace to latest origin/<default_branch> before pipeline starts.
    # Critical for resumed workers whose worktrees may be hours/days stale.
    local default_branch
    default_branch=$(get_default_branch)
    log "Advancing workspace to latest origin/$default_branch"
    if ! git_advance_to_main "$workspace"; then
        log_warn "Could not advance to origin/$default_branch — proceeding with current state"
    fi

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

    local pipeline_file
    pipeline_file=$(pipeline_resolve "$project_dir" "$task_id" "${WIGGUM_PIPELINE:-}") || true
    if [ -n "$pipeline_file" ]; then
        pipeline_load "$pipeline_file"
    else
        pipeline_load_builtin_defaults
    fi

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

    # Write stop-reason markers for infrastructure failures
    # These persist across resume cycles, unlike env vars
    case "${RALPH_LOOP_STOP_REASON:-}" in
        fast_fail)
            echo "$(epoch_now)" > "$worker_dir/stop-reason-fast-fail"
            log_warn "Stop-reason marker: fast_fail"
            ;;
        workspace_deleted)
            echo "$(epoch_now)" > "$worker_dir/stop-reason-workspace-deleted"
            log_warn "Stop-reason marker: workspace_deleted"
            ;;
    esac

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

    # Check test result from pipeline step
    local test_result
    test_result=$(agent_read_step_result "$worker_dir" "test")
    if [ "$test_result" = "FIX" ] || [ "$test_result" = "FAIL" ]; then
        log_error "Test step result: $test_result - marking task as failed"
        final_status="FAILED"
    fi

    local pr_url="N/A"
    local task_desc=""

    log_debug "Finalization check: has_violations=$has_violations, final_status=$final_status"

    # Skip PR creation if the pipeline already merged the PR (e.g., fix pipeline).
    # The merge step handles the full push+merge cycle; creating a new PR here
    # would produce a duplicate that triggers spurious fix cycles.
    local merge_step_result
    merge_step_result=$(agent_read_step_result "$worker_dir" "merge")
    local pipeline_already_merged=false
    if [ "$merge_step_result" = "PASS" ]; then
        pipeline_already_merged=true
        log "Pipeline merge step already merged the PR — skipping commit/PR creation"
    fi

    # Only create commits and PRs if no violations and task is complete
    if [ "$pipeline_already_merged" = true ]; then
        log_debug "Finalization: no PR creation needed (pipeline merged)"
        # Pick up existing PR URL for cleanup/kanban (pr_url.txt written by earlier pipeline run)
        if [ -f "$worker_dir/pr_url.txt" ]; then
            pr_url=$(cat "$worker_dir/pr_url.txt")
        fi
    elif [ "$has_violations" = false ] && [ "$final_status" = "COMPLETE" ]; then
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
        # If PR was created, mark as Pending Approval [P] - wiggum pr sync will mark [x] when merged
        # If no PR (gh CLI unavailable), mark as complete [x] directly
        if [ -n "$pr_url" ] && [ "$pr_url" != "N/A" ]; then
            log "Marking task $task_id as pending approval [P] in kanban (PR: $pr_url)"
            lifecycle_is_loaded || lifecycle_load
            if ! emit_event "$worker_dir" "worker.completion" "task-worker.COMPLETE"; then
                # Fallback for backward compatibility
                update_kanban_pending_approval "$RALPH_DIR/kanban.md" "$task_id" || true
            fi
            # PR status sync is separate from issue status
            github_pr_sync_task_status "$RALPH_DIR" "$task_id" "P" "=" || true
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
        lifecycle_is_loaded || lifecycle_load
        if ! emit_event "$worker_dir" "worker.failure" "task-worker.FAILED"; then
            # Fallback for backward compatibility
            update_kanban_failed "$RALPH_DIR/kanban.md" "$task_id" || true
        fi
        # Post failure summary to GitHub issue (non-blocking)
        _post_task_failure_to_github "$worker_dir" "$task_id" || true
        log_error "Task worker $worker_id failed task $task_id"
    fi

    # Log final worker status to audit log
    audit_log_worker_complete "$task_id" "$worker_id" "$final_status"

    # Update metrics.json with latest worker data
    log_debug "Exporting metrics to metrics.json"
    export_metrics "$RALPH_DIR" 2>/dev/null || true
}

# Post failure summary to GitHub issue
#
# Builds a markdown table from pipeline result files and posts it
# to the linked GitHub issue via github_issue_post_failure_summary.
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task ID
#
# Returns: 0 on success, 1 on failure or if no sync state
_post_task_failure_to_github() {
    local worker_dir="$1"
    local task_id="$2"

    # Skip if no results directory
    [ -d "$worker_dir/results" ] || return 0

    # Skip if no sync state (no GitHub integration)
    [ -f "$RALPH_DIR/github-sync-state.json" ] || return 0

    local summary=""

    # Include failure-summarizer report if available (the most critical information)
    local report_file=""
    report_file=$(find "$worker_dir/reports" -name "*-failure-summarize-report.md" 2>/dev/null | sort | tail -1)
    if [ -n "$report_file" ] && [ -f "$report_file" ]; then
        summary+="$(cat "$report_file")

"
    fi

    # Collect errors from failed steps
    local errors_section=""
    local result_file
    while IFS= read -r result_file; do
        [ -n "$result_file" ] || continue
        [ -f "$result_file" ] || continue

        local gate_result
        gate_result=$(jq -r '.outputs.gate_result // "UNKNOWN"' "$result_file" 2>/dev/null)
        gate_result="${gate_result:-UNKNOWN}"
        [ "$gate_result" = "FAIL" ] || continue

        local basename_file
        basename_file=$(basename "$result_file")
        local step_id
        step_id=$(echo "$basename_file" | sed -E 's/^[0-9]+-(.+)-result\.json$/\1/')

        local error_count
        error_count=$(jq '.errors | length' "$result_file" 2>/dev/null)
        error_count="${error_count:-0}"
        if [ "$error_count" -gt 0 ]; then
            local error_text
            error_text=$(jq -r '.errors[]' "$result_file" 2>/dev/null)
            errors_section+="**$step_id**: $error_text
"
        fi
    done < <(find "$worker_dir/results" -name "*-result.json" 2>/dev/null | sort)

    if [ -n "$errors_section" ]; then
        summary+="### Errors

$errors_section
"
    fi

    # Build pipeline results table
    summary+="<details>
<summary>Pipeline Results</summary>

| Step | Result | Duration |
|------|--------|----------|"

    while IFS= read -r result_file; do
        [ -n "$result_file" ] || continue
        [ -f "$result_file" ] || continue

        local basename_file
        basename_file=$(basename "$result_file")

        # Extract step_id from filename: <epoch>-<step_id>-result.json
        local step_id
        step_id=$(echo "$basename_file" | sed -E 's/^[0-9]+-(.+)-result\.json$/\1/')

        local gate_result duration_s
        gate_result=$(jq -r '.outputs.gate_result // "UNKNOWN"' "$result_file" 2>/dev/null)
        gate_result="${gate_result:-UNKNOWN}"
        duration_s=$(jq -r '.duration_seconds // 0' "$result_file" 2>/dev/null)
        duration_s="${duration_s:-0}"

        # Format duration
        local duration_str
        if [ "$duration_s" -lt 60 ]; then
            duration_str="${duration_s}s"
        elif [ "$duration_s" -lt 3600 ]; then
            duration_str="$((duration_s / 60))m $((duration_s % 60))s"
        else
            duration_str="$((duration_s / 3600))h $(( (duration_s % 3600) / 60 ))m"
        fi

        summary+="
| $step_id | $gate_result | $duration_str |"
    done < <(find "$worker_dir/results" -name "*-result.json" 2>/dev/null | sort)

    summary+="

</details>"

    source "$WIGGUM_HOME/lib/github/issue-writer.sh"
    github_issue_post_failure_summary "$RALPH_DIR" "$task_id" "$summary"
}
