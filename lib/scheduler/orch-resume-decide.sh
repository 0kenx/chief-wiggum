#!/usr/bin/env bash
# orch-resume-decide.sh - Resume decision and background resume logic
#
# Extracted from orchestrator-functions.sh. Provides functions for
# determining resume actions (RETRY/COMPLETE/ABORT/DEFER), launching
# background decide/resume processes, and polling their results.
#
# Global arrays _PENDING_RESUMES and _PENDING_DECIDES are declared in
# orchestrator-functions.sh and referenced at call time.
set -euo pipefail

[ -n "${_ORCH_RESUME_DECIDE_LOADED:-}" ] && return 0
_ORCH_RESUME_DECIDE_LOADED=1

source "$WIGGUM_HOME/lib/core/atomic-write.sh"

# Check if a pipeline step completed (has a result file) vs was interrupted
#
# A step that completed (even with FAIL) needs LLM analysis via resume-decide.
# A step that was interrupted mid-execution can be directly resumed (RETRY).
#
# Args:
#   worker_dir - Worker directory path
#   step_id    - Step ID to check
#
# Returns: 0 if step completed (has result), 1 if interrupted (no result)
_step_has_result() {
    local worker_dir="$1"
    local step_id="$2"

    [ -d "$worker_dir/results" ] || return 1

    local result_file
    result_file=$(find "$worker_dir/results" -name "*-${step_id}-result.json" 2>/dev/null | sort -r | head -1)
    [ -f "$result_file" ]
}

# Handle an auto-ABORT decision for a worker (shared by fast-paths)
#
# Updates resume state, marks kanban as failed, sets terminal, and cleans up.
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier
#   reason     - Reason string for the abort
_resume_decide_handle_abort() {
    local worker_dir="$1"
    local task_id="$2"
    local reason="${3:-Unrecoverable — auto-aborted}"

    resume_state_increment "$worker_dir" "ABORT" "" "" "Auto-abort: $reason"
    update_kanban_failed "$RALPH_DIR/kanban.md" "$task_id" || true
    github_issue_sync_task_status "$RALPH_DIR" "$task_id" "*" || true
    resume_state_set_terminal "$worker_dir" "$reason"
    rm -f "$worker_dir/resume-decision.json"
    activity_log "worker.resume_abort" "$(basename "$worker_dir")" "$task_id"
    scheduler_mark_event
}

# Run resume-decide analysis for a single worker (blocking)
#
# Determines the resume action for a stopped worker:
#   - Interrupted steps (no result file): writes RETRY decision directly
#   - Completed steps: runs system.resume-decide agent for LLM analysis
#   - Handles COMPLETE/ABORT/DEFER decisions inline
#   - RETRY decisions are left for the unified queue to pick up
#
# Args:
#   worker_dir  - Worker directory path
#   task_id     - Task identifier
#   worker_type - Worker type (main, fix, resolve)
#
# Returns: 0 on success, 1 on failure
_resume_decide_for_worker() {
    local worker_dir="$1"
    local task_id="$2"
    local worker_type="$3"
    safe_path "$worker_dir" "worker_dir" || return 1

    local worker_id
    worker_id=$(basename "$worker_dir")

    # Get current step from pipeline config
    local current_step=""
    if [ -f "$worker_dir/pipeline-config.json" ]; then
        current_step=$(jq -r '.current.step_id // ""' "$worker_dir/pipeline-config.json" 2>/dev/null)
    fi

    # Fast path: interrupted step (no result file) → direct RETRY
    if [ -n "$current_step" ] && ! _step_has_result "$worker_dir" "$current_step"; then
        local _fast_pipeline=""
        if [ -f "$worker_dir/pipeline-config.json" ]; then
            _fast_pipeline=$(jq -r '.pipeline.name // ""' "$worker_dir/pipeline-config.json" 2>/dev/null)
            [[ "$_fast_pipeline" == "null" ]] && _fast_pipeline=""
        fi
        atomic_write "$worker_dir/resume-decision.json" jq -n --arg step "$current_step" --arg pipe "$_fast_pipeline" '{
            decision: "RETRY",
            pipeline: $pipe,
            resume_step: $step,
            reason: "Step interrupted, direct resume"
        }'
        log "Direct RETRY decision for $task_id (interrupted at $current_step)"
        return 0
    fi

    # Fast path: workspace deleted → ABORT (nothing to resume)
    if [ ! -d "$worker_dir/workspace" ]; then
        log "Direct ABORT for $task_id (workspace missing)"
        _resume_decide_handle_abort "$worker_dir" "$task_id" "Workspace no longer exists"
        return 0
    fi

    # Fast path: fast-fail marker → DEFER with long cooldown
    if [ -f "$worker_dir/stop-reason-fast-fail" ]; then
        local marker_epoch
        marker_epoch=$(cat "$worker_dir/stop-reason-fast-fail" 2>/dev/null)
        marker_epoch="${marker_epoch:-0}"
        local marker_age=$(( $(epoch_now) - marker_epoch ))
        if [ "$marker_age" -lt 3600 ]; then
            local cooldown=600
            resume_state_increment "$worker_dir" "DEFER" "" "" "Backend fast-fail (age: ${marker_age}s)"
            resume_state_set_cooldown "$worker_dir" "$cooldown"
            rm -f "$worker_dir/resume-decision.json"
            log "Direct DEFER for $task_id (fast-fail marker, age ${marker_age}s, cooldown ${cooldown}s)"
            return 0
        else
            # Marker is old, backend may have recovered — allow normal decide
            rm -f "$worker_dir/stop-reason-fast-fail"
        fi
    fi

    # Fast path: repeated same-step failures → ABORT
    if _has_repeated_step_failures "$worker_dir"; then
        log_error "Direct ABORT for $task_id (repeated failures at step ${current_step:-unknown})"
        _resume_decide_handle_abort "$worker_dir" "$task_id" \
            "Repeated failures at same pipeline step (${current_step:-unknown})"
        return 0
    fi

    # Slow path: need LLM analysis via resume-decide agent
    # Convert logs to readable conversations
    if [ -d "$worker_dir/logs" ]; then
        "$WIGGUM_HOME/lib/utils/log-converter.sh" --dir "$worker_dir" 2>/dev/null || true
    else
        mkdir -p "$worker_dir/conversations"
        if [ ! -f "$worker_dir/worker.log" ]; then
            echo "[$(date '+%Y-%m-%d %H:%M:%S')] Worker was interrupted before producing logs" > "$worker_dir/worker.log"
        fi
    fi

    # Run system.resume-decide agent
    source "$WIGGUM_HOME/lib/worker/agent-registry.sh"
    source "$WIGGUM_HOME/lib/core/agent-base.sh"
    local _agent_exit=0
    run_agent "system.resume-decide" "$worker_dir" "$PROJECT_DIR" 0 1 || _agent_exit=$?
    if [ "$_agent_exit" -ne 0 ]; then
        log_warn "resume-decide agent exited $_agent_exit for $task_id — will still process decision if written"
    fi

    # Read decision from resume-decision.json
    if [ ! -f "$worker_dir/resume-decision.json" ]; then
        log_error "resume-decide agent did not produce a decision for $task_id"
        return 1
    fi

    local decision
    decision=$(jq -r '.decision // "ABORT"' "$worker_dir/resume-decision.json" 2>/dev/null)

    case "$decision" in
        RETRY)
            # Update resume state and leave decision file for unified queue
            local resume_pipeline resume_step_id
            resume_pipeline=$(jq -r '.pipeline // ""' "$worker_dir/resume-decision.json" 2>/dev/null)
            resume_step_id=$(jq -r '.resume_step // ""' "$worker_dir/resume-decision.json" 2>/dev/null)
            [ "$resume_pipeline" = "null" ] && resume_pipeline=""
            [ "$resume_step_id" = "null" ] && resume_step_id=""

            resume_state_increment "$worker_dir" "RETRY" "$resume_pipeline" "$resume_step_id" \
                "Resume-decide recommended RETRY"

            # Enforce max attempts — convert RETRY to ABORT if exceeded
            if resume_state_max_exceeded "$worker_dir"; then
                log_error "Task $task_id hit max resume attempts — converting RETRY to ABORT"
                _resume_decide_handle_abort "$worker_dir" "$task_id" \
                    "Max resume attempts exceeded (RETRY at step ${resume_step_id:-unknown})"
                return 0
            fi

            log "Resume-decide for $task_id: RETRY from '$resume_step_id'"
            ;;
        COMPLETE)
            resume_state_increment "$worker_dir" "COMPLETE" "" "" "Resume-decide finalized as COMPLETE"

            # Create PR if needed
            local pr_url=""
            if [ -f "$worker_dir/pr_url.txt" ]; then
                pr_url=$(cat "$worker_dir/pr_url.txt" 2>/dev/null)
            fi
            if [ -z "$pr_url" ] && [ -d "$worker_dir/workspace" ]; then
                source "$WIGGUM_HOME/lib/git/git-operations.sh"
                local branch_name
                branch_name=$(cd "$worker_dir/workspace" && git rev-parse --abbrev-ref HEAD 2>/dev/null || echo "")
                if [ -n "$branch_name" ] && [ "$branch_name" != "HEAD" ]; then
                    (cd "$worker_dir/workspace" && git push -u origin "$branch_name" 2>/dev/null) || true
                    local task_desc=""
                    if [ -f "$worker_dir/prd.md" ]; then
                        task_desc=$(head -5 "$worker_dir/prd.md" | sed -n 's/^# *//p' | head -1)
                    fi
                    task_desc="${task_desc:-Task $task_id}"
                    local pr_exit=0
                    git_create_pr "$branch_name" "$task_id" "$task_desc" "$worker_dir" "$PROJECT_DIR" || pr_exit=$?
                    if [ $pr_exit -eq 0 ] && [ -n "${GIT_PR_URL:-}" ]; then
                        echo "$GIT_PR_URL" > "$worker_dir/pr_url.txt"
                    fi
                fi
            fi

            # Mark task [P] and set terminal
            update_kanban_pending_approval "$RALPH_DIR/kanban.md" "$task_id" || true
            resume_state_set_terminal "$worker_dir" "Work complete, task marked [P]"

            # Remove decision file so it doesn't enter unified queue
            rm -f "$worker_dir/resume-decision.json"
            log "Task $task_id finalized as COMPLETE by resume-decide"
            activity_log "worker.resume_complete" "$worker_id" "$task_id"
            scheduler_mark_event
            ;;
        ABORT)
            resume_state_increment "$worker_dir" "ABORT" "" "" "Resume-decide: unrecoverable failure"
            update_kanban_failed "$RALPH_DIR/kanban.md" "$task_id" || true
            github_issue_sync_task_status "$RALPH_DIR" "$task_id" "*" || true
            resume_state_set_terminal "$worker_dir" "Unrecoverable failure — aborted by resume-decide"
            rm -f "$worker_dir/resume-decision.json"
            log_error "Task $task_id marked FAILED by resume-decide (unrecoverable)"
            activity_log "worker.resume_abort" "$worker_id" "$task_id"
            scheduler_mark_event
            ;;
        DEFER)
            load_resume_config
            resume_state_increment "$worker_dir" "DEFER" "" "" "Resume-decide: deferred"
            resume_state_set_cooldown "$worker_dir" "$RESUME_COOLDOWN_SECONDS"
            rm -f "$worker_dir/resume-decision.json"
            log "Task $task_id deferred by resume-decide (cooldown: ${RESUME_COOLDOWN_SECONDS}s)"
            activity_log "worker.resume_defer" "$worker_id" "$task_id"
            ;;
        *)
            resume_state_increment "$worker_dir" "ABORT" "" "" "Unknown decision: $decision"
            update_kanban_failed "$RALPH_DIR/kanban.md" "$task_id" || true
            github_issue_sync_task_status "$RALPH_DIR" "$task_id" "*" || true
            resume_state_set_terminal "$worker_dir" "Unknown decision '$decision' — treated as ABORT"
            rm -f "$worker_dir/resume-decision.json"
            log_error "Task $task_id: unknown resume decision '$decision' — treated as ABORT"
            activity_log "worker.resume_abort" "$worker_id" "$task_id" "decision=$decision"
            scheduler_mark_event
            ;;
    esac

    return 0
}

# Launch a resume-decide process in background (non-blocking)
#
# Runs _resume_decide_for_worker in a background subshell, tracks the PID
# in _PENDING_DECIDES, and writes decide.pid to the worker directory.
#
# Args:
#   worker_dir  - Worker directory path
#   task_id     - Task identifier
#   worker_type - Worker type (main, fix, resolve)
#
# Side effects:
#   - Writes decide.pid to worker directory
#   - Writes to _PENDING_DECIDES associative array
#   - Appends to $RALPH_DIR/orchestrator/decide-pending disk file
_launch_decide_background() {
    local worker_dir="$1"
    local task_id="$2"
    local worker_type="$3"

    # Export variables needed by the subprocess
    export _DECIDE_WIGGUM_HOME="$WIGGUM_HOME"
    export _DECIDE_WORKER_DIR="$worker_dir"
    export _DECIDE_TASK_ID="$task_id"
    export _DECIDE_WORKER_TYPE="$worker_type"
    export _DECIDE_PROJECT_DIR="$PROJECT_DIR"
    export _DECIDE_RALPH_DIR="$RALPH_DIR"

    # shellcheck disable=SC2016
    (
        set -euo pipefail
        export WIGGUM_HOME="$_DECIDE_WIGGUM_HOME"
        export PROJECT_DIR="$_DECIDE_PROJECT_DIR"
        export RALPH_DIR="$_DECIDE_RALPH_DIR"

        source "$WIGGUM_HOME/lib/core/defaults.sh"
        source "$WIGGUM_HOME/lib/core/logger.sh"
        source "$WIGGUM_HOME/lib/core/exit-codes.sh"
        source "$WIGGUM_HOME/lib/core/platform.sh"
        source "$WIGGUM_HOME/lib/core/resume-state.sh"
        source "$WIGGUM_HOME/lib/core/file-lock.sh"
        source "$WIGGUM_HOME/lib/tasks/task-parser.sh"
        source "$WIGGUM_HOME/lib/utils/activity-log.sh"
        source "$WIGGUM_HOME/lib/scheduler/scheduler.sh"
        source "$WIGGUM_HOME/lib/scheduler/orchestrator-functions.sh"
        activity_init "$PROJECT_DIR"

        safe_path "$RALPH_DIR" "RALPH_DIR" || exit 1
        mkdir -p "$RALPH_DIR/logs"
        export LOG_FILE="$RALPH_DIR/logs/resume.log"

        _exit_code=0
        _resume_decide_for_worker "$_DECIDE_WORKER_DIR" "$_DECIDE_TASK_ID" "$_DECIDE_WORKER_TYPE" || _exit_code=$?
        echo "$_exit_code" > "$_DECIDE_WORKER_DIR/.decide-exit-code"
        rm -f "$_DECIDE_WORKER_DIR/decide.pid"
        exit "$_exit_code"
    ) >> "$RALPH_DIR/logs/workers.log" 2>&1 &
    local decide_pid=$!

    # Clean up exported decide variables from parent environment
    unset _DECIDE_WIGGUM_HOME _DECIDE_WORKER_DIR _DECIDE_TASK_ID \
          _DECIDE_WORKER_TYPE _DECIDE_PROJECT_DIR _DECIDE_RALPH_DIR

    # Write decide.pid so is_worker_running() sees this worker as busy
    echo "$decide_pid" > "$worker_dir/decide.pid"

    # Track decide process in-memory and persist to disk
    _PENDING_DECIDES[$decide_pid]="$worker_dir|$task_id|$worker_type"
    local _decide_pending="$RALPH_DIR/orchestrator/decide-pending"
    {
        flock -x 200
        echo "$decide_pid|$worker_dir|$task_id|$worker_type" >> "$_decide_pending"
    } 200>"$_decide_pending.lock"

    log "Resume-decide launched for $task_id (decide PID: $decide_pid)"
}

# Poll background resume-decide processes for completion
#
# Called each main-loop iteration. Checks if any resume-decide processes
# have finished. On completion:
#   - Exit 0: decision file written, unified queue handles RETRY next tick
#   - Non-zero: sets cooldown and increments resume state
#
# Side effects:
#   - Removes finished entries from _PENDING_DECIDES
#   - Ingests entries from decide-pending disk file
_poll_pending_decides() {
    # Ingest entries persisted to disk by _launch_decide_background
    local _decide_pending="$RALPH_DIR/orchestrator/decide-pending"
    if [ -s "$_decide_pending" ]; then
        local _dp_lines=""
        {
            flock -x 200
            _dp_lines=$(cat "$_decide_pending")
            : > "$_decide_pending"
        } 200>"$_decide_pending.lock"

        local _dp_line
        while IFS= read -r _dp_line; do
            [ -n "$_dp_line" ] || continue
            local _dp_pid _dp_wdir _dp_tid _dp_wtype
            IFS='|' read -r _dp_pid _dp_wdir _dp_tid _dp_wtype <<< "$_dp_line"
            # Skip if already tracked
            [ -z "${_PENDING_DECIDES[$_dp_pid]+x}" ] || continue
            _PENDING_DECIDES[$_dp_pid]="$_dp_wdir|$_dp_tid|$_dp_wtype"
        done <<< "$_dp_lines"
    fi

    [ ${#_PENDING_DECIDES[@]} -gt 0 ] || return 0

    local pid
    for pid in "${!_PENDING_DECIDES[@]}"; do
        # Still running? Skip.
        if kill -0 "$pid" 2>/dev/null; then
            continue
        fi

        # Parse metadata
        local entry="${_PENDING_DECIDES[$pid]}"
        unset '_PENDING_DECIDES[$pid]'
        local worker_dir task_id worker_type
        IFS='|' read -r worker_dir task_id worker_type <<< "$entry"

        # Clean up decide.pid if still present
        rm -f "$worker_dir/decide.pid"

        # Get exit code from file written by the decide wrapper
        local decide_exit=1
        if [ -f "$worker_dir/.decide-exit-code" ]; then
            decide_exit=$(cat "$worker_dir/.decide-exit-code")
            decide_exit="${decide_exit:-1}"
            rm -f "$worker_dir/.decide-exit-code"
        else
            # Fallback: try wait in case this was a direct child
            local _wait_rc=0
            wait "$pid" 2>/dev/null || _wait_rc=$?
            if [ "$_wait_rc" -ne 127 ]; then
                decide_exit="$_wait_rc"
            fi
        fi

        if [ "$decide_exit" -eq 0 ]; then
            # Decision written (or COMPLETE/ABORT/DEFER handled inline)
            log_debug "Resume-decide completed for $task_id (exit: 0)"
        else
            # Decide process itself crashed — set cooldown
            log_error "Resume-decide failed for $task_id (exit code: $decide_exit)"
            local _err_step=""
            if [ -f "$worker_dir/pipeline-config.json" ]; then
                _err_step=$(jq -r '.current.step_id // ""' "$worker_dir/pipeline-config.json" 2>/dev/null)
            fi
            resume_state_increment "$worker_dir" "ERROR" "" "${_err_step:-}" \
                "Resume-decide process failed (exit code: $decide_exit)"

            if resume_state_max_exceeded "$worker_dir"; then
                resume_state_set_terminal "$worker_dir" \
                    "Max resume attempts exceeded after decide errors (last exit: $decide_exit)"
                update_kanban_failed "$RALPH_DIR/kanban.md" "$task_id" || true
                github_issue_sync_task_status "$RALPH_DIR" "$task_id" "*" || true
                log_error "Task $task_id marked FAILED — max resume attempts exceeded (decide exit: $decide_exit)"
                activity_log "worker.resume_failed" "$(basename "$worker_dir")" "$task_id" \
                    "exit_code=$decide_exit reason=max_attempts_exceeded"
                scheduler_mark_event
            else
                local _min_retry="${RESUME_MIN_RETRY_INTERVAL:-30}"
                resume_state_set_cooldown "$worker_dir" "$_min_retry"
                log_error "Resume-decide failed for $task_id (exit: $decide_exit) — cooldown ${_min_retry}s"
                activity_log "worker.resume_decide_error" "$(basename "$worker_dir")" "$task_id" \
                    "exit_code=$decide_exit cooldown=$_min_retry"
            fi

            # Clean up any partial decision file
            rm -f "$worker_dir/resume-decision.json"
        fi
    done
}

# Recover stranded resume decisions after orchestrator restart
#
# Scans for workers with resume-decision.json that aren't running and aren't
# tracked in _PENDING_DECIDES. For non-RETRY decisions (COMPLETE/ABORT/DEFER),
# processes them inline using the same logic as _resume_decide_for_worker().
# RETRY decisions are left for get_workers_with_retry_decision to pick up.
#
# This handles the case where run_agent exits non-zero in _resume_decide_for_worker
# after writing the decision file, or the orchestrator restarts after decisions
# are written but before they're processed.
#
# Globals:
#   RALPH_DIR   - Required
#   PROJECT_DIR - Required
#   _PENDING_DECIDES - Checked to avoid double-processing
#
# Returns: 0 always (errors are logged per-worker)
_recover_stranded_decisions() {
    [ -d "$RALPH_DIR/workers" ] || return 0

    local worker_dir
    for worker_dir in "$RALPH_DIR/workers"/worker-*; do
        [ -d "$worker_dir" ] || continue
        [ -f "$worker_dir/resume-decision.json" ] || continue

        # Skip if worker is running
        is_worker_running "$worker_dir" && continue

        # Skip if tracked by _PENDING_DECIDES (being handled)
        local _tracked=false
        local _pid
        for _pid in "${!_PENDING_DECIDES[@]}"; do
            local _entry="${_PENDING_DECIDES[$_pid]}"
            [[ "$_entry" == "$worker_dir|"* ]] && { _tracked=true; break; }
        done
        [ "$_tracked" = "true" ] && continue

        local decision
        decision=$(jq -r '.decision // ""' "$worker_dir/resume-decision.json" 2>/dev/null)

        # RETRY is handled by get_workers_with_retry_decision — skip
        [ "$decision" = "RETRY" ] && continue

        local task_id worker_id
        task_id=$(get_task_id_from_worker "$(basename "$worker_dir")")
        worker_id=$(basename "$worker_dir")

        log_warn "Recovering stranded $decision decision for $task_id"

        case "$decision" in
            COMPLETE)
                resume_state_increment "$worker_dir" "COMPLETE" "" "" \
                    "Recovered stranded COMPLETE decision"

                # Try to create PR if workspace and branch exist
                local pr_url=""
                [ -f "$worker_dir/pr_url.txt" ] && pr_url=$(cat "$worker_dir/pr_url.txt" 2>/dev/null)
                if [ -z "$pr_url" ] && [ -d "$worker_dir/workspace" ]; then
                    source "$WIGGUM_HOME/lib/git/git-operations.sh"
                    local branch_name
                    branch_name=$(cd "$worker_dir/workspace" && git rev-parse --abbrev-ref HEAD 2>/dev/null || echo "")
                    if [ -n "$branch_name" ] && [ "$branch_name" != "HEAD" ]; then
                        (cd "$worker_dir/workspace" && git push -u origin "$branch_name" 2>/dev/null) || true
                        local task_desc=""
                        [ -f "$worker_dir/prd.md" ] && task_desc=$(head -5 "$worker_dir/prd.md" | sed -n 's/^# *//p' | head -1)
                        task_desc="${task_desc:-Task $task_id}"
                        local pr_exit=0
                        git_create_pr "$branch_name" "$task_id" "$task_desc" "$worker_dir" "$PROJECT_DIR" || pr_exit=$?
                        if [ $pr_exit -eq 0 ] && [ -n "${GIT_PR_URL:-}" ]; then
                            echo "$GIT_PR_URL" > "$worker_dir/pr_url.txt"
                            pr_url="$GIT_PR_URL"
                        fi
                    fi
                fi

                if [ -n "$pr_url" ] || [ -d "$worker_dir/workspace" ]; then
                    update_kanban_pending_approval "$RALPH_DIR/kanban.md" "$task_id" || true
                    github_issue_sync_task_status "$RALPH_DIR" "$task_id" "P" || true
                    resume_state_set_terminal "$worker_dir" "Recovered: work complete, task marked [P]"
                else
                    # No workspace, no PR — work was lost
                    update_kanban_failed "$RALPH_DIR/kanban.md" "$task_id" || true
                    github_issue_sync_task_status "$RALPH_DIR" "$task_id" "*" || true
                    resume_state_set_terminal "$worker_dir" "Recovered: COMPLETE but no workspace or PR — work lost"
                    log_error "Task $task_id COMPLETE decision but no workspace or PR — marking failed"
                fi

                rm -f "$worker_dir/resume-decision.json"
                activity_log "worker.resume_complete" "$worker_id" "$task_id" "recovered=true"
                scheduler_mark_event
                ;;
            ABORT)
                resume_state_increment "$worker_dir" "ABORT" "" "" "Recovered stranded ABORT"
                update_kanban_failed "$RALPH_DIR/kanban.md" "$task_id" || true
                github_issue_sync_task_status "$RALPH_DIR" "$task_id" "*" || true
                resume_state_set_terminal "$worker_dir" "Recovered: aborted by resume-decide"
                rm -f "$worker_dir/resume-decision.json"
                activity_log "worker.resume_abort" "$worker_id" "$task_id" "recovered=true"
                scheduler_mark_event
                ;;
            DEFER)
                load_resume_config
                resume_state_increment "$worker_dir" "DEFER" "" "" "Recovered stranded DEFER"
                resume_state_set_cooldown "$worker_dir" "$RESUME_COOLDOWN_SECONDS"
                rm -f "$worker_dir/resume-decision.json"
                activity_log "worker.resume_defer" "$worker_id" "$task_id" "recovered=true"
                ;;
            *)
                resume_state_increment "$worker_dir" "ABORT" "" "" "Recovered unknown decision: $decision"
                update_kanban_failed "$RALPH_DIR/kanban.md" "$task_id" || true
                github_issue_sync_task_status "$RALPH_DIR" "$task_id" "*" || true
                resume_state_set_terminal "$worker_dir" "Recovered: unknown decision '$decision'"
                rm -f "$worker_dir/resume-decision.json"
                scheduler_mark_event
                ;;
        esac
    done
}

# Launch a resume worker synchronously (blocking until PID is obtained)
#
# Reads resume-decision.json for resume_step and pipeline, validates the
# step, launches the worker via setsid, waits for agent.pid, and marks
# the decision as consumed.
#
# Sets: SPAWNED_WORKER_PID, SPAWNED_WORKER_ID (for caller to use)
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier
#
# Returns: 0 on success, 1 on failure
_launch_resume_worker() {
    local worker_dir="$1"
    local task_id="$2"

    SPAWNED_WORKER_PID=""
    SPAWNED_WORKER_ID=""

    # Read decision
    if [ ! -f "$worker_dir/resume-decision.json" ]; then
        log_error "No resume-decision.json for $task_id"
        return 1
    fi

    local resume_step resume_pipeline
    resume_step=$(jq -r '.resume_step // "execution"' "$worker_dir/resume-decision.json" 2>/dev/null)
    resume_pipeline=$(jq -r '.pipeline // ""' "$worker_dir/resume-decision.json" 2>/dev/null)
    [ "$resume_step" = "null" ] && resume_step="execution"
    [ "$resume_pipeline" = "null" ] && resume_pipeline=""

    # Read report/instructions path from resume-decide result file
    local resume_instructions_path=""
    local resume_result_file
    source "$WIGGUM_HOME/lib/core/agent-result.sh"
    resume_result_file=$(agent_find_latest_result "$worker_dir" "system.resume-decide" 2>/dev/null || true)
    if [ -n "${resume_result_file:-}" ] && [ -f "$resume_result_file" ]; then
        resume_instructions_path=$(jq -r '.outputs.report_file // ""' "$resume_result_file" 2>/dev/null)
    fi

    # Validate pipeline step
    local effective_pipeline="${resume_pipeline:-${WIGGUM_PIPELINE:-}}"
    source "$WIGGUM_HOME/lib/pipeline/pipeline-loader.sh"
    local pipeline_file
    pipeline_file=$(pipeline_resolve "$PROJECT_DIR" "$task_id" "$effective_pipeline")
    if [ -n "$pipeline_file" ]; then
        pipeline_load "$pipeline_file" || {
            log_error "Failed to load pipeline config: $pipeline_file"
            return 1
        }
    else
        pipeline_load_builtin_defaults
    fi

    local step_idx
    step_idx=$(pipeline_find_step_index "$resume_step") || true
    if [ "$step_idx" = "-1" ]; then
        # Check if it's an inline step (e.g., "test-fix" inside test's on_result)
        local parent_step
        parent_step=$(pipeline_resolve_inline_to_parent "$resume_step")
        if [ -n "$parent_step" ]; then
            log "Mapping inline resume step '$resume_step' to parent step '$parent_step' for $task_id"
            resume_step="$parent_step"
            step_idx=$(pipeline_find_step_index "$resume_step") || true
        fi
    fi
    if [ "$step_idx" = "-1" ]; then
        log_error "Invalid resume step '$resume_step' for $task_id"
        return 1
    fi

    log "Launching resume worker for $task_id from step '$resume_step' (index $step_idx)"

    # Move task back to [=] in-progress (e.g., from [*] failed)
    update_kanban_status "$RALPH_DIR/kanban.md" "$task_id" "=" || true

    # Launch worker via setsid (same pattern as bin/wiggum-worker resume)
    export _WORKER_WIGGUM_HOME="$WIGGUM_HOME"
    export _WORKER_DIR="$worker_dir"
    export _WORKER_PROJECT_DIR="$PROJECT_DIR"
    export _WORKER_MAX_ITERATIONS="$MAX_ITERATIONS"
    export _WORKER_MAX_TURNS="$MAX_TURNS"
    export _WORKER_RESUME_STEP="$resume_step"
    export _WORKER_RESUME_INSTRUCTIONS="${resume_instructions_path:-}"

    # shellcheck disable=SC2016
    setsid bash -c '
        set -euo pipefail
        _log_ts() { echo "[$(date -Iseconds)] $*"; }
        _log_ts "INFO: Worker subprocess starting (two-phase resume)"
        _log_ts "INFO: WIGGUM_HOME=$_WORKER_WIGGUM_HOME"
        _log_ts "INFO: worker_dir=$_WORKER_DIR"
        _log_ts "INFO: resume_step=$_WORKER_RESUME_STEP"

        export WIGGUM_HOME="$_WORKER_WIGGUM_HOME"

        if ! source "$WIGGUM_HOME/lib/worker/agent-registry.sh" 2>&1; then
            _log_ts "ERROR: Failed to source agent-registry.sh"
            exit 1
        fi

        _log_ts "INFO: Running agent system.task-worker"
        _exit_code=0
        run_agent "system.task-worker" "$_WORKER_DIR" "$_WORKER_PROJECT_DIR" 30 "$_WORKER_MAX_ITERATIONS" "$_WORKER_MAX_TURNS" \
            "$_WORKER_RESUME_STEP" "$_WORKER_RESUME_INSTRUCTIONS" || _exit_code=$?
        if [ $_exit_code -ne 0 ]; then
            _log_ts "ERROR: run_agent failed with exit code $_exit_code"
            exit 1
        fi
    ' >> "$RALPH_DIR/logs/workers.log" 2>&1 &

    # Clean up exported worker variables from parent environment
    unset _WORKER_WIGGUM_HOME _WORKER_DIR _WORKER_PROJECT_DIR \
          _WORKER_MAX_ITERATIONS _WORKER_MAX_TURNS _WORKER_RESUME_STEP \
          _WORKER_RESUME_INSTRUCTIONS

    # Wait for agent.pid (with timeout)
    local wait_timeout="${PID_WAIT_TIMEOUT:-300}"
    if ! wait_for_worker_pid "$worker_dir" "$wait_timeout"; then
        log_error "Agent PID file not created for $task_id after resume launch"
        return 1
    fi

    SPAWNED_WORKER_PID=$(cat "$worker_dir/agent.pid")
    SPAWNED_WORKER_ID=$(basename "$worker_dir")

    # Mark decision as consumed so it doesn't re-enter the queue
    mv "$worker_dir/resume-decision.json" "$worker_dir/resume-decision.json.consumed"

    activity_log "worker.resumed" "$SPAWNED_WORKER_ID" "$task_id" \
        "pipeline_step=$resume_step pid=$SPAWNED_WORKER_PID"

    return 0
}

# Poll background resume processes for completion
#
# Called each main-loop iteration. Checks if any wiggum-worker resume processes
# launched by _schedule_resume_workers() have finished, and if so, registers
# the resulting worker into the pool.
_poll_pending_resumes() {
    # Ingest entries persisted to disk by _schedule_resume_workers.
    # This is the primary mechanism when the function runs inside a
    # periodic-service subshell (where in-memory updates are lost).
    local _resume_pending="$RALPH_DIR/orchestrator/resume-pending"
    if [ -s "$_resume_pending" ]; then
        local _rp_lines=""
        {
            flock -x 200
            _rp_lines=$(cat "$_resume_pending")
            : > "$_resume_pending"
        } 200>"$_resume_pending.lock"

        local _rp_line
        while IFS= read -r _rp_line; do
            [ -n "$_rp_line" ] || continue
            local _rp_pid _rp_wdir _rp_tid _rp_wtype
            IFS='|' read -r _rp_pid _rp_wdir _rp_tid _rp_wtype <<< "$_rp_line"
            # Skip if already tracked
            [ -z "${_PENDING_RESUMES[$_rp_pid]+x}" ] || continue
            _PENDING_RESUMES[$_rp_pid]="$_rp_wdir|$_rp_tid|$_rp_wtype"
        done <<< "$_rp_lines"
    fi

    [ ${#_PENDING_RESUMES[@]} -gt 0 ] || return 0

    local pid
    for pid in "${!_PENDING_RESUMES[@]}"; do
        # Still running? Skip.
        if kill -0 "$pid" 2>/dev/null; then
            continue
        fi

        # Parse metadata
        local entry="${_PENDING_RESUMES[$pid]}"
        unset '_PENDING_RESUMES[$pid]'
        local worker_dir task_id worker_type
        IFS='|' read -r worker_dir task_id worker_type <<< "$entry"

        # Get exit code from file written by the resume wrapper.
        # wait(2) cannot be used because the resume PID is not a direct
        # child when _schedule_resume_workers ran in a subshell.
        local resume_exit=1
        if [ -f "$worker_dir/.resume-exit-code" ]; then
            resume_exit=$(cat "$worker_dir/.resume-exit-code")
            resume_exit="${resume_exit:-1}"
            rm -f "$worker_dir/.resume-exit-code"
        else
            # Fallback: try wait in case this was a direct child
            local _wait_rc=0
            wait "$pid" 2>/dev/null || _wait_rc=$?
            if [ "$_wait_rc" -ne 127 ]; then
                resume_exit="$_wait_rc"
            fi
        fi

        case "$resume_exit" in
            0)
                # RETRY: worker subprocess launched — poll for PID
                if wait_for_worker_pid "$worker_dir" "$PID_WAIT_TIMEOUT"; then
                    local wpid
                    wpid=$(cat "$worker_dir/agent.pid")
                    pool_add "$wpid" "$worker_type" "$task_id"
                    scheduler_mark_event
                    activity_log "worker.resumed" "$(basename "$worker_dir")" "$task_id" \
                        "pipeline_step=$(cat "$worker_dir/current_step" 2>/dev/null || echo unknown) pid=$wpid type=$worker_type"
                    log "Resumed worker for $task_id (PID: $wpid, type: $worker_type)"
                else
                    log_error "Resume started but PID not created for $task_id"
                fi
                ;;
            "$EXIT_RESUME_COMPLETE")
                log "Task $task_id finalized as COMPLETE by resume-decide"
                activity_log "worker.resume_complete" "$(basename "$worker_dir")" "$task_id"
                scheduler_mark_event
                ;;
            "$EXIT_RESUME_ABORT")
                log_error "Task $task_id marked FAILED by resume-decide (unrecoverable)"
                activity_log "worker.resume_abort" "$(basename "$worker_dir")" "$task_id"
                scheduler_mark_event
                ;;
            "$EXIT_RESUME_DEFER")
                log "Task $task_id deferred by resume-decide (will retry after cooldown)"
                activity_log "worker.resume_defer" "$(basename "$worker_dir")" "$task_id"
                ;;
            *)
                # Track the failure so resume_state_max_exceeded() eventually stops retrying.
                # wiggum-worker resume only calls resume_state_increment after a successful
                # resume-decide decision, so crashes before that leave state untouched.
                local _err_step=""
                if [[ -f "$worker_dir/pipeline-config.json" ]]; then
                    _err_step=$(jq -r '.current.step_id // ""' "$worker_dir/pipeline-config.json" 2>/dev/null)
                fi
                resume_state_increment "$worker_dir" "ERROR" "" "${_err_step:-}" \
                    "Resume process failed (exit code: $resume_exit)"

                if resume_state_max_exceeded "$worker_dir"; then
                    resume_state_set_terminal "$worker_dir" \
                        "Max resume attempts exceeded after repeated errors (last exit: $resume_exit)"
                    update_kanban_failed "$RALPH_DIR/kanban.md" "$task_id" || true
                    github_issue_sync_task_status "$RALPH_DIR" "$task_id" "*" || true
                    log_error "Task $task_id marked FAILED — max resume attempts exceeded (exit code: $resume_exit)"
                    activity_log "worker.resume_failed" "$(basename "$worker_dir")" "$task_id" \
                        "exit_code=$resume_exit reason=max_attempts_exceeded"
                    scheduler_mark_event
                else
                    # Short cooldown to prevent same-tick retry; priority
                    # degradation is automatic via attempt_count in
                    # get_unified_work_queue().
                    local _min_retry="${RESUME_MIN_RETRY_INTERVAL:-30}"
                    resume_state_set_cooldown "$worker_dir" "$_min_retry"
                    log_error "Resume failed for $task_id (exit code: $resume_exit) — will retry after ${_min_retry}s cooldown"
                    activity_log "worker.resume_error" "$(basename "$worker_dir")" "$task_id" \
                        "exit_code=$resume_exit cooldown=$_min_retry"
                fi
                ;;
        esac
    done
}
