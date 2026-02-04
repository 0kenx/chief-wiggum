#!/usr/bin/env bash
# lib/worker/cmd-resume.sh - Resume command logic for wiggum worker
#
# Provides: do_resume(), _read_resume_decision(), _handle_complete(), _handle_abort(), _handle_defer()
# Sourced by: bin/wiggum-worker

[ -n "${_CMD_RESUME_LOADED:-}" ] && return 0
_CMD_RESUME_LOADED=1

WIGGUM_HOME="${WIGGUM_HOME:-$HOME/.claude/chief-wiggum}"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/tasks/task-parser.sh"
source "$WIGGUM_HOME/lib/utils/audit-logger.sh"
source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"
source "$WIGGUM_HOME/lib/worker/agent-registry.sh"
source "$WIGGUM_HOME/lib/core/agent-base.sh"
source "$WIGGUM_HOME/lib/git/git-operations.sh"
source "$WIGGUM_HOME/lib/core/file-lock.sh"
source "$WIGGUM_HOME/lib/runtime/runtime.sh"
source "$WIGGUM_HOME/lib/backend/claude/usage-tracker.sh"
source "$WIGGUM_HOME/lib/pipeline/pipeline-loader.sh"
source "$WIGGUM_HOME/lib/core/resume-state.sh"
source "$WIGGUM_HOME/lib/core/safe-path.sh"

# Check if a step completed (has a result file) vs was interrupted (no result)
#
# A step that completed (even with FAIL) needs LLM analysis via resume-decide.
# A step that was interrupted mid-execution can be directly resumed.
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

# Get current step from pipeline config
#
# Args:
#   worker_dir - Worker directory path
#
# Echoes: step ID or empty string
_get_current_step() {
    local worker_dir="$1"
    local config_file="$worker_dir/pipeline-config.json"

    [ -f "$config_file" ] || return 0
    jq -r '.current.step_id // ""' "$config_file" 2>/dev/null
}

# Output message respecting quiet mode
_msg() {
    [ "$QUIET_MODE" = "true" ] || echo "$@"
}

# Resume a stopped worker
do_resume() {
    local worker_dir="$1"
    local force_mode="${2:-false}"
    local worker_id
    worker_id=$(basename "$worker_dir")
    local task_id
    # Match any task prefix format: TASK-001, PIPELINE-001, etc.
    task_id=$(echo "$worker_id" | sed -E 's/worker-([A-Za-z]{2,10}-[0-9]{1,4})-.*/\1/')

    safe_path "$RALPH_DIR" "RALPH_DIR" || return 1
    safe_path "$worker_dir" "worker_dir" || return 1
    # Initialize logging for resume command
    mkdir -p "$RALPH_DIR/logs"
    export LOG_FILE="$RALPH_DIR/logs/resume.log"
    source "$WIGGUM_HOME/lib/utils/activity-log.sh"
    activity_init "$PROJECT_DIR"

    log "Resuming worker $worker_id"
    log_debug "worker_dir=$worker_dir"
    log_debug "task_id=$task_id"
    log_debug "force_mode=$force_mode"
    activity_log "resume.started" "$worker_id" "$task_id"

    # Check if already running
    if [ -f "$worker_dir/agent.pid" ]; then
        local existing_pid
        existing_pid=$(cat "$worker_dir/agent.pid" 2>/dev/null)
        if kill -0 "$existing_pid" 2>/dev/null; then
            echo "Error: Worker $worker_id is already running (PID: $existing_pid)"
            exit $EXIT_ERROR
        fi
    fi

    # Check if resume already in progress
    if [ -f "$worker_dir/resume.pid" ]; then
        local resume_pid
        resume_pid=$(cat "$worker_dir/resume.pid" 2>/dev/null)
        if [[ "$resume_pid" =~ ^[0-9]+$ ]] && kill -0 "$resume_pid" 2>/dev/null; then
            echo "Error: Resume already in progress for $worker_id (PID: $resume_pid)"
            exit $EXIT_ERROR
        fi
        # Stale resume.pid — clean up
        rm -f "$worker_dir/resume.pid"
    fi

    # Track this resume process so wiggum-status can detect it
    echo "$$" > "$worker_dir/resume.pid"
    # shellcheck disable=SC2064
    trap "rm -f '${worker_dir}/resume.pid'" EXIT

    # Check main repo is clean (prevents workspace violations)
    local dirty_files
    dirty_files=$(cd "$PROJECT_DIR" && git status --porcelain 2>/dev/null | grep -v "^.. .ralph/" || true)
    if [ -n "$dirty_files" ]; then
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo "MAIN REPO HAS UNCOMMITTED CHANGES"
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo ""
        echo "Cannot resume worker - main repository has uncommitted changes:"
        echo "$dirty_files" | head -10
        echo ""
        echo "This would cause workspace boundary violations."
        echo "Please commit or stash your changes first."
        echo ""
        exit $EXIT_ERROR
    fi

    # Check for workspace violations
    if [ -f "$worker_dir/violation_status.txt" ]; then
        local violation_status
        violation_status=$(cat "$worker_dir/violation_status.txt" 2>/dev/null)
        if [ "$violation_status" = "WORKSPACE_VIOLATION" ]; then
            if [ "$force_mode" = "true" ]; then
                echo "Warning: Clearing workspace violation status (forced)"
                rm -f "$worker_dir/violation_status.txt"
            else
                echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
                echo "WORKSPACE VIOLATION DETECTED"
                echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
                echo ""
                echo "This worker was previously stopped due to a workspace violation."
                echo "Files were modified outside the worker's isolated workspace."
                echo ""
                echo "Before resuming, you should:"
                echo "  1. Review the violation log: $RALPH_DIR/logs/violations.log"
                echo "  2. Ensure no uncommitted changes exist in the main repo"
                echo "  3. Manually inspect $worker_dir/workspace for issues"
                echo ""
                echo "To force resume (clears violation status):"
                echo "  wiggum worker resume $worker_id -f"
                echo ""
                exit $EXIT_ERROR
            fi
        fi
    fi

    # Check PRD exists
    if [ ! -f "$worker_dir/prd.md" ]; then
        echo "Error: PRD not found at $worker_dir/prd.md"
        exit $EXIT_ERROR
    fi

    # Check workspace exists
    if [ ! -d "$worker_dir/workspace" ]; then
        echo "Error: Workspace not found at $worker_dir/workspace"
        echo "The worktree may have been cleaned up."
        exit $EXIT_ERROR
    fi

    _msg "Resuming worker $worker_id for task $task_id"
    _msg ""

    # === STEP 1: Check if step completed vs was interrupted ===
    local current_step resume_step needs_resume_decide=true resume_result_file=""
    current_step=$(_get_current_step "$worker_dir")

    if [ -n "$current_step" ] && ! _step_has_result "$worker_dir" "$current_step"; then
        # Step was interrupted mid-execution (no result file)
        # Direct resume is appropriate - no need for LLM analysis
        needs_resume_decide=false
        resume_step="$current_step"
        _msg "Step '$current_step' was interrupted (no result file) - resuming directly"
    else
        # Step completed (has result file) or no current step recorded
        # Need LLM to analyze what happened and decide resume point
        _msg "Step '${current_step:-unknown}' completed - running resume-decide agent"
    fi

    # === STEP 2: Convert logs to conversations (if needed for resume-decide) ===
    if [ "$needs_resume_decide" = "true" ]; then
        _msg "Converting logs to readable conversations..."
        if [ -d "$worker_dir/logs" ]; then
            "$WIGGUM_HOME/lib/utils/log-converter.sh" --dir "$worker_dir"
        else
            _msg "  No logs directory found — starting fresh"
            mkdir -p "$worker_dir/conversations"
            # Create a minimal worker.log so system.resume-decide has something to read
            if [ ! -f "$worker_dir/worker.log" ]; then
                echo "[$(date '+%Y-%m-%d %H:%M:%S')] Worker was interrupted before producing logs" > "$worker_dir/worker.log"
            fi
        fi

        # === STEP 3: Run system.resume-decide agent ===
        _msg "Analyzing previous run to decide resume step..."
        run_agent "system.resume-decide" "$worker_dir" "$PROJECT_DIR" 0 1

        # === STEP 4: Read decision ===
        # Get the result file path for later use (workspace recovery, instructions)
        resume_result_file=$(agent_find_latest_result "$worker_dir" "system.resume-decide")
    fi

    # === STEP 5: Parse decision ===
    local decision="" resume_pipeline="" resume_step_id=""
    _read_resume_decision "$worker_dir" "$needs_resume_decide" "$current_step"

    # Update resume state with this attempt
    resume_state_increment "$worker_dir" "$decision" "$resume_pipeline" "$resume_step_id" \
        "Resume attempt via wiggum worker resume"

    # Route by decision
    case "$decision" in
        COMPLETE) _handle_complete "$worker_dir" "$task_id" ;;
        ABORT)    _handle_abort "$worker_dir" "$task_id" ;;
        DEFER)    _handle_defer "$worker_dir" "$task_id" ;;
        RETRY)    ;; # fall through to pipeline validation + worker launch
        *)        _handle_abort "$worker_dir" "$task_id" ;; # unknown → abort
    esac

    # === RETRY path: Load pipeline config ===
    resume_step="$resume_step_id"
    local effective_pipeline="${resume_pipeline:-${WIGGUM_PIPELINE:-}}"
    local pipeline_file
    pipeline_file=$(pipeline_resolve "$PROJECT_DIR" "$task_id" "$effective_pipeline")
    if [ -n "$pipeline_file" ]; then
        pipeline_load "$pipeline_file" || {
            _msg "Error: Failed to load pipeline config: $pipeline_file"
            exit $EXIT_ERROR
        }
    else
        pipeline_load_builtin_defaults
    fi

    # Validate step exists in pipeline
    local step_idx
    step_idx=$(pipeline_find_step_index "$resume_step") || true
    if [ "$step_idx" = "-1" ]; then
        # Check if it's an inline step (e.g., "audit-fix" inside audit's on_result)
        local parent_step
        parent_step=$(pipeline_resolve_inline_to_parent "$resume_step")
        if [ -n "$parent_step" ]; then
            log "Mapping inline resume step '$resume_step' to parent step '$parent_step'"
            _msg "Note: '$resume_step' is an inline step — resuming from parent step '$parent_step'"
            resume_step="$parent_step"
            step_idx=$(pipeline_find_step_index "$resume_step") || true
        fi
    fi
    if [ "$step_idx" = "-1" ]; then
        # Build list of valid step IDs for error message
        local valid_steps=""
        local count
        count=$(pipeline_step_count)
        for ((i=0; i<count; i++)); do
            local sid
            sid=$(pipeline_get "$i" ".id")
            if [ -n "$valid_steps" ]; then
                valid_steps="$valid_steps, $sid"
            else
                valid_steps="$sid"
            fi
        done
        _msg "Error: Invalid resume step '$resume_step'"
        _msg "Valid steps from pipeline '$PIPELINE_NAME': $valid_steps"
        exit $EXIT_ERROR
    fi

    log "Resume decision: RETRY from '$resume_step' step (index $step_idx)"
    log_debug "needs_resume_decide=$needs_resume_decide pipeline=$effective_pipeline"
    activity_log "resume.decision" "$worker_id" "$task_id" \
        "decision=RETRY" "resume_step=$resume_step" "step_idx=$step_idx" \
        "pipeline=${effective_pipeline:-default}"

    _msg "Resume decision: RETRY from '$resume_step' step (index $step_idx)"
    _msg ""

    # === Handle workspace recovery if needed ===
    if [ "$needs_resume_decide" = "true" ]; then
        local last_checkpoint recovery_possible
        if [ -n "${resume_result_file:-}" ] && [ -f "$resume_result_file" ]; then
            last_checkpoint=$(jq -r '.outputs.workspace_recovery.last_checkpoint_step // ""' "$resume_result_file" 2>/dev/null)
            recovery_possible=$(jq -r '.outputs.workspace_recovery.recovery_possible // false' "$resume_result_file" 2>/dev/null)
        fi

        if [ "${recovery_possible:-false}" = "true" ] && [ -n "${last_checkpoint:-}" ]; then
            _msg "Workspace recovery checkpoint available: $last_checkpoint"

            local checkpoint_commit
            checkpoint_commit=$(cd "$worker_dir/workspace" && \
                git log --oneline --all --grep="$last_checkpoint" -1 --format="%H" 2>/dev/null || true)

            if [ -n "$checkpoint_commit" ]; then
                _msg "  Found checkpoint commit: ${checkpoint_commit:0:8}"

                local has_changes
                has_changes=$(cd "$worker_dir/workspace" && git status --porcelain 2>/dev/null | head -1)

                if [ -n "$has_changes" ]; then
                    _msg "  Workspace has uncommitted changes - preserving current state"
                    _msg "  (Use 'git reset --hard $checkpoint_commit' manually to reset if needed)"
                else
                    _msg "  Workspace has no uncommitted changes - ready for recovery"
                fi
            else
                _msg "  Note: No commit found for checkpoint '$last_checkpoint'"
                _msg "  Workspace state may be uncertain - proceeding anyway"
            fi
        fi
    fi
    _msg ""

    # === Check rate limit before launching ===
    usage_tracker_write_shared "$RALPH_DIR" > /dev/null 2>&1 || true
    if rate_limit_check "$RALPH_DIR"; then
        log "Rate limit threshold reached - waiting for cycle reset before resuming"
        rate_limit_wait_for_cycle_reset
        usage_tracker_write_shared "$RALPH_DIR" > /dev/null 2>&1 || true
    fi

    # === Mark task in-progress ===
    # Move task back to [=] (e.g., from [*] failed) so kanban reflects active work
    update_kanban_status "$RALPH_DIR/kanban.md" "$task_id" "=" || true

    # === Launch system.task-worker ===
    _msg "Launching system.task-worker from step: $resume_step"

    # Clean up stale agent.pid from resume-decide's run_agent call and reset
    # registry state so the parent EXIT trap doesn't delete the new PID file
    # created by the setsid subprocess.
    rm -f "$worker_dir/agent.pid"
    _AGENT_REGISTRY_IS_TOP_LEVEL=false
    _AGENT_RUNNER_DIR=""

    mkdir -p "$RALPH_DIR/logs"

    # Launch agent in background using setsid to create a new session/process group.
    # This prevents SIGINT from the parent (wiggum worker resume) from killing the worker.
    #
    # Security: Pass variables via environment exports, not string interpolation.
    # This prevents command injection if any variable contains shell metacharacters.
    export _WORKER_WIGGUM_HOME="$WIGGUM_HOME"
    export _WORKER_DIR="$worker_dir"
    export _WORKER_PROJECT_DIR="$PROJECT_DIR"
    export _WORKER_MAX_ITERATIONS="$MAX_ITERATIONS"
    export _WORKER_MAX_TURNS="$MAX_TURNS"
    export _WORKER_RESUME_STEP="$resume_step"

    # Read report path from result file (standard mechanism)
    local resume_instructions_path=""
    if [ -z "${resume_result_file:-}" ]; then
        resume_result_file=$(agent_find_latest_result "$worker_dir" "system.resume-decide")
    fi
    if [ -n "${resume_result_file:-}" ] && [ -f "$resume_result_file" ]; then
        resume_instructions_path=$(jq -r '.outputs.report_file // ""' "$resume_result_file")
    fi
    export _WORKER_RESUME_INSTRUCTIONS="${resume_instructions_path:-}"

    # shellcheck disable=SC2016
    setsid bash -c '
        set -euo pipefail
        _log_ts() { echo "[$(date -Iseconds)] $*"; }
        _log_ts "INFO: Worker subprocess starting (resume)"
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

    # Wait briefly for agent.pid to be created
    local wait_count=0
    while [ ! -f "$worker_dir/agent.pid" ] && [ $wait_count -lt 10 ]; do
        sleep 0.1
        ((++wait_count))
    done

    if [ -f "$worker_dir/agent.pid" ]; then
        local worker_pid
        worker_pid=$(cat "$worker_dir/agent.pid")
        _msg "Worker running (PID: $worker_pid)"
    else
        _msg "Worker started (PID file pending)"
    fi
    _msg "Use 'wiggum monitor' to follow progress"
}

# Read and parse the resume decision from resume-decision.json or resume-step.txt
#
# Sets outer-scope variables: decision, resume_pipeline, resume_step_id
#
# Args:
#   worker_dir          - Worker directory path
#   needs_resume_decide - "true" if resume-decide was run
#   current_step        - Current step from pipeline config (fallback for direct resume)
_read_resume_decision() {
    local worker_dir="$1"
    local needs_resume_decide="$2"
    local current_step="${3:-}"

    if [ "$needs_resume_decide" != "true" ]; then
        # Direct resume: step was interrupted mid-execution
        decision="RETRY"
        resume_step_id="$current_step"
        # Read pipeline name from pipeline-config.json so we load the correct pipeline
        if [ -f "$worker_dir/pipeline-config.json" ]; then
            resume_pipeline=$(jq -r '.pipeline.name // ""' "$worker_dir/pipeline-config.json" 2>/dev/null)
            if [[ "$resume_pipeline" == "null" ]]; then resume_pipeline=""; fi
        fi
        return
    fi

    # Read from structured JSON (preferred) or fallback to text file
    if [ -f "$worker_dir/resume-decision.json" ]; then
        decision=$(jq -r '.decision // "ABORT"' "$worker_dir/resume-decision.json")
        resume_pipeline=$(jq -r '.pipeline // ""' "$worker_dir/resume-decision.json")
        resume_step_id=$(jq -r '.resume_step // ""' "$worker_dir/resume-decision.json")
        # Normalize null to empty
        if [[ "$resume_pipeline" == "null" ]]; then resume_pipeline=""; fi
        if [[ "$resume_step_id" == "null" ]]; then resume_step_id=""; fi
    else
        # Backward compat: old resume-step.txt
        local raw
        raw=$(cat "$worker_dir/resume-step.txt" 2>/dev/null || echo "ABORT")
        raw=$(echo "$raw" | tr -d '[:space:]')
        if [[ "$raw" == RETRY:* ]]; then
            decision="RETRY"
            resume_pipeline=$(echo "$raw" | cut -d: -f2)
            resume_step_id=$(echo "$raw" | cut -d: -f3)
        elif [[ "$raw" == "COMPLETE" || "$raw" == "ABORT" || "$raw" == "DEFER" ]]; then
            decision="$raw"
        else
            # Legacy: bare step_id → treat as RETRY with current pipeline
            decision="RETRY"
            resume_step_id="$raw"
        fi
    fi
}

# Handle COMPLETE decision: ensure PR exists, mark task [P]
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task ID
_handle_complete() {
    local worker_dir="$1"
    local task_id="$2"
    local worker_id
    worker_id=$(basename "$worker_dir")

    _msg ""
    _msg "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    _msg "RESUME DECISION: COMPLETE"
    _msg "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    _msg ""

    # Check if PR already exists
    local pr_url=""
    if [ -f "$worker_dir/pr_url.txt" ]; then
        pr_url=$(cat "$worker_dir/pr_url.txt" 2>/dev/null)
    fi

    if [ -z "$pr_url" ]; then
        # No PR exists — push branch and create PR
        _msg "No PR found — creating PR..."
        local workspace="$worker_dir/workspace"
        if [ -d "$workspace" ]; then
            # Get branch name
            local branch_name
            branch_name=$(cd "$workspace" && git rev-parse --abbrev-ref HEAD 2>/dev/null || echo "")
            if [ -n "$branch_name" ] && [ "$branch_name" != "HEAD" ]; then
                # Push branch
                (cd "$workspace" && git push -u origin "$branch_name" 2>/dev/null) || true

                # Get task description from PRD
                local task_desc=""
                if [ -f "$worker_dir/prd.md" ]; then
                    task_desc=$(head -5 "$worker_dir/prd.md" | sed -n 's/^# *//p' | head -1)
                fi
                task_desc="${task_desc:-Task $task_id}"

                # Create PR
                local pr_exit=0
                git_create_pr "$branch_name" "$task_id" "$task_desc" "$worker_dir" "$PROJECT_DIR" || pr_exit=$?
                if [ $pr_exit -eq 0 ] && [ -n "${GIT_PR_URL:-}" ]; then
                    pr_url="$GIT_PR_URL"
                    echo "$pr_url" > "$worker_dir/pr_url.txt"
                    _msg "PR created: $pr_url"
                else
                    log_warn "Failed to create PR for $task_id (exit: $pr_exit)"
                    _msg "Warning: Could not create PR, but marking task as complete"
                fi
            else
                log_warn "No branch found in workspace for $task_id"
            fi
        fi
    else
        _msg "PR exists: $pr_url"
    fi

    # Mark task as [P] pending approval
    update_kanban_pending_approval "$RALPH_DIR/kanban.md" "$task_id" || true

    # Set git-state to needs_merge so merge flow picks it up
    echo "needs_merge" > "$worker_dir/git-state" 2>/dev/null || true

    # Mark resume state as terminal
    resume_state_set_terminal "$worker_dir" "Work complete, task marked [P]"

    # Show report if available
    local report
    report=$(agent_find_latest_report "$worker_dir" "system.resume-decide")
    if [ -n "$report" ] && [ -f "$report" ] && [ "$QUIET_MODE" != "true" ]; then
        _msg ""
        _msg "Analysis:"
        cat "$report"
    fi

    log "Task $task_id finalized as COMPLETE"
    activity_log "resume.complete" "$worker_id" "$task_id" "pr_url=${pr_url:-none}"
    _msg ""

    exit $EXIT_RESUME_COMPLETE
}

# Handle ABORT decision: mark task [*] failed
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task ID
_handle_abort() {
    local worker_dir="$1"
    local task_id="$2"
    local worker_id
    worker_id=$(basename "$worker_dir")

    _msg ""
    _msg "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    _msg "RESUME DECISION: ABORT"
    _msg "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    _msg ""

    # Mark task as [*] failed
    update_kanban_failed "$RALPH_DIR/kanban.md" "$task_id" || true

    # Mark resume state as terminal
    resume_state_set_terminal "$worker_dir" "Unrecoverable failure — aborted by resume-decide"

    # Show report if available
    local abort_report
    abort_report=$(agent_find_latest_report "$worker_dir" "system.resume-decide")
    if [ -n "$abort_report" ] && [ -f "$abort_report" ]; then
        _msg "Reason:"
        [ "$QUIET_MODE" = "true" ] || cat "$abort_report"
    fi

    log_error "Task $task_id marked FAILED by resume-decide (unrecoverable)"
    activity_log "resume.abort" "$worker_id" "$task_id"
    _msg ""

    exit $EXIT_RESUME_ABORT
}

# Handle DEFER decision: write cooldown, no kanban change
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task ID
_handle_defer() {
    local worker_dir="$1"
    local task_id="$2"
    local worker_id
    worker_id=$(basename "$worker_dir")

    _msg ""
    _msg "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    _msg "RESUME DECISION: DEFER"
    _msg "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    _msg ""

    # Load cooldown config
    load_resume_config

    # Set cooldown
    resume_state_set_cooldown "$worker_dir" "$RESUME_COOLDOWN_SECONDS"

    _msg "Task $task_id deferred — will retry after ${RESUME_COOLDOWN_SECONDS}s cooldown"

    # Show report if available
    local defer_report
    defer_report=$(agent_find_latest_report "$worker_dir" "system.resume-decide")
    if [ -n "$defer_report" ] && [ -f "$defer_report" ] && [ "$QUIET_MODE" != "true" ]; then
        _msg ""
        _msg "Reason:"
        cat "$defer_report"
    fi

    log "Task $task_id deferred by resume-decide (cooldown: ${RESUME_COOLDOWN_SECONDS}s)"
    activity_log "resume.defer" "$worker_id" "$task_id" "cooldown=${RESUME_COOLDOWN_SECONDS}"
    _msg ""

    exit $EXIT_RESUME_DEFER
}

