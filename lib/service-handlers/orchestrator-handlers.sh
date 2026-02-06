#!/usr/bin/env bash
# =============================================================================
# orchestrator-handlers.sh - Service handlers for orchestrator functions
#
# This module provides the ONLY functions callable by the service scheduler.
# All service handler functions MUST:
#   1. Be defined in files under lib/service-handlers/
#   2. Use the svc_* prefix (enforced by service-runner.sh)
#
# These are thin wrappers around the orchestrator functions in
# lib/scheduler/orchestrator-functions.sh. The wrapper pattern provides:
#   - Security boundary (only svc_* functions can be invoked via services.json)
#   - Clear contract for what services can do
#   - Centralized location for all service entry points
#
# Naming convention: svc_orch_* for orchestrator-related handlers
# =============================================================================

# Prevent double-sourcing
[ -n "${_SERVICE_HANDLERS_ORCH_LOADED:-}" ] && return 0
_SERVICE_HANDLERS_ORCH_LOADED=1

# Source memory service handlers
source "$WIGGUM_HOME/lib/service-handlers/memory-handlers.sh"

# Source meta-agent service handlers
source "$WIGGUM_HOME/lib/service-handlers/meta-handlers.sh"

# =============================================================================
# Orchestrator Service Handlers
#
# Each handler wraps a function from lib/scheduler/orchestrator-functions.sh
# =============================================================================

# Update shared usage data for rate limiting
svc_orch_usage_tracker_write_shared() {
    orch_usage_tracker_write_shared "$@"
}

# Create workspaces for orphaned PRs
svc_orch_create_orphan_pr_workspaces() {
    orch_create_orphan_pr_workspaces "$@"
}

# Spawn PR optimizer in background
svc_orch_spawn_pr_optimizer() {
    orch_spawn_pr_optimizer "$@"
}

# Check for completed PR optimizer
svc_orch_check_pr_optimizer() {
    orch_check_pr_optimizer "$@"
}

# Check for conflict batches and spawn multi-PR planner
svc_orch_spawn_multi_pr_planner() {
    orch_spawn_multi_pr_planner "$@"
}

# Spawn fix workers for PR comment issues
svc_orch_spawn_fix_workers() {
    orch_spawn_fix_workers "$@"
}

# Spawn resolve workers for merge conflicts
svc_orch_spawn_resolve_workers() {
    orch_spawn_resolve_workers "$@"
}

# Clean up finished main workers
svc_orch_cleanup_main_workers() {
    orch_cleanup_main_workers "$@"
}

# Clean up finished/timed-out fix workers
svc_orch_cleanup_fix_workers() {
    orch_cleanup_fix_workers "$@"
}

# Clean up finished/timed-out resolve workers
svc_orch_cleanup_resolve_workers() {
    orch_cleanup_resolve_workers "$@"
}

# Spawn workers for ready tasks
svc_orch_spawn_ready_tasks() {
    orch_spawn_ready_tasks "$@"
}

# Clean up all finished workers (main, fix, resolve)
svc_orch_cleanup_all_workers() {
    orch_cleanup_all_workers "$@"
}

# Process orphaned fix_completed/needs_merge workers (only when state changed)
svc_orch_process_pending_merges() {
    [[ "${POOL_CLEANUP_EVENT:-false}" = "true" ]] \
        || [[ "${SCHED_SCHEDULING_EVENT:-false}" = "true" ]] \
        || return 0
    orch_process_pending_merges "$@"
}

# Display orchestrator status on scheduling events
svc_orch_display_status() {
    orch_display_status "$@"
}

# Sync GitHub issues to local kanban and push status updates
svc_orch_github_issue_sync() {
    orch_github_issue_sync "$@"
}

# Sync plan files with GitHub issue comments
svc_orch_github_plan_sync() {
    orch_github_plan_sync "$@"
}

# Run failure recovery for failed workers
svc_orch_failure_recovery() {
    orch_failure_recovery "$@"
}

# Rotate oversized global log files
svc_orch_log_rotation() {
    log_rotation_check_all
}

# =============================================================================
# Startup Phase Handlers (Phase 3)
# =============================================================================

# Validate kanban format
svc_orch_validate_kanban() {
    log "Validating kanban.md format..."
    if ! "$WIGGUM_HOME/bin/wiggum-validate" --quiet; then
        log_error "Kanban validation failed. Run 'wiggum validate' to see details."
        return 1
    fi
    log "Kanban validation passed"
}

# Initialize scheduler and detect dependency cycles
svc_orch_init_scheduler() {
    # Use distributed scheduler initialization if in github or hybrid mode
    if [[ "${WIGGUM_TASK_SOURCE_MODE:-local}" != "local" ]]; then
        scheduler_init_with_task_source "$RALPH_DIR" "$PROJECT_DIR" \
            "$AGING_FACTOR" "$SIBLING_WIP_PENALTY" "$PLAN_BONUS" "$DEP_BONUS_PER_TASK" \
            "$RESUME_INITIAL_BONUS" "$RESUME_FAIL_PENALTY" "${WIGGUM_SERVER_ID:-}"
    else
        scheduler_init "$RALPH_DIR" "$PROJECT_DIR" \
            "$AGING_FACTOR" "$SIBLING_WIP_PENALTY" "$PLAN_BONUS" "$DEP_BONUS_PER_TASK" \
            "$RESUME_INITIAL_BONUS" "$RESUME_FAIL_PENALTY"
    fi

    log "Checking for dependency cycles..."
    scheduler_detect_cycles || true
}

# Pre-flight: check clean git status and pull main
svc_orch_preflight_git() {
    if [ -n "$(git status --porcelain 2>/dev/null)" ]; then
        log_error "Git working directory is not clean. Please commit or stash your changes before running."
        echo ""
        echo "Uncommitted changes detected:"
        git status --short
        return 1
    fi

    log "Pulling latest changes from origin/main..."
    if ! git pull --ff-only origin main 2>&1; then
        log_error "Git pull failed. Please resolve any issues before running."
        return 1
    fi
}

# Pre-flight: test SSH connection
svc_orch_preflight_ssh() {
    log "Running pre-flight checks..."

    local git_remote
    git_remote=$(git remote get-url origin 2>/dev/null)
    if [ -n "$git_remote" ]; then
        local git_host=""
        if [[ "$git_remote" =~ ^git@([^:]+): ]]; then
            git_host="${BASH_REMATCH[1]}"
        elif [[ "$git_remote" =~ ^ssh://git@([^/]+)/ ]]; then
            git_host="${BASH_REMATCH[1]}"
        fi

        if [ -n "$git_host" ]; then
            echo "  → Testing SSH connection to $git_host..."
            local ssh_output
            ssh_output=$(ssh -T "git@$git_host" 2>&1) || true
            echo "$ssh_output" | head -5
            if ! echo "$ssh_output" | grep -qi "successfully authenticated"; then
                log_error "SSH test failed. Please ensure your SSH keys are set up and the agent is running."
                echo ""
                echo "Try running: ssh -T git@$git_host"
                return 1
            fi
            echo "  ✓ SSH connection successful"
        fi
    fi
}

# Pre-flight: test GitHub CLI authentication
svc_orch_preflight_gh() {
    echo "  → Checking gh auth status..."
    if gh auth status &>/dev/null; then
        echo "  ✓ GitHub CLI authenticated"
    else
        log_error "gh auth check failed. Please log in with: gh auth login"
        echo ""
        echo "Try running: gh auth status"
        return 1
    fi
    echo ""
}

# Restore active workers from existing worker directories
svc_orch_restore_workers() {
    scheduler_restore_workers
}

# Initialize terminal header display
svc_orch_init_terminal() {
    local mode_desc="standard"
    if [[ "$WIGGUM_RUN_MODE" == "fix-only" ]]; then
        mode_desc="fix-only"
    elif [[ "$WIGGUM_RUN_MODE" == "merge-only" ]]; then
        mode_desc="merge-only"
    elif [[ "$WIGGUM_RUN_MODE" == "resume-only" ]]; then
        mode_desc="resume-only"
    elif [ "${WIGGUM_SMART_MODE:-false}" = "true" ]; then
        mode_desc="smart"
    elif [ "${WIGGUM_PLAN_MODE:-false}" = "true" ]; then
        mode_desc="plan mode"
    fi
    if [ -n "${WIGGUM_PIPELINE:-}" ]; then
        mode_desc="$mode_desc, pipeline: $WIGGUM_PIPELINE"
    fi

    # Display failed tasks info
    local failed_tasks
    failed_tasks=$(get_failed_tasks "$RALPH_DIR/kanban.md")
    if [ -n "$failed_tasks" ]; then
        local failed_count
        failed_count=$(echo "$failed_tasks" | wc -w)
        log "Found $failed_count failed task(s) - waiting (use 'wiggum worker resume' to restart):"
        for task_id in $failed_tasks; do
            echo "  ⏸ $task_id"
        done
        echo ""
    fi

    log "Starting Chief Wiggum in $PROJECT_DIR ($mode_desc, max $MAX_WORKERS concurrent workers)"
    echo ""
    echo "Press Ctrl+C to stop and view 'wiggum status' for details"
    echo "=========================================="
    echo ""

    # Run initial scheduler tick and status display so the terminal shows
    # real data immediately, rather than waiting for the first post-phase cycle
    scheduler_tick
    SCHED_SCHEDULING_EVENT=true
    svc_orch_status_display
}

# =============================================================================
# Pre Phase Handlers (Phase 4)
# =============================================================================

# Consume persisted pool entries from subshells
svc_orch_pool_ingest() {
    pool_ingest_pending "$RALPH_DIR"
}

# Poll background resume-decide processes for completion
svc_orch_resume_poll() {
    _poll_pending_decides
}

# Run resume-decide analysis for stopped workers (Phase 1 of two-phase resume)
#
# Scans for stopped workers needing a decide phase, writes RETRY decisions
# for interrupted steps (fast path), and launches LLM analysis in background
# for completed steps. Decisions are picked up by svc_orch_task_spawner.
svc_orch_resume_decide() {
    local max_decide="${RESUME_MAX_DECIDE_CONCURRENT:-20}"
    _poll_pending_decides
    _recover_stranded_decisions

    local decide_count="${#_PENDING_DECIDES[@]}"
    local workers_needing_decide
    workers_needing_decide=$(get_workers_needing_decide "$RALPH_DIR")

    while read -r worker_dir task_id current_step worker_type; do
        [ -n "$worker_dir" ] || continue
        [ "$decide_count" -lt "$max_decide" ] || break

        # For interrupted steps, write decision inline (fast, no background)
        if [ -n "$current_step" ] && ! _step_has_result "$worker_dir" "$current_step"; then
            resume_state_increment "$worker_dir" "RETRY" "" "$current_step" \
                "Step interrupted, direct resume"
            if resume_state_max_exceeded "$worker_dir"; then
                update_kanban_failed "$RALPH_DIR/kanban.md" "$task_id" || true
                source "$WIGGUM_HOME/lib/github/issue-sync.sh"
                github_issue_sync_task_status "$RALPH_DIR" "$task_id" "*" || true
                resume_state_set_terminal "$worker_dir" "Max resume attempts exceeded (direct RETRY)"
                log_error "Task $task_id marked FAILED — max resume attempts exceeded at step $current_step"
                activity_log "worker.resume_failed" "$(basename "$worker_dir")" "$task_id" \
                    "reason=max_direct_retry step=$current_step"
                scheduler_mark_event
                continue
            fi
            jq -n --arg step "$current_step" '{
                decision: "RETRY",
                pipeline: null,
                resume_step: $step,
                reason: "Step interrupted, direct resume"
            }' > "$worker_dir/resume-decision.json"
            log "Direct RETRY decision for $task_id (interrupted at $current_step)"
            continue
        fi

        _launch_decide_background "$worker_dir" "$task_id" "$worker_type"
        ((++decide_count))
    done <<< "$workers_needing_decide"
}

# Reap finished workers and run completion callbacks
svc_orch_worker_cleanup() {
    pool_cleanup_finished "main" 0 _handle_main_worker_completion ""
    pool_cleanup_finished "fix" "$FIX_WORKER_TIMEOUT" _handle_fix_worker_completion _handle_fix_worker_timeout
    pool_cleanup_finished "resolve" "$RESOLVE_WORKER_TIMEOUT" _handle_resolve_worker_completion _handle_resolve_worker_timeout
}

# =============================================================================
# Post Phase Handlers (Phase 4)
# =============================================================================

# Ingest cleanup events persisted by pre-phase (Python mode cross-subprocess)
svc_orch_ingest_cleanup_event() {
    pool_ingest_cleanup_event "$RALPH_DIR"
}

# Check if all tasks are complete, write exit signal (throttled)
_ORCH_COMPLETION_INTERVAL=10
_ORCH_COMPLETION_LAST=0

svc_orch_check_completion() {
    local tick="${_ORCH_ITERATION:-0}"
    if [[ "${POOL_CLEANUP_EVENT:-false}" != "true" ]] \
        && [[ "${SCHED_SCHEDULING_EVENT:-false}" != "true" ]] \
        && (( tick - _ORCH_COMPLETION_LAST < _ORCH_COMPLETION_INTERVAL )); then
        return 0
    fi
    _ORCH_COMPLETION_LAST=$tick
    if scheduler_is_complete; then
        touch "$RALPH_DIR/orchestrator/should-exit"
    fi
}

# Check rate limits and pause if needed
svc_orch_rate_limit_guard() {
    if rate_limit_check "$RALPH_DIR"; then
        local cycle_prompts
        cycle_prompts=$(jq -r '.current_5h_cycle.total_prompts // 0' "$RALPH_DIR/orchestrator/claude-usage.json" 2>/dev/null)
        log "Rate limit threshold reached ($cycle_prompts >= $WIGGUM_RATE_LIMIT_THRESHOLD prompts in 5h cycle)"
        activity_log "rate_limit.detected" "" "" "prompts=$cycle_prompts threshold=$WIGGUM_RATE_LIMIT_THRESHOLD"
        rate_limit_wait_for_cycle_reset
        activity_log "rate_limit.resumed" "" ""
        usage_tracker_write_shared "$RALPH_DIR" > /dev/null 2>&1 || true
    fi
}

# Parse kanban and update scheduler state
svc_orch_scheduler_tick() {
    # Always run scheduler_tick — it rebuilds SCHED_UNIFIED_QUEUE which includes
    # resume candidates from worker directories (independent of kanban changes).
    # Kanban parsing is already cached internally by _get_cached_metadata().
    scheduler_tick
}

# Spawn workers for ready tasks and resume candidates from unified queue
svc_orch_task_spawner() {
    # Early exit: nothing to spawn if unified queue is empty
    # (populated by scheduler_tick in post phase order 30, before this at order 45)
    [[ -n "${SCHED_UNIFIED_QUEUE:-}" ]] || return 0

    local pending_main_count=0
    local pending_priority_count=0

    # Pre-flight: pull latest main once per cycle
    if ! pre_worker_checks; then
        log_error "Pre-worker git checks failed - skipping all spawns this cycle"
        return 0
    fi

    while IFS='|' read -r _pri work_type task_id worker_dir worker_type resume_step; do
        [ -n "$task_id" ] || continue

        # Run-mode filtering
        case "$WIGGUM_RUN_MODE" in
            default)     ;;  # allow all work types
            resume-only)
                [ "$work_type" = "resume" ] || continue
                ;;
            fix-only)
                if [ "$work_type" = "resume" ]; then
                    [[ "$worker_type" =~ ^(fix|resolve)$ ]] || continue
                else
                    continue  # no new tasks in fix-only mode
                fi
                ;;
            merge-only)
                if [ "$work_type" = "resume" ]; then
                    [ "$worker_type" = "resolve" ] || continue
                else
                    continue  # no new tasks in merge-only mode
                fi
                ;;
            *)  continue ;;
        esac

        # Capacity check (shared between new and resume)
        if [[ "$worker_type" =~ ^(fix|resolve)$ ]]; then
            local fix_count resolve_count total_priority
            fix_count=$(pool_count "fix")
            resolve_count=$(pool_count "resolve")
            total_priority=$((fix_count + resolve_count + pending_priority_count))
            if [ "$total_priority" -ge "$FIX_WORKER_LIMIT" ]; then
                continue  # skip this item, might have main-type items later
            fi
        else
            local main_count
            main_count=$(pool_count "main")
            if [ "$((main_count + pending_main_count))" -ge "$MAX_WORKERS" ]; then
                continue  # at main capacity, skip this item but process fix/resolve workers
            fi
        fi

        if [ "$work_type" = "new" ]; then
            # --- New task spawn logic ---

            if ! scheduler_can_spawn_task "$task_id" "$MAX_WORKERS"; then
                case "$SCHED_SKIP_REASON" in
                    at_capacity) continue ;;  # skip this main task, may have fix/resolve tasks later
                    file_conflict)
                        local -A _temp_workers=()
                        _build_workers() {
                            local pid="$1" type="$2" tid="$3"
                            [ "$type" = "main" ] && _temp_workers[$pid]="$tid"
                        }
                        pool_foreach "main" _build_workers
                        local conflicts
                        conflicts=$(get_conflicting_files "$RALPH_DIR" "$task_id" _temp_workers | tr '\n' ',' | sed 's/,$//')
                        log "Deferring $task_id - file conflict: $conflicts"
                        ;;
                    *) ;;
                esac
                continue
            fi

            local task_priority
            task_priority=$(echo "${_SCHED_TICK_METADATA:-}" | awk -F'|' -v t="$task_id" '$1 == t { print $3 }')
            task_priority="${task_priority:-MEDIUM}"

            log "Assigning $task_id (Priority: ${task_priority:-MEDIUM}) to new worker"
            if ! update_kanban_status "$RALPH_DIR/kanban.md" "$task_id" "="; then
                log_error "Failed to mark $task_id as in-progress"
                scheduler_increment_skip "$task_id"
                local skip_count
                skip_count=$(scheduler_get_skip_count "$task_id")
                log "Task $task_id skip count: $skip_count/$MAX_SKIP_RETRIES"
                if [ "$skip_count" -ge "$MAX_SKIP_RETRIES" ]; then
                    log_error "Task $task_id permanently skipped after $MAX_SKIP_RETRIES consecutive kanban failures"
                fi
                continue
            fi

            # Smart routing
            local _saved_pipeline="${WIGGUM_PIPELINE:-}"
            local _saved_plan_mode="${WIGGUM_PLAN_MODE:-false}"
            if [ "${WIGGUM_SMART_MODE:-false}" = "true" ]; then
                local _complexity _routing _rt_pipeline _rt_plan_mode
                _complexity=$(smart_assess_complexity "$RALPH_DIR/kanban.md" "$task_id")
                _routing=$(smart_get_routing "$_complexity")
                IFS='|' read -r _rt_pipeline _rt_plan_mode <<< "$_routing"
                export WIGGUM_PIPELINE="$_rt_pipeline"
                export WIGGUM_PLAN_MODE="$_rt_plan_mode"
                log "Smart routing: $task_id -> $_complexity (pipeline=${_rt_pipeline:-default}, plan=$_rt_plan_mode)"
            fi

            local spawn_rc=0
            spawn_worker "$task_id" || spawn_rc=$?
            if [ "$spawn_rc" -eq 2 ]; then
                # Deferred - worker exists and is resumable, revert kanban to pending
                update_kanban_status "$RALPH_DIR/kanban.md" "$task_id" " " || true
                export WIGGUM_PIPELINE="$_saved_pipeline"
                export WIGGUM_PLAN_MODE="$_saved_plan_mode"
                continue
            elif [ "$spawn_rc" -ne 0 ]; then
                log_error "Failed to spawn worker for $task_id"
                update_kanban_status "$RALPH_DIR/kanban.md" "$task_id" "*"
                source "$WIGGUM_HOME/lib/github/issue-sync.sh"
                github_issue_sync_task_status "$RALPH_DIR" "$task_id" "*" || true
                export WIGGUM_PIPELINE="$_saved_pipeline"
                export WIGGUM_PLAN_MODE="$_saved_plan_mode"
                continue
            fi

            export WIGGUM_PIPELINE="$_saved_pipeline"
            export WIGGUM_PLAN_MODE="$_saved_plan_mode"

            pool_add "$SPAWNED_WORKER_PID" "main" "$task_id"
            scheduler_mark_event
            scheduler_remove_from_aging "$task_id"
            audit_log_task_assigned "$task_id" "$SPAWNED_WORKER_ID" "$SPAWNED_WORKER_PID"
            log "Spawned worker $SPAWNED_WORKER_ID for $task_id (PID: $SPAWNED_WORKER_PID)"
            ((++pending_main_count))
        else
            # --- Resume task launch logic ---

            # Check task is still pending or in-progress
            local task_status
            task_status=$(get_task_status "$RALPH_DIR/kanban.md" "$task_id")
            case "$task_status" in
                " "|"=") ;;
                *)
                    log_debug "Skipping resume of $task_id - task status is '$task_status'"
                    continue
                    ;;
            esac

            # Mark as in-progress if pending
            if [ "$task_status" = " " ]; then
                if ! update_kanban_status "$RALPH_DIR/kanban.md" "$task_id" "="; then
                    log_error "Failed to mark $task_id as in-progress for resume"
                    continue
                fi
            fi

            log "Launching resume worker for $task_id (pipeline at: '$resume_step')"
            if _launch_resume_worker "$worker_dir" "$task_id"; then
                pool_add "$SPAWNED_WORKER_PID" "$worker_type" "$task_id"
                scheduler_mark_event
                audit_log_task_assigned "$task_id" "$SPAWNED_WORKER_ID" "$SPAWNED_WORKER_PID" 2>/dev/null || true
                log "Resumed worker $SPAWNED_WORKER_ID for $task_id (PID: $SPAWNED_WORKER_PID)"
                if [[ "$worker_type" =~ ^(fix|resolve)$ ]]; then
                    ((++pending_priority_count))
                else
                    ((++pending_main_count))
                fi
            else
                log_error "Failed to launch resume worker for $task_id"
            fi
        fi
    done <<< "$SCHED_UNIFIED_QUEUE"
}

# Detect orphan workers (interval-scheduled, every 60s)
svc_orch_orphan_detection() {
    scheduler_detect_orphan_workers
}

# Update aging tracking after scheduling events
svc_orch_aging_update() {
    scheduler_update_aging
}

# Log current orchestrator status
svc_orch_status_display() {
    if [ "$SCHED_SCHEDULING_EVENT" = true ]; then
        local cyclic_ref status_counts
        cyclic_ref=$(scheduler_get_cyclic_tasks_ref)
        status_counts=$(compute_status_counts "$SCHED_READY_TASKS" "$SCHED_BLOCKED_TASKS" "$cyclic_ref" "$RALPH_DIR")
        local _sc_ready _sc_blocked _sc_deferred _sc_cyclic _sc_errors _sc_stuck
        IFS='|' read -r _sc_ready _sc_blocked _sc_deferred _sc_cyclic _sc_errors _sc_stuck <<< "$status_counts"

        _log_detailed_status \
            "${_ORCH_ITERATION:-0}" \
            "$MAX_WORKERS" \
            "$SCHED_READY_TASKS" \
            "$SCHED_BLOCKED_TASKS" \
            "$cyclic_ref" \
            "$RALPH_DIR" \
            "$(scheduler_get_ready_since_file)" \
            "$AGING_FACTOR" \
            "$PLAN_BONUS" \
            "$DEP_BONUS_PER_TASK"

        log "[status] ready: $_sc_ready | blocked: $_sc_blocked | deferred: $_sc_deferred | errors: $_sc_errors"
    fi
}

# Persist service state to disk (throttled: only on dirty or every 10s)
_ORCH_LAST_STATE_SAVE=0

svc_orch_state_save() {
    local now="${_ORCH_TICK_EPOCH:-$(epoch_now)}"
    if [[ "${POOL_CLEANUP_EVENT:-false}" == "true" ]] \
        || [[ "${SCHED_SCHEDULING_EVENT:-false}" == "true" ]] \
        || (( now - _ORCH_LAST_STATE_SAVE >= 10 )); then
        service_state_save 2>/dev/null || true
        _ORCH_LAST_STATE_SAVE=$now
    fi
}

# =============================================================================
# Shutdown Phase Handlers (Phase 5)
# =============================================================================

# Terminal cleanup (no-op, terminal header removed)
svc_orch_terminal_cleanup() {
    true
}

# Remove orchestrator lock file on shutdown
svc_orch_lock_cleanup() {
    _release_lock
}

# =============================================================================
# Distributed Mode Service Handlers
# =============================================================================

# Update heartbeats for claimed tasks (distributed mode only)
svc_orch_distributed_heartbeat() {
    # Only run in distributed modes
    [[ "${WIGGUM_TASK_SOURCE_MODE:-local}" == "local" ]] && return 0

    scheduler_update_heartbeats
}

# Run orphan recovery scan (distributed mode only)
svc_orch_distributed_orphan_recovery() {
    # Only run in distributed modes
    [[ "${WIGGUM_TASK_SOURCE_MODE:-local}" == "local" ]] && return 0

    scheduler_run_orphan_recovery
}

# Clean shutdown of distributed components
svc_orch_distributed_shutdown() {
    # Only run in distributed modes
    [[ "${WIGGUM_TASK_SOURCE_MODE:-local}" == "local" ]] && return 0

    scheduler_shutdown_distributed
}
