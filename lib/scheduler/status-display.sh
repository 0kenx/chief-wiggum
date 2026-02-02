#!/usr/bin/env bash
# status-display.sh - Orchestrator status output formatting
#
# Provides:
#   compute_status_counts()  - Returns pipe-delimited status counts for header
#   _log_detailed_status()   - Logs detailed status to LOG_FILE via log_debug
#   display_final_summary()  - Final summary after orchestration completes
#
# shellcheck disable=SC2329  # Functions are invoked indirectly via callbacks
set -euo pipefail

[ -n "${_STATUS_DISPLAY_LOADED:-}" ] && return 0
_STATUS_DISPLAY_LOADED=1
source "$WIGGUM_HOME/lib/core/platform.sh"

# Source dependencies
source "$WIGGUM_HOME/lib/scheduler/worker-pool.sh"
source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"
source "$WIGGUM_HOME/lib/tasks/task-parser.sh"
source "$WIGGUM_HOME/lib/tasks/conflict-detection.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"

# Compute status counts for the terminal header
#
# Returns pipe-delimited string: ready|blocked|deferred|cyclic|errors|stuck
# Extracts count-only logic without any display output.
#
# Args:
#   ready_tasks      - Space-separated list of ready task IDs
#   blocked_tasks    - Space-separated list of blocked task IDs
#   cyclic_tasks_ref - Name of associative array containing cyclic task IDs
#   ralph_dir        - Ralph directory path
#
# Outputs: "ready|blocked|deferred|cyclic|errors|stuck"
compute_status_counts() {
    local ready_tasks="$1"
    local blocked_tasks="$2"
    local -n _csc_cyclic_ref="$3"
    local ralph_dir="$4"

    local ready_count=0 blocked_count=0 deferred_count=0 cyclic_count=0 error_count=0 stuck_count=0

    # Build PID->task_id map for file conflict checking (once)
    local -A _csc_workers=()
    _csc_build_workers() {
        local pid="$1" type="$2" task_id="$3"
        [[ "$type" == "main" ]] && _csc_workers[$pid]="$task_id"
    }
    pool_foreach "main" _csc_build_workers

    # --- Deferred (file conflict) count ---
    local task_id
    for task_id in $ready_tasks; do
        if has_file_conflict "$ralph_dir" "$task_id" _csc_workers; then
            ((++deferred_count)) || true
        fi
    done

    # --- Ready count (minus deferred; in-progress already excluded by get_ready_tasks) ---
    if [[ -n "$ready_tasks" ]]; then
        ready_count=$(echo "$ready_tasks" | wc -w)
        ready_count=$((ready_count))  # trim whitespace from wc
        ready_count=$((ready_count - deferred_count))
        [[ "$ready_count" -lt 0 ]] && ready_count=0
    fi

    # --- Blocked count (re-validated against race conditions) ---
    if [[ -n "$blocked_tasks" ]]; then
        for task_id in $blocked_tasks; do
            if ! are_dependencies_satisfied "$ralph_dir/kanban.md" "$task_id"; then
                ((++blocked_count)) || true
            fi
        done
    fi

    # --- Cyclic count ---
    cyclic_count=${#_csc_cyclic_ref[@]}

    # --- Error count (time-filtered from workers.log) ---
    if [[ -f "$ralph_dir/logs/workers.log" ]]; then
        local error_max_age="${ERROR_LOG_MAX_AGE:-3600}"
        local cutoff_time
        cutoff_time=$(iso_from_epoch "$(($(epoch_now) - error_max_age))" 2>/dev/null || \
                      date -v-"${error_max_age}"S -Iseconds 2>/dev/null || \
                      echo "")

        local error_lines=""
        error_lines=$(grep -i "ERROR\|WARN" "$ralph_dir/logs/workers.log" 2>/dev/null || true)

        if [[ -n "$error_lines" && -n "$cutoff_time" ]]; then
            error_count=$(echo "$error_lines" | awk -v cutoff="$cutoff_time" '{
                    if (match($0, /\[[0-9T:+-]+\]/)) {
                        ts = substr($0, RSTART+1, RLENGTH-2)
                        if (ts >= cutoff) count++
                    }
                } END { print count+0 }')
        elif [[ -n "$error_lines" ]]; then
            error_count=$(echo "$error_lines" | wc -l)
            error_count=$((error_count))  # trim whitespace
        fi
    fi

    # --- Stuck count (activity idle threshold) ---
    local now_ts stuck_threshold
    now_ts=$(epoch_now)
    stuck_threshold="${STUCK_WORKER_THRESHOLD:-1800}"
    if [[ "$stuck_threshold" -gt 0 ]]; then
        _csc_check_stuck() {
            local pid="$1" type="$2" task_id="$3"
            [[ "$type" == "main" ]] || return 0
            local worker_dir
            worker_dir=$(find_worker_by_task_id "$ralph_dir" "$task_id" 2>/dev/null || true)
            [[ -n "$worker_dir" ]] || return 0
            local activity_file="$worker_dir/activity.jsonl"
            if [[ -f "$activity_file" ]]; then
                local last_activity
                last_activity=$(stat -c %Y "$activity_file" 2>/dev/null || stat -f %m "$activity_file" 2>/dev/null || echo "$now_ts")
                local idle_time=$((now_ts - last_activity))
                if [[ "$idle_time" -ge "$stuck_threshold" ]]; then
                    ((++stuck_count)) || true
                fi
            fi
        }
        pool_foreach "main" _csc_check_stuck
    fi

    echo "${ready_count}|${blocked_count}|${deferred_count}|${cyclic_count}|${error_count}|${stuck_count}"
}

# Log detailed orchestrator status via log_debug
#
# All output goes to LOG_FILE + stderr (not stdout/scroll region).
# Visible via WIGGUM_LOG_LEVEL=debug or in orchestrator.log.
#
# Args:
#   iteration         - Current iteration number
#   max_workers       - Maximum workers allowed
#   ready_tasks       - Space-separated list of ready task IDs
#   blocked_tasks     - Space-separated list of blocked task IDs
#   cyclic_tasks_ref  - Name of associative array containing cyclic task IDs
#   ralph_dir         - Ralph directory path
#   ready_since_file  - Path to ready-since tracking file
#   aging_factor      - Aging factor for priority calculation
#   plan_bonus        - Plan bonus for priority calculation
#   dep_bonus_per_task - Dependency bonus per task
#
# Uses: _WORKER_POOL from worker-pool.sh
_log_detailed_status() {
    local iteration="$1"
    local max_workers="$2"
    local ready_tasks="$3"
    local blocked_tasks="$4"
    local -n _cyclic_tasks_ref="$5"
    local ralph_dir="$6"
    local ready_since_file="$7"
    local aging_factor="$8"
    local plan_bonus="$9"
    local dep_bonus_per_task="${10}"

    local main_count fix_count resolve_count
    main_count=$(pool_count "main")
    fix_count=$(pool_count "fix")
    resolve_count=$(pool_count "resolve")

    log_debug ""
    log_debug "=== Status Update (iteration $iteration) ==="
    log_debug "Active workers: $main_count/$max_workers"

    # Show which tasks are being worked on (main workers)
    if [ "$main_count" -gt 0 ]; then
        log_debug "In Progress:"
        local now_ts stuck_threshold
        now_ts=$(epoch_now)
        stuck_threshold="${STUCK_WORKER_THRESHOLD:-1800}"

        _display_workers_callback() {
            local pid="$1" type="$2" task_id="$3" start_time="$4"
            if [ "$type" = "main" ]; then
                local status_suffix=""
                local worker_dir
                worker_dir=$(find_worker_by_task_id "$ralph_dir" "$task_id" 2>/dev/null || true)

                # Check for stuck worker: no activity file update for threshold seconds
                if [ -n "$worker_dir" ] && [ "$stuck_threshold" -gt 0 ]; then
                    local activity_file="$worker_dir/activity.jsonl"
                    if [ -f "$activity_file" ]; then
                        local last_activity
                        last_activity=$(stat -c %Y "$activity_file" 2>/dev/null || stat -f %m "$activity_file" 2>/dev/null || echo "$now_ts")
                        local idle_time=$((now_ts - last_activity))
                        if [ "$idle_time" -ge "$stuck_threshold" ]; then
                            status_suffix=" [STUCK: ${idle_time}s idle]"
                        fi
                    fi
                fi

                log_debug "  - $task_id (PID: $pid)$status_suffix"
            fi
        }
        pool_foreach "main" _display_workers_callback
    fi

    # Show active fix workers
    if [ "$fix_count" -gt 0 ]; then
        log_debug "Fix Workers:"
        local now
        now=$(epoch_now)
        _display_fix_callback() {
            local pid="$1" type="$2" task_id="$3" start_time="$4"
            local elapsed=$((now - start_time))
            log_debug "  - $task_id (PID: $pid, ${elapsed}s elapsed)"
        }
        pool_foreach "fix" _display_fix_callback
    fi

    # Show active resolve workers
    if [ "$resolve_count" -gt 0 ]; then
        log_debug "Resolve Workers:"
        local now
        now=$(epoch_now)
        _display_resolve_callback() {
            local pid="$1" type="$2" task_id="$3" start_time="$4"
            local elapsed=$((now - start_time))
            log_debug "  - $task_id (PID: $pid, ${elapsed}s elapsed)"
        }
        pool_foreach "resolve" _display_resolve_callback
    fi

    # Show blocked tasks waiting on dependencies
    if [ -n "$blocked_tasks" ]; then
        local has_blocked=false
        local blocked_output=""
        local task_id
        for task_id in $blocked_tasks; do
            # Re-validate that task is still blocked (handles race with concurrent completions)
            if ! are_dependencies_satisfied "$ralph_dir/kanban.md" "$task_id"; then
                local waiting_on
                waiting_on=$(get_unsatisfied_dependencies "$ralph_dir/kanban.md" "$task_id" | tr '\n' ',' | sed 's/,$//')
                # Skip if empty (race condition: deps completed between checks)
                if [ -n "$waiting_on" ]; then
                    blocked_output+="  - $task_id (waiting on: $waiting_on)"$'\n'
                    has_blocked=true
                fi
            fi
        done
        if [ "$has_blocked" = true ]; then
            log_debug "Blocked (waiting on dependencies):"
            log_debug "$blocked_output"
        fi
    fi

    # Show tasks skipped due to dependency cycles
    if [ ${#_cyclic_tasks_ref[@]} -gt 0 ]; then
        log_debug "Skipped (dependency cycle):"
        local task_id
        for task_id in "${!_cyclic_tasks_ref[@]}"; do
            local error_type="${_cyclic_tasks_ref[$task_id]}"
            if [ "$error_type" = "SELF" ]; then
                log_debug "  - $task_id (self-dependency)"
            else
                log_debug "  - $task_id (circular dependency)"
            fi
        done
    fi

    # Build list of active task IDs for conflict checking
    local -A active_task_ids=()
    _collect_active_tasks() {
        local pid="$1" type="$2" task_id="$3"
        if [ "$type" = "main" ]; then
            active_task_ids[$task_id]=1
        fi
    }
    pool_foreach "main" _collect_active_tasks

    # Show tasks deferred due to file conflicts
    local deferred_conflicts=()
    local task_id
    for task_id in $ready_tasks; do
        # Create a temporary associative array in the format expected by has_file_conflict
        # has_file_conflict expects: PID -> task_id mapping
        local -A _temp_workers=()
        _build_temp_workers() {
            local pid="$1" type="$2" task_id="$3"
            if [ "$type" = "main" ]; then
                _temp_workers[$pid]="$task_id"
            fi
        }
        pool_foreach "main" _build_temp_workers

        if has_file_conflict "$ralph_dir" "$task_id" _temp_workers; then
            deferred_conflicts+=("$task_id")
        fi
    done

    if [ ${#deferred_conflicts[@]} -gt 0 ]; then
        log_debug "Deferred (file conflict):"
        for task_id in "${deferred_conflicts[@]}"; do
            local -A _temp_workers=()
            _build_temp_workers_for_conflict() {
                local pid="$1" type="$2" tid="$3"
                if [ "$type" = "main" ]; then
                    _temp_workers[$pid]="$tid"
                fi
            }
            pool_foreach "main" _build_temp_workers_for_conflict

            local conflicting_tasks
            conflicting_tasks=$(get_conflicting_tasks "$ralph_dir" "$task_id" _temp_workers | tr '\n' ',' | sed 's/,$//')
            log_debug "  - $task_id (conflicts with: $conflicting_tasks)"
        done
    fi

    # Show top 7 ready tasks with priority scores (excluding in-progress and deferred)
    local ready_count
    ready_count=$(echo "$ready_tasks" | grep -c . 2>/dev/null || true)
    ready_count=${ready_count:-0}

    # Subtract deferred tasks from count (in-progress tasks already excluded by get_ready_tasks)
    ready_count=$((ready_count - ${#deferred_conflicts[@]}))

    if [ "$ready_count" -gt 0 ]; then
        log_debug "Ready ($ready_count tasks, top 7 by priority):"

        # Get priority scores for display
        local all_metadata
        all_metadata=$(get_all_tasks_with_metadata "$ralph_dir/kanban.md")

        local display_count=0
        for task_id in $ready_tasks; do
            [ "$display_count" -ge 7 ] && break

            # Skip in-progress tasks
            if [ -n "${active_task_ids[$task_id]+x}" ]; then
                continue
            fi

            # Skip deferred tasks
            local is_deferred=false
            local deferred
            for deferred in "${deferred_conflicts[@]}"; do
                if [ "$task_id" = "$deferred" ]; then
                    is_deferred=true
                    break
                fi
            done
            [ "$is_deferred" = true ] && continue

            local priority iters_waiting effective_pri
            priority=$(echo "$all_metadata" | awk -F'|' -v t="$task_id" '$1 == t { print $3 }')
            iters_waiting=$(awk -F'|' -v t="$task_id" '$1 == t { print $2 }' "$ready_since_file" 2>/dev/null)
            iters_waiting=${iters_waiting:-0}
            effective_pri=$(get_effective_priority "$priority" "$iters_waiting" "$aging_factor")

            # Apply plan bonus
            if task_has_plan "$ralph_dir" "$task_id"; then
                effective_pri=$((effective_pri - plan_bonus))
            fi

            # Apply dep bonus
            local dep_depth
            dep_depth=$(get_dependency_depth "$ralph_dir/kanban.md" "$task_id")
            effective_pri=$((effective_pri - dep_depth * dep_bonus_per_task))
            [[ "$effective_pri" -lt 0 ]] && effective_pri=0 || true

            log_debug "  - $task_id (score: $effective_pri)"
            ((++display_count))
        done
    fi

    # Show recent errors only (not info), filtered by age
    if [ -f "$ralph_dir/logs/workers.log" ]; then
        local recent_errors cutoff_time
        local error_max_age="${ERROR_LOG_MAX_AGE:-3600}"

        # Calculate cutoff timestamp (now - max_age)
        cutoff_time=$(iso_from_epoch "$(($(epoch_now) - error_max_age))" 2>/dev/null || \
                      date -v-"${error_max_age}"S -Iseconds 2>/dev/null || \
                      echo "")

        local error_lines=""
        error_lines=$(grep -i "ERROR\|WARN" "$ralph_dir/logs/workers.log" 2>/dev/null || true)

        if [[ -n "$error_lines" && -n "$cutoff_time" ]]; then
            recent_errors=$(echo "$error_lines" | awk -v cutoff="$cutoff_time" '{
                    if (match($0, /\[[0-9T:+-]+\]/)) {
                        ts = substr($0, RSTART+1, RLENGTH-2)
                        if (ts >= cutoff) print
                    }
                }' | tail -n 5)
        elif [[ -n "$error_lines" ]]; then
            recent_errors=$(echo "$error_lines" | tail -n 5)
        else
            recent_errors=""
        fi

        if [ -n "$recent_errors" ]; then
            log_debug ""
            log_debug "Recent errors:"
            log_debug "$recent_errors"
        fi
    fi

    log_debug "=========================================="
}

# Display final summary when orchestration completes
#
# Args:
#   ralph_dir - Ralph directory path
display_final_summary() {
    local ralph_dir="$1"

    echo ""
    echo "=========================================="
    log "Chief Wiggum finished - all tasks complete!"
    echo ""

    # Show final summary
    local completed_count
    completed_count=$(grep -c '^\- \[x\]' "$ralph_dir/kanban.md" 2>/dev/null) || completed_count=0

    echo "Summary:"
    echo "  - Total tasks completed: $completed_count"
    echo "  - Changelog: .ralph/changelog.md"
    echo ""
    echo "Next steps:"
    echo "  - Review completed work: wiggum pr list"
    echo "  - Merge PRs: wiggum pr merge-all"
    echo "  - Clean up: wiggum clean"
    echo ""
}
