#!/usr/bin/env bash
# worker-complete.sh - Worker self-completion module
#
# Lightweight module sourced by worker setsid subprocesses after run_agent
# completes. Reads pipeline results and emits lifecycle events directly,
# removing the dependency on the orchestrator for state transitions.
#
# This ensures workers self-manage their lifecycle state even if the
# orchestrator is not running when the pipeline finishes.
#
# Provides: worker_complete_fix()
# Sourced by: cmd-fix.sh, cmd-resume.sh (inside setsid blocks)
set -euo pipefail

[ -n "${_WORKER_COMPLETE_LOADED:-}" ] && return 0
_WORKER_COMPLETE_LOADED=1

# Self-complete a fix worker after its pipeline finishes
#
# Mirrors the logic of handle_fix_worker_completion in fix-workers.sh:
# reads the latest result file, determines gate_result and push_succeeded,
# then emits the appropriate lifecycle event (fix.pass, fix.fail, etc.).
#
# This must be called BEFORE the EXIT trap removes agent.pid, so the
# orchestrator sees a transitioned state instead of a dead "fixing" worker.
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier
#
# Returns: 0 always (errors are logged but never propagated)
# shellcheck disable=SC2034  # task_id passed for API consistency; lifecycle-engine resolves it from worker_dir
worker_complete_fix() {
    local worker_dir="$1"
    local task_id="$2"

    # Guard: only self-complete from "fixing" state
    local current_state
    current_state=$(jq -r '.current_state // "none"' "$worker_dir/git-state.json" 2>/dev/null) || current_state="none"
    if [[ "$current_state" != "fixing" ]]; then
        return 0
    fi

    # Load lifecycle engine (pulls in loader, git-state, guards)
    source "$WIGGUM_HOME/lib/core/lifecycle-engine.sh"
    lifecycle_is_loaded || lifecycle_load

    # Find the fix pipeline result.
    #
    # Priority order (highest signal first):
    #   1. task-worker result — contains the pipeline-level gate_result which
    #      reflects the FINAL pipeline outcome (e.g. test-run FAIL → abort →
    #      gate_result=FIX). This is the most accurate signal.
    #   2. test-run result — if the pipeline ran a test step after pr-fix,
    #      its result overrides pr-fix because tests are a later gate.
    #   3. pr-fix result — only used when no later pipeline step ran.
    #   4. newest result with gate_result — generic fallback.
    local result_file=""
    local gate_result="FAIL"
    local push_succeeded="false"

    if [ -d "$worker_dir/results" ]; then
        # 1. Prefer task-worker result (pipeline-level outcome)
        result_file=$(find "$worker_dir/results" -maxdepth 1 -name "*-system.task-worker-result.json" -type f 2>/dev/null | sort -r | head -1)

        # 2. Fall back to test-run result (later gate than pr-fix)
        if [ -z "$result_file" ]; then
            result_file=$(find "$worker_dir/results" -maxdepth 1 -name "*-test-run-result.json" -type f 2>/dev/null | sort -r | head -1)
        fi

        # 3. Fall back to pr-fix result
        if [ -z "$result_file" ]; then
            result_file=$(find "$worker_dir/results" -maxdepth 1 -name "*-pr-fix-result.json" -type f 2>/dev/null | sort -r | head -1)
        fi

        # 4. Generic fallback: newest result with gate_result field
        if [ -z "$result_file" ]; then
            local candidate
            while read -r candidate; do
                [ -f "$candidate" ] || continue
                if jq -e '.outputs.gate_result // .gate_result' "$candidate" &>/dev/null; then
                    result_file="$candidate"
                    break
                fi
            done < <(find "$worker_dir/results" -maxdepth 1 -name "*-result.json" -type f 2>/dev/null | sort -r)
        fi
    fi

    if [ -z "$result_file" ]; then
        # No result file means the pipeline didn't produce output.
        # Emit timeout so state resets to needs_fix for retry.
        emit_event "$worker_dir" "fix.timeout" "worker-complete.worker_complete_fix" || true
        return 0
    fi

    gate_result=$(jq -r '.outputs.gate_result // .gate_result // "FAIL"' "$result_file" 2>/dev/null) || gate_result="FAIL"
    push_succeeded=$(jq -r '.outputs.push_succeeded // "false"' "$result_file" 2>/dev/null) || push_succeeded="false"

    # If chosen result didn't report push success, check pr-fix and commit-push
    if [ "$push_succeeded" != "true" ] && [ -d "$worker_dir/results" ]; then
        local pr_fix_result
        pr_fix_result=$(find "$worker_dir/results" -maxdepth 1 -name "*-pr-fix-result.json" -type f 2>/dev/null | sort -r | head -1)
        if [ -n "$pr_fix_result" ] && [ -f "$pr_fix_result" ]; then
            local pr_push
            pr_push=$(jq -r '.outputs.push_succeeded // "false"' "$pr_fix_result" 2>/dev/null) || pr_push="false"
            if [ "$pr_push" = "true" ]; then
                push_succeeded="true"
            fi
        fi

        if [ "$push_succeeded" != "true" ]; then
            local commit_push_result
            commit_push_result=$(find "$worker_dir/results" -maxdepth 1 -name "*-commit-push-result.json" -type f 2>/dev/null | sort -r | head -1)
            if [ -n "$commit_push_result" ] && [ -f "$commit_push_result" ]; then
                local push_status
                push_status=$(jq -r '.outputs.push_status // .push_status // ""' "$commit_push_result" 2>/dev/null) || push_status=""
                if [ "$push_status" = "success" ]; then
                    push_succeeded="true"
                fi
            fi
        fi
    fi

    # Emit the appropriate lifecycle event
    local event=""
    case "$gate_result" in
        PASS)
            event="fix.pass"
            ;;
        SKIP)
            event="fix.skip"
            ;;
        FIX)
            event="fix.partial"
            ;;
        *)
            event="fix.fail"
            ;;
    esac

    emit_event "$worker_dir" "$event" "worker-complete.worker_complete_fix" || true

    return 0
}
