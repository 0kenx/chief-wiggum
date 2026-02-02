#!/usr/bin/env bash
# lib/worker/cmd-merge.sh - Merge command logic for wiggum worker
#
# Provides: do_start_merge()
# Sourced by: bin/wiggum-worker

[ -n "${_CMD_MERGE_LOADED:-}" ] && return 0
_CMD_MERGE_LOADED=1

source "$WIGGUM_HOME/lib/core/exit-codes.sh"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/tasks/task-parser.sh"
source "$WIGGUM_HOME/lib/worker/worker-lifecycle.sh"
source "$WIGGUM_HOME/lib/worker/git-state.sh"
source "$WIGGUM_HOME/lib/scheduler/merge-manager.sh"

# Output message respecting quiet mode
_msg() {
    [ "$QUIET_MODE" = "true" ] || echo "$@"
}

# Attempt to merge a task's PR (synchronous)
#
# Uses outer-scope: PROJECT_DIR, RALPH_DIR, WIGGUM_HOME, QUIET_MODE
#
# Args:
#   input_id - Task ID (partial or full)
do_start_merge() {
    local input_id="$1"

    # Check .ralph directory exists
    if [ ! -d "$RALPH_DIR" ]; then
        echo "Error: No .ralph directory found. Run 'wiggum init' first."
        exit $EXIT_WORKER_NO_RALPH_DIR
    fi

    if [ -z "$input_id" ]; then
        echo "Error: Task ID required"
        echo "Usage: wiggum worker merge <TASK-ID>"
        exit $EXIT_USAGE
    fi

    # Check if kanban exists
    if [ ! -f "$RALPH_DIR/kanban.md" ]; then
        echo "Error: No kanban.md found at $RALPH_DIR/kanban.md"
        exit $EXIT_WORKER_NO_KANBAN
    fi

    # Resolve partial task ID to full task ID
    local task_id
    task_id=$(resolve_task_id "$RALPH_DIR/kanban.md" "$input_id") || exit $EXIT_WORKER_TASK_NOT_FOUND

    # Find existing worker directory for this task
    local worker_dir
    worker_dir=$(find_worker_by_task_id "$RALPH_DIR" "$task_id")

    if [ -z "$worker_dir" ] || [ ! -d "$worker_dir" ]; then
        echo "Error: No worker directory found for $task_id"
        echo "A worker must exist before merging. Use 'wiggum worker start $task_id' first."
        exit $EXIT_ERROR
    fi

    # Get PR number from git-state.json
    local pr_number
    pr_number=$(git_state_get_pr "$worker_dir")

    # Fallback: discover PR from workspace branch
    if [ "$pr_number" = "null" ] || [ -z "$pr_number" ]; then
        if [ -d "$worker_dir/workspace" ]; then
            local branch
            branch=$(git -C "$worker_dir/workspace" rev-parse --abbrev-ref HEAD 2>/dev/null || true)
            if [ -n "$branch" ] && [ "$branch" != "HEAD" ]; then
                pr_number=$(gh pr list --head "$branch" --state open --json number -q '.[0].number' 2>/dev/null || true)
                if [ -n "$pr_number" ]; then
                    git_state_set_pr "$worker_dir" "$pr_number"
                fi
            fi
        fi
    fi

    if [ -z "$pr_number" ] || [ "$pr_number" = "null" ]; then
        echo "Error: No PR found for $task_id"
        echo "Ensure the worker has created a PR first."
        exit $EXIT_ERROR
    fi

    _msg "Attempting to merge PR #$pr_number for $task_id..."

    # Set state to needs_merge
    git_state_set "$worker_dir" "needs_merge" "wiggum-worker.do_start_merge" "Manual merge via 'wiggum worker merge $task_id'"

    # Attempt merge (synchronous)
    local merge_result=0
    attempt_pr_merge "$worker_dir" "$task_id" "$RALPH_DIR" || merge_result=$?

    case $merge_result in
        0)
            _msg "PR #$pr_number merged successfully for $task_id"
            ;;
        1)
            echo "Merge conflict for $task_id (PR #$pr_number)"
            echo "Resolve conflicts with: wiggum pr resolve $task_id"
            exit 1
            ;;
        *)
            local last_error
            last_error=$(git_state_get_error "$worker_dir")
            echo "Merge failed for $task_id (PR #$pr_number)"
            if [ "$last_error" != "null" ] && [ -n "$last_error" ]; then
                echo "Error: $last_error"
            fi
            exit 2
            ;;
    esac
}
