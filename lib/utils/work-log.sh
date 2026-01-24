#!/usr/bin/env bash
# =============================================================================
# work-log.sh - Structured markdown work logs per iteration
#
# Creates human-readable markdown files documenting each iteration's work,
# namespaced per run using RALPH_RUN_ID:
#   work-log/{run_id}/index.md         - Links to all iterations in this run
#   work-log/{run_id}/iteration-N.md   - Per-iteration structured log
#
# Provides:
#   work_log_init(output_dir)
#   work_log_write_iteration(output_dir, iteration, session_id, exit_code, summary_text, log_file)
# =============================================================================

# Prevent double-sourcing
[ -n "${_WORK_LOG_LOADED:-}" ] && return 0
_WORK_LOG_LOADED=1

# Initialize work log directory structure
#
# Args:
#   output_dir - Worker output directory (contains logs/, summaries/, etc.)
#
# Uses RALPH_RUN_ID env var to namespace work logs per run.
#
# Returns: 0 on success
work_log_init() {
    local output_dir="$1"
    local run_id="${RALPH_RUN_ID:-default}"
    local log_dir="$output_dir/work-log/$run_id"

    mkdir -p "$log_dir"

    # Create index.md for this run
    cat > "$log_dir/index.md" << EOF
# Work Log: $run_id

| Iteration | Timestamp | Exit Code | Summary |
|-----------|-----------|-----------|---------|
EOF
}

# Write a per-iteration markdown log file
#
# Args:
#   output_dir   - Worker output directory
#   iteration    - Iteration number (0-based)
#   session_id   - Claude session ID
#   exit_code    - Exit code from work phase
#   summary_text - Extracted summary text (can be multi-line)
#   log_file     - Path to the iteration log file (for extracting file changes)
#
# Returns: 0 on success
work_log_write_iteration() {
    local output_dir="$1"
    local iteration="$2"
    local session_id="$3"
    local exit_code="$4"
    local summary_text="$5"
    local log_file="${6:-}"

    local run_id="${RALPH_RUN_ID:-default}"
    local log_dir="$output_dir/work-log/$run_id"
    local iter_file="$log_dir/iteration-${iteration}.md"
    local timestamp
    timestamp=$(date -Iseconds)

    # Extract sections from summary text
    local context="" decisions="" pending="" current_work="" outcome=""

    if [ -n "$summary_text" ]; then
        # Extract Key Technical Concepts / Primary Request section as context
        context=$(echo "$summary_text" | sed -n '/^## *\(Primary Request\|Key Technical\)/,/^## /{ /^## *\(Primary Request\|Key Technical\)/d; /^## /d; p; }' | head -20)
        [ -z "$context" ] && context=$(echo "$summary_text" | head -5)

        # Extract Problem Solving section as decisions
        decisions=$(echo "$summary_text" | sed -n '/^## *\(Problem Solving\|Decisions\)/,/^## /{ /^## /d; p; }' | head -15)

        # Extract Pending Tasks
        pending=$(echo "$summary_text" | sed -n '/^## *Pending/,/^## /{ /^## /d; p; }' | head -10)

        # Extract Current Work
        current_work=$(echo "$summary_text" | sed -n '/^## *Current Work/,/^## /{ /^## /d; p; }' | head -10)

        # Determine outcome
        if [ "$exit_code" -eq 0 ]; then
            outcome="Completed successfully"
        elif [ "$exit_code" -eq 130 ] || [ "$exit_code" -eq 143 ]; then
            outcome="Interrupted by signal (exit code: $exit_code)"
        else
            outcome="Completed with errors (exit code: $exit_code)"
        fi
    fi

    # Extract files changed from log file if available
    local files_changed=""
    if [ -n "$log_file" ] && [ -f "$log_file" ]; then
        files_changed=$(grep -oP '"file_path"\s*:\s*"\K[^"]+' "$log_file" 2>/dev/null | sort -u | head -20)
    fi

    # Write iteration markdown
    {
        echo "# Iteration $iteration"
        echo ""
        echo "**Timestamp:** $timestamp"
        echo "**Session:** $session_id"
        echo "**Exit Code:** $exit_code"
        echo ""

        echo "## Context"
        if [ -n "$context" ]; then
            echo "$context"
        else
            echo "_No context extracted_"
        fi
        echo ""

        echo "## Decisions"
        if [ -n "$decisions" ]; then
            echo "$decisions"
        else
            echo "_No decisions recorded_"
        fi
        echo ""

        echo "## Files Changed"
        if [ -n "$files_changed" ]; then
            echo "$files_changed" | while read -r f; do
                echo "- \`$f\`"
            done
        else
            echo "_No file changes detected_"
        fi
        echo ""

        echo "## Errors Encountered"
        if [ "$exit_code" -ne 0 ]; then
            echo "- Exit code: $exit_code"
            if [ "$exit_code" -eq 130 ] || [ "$exit_code" -eq 143 ]; then
                echo "- Interrupted by signal"
            fi
        else
            echo "_None_"
        fi
        echo ""

        echo "## Outcome"
        echo "$outcome"
        if [ -n "$current_work" ]; then
            echo ""
            echo "### Current State"
            echo "$current_work"
        fi
        if [ -n "$pending" ]; then
            echo ""
            echo "### Pending"
            echo "$pending"
        fi
        echo ""

        echo "---"
        # Navigation links
        if [ "$iteration" -gt 0 ]; then
            echo -n "[Previous](iteration-$((iteration - 1)).md)"
        fi
        echo " | [Next](iteration-$((iteration + 1)).md)"
    } > "$iter_file"

    # Update index.md with link to this iteration
    local short_summary
    short_summary=$(echo "$context" | head -1 | cut -c1-60)
    [ -z "$short_summary" ] && short_summary="Iteration $iteration"
    echo "| [$iteration](iteration-${iteration}.md) | $timestamp | $exit_code | $short_summary |" >> "$log_dir/index.md"
}
