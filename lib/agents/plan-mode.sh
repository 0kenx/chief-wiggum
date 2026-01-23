#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: plan-mode
# AGENT_DESCRIPTION: Creates implementation plans stored in .ralph/plans/TASK-xxx.md.
#   Operates in READ-ONLY mode, exploring the codebase to understand existing patterns
#   and design an implementation approach. Uses Glob, Grep, Read for exploration.
#   Output format includes Overview, Requirements Analysis, Existing Patterns,
#   Implementation Approach, Dependencies, Challenges, and Critical Files sections.
# REQUIRED_PATHS:
#   - prd.md : Product Requirements Document containing task to plan
# OUTPUT_FILES:
#   - .ralph/plans/TASK-xxx.md : The generated implementation plan (TASK-xxx from input)
#   - plan-result.txt          : Contains PASS or FAIL
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "plan-mode" "Creates implementation plans stored in .ralph/plans/TASK-xxx.md"

# Required paths before agent can run
agent_required_paths() {
    echo "prd.md"
}

# Source dependencies using base library helpers
agent_source_core
agent_source_ralph

# Source exit codes for standardized returns
source "$WIGGUM_HOME/lib/core/exit-codes.sh"

# Main entry point - creates implementation plan
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    local max_iterations="${3:-${AGENT_CONFIG_MAX_ITERATIONS:-5}}"
    local max_turns="${4:-${AGENT_CONFIG_MAX_TURNS:-30}}"

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

    log "Plan-mode agent starting for $task_id (max $max_turns turns per session)"

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Ensure plans directory exists
    mkdir -p "$project_dir/.ralph/plans"

    # === EXECUTION PHASE ===
    # Set up callback context using base library
    # Note: No worktree - we use project_dir directly (read-only access)
    agent_setup_context "$worker_dir" "$project_dir" "$project_dir" "$task_id"
    _PLAN_PRD_FILE="$prd_file"
    _PLAN_TASK_ID="$task_id"
    _PLAN_OUTPUT_FILE=".ralph/plans/${task_id}.md"

    # Run planning loop (operates on project_dir, not a worktree)
    run_ralph_loop "$project_dir" \
        "$(_get_system_prompt "$project_dir" "$task_id")" \
        "_plan_user_prompt" \
        "_plan_completion_check" \
        "$max_iterations" "$max_turns" "$worker_dir" "plan"

    local loop_result=$?

    # === FINALIZATION PHASE ===
    # Check if plan was written to the correct location
    local plan_file="$project_dir/.ralph/plans/${task_id}.md"
    if [ -f "$plan_file" ] && [ -s "$plan_file" ]; then
        log "Plan saved to $plan_file"
    else
        log_warn "No plan output generated at $plan_file"
    fi

    # Record completion
    agent_log_complete "$worker_dir" "$loop_result" "$start_time"

    # Write structured agent result
    local result_status="failure"
    local gate_result="FAIL"
    if [ $loop_result -eq 0 ] && [ -f "$plan_file" ] && [ -s "$plan_file" ]; then
        result_status="success"
        gate_result="PASS"
    fi

    # Build outputs JSON
    local outputs_json
    outputs_json=$(jq -n \
        --arg gate_result "$gate_result" \
        --arg plan_file ".ralph/plans/${task_id}.md" \
        --arg task_id "$task_id" \
        '{
            gate_result: $gate_result,
            plan_file: $plan_file,
            task_id: $task_id
        }')

    agent_write_result "$worker_dir" "$result_status" "$loop_result" "$outputs_json"

    log "Plan-mode agent finished: $worker_id"
    return $loop_result
}

# System prompt - READ-ONLY mode emphasis
_get_system_prompt() {
    local project_dir="$1"
    local task_id="$2"
    local plan_output=".ralph/plans/${task_id}.md"

    cat << EOF
You are a software architect and planning specialist. Your role is to explore the codebase and design implementation plans.

PROJECT: $project_dir
TASK: $task_id
OUTPUT: $plan_output

=== CRITICAL: READ-ONLY MODE - NO FILE MODIFICATIONS ===

This is a READ-ONLY planning task. You are STRICTLY PROHIBITED from:
* Creating new files (no Write, touch, or file creation)
* Modifying existing files (no Edit operations)
* Deleting, moving, or copying files
* Running commands that change state (npm install, pip install, git commit, etc.)

EXCEPTION: You may ONLY write to $plan_output

## Allowed Operations

* Glob, Grep, Read - for exploring the codebase
* Bash (read-only only): ls, git status, git log, git diff, find
* Write - ONLY to $plan_output

Your role is EXCLUSIVELY to explore and plan. You do NOT implement.
EOF
}

# User prompt callback for ralph loop
_plan_user_prompt() {
    local iteration="$1"
    # shellcheck disable=SC2034  # output_dir is part of callback signature
    local output_dir="$2"
    local task_id="$_PLAN_TASK_ID"
    local plan_output="$_PLAN_OUTPUT_FILE"

    # Always include the initial prompt to ensure full context after summarization
    cat << PROMPT_EOF
PLANNING TASK: $task_id

## Your Process

1. **Understand Requirements**: Read @../prd.md to understand what needs to be built

2. **Explore Thoroughly**:
   - Find existing patterns and conventions using Glob, Grep, Read
   - Understand the current architecture
   - Identify similar features as reference
   - Trace through relevant code paths
   - Use Bash ONLY for read-only operations (ls, git status, git log, git diff, find)

3. **Design Solution**:
   - Create implementation approach based on findings
   - Consider trade-offs and architectural decisions
   - Follow existing patterns where appropriate

4. **Write the Plan**: Document in $plan_output

## Required Output

Write to $plan_output with this structure:

\`\`\`markdown
# Implementation Plan: $task_id

## Overview
[1-2 sentences: what will be implemented and why]

## Requirements Analysis
| Requirement | Acceptance Criteria | Complexity |
|-------------|---------------------|------------|
| [from PRD] | [how to verify] | Low/Med/High |

## Existing Patterns
[Patterns found in codebase that implementation should follow, with file references]

## Implementation Approach
[Step-by-step strategy with specific file/function references]

## Dependencies and Sequencing
[Order of operations, what depends on what]

## Potential Challenges
[Technical risks, edge cases, things to watch out for]

### Critical Files
| Action | File | Reason |
|--------|------|--------|
| CREATE | path/file.ext | [Purpose] |
| MODIFY | path/file.ext | [What changes] |
| REFERENCE | path/file.ext | [Pattern to follow] |
\`\`\`

The "### Critical Files" section is REQUIRED - list 3-5 files most critical for implementation.

REMEMBER: You can ONLY explore and plan. Do NOT write, edit, or modify any files except $plan_output.
PROMPT_EOF

    if [ "$iteration" -gt 0 ]; then
        # Add continuation context for subsequent iterations
        cat << CONTINUE_EOF

CONTINUATION (Iteration $iteration):

Check if $plan_output exists and is complete:
1. All sections filled with meaningful content
2. "### Critical Files" section exists with specific files listed
3. Implementation approach is detailed and actionable

If incomplete, continue exploration and update. If complete, no action needed.
CONTINUE_EOF
    fi
}

# Completion check - returns 0 if plan is complete
_plan_completion_check() {
    local project_dir
    project_dir=$(agent_get_project_dir)
    local plan_file="$project_dir/$_PLAN_OUTPUT_FILE"

    # Check if plan file exists and contains the critical section
    if [ -f "$plan_file" ] && [ -s "$plan_file" ]; then
        if grep -q '### Critical Files' "$plan_file" 2>/dev/null; then
            return 0  # Complete
        fi
    fi

    return 1  # Not complete
}
