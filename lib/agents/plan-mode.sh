#!/usr/bin/env bash
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
#   - plan-output.md : The generated implementation plan
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "plan-mode" "Creates implementation plans stored in .ralph/plans/TASK-xxx.md"

# Required paths before agent can run
agent_required_paths() {
    echo "prd.md"
}

# Output files that must exist (non-empty) after agent completes
agent_output_files() {
    echo "plan-output.md"
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
    # Use config values (set by load_agent_config in agent-registry)
    local max_iterations="${WIGGUM_PLAN_MAX_ITERATIONS:-${AGENT_CONFIG_MAX_ITERATIONS:-5}}"
    local max_turns="${WIGGUM_PLAN_MAX_TURNS:-${AGENT_CONFIG_MAX_TURNS:-30}}"

    # Extract worker and task IDs
    local worker_id task_id
    worker_id=$(basename "$worker_dir")
    # Match any task prefix format: TASK-001, PIPELINE-001, etc.
    task_id=$(echo "$worker_id" | sed -E 's/worker-([A-Z]+-[0-9]+)-.*/\1/')

    # Allow task_id override from environment (for standalone invocation)
    task_id="${TASK_ID:-$task_id}"

    # Setup environment
    export WORKER_ID="$worker_id"
    export TASK_ID="$task_id"
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

    # Run planning loop (operates on project_dir, not a worktree)
    run_ralph_loop "$project_dir" \
        "$(_get_system_prompt "$project_dir")" \
        "_plan_user_prompt" \
        "_plan_completion_check" \
        "$max_iterations" "$max_turns" "$worker_dir" "plan"

    local loop_result=$?

    # === FINALIZATION PHASE ===
    # Copy plan to .ralph/plans/${task_id}.md if complete
    if [ -f "$worker_dir/plan-output.md" ] && [ -s "$worker_dir/plan-output.md" ]; then
        local plan_dest="$project_dir/.ralph/plans/${task_id}.md"
        cp "$worker_dir/plan-output.md" "$plan_dest"
        log "Plan saved to $plan_dest"
    else
        log_warn "No plan output generated"
    fi

    # Record completion
    agent_log_complete "$worker_dir" "$loop_result" "$start_time"

    # Write structured agent result
    local result_status="failure"
    if [ $loop_result -eq 0 ] && [ -f "$worker_dir/plan-output.md" ]; then
        result_status="success"
    fi

    # Build outputs JSON
    local outputs_json
    outputs_json=$(jq -n \
        --arg plan_file ".ralph/plans/${task_id}.md" \
        --arg task_id "$task_id" \
        '{
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
    local prd_relative="../prd.md"

    cat << EOF
IMPLEMENTATION PLANNING MODE - READ-ONLY EXPLORATION

You are in READ-ONLY planning mode. Your task is to explore the codebase and create a detailed implementation plan.

PROJECT DIRECTORY: $project_dir
PRD LOCATION: $prd_relative

CRITICAL RULES:
1. READ-ONLY: You MUST NOT modify any files in the project
2. EXPLORATION ONLY: Use Glob, Grep, and Read to understand the codebase
3. SINGLE OUTPUT: You may ONLY write to the file: plan-output.md
4. NO CODE CHANGES: Do not write code, create files, or execute commands that modify state

Your goal is to thoroughly understand:
- What the task requires (from the PRD)
- How the existing codebase is structured
- What patterns and conventions are used
- What files will need to be modified or created
- What dependencies or challenges exist

After exploration, document your findings in plan-output.md following the required format.
EOF
}

# User prompt callback for ralph loop
_plan_user_prompt() {
    local iteration="$1"
    # shellcheck disable=SC2034  # output_dir is part of callback signature
    local output_dir="$2"

    # Always include the initial prompt to ensure full context after summarization
    cat << 'PROMPT_EOF'
IMPLEMENTATION PLANNING TASK:

Create a comprehensive implementation plan by exploring the codebase and analyzing the requirements.

STEP-BY-STEP PROCESS:

1. **Read the PRD**: Examine @../prd.md to understand what needs to be implemented

2. **Explore the Codebase**: Use Glob, Grep, and Read to understand:
   - Project structure and organization
   - Existing patterns and conventions
   - Related code that will need to be modified
   - Dependencies and integrations

3. **Identify Critical Files**: Determine which files will be:
   - Modified (existing files that need changes)
   - Created (new files that need to be added)
   - Referenced (files to use as patterns/templates)

4. **Analyze Dependencies**: Understand:
   - What order tasks should be done in
   - What depends on what
   - Potential blockers or challenges

5. **Write the Plan**: Create plan-output.md with the following sections:

```markdown
## Overview
[Brief summary of what will be implemented and why]

## Requirements Analysis
[Breakdown of requirements from PRD with acceptance criteria]

## Existing Patterns
[Patterns, conventions, and structures found in the codebase that should be followed]

## Implementation Approach
[Detailed step-by-step approach for implementing each requirement]

## Dependencies and Sequencing
[Order of operations, what depends on what, integration points]

## Potential Challenges
[Technical challenges, edge cases, risks to consider]

### Critical Files
[List of files that will be created or modified, with brief description of changes]
```

IMPORTANT:
- The plan MUST include a "### Critical Files" section
- Be specific about file paths and what changes are needed
- Reference actual code patterns you found in the codebase
- Think through edge cases and potential issues
- The plan should be detailed enough that another developer could implement it

Write your complete plan to: plan-output.md
PROMPT_EOF

    if [ "$iteration" -gt 0 ]; then
        # Add continuation context for subsequent iterations
        cat << CONTINUE_EOF

CONTINUATION CONTEXT (Iteration $iteration):

If the plan-output.md file exists, review it and ensure it is complete:
1. Check that all sections are filled in with meaningful content
2. Verify the "### Critical Files" section exists and lists specific files
3. Ensure the implementation approach is detailed and actionable

If the plan is incomplete, continue your exploration and update plan-output.md.
If the plan is complete, no further action is needed.

Remember: This is READ-ONLY mode. Only write to plan-output.md.
CONTINUE_EOF
    fi
}

# Completion check - returns 0 if plan is complete
_plan_completion_check() {
    local worker_dir
    worker_dir=$(agent_get_worker_dir)
    local plan_file="$worker_dir/plan-output.md"

    # Check if plan file exists and contains the critical section
    if [ -f "$plan_file" ] && [ -s "$plan_file" ]; then
        if grep -q '### Critical Files' "$plan_file" 2>/dev/null; then
            return 0  # Complete
        fi
    fi

    return 1  # Not complete
}
