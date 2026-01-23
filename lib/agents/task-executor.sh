#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: task-executor
# AGENT_DESCRIPTION: Executes task implementation via supervised ralph loop.
#   Encapsulates the main code-writing agent interaction, reading configuration
#   from executor-config.json and running the supervised ralph loop with PRD
#   task completion checks.
# REQUIRED_PATHS:
#   - workspace : Directory containing the code to work on
#   - prd.md    : Product Requirements Document containing tasks to execute
# OUTPUT_FILES:
#   - logs/iteration-*.log : Per-iteration conversation logs
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "task-executor" "Executes task implementation via supervised ralph loop"

# Required paths before agent can run
agent_required_paths() {
    echo "workspace"
    echo "prd.md"
}

# Source dependencies using base library helpers
agent_source_core
agent_source_ralph_supervised
agent_source_tasks

# Track plan file and resume instructions for user prompt callback
_TASK_PLAN_FILE=""
_TASK_PRD_FILE=""
_TASK_RESUME_INSTRUCTIONS=""

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"

    local workspace="$worker_dir/workspace"

    if [ ! -d "$workspace" ]; then
        log_error "Workspace not found: $workspace"
        return 1
    fi

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Read configuration from executor-config.json
    local config_file="$worker_dir/executor-config.json"
    local max_iterations max_turns supervisor_interval plan_file resume_instructions

    if [ -f "$config_file" ]; then
        max_iterations=$(jq -r '.max_iterations // 20' "$config_file")
        max_turns=$(jq -r '.max_turns // 50' "$config_file")
        supervisor_interval=$(jq -r '.supervisor_interval // 2' "$config_file")
        plan_file=$(jq -r '.plan_file // ""' "$config_file")
        resume_instructions=$(jq -r '.resume_instructions // ""' "$config_file")
    else
        max_iterations="${AGENT_CONFIG_MAX_ITERATIONS:-20}"
        max_turns="${AGENT_CONFIG_MAX_TURNS:-50}"
        supervisor_interval="${WIGGUM_SUPERVISOR_INTERVAL:-2}"
        plan_file=""
        resume_instructions=""
    fi

    # Set up callback context
    local task_id
    local worker_id
    worker_id=$(basename "$worker_dir")
    task_id=$(echo "$worker_id" | sed -E 's/worker-([A-Z]+-[0-9]+)-.*/\1/')
    agent_setup_context "$worker_dir" "$workspace" "$project_dir" "$task_id"

    # Set globals for callbacks
    _TASK_PRD_FILE="$worker_dir/prd.md"
    _TASK_PLAN_FILE="$plan_file"
    _TASK_RESUME_INSTRUCTIONS="$resume_instructions"

    log "Task executor starting (max_iterations=$max_iterations, max_turns=$max_turns, supervisor_interval=$supervisor_interval)"

    # Run main work loop with supervision
    run_ralph_loop_supervised "$workspace" \
        "$(_get_system_prompt "$workspace")" \
        "_task_user_prompt" \
        "_task_completion_check" \
        "$max_iterations" "$max_turns" "$worker_dir" "iteration" \
        "$supervisor_interval"

    local loop_result=$?

    log "Task executor completed with exit code: $loop_result"

    # Write structured agent result
    local result_status="failure"
    if [ $loop_result -eq 0 ]; then
        result_status="success"
    fi

    local session_id="${RALPH_LOOP_LAST_SESSION_ID:-}"
    local outputs_json
    outputs_json=$(jq -n \
        --arg gate_result "$([ $loop_result -eq 0 ] && echo "PASS" || echo "FAIL")" \
        --arg session_id "$session_id" \
        --argjson loop_exit_code "$loop_result" \
        '{
            gate_result: $gate_result,
            session_id: $session_id,
            loop_exit_code: $loop_exit_code
        }')

    agent_write_result "$worker_dir" "$result_status" "$loop_result" "$outputs_json"

    return $loop_result
}

# System prompt - workspace boundary enforcement
_get_system_prompt() {
    local workspace="$1"
    local prd_relative="../prd.md"

    cat << EOF
SENIOR SOFTWARE ENGINEER ROLE:

You are a senior software engineer implementing a specific task from a PRD.
Your goal is to deliver production-quality code that fits naturally into the existing codebase.

WORKSPACE: $workspace
PRD: $prd_relative

## Core Principles

1. **Understand Before You Build**
   - Study the existing architecture before writing code
   - Find similar patterns in the codebase and follow them
   - Understand how your changes integrate with existing systems

2. **Write Production-Quality Code**
   - Code should be correct, secure, and maintainable
   - Handle errors appropriately - don't swallow exceptions
   - Include tests that verify the implementation works
   - Follow the project's existing conventions exactly

3. **Stay Focused**
   - Complete the PRD task fully, but don't over-engineer
   - Don't refactor unrelated code or add unrequested features
   - If blocked, document clearly and mark as incomplete

## Workspace Security

CRITICAL: You MUST NOT access files outside your workspace.
- Allowed: $workspace and $prd_relative
- Do NOT use paths like ../../ to escape
- Do NOT follow symlinks outside the workspace

For subagent prompts, prepend:
<workspace>Your allowed workspace is: $workspace. Do not read or modify files outside of this directory</workspace>
EOF
}

# --- User prompt composable segments ---

_emit_supervisor_section() {
    local feedback="$1"
    [ -z "$feedback" ] && return
    cat << EOF
SUPERVISOR GUIDANCE:

$feedback

---

EOF
}

_emit_protocol_section() {
    cat << 'PROMPT_EOF'
TASK EXECUTION PROTOCOL:

Your mission: Complete the next incomplete task from the PRD with production-quality code.

## Phase 1: Understand the Task

1. **Read the PRD** (@../prd.md)
   - Find the first incomplete task marked with `- [ ]`
   - Skip completed `- [x]` and failed `- [*]` tasks
   - Focus on ONE task only

2. **Understand the Requirements**
   - What exactly needs to be implemented?
   - What are the acceptance criteria?
   - What edge cases should be handled?

## Phase 2: Study the Architecture

Before writing ANY code, understand the existing codebase:

3. **Explore the Project Structure**
   - How is the codebase organized?
   - Where do similar features live?
   - What are the key abstractions and patterns?

4. **Find Existing Patterns**
   - Search for similar functionality already implemented
   - Note the patterns used: naming, structure, error handling
   - Identify the testing approach used in the project

5. **Understand Integration Points**
   - What existing code will you interact with?
   - What APIs or interfaces must you follow?
   - Are there shared utilities you should use?

## Phase 3: Implement with Quality

6. **Write the Implementation**
   - Follow the patterns you discovered in Phase 2
   - Match the existing code style exactly
   - Handle errors appropriately (don't swallow them)
   - Keep functions focused and readable

7. **Write Tests**
   - Add tests that verify your implementation works
   - Follow the project's existing test patterns
   - Test the happy path and key edge cases
   - If the project has no tests, at least manually verify

8. **Security Considerations**
   - Validate inputs from untrusted sources
   - Avoid injection vulnerabilities
   - Don't hardcode secrets or credentials
   - Handle sensitive data appropriately

## Phase 4: Verify and Complete

9. **Run Tests and Verification**
   - Run the test suite if one exists
   - Manually verify your implementation works
   - Check for obvious regressions

10. **Update the PRD**
    - `- [ ]` → `- [x]` if successfully completed
    - `- [ ]` → `- [*]` if blocked (explain why)

## Quality Checklist

Before marking complete, verify:
- [ ] Implementation meets all requirements
- [ ] Code follows existing patterns in the codebase
- [ ] Error cases are handled appropriately
- [ ] Tests are added (matching project conventions)
- [ ] No security vulnerabilities introduced
- [ ] Changes integrate cleanly with existing code

## Rules

- Complete ONE task fully before moving to the next
- If blocked, document clearly and mark as `- [*]`
- Don't over-engineer or add unrequested features
- Stay within the workspace directory
PROMPT_EOF
}

_emit_plan_section() {
    local plan_file="$1"
    [ -z "$plan_file" ] || [ ! -f "$plan_file" ] && return
    cat << PLAN_EOF

IMPLEMENTATION PLAN AVAILABLE:

An implementation plan has been created for this task. Before starting:
1. Read the plan at: @$plan_file
2. Follow the implementation approach described in the plan
3. Pay attention to the Critical Files section
4. Consider the potential challenges identified

The plan provides guidance on:
- Existing patterns in the codebase to follow
- Recommended implementation approach
- Dependencies and sequencing
- Potential challenges to watch for
PLAN_EOF
}

_emit_resume_section() {
    local iteration="$1"
    local resume_file="$2"
    [ "$iteration" -ne 0 ] && return
    [ -z "$resume_file" ] || [ ! -f "$resume_file" ] || [ ! -s "$resume_file" ] && return
    local resume_content
    resume_content=$(cat "$resume_file")
    cat << RESUME_EOF

CONTEXT FROM PREVIOUS SESSION (RESUMED):

This worker is resuming from a previous interrupted run. The following context
describes what was accomplished and what needs to happen now:

$resume_content

Continue from where the previous session left off:
- Do NOT repeat work that was already completed
- Pick up where the previous session stopped
- If a task was partially completed, continue from where it left off
- Use the context above to maintain consistency in approach and patterns

CRITICAL: Do NOT read files in the logs/ directory - they contain full conversation JSON streams that are too large and will deplete your context window.
RESUME_EOF
}

_emit_context_section() {
    local iteration="$1"
    local output_dir="$2"
    [ "$iteration" -le 0 ] && return
    local prev_iter=$((iteration - 1))
    [ -f "$output_dir/summaries/iteration-$prev_iter-summary.txt" ] || return
    cat << CONTEXT_EOF

CONTEXT FROM PREVIOUS ITERATION:

This is iteration $iteration of a multi-iteration work session. Previous work has been completed in earlier iterations.

To understand what has already been accomplished and maintain continuity:
- Read the file @../summaries/iteration-$prev_iter-summary.txt to understand completed work and context
- This summary describes what was done, decisions made, and files modified
- Use this information to avoid duplicating work and to build upon previous progress
- Ensure your approach aligns with patterns and decisions from earlier iterations

CRITICAL: Do NOT read files in the logs/ directory - they contain full conversation JSON streams that are too large and will deplete your context window. Only read the summaries/iteration-X-summary.txt files for context.
CONTEXT_EOF
}

# User prompt callback for supervised ralph loop
# Args: iteration, output_dir, supervisor_dir, supervisor_feedback
_task_user_prompt() {
    local iteration="$1"
    local output_dir="$2"
    local _supervisor_dir="$3"  # unused but part of callback signature
    local supervisor_feedback="$4"

    _emit_supervisor_section "$supervisor_feedback"
    _emit_protocol_section
    _emit_plan_section "$_TASK_PLAN_FILE"
    _emit_resume_section "$iteration" "$_TASK_RESUME_INSTRUCTIONS"
    _emit_context_section "$iteration" "$output_dir"
}

# Completion check - check PRD for incomplete tasks
_task_completion_check() {
    ! has_incomplete_tasks "$_TASK_PRD_FILE"
}
