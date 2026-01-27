#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: resume-decide
# AGENT_DESCRIPTION: Analyzes previous worker conversation logs and worker.log
#   to decide which step to resume from (or ABORT). Produces resume instructions
#   for the resumed worker with context about what was accomplished and what
#   needs to happen next.
# REQUIRED_PATHS:
#   - conversations : Directory with converted conversation markdown files
#   - worker.log    : Phase-level status log from previous run
# OUTPUT_FILES:
#   - resume-step.txt         : Contains the step name to resume from (or ABORT)
#   - resume-instructions.md  : Context and guidance for the resumed worker
#   - resume-result.json      : Contains PASS or FAIL
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "system.resume-decide" "Analyzes logs to decide resume step"

# Required paths before agent can run
agent_required_paths() {
    echo "conversations"
    echo "worker.log"
}

# Output files that must exist (non-empty) after agent completes
# resume-step.txt is a special control file read by the pipeline directly
agent_output_files() {
    echo "resume-step.txt"
}

# Global variable to track report path across functions
declare -g _RESUME_DECIDE_REPORT_PATH=""

# Source dependencies
agent_source_core
agent_source_once

# Source pipeline loader for dynamic config reading
source "$WIGGUM_HOME/lib/pipeline/pipeline-loader.sh"

# Load pipeline configuration and cache step info for prompt generation
# Sets _PIPELINE_STEPS array with step IDs in order
_load_pipeline_config() {
    local project_dir="${1:-$WIGGUM_HOME}"

    # Try to resolve and load pipeline config
    local pipeline_path
    pipeline_path=$(pipeline_resolve "$project_dir" "" "${WIGGUM_PIPELINE:-}")

    if [ -n "$pipeline_path" ] && [ -f "$pipeline_path" ]; then
        pipeline_load "$pipeline_path" 2>/dev/null || pipeline_load_builtin_defaults
    else
        pipeline_load_builtin_defaults
    fi
}

# Find the last step with commit_after=true before a given step
# This identifies the recovery checkpoint for workspace reset
#
# Args:
#   step_id - The step we want to resume from
#
# Returns: step_id of the last checkpoint, or empty if none
_find_last_checkpoint_before() {
    local target_step="$1"
    local step_count
    step_count=$(pipeline_step_count)

    local target_idx=-1
    local last_checkpoint=""
    local i=0

    # First, find the target step's index
    while [ "$i" -lt "$step_count" ]; do
        local step_id
        step_id=$(pipeline_get "$i" ".id")
        if [ "$step_id" = "$target_step" ]; then
            target_idx=$i
            break
        fi
        i=$((i + 1))
    done

    # If target not found, return empty
    [ "$target_idx" -lt 0 ] && return

    # Now find the last checkpoint before target
    i=0
    while [ "$i" -lt "$target_idx" ]; do
        local step_id commit_after
        step_id=$(pipeline_get "$i" ".id")
        commit_after=$(pipeline_get "$i" ".commit_after" "false")

        if [ "$commit_after" = "true" ]; then
            last_checkpoint="$step_id"
        fi
        i=$((i + 1))
    done

    echo "$last_checkpoint"
}

# Check if a step has commit_after=true
#
# Args:
#   step_id - The step to check
#
# Returns: 0 if true, 1 if false
_step_has_commit_after() {
    local target_step="$1"
    local step_count
    step_count=$(pipeline_step_count)

    local i=0
    while [ "$i" -lt "$step_count" ]; do
        local step_id commit_after
        step_id=$(pipeline_get "$i" ".id")
        if [ "$step_id" = "$target_step" ]; then
            commit_after=$(pipeline_get "$i" ".commit_after" "false")
            [ "$commit_after" = "true" ] && return 0
            return 1
        fi
        i=$((i + 1))
    done
    return 1
}

# Get an agent's execution mode from its .md file
# Returns: mode string (ralph_loop, once, resume) or empty if not found
_get_agent_mode() {
    local agent_type="$1"
    local agent_path="${agent_type//./\/}"
    local md_file="$WIGGUM_HOME/lib/agents/${agent_path}.md"

    if [ ! -f "$md_file" ]; then
        echo ""
        return
    fi

    # Extract just the frontmatter and mode field
    local in_frontmatter=false
    local mode=""
    while IFS= read -r line; do
        if [ "$line" = "---" ]; then
            if [ "$in_frontmatter" = true ]; then
                break  # End of frontmatter
            fi
            in_frontmatter=true
            continue
        fi
        if [ "$in_frontmatter" = true ]; then
            if [[ "$line" =~ ^mode:[[:space:]]*(.+)$ ]]; then
                mode="${BASH_REMATCH[1]}"
                # Remove quotes if present
                mode="${mode#\"}"
                mode="${mode%\"}"
                break
            fi
        fi
    done < "$md_file"

    echo "${mode:-ralph_loop}"  # Default to ralph_loop if not specified
}

# Generate the "Pipeline Steps" table dynamically from loaded pipeline
# Returns markdown table via stdout
_generate_steps_table() {
    local step_count
    step_count=$(pipeline_step_count)

    echo "| # | Step | Agent | Commit After | Recovery Notes |"
    echo "|---|------|-------|--------------|----------------|"

    local i=0
    local step_num=1
    while [ "$i" -lt "$step_count" ]; do
        local step_id agent is_readonly enabled_by commit_after notes=""
        step_id=$(pipeline_get "$i" ".id")
        agent=$(pipeline_get "$i" ".agent")
        is_readonly=$(pipeline_get "$i" ".readonly" "false")
        enabled_by=$(pipeline_get "$i" ".enabled_by" "")
        commit_after=$(pipeline_get "$i" ".commit_after" "false")

        # Skip disabled-by-default steps in the table
        if [ -n "$enabled_by" ]; then
            i=$((i + 1))
            continue
        fi

        # Determine recovery notes
        local agent_mode
        agent_mode=$(_get_agent_mode "$agent")
        if [ "$agent_mode" = "ralph_loop" ]; then
            notes="Stateful - restart from beginning"
        elif [ "$is_readonly" = "true" ]; then
            notes="Read-only - no workspace changes"
        elif [ "$commit_after" = "true" ]; then
            notes="**Checkpoint** - workspace recoverable"
        else
            notes="No checkpoint - workspace state uncertain"
        fi

        local commit_marker="No"
        [ "$commit_after" = "true" ] && commit_marker="**Yes**"

        echo "| $step_num | \`$step_id\` | $agent | $commit_marker | $notes |"
        step_num=$((step_num + 1))
        i=$((i + 1))
    done
}

# Generate the "Decision Criteria" section
# Returns markdown via stdout
_generate_decision_criteria() {
    cat << 'EOF'
## Recovery-Focused Decision Making

Your goal is NOT just to find the interruption point, but to identify the **best step to resume from**
that will successfully recover the pipeline. Consider these factors:

### Workspace Recoverability

Steps marked with **Commit After = Yes** create git commits after completion. This means:
- The workspace can be reset to a known state from that commit
- Resuming from the NEXT step after a committed step is safe
- The resumed step will see a clean, known workspace state

Steps without commits leave the workspace in an indeterminate state:
- Partial changes may exist
- Resuming may encounter conflicts or inconsistencies
- You may need to go back to an earlier committed step

### Decision Matrix

| Scenario | Best Recovery Step |
|----------|-------------------|
| Pipeline went in unexpected direction (wrong approach, bad assumptions) | Last **committed checkpoint** before divergence |
| PRD incomplete but workspace has useful progress | First stateful step (to restart with preserved workspace) |
| Step failed due to transient issue (rate limits, timeouts) | The failed step itself |
| Workspace is corrupted or in unknown state | Last committed checkpoint (or `ABORT` if none) |
| All phases complete but results are wrong | The step that produced wrong results |
| All phases complete with correct outputs | `ABORT` (nothing to resume) |
| Fundamental issue (impossible task, bad PRD) | `ABORT` |

### The Key Question

Ask yourself: "If I resume from step X, will the workspace be in a known good state that allows
that step to succeed?" If the answer is uncertain, go back to an earlier committed checkpoint.
EOF
}

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    # $3 is max_iterations (unused — this agent runs once)
    local max_turns="${4:-25}"

    # Setup logging to worker.log
    export LOG_FILE="$worker_dir/worker.log"

    # Extract worker info for logging
    local worker_id
    worker_id=$(basename "$worker_dir")
    local task_id
    task_id=$(echo "$worker_id" | sed -E 's/worker-([A-Za-z]{2,10}-[0-9]{1,4})-.*/\1/' || echo "")
    local start_time
    start_time=$(date -Iseconds)

    # Log header
    log_section "RESUME-DECIDE"
    log_kv "Agent" "system.resume-decide"
    log_kv "Worker ID" "$worker_id"
    log_kv "Task ID" "$task_id"
    log_kv "Worker Dir" "$worker_dir"
    log_kv "Started" "$start_time"

    log "Analyzing previous run..."

    # Load pipeline configuration for dynamic prompt generation
    _load_pipeline_config "$project_dir"

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Set up context for epoch-named results
    agent_setup_context "$worker_dir" "$worker_dir" "$project_dir"

    # Build a lightweight user prompt with file paths for the agent to explore
    local user_prompt
    user_prompt=$(_build_user_prompt "$worker_dir")

    # Run Claude with tool access so it can read the files itself
    # Create run-namespaced log directory (unified agent interface)
    local step_id="${WIGGUM_STEP_ID:-resume-decide}"
    local run_epoch
    run_epoch=$(date +%s)
    local run_id="${step_id}-${run_epoch}"
    mkdir -p "$worker_dir/logs/$run_id"
    local log_file="$worker_dir/logs/$run_id/${step_id}-0-${run_epoch}.log"

    local workspace="$worker_dir"
    [ -d "$worker_dir/workspace" ] && workspace="$worker_dir/workspace"

    run_agent_once "$workspace" \
        "$(_get_system_prompt "$worker_dir")" \
        "$user_prompt" \
        "$log_file" \
        "$max_turns"

    local agent_exit=$?

    if [ $agent_exit -ne 0 ]; then
        log_warn "Resume-decide agent exited with code $agent_exit"
    fi

    # Extract <step> and <instructions> from Claude's output
    local step instructions
    step=$(_extract_tag_content_from_stream_json "$log_file" "step") || true
    instructions=$(_extract_tag_content_from_stream_json "$log_file" "instructions") || true

    # Default to ABORT if no step extracted
    if [ -z "$step" ]; then
        log_error "No <step> tag found in resume-decide output"
        step="ABORT"
        instructions="${instructions:-Resume-decide agent did not produce a valid step decision.}"
    fi

    # Determine workspace recovery information
    local last_checkpoint=""
    local recovery_possible="false"

    if [ "$step" != "ABORT" ]; then
        # Find the last commit checkpoint before the chosen step
        last_checkpoint=$(_find_last_checkpoint_before "$step")

        # Recovery is possible if there's a checkpoint
        if [ -n "$last_checkpoint" ]; then
            recovery_possible="true"
            log "Found recovery checkpoint: $last_checkpoint (before $step)"
        else
            log "No commit checkpoint found before $step - workspace state may be uncertain"
        fi
    fi

    # Write outputs
    echo "$step" > "$worker_dir/resume-step.txt"
    if [ -z "$instructions" ]; then
        instructions="Resuming from step: $step. No detailed instructions available."
    fi
    _RESUME_DECIDE_REPORT_PATH=$(agent_write_report "$worker_dir" "$instructions")

    log "Resume decision: $step"

    # Log completion footer
    log_subsection "RESUME-DECIDE COMPLETED"
    log_kv "Decision" "$step"
    log_kv "Last Checkpoint" "${last_checkpoint:-none}"
    log_kv "Recovery Possible" "$recovery_possible"
    log_kv "Finished" "$(date -Iseconds)"

    # Build result JSON with recovery metadata
    local result_json
    result_json=$(jq -n \
        --arg resume_step "$step" \
        --arg report_file "${_RESUME_DECIDE_REPORT_PATH:-}" \
        --arg last_checkpoint "$last_checkpoint" \
        --arg recovery_possible "$recovery_possible" \
        '{
            resume_step: $resume_step,
            report_file: $report_file,
            workspace_recovery: {
                last_checkpoint_step: (if $last_checkpoint == "" then null else $last_checkpoint end),
                recovery_possible: ($recovery_possible == "true")
            }
        }')

    # Both resume and abort are successful decisions
    agent_write_result "$worker_dir" "PASS" "$result_json"

    return 0
}

# System prompt for the resume-decide agent
_get_system_prompt() {
    local worker_dir="$1"

    cat << EOF
RESUME DECISION AGENT:

You determine where an interrupted worker should resume from to **recover the pipeline**.
You do NOT fix issues - only analyze and decide the best recovery point.

WORKER DIRECTORY: $worker_dir

## Core Principle: FIND THE BEST RECOVERY POINT

Your job is NOT just to find where the pipeline stopped. It's to identify which step,
when resumed from, will lead to successful pipeline completion.

This may mean:
- Going back to an earlier step if the workspace is in an unknown state
- Resuming from a step with a committed checkpoint (see "Commit After" column in pipeline table)
- Restarting execution entirely if the approach taken was fundamentally wrong

## Worker Directory Layout

\`\`\`
$worker_dir/
├── worker.log           ← Phase-level status log (YOUR PRIMARY EVIDENCE)
├── prd.md               ← Task requirements (check completion status)
├── workspace/           ← Code changes (PRESERVED - do not modify)
├── pipeline-config.json ← Pipeline configuration with step info
├── conversations/       ← Converted conversation logs (step-*.md files)
├── logs/                ← Raw JSON stream logs (DO NOT READ - too large)
├── summaries/           ← Iteration summaries
├── results/             ← Step result files (*-<step>-result.json)
└── reports/             ← Step report files (*-<step>-report.md)
\`\`\`

## Pipeline Steps (in execution order)

$(_generate_steps_table)

## Understanding Commit Checkpoints

Steps with **Commit After = Yes** create git commits after completion. These are **recovery checkpoints**:
- The workspace state at that point is recorded in git history
- When resuming from the NEXT step, the workspace can be reset to this known state
- If something went wrong after a checkpoint, going back to it is safe

Steps without commits have uncertain workspace state:
- Partial work may exist
- Files may be in inconsistent states
- Resuming may encounter unexpected conditions

## Discovering Phase Evidence

**DO NOT rely on hardcoded phase names.** Explore the worker directory to discover what ran:

1. **List result files**: \`ls -la $worker_dir/results/\`
   - Files are named: \`<epoch>-<step-id>-result.json\`
   - Read the JSON to see the gate_result (PASS/FAIL/FIX/SKIP)

2. **List summaries**: \`ls -la $worker_dir/summaries/\`
   - Contains iteration-by-iteration progress

3. **List conversations**: \`ls -la $worker_dir/conversations/\`
   - Human-readable logs showing what each step did

4. **Read worker.log**: Contains timestamped phase markers like:
   - "PIPELINE STEP: <step_id>" - step started
   - "STEP COMPLETED: <step_id>" with "Result: <result>" - step finished
   - Errors and warnings

5. **Check git history in workspace**:
   \`cd $worker_dir/workspace && git log --oneline -10\`
   - Shows commits from steps with commit_after=true
   - Helps identify recovery checkpoints

## Git Restrictions (CRITICAL)

You are a READ-ONLY analyst. The workspace contains uncommitted work that MUST NOT be destroyed.

**FORBIDDEN (will corrupt the workspace):**
- \`git checkout\`, \`git stash\`, \`git reset\`, \`git clean\`, \`git restore\`
- \`git commit\`, \`git add\`
- Any write operation to workspace/

**ALLOWED (read-only):**
- \`git status\`, \`git diff\`, \`git log\`, \`git show\`
- Reading any file in the worker directory
EOF
}

# Build user prompt — structured methodology for dynamic pipeline exploration
_build_user_prompt() {
    local worker_dir="$1"

    cat << EOF
RESUME ANALYSIS TASK:

Analyze this interrupted worker and determine the **best step to resume from** for successful
pipeline recovery. Your job is NOT just to find where it stopped - it's to find the step that,
when resumed, will lead to successful completion.

## Step 1: Explore the Worker Directory Structure

First, understand what exists in this worker directory:

\`\`\`bash
# List all top-level contents
ls -la $worker_dir/

# Check what result files exist (shows which steps completed)
ls -la $worker_dir/results/ 2>/dev/null || echo "No results directory"

# Check what summaries exist
ls -la $worker_dir/summaries/ 2>/dev/null || echo "No summaries directory"

# Check what conversations were logged
ls -la $worker_dir/conversations/ 2>/dev/null || echo "No conversations directory"
\`\`\`

## Step 2: Read the Worker Log

The worker.log is your primary evidence of what happened:

\`\`\`
$worker_dir/worker.log
\`\`\`

Look for these patterns:
- **"PIPELINE STEP: <step_id>"** — A step started
- **"STEP COMPLETED: <step_id>"** with **"Result: <PASS|FAIL|FIX|SKIP>"** — A step finished
- **"ERROR"** markers — Something went wrong
- **Timestamps** — Understand the sequence of events

Build a timeline of which steps ran and what their results were.

## Step 3: Examine Result Files

For each step that claims to have completed, read its result file:

\`\`\`bash
# Result files are named: <epoch>-<step-id>-result.json
cat $worker_dir/results/*-result.json 2>/dev/null
\`\`\`

Each result JSON contains:
- \`gate_result\`: PASS, FAIL, FIX, or SKIP
- \`outputs\`: Additional metadata from the step

A step is NOT complete if:
- The log says it started but no result file exists
- The result file shows FAIL or an unexpected state

## Step 4: Identify Recovery Checkpoints

Check the git history in the workspace to find committed checkpoints:

\`\`\`bash
cd $worker_dir/workspace && git log --oneline -15
\`\`\`

Commits from pipeline steps (with commit_after=true) are recovery points.
If you need to resume from a step after a checkpoint, the workspace can be
reset to that known state.

## Step 5: Check PRD Completion Status

\`\`\`
$worker_dir/prd.md
\`\`\`

Count task markers:
- \`- [x]\` = completed
- \`- [ ]\` = incomplete
- \`- [*]\` = blocked/failed

If tasks are incomplete, determine if:
- Execution never finished (resume from execution)
- Execution finished but went in wrong direction (may need to go back further)

## Step 6: Verify Workspace State

Check what actual changes exist:

\`\`\`bash
cd $worker_dir/workspace && git status
cd $worker_dir/workspace && git diff --stat
\`\`\`

Compare against what was claimed in:
- PRD task descriptions
- Summaries (if they exist)
- Conversation logs

If workspace contradicts claims, you may need to go back to an earlier checkpoint.

## Step 7: Decide the Best Recovery Step

Consider these questions:

1. **Is the workspace in a known good state?**
   - If uncertain, find the last committed checkpoint and resume from the step AFTER it

2. **Did the pipeline go in the wrong direction?**
   - If the approach was fundamentally wrong, go back to a checkpoint before the divergence
   - The resumed step can try a different approach

3. **Was this a transient failure?**
   - If a step failed due to rate limits, timeouts, or similar, resume from that step

4. **Are all steps actually complete?**
   - If everything completed successfully, return ABORT

## Decision Criteria

$(_generate_decision_criteria)

## Important Considerations

- **Read logs dynamically** — Don't assume specific phase names. Explore what actually exists.
- **Trust evidence over claims** — Verify workspace diff matches what logs/PRD say happened.
- **Consider workspace recoverability** — Steps with commit_after create safe recovery points.
- **Don't read logs/ directory** — Raw JSON streams will exhaust your context.
- **Recovery > Correctness** — Choose the step that gives the best chance of successful completion.

## Output Format

<step>STEP_ID</step>

<instructions>
## Analysis Summary

[Brief summary of what you found: which steps ran, their results, current state]

## What Was Accomplished

[Bullet points of completed work, referencing specific files and results]

## Why This Recovery Point

[Explain why you chose this step:
- Is there a committed checkpoint before it?
- What state will the workspace be in?
- What makes this the best recovery choice?]

## Guidance for Resumed Step

[Specific instructions for the resumed step:
- If going back to execution: what approach to try, what to preserve
- If resuming a failed step: what caused the failure, how to avoid it
- Context the resumed agent needs to succeed]

## Warnings

[Issues to be aware of:
- Errors from previous run
- Partial work that may need attention
- Decisions that should be preserved or changed]
</instructions>

The <step> tag MUST be exactly one of the pipeline step IDs from the table in the system prompt, or ABORT
EOF
}

