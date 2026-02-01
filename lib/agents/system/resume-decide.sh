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
source "$WIGGUM_HOME/lib/core/platform.sh"

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

Your goal is NOT just to find the interruption point, but to identify the **best outcome** for this worker.
You have FOUR possible decisions:

### Decision Options

| Decision | When to Use |
|----------|-------------|
| **COMPLETE** | All PRD requirements met, code committed, build passes. Work is done. |
| **RETRY:PIPELINE:STEP** | Resume pipeline from a specific step. Work remains. |
| **ABORT** | Fundamental/unrecoverable issue (bad PRD, impossible task, repeated failures). |
| **DEFER** | Transient failure (OOM, API timeout, rate limit). Worth retrying later. |

### COMPLETE Criteria

Choose COMPLETE when:
- All PRD items are implemented and committed
- Git status shows committed work (not just staged)
- A PR already exists (check `pr_url.txt`) OR the branch has commits ready for PR creation
- Build/tests pass (or no test step was configured)

Do NOT choose COMPLETE if PRD items remain unchecked or workspace has no meaningful changes.

### RETRY Criteria

Choose RETRY when work remains and can be continued. Format: `RETRY:PIPELINE_NAME:STEP_ID`
- PIPELINE_NAME comes from `pipeline-config.json` field `.pipeline.name`
- STEP_ID is the step to resume from

Consider workspace recoverability:
- Steps with **Commit After = Yes** create recovery checkpoints
- Resuming from the NEXT step after a committed step is safe
- If workspace state is uncertain, go back to an earlier checkpoint

### ABORT Criteria

Choose ABORT only for truly unrecoverable situations:
- Bad/impossible requirements in PRD
- Architectural impossibility
- Same step has failed repeatedly across multiple resume attempts
- Fundamental tooling/environment issues that won't self-resolve

### DEFER Criteria

Choose DEFER for transient issues that may resolve on their own:
- Out-of-memory errors during execution
- API rate limiting or service unavailability
- Network timeouts
- Resource contention issues

The system will automatically retry after a cooldown period.

### Workspace Recoverability

Steps marked with **Commit After = Yes** create git commits after completion. This means:
- The workspace can be reset to a known state from that commit
- Resuming from the NEXT step after a committed step is safe
- The resumed step will see a clean, known workspace state

### The Key Question

Ask yourself: "What is the RIGHT outcome for this worker right now?"
- If work is done → COMPLETE
- If work can continue → RETRY from the best recovery point
- If something temporary went wrong → DEFER
- If it's fundamentally broken → ABORT
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
    start_time=$(iso_now)

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
    run_epoch=$(epoch_now)
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

    # Extract <decision> and <instructions> from Claude's output
    # Try <decision> tag first (new format), fall back to <step> (legacy)
    local raw_decision instructions
    raw_decision=$(_extract_tag_content_from_stream_json "$log_file" "decision") || true
    if [ -z "$raw_decision" ]; then
        # Legacy fallback: try <step> tag
        raw_decision=$(_extract_tag_content_from_stream_json "$log_file" "step") || true
    fi
    instructions=$(_extract_tag_content_from_stream_json "$log_file" "instructions") || true

    # Default to ABORT if no decision extracted
    if [ -z "$raw_decision" ]; then
        log_error "No <decision> or <step> tag found in resume-decide output"
        raw_decision="ABORT"
        instructions="${instructions:-Resume-decide agent did not produce a valid decision.}"
    fi

    # Strip whitespace
    raw_decision=$(echo "$raw_decision" | tr -d '[:space:]')

    # Parse decision into components
    local decision="" resume_pipeline="" resume_step_id="" reason=""
    _parse_resume_decision "$raw_decision" "$instructions"

    # Determine workspace recovery information (for RETRY decisions)
    local last_checkpoint=""
    local recovery_possible="false"

    if [ "$decision" = "RETRY" ] && [ -n "$resume_step_id" ]; then
        # Find the last commit checkpoint before the chosen step
        last_checkpoint=$(_find_last_checkpoint_before "$resume_step_id")

        # Recovery is possible if there's a checkpoint
        if [ -n "$last_checkpoint" ]; then
            recovery_possible="true"
            log "Found recovery checkpoint: $last_checkpoint (before $resume_step_id)"
        else
            log "No commit checkpoint found before $resume_step_id - workspace state may be uncertain"
        fi
    fi

    # Write outputs
    # Backward compat: resume-step.txt with raw decision
    echo "$raw_decision" > "$worker_dir/resume-step.txt"

    # New: structured resume-decision.json
    _write_resume_decision "$worker_dir" "$decision" "$resume_pipeline" "$resume_step_id" "$reason"

    if [ -z "$instructions" ]; then
        instructions="Decision: $raw_decision. No detailed instructions available."
    fi
    _RESUME_DECIDE_REPORT_PATH=$(agent_write_report "$worker_dir" "$instructions")

    log "Resume decision: $raw_decision"

    # Log completion footer
    log_subsection "RESUME-DECIDE COMPLETED"
    log_kv "Decision" "$decision"
    log_kv "Pipeline" "${resume_pipeline:-n/a}"
    log_kv "Resume Step" "${resume_step_id:-n/a}"
    log_kv "Last Checkpoint" "${last_checkpoint:-none}"
    log_kv "Recovery Possible" "$recovery_possible"
    log_kv "Finished" "$(iso_now)"

    # Build result JSON with recovery metadata
    local result_json
    result_json=$(jq -n \
        --arg decision "$decision" \
        --arg resume_pipeline "$resume_pipeline" \
        --arg resume_step "$resume_step_id" \
        --arg report_file "${_RESUME_DECIDE_REPORT_PATH:-}" \
        --arg last_checkpoint "$last_checkpoint" \
        --arg recovery_possible "$recovery_possible" \
        '{
            decision: $decision,
            resume_pipeline: (if $resume_pipeline == "" then null else $resume_pipeline end),
            resume_step: (if $resume_step == "" then null else $resume_step end),
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

# Parse raw decision string into components
#
# Sets outer-scope variables: decision, resume_pipeline, resume_step_id, reason
#
# Args:
#   raw_decision - Raw decision string (e.g., "RETRY:default:execution", "COMPLETE")
#   instructions - Instructions text for reason fallback
_parse_resume_decision() {
    local raw="$1"
    local instr="${2:-}"

    if [[ "$raw" == RETRY:* ]]; then
        decision="RETRY"
        # Parse RETRY:pipeline:step
        resume_pipeline=$(echo "$raw" | cut -d: -f2)
        resume_step_id=$(echo "$raw" | cut -d: -f3)
        reason="Resume from $resume_step_id in pipeline $resume_pipeline"
    elif [[ "$raw" == "COMPLETE" ]]; then
        decision="COMPLETE"
        reason="${instr:0:200}"
    elif [[ "$raw" == "ABORT" ]]; then
        decision="ABORT"
        reason="${instr:0:200}"
    elif [[ "$raw" == "DEFER" ]]; then
        decision="DEFER"
        reason="${instr:0:200}"
    else
        # Legacy: bare step_id → treat as RETRY with unknown pipeline
        decision="RETRY"
        resume_step_id="$raw"
        reason="Legacy format: resuming from step $raw"
    fi
}

# Write structured resume-decision.json
#
# Args:
#   worker_dir     - Worker directory path
#   decision       - Decision type (COMPLETE, RETRY, ABORT, DEFER)
#   pipeline       - Pipeline name (for RETRY)
#   step           - Step ID (for RETRY)
#   reason         - Human-readable reason
_write_resume_decision() {
    local worker_dir="$1"
    local dec="$2"
    local pipeline="${3:-}"
    local step="${4:-}"
    local reason="${5:-}"

    jq -n \
        --arg decision "$dec" \
        --arg pipeline "$pipeline" \
        --arg resume_step "$step" \
        --arg reason "$reason" \
        '{
            decision: $decision,
            pipeline: (if $pipeline == "" then null else $pipeline end),
            resume_step: (if $resume_step == "" then null else $resume_step end),
            reason: $reason
        }' > "$worker_dir/resume-decision.json"
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

## Output Format

Your final output MUST contain a \`<decision>\` tag with one of these values:
- \`COMPLETE\` — All PRD requirements met, code committed
- \`RETRY:PIPELINE_NAME:STEP_ID\` — Resume from step (e.g., \`RETRY:default:execution\`)
- \`ABORT\` — Unrecoverable failure
- \`DEFER\` — Transient issue, try again later

And an \`<instructions>\` tag with analysis details for the resumed worker.
EOF
}

# Build user prompt — structured methodology for dynamic pipeline exploration
_build_user_prompt() {
    local worker_dir="$1"

    # Extract pipeline name from config for RETRY decisions
    local pipeline_name=""
    if [ -f "$worker_dir/pipeline-config.json" ]; then
        pipeline_name=$(jq -r '.pipeline.name // ""' "$worker_dir/pipeline-config.json" 2>/dev/null)
    fi
    pipeline_name="${pipeline_name:-default}"

    cat << EOF
RESUME ANALYSIS TASK:

Analyze this interrupted worker and determine the **best outcome** — whether the work is done
(COMPLETE), should be resumed from a specific step (RETRY), is unrecoverable (ABORT), or hit
a transient issue (DEFER).

The worker was using pipeline '${pipeline_name}'.

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

## Step 5: Check PRD Completion Status and PR

\`\`\`
$worker_dir/prd.md
\`\`\`

Count task markers:
- \`- [x]\` = completed
- \`- [ ]\` = incomplete
- \`- [*]\` = blocked/failed

Also check if a PR already exists:
\`\`\`bash
cat $worker_dir/pr_url.txt 2>/dev/null || echo "No PR exists yet"
\`\`\`

If ALL PRD items are complete and code is committed, this may be a COMPLETE decision.
If tasks are incomplete, determine if:
- Execution never finished (RETRY from execution)
- Execution finished but went in wrong direction (RETRY from earlier checkpoint)

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

## Step 7: Make Your Decision

Consider these questions:

1. **Is ALL the work done?**
   - If all PRD items are complete, code is committed, and build passes → **COMPLETE**
   - Check \`pr_url.txt\` — if a PR already exists, that's further evidence of COMPLETE

2. **Is the workspace in a known good state for resuming?**
   - If uncertain, find the last committed checkpoint and use RETRY from the step AFTER it

3. **Did the pipeline go in the wrong direction?**
   - If the approach was fundamentally wrong, RETRY from a checkpoint before the divergence

4. **Was this a transient failure (OOM, timeout, rate limit)?**
   - If a step failed due to transient issues → **DEFER** (system retries after cooldown)

5. **Is this fundamentally unrecoverable?**
   - Bad PRD, impossible task, repeated same failure → **ABORT**

## Decision Criteria

$(_generate_decision_criteria)

## Important Considerations

- **Read logs dynamically** — Don't assume specific phase names. Explore what actually exists.
- **Trust evidence over claims** — Verify workspace diff matches what logs/PRD say happened.
- **Consider workspace recoverability** — Steps with commit_after create safe recovery points.
- **Don't read logs/ directory** — Raw JSON streams will exhaust your context.
- **For RETRY, use format** \`RETRY:${pipeline_name}:STEP_ID\` (pipeline name from above).

## Output Format

<decision>DECISION</decision>

Where DECISION is one of:
- \`COMPLETE\`
- \`RETRY:${pipeline_name}:STEP_ID\` (e.g., \`RETRY:${pipeline_name}:execution\`)
- \`ABORT\`
- \`DEFER\`

<instructions>
## Analysis Summary

[Brief summary of what you found: which steps ran, their results, current state]

## What Was Accomplished

[Bullet points of completed work, referencing specific files and results]

## Why This Decision

[Explain why you chose this decision:
- For COMPLETE: evidence that all work is done
- For RETRY: why this step, is there a committed checkpoint before it?
- For ABORT: what makes this unrecoverable
- For DEFER: what transient issue was encountered]

## Guidance for Resumed Step (RETRY only)

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
EOF
}

