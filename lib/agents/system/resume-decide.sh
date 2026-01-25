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
#   - resume-result.json      : Contains PASS, STOP, or FAIL
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
    pipeline_path=$(pipeline_resolve "$project_dir" "" "")

    if [ -n "$pipeline_path" ] && [ -f "$pipeline_path" ]; then
        pipeline_load "$pipeline_path" 2>/dev/null || pipeline_load_builtin_defaults
    else
        pipeline_load_builtin_defaults
    fi
}

# Find the entry point step (the main implementation step, typically system.task-executor)
# Returns the step ID of the first step with agent "system.task-executor", or the first non-disabled step
_find_entry_point_step() {
    local step_count
    step_count=$(pipeline_step_count)

    # First, look for system.task-executor agent
    local i=0
    while [ "$i" -lt "$step_count" ]; do
        local agent enabled_by
        agent=$(pipeline_get "$i" ".agent")
        enabled_by=$(pipeline_get "$i" ".enabled_by" "")

        if [ -z "$enabled_by" ] && [ "$agent" = "system.task-executor" ]; then
            pipeline_get "$i" ".id"
            return 0
        fi
        i=$((i + 1))
    done

    # Fallback: first non-disabled step
    i=0
    while [ "$i" -lt "$step_count" ]; do
        local enabled_by
        enabled_by=$(pipeline_get "$i" ".enabled_by" "")

        if [ -z "$enabled_by" ]; then
            pipeline_get "$i" ".id"
            return 0
        fi
        i=$((i + 1))
    done

    echo "unknown"
}

# Generate the "Pipeline Steps" table dynamically from loaded pipeline
# Returns markdown table via stdout
_generate_steps_table() {
    local step_count entry_step
    step_count=$(pipeline_step_count)
    entry_step=$(_find_entry_point_step)

    echo "| # | Step | Agent | Special Handling |"
    echo "|---|------|-------|------------------|"

    local i=0
    local step_num=1
    while [ "$i" -lt "$step_count" ]; do
        local step_id agent is_readonly enabled_by special=""
        step_id=$(pipeline_get "$i" ".id")
        agent=$(pipeline_get "$i" ".agent")
        is_readonly=$(pipeline_get "$i" ".readonly" "false")
        enabled_by=$(pipeline_get "$i" ".enabled_by" "")

        # Skip disabled-by-default steps in the table
        if [ -n "$enabled_by" ]; then
            i=$((i + 1))
            continue
        fi

        # Determine special handling notes
        # The entry point step (task-executor) cannot resume mid-step
        if [ "$step_id" = "$entry_step" ]; then
            special="Cannot resume mid-step"
        elif [ "$is_readonly" = "true" ]; then
            special="Read-only"
        fi

        echo "| $step_num | \`$step_id\` | $agent | $special |"
        step_num=$((step_num + 1))
        i=$((i + 1))
    done
}

# Generate the "Decision Criteria" table dynamically from loaded pipeline
# Returns markdown table via stdout
_generate_decision_criteria() {
    local step_count entry_step
    step_count=$(pipeline_step_count)
    entry_step=$(_find_entry_point_step)

    echo "| Scenario | Decision |"
    echo "|----------|----------|"

    # Always start with entry-point-related criteria (PRD tasks)
    echo "| PRD has incomplete \\\`- [ ]\\\` tasks | \\\`$entry_step\\\` |"
    echo "| PRD says complete but workspace diff contradicts claims | \\\`$entry_step\\\` |"

    # Build criteria for each step after entry point
    local prev_step="$entry_step"
    local i=0
    while [ "$i" -lt "$step_count" ]; do
        local step_id enabled_by
        step_id=$(pipeline_get "$i" ".id")
        enabled_by=$(pipeline_get "$i" ".enabled_by" "")

        # Skip disabled-by-default and entry point (handled above)
        if [ -n "$enabled_by" ] || [ "$step_id" = "$entry_step" ]; then
            i=$((i + 1))
            continue
        fi

        # Generate criterion: if prev_step complete but this step never ran
        if [ "$prev_step" != "$entry_step" ]; then
            echo "| ${prev_step^} complete, $step_id never ran or has no result file | \\\`$step_id\\\` |"
        else
            echo "| ${entry_step^} complete, $step_id never ran or has no result file | \\\`$step_id\\\` |"
        fi

        prev_step="$step_id"
        i=$((i + 1))
    done

    # Final criteria
    echo "| All phases complete with outputs | \\\`ABORT\\\` |"
    echo "| Fundamental issue (impossible task, repeated failures, bad PRD) | \\\`ABORT\\\` |"
}

# Get list of valid step IDs for the <step> tag validation
_get_valid_steps() {
    local step_count
    step_count=$(pipeline_step_count)

    # Collect all non-disabled step IDs
    local steps=""
    local i=0
    while [ "$i" -lt "$step_count" ]; do
        local step_id enabled_by
        step_id=$(pipeline_get "$i" ".id")
        enabled_by=$(pipeline_get "$i" ".enabled_by" "")

        if [ -z "$enabled_by" ]; then
            if [ -z "$steps" ]; then
                steps="$step_id"
            else
                steps="$steps|$step_id"
            fi
        fi
        i=$((i + 1))
    done

    echo "$steps"
}

# Main entry point
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    # $3 is max_iterations (unused — this agent runs once)
    local max_turns="${4:-25}"

    # Setup logging to worker.log
    export LOG_FILE="$worker_dir/worker.log"

    log "Resume-decide agent analyzing previous run..."

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

    # Extract decision from the JSON stream log (same pattern as other agents)
    _extract_decision "$worker_dir"

    if [ $agent_exit -ne 0 ]; then
        log_warn "Resume-decide agent exited with code $agent_exit"
    fi

    # Verify outputs exist
    if [ ! -f "$worker_dir/resume-step.txt" ] || [ ! -s "$worker_dir/resume-step.txt" ]; then
        log_error "resume-decide failed to produce resume-step.txt"
        echo "ABORT" > "$worker_dir/resume-step.txt"
        echo "Resume-decide agent failed to produce a decision." > "$worker_dir/reports/resume-instructions.md"
        agent_write_result "$worker_dir" "failure" 1 '{"gate_result":"FAIL"}'
        return 1
    fi

    local step
    step=$(cat "$worker_dir/resume-step.txt")
    log "Resume decision: $step"

    # Archive artifacts from the resume point onward (not earlier phases)
    if [ "$step" != "ABORT" ]; then
        archive_from_step "$worker_dir" "$step"
        agent_write_result "$worker_dir" "success" 0 "$(printf '{"gate_result":"PASS","resume_step":"%s"}' "$step")"
    else
        agent_write_result "$worker_dir" "success" 0 '{"gate_result":"STOP","resume_step":"ABORT"}'
    fi

    return 0
}

# Archive artifacts from the resume step onward using timestamp comparison.
# Finds the conversation log for the resume step, uses its mtime as reference,
# and archives all artifacts created at or after that point.
# Earlier phase artifacts are kept (they represent completed work).
# Workspace is LEFT UNTOUCHED (it has the actual code changes).
archive_from_step() {
    local worker_dir="$1"
    local resume_step="$2"
    local archive_dir
    archive_dir="$worker_dir/history/resume-$(date +%s)"

    # Map resume step to its conversation log prefix
    # All agents use their step ID as the prefix (no special cases)
    local step_prefix="${resume_step}-"

    # Find the earliest conversation log for the resume step (timestamp reference)
    local reference_file=""
    if [ -d "$worker_dir/conversations" ]; then
        reference_file=$(ls -tr "$worker_dir/conversations/${step_prefix}"*.md 2>/dev/null | head -1)
    fi

    if [ -z "$reference_file" ]; then
        log_warn "No conversation log found for step '$resume_step', archiving all run artifacts"
        _archive_all "$worker_dir" "$archive_dir"
        return
    fi

    mkdir -p "$archive_dir"

    # Always archive run-level artifacts (they span the whole run, will be regenerated)
    mv "$worker_dir/logs" "$archive_dir/" 2>/dev/null || true
    mv "$worker_dir/worker.log" "$archive_dir/" 2>/dev/null || true

    # Archive conversation files with mtime >= reference file
    if [ -d "$worker_dir/conversations" ]; then
        mkdir -p "$archive_dir/conversations"
        for f in "$worker_dir/conversations/"*.md; do
            [ -f "$f" ] || continue
            if [ ! "$f" -ot "$reference_file" ]; then
                mv "$f" "$archive_dir/conversations/"
            fi
        done
    fi

    # Archive results/ and reports/ directories
    for subdir in results reports; do
        [ -d "$worker_dir/$subdir" ] || continue
        mkdir -p "$archive_dir/$subdir"
        for f in "$worker_dir/$subdir"/*; do
            [ -f "$f" ] || continue
            if [ ! "$f" -ot "$reference_file" ]; then
                mv "$f" "$archive_dir/$subdir/"
            fi
        done
        # Remove subdir if now empty
        rmdir "$worker_dir/$subdir" 2>/dev/null || true
    done

    # Archive artifact directories whose contents are entirely from the resume point onward
    for dir in summaries checkpoints supervisors; do
        [ -d "$worker_dir/$dir" ] || continue
        local dominated=true
        while IFS= read -r f; do
            if [ "$f" -ot "$reference_file" ]; then
                dominated=false
                break
            fi
        done < <(find "$worker_dir/$dir" -type f 2>/dev/null)
        if [ "$dominated" = true ]; then
            mv "$worker_dir/$dir" "$archive_dir/"
        fi
    done

    # Preserve resume-instructions.md — needed by the resumed worker
    if [ -f "$archive_dir/reports/resume-instructions.md" ]; then
        mkdir -p "$worker_dir/reports"
        mv "$archive_dir/reports/resume-instructions.md" "$worker_dir/reports/"
    fi
    log "Archived artifacts from step '$resume_step' (ref: $(basename "$reference_file")) to $(basename "$archive_dir")"
}

# Fallback: archive all run artifacts when no reference file exists
_archive_all() {
    local worker_dir="$1"
    local archive_dir="$2"

    mkdir -p "$archive_dir"
    mv "$worker_dir/logs" "$archive_dir/" 2>/dev/null || true
    mv "$worker_dir/summaries" "$archive_dir/" 2>/dev/null || true
    mv "$worker_dir/checkpoints" "$archive_dir/" 2>/dev/null || true
    mv "$worker_dir/conversations" "$archive_dir/" 2>/dev/null || true
    mv "$worker_dir/supervisors" "$archive_dir/" 2>/dev/null || true
    mv "$worker_dir/worker.log" "$archive_dir/" 2>/dev/null || true
    mv "$worker_dir/results" "$archive_dir/" 2>/dev/null || true
    mv "$worker_dir/reports" "$archive_dir/" 2>/dev/null || true
    log "Archived all run artifacts to $(basename "$archive_dir")"
}

# System prompt for the resume-decide agent
_get_system_prompt() {
    local worker_dir="$1"

    cat << EOF
RESUME DECISION AGENT:

You determine where an interrupted worker should resume from. You do NOT fix issues - only analyze and decide.

WORKER DIRECTORY: $worker_dir

## Core Principle: EVIDENCE OVER ASSUMPTIONS

Trust nothing about the worker's state without verifying it in the logs and filesystem.
A phase claiming success means nothing if its output files are missing.
An interrupted phase needs evidence of WHERE it stopped, not just THAT it stopped.

## Worker Directory Layout

\`\`\`
$worker_dir/
├── worker.log           ← Phase-level status log (YOUR PRIMARY EVIDENCE)
├── prd.md               ← Task requirements (check completion status)
├── workspace/           ← Code changes (PRESERVED - do not modify)
├── conversations/       ← Converted conversation logs from previous run
│   ├── execution-*.md   ← Main work loop conversations
│   ├── audit-*.md       ← Security audit conversations
│   ├── test-*.md        ← Test coverage conversations
│   └── ...              ← Other sub-agent conversations
├── logs/                ← Raw JSON stream logs (DO NOT READ - too large)
├── summaries/           ← Iteration summaries
├── results/             ← Phase result files (PASS/FAIL/FIX/etc.)
└── reports/             ← Phase report files
\`\`\`

## Pipeline Steps (in execution order)

$(_generate_steps_table)

## Phase Completion Evidence

| Phase | Log Pattern (in worker.log) | Output File |
|-------|---------------------------|-------------|
| execution | "Task completed successfully" or "Ralph loop finished" | summaries/summary.txt |
| audit | "Security audit result: PASS\|FIX\|FAIL" | results/*-security-audit-result.json |
| test | "Test coverage result: PASS\|FAIL\|SKIP" | results/*-test-coverage-result.json |
| docs | "Documentation writer result:" | results/*-documentation-writer-result.json |
| validation | "Validation review completed with result:" | results/*-validation-review-result.json |
| finalization | "PR created:" or "Commit created" | results/*-system.task-worker-result.json |

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

# Build user prompt — structured methodology matching validation-review/security-audit patterns
_build_user_prompt() {
    local worker_dir="$1"

    # List available conversation files for the agent's awareness
    local conv_files=""
    if [ -d "$worker_dir/conversations" ]; then
        conv_files=$(ls "$worker_dir/conversations/"*.md 2>/dev/null | sort || true)
    fi

    # List result files that exist (epoch-named JSON results)
    local result_files=""
    result_files=$(ls "$worker_dir/results/"*-result.json 2>/dev/null | sort || true)

    cat << EOF
RESUME ANALYSIS TASK:

Determine where this interrupted worker should resume from. Trust nothing - verify everything.

## Step 1: Establish Ground Truth

Read the worker.log to understand what phases actually ran:

\`\`\`
$worker_dir/worker.log
\`\`\`

For EACH phase, look for:
- **Start marker**: "Running security audit..." / "Running test generation..." / etc.
- **Completion marker**: "result: PASS" / "result: FAIL" / etc.
- **Error markers**: "ERROR" / non-zero exit codes / missing output

## Step 2: Verify Phase Outputs

Cross-reference log claims against actual output files:

$(if [ -n "$result_files" ]; then
    echo "Result files found:"
    echo "$result_files" | while read -r f; do echo "- $f"; done
else
    echo "No result files found (phases may not have completed)."
fi)

For each phase that claims completion in the log, verify its output file EXISTS and is NON-EMPTY.
A phase is NOT complete if its output file is missing, even if the log says it ran.

## Step 3: Check PRD Completion Status

\`\`\`
$worker_dir/prd.md
\`\`\`

Count:
- \`- [x]\` tasks (completed)
- \`- [ ]\` tasks (incomplete)
- \`- [*]\` tasks (blocked/failed)

If ANY tasks are \`- [ ]\`, execution is NOT complete.

## Step 4: Verify Workspace Matches Claims

If execution appears complete, verify the workspace reflects what was claimed:

\`\`\`bash
cd $worker_dir/workspace && git diff --name-only   # What files actually changed
cd $worker_dir/workspace && git diff --stat         # Summary of changes
\`\`\`

Cross-reference against:
- The PRD task descriptions (what SHOULD have been modified)
- The summary file (summaries/summary.txt - what was CLAIMED to be modified)
- Conversation logs (what the agent SAID it did)

For each claimed modification:
1. **Does the file appear in git diff?** If not, the change was never made or was reverted
2. **Does the diff content match the description?** A file listed as "added new endpoint" should contain route/handler code, not just a comment
3. **Are claimed new files actually present?** Check \`git status\` for untracked files

If workspace state contradicts claims (files missing, changes don't match descriptions), execution is NOT truly complete — resume from \`execution\`.

## Step 5: Identify the Interruption Point

The resume step is the EARLIEST phase that:
- Started but did not produce its output file, OR
- Never started (no log entry), OR
- Produced a FAIL/error result that needs retry, OR
- Claims completion but workspace evidence contradicts it

## Step 6: Gather Context for Instructions

If resuming from a post-execution step, read the relevant conversation logs for context:

$(if [ -n "$conv_files" ]; then
    echo "Available conversation logs:"
    echo "$conv_files" | while read -r f; do echo "- $f"; done
else
    echo "No conversation logs found."
fi)

Read ONLY the conversations relevant to understanding what was accomplished (not the failed phase's log).

## Decision Criteria

$(_generate_decision_criteria)

## Common Mistakes to Avoid

- **Don't trust PRD checkboxes alone** — verify workspace diff actually contains the claimed changes
- **Don't resume from a post-execution step if the diff is empty** — execution didn't actually produce work
- **Don't skip a phase** — always resume from the EARLIEST incomplete phase
- **Don't assume a phase ran** just because the next phase started (it may have been skipped)
- **Don't read logs/ directory** — these are raw JSON streams that will exhaust your context

## Output Format

<step>STEP_NAME</step>

<instructions>
## What Was Accomplished

[Bullet points of completed work, with specific files modified and patterns used]

## Current State

[Description of workspace state: what code exists, what's been committed vs uncommitted]

## What Needs to Happen Now

[Specific guidance for the resumed phase:
- If execution: which PRD tasks remain, what patterns to follow
- If audit/test/docs/validation: context about what was implemented
- If finalization: what to commit, branch naming, PR description context]

## Warnings

[Issues from the previous run to be aware of:
- Errors encountered
- Partial work that may need cleanup
- Patterns or decisions that should be maintained]
</instructions>

The <step> tag MUST be exactly one of the pipeline step IDs shown in the table above, or ABORT
EOF
}

# Extract decision from the resume-decide JSON stream log
# Uses shared agent-base.sh utilities (same pattern as security-audit, test-coverage, etc.)
_extract_decision() {
    local worker_dir="$1"
    local step_id="${WIGGUM_STEP_ID:-resume-decide}"

    # Find the latest log file matching the step pattern (unified agent interface)
    local log_file
    log_file=$(find "$worker_dir/logs" -name "${step_id}-*.log" ! -name "*summary*" -printf '%T@ %p\n' 2>/dev/null | sort -rn | head -1 | cut -d' ' -f2-)

    if [ -z "$log_file" ] || [ ! -f "$log_file" ]; then
        log_error "No resume-decide log file found in $worker_dir/logs"
        echo "ABORT" > "$worker_dir/resume-step.txt"
        echo "No decision log produced." > "$worker_dir/reports/resume-instructions.md"
        return 1
    fi

    local log_size
    log_size=$(wc -c < "$log_file" 2>/dev/null || echo 0)
    log "Resume-decide log: $log_file ($log_size bytes)"

    # Extract assistant text from stream-JSON (shared utility)
    local full_text
    full_text=$(_extract_text_from_stream_json "$log_file") || true

    if [ -z "$full_text" ]; then
        log_error "No assistant text found in resume-decide log"
        echo "ABORT" > "$worker_dir/resume-step.txt"
        echo "Failed to extract decision from agent output." > "$worker_dir/reports/resume-instructions.md"
        return 1
    fi

    # Extract step value from <step>...</step> (last occurrence, like _extract_result_value)
    # Use dynamic step list from pipeline config
    local valid_steps
    valid_steps=$(_get_valid_steps)
    local step
    step=$(echo "$full_text" | \
        grep -oP "(?<=<step>)(${valid_steps}|ABORT)(?=</step>)" 2>/dev/null | \
        tail -1) || true

    if [ -z "$step" ]; then
        log_error "No valid <step> tag found in resume-decide output"
        echo "ABORT" > "$worker_dir/resume-step.txt"
        echo "Agent did not produce a valid step decision." > "$worker_dir/reports/resume-instructions.md"
        return 1
    fi

    echo "$step" > "$worker_dir/resume-step.txt"

    # Extract instructions from <instructions>...</instructions> (shared utility)
    local instructions
    instructions=$(_extract_tag_content_from_stream_json "$log_file" "instructions") || true

    if [ -z "$instructions" ]; then
        instructions="Resuming from step: $step. No detailed instructions available."
    fi

    echo "$instructions" > "$worker_dir/reports/resume-instructions.md"

    log "Extracted decision: step=$step"
    return 0
}
