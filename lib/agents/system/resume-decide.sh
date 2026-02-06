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

# Valid decision values for backup extraction
agent_valid_results() {
    echo "COMPLETE|RETRY|ABORT|DEFER"
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
| Decision | When to Use |
|----------|-------------|
| **COMPLETE** | All PRD items `[x]`, code committed, logs show build/tests passed. |
| **RETRY:PIPELINE:STEP** | Work remains and can be continued from a specific step. **Default when in doubt.** |
| **DEFER** | Transient failure (OOM, API timeout, rate limit) — system retries after cooldown. |
| **ABORT** | Task is uncompletable after a full retry (see strict criteria below). |

### COMPLETE — all work is done

- All PRD items marked `[x]`, git shows committed work, logs confirm build/tests passed.
- A PR exists (`pr_url.txt`) or the branch has commits ready for one.
- Do NOT run tests/builds yourself — rely on logged evidence only.

### RETRY — resume from a recovery point (default choice)

Format: `RETRY:PIPELINE_NAME:STEP_ID`
- Prefer resuming after the last committed checkpoint (Commit After = Yes).
- If workspace state is uncertain, go back to an earlier checkpoint.
- When the approach was fundamentally wrong, retry from the first pipeline step.

### DEFER — transient infrastructure failure

OOM, API rate limit, network timeout, resource contention. System retries after cooldown.

### ABORT — last resort, strict criteria

ABORT is almost never correct. Choose it ONLY when BOTH conditions are true:
1. The pipeline has already retried from the very first step at least once
   (look for multiple full pipeline runs in worker.log).
2. The task is uncompletable (impossible requirements, architectural impossibility)
   OR has unreasonable scope that renders successful completion unlikely.

**If in doubt between ABORT and RETRY, always choose RETRY** from the first pipeline step.
A fresh attempt is almost always better than giving up.
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

    # Resolve pipeline name (used by prompts and fallback default)
    local pipeline_name=""
    if [ -f "$worker_dir/pipeline-config.json" ]; then
        pipeline_name=$(jq -r '.pipeline.name // ""' "$worker_dir/pipeline-config.json" 2>/dev/null) || true
    fi
    pipeline_name="${pipeline_name:-default}"

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

    # Fallback: parse decision from the stream-JSON result text when XML tags are missing.
    # This handles two failure modes:
    #   1. Agent hit max_turns before outputting tags (error_max_turns)
    #   2. Agent wrote decision in natural language instead of XML tags
    if [ -z "$raw_decision" ]; then
        log_warn "No <decision> or <step> tag found — attempting fallback extraction from result text"
        raw_decision=$(_fallback_extract_decision "$log_file") || true
        if [ -n "$raw_decision" ]; then
            log "Fallback extraction recovered decision: $raw_decision"
            # Use the result text as instructions if we didn't get any
            if [ -z "$instructions" ]; then
                instructions=$(_extract_result_text_from_stream_json "$log_file") || true
            fi
        fi
    fi

    # Backup: resume original session and ask for just the decision tag.
    # This gives the LLM another chance with its full context intact.
    if [ -z "$raw_decision" ]; then
        local session_id
        session_id=$(_extract_session_id_from_log "$log_file") || true
        if [ -n "$session_id" ]; then
            log_warn "Attempting backup session resume to recover decision (session: ${session_id:0:8}...)"
            raw_decision=$(_backup_decision_extraction "$session_id" "$worker_dir" "$pipeline_name") || true
            if [ -n "$raw_decision" ]; then
                log "Backup session resume recovered decision: $raw_decision"
                if [ -z "$instructions" ]; then
                    instructions="Decision recovered via backup session resume."
                fi
            fi
        else
            log_warn "No session_id in log — cannot attempt backup session resume"
        fi
    fi

    # Last resort: default to RETRY from first pipeline step (not ABORT — a fresh
    # attempt is almost always better than giving up)
    if [ -z "$raw_decision" ]; then
        log_error "All decision extraction methods failed — defaulting to RETRY from first step"
        local first_step_id
        first_step_id=$(pipeline_get 0 ".id") || true
        first_step_id="${first_step_id:-planning}"
        local fallback_pipeline="${pipeline_name:-default}"
        raw_decision="RETRY:${fallback_pipeline}:${first_step_id}"
        instructions="${instructions:-Resume-decide agent did not produce a valid decision. Retrying from first pipeline step.}"
    fi

    # Strip whitespace
    raw_decision=$(echo "$raw_decision" | tr -d '[:space:]')

    # Parse decision into components
    local decision="" resume_pipeline="" resume_step_id="" reason=""
    _parse_resume_decision "$raw_decision" "$instructions"

    # After failure-recovery pipeline completes, restore the original pipeline
    # The failure-recovery pipeline is a meta-pipeline for workspace recovery only
    if [ "$resume_pipeline" = "failure-recovery" ]; then
        local orig_pipeline="default"
        if [ -f "$worker_dir/original-pipeline.txt" ]; then
            orig_pipeline=$(cat "$worker_dir/original-pipeline.txt")
        fi
        resume_pipeline="$orig_pipeline"
        raw_decision="RETRY:${orig_pipeline}:${resume_step_id}"
        reason="Resume from $resume_step_id in pipeline $orig_pipeline (after failure recovery)"
    fi

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

# Fallback decision extraction from the stream-JSON result text
#
# When XML tags are missing (agent hit max_turns or forgot tags), attempt to
# recover the decision from the result summary text that Claude CLI writes.
# Searches both the result summary and full assistant text for structured
# RETRY:pipeline:step patterns and contextual decision keywords.
#
# Args:
#   log_file - Path to the stream-JSON log file
#
# Returns: Extracted decision string or empty
_fallback_extract_decision() {
    local log_file="$1"

    # Gather both result text and full assistant text for comprehensive search
    local result_text full_text
    result_text=$(_extract_result_text_from_stream_json "$log_file") || true
    full_text=$(_extract_text_from_stream_json "$log_file") || true

    # Nothing to search
    if [ -z "$result_text" ] && [ -z "$full_text" ]; then
        log_debug "Fallback: no result text or assistant text found in log"
        return 0
    fi

    # Search each text source — result text first (concise), then full text
    local text_source
    for text_source in "$result_text" "$full_text"; do
        [ -z "$text_source" ] && continue

        # Try structured RETRY:pipeline:step pattern (most specific)
        local retry_match
        retry_match=$(echo "$text_source" | grep -oE 'RETRY:[A-Za-z0-9_-]+:[A-Za-z0-9_-]+' | tail -1) || true
        if [ -n "$retry_match" ]; then
            echo "$retry_match"
            return 0
        fi
    done

    # Broader keyword search across both sources
    for text_source in "$result_text" "$full_text"; do
        [ -z "$text_source" ] && continue

        # Match COMPLETE with contextual signals (broader than before)
        if echo "$text_source" | grep -qiE '(decision|verdict|recommend|should be|this is|conclusion|outcome)\b.*\bCOMPLETE\b'; then
            echo "COMPLETE"
            return 0
        fi
        # Standalone COMPLETE on its own line
        if echo "$text_source" | grep -qE '^\s*COMPLETE\s*$'; then
            echo "COMPLETE"
            return 0
        fi

        # Match DEFER with contextual signals
        if echo "$text_source" | grep -qiE '(decision|verdict|recommend|should be|this is|conclusion|outcome)\b.*\bDEFER\b'; then
            echo "DEFER"
            return 0
        fi
        if echo "$text_source" | grep -qE '^\s*DEFER\s*$'; then
            echo "DEFER"
            return 0
        fi
    done

    # Don't match ABORT from natural language — too dangerous as a false positive.
    # If we can't confidently determine the decision, return empty and let the
    # caller fall through to backup session resume or RETRY-from-first-step default.
    return 0
}

# Backup decision extraction via session resume
#
# When all tag and keyword extraction methods fail, resume the original Claude
# session with a focused prompt requesting only the decision tag. This gives the
# LLM another chance to output the decision in the expected format with its full
# conversation context intact.
#
# Args:
#   session_id    - Session ID from the original run
#   worker_dir    - Worker directory for log storage
#   pipeline_name - Pipeline name for RETRY format
#
# Returns: Extracted decision string or empty
_backup_decision_extraction() {
    local session_id="$1"
    local worker_dir="$2"
    local pipeline_name="${3:-default}"

    local prompt
    prompt="STOP. Output ONLY your decision in this exact format — nothing else:

<decision>VALUE</decision>

VALUE must be one of:
- COMPLETE
- RETRY:${pipeline_name}:STEP_ID
- ABORT
- DEFER

Output the <decision> tag NOW. No explanation, no other text."

    local step_id="${WIGGUM_STEP_ID:-resume-decide}"
    local run_id="${RALPH_RUN_ID:-default}"
    local backup_log
    backup_log="$worker_dir/logs/$run_id/${step_id}-backup-$(epoch_now).log"
    mkdir -p "$(dirname "$backup_log")"

    local exit_code=0
    run_agent_resume "$session_id" "$prompt" "$backup_log" 5 || exit_code=$?

    if [ $exit_code -ne 0 ]; then
        log_debug "Backup session resume exited with code $exit_code"
    fi

    # Try tag extraction from backup log
    local decision
    decision=$(_extract_tag_content_from_stream_json "$backup_log" "decision") || true
    if [ -n "$decision" ]; then
        echo "$decision"
        return 0
    fi

    # Try structured patterns in result text and full text
    local backup_result backup_text
    backup_result=$(_extract_result_text_from_stream_json "$backup_log") || true
    backup_text=$(_extract_text_from_stream_json "$backup_log") || true

    local text_source
    for text_source in "$backup_result" "$backup_text"; do
        [ -z "$text_source" ] && continue

        local retry_match
        retry_match=$(echo "$text_source" | grep -oE 'RETRY:[A-Za-z0-9_-]+:[A-Za-z0-9_-]+' | tail -1) || true
        if [ -n "$retry_match" ]; then
            echo "$retry_match"
            return 0
        fi

        # In the backup prompt context, bare keywords are reliable since
        # the prompt only asks for the decision tag with no other text
        local keyword
        keyword=$(echo "$text_source" | grep -oE '\b(COMPLETE|DEFER|ABORT)\b' | tail -1) || true
        if [ -n "$keyword" ]; then
            echo "$keyword"
            return 0
        fi
    done

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
RESUME DECISION AGENT — read-only analyst for interrupted pipeline workers.

CRITICAL: Your response MUST contain <decision>VALUE</decision> and <instructions>...</instructions>
tags. Without these tags your entire analysis is discarded. Output the tags BEFORE any final
commentary — do not save them for last.

WORKER DIRECTORY: $worker_dir

## What You Do

Analyze logs, result files, PRD status, and git history to find the best recovery point.
You do NOT fix anything — you decide where to resume. Be efficient — read only what you
need to make the decision. Do not exhaustively explore every file.

## Execution Restrictions

You are READ-ONLY. Do NOT run tests, builds, linters, or any project code.
Do NOT modify the workspace (\`git checkout/stash/reset/clean/restore/commit/add\` are forbidden).
Allowed: \`git status\`, \`git diff\`, \`git log\`, \`git show\`, reading files, \`ls\`.

## Worker Layout

Key paths under \`$worker_dir/\`:
- \`worker.log\` — primary evidence (look for "PIPELINE STEP:", "STEP COMPLETED:", "Result:", errors)
- \`results/*-result.json\` — per-step gate_result (PASS/FAIL/FIX/SKIP)
- \`prd.md\` — task requirements (\`- [x]\` done, \`- [ ]\` incomplete, \`- [*]\` failed)
- \`summaries/\`, \`conversations/\`, \`reports/\` — additional context
- \`pr_url.txt\` — PR URL if one was created
- \`workspace/\` — code (read-only, check \`git log\` for checkpoints)
- Do NOT read \`logs/\` or \`conversations/\` — these exhaust context and are not needed

## Pipeline Steps

$(_generate_steps_table)

Steps with **Commit After = Yes** are recovery checkpoints — resuming from the next step is safe.

## Decision Values

    <decision>COMPLETE</decision>
    <decision>RETRY:pipeline:step_id</decision>
    <decision>ABORT</decision>
    <decision>DEFER</decision>

## REMINDER — OUTPUT TAGS

End your response with <decision>VALUE</decision> and <instructions>...</instructions>.
These are not optional. The system parses them programmatically.
EOF
}

# Build user prompt — structured methodology for dynamic pipeline exploration
_build_user_prompt() {
    local worker_dir="$1"

    # Extract pipeline name and full config for the prompt
    local pipeline_name="" pipeline_config_body=""
    if [ -f "$worker_dir/pipeline-config.json" ]; then
        pipeline_name=$(jq -r '.pipeline.name // ""' "$worker_dir/pipeline-config.json" 2>/dev/null)
        pipeline_config_body=$(cat "$worker_dir/pipeline-config.json" 2>/dev/null)
    fi
    pipeline_name="${pipeline_name:-default}"
    pipeline_config_body="${pipeline_config_body:-"(pipeline-config.json not found)"}"

    cat << EOF
RESUME ANALYSIS TASK:

Analyze this interrupted worker and determine the **best outcome** — whether the work is done
(COMPLETE), should be resumed from a specific step (RETRY), is unrecoverable (ABORT), or hit
a transient issue (DEFER).

Pipeline: '${pipeline_name}'

## Pipeline Configuration

\`\`\`json
${pipeline_config_body}
\`\`\`

Use the step IDs from this config for RETRY decisions. Steps with \`"commit_after": true\` are
recovery checkpoints — resuming from the step after a checkpoint is always safe.

IMPORTANT: You are a read-only analyst. Do NOT run tests, builds, linters, or any project code.
Make your decision purely from logs, result files, PRD status, and git history.

**Be efficient with your turns.** Read the essential files (worker.log, results, PRD, git log)
in parallel in your first 1-2 turns, then make your decision. Do NOT explore conversations/,
logs/, or other verbose directories. You have a limited turn budget.

## Analysis Steps

Read these files (in parallel where possible), then output your decision:

1. **Worker log + result files + PRD** — Read all three in a single turn:
   - \`$worker_dir/worker.log\` — look for "PIPELINE STEP:", "STEP COMPLETED:", "Result:", errors
   - \`$worker_dir/results/\` — list and read \`*-result.json\` files for gate_result values
   - \`$worker_dir/prd.md\` — count \`- [x]\` done vs \`- [ ]\` incomplete

2. **Git state + PR** — In parallel with step 1:
   - \`git -C $worker_dir/workspace log --oneline -10\`
   - \`git -C $worker_dir/workspace status\`
   - Check \`$worker_dir/pr_url.txt\` for an existing PR

3. **Decision** — After reading the above, immediately output your decision tags.
   Do NOT read additional files unless the above is genuinely ambiguous.

Do NOT read \`logs/\` or \`conversations/\` — these are raw streams that exhaust context.

## Decision Criteria

$(_generate_decision_criteria)

## Important Considerations

- **For RETRY, use format** \`RETRY:${pipeline_name}:STEP_ID\` (pipeline name from above).
- **Trust evidence over claims** — verify workspace diff matches what logs/PRD say.
- **Consider workspace recoverability** — steps with commit_after create safe recovery points.

## MANDATORY OUTPUT — Output these tags immediately after your analysis

<decision>VALUE</decision>
<instructions>Brief analysis and guidance</instructions>

VALUE is one of: COMPLETE, RETRY:${pipeline_name}:STEP_ID, ABORT, or DEFER.
Do NOT wrap in code fences. These tags are parsed programmatically — without them your work is lost.
EOF
}

