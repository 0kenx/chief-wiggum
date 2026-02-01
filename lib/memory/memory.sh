#!/usr/bin/env bash
# =============================================================================
# memory.sh - Long-term memory service for cross-task knowledge
#
# Extracts knowledge from completed task executions. Deterministic metrics
# (pass rates, durations, iteration counts) are computed by Bash/jq and
# stored in .json files. LLM observations are written by the memory-analyst
# agent into .md files.
#
# Usage:
#   source "$WIGGUM_HOME/lib/memory/memory.sh"
#   memory_init "$RALPH_DIR"
#   memory_collect_stats "$worker_dir" "$RALPH_DIR"
#   memory_queue_worker "$worker_dir"
#   memory_process_pending "$RALPH_DIR"
# =============================================================================
set -euo pipefail

[ -n "${_MEMORY_LOADED:-}" ] && return 0
_MEMORY_LOADED=1

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"

# =============================================================================
# INITIALIZATION
# =============================================================================

# Create full memory directory structure and scaffold INDEX.md files
#
# Args:
#   ralph_dir - Path to .ralph directory
memory_init() {
    local ralph_dir="$1"
    local memory_dir="$ralph_dir/memory"

    mkdir -p \
        "$memory_dir/patterns/errors" \
        "$memory_dir/patterns/fixes" \
        "$memory_dir/patterns/tests" \
        "$memory_dir/patterns/security" \
        "$memory_dir/patterns/environment" \
        "$memory_dir/agents" \
        "$memory_dir/tasks"

    # Scaffold root INDEX.md if missing
    if [ ! -f "$memory_dir/INDEX.md" ]; then
        _memory_scaffold_root_index "$memory_dir"
    fi

    # Scaffold ESCALATED.md if missing
    if [ ! -f "$memory_dir/ESCALATED.md" ]; then
        cat > "$memory_dir/ESCALATED.md" << 'EOF'
# Escalated Issues

Issues below were identified by automated analysis and require external intervention.
The agent system cannot resolve these on its own.

## OPEN

## RESOLVED
EOF
    fi

    # Scaffold category INDEX.md files if missing
    _memory_scaffold_patterns_index "$memory_dir"
    _memory_scaffold_category_index "$memory_dir/patterns/errors" "Error Patterns"
    _memory_scaffold_category_index "$memory_dir/patterns/fixes" "Fix Patterns"
    _memory_scaffold_category_index "$memory_dir/patterns/tests" "Test Insights"
    _memory_scaffold_category_index "$memory_dir/patterns/security" "Security Patterns"
    _memory_scaffold_category_index "$memory_dir/patterns/environment" "Environment Issues"
    _memory_scaffold_category_index "$memory_dir/agents" "Agent Performance"
    _memory_scaffold_category_index "$memory_dir/tasks" "Task History"

    # Scaffold global stats.json if missing
    if [ ! -f "$memory_dir/stats.json" ]; then
        cat > "$memory_dir/stats.json" << EOF
{
  "version": "1.0",
  "updated_at": "$(iso_now)",
  "tasks_analyzed": 0,
  "success_rate": 0,
  "avg_fix_cycles": 0,
  "avg_total_duration_s": 0,
  "total_token_cost": 0
}
EOF
    fi

    # Ensure pending.list exists
    touch "$memory_dir/pending.list"
}

# =============================================================================
# PHASE A: DETERMINISTIC STATS COLLECTION
# =============================================================================

# Collect deterministic stats from a completed worker
#
# Parses results/*.json files to build task and agent stats.
# No LLM involved - pure jq processing.
#
# Args:
#   worker_dir - Worker directory path
#   ralph_dir  - Path to .ralph directory
memory_collect_stats() {
    local worker_dir="$1"
    local ralph_dir="$2"
    local memory_dir="$ralph_dir/memory"

    # Ensure memory is initialized
    [ -d "$memory_dir" ] || memory_init "$ralph_dir"

    # Extract task ID from worker dir name
    local worker_id task_id
    worker_id=$(basename "$worker_dir")
    task_id=""
    if [[ "$worker_id" =~ ^worker-([A-Za-z]{2,10}-[0-9]{1,4})- ]]; then
        task_id="${BASH_REMATCH[1]}"
    fi

    if [ -z "$task_id" ]; then
        log_warn "memory: Could not extract task ID from $worker_id"
        return 1
    fi

    # Create task directory
    local task_dir="$memory_dir/tasks/$task_id"
    mkdir -p "$task_dir"

    # Build task stats.json from results
    _memory_build_task_stats "$worker_dir" "$task_id" "$task_dir"

    # Rebuild agent stats from all task stats
    memory_rebuild_agent_stats "$memory_dir"

    # Rebuild global stats from agent stats
    memory_rebuild_global_stats "$memory_dir"

    # Regenerate INDEX.md files
    memory_rebuild_indexes "$memory_dir"

    log_debug "memory: Collected stats for $task_id"
}

# Build task-level stats.json from worker result files
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier
#   task_dir   - Output task directory in memory
_memory_build_task_stats() {
    local worker_dir="$1"
    local task_id="$2"
    local task_dir="$3"

    local worker_id
    worker_id=$(basename "$worker_dir")

    # Collect all result files
    local results_dir="$worker_dir/results"
    local outcome="success"
    local total_duration=0
    local total_iterations=0
    local fix_cycles=0
    local token_cost=0
    local pipeline_json="{}"
    local files_touched="[]"

    if [ -d "$results_dir" ]; then
        # Process each result file to build pipeline stats
        local pipeline_entries=""
        local result_files
        result_files=$(find "$results_dir" -name "*.json" -type f 2>/dev/null | sort || true)

        for result_file in $result_files; do
            [ -f "$result_file" ] || continue

            local agent_type gate_result duration iterations
            agent_type=$(jq -r '.agent_type // ""' "$result_file" 2>/dev/null)
            agent_type="${agent_type:-unknown}"
            gate_result=$(jq -r '.outputs.gate_result // .status // ""' "$result_file" 2>/dev/null)
            gate_result="${gate_result:-unknown}"
            duration=$(jq -r '.duration_seconds // 0' "$result_file" 2>/dev/null)
            duration="${duration:-0}"
            iterations=$(jq -r '.iterations_completed // 1' "$result_file" 2>/dev/null)
            iterations="${iterations:-1}"

            # Ensure numeric
            [[ "$duration" =~ ^[0-9]+$ ]] || duration=0
            [[ "$iterations" =~ ^[0-9]+$ ]] || iterations=1

            total_duration=$((total_duration + duration))
            total_iterations=$((total_iterations + iterations))

            # Count fix cycles (FIX results)
            if [ "$gate_result" = "FIX" ]; then
                ((++fix_cycles)) || true
            fi

            # Track failures
            if [ "$gate_result" = "FAIL" ]; then
                outcome="failure"
            fi

            # Extract step_id from agent_type for pipeline key
            local step_key
            step_key=$(echo "$agent_type" | sed 's/.*\.//' | tr '-' '_')

            # Build pipeline entry
            local entry
            entry=$(jq -n \
                --arg result "$gate_result" \
                --argjson iterations "$iterations" \
                --argjson duration "$duration" \
                '{result: $result, iterations: $iterations, duration_s: $duration}')

            if [ -z "$pipeline_entries" ]; then
                pipeline_entries=$(jq -n --arg key "$step_key" --argjson val "$entry" '{($key): $val}')
            else
                pipeline_entries=$(echo "$pipeline_entries" | jq --arg key "$step_key" --argjson val "$entry" '. + {($key): $val}')
            fi
        done

        pipeline_json="${pipeline_entries:-{\}}"
    fi

    # Extract token cost from metrics.txt if available
    if [ -f "$worker_dir/metrics.txt" ]; then
        local cost_line
        cost_line=$(grep -i 'cost' "$worker_dir/metrics.txt" 2>/dev/null | tail -1 || true)
        if [ -n "$cost_line" ]; then
            token_cost=$(echo "$cost_line" | grep -oE '[0-9]+\.?[0-9]*' | tail -1 || echo "0")
        fi
    fi
    token_cost="${token_cost:-0}"

    # Extract files touched from git diff if workspace exists
    if [ -d "$worker_dir/workspace" ]; then
        local touched
        touched=$(git -C "$worker_dir/workspace" diff --name-only origin/main 2>/dev/null || true)
        if [ -n "$touched" ]; then
            files_touched=$(echo "$touched" | jq -R -s 'split("\n") | map(select(. != ""))')
        fi
    fi

    # Write task stats.json
    jq -n \
        --arg task_id "$task_id" \
        --arg worker_id "$worker_id" \
        --arg worker_dir "$worker_dir" \
        --arg outcome "$outcome" \
        --argjson total_duration "$total_duration" \
        --argjson total_iterations "$total_iterations" \
        --argjson fix_cycles "$fix_cycles" \
        --argjson token_cost "$token_cost" \
        --argjson pipeline "$pipeline_json" \
        --argjson files_touched "$files_touched" \
        --arg analyzed_at "$(iso_now)" \
        '{
            task_id: $task_id,
            worker_id: $worker_id,
            worker_dir: $worker_dir,
            outcome: $outcome,
            total_duration_s: $total_duration,
            total_iterations: $total_iterations,
            fix_cycles: $fix_cycles,
            token_cost: $token_cost,
            pipeline: $pipeline,
            files_touched: $files_touched,
            analyzed_at: $analyzed_at
        }' > "$task_dir/stats.json"
}

# =============================================================================
# AGENT STATS REBUILD
# =============================================================================

# Recompute agents/*/stats.json from all tasks/*/stats.json
#
# Args:
#   memory_dir - Path to .ralph/memory directory
memory_rebuild_agent_stats() {
    local memory_dir="$1"
    local tasks_dir="$memory_dir/tasks"

    [ -d "$tasks_dir" ] || return 0

    # Collect per-agent stats from all task stats
    # Use a temporary file to aggregate across tasks
    local tmp_dir
    tmp_dir=$(mktemp -d)

    local task_stats_files
    task_stats_files=$(find "$tasks_dir" -name "stats.json" -type f 2>/dev/null || true)

    for stats_file in $task_stats_files; do
        [ -f "$stats_file" ] || continue

        # Extract pipeline entries (each key is an agent step)
        local pipeline_keys
        pipeline_keys=$(jq -r '.pipeline // {} | keys[]' "$stats_file" 2>/dev/null || true)

        for step_key in $pipeline_keys; do
            [ -n "$step_key" ] || continue

            local result duration iterations
            result=$(jq -r ".pipeline[\"$step_key\"].result // \"\"" "$stats_file" 2>/dev/null)
            duration=$(jq -r ".pipeline[\"$step_key\"].duration_s // 0" "$stats_file" 2>/dev/null)
            iterations=$(jq -r ".pipeline[\"$step_key\"].iterations // 1" "$stats_file" 2>/dev/null)

            # Ensure numeric
            [[ "$duration" =~ ^[0-9]+$ ]] || duration=0
            [[ "$iterations" =~ ^[0-9]+$ ]] || iterations=1

            # Append to agent's data file
            local agent_name
            agent_name=$(echo "$step_key" | tr '_' '-')
            echo "$result $duration $iterations" >> "$tmp_dir/$agent_name.dat"
        done
    done

    # Build stats.json for each agent that has data
    local dat_files
    dat_files=$(find "$tmp_dir" -name "*.dat" -type f 2>/dev/null || true)

    for dat_file in $dat_files; do
        [ -f "$dat_file" ] || continue

        local agent_name
        agent_name=$(basename "$dat_file" .dat)
        local agent_dir="$memory_dir/agents/$agent_name"
        mkdir -p "$agent_dir"

        local runs=0 pass_count=0 fix_count=0 fail_count=0
        local total_iters=0 total_dur=0
        local min_dur=999999999 max_dur=0

        while read -r result duration iters; do
            ((++runs)) || true
            total_dur=$((total_dur + duration))
            total_iters=$((total_iters + iters))

            [ "$duration" -lt "$min_dur" ] && min_dur=$duration
            [ "$duration" -gt "$max_dur" ] && max_dur=$duration

            case "$result" in
                PASS|SKIP) ((++pass_count)) || true ;;
                FIX)  ((++fix_count)) || true ;;
                FAIL) ((++fail_count)) || true ;;
            esac
        done < "$dat_file"

        # Compute rates (using fixed-point: multiply by 10000, divide later)
        local pass_rate=0 fix_rate=0 fail_rate=0
        local avg_iterations=0 avg_duration=0

        if [ "$runs" -gt 0 ]; then
            pass_rate=$(( (pass_count * 10000) / runs ))
            fix_rate=$(( (fix_count * 10000) / runs ))
            fail_rate=$(( (fail_count * 10000) / runs ))
            avg_iterations=$(( (total_iters * 100) / runs ))
            avg_duration=$((total_dur / runs))
        fi

        [ "$min_dur" -eq 999999999 ] && min_dur=0

        jq -n \
            --arg agent_type "$agent_name" \
            --argjson runs "$runs" \
            --arg pass_rate "$(printf '%d.%02d' $((pass_rate / 100)) $((pass_rate % 100)))" \
            --arg fix_rate "$(printf '%d.%02d' $((fix_rate / 100)) $((fix_rate % 100)))" \
            --arg fail_rate "$(printf '%d.%02d' $((fail_rate / 100)) $((fail_rate % 100)))" \
            --arg avg_iterations "$(printf '%d.%01d' $((avg_iterations / 100)) $(( (avg_iterations % 100) / 10 )))" \
            --argjson avg_duration "$avg_duration" \
            --argjson min_duration "$min_dur" \
            --argjson max_duration "$max_dur" \
            --arg updated_at "$(iso_now)" \
            '{
                agent_type: $agent_type,
                runs: $runs,
                pass_rate: ($pass_rate | tonumber),
                fix_rate: ($fix_rate | tonumber),
                fail_rate: ($fail_rate | tonumber),
                avg_iterations: ($avg_iterations | tonumber),
                avg_duration_s: $avg_duration,
                min_duration_s: $min_duration,
                max_duration_s: $max_duration,
                updated_at: $updated_at
            }' > "$agent_dir/stats.json"
    done

    rm -rf "$tmp_dir"
}

# =============================================================================
# GLOBAL STATS REBUILD
# =============================================================================

# Recompute global stats.json from all tasks/*/stats.json
#
# Args:
#   memory_dir - Path to .ralph/memory directory
memory_rebuild_global_stats() {
    local memory_dir="$1"
    local tasks_dir="$memory_dir/tasks"

    local tasks_analyzed=0
    local success_count=0
    local total_fix_cycles=0
    local total_duration=0
    local total_cost=0

    if [ -d "$tasks_dir" ]; then
        local task_stats_files
        task_stats_files=$(find "$tasks_dir" -name "stats.json" -type f 2>/dev/null || true)

        for stats_file in $task_stats_files; do
            [ -f "$stats_file" ] || continue
            ((++tasks_analyzed)) || true

            local outcome fix_cycles duration cost
            outcome=$(jq -r '.outcome // ""' "$stats_file" 2>/dev/null)
            fix_cycles=$(jq -r '.fix_cycles // 0' "$stats_file" 2>/dev/null)
            duration=$(jq -r '.total_duration_s // 0' "$stats_file" 2>/dev/null)
            cost=$(jq -r '.token_cost // 0' "$stats_file" 2>/dev/null)

            fix_cycles="${fix_cycles:-0}"
            duration="${duration:-0}"
            cost="${cost:-0}"
            [[ "$fix_cycles" =~ ^[0-9]+$ ]] || fix_cycles=0
            [[ "$duration" =~ ^[0-9]+$ ]] || duration=0

            [ "$outcome" = "success" ] && ((++success_count)) || true
            total_fix_cycles=$((total_fix_cycles + fix_cycles))
            total_duration=$((total_duration + duration))

            # Cost can be decimal - accumulate as string for jq
            total_cost=$(echo "$total_cost + $cost" | bc 2>/dev/null || echo "$total_cost")
        done
    fi

    # Compute rates
    local success_rate=0 avg_fix_cycles=0 avg_duration=0
    if [ "$tasks_analyzed" -gt 0 ]; then
        success_rate=$(( (success_count * 100) / tasks_analyzed ))
        avg_fix_cycles=$(( (total_fix_cycles * 10) / tasks_analyzed ))
        avg_duration=$((total_duration / tasks_analyzed))
    fi

    jq -n \
        --arg version "1.0" \
        --arg updated_at "$(iso_now)" \
        --argjson tasks_analyzed "$tasks_analyzed" \
        --arg success_rate "$(printf '0.%02d' "$success_rate")" \
        --arg avg_fix_cycles "$(printf '%d.%01d' $((avg_fix_cycles / 10)) $((avg_fix_cycles % 10)))" \
        --argjson avg_total_duration_s "$avg_duration" \
        --argjson total_token_cost "$total_cost" \
        '{
            version: $version,
            updated_at: $updated_at,
            tasks_analyzed: $tasks_analyzed,
            success_rate: ($success_rate | tonumber),
            avg_fix_cycles: ($avg_fix_cycles | tonumber),
            avg_total_duration_s: $avg_total_duration_s,
            total_token_cost: $total_token_cost
        }' > "$memory_dir/stats.json"
}

# =============================================================================
# QUEUE MANAGEMENT
# =============================================================================

# Append worker directory to pending.list for LLM analysis
#
# Deduplicates entries. Thread-safe via flock.
#
# Args:
#   worker_dir - Worker directory path
memory_queue_worker() {
    local worker_dir="$1"
    local ralph_dir
    ralph_dir=$(realpath "$worker_dir/../.." 2>/dev/null || echo "")
    [ -n "$ralph_dir" ] || return 1

    local memory_dir="$ralph_dir/memory"
    local pending_list="$memory_dir/pending.list"

    # Ensure memory directory exists
    [ -d "$memory_dir" ] || memory_init "$ralph_dir"

    # Deduplicate: skip if already queued
    if [ -f "$pending_list" ] && grep -qF "$worker_dir" "$pending_list" 2>/dev/null; then
        log_debug "memory: Worker already queued: $(basename "$worker_dir")"
        return 0
    fi

    # Append with flock for thread safety
    (
        flock -w 5 200 || { log_warn "memory: Could not acquire lock for pending.list"; return 1; }
        # Re-check after lock
        if ! grep -qF "$worker_dir" "$pending_list" 2>/dev/null; then
            echo "$worker_dir" >> "$pending_list"
        fi
    ) 200>"$pending_list.lock"
}

# Process next pending worker through memory-analyst agent
#
# Pops the first entry from pending.list and runs the memory-analyst agent.
#
# Args:
#   ralph_dir - Path to .ralph directory
#
# Returns: 0 if processed, 1 if nothing to process
memory_process_pending() {
    local ralph_dir="$1"
    local memory_dir="$ralph_dir/memory"
    local pending_list="$memory_dir/pending.list"

    [ -f "$pending_list" ] || return 1

    # Pop first entry atomically
    local worker_dir=""
    (
        flock -w 5 200 || return 1

        worker_dir=$(head -1 "$pending_list" 2>/dev/null || true)
        if [ -n "$worker_dir" ]; then
            # Remove first line
            local tmp
            tmp=$(tail -n +2 "$pending_list" 2>/dev/null || true)
            echo "$tmp" > "$pending_list"
        fi

        # Write worker_dir to a temp file for the outer scope
        echo "$worker_dir" > "$pending_list.current"
    ) 200>"$pending_list.lock"

    worker_dir=$(cat "$pending_list.current" 2>/dev/null || true)
    rm -f "$pending_list.current"

    [ -n "$worker_dir" ] || return 1
    [ -d "$worker_dir" ] || return 1

    # Extract task ID
    local worker_id task_id
    worker_id=$(basename "$worker_dir")
    task_id=""
    if [[ "$worker_id" =~ ^worker-([A-Za-z]{2,10}-[0-9]{1,4})- ]]; then
        task_id="${BASH_REMATCH[1]}"
    fi
    [ -n "$task_id" ] || return 1

    # Skip if already analyzed
    if memory_is_analyzed "$memory_dir" "$task_id"; then
        log_debug "memory: Task $task_id already analyzed, skipping"
        return 0
    fi

    log "memory: Running analysis for $task_id"

    # Run the memory-analyst agent
    # The agent runs outside worker context, with memory dir as workspace
    source "$WIGGUM_HOME/lib/worker/agent-registry.sh"

    # Create a minimal worker dir for the agent
    local analyst_worker_dir="$ralph_dir/memory/.analyst-work"
    mkdir -p "$analyst_worker_dir/workspace" "$analyst_worker_dir/results" "$analyst_worker_dir/logs"

    # Set up environment for the agent
    local project_dir
    project_dir=$(realpath "$ralph_dir/.." 2>/dev/null || echo "")

    export WORKER_WORKSPACE="$memory_dir"
    export WORKER_DIR="$analyst_worker_dir"
    export MEMORY_WORKER_DIR="$worker_dir"
    export MEMORY_TASK_ID="$task_id"
    export MEMORY_DIR="$memory_dir"

    local exit_code=0
    run_sub_agent "system.memory-analyst" "$analyst_worker_dir" "$project_dir" || exit_code=$?

    # Clean up analyst work dir
    rm -rf "$analyst_worker_dir"

    if [ "$exit_code" -eq 0 ]; then
        log "memory: Analysis complete for $task_id"
        # Rebuild indexes after LLM writes
        memory_rebuild_indexes "$memory_dir"
    else
        log_warn "memory: Analysis failed for $task_id (exit=$exit_code)"
        # Re-queue for retry on next cycle
        memory_queue_worker "$worker_dir"
    fi

    return "$exit_code"
}

# Check if a task has already been analyzed by the LLM
#
# Args:
#   memory_dir - Path to .ralph/memory directory
#   task_id    - Task identifier
#
# Returns: 0 if analyzed, 1 if not
memory_is_analyzed() {
    local memory_dir="$1"
    local task_id="$2"

    [ -f "$memory_dir/tasks/$task_id/analysis.md" ]
}

# =============================================================================
# INDEX REBUILDING
# =============================================================================

# Regenerate all INDEX.md files from directory contents
#
# Args:
#   memory_dir - Path to .ralph/memory directory
memory_rebuild_indexes() {
    local memory_dir="$1"

    _memory_rebuild_tasks_index "$memory_dir"
    _memory_rebuild_agents_index "$memory_dir"
    _memory_rebuild_patterns_indexes "$memory_dir"
    _memory_rebuild_root_index "$memory_dir"
}

# Rebuild tasks/INDEX.md from tasks/*/stats.json
_memory_rebuild_tasks_index() {
    local memory_dir="$1"
    local tasks_dir="$memory_dir/tasks"
    local index_file="$tasks_dir/INDEX.md"

    [ -d "$tasks_dir" ] || return 0

    {
        echo "# Task History"
        echo ""
        echo "| Task | Outcome | Fix Cycles | Analysis |"
        echo "|------|---------|------------|----------|"

        for task_dir in "$tasks_dir"/*/; do
            [ -d "$task_dir" ] || continue
            local task_id
            task_id=$(basename "$task_dir")
            [ "$task_id" = ".analyst-work" ] && continue

            local outcome="unknown" fix_cycles=0 has_analysis="pending"
            if [ -f "$task_dir/stats.json" ]; then
                outcome=$(jq -r '.outcome // "unknown"' "$task_dir/stats.json" 2>/dev/null)
                outcome="${outcome:-unknown}"
                fix_cycles=$(jq -r '.fix_cycles // 0' "$task_dir/stats.json" 2>/dev/null)
                fix_cycles="${fix_cycles:-0}"
            fi
            if [ -f "$task_dir/analysis.md" ]; then
                has_analysis="[analysis](${task_id}/analysis.md)"
            fi

            echo "| [${task_id}](${task_id}/) | $outcome | $fix_cycles | $has_analysis |"
        done
    } > "$index_file"
}

# Rebuild agents/INDEX.md from agents/*/stats.json
_memory_rebuild_agents_index() {
    local memory_dir="$1"
    local agents_dir="$memory_dir/agents"
    local index_file="$agents_dir/INDEX.md"

    [ -d "$agents_dir" ] || return 0

    {
        echo "# Agent Performance"
        echo ""
        echo "| Agent | Pass Rate | Avg Iterations | Observations |"
        echo "|-------|-----------|---------------|--------------|"

        for agent_dir in "$agents_dir"/*/; do
            [ -d "$agent_dir" ] || continue
            local agent_name
            agent_name=$(basename "$agent_dir")

            local pass_rate="n/a" avg_iters="n/a" has_obs="none"
            if [ -f "$agent_dir/stats.json" ]; then
                pass_rate=$(jq -r '.pass_rate // "n/a"' "$agent_dir/stats.json" 2>/dev/null)
                pass_rate="${pass_rate:-n/a}"
                avg_iters=$(jq -r '.avg_iterations // "n/a"' "$agent_dir/stats.json" 2>/dev/null)
                avg_iters="${avg_iters:-n/a}"
            fi
            if [ -f "$agent_dir/observations.md" ]; then
                has_obs="[notes](${agent_name}/observations.md)"
            fi

            echo "| [${agent_name}](${agent_name}/) | ${pass_rate} | ${avg_iters} | $has_obs |"
        done
    } > "$index_file"
}

# Rebuild pattern category INDEX.md files
_memory_rebuild_patterns_indexes() {
    local memory_dir="$1"
    local patterns_dir="$memory_dir/patterns"

    [ -d "$patterns_dir" ] || return 0

    # Rebuild each category index
    for category_dir in "$patterns_dir"/*/; do
        [ -d "$category_dir" ] || continue
        local category_name
        category_name=$(basename "$category_dir")

        local title
        case "$category_name" in
            errors)      title="Error Patterns" ;;
            fixes)       title="Fix Patterns" ;;
            tests)       title="Test Insights" ;;
            security)    title="Security Patterns" ;;
            environment) title="Environment Issues" ;;
            *)           title="$category_name" ;;
        esac

        {
            echo "# $title"
            echo ""

            local has_patterns=false
            for pattern_file in "$category_dir"/*.md; do
                [ -f "$pattern_file" ] || continue
                local filename
                filename=$(basename "$pattern_file")
                [ "$filename" = "INDEX.md" ] && continue
                has_patterns=true

                # Extract first heading as description
                local desc
                desc=$(head -5 "$pattern_file" | grep '^#' | head -1 | sed 's/^#* *//' || echo "$filename")
                echo "- [$desc]($filename)"
            done

            if [ "$has_patterns" = false ]; then
                echo "No patterns recorded yet."
            fi
        } > "$category_dir/INDEX.md"
    done

    # Rebuild patterns/INDEX.md with category counts
    {
        echo "# Pattern Categories"
        echo ""

        for category_dir in "$patterns_dir"/*/; do
            [ -d "$category_dir" ] || continue
            local category_name
            category_name=$(basename "$category_dir")

            local title
            case "$category_name" in
                errors)      title="Errors" ;;
                fixes)       title="Fixes" ;;
                tests)       title="Tests" ;;
                security)    title="Security" ;;
                environment) title="Environment" ;;
                *)           title="$category_name" ;;
            esac

            local count=0
            for f in "$category_dir"/*.md; do
                [ -f "$f" ] || continue
                [ "$(basename "$f")" = "INDEX.md" ] && continue
                ((++count)) || true
            done

            echo "- [$title](${category_name}/INDEX.md) - $count patterns"
        done
    } > "$patterns_dir/INDEX.md"
}

# Rebuild root INDEX.md
_memory_rebuild_root_index() {
    local memory_dir="$1"

    local tasks_analyzed=0
    if [ -f "$memory_dir/stats.json" ]; then
        tasks_analyzed=$(jq -r '.tasks_analyzed // 0' "$memory_dir/stats.json" 2>/dev/null)
        tasks_analyzed="${tasks_analyzed:-0}"
    fi

    _memory_scaffold_root_index "$memory_dir" "$tasks_analyzed"
}

# =============================================================================
# SCAFFOLD HELPERS
# =============================================================================

_memory_scaffold_root_index() {
    local memory_dir="$1"
    local tasks_analyzed="${2:-0}"

    cat > "$memory_dir/INDEX.md" << EOF
# Project Memory

Last updated: $(iso_now) | Tasks analyzed: $tasks_analyzed
Global stats: [stats.json](stats.json)

## Escalated Issues
**[ESCALATED.md](ESCALATED.md)** - Structural issues requiring external intervention

## Patterns
- [Error Patterns](patterns/errors/INDEX.md)
- [Fix Patterns](patterns/fixes/INDEX.md)
- [Test Insights](patterns/tests/INDEX.md)
- [Security Patterns](patterns/security/INDEX.md)
- [Environment Issues](patterns/environment/INDEX.md)

## Agents
- [Agent Overview](agents/INDEX.md)

## Tasks
- [Task History](tasks/INDEX.md)
EOF
}

_memory_scaffold_patterns_index() {
    local memory_dir="$1"
    [ -f "$memory_dir/patterns/INDEX.md" ] && return 0

    cat > "$memory_dir/patterns/INDEX.md" << 'EOF'
# Pattern Categories

- [Errors](errors/INDEX.md) - 0 patterns
- [Fixes](fixes/INDEX.md) - 0 patterns
- [Tests](tests/INDEX.md) - 0 patterns
- [Security](security/INDEX.md) - 0 patterns
- [Environment](environment/INDEX.md) - 0 patterns
EOF
}

_memory_scaffold_category_index() {
    local dir="$1"
    local title="$2"
    [ -f "$dir/INDEX.md" ] && return 0

    cat > "$dir/INDEX.md" << EOF
# $title

No patterns recorded yet.
EOF
}
