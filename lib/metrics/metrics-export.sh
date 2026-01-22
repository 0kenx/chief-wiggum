#!/usr/bin/env bash
# Export metrics to metrics.json file
# This script aggregates metrics from all workers and writes to .ralph/metrics.json
set -euo pipefail

source "$WIGGUM_HOME/lib/metrics/calculate-cost.sh"

# Export metrics for all workers to .ralph/metrics.json
export_metrics() {
    local ralph_dir="$1"
    local workers_dir="$ralph_dir/workers"
    local output_file="$ralph_dir/metrics.json"

    if [ ! -d "$workers_dir" ]; then
        echo "No workers directory found"
        return 1
    fi

    # Initialize aggregated values
    local total_workers=0
    local successful_workers=0
    local failed_workers=0
    local total_time_seconds=0
    local total_cost=0
    local total_input_tokens=0
    local total_output_tokens=0
    local total_cache_creation=0
    local total_cache_read=0
    local total_context_tokens=0

    # Build workers array
    local workers_json="[]"

    for worker_dir in "$workers_dir"/worker-*; do
        [ -d "$worker_dir" ] || continue

        local worker_id
        worker_id=$(basename "$worker_dir")
        local prd_file="$worker_dir/prd.md"
        local log_dir="$worker_dir/logs"

        ((total_workers++))

        # Determine worker status from PRD
        local status="in_progress"
        if [ -f "$prd_file" ]; then
            if grep -q '^\- \[\*\]' "$prd_file" 2>/dev/null; then
                status="failed"
                ((failed_workers++))
            elif ! grep -q '^\- \[ \]' "$prd_file" 2>/dev/null && grep -q '^\- \[x\]' "$prd_file" 2>/dev/null; then
                status="success"
                ((successful_workers++))
            fi
        fi

        # Calculate worker metrics if logs exist
        local worker_time_seconds=0
        local worker_cost=0
        local worker_input=0
        local worker_output=0
        local worker_cache_creation=0
        local worker_cache_read=0
        local worker_context_tokens=0
        local worker_context_size=200000
        local worker_context_percent=0
        local worker_time_formatted="00:00:00"
        local pr_url=""

        if [ -d "$log_dir" ]; then
            # Sum all result entries from iteration logs using jq
            local totals
            totals=$(find "$log_dir" -type f -name "iteration-*.log" -exec grep '"type":"result"' {} \; 2>/dev/null | \
                jq -s '{
                    duration_ms: (map(.duration_ms) | add // 0),
                    total_cost: (map(.total_cost_usd) | add // 0),
                    input_tokens: (map(.usage.input_tokens) | add // 0),
                    output_tokens: (map(.usage.output_tokens) | add // 0),
                    cache_creation_tokens: (map(.usage.cache_creation_input_tokens) | add // 0),
                    cache_read_tokens: (map(.usage.cache_read_input_tokens) | add // 0)
                }' 2>/dev/null)

            if [ -n "$totals" ]; then
                local duration_ms
                duration_ms=$(echo "$totals" | jq -r '.duration_ms // 0')
                worker_time_seconds=$((duration_ms / 1000))
                worker_cost=$(echo "$totals" | jq -r '.total_cost // 0')
                worker_input=$(echo "$totals" | jq -r '.input_tokens // 0')
                worker_output=$(echo "$totals" | jq -r '.output_tokens // 0')
                worker_cache_creation=$(echo "$totals" | jq -r '.cache_creation_tokens // 0')
                worker_cache_read=$(echo "$totals" | jq -r '.cache_read_tokens // 0')

                # Calculate context usage
                worker_context_tokens=$((worker_input + worker_cache_read + worker_cache_creation))
                worker_context_percent=$(echo "scale=1; $worker_context_tokens * 100 / $worker_context_size" | bc 2>/dev/null || echo "0")

                # Format time
                local hours=$((worker_time_seconds / 3600))
                local minutes=$(((worker_time_seconds % 3600) / 60))
                local seconds=$((worker_time_seconds % 60))
                worker_time_formatted=$(printf "%02d:%02d:%02d" $hours $minutes $seconds)

                # Update totals
                total_time_seconds=$((total_time_seconds + worker_time_seconds))
                total_cost=$(echo "$total_cost + $worker_cost" | bc)
                total_input_tokens=$((total_input_tokens + worker_input))
                total_output_tokens=$((total_output_tokens + worker_output))
                total_cache_creation=$((total_cache_creation + worker_cache_creation))
                total_cache_read=$((total_cache_read + worker_cache_read))
                total_context_tokens=$((total_context_tokens + worker_context_tokens))
            fi
        fi

        # Check for PR URL
        if [ -f "$worker_dir/pr_url.txt" ]; then
            pr_url=$(cat "$worker_dir/pr_url.txt")
        fi

        # Build worker JSON
        local worker_json
        worker_json=$(jq -n \
            --arg worker_id "$worker_id" \
            --arg status "$status" \
            --arg time_spent "$worker_time_formatted" \
            --argjson time_seconds "$worker_time_seconds" \
            --argjson input "$worker_input" \
            --argjson output "$worker_output" \
            --argjson cache_creation "$worker_cache_creation" \
            --argjson cache_read "$worker_cache_read" \
            --argjson context_tokens "$worker_context_tokens" \
            --argjson context_size "$worker_context_size" \
            --arg context_percent "$worker_context_percent" \
            --argjson cost "$worker_cost" \
            --arg pr_url "$pr_url" \
            '{
                worker_id: $worker_id,
                status: $status,
                time_spent: $time_spent,
                time_seconds: $time_seconds,
                tokens: {
                    input: $input,
                    output: $output,
                    cache_creation: $cache_creation,
                    cache_read: $cache_read,
                    total: ($input + $output + $cache_creation + $cache_read)
                },
                context: {
                    tokens: $context_tokens,
                    size: $context_size,
                    percent: ($context_percent | tonumber)
                },
                cost: $cost,
                pr_url: $pr_url
            }')

        workers_json=$(echo "$workers_json" | jq --argjson worker "$worker_json" '. + [$worker]')
    done

    # Calculate totals and success rate
    local success_rate=0
    if [ $total_workers -gt 0 ]; then
        success_rate=$(echo "scale=2; $successful_workers * 100 / $total_workers" | bc)
    fi

    local total_tokens=$((total_input_tokens + total_output_tokens + total_cache_creation + total_cache_read))
    local total_context_size=200000
    local total_context_percent=0
    if [ $total_workers -gt 0 ]; then
        total_context_percent=$(echo "scale=1; ($total_context_tokens / $total_workers) * 100 / $total_context_size" | bc 2>/dev/null || echo "0")
    fi

    # Format total time
    local total_hours=$((total_time_seconds / 3600))
    local total_minutes=$(((total_time_seconds % 3600) / 60))
    local total_seconds=$((total_time_seconds % 60))
    local total_time_formatted
    total_time_formatted=$(printf "%02d:%02d:%02d" $total_hours $total_minutes $total_seconds)

    # Build final JSON
    local metrics_json
    metrics_json=$(jq -n \
        --argjson total_workers "$total_workers" \
        --argjson successful_workers "$successful_workers" \
        --argjson failed_workers "$failed_workers" \
        --arg success_rate "$success_rate" \
        --arg total_time "$total_time_formatted" \
        --argjson total_time_seconds "$total_time_seconds" \
        --argjson total_cost "$total_cost" \
        --argjson input "$total_input_tokens" \
        --argjson output "$total_output_tokens" \
        --argjson cache_creation "$total_cache_creation" \
        --argjson cache_read "$total_cache_read" \
        --argjson total_tokens "$total_tokens" \
        --argjson context_tokens "$total_context_tokens" \
        --argjson context_size "$total_context_size" \
        --arg context_percent "$total_context_percent" \
        --argjson workers "$workers_json" \
        '{
            summary: {
                total_workers: $total_workers,
                successful_workers: $successful_workers,
                failed_workers: $failed_workers,
                success_rate: ($success_rate | tonumber),
                total_time: $total_time,
                total_time_seconds: $total_time_seconds,
                total_cost: $total_cost
            },
            tokens: {
                input: $input,
                output: $output,
                cache_creation: $cache_creation,
                cache_read: $cache_read,
                total: $total_tokens
            },
            context: {
                tokens: $context_tokens,
                size: $context_size,
                percent: ($context_percent | tonumber)
            },
            workers: $workers
        }')

    # Write to file
    echo "$metrics_json" > "$output_file"
    echo "Metrics exported to $output_file"
}

# Update metrics for a single worker (for real-time updates)
update_worker_metrics() {
    local ralph_dir="$1"
    local worker_id="$2"

    # Currently we ignore worker_id and re-export all metrics (simple approach for now).
    # The worker_id parameter is kept for future enhancements (e.g., partial per-worker updates).
    : "$worker_id"

    export_metrics "$ralph_dir"
}

# If called directly
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    if [ $# -lt 1 ]; then
        echo "Usage: $0 <ralph_dir>"
        exit 1
    fi
    export_metrics "$1"
fi
