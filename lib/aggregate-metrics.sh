#!/usr/bin/env bash
# Aggregate metrics across all workers

aggregate_all_metrics() {
    local ralph_dir="$1"
    local output_json="${2:-$ralph_dir/metrics.json}"

    if [ ! -d "$ralph_dir" ]; then
        echo "Error: .ralph directory not found: $ralph_dir" >&2
        return 1
    fi

    local workers_dir="$ralph_dir/workers"
    if [ ! -d "$workers_dir" ]; then
        echo "Error: Workers directory not found: $workers_dir" >&2
        return 1
    fi

    # Initialize totals
    local total_input_tokens=0
    local total_output_tokens=0
    local total_cache_creation_tokens=0
    local total_cache_read_tokens=0
    local total_time_seconds=0
    local total_cost=0
    local worker_count=0
    local successful_workers=0
    local failed_workers=0

    # Arrays to store per-worker data for JSON export
    declare -a worker_data=()

    # Iterate through all worker directories
    for worker_dir in "$workers_dir"/worker-*; do
        [ -d "$worker_dir" ] || continue

        local worker_id=$(basename "$worker_dir")
        local log_file="$worker_dir/worker.log"
        local metrics_file="$worker_dir/metrics.txt"

        # Skip if no log file exists
        [ -f "$log_file" ] || continue

        ((worker_count++))

        # Check if worker was successful by looking for PR URL
        local status="unknown"
        if [ -f "$worker_dir/pr_url.txt" ]; then
            status="success"
            ((successful_workers++))
        elif [ -f "$worker_dir/violation_status.txt" ]; then
            status="failed"
            ((failed_workers++))
        else
            # Check if still in progress or failed
            if grep -q "WORKER_END_TIME=" "$log_file" 2>/dev/null; then
                status="failed"
                ((failed_workers++))
            else
                status="in_progress"
            fi
        fi

        # Extract metrics from log file
        local input_tokens=0
        local output_tokens=0
        local cache_creation_tokens=0
        local cache_read_tokens=0

        # Parse JSON lines for token usage
        while IFS= read -r line; do
            local it=$(echo "$line" | grep -o '"input_tokens":[0-9]*' | head -1 | cut -d':' -f2)
            [ -n "$it" ] && input_tokens=$((input_tokens + it))

            local ot=$(echo "$line" | grep -o '"output_tokens":[0-9]*' | head -1 | cut -d':' -f2)
            [ -n "$ot" ] && output_tokens=$((output_tokens + ot))

            local cct=$(echo "$line" | grep -o '"cache_creation_input_tokens":[0-9]*' | head -1 | cut -d':' -f2)
            [ -n "$cct" ] && cache_creation_tokens=$((cache_creation_tokens + cct))

            local crt=$(echo "$line" | grep -o '"cache_read_input_tokens":[0-9]*' | head -1 | cut -d':' -f2)
            [ -n "$crt" ] && cache_read_tokens=$((cache_read_tokens + crt))
        done < <(grep '"input_tokens"' "$log_file" 2>/dev/null)

        # Calculate time spent
        local time_seconds=0
        local start_ts=$(grep "WORKER_START_TIME=" "$log_file" 2>/dev/null | head -1 | cut -d'=' -f2)
        local end_ts=$(grep "WORKER_END_TIME=" "$log_file" 2>/dev/null | tail -1 | cut -d'=' -f2)

        if [ -n "$start_ts" ] && [ -n "$end_ts" ] && [ "$end_ts" -gt "$start_ts" ] 2>/dev/null; then
            time_seconds=$((end_ts - start_ts))
        elif [ -f "$metrics_file" ]; then
            # Fallback: try to parse from metrics.txt
            time_seconds=$(grep "Time Spent:.*(\([0-9]*\) seconds)" "$metrics_file" 2>/dev/null | sed 's/.*(\([0-9]*\) seconds).*/\1/' || echo "0")
        fi

        # Calculate cost for this worker
        local cost_input=$(echo "scale=6; ($input_tokens * 3.00) / 1000000" | bc 2>/dev/null || echo "0")
        local cost_output=$(echo "scale=6; ($output_tokens * 15.00) / 1000000" | bc 2>/dev/null || echo "0")
        local cost_cache_creation=$(echo "scale=6; ($cache_creation_tokens * 3.00) / 1000000" | bc 2>/dev/null || echo "0")
        local cost_cache_read=$(echo "scale=6; ($cache_read_tokens * 0.30) / 1000000" | bc 2>/dev/null || echo "0")
        local worker_cost=$(echo "scale=6; $cost_input + $cost_output + $cost_cache_creation + $cost_cache_read" | bc 2>/dev/null || echo "0")

        # Add to totals
        total_input_tokens=$((total_input_tokens + input_tokens))
        total_output_tokens=$((total_output_tokens + output_tokens))
        total_cache_creation_tokens=$((total_cache_creation_tokens + cache_creation_tokens))
        total_cache_read_tokens=$((total_cache_read_tokens + cache_read_tokens))
        total_time_seconds=$((total_time_seconds + time_seconds))
        total_cost=$(echo "scale=6; $total_cost + $worker_cost" | bc 2>/dev/null || echo "$total_cost")

        # Format time as HH:MM:SS
        local hours=$((time_seconds / 3600))
        local minutes=$(((time_seconds % 3600) / 60))
        local seconds=$((time_seconds % 60))
        local time_formatted=$(printf "%02d:%02d:%02d" $hours $minutes $seconds)

        # Store worker data for JSON
        local pr_url=""
        if [ -f "$worker_dir/pr_url.txt" ]; then
            pr_url=$(cat "$worker_dir/pr_url.txt")
        fi

        # Build JSON object for this worker (escaping quotes in strings)
        local worker_json=$(cat <<EOF
    {
      "worker_id": "$worker_id",
      "status": "$status",
      "time_spent": "$time_formatted",
      "time_seconds": $time_seconds,
      "tokens": {
        "input": $input_tokens,
        "output": $output_tokens,
        "cache_creation": $cache_creation_tokens,
        "cache_read": $cache_read_tokens,
        "total": $((input_tokens + output_tokens + cache_creation_tokens + cache_read_tokens))
      },
      "cost": $(printf "%.6f" $worker_cost),
      "pr_url": "$pr_url"
    }
EOF
)
        worker_data+=("$worker_json")
    done

    # Calculate success rate
    local success_rate=0
    if [ $worker_count -gt 0 ]; then
        success_rate=$(echo "scale=2; ($successful_workers * 100) / $worker_count" | bc 2>/dev/null || echo "0")
    fi

    # Format total time as HH:MM:SS
    local total_hours=$((total_time_seconds / 3600))
    local total_minutes=$(((total_time_seconds % 3600) / 60))
    local total_seconds=$((total_time_seconds % 60))
    local total_time_formatted=$(printf "%02d:%02d:%02d" $total_hours $total_minutes $total_seconds)

    # Calculate cost breakdown
    local cost_input=$(echo "scale=6; ($total_input_tokens * 3.00) / 1000000" | bc 2>/dev/null || echo "0")
    local cost_output=$(echo "scale=6; ($total_output_tokens * 15.00) / 1000000" | bc 2>/dev/null || echo "0")
    local cost_cache_creation=$(echo "scale=6; ($total_cache_creation_tokens * 3.00) / 1000000" | bc 2>/dev/null || echo "0")
    local cost_cache_read=$(echo "scale=6; ($total_cache_read_tokens * 0.30) / 1000000" | bc 2>/dev/null || echo "0")

    # Display summary report
    echo ""
    echo "=========================================="
    echo "=== Cumulative Metrics Report ==="
    echo "=========================================="
    echo ""
    echo "Workers:"
    echo "  Total workers: $worker_count"
    echo "  Successful: $successful_workers"
    echo "  Failed: $failed_workers"
    echo "  Success rate: ${success_rate}%"
    echo ""
    echo "Time:"
    echo "  Total time: $total_time_formatted ($total_time_seconds seconds)"
    if [ $worker_count -gt 0 ]; then
        local avg_time=$((total_time_seconds / worker_count))
        local avg_hours=$((avg_time / 3600))
        local avg_minutes=$(((avg_time % 3600) / 60))
        local avg_seconds=$((avg_time % 60))
        echo "  Average per worker: $(printf "%02d:%02d:%02d" $avg_hours $avg_minutes $avg_seconds)"
    fi
    echo ""
    echo "Tokens:"
    echo "  Input tokens: $(printf "%'d" $total_input_tokens)"
    echo "  Output tokens: $(printf "%'d" $total_output_tokens)"
    echo "  Cache creation: $(printf "%'d" $total_cache_creation_tokens)"
    echo "  Cache read: $(printf "%'d" $total_cache_read_tokens)"
    echo "  Total tokens: $(printf "%'d" $((total_input_tokens + total_output_tokens + total_cache_creation_tokens + total_cache_read_tokens)))"
    echo ""
    echo "Cost Breakdown (Claude Sonnet 4.5):"
    echo "  Input tokens: \$$(printf "%.6f" $cost_input)"
    echo "  Output tokens: \$$(printf "%.6f" $cost_output)"
    echo "  Cache creation: \$$(printf "%.6f" $cost_cache_creation)"
    echo "  Cache read: \$$(printf "%.6f" $cost_cache_read)"
    echo "  Total cost: \$$(printf "%.6f" $total_cost)"
    echo ""
    echo "=========================================="
    echo ""

    # Generate JSON output
    local workers_json=$(IFS=,; echo "${worker_data[*]}")

    cat > "$output_json" <<EOF
{
  "summary": {
    "total_workers": $worker_count,
    "successful_workers": $successful_workers,
    "failed_workers": $failed_workers,
    "success_rate": $success_rate,
    "total_time": "$total_time_formatted",
    "total_time_seconds": $total_time_seconds,
    "total_cost": $(printf "%.6f" $total_cost)
  },
  "tokens": {
    "input": $total_input_tokens,
    "output": $total_output_tokens,
    "cache_creation": $total_cache_creation_tokens,
    "cache_read": $total_cache_read_tokens,
    "total": $((total_input_tokens + total_output_tokens + total_cache_creation_tokens + total_cache_read_tokens))
  },
  "cost_breakdown": {
    "input": $(printf "%.6f" $cost_input),
    "output": $(printf "%.6f" $cost_output),
    "cache_creation": $(printf "%.6f" $cost_cache_creation),
    "cache_read": $(printf "%.6f" $cost_cache_read),
    "total": $(printf "%.6f" $total_cost)
  },
  "workers": [
$workers_json
  ]
}
EOF

    echo "Metrics exported to: $output_json"
    echo ""

    return 0
}

# If called directly
if [ $# -gt 0 ]; then
    aggregate_all_metrics "$@"
fi
