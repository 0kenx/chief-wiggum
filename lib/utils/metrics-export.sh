#!/usr/bin/env bash
# Export metrics to metrics.json file
# This script aggregates metrics from all workers and writes to .ralph/metrics.json
# Uses mtime-based caching per worker to skip recomputation of unchanged workers.
set -euo pipefail

source "$WIGGUM_HOME/lib/utils/calculate-cost.sh"

# =============================================================================
# Cache helpers
# =============================================================================

# Portable file mtime+size via stat(2) — no file content read
#
# Args:
#   file - Path to file
#
# Returns: "mtime_size" string via stdout
_file_stat() {
    local file="$1"
    if [[ "$OSTYPE" == darwin* ]]; then
        stat -f '%m_%z' "$file" 2>/dev/null || echo "0_0"
    else
        stat -c '%Y_%s' "$file" 2>/dev/null || echo "0_0"
    fi
}

# Build mtime-based fingerprint for a worker directory
# Only uses stat(2) calls — no file content reads
#
# Args:
#   worker_dir - Path to the worker directory
#
# Returns: fingerprint string via stdout
_worker_fingerprint() {
    local worker_dir="$1"
    local fp=""

    # PRD mtime+size (determines status)
    if [ -f "$worker_dir/prd.md" ]; then
        fp="prd:$(_file_stat "$worker_dir/prd.md")"
    fi

    # PR URL mtime+size
    if [ -f "$worker_dir/pr_url.txt" ]; then
        fp+="|pr:$(_file_stat "$worker_dir/pr_url.txt")"
    fi

    # Log files: batch stat for efficiency
    if [ -d "$worker_dir/logs" ]; then
        local log_stats=""
        if [[ "$OSTYPE" == darwin* ]]; then
            log_stats=$(find "$worker_dir/logs" -type f -name "*.log" ! -name "*summary*" \
                -exec stat -f '%m_%z %N' {} + 2>/dev/null | sort) || true
        else
            log_stats=$(find "$worker_dir/logs" -type f -name "*.log" ! -name "*summary*" \
                -exec stat -c '%Y_%s %n' {} + 2>/dev/null | sort) || true
        fi
        if [ -n "$log_stats" ]; then
            fp+="|logs:${log_stats}"
        fi
    fi

    echo "$fp"
}

# Compute metrics for a single worker (the expensive operation)
# Parses log files with find/grep/jq pipeline
#
# Args:
#   worker_dir - Path to the worker directory
#   worker_id  - Worker identifier
#
# Returns: worker metrics JSON via stdout
_compute_worker_metrics() {
    local worker_dir="$1"
    local worker_id="$2"
    local prd_file="$worker_dir/prd.md"
    local log_dir="$worker_dir/logs"

    # Determine worker status from PRD
    local status="in_progress"
    if [ -f "$prd_file" ]; then
        if grep -q '^\- \[\*\]' "$prd_file" 2>/dev/null; then
            status="failed"
        elif ! grep -q '^\- \[ \]' "$prd_file" 2>/dev/null && grep -q '^\- \[x\]' "$prd_file" 2>/dev/null; then
            status="success"
        fi
    fi

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
        local totals
        totals=$(find "$log_dir" -type f -name "*.log" ! -name "*summary*" -exec grep '"type":"result"' {} \; 2>/dev/null | \
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

            worker_context_tokens=$((worker_input + worker_cache_read + worker_cache_creation))
            worker_context_percent=$(echo "scale=1; $worker_context_tokens * 100 / $worker_context_size" | bc 2>/dev/null || echo "0")

            local hours=$((worker_time_seconds / 3600))
            local minutes=$(((worker_time_seconds % 3600) / 60))
            local seconds=$((worker_time_seconds % 60))
            worker_time_formatted=$(printf "%02d:%02d:%02d" "$hours" "$minutes" "$seconds")
        fi
    fi

    if [ -f "$worker_dir/pr_url.txt" ]; then
        pr_url=$(cat "$worker_dir/pr_url.txt")
    fi

    jq -n \
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
        }'
}

# Remove cache entries for workers that no longer exist
#
# Args:
#   cache_dir   - Path to the metrics cache directory
#   workers_dir - Path to the workers directory
_cleanup_metrics_cache() {
    local cache_dir="$1"
    local workers_dir="$2"

    for cache_file in "$cache_dir"/*.json; do
        [ -f "$cache_file" ] || continue
        local cached_id
        cached_id=$(basename "$cache_file" .json)
        if [ ! -d "$workers_dir/$cached_id" ]; then
            rm -f "$cache_file"
        fi
    done
}

# =============================================================================
# Public API
# =============================================================================

# Export metrics for all workers to .ralph/metrics.json
# Uses per-worker mtime fingerprinting: only workers whose files changed
# since the last export get recomputed through the expensive find/grep/jq
# pipeline. Unchanged workers are read from cache.
export_metrics() {
    local ralph_dir="$1"
    local workers_dir="$ralph_dir/workers"
    local output_file="$ralph_dir/metrics.json"
    local cache_dir="$ralph_dir/cache/metrics"

    if [ ! -d "$workers_dir" ]; then
        echo "No workers directory found"
        return 1
    fi

    mkdir -p "$cache_dir"

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

        ((++total_workers))

        # Compute mtime-based fingerprint and check cache
        local current_fp
        current_fp=$(_worker_fingerprint "$worker_dir")
        local cache_file="$cache_dir/${worker_id}.json"
        local worker_json=""

        if [ -f "$cache_file" ]; then
            local cached_fp
            cached_fp=$(jq -r '.fingerprint // ""' "$cache_file" 2>/dev/null)
            if [[ "$cached_fp" == "$current_fp" ]]; then
                worker_json=$(jq -c '.data' "$cache_file" 2>/dev/null)
            fi
        fi

        if [ -z "$worker_json" ] || [[ "$worker_json" == "null" ]]; then
            # Cache miss — compute metrics (expensive: find/grep/jq on log files)
            worker_json=$(_compute_worker_metrics "$worker_dir" "$worker_id")

            # Store in cache
            jq -n --arg fp "$current_fp" --argjson data "$worker_json" \
                '{fingerprint: $fp, data: $data}' > "$cache_file"
        fi

        # Extract aggregation values in a single jq call (RS-delimited per CLAUDE.md)
        local agg_values
        agg_values=$(echo "$worker_json" | jq -r '[
            .status,
            (.time_seconds | tostring),
            (.cost | tostring),
            (.tokens.input | tostring),
            (.tokens.output | tostring),
            (.tokens.cache_creation | tostring),
            (.tokens.cache_read | tostring),
            (.context.tokens | tostring)
        ] | join("\u001e")')

        local w_status w_time w_cost w_input w_output w_ccreate w_cread w_ctx
        IFS=$'\x1e' read -r w_status w_time w_cost w_input w_output w_ccreate w_cread w_ctx <<< "$agg_values"

        case "$w_status" in
            success) ((++successful_workers)) ;;
            failed) ((++failed_workers)) ;;
        esac

        total_time_seconds=$((total_time_seconds + w_time))
        total_cost=$(echo "$total_cost + $w_cost" | bc)
        total_input_tokens=$((total_input_tokens + w_input))
        total_output_tokens=$((total_output_tokens + w_output))
        total_cache_creation=$((total_cache_creation + w_ccreate))
        total_cache_read=$((total_cache_read + w_cread))
        total_context_tokens=$((total_context_tokens + w_ctx))

        workers_json=$(echo "$workers_json" | jq --argjson worker "$worker_json" '. + [$worker]')
    done

    # Clean up stale cache entries
    _cleanup_metrics_cache "$cache_dir" "$workers_dir"

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
    total_time_formatted=$(printf "%02d:%02d:%02d" "$total_hours" "$total_minutes" "$total_seconds")

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

    # Write atomically via temp-file + mv (rename() is atomic on same fs)
    local tmp_file="${output_file}.tmp.$$"
    echo "$metrics_json" > "$tmp_file"
    mv "$tmp_file" "$output_file"
    echo "Metrics exported to $output_file"
}

# Update metrics for a single worker (for real-time updates)
# With mtime-based caching, only the changed worker gets recomputed;
# all other workers hit the cache.
update_worker_metrics() {
    local ralph_dir="$1"
    local worker_id="$2"

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
