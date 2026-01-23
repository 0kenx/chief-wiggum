#!/usr/bin/env bash
# Calculate time spent and API cost from worker logs
set -euo pipefail

# Model context window sizes (in tokens)
# All current Claude models have 200k context windows
declare -A MODEL_CONTEXT_SIZES=(
    ["claude-3-5-sonnet-20241022"]=200000
    ["claude-sonnet-4-20250514"]=200000
    ["claude-3-opus-20240229"]=200000
    ["claude-opus-4-0-20250514"]=200000
    ["claude-3-5-haiku-20241022"]=200000
    ["claude-3-haiku-20240307"]=200000
    ["default"]=200000
)

# Get context window size for a model
get_context_size() {
    local model="$1"
    if [[ -n "${MODEL_CONTEXT_SIZES[$model]:-}" ]]; then
        echo "${MODEL_CONTEXT_SIZES[$model]}"
    else
        echo "${MODEL_CONTEXT_SIZES[default]}"
    fi
}

# Format model name for display (extract short name)
format_model_name() {
    local model="$1"
    # Strip date suffix, then remove "claude-" prefix (e.g., "claude-3-5-sonnet-20241022" → "claude-3-5-sonnet" → "3-5-sonnet", then uppercased)
    echo "$model" | sed -E 's/-[0-9]{8}$//' | sed 's/claude-//' | tr '[:lower:]' '[:upper:]'
}

calculate_worker_cost() {
    local log_file="$1"
    local log_dir
    log_dir="$(dirname "$log_file")/logs"

    # Check if logs directory exists
    if [ ! -d "$log_dir" ]; then
        echo "Error: Logs directory not found: $log_dir" >&2
        return 1
    fi

    # Sum all result entries from iteration logs using jq
    local totals
    totals=$(find "$log_dir" -type f -name "*.log" -exec grep '"type":"result"' {} \; | \
        jq -s '{
            duration_ms: (map(.duration_ms) | add),
            duration_api_ms: (map(.duration_api_ms) | add),
            total_cost: (map(.total_cost_usd) | add),
            num_turns: (map(.num_turns) | add),
            web_search_requests: (map(.usage.server_tool_use.web_search_requests) | add),
            input_tokens: (map(.usage.input_tokens) | add),
            output_tokens: (map(.usage.output_tokens) | add),
            cache_creation_tokens: (map(.usage.cache_creation_input_tokens) | add),
            cache_read_tokens: (map(.usage.cache_read_input_tokens) | add),
            model_usage: (map(.modelUsage | to_entries) | flatten | group_by(.key) | map({
                key: .[0].key,
                value: {
                    inputTokens: (map(.value.inputTokens) | add),
                    outputTokens: (map(.value.outputTokens) | add),
                    cacheReadInputTokens: (map(.value.cacheReadInputTokens) | add),
                    cacheCreationInputTokens: (map(.value.cacheCreationInputTokens) | add),
                    costUSD: (map(.value.costUSD) | add)
                }
            }) | from_entries)
        }')

    local duration_ms duration_api_ms total_cost num_turns web_search_requests
    local input_tokens output_tokens cache_creation_tokens cache_read_tokens
    duration_ms=$(echo "$totals" | jq -r '.duration_ms')
    duration_api_ms=$(echo "$totals" | jq -r '.duration_api_ms')
    total_cost=$(echo "$totals" | jq -r '.total_cost')
    num_turns=$(echo "$totals" | jq -r '.num_turns')
    web_search_requests=$(echo "$totals" | jq -r '.web_search_requests')
    input_tokens=$(echo "$totals" | jq -r '.input_tokens')
    output_tokens=$(echo "$totals" | jq -r '.output_tokens')
    cache_creation_tokens=$(echo "$totals" | jq -r '.cache_creation_tokens')
    cache_read_tokens=$(echo "$totals" | jq -r '.cache_read_tokens')

    # Format time
    local time_spent=$((duration_ms / 1000))
    local hours=$((time_spent / 3600))
    local minutes=$(((time_spent % 3600) / 60))
    local seconds=$((time_spent % 60))
    local time_formatted
    time_formatted=$(printf "%02d:%02d:%02d" $hours $minutes $seconds)

    local api_time_spent=$((duration_api_ms / 1000))
    local api_hours=$((api_time_spent / 3600))
    local api_minutes=$(((api_time_spent % 3600) / 60))
    local api_seconds=$((api_time_spent % 60))
    local api_time_formatted
    api_time_formatted=$(printf "%02d:%02d:%02d" $api_hours $api_minutes $api_seconds)

    # Output results
    echo "=== Worker Time and Cost Report ==="
    echo ""
    echo "Time Spent: $time_formatted (API: $api_time_formatted)"
    echo "Turns: $num_turns"
    echo "Web Searches: $web_search_requests"
    echo ""
    echo "Token Usage:"
    echo "  Input tokens: $(printf "%'d" "$input_tokens")"
    echo "  Output tokens: $(printf "%'d" "$output_tokens")"
    echo "  Cache creation tokens: $(printf "%'d" "$cache_creation_tokens")"
    echo "  Cache read tokens: $(printf "%'d" "$cache_read_tokens")"
    echo "  Total tokens: $(printf "%'d" $((input_tokens + output_tokens + cache_creation_tokens + cache_read_tokens)))"
    echo ""
    echo "Per-Model Usage:"
    echo "$totals" | jq -r '.model_usage | to_entries[] | "  \(.key):\n    Input: \(.value.inputTokens), Output: \(.value.outputTokens)\n    Cache read: \(.value.cacheReadInputTokens), Cache create: \(.value.cacheCreationInputTokens)\n    Cost: $\(.value.costUSD | . * 100 | round / 100)"'
    echo ""

    # Calculate and display context usage per model
    echo "Context Usage:"
    local model_context_json=""
    while IFS= read -r model_line; do
        local model_name model_input model_cache_read model_cache_create
        model_name=$(echo "$model_line" | jq -r '.key')
        model_input=$(echo "$model_line" | jq -r '.value.inputTokens // 0')
        model_cache_read=$(echo "$model_line" | jq -r '.value.cacheReadInputTokens // 0')
        model_cache_create=$(echo "$model_line" | jq -r '.value.cacheCreationInputTokens // 0')

        # Calculate context tokens (input + cache_read + cache_creation)
        local context_tokens=$((model_input + model_cache_read + model_cache_create))
        local context_size
        context_size=$(get_context_size "$model_name")
        local context_percent
        context_percent=$(echo "scale=1; $context_tokens * 100 / $context_size" | bc 2>/dev/null || echo "0")

        local display_name
        display_name=$(format_model_name "$model_name")
        echo "  [$display_name] Context: ${context_percent}% (${context_tokens}/${context_size} tokens)"

        # Build JSON for export
        if [ -n "$model_context_json" ]; then
            model_context_json="${model_context_json},"
        fi
        model_context_json="${model_context_json}\"$model_name\":{\"context_tokens\":$context_tokens,\"context_size\":$context_size,\"context_percent\":$context_percent}"
    done < <(echo "$totals" | jq -c '.model_usage | to_entries[]')
    echo ""

    echo "Total Cost: \$$(printf "%.2f" "$total_cost")"
    echo ""

    # Calculate total context usage for primary model (use the one with highest usage)
    local primary_context_tokens=$((input_tokens + cache_read_tokens + cache_creation_tokens))
    local primary_context_size="${MODEL_CONTEXT_SIZES[default]}"
    local primary_context_percent
    primary_context_percent=$(echo "scale=1; $primary_context_tokens * 100 / $primary_context_size" | bc 2>/dev/null || echo "0")

    # Export for use in PR summary
    export WORKER_TIME_SPENT="$time_formatted"
    WORKER_TOTAL_COST=$(printf "%.2f" "$total_cost")
    export WORKER_TOTAL_COST
    export WORKER_INPUT_TOKENS=$input_tokens
    export WORKER_OUTPUT_TOKENS=$output_tokens
    export WORKER_CACHE_CREATION_TOKENS=$cache_creation_tokens
    export WORKER_CACHE_READ_TOKENS=$cache_read_tokens
    export WORKER_CONTEXT_TOKENS=$primary_context_tokens
    export WORKER_CONTEXT_SIZE=$primary_context_size
    export WORKER_CONTEXT_PERCENT=$primary_context_percent
    export WORKER_MODEL_CONTEXT_JSON="{$model_context_json}"
}

# Calculate context usage for the latest iteration (for real-time display)
# Returns: model_name, context_tokens, context_size, context_percent
calculate_latest_context_usage() {
    local log_dir="$1"

    if [ ! -d "$log_dir" ]; then
        return 1
    fi

    # Find the latest iteration log file with result entries
    local latest_log
    latest_log=$(find "$log_dir" -type f -name "*.log" -exec grep -l '"type":"result"' {} \; 2>/dev/null | sort -V | tail -1)

    if [ -z "$latest_log" ]; then
        return 1
    fi

    # Get the latest result entry
    local result
    result=$(grep '"type":"result"' "$latest_log" | tail -1)

    if [ -z "$result" ]; then
        return 1
    fi

    # Extract model usage from the result
    local model_usage
    model_usage=$(echo "$result" | jq -r '.modelUsage | to_entries | sort_by(.value.inputTokens) | reverse | .[0] // empty')

    if [ -z "$model_usage" ] || [ "$model_usage" = "null" ]; then
        return 1
    fi

    local model_name input_tokens cache_read cache_create
    model_name=$(echo "$model_usage" | jq -r '.key')
    input_tokens=$(echo "$model_usage" | jq -r '.value.inputTokens // 0')
    cache_read=$(echo "$model_usage" | jq -r '.value.cacheReadInputTokens // 0')
    cache_create=$(echo "$model_usage" | jq -r '.value.cacheCreationInputTokens // 0')

    local context_tokens=$((input_tokens + cache_read + cache_create))
    local context_size
    context_size=$(get_context_size "$model_name")
    local context_percent
    if [ "$context_size" -gt 0 ] 2>/dev/null; then
        context_percent=$(echo "scale=1; $context_tokens * 100 / $context_size" | bc 2>/dev/null || echo "0")
    else
        context_percent="0"
    fi

    local display_name
    display_name=$(format_model_name "$model_name")

    echo "$display_name $context_tokens $context_size $context_percent"
}

# If called directly with log file argument (not when sourced)
if [[ "${BASH_SOURCE[0]}" == "${0}" ]] && [ $# -gt 0 ]; then
    calculate_worker_cost "$1"
fi
