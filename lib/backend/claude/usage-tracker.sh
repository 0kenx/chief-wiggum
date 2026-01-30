#!/usr/bin/env bash
# Claude Code usage tracker
#
# Parses JSONL conversation logs from ~/.claude/projects/ and calculates
# usage statistics across two time windows:
#   - Current 5-hour cycle (prompt count)
#   - Current week Monday-to-now (Sonnet/Opus hours, total prompts)
#
# Usage:
#   source "$WIGGUM_HOME/lib/backend/claude/usage-tracker.sh"
#   usage_tracker_update           # Calculate and save usage data
#   usage_tracker_calculate        # Calculate only (prints JSON to stdout)
#
# Environment:
#   CLAUDE_PROJECTS_DIR - Override default ~/.claude/projects path
#   USAGE_DATA_DIR      - Override default data output directory
set -euo pipefail

WIGGUM_HOME="${WIGGUM_HOME:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"
source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/platform.sh"

_USAGE_TRACKER_PROJECTS_DIR="${CLAUDE_PROJECTS_DIR:-$HOME/.claude/projects}"
_USAGE_TRACKER_DATA_DIR="${USAGE_DATA_DIR:-$WIGGUM_HOME/data}"

# Get Monday midnight epoch timestamp for current week
_usage_get_week_start() {
    local now dow monday_midnight
    now=$(date +%s)
    dow=$(date +%u)  # 1=Monday, 7=Sunday
    local days_since_monday=$(( dow - 1 ))
    local seconds_since_monday=$(( days_since_monday * 86400 ))

    # Get today's midnight (portable across GNU/BSD)
    local today_midnight
    today_midnight=$(date_today_midnight)

    monday_midnight=$(( today_midnight - seconds_since_monday ))
    echo "$monday_midnight"
}

# Parse threshold_boundary from config (unix epoch or ISO timestamp)
# Returns epoch timestamp or empty string if not configured
_usage_get_threshold_boundary() {
    local config_file="${WIGGUM_HOME}/config/config.json"
    local boundary=""

    if [ -f "$config_file" ]; then
        boundary=$(jq -r '.rate_limit.threshold_boundary // empty' "$config_file" 2>/dev/null)
    fi

    # Also check environment variable override
    boundary="${WIGGUM_RATE_LIMIT_BOUNDARY:-$boundary}"

    if [ -z "$boundary" ]; then
        echo ""
        return
    fi

    # Check if it's already a unix epoch (numeric)
    if [[ "$boundary" =~ ^[0-9]+$ ]]; then
        echo "$boundary"
        return
    fi

    # Try to parse as ISO timestamp (portable across GNU/BSD)
    local epoch
    epoch=$(date_parse_epoch "$boundary" 2>/dev/null) || epoch=""
    echo "$epoch"
}

# Get current 5-hour cycle start epoch timestamp
# If threshold_boundary is configured, cycles are aligned to that boundary
# Otherwise, uses rolling 5h windows from epoch
_usage_get_5h_cycle_start() {
    local now boundary
    now=$(date +%s)
    boundary=$(_usage_get_threshold_boundary)

    if [ -n "$boundary" ] && [ "$boundary" -gt 0 ] 2>/dev/null; then
        local cycle_seconds=18000  # 5 hours
        local seconds_since_boundary=$(( now - boundary ))
        local cycles_elapsed

        # Floor division (bash truncates toward zero, we need toward -infinity)
        if [ "$seconds_since_boundary" -lt 0 ]; then
            # For negative: floor(x/y) = (x - y + 1) / y when x < 0
            cycles_elapsed=$(( (seconds_since_boundary - cycle_seconds + 1) / cycle_seconds ))
        else
            cycles_elapsed=$(( seconds_since_boundary / cycle_seconds ))
        fi

        echo $(( boundary + (cycles_elapsed * cycle_seconds) ))
    else
        # Original rolling window behavior
        local hours_since_epoch cycle_number
        hours_since_epoch=$(( now / 3600 ))
        cycle_number=$(( hours_since_epoch / 5 ))
        echo $(( cycle_number * 5 * 3600 ))
    fi
}

# Check if message content is a command (slash command or local command output)
# Args: $1 = content string
_usage_is_command_message() {
    local content="$1"
    if [[ "$content" == *"<command-name>"* ]] || [[ "$content" == *"<local-command-stdout>"* ]]; then
        return 0
    fi
    return 1
}

# Analyze a single JSONL session file
# Args: $1 = path to .jsonl file
# Output: JSON object with session stats on stdout
_usage_analyze_session() {
    local jsonl_path="$1"

    if [ ! -f "$jsonl_path" ]; then
        return 1
    fi

    local session_id project_name
    session_id=$(basename "$jsonl_path" .jsonl)
    project_name=$(basename "$(dirname "$jsonl_path")")

    # Use jq to process the entire JSONL file in one pass
    # This extracts timestamps, counts prompts, and counts model responses
    jq -s -r --arg session_id "$session_id" --arg project "$project_name" '
        # Collect all data in a single pass
        reduce .[] as $msg (
            {"timestamps": [], "prompts": 0, "sonnet": 0, "opus": 0,
             "input_tokens": 0, "output_tokens": 0};

            # Collect timestamps
            (if $msg.timestamp then
                .timestamps += [$msg.timestamp]
            else . end) |

            # Count user prompts (external, non-meta, non-command)
            (if ($msg.type == "user" and
                 ($msg.message // {}).role == "user" and
                 ($msg.isMeta // false | not) and
                 $msg.userType == "external")
            then
                # Check content for command messages
                (($msg.message // {}).content // "") as $content |
                if ($content | type) == "string" then
                    if ($content != "" and
                        ($content | contains("<command-name>") | not) and
                        ($content | contains("<local-command-stdout>") | not))
                    then .prompts += 1
                    else .
                    end
                elif ($content | type) == "array" then
                    # Check array content items
                    ([$content[] |
                        select(.type == "text") |
                        .text // "" |
                        select(contains("<command-name>") or contains("<local-command-stdout>"))
                    ] | length) as $cmd_count |
                    if $cmd_count == 0 and ($content | length) > 0
                    then .prompts += 1
                    else .
                    end
                else .
                end
            else . end) |

            # Count model responses by type and accumulate tokens
            (if $msg.type == "assistant" then
                (($msg.message // {}).model // "" | ascii_downcase) as $model |
                (($msg.message // {}).usage // {}) as $usage |
                (if ($model | contains("opus")) then .opus += 1
                elif ($model | contains("sonnet")) then .sonnet += 1
                else .
                end) |
                .input_tokens += (($usage.input_tokens // 0) + ($usage.cache_read_input_tokens // 0) + ($usage.cache_creation_input_tokens // 0)) |
                .output_tokens += ($usage.output_tokens // 0)
            else . end)
        ) |

        # Calculate timestamps
        (.timestamps | map(
            # Strip fractional seconds
            sub("\\.[0-9]+"; "") |
            # Extract tz offset in seconds, then parse datetime and adjust
            (if endswith("Z") then 0
             elif test("[+-][0-9]{2}:[0-9]{2}$") then
                ((.[-6:] | split(":") |
                    ((.[0] | tonumber) * 3600) + ((.[1] | tonumber) * 60)
                ))
             elif test("[+-][0-9]{4}$") then
                ((.[-5:] |
                    (.[0:3] | tonumber) * 3600 + (.[3:5] | tonumber) * 60
                ))
             else 0 end) as $tz_offset |
            # Strip timezone suffix to get bare datetime
            sub("Z$"; "") | sub("[+-][0-9]{2}:?[0-9]{2}$"; "") |
            try ((strptime("%Y-%m-%dT%H:%M:%S") | mktime) - $tz_offset) catch null
        ) | map(select(. != null))) as $epochs |

        ($epochs | if length > 0 then min else 0 end) as $start |
        ($epochs | if length > 0 then max else 0 end) as $end |
        (if $start > 0 and $end > 0 then (($end - $start) / 3600) else 0 end) as $duration |

        {
            session_id: $session_id,
            project: $project,
            start_time: $start,
            end_time: $end,
            duration_hours: $duration,
            prompt_count: .prompts,
            sonnet_responses: .sonnet,
            opus_responses: .opus,
            input_tokens: .input_tokens,
            output_tokens: .output_tokens
        }
    ' "$jsonl_path" 2>/dev/null || echo '{}'
}

# Calculate usage statistics across all sessions
# Output: JSON object with usage data on stdout
usage_tracker_calculate() {
    local week_start cycle_start
    week_start=$(_usage_get_week_start)
    cycle_start=$(_usage_get_5h_cycle_start)

    log_debug "Week start: $week_start, 5h cycle start: $cycle_start"
    log_debug "Projects dir: $_USAGE_TRACKER_PROJECTS_DIR"

    if [ ! -d "$_USAGE_TRACKER_PROJECTS_DIR" ]; then
        log_warn "Claude projects directory not found: $_USAGE_TRACKER_PROJECTS_DIR"
        _usage_empty_result "$week_start" "$cycle_start"
        return 0
    fi

    # Only process files modified since the week start (avoids scanning thousands of old files)
    local week_start_date
    week_start_date=$(date -d "@$week_start" +%Y-%m-%dT%H:%M:%S 2>/dev/null) || \
        week_start_date=$(date -r "$week_start" +%Y-%m-%dT%H:%M:%S 2>/dev/null) || \
        week_start_date=""

    local find_args=(-name "*.jsonl")
    if [ -n "$week_start_date" ]; then
        find_args+=(-newermt "$week_start_date")
    fi

    # Process files in parallel using xargs -P with jq directly (no bash re-sourcing)
    local sessions_ndjson
    sessions_ndjson=$(find "$_USAGE_TRACKER_PROJECTS_DIR" "${find_args[@]}" -print0 2>/dev/null | \
        xargs -0 -P"${USAGE_TRACKER_JOBS:-$(nproc)}" -n1 jq -s -r '
            reduce .[] as $msg (
                {"timestamps": [], "prompts": 0, "sonnet": 0, "opus": 0,
                 "input_tokens": 0, "output_tokens": 0, "cache_read_tokens": 0, "cache_create_tokens": 0};

                (if $msg.timestamp then
                    .timestamps += [$msg.timestamp]
                else . end) |

                (if ($msg.type == "user" and
                     ($msg.message // {}).role == "user" and
                     ($msg.isMeta // false | not) and
                     $msg.userType == "external")
                then
                    (($msg.message // {}).content // "") as $content |
                    if ($content | type) == "string" then
                        if ($content != "" and
                            ($content | contains("<command-name>") | not) and
                            ($content | contains("<local-command-stdout>") | not))
                        then .prompts += 1
                        else .
                        end
                    elif ($content | type) == "array" then
                        ([$content[] |
                            select(.type == "text") |
                            .text // "" |
                            select(contains("<command-name>") or contains("<local-command-stdout>"))
                        ] | length) as $cmd_count |
                        if $cmd_count == 0 and ($content | length) > 0
                        then .prompts += 1
                        else .
                        end
                    else .
                    end
                else . end) |

                (if $msg.type == "assistant" then
                    (($msg.message // {}).model // "" | ascii_downcase) as $model |
                    (($msg.message // {}).usage // {}) as $usage |
                    (if ($model | contains("opus")) then .opus += 1
                    elif ($model | contains("sonnet")) then .sonnet += 1
                    else .
                    end) |
                    .input_tokens += (($usage.input_tokens // 0) + ($usage.cache_read_input_tokens // 0) + ($usage.cache_creation_input_tokens // 0)) |
                    .output_tokens += ($usage.output_tokens // 0)
                else . end)
            ) |

            (.timestamps | map(
                sub("\\.[0-9]+"; "") |
                (if endswith("Z") then 0
                 elif test("[+-][0-9]{2}:[0-9]{2}$") then
                    ((.[-6:] | split(":") |
                        ((.[0] | tonumber) * 3600) + ((.[1] | tonumber) * 60)
                    ))
                 elif test("[+-][0-9]{4}$") then
                    ((.[-5:] |
                        (.[0:3] | tonumber) * 3600 + (.[3:5] | tonumber) * 60
                    ))
                 else 0 end) as $tz_offset |
                sub("Z$"; "") | sub("[+-][0-9]{2}:?[0-9]{2}$"; "") |
                try ((strptime("%Y-%m-%dT%H:%M:%S") | mktime) - $tz_offset) catch null
            ) | map(select(. != null))) as $epochs |

            ($epochs | if length > 0 then min else 0 end) as $start |
            ($epochs | if length > 0 then max else 0 end) as $end |
            (if $start > 0 and $end > 0 then (($end - $start) / 3600) else 0 end) as $duration |

            {
                start_time: $start,
                end_time: $end,
                duration_hours: $duration,
                prompt_count: .prompts,
                sonnet_responses: .sonnet,
                opus_responses: .opus,
                input_tokens: .input_tokens,
                output_tokens: .output_tokens
            }
        ' 2>/dev/null | grep -v '^{}$')

    # Aggregate: filter out empty/zero-duration sessions and calculate stats
    echo "$sessions_ndjson" | jq -s --argjson week_start "$week_start" \
                                     --argjson cycle_start "$cycle_start" '
        # Remove empty objects and zero-duration sessions
        map(select(.duration_hours > 0)) |

        # Filter sessions by time window
        (map(select(.start_time >= $week_start))) as $week_sessions |
        (map(select(.start_time >= $cycle_start))) as $cycle_sessions |

        # 5-hour cycle stats
        ($cycle_sessions | map(.prompt_count) | add // 0) as $cycle_prompts |
        ($cycle_sessions | map(.input_tokens) | add // 0) as $cycle_input_tokens |
        ($cycle_sessions | map(.output_tokens) | add // 0) as $cycle_output_tokens |

        # Weekly stats
        ($week_sessions | map(.prompt_count) | add // 0) as $weekly_prompts |
        ($week_sessions | map(.input_tokens) | add // 0) as $weekly_input_tokens |
        ($week_sessions | map(.output_tokens) | add // 0) as $weekly_output_tokens |

        # Model-specific hours (proportioned by response ratio)
        ($week_sessions | reduce .[] as $s (
            {"sonnet_hours": 0, "opus_hours": 0};
            ($s.sonnet_responses + $s.opus_responses) as $total |
            if $total > 0 then
                .sonnet_hours += ($s.duration_hours * ($s.sonnet_responses / $total)) |
                .opus_hours += ($s.duration_hours * ($s.opus_responses / $total))
            else .
            end
        )) as $model_hours |

        {
            current_5h_cycle: {
                start_time: ($cycle_start * 1000 | floor),
                total_prompts: $cycle_prompts,
                input_tokens: $cycle_input_tokens,
                output_tokens: $cycle_output_tokens
            },
            current_week: {
                start_time: ($week_start * 1000 | floor),
                sonnet_hours: ($model_hours.sonnet_hours * 100 | round / 100),
                opus_hours: ($model_hours.opus_hours * 100 | round / 100),
                total_prompts: $weekly_prompts,
                total_sessions: ($week_sessions | length),
                input_tokens: $weekly_input_tokens,
                output_tokens: $weekly_output_tokens
            },
            last_updated: (now * 1000 | floor)
        }
    '
}

# Generate empty result JSON
_usage_empty_result() {
    local week_start="$1"
    local cycle_start="$2"
    local now_ms
    now_ms=$(( $(date +%s) * 1000 ))

    cat <<EOF
{
  "current_5h_cycle": {
    "start_time": $(( cycle_start * 1000 )),
    "total_prompts": 0,
    "input_tokens": 0,
    "output_tokens": 0
  },
  "current_week": {
    "start_time": $(( week_start * 1000 )),
    "sonnet_hours": 0,
    "opus_hours": 0,
    "total_prompts": 0,
    "total_sessions": 0,
    "input_tokens": 0,
    "output_tokens": 0
  },
  "last_updated": $now_ms
}
EOF
}

# Save usage data JSON to file
# Args: $1 = JSON string of usage data
usage_tracker_save() {
    local usage_json="$1"
    local output_dir="${_USAGE_TRACKER_DATA_DIR}"

    mkdir -p "$output_dir"

    local output_file="$output_dir/usage_data.json"
    echo "$usage_json" | jq '.' > "$output_file"
    log_debug "Usage data saved to $output_file"
}

# Calculate and save usage data (main entry point)
# Output: prints usage JSON to stdout
usage_tracker_update() {
    local usage_json
    usage_json=$(usage_tracker_calculate)
    usage_tracker_save "$usage_json"
    echo "$usage_json"
}

# Write usage JSON to a shared .ralph/claude-usage.json file
# Args: $1 = ralph directory path
# Output: prints usage JSON to stdout
usage_tracker_write_shared() {
    local ralph_dir="$1"
    local usage_json
    usage_json=$(usage_tracker_calculate)
    mkdir -p "$ralph_dir"
    echo "$usage_json" > "$ralph_dir/claude-usage.json"
    echo "$usage_json"
}

# Check if rate limit threshold has been exceeded
# Args: $1 = ralph directory path
# Returns: 0 if over threshold (rate limited), 1 if OK
rate_limit_check() {
    local ralph_dir="$1"
    local usage_file="$ralph_dir/claude-usage.json"
    local config_file="${WIGGUM_HOME}/config/config.json"

    # Read threshold from config, env var, or use default
    local threshold="${WIGGUM_RATE_LIMIT_THRESHOLD:-}"
    if [ -z "$threshold" ] && [ -f "$config_file" ]; then
        threshold=$(jq -r '.rate_limit.threshold_prompts // empty' "$config_file" 2>/dev/null)
    fi
    threshold="${threshold:-900}"

    if [ ! -f "$usage_file" ]; then
        return 1  # No data = not rate limited
    fi

    # Get the current cycle start time
    local current_cycle_start
    current_cycle_start=$(_usage_get_5h_cycle_start)
    local current_cycle_start_ms=$(( current_cycle_start * 1000 ))

    # Get stored cycle start time from usage file
    local stored_cycle_start_ms
    stored_cycle_start_ms=$(jq -r '.current_5h_cycle.start_time // 0' "$usage_file" 2>/dev/null)

    # If stored cycle is from a previous cycle, data is stale - not rate limited
    if [ "$stored_cycle_start_ms" -lt "$current_cycle_start_ms" ]; then
        return 1  # Stale data from old cycle = not rate limited
    fi

    local cycle_prompts
    cycle_prompts=$(jq -r '.current_5h_cycle.total_prompts // 0' "$usage_file" 2>/dev/null)

    if [ "$cycle_prompts" -ge "$threshold" ]; then
        return 0  # Rate limited
    fi
    return 1  # OK
}

# Wait until the current 5-hour cycle resets, logging periodically
rate_limit_wait_for_cycle_reset() {
    local now cycle_start cycle_end wait_seconds
    now=$(date +%s)
    cycle_start=$(_usage_get_5h_cycle_start)
    cycle_end=$(( cycle_start + 18000 ))  # 5 hours
    wait_seconds=$(( cycle_end - now ))

    if [ "$wait_seconds" -le 0 ]; then
        return 0
    fi

    log "Rate limit reached. Waiting ${wait_seconds}s for 5h cycle reset ($(date_format_epoch "$cycle_end" "%H:%M:%S"))"

    local elapsed=0
    while [ "$elapsed" -lt "$wait_seconds" ]; do
        local remaining=$(( wait_seconds - elapsed ))
        local remaining_min=$(( remaining / 60 ))
        log "Rate limit: ${remaining_min}m remaining until cycle reset"
        local sleep_interval=300
        if [ "$remaining" -lt 300 ]; then
            sleep_interval="$remaining"
        fi
        sleep "$sleep_interval"
        elapsed=$(( elapsed + sleep_interval ))
    done

    log "Rate limit cycle reset complete - resuming"
}
