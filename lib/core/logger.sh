#!/usr/bin/env bash
# Logging utilities for Chief Wiggum
#
# Log Levels (in order of severity):
#   TRACE - Very detailed tracing information (LOG_LEVEL=TRACE)
#   DEBUG - Detailed diagnostic information (only when DEBUG=1 or LOG_LEVEL=DEBUG)
#   INFO  - General operational messages (default level)
#   WARN  - Warning conditions that should be reviewed
#   ERROR - Error conditions requiring attention
#
# Environment variables:
#   LOG_FILE  - Optional file to append all logs to (in addition to stdout/stderr)
#   LOG_LEVEL - Minimum level to output: TRACE, DEBUG, INFO, WARN, ERROR (default: INFO)
#   DEBUG     - If set to 1, equivalent to LOG_LEVEL=DEBUG (legacy compatibility)
set -euo pipefail

# Log level numeric values for comparison
_log_level_value() {
    case "$1" in
        TRACE) echo 0 ;;
        DEBUG) echo 1 ;;
        INFO)  echo 2 ;;
        WARN)  echo 3 ;;
        ERROR) echo 4 ;;
        *)     echo 2 ;;  # default to INFO
    esac
}

# Cache numeric min level at source time for fast-path filtering
_CACHED_MIN_LEVEL=$(_log_level_value "${LOG_LEVEL:-INFO}")
if [[ "${DEBUG:-0}" == "1" ]] && (( _CACHED_MIN_LEVEL > 1 )); then
    _CACHED_MIN_LEVEL=1
fi

# Detect printf %()T support (bash 4.2+, avoids date subprocess per log line)
_LOG_HAS_PRINTF_T=0
if printf '%(%s)T' -1 &>/dev/null; then
    _LOG_HAS_PRINTF_T=1
fi

# Check if a log level should be output
_should_log() {
    local level="$1"
    local min_level="${LOG_LEVEL:-INFO}"

    # DEBUG=1 overrides LOG_LEVEL for backwards compatibility
    if [[ "${DEBUG:-0}" == "1" ]]; then
        min_level="DEBUG"
    fi

    local level_val min_val
    level_val=$(_log_level_value "$level")
    min_val=$(_log_level_value "$min_level")

    [[ $level_val -ge $min_val ]]
}

# Internal: format and output a log message
_log_output() {
    local level="$1"
    local message="$2"
    local stream="${3:-1}"  # 1=stdout, 2=stderr

    # Check if we should log at this level
    if ! _should_log "$level"; then
        return
    fi

    local timestamp
    if (( _LOG_HAS_PRINTF_T )); then
        printf -v timestamp '%(%Y-%m-%dT%H:%M:%S%z)T' -1
    else
        timestamp=$(date -Iseconds)
    fi
    local formatted="[$timestamp] ${level}: $message"

    # Output to appropriate stream
    if [[ "$stream" == "2" ]]; then
        echo "$formatted" >&2
    else
        echo "$formatted"
    fi

    # Append to LOG_FILE if set (with locking to prevent interleaving)
    if [[ -n "${LOG_FILE:-}" ]]; then
        # Skip locking for special files like /dev/null
        if [[ "$LOG_FILE" == "/dev/"* ]]; then
            echo "$formatted" >> "$LOG_FILE" 2>/dev/null || true
        else
            # Use flock for regular files to prevent interleaved writes
            # Fallback to unlocked write if locking fails
            local lock_file="${LOG_FILE}.lock"
            if [[ -w "$(dirname "$LOG_FILE")" ]] 2>/dev/null; then
                {
                    flock -w 1 200 2>/dev/null && echo "$formatted" >> "$LOG_FILE"
                } 200>"$lock_file" 2>/dev/null || echo "$formatted" >> "$LOG_FILE" 2>/dev/null
            else
                echo "$formatted" >> "$LOG_FILE" 2>/dev/null
            fi
        fi
    fi
    return 0
}

# Log at INFO level (to stdout)
log() {
    (( _CACHED_MIN_LEVEL <= 2 )) || return 0
    _log_output "INFO" "$1" 1
}

# Alias for log() with explicit name
log_info() {
    (( _CACHED_MIN_LEVEL <= 2 )) || return 0
    _log_output "INFO" "$1" 1
}

# Log at WARN level (to stderr)
log_warn() {
    (( _CACHED_MIN_LEVEL <= 3 )) || return 0
    _log_output "WARN" "$1" 2
}

# Log at ERROR level (to stderr)
log_error() {
    (( _CACHED_MIN_LEVEL <= 4 )) || return 0
    _log_output "ERROR" "$1" 2
}

# Log at DEBUG level (to stderr, only when DEBUG=1 or LOG_LEVEL=DEBUG)
log_debug() {
    (( _CACHED_MIN_LEVEL <= 1 )) || [[ "${DEBUG:-0}" == "1" ]] || [[ "${LOG_LEVEL:-}" == "DEBUG" ]] || [[ "${LOG_LEVEL:-}" == "TRACE" ]] || return 0
    _log_output "DEBUG" "$1" 2
}

# Log at TRACE level (to stderr, only when LOG_LEVEL=TRACE)
log_trace() {
    (( _CACHED_MIN_LEVEL <= 0 )) || [[ "${LOG_LEVEL:-}" == "TRACE" ]] || return 0
    _log_output "TRACE" "$1" 2
}

# Redact sensitive patterns from log output
# Masks API keys, tokens, and other credentials
_redact_sensitive() {
    local line="$1"
    # Redact common credential patterns:
    # - ANTHROPIC_AUTH_TOKEN, API_KEY, SECRET_KEY, etc.
    # - Bearer tokens
    # - sk- prefix keys (API keys)
    # - Base64-encoded secrets (long alphanumeric strings after = or :)
    line=$(printf '%s' "$line" | sed -E \
        -e 's/(ANTHROPIC_AUTH_TOKEN|ANTHROPIC_API_KEY|API_KEY|SECRET_KEY|AUTH_TOKEN|ACCESS_TOKEN|PRIVATE_KEY)=([^[:space:]]+)/\1=[REDACTED]/gi' \
        -e 's/(GH_TOKEN|GITHUB_TOKEN|GITHUB_PAT_TOKEN|AWS_SECRET_ACCESS_KEY|AWS_SESSION_TOKEN|DATABASE_URL)=([^[:space:]]+)/\1=[REDACTED]/gi' \
        -e 's/(Bearer )[A-Za-z0-9_\-\.]+/\1[REDACTED]/g' \
        -e 's/(sk-|ghp_|gho_|ghs_|ghu_|github_pat_)[A-Za-z0-9\-_]{20,}/\1[REDACTED]/g' \
        -e 's/(password[=:]["'"'"']?)[^[:space:]"'"'"']+/\1[REDACTED]/gi')
    printf '%s' "$line"
}

# Capture command output with logging
# Usage: log_command "description" command args...
# Output goes to stdout and LOG_FILE (if set)
# Security: Redacts sensitive credentials from logged output
log_command() {
    local description="$1"
    shift
    log_debug "Executing: $description"
    if [[ -n "${LOG_FILE:-}" ]]; then
        "$@" 2>&1 | while IFS= read -r line; do
            local redacted_line ts
            redacted_line=$(_redact_sensitive "$line")
            if (( _LOG_HAS_PRINTF_T )); then
                printf -v ts '%(%Y-%m-%dT%H:%M:%S%z)T' -1
            else
                ts=$(date -Iseconds)
            fi
            echo "[$ts] OUTPUT: $redacted_line" | tee -a "$LOG_FILE"
        done
    else
        "$@" 2>&1 | while IFS= read -r line; do
            _redact_sensitive "$line"
            echo
        done
    fi
}

# =============================================================================
# SECTION DIVIDERS AND HEADERS
# =============================================================================

# Log a major section divider (double line)
# Usage: log_section "Section Name"
log_section() {
    local title="$1"
    local width=70
    local line
    line=$(printf '=%.0s' $(seq 1 $width))

    _log_output "INFO" "" 1
    _log_output "INFO" "$line" 1
    _log_output "INFO" "  $title" 1
    _log_output "INFO" "$line" 1
}

# Log a minor section divider (single line)
# Usage: log_subsection "Subsection Name"
log_subsection() {
    local title="$1"
    local width=70
    local line
    line=$(printf -- '-%.0s' $(seq 1 $width))

    _log_output "INFO" "" 1
    _log_output "INFO" "$line" 1
    _log_output "INFO" "  $title" 1
    _log_output "INFO" "$line" 1
}

# Log a key-value pair (for config display)
# Usage: log_kv "key" "value"
log_kv() {
    local key="$1"
    local value="$2"
    local padding=25

    printf -v formatted "  %-${padding}s : %s" "$key" "$value"
    _log_output "INFO" "$formatted" 1
}

# Log agent header with full context
# Usage: log_agent_header "agent_type" "worker_id" "task_id"
log_agent_header() {
    local agent_type="$1"
    local worker_id="${2:-}"
    local task_id="${3:-}"
    local step_id="${WIGGUM_STEP_ID:-}"

    log_section "AGENT: $agent_type"
    [ -n "$step_id" ] && log_kv "Step ID" "$step_id"
    [ -n "$worker_id" ] && log_kv "Worker ID" "$worker_id"
    [ -n "$task_id" ] && log_kv "Task ID" "$task_id"
    local _started_ts
    if (( _LOG_HAS_PRINTF_T )); then
        printf -v _started_ts '%(%Y-%m-%dT%H:%M:%S%z)T' -1
    else
        _started_ts=$(date -Iseconds)
    fi
    log_kv "Started" "$_started_ts"
}

# Log agent completion with status
# Usage: log_agent_complete "agent_type" "exit_code" "duration_secs"
log_agent_complete() {
    local agent_type="$1"
    local exit_code="${2:-0}"
    local duration="${3:-}"
    local status="SUCCESS"

    [ "$exit_code" -ne 0 ] && status="FAILED (exit=$exit_code)"

    log_subsection "COMPLETED: $agent_type"
    log_kv "Status" "$status"
    [ -n "$duration" ] && log_kv "Duration" "${duration}s"
    local _finished_ts
    if (( _LOG_HAS_PRINTF_T )); then
        printf -v _finished_ts '%(%Y-%m-%dT%H:%M:%S%z)T' -1
    else
        _finished_ts=$(date -Iseconds)
    fi
    log_kv "Finished" "$_finished_ts"
    _log_output "INFO" "" 1
}

# Log configuration block
# Usage: log_config_block "Config Name" <<< "key1=val1\nkey2=val2"
# Or: log_config_block "Config Name" "key1" "val1" "key2" "val2"
log_config_block() {
    local title="$1"
    shift

    log_subsection "CONFIG: $title"

    if [ $# -eq 0 ]; then
        # Read from stdin
        while IFS='=' read -r key value; do
            [ -n "$key" ] && log_kv "$key" "$value"
        done
    else
        # Read from args (key value pairs)
        while [ $# -ge 2 ]; do
            log_kv "$1" "$2"
            shift 2
        done
    fi
}
