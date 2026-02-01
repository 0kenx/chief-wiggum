#!/usr/bin/env bash
# log-rotation.sh - Automatic archival and rotation for global log files
#
# Rotates .log and .jsonl files in .ralph/logs/ when they exceed a
# configurable line threshold. Archived logs are gzip-compressed and
# stored in .ralph/logs/archive/.
#
# Uses the same flock pattern as _log_output() and append_with_lock()
# for concurrency safety. Truncation preserves the inode so existing
# writers and tail -f continue working.
set -euo pipefail

# Prevent double-sourcing
[ -n "${_LOG_ROTATION_LOADED:-}" ] && return 0
_LOG_ROTATION_LOADED=1

# Module state (set by log_rotation_init)
_LR_LOGS_DIR=""
_LR_ARCHIVE_DIR=""
_LR_ENABLED="true"
_LR_MAX_LINES=10000
_LR_MAX_ARCHIVES=10

# Initialize log rotation module
#
# Args:
#   logs_dir - Path to the logs directory (e.g., .ralph/logs)
#
# Loads config from env vars (override config.json values loaded by defaults.sh):
#   WIGGUM_LOG_ROTATE_ENABLED      - Master on/off (default: true)
#   WIGGUM_LOG_ROTATE_LINES        - Lines before rotation (default: 10000)
#   WIGGUM_LOG_ROTATE_MAX_ARCHIVES - Max archives per log file (default: 10)
log_rotation_init() {
    local logs_dir="$1"

    _LR_LOGS_DIR="$logs_dir"
    _LR_ARCHIVE_DIR="$logs_dir/archive"

    # Load config (env vars take precedence, then config.json cache, then defaults)
    _LR_ENABLED="${WIGGUM_LOG_ROTATE_ENABLED:-${_CACHE_LOG_ROTATE_ENABLED:-true}}"
    _LR_MAX_LINES="${WIGGUM_LOG_ROTATE_LINES:-${_CACHE_LOG_ROTATE_LINES:-10000}}"
    _LR_MAX_ARCHIVES="${WIGGUM_LOG_ROTATE_MAX_ARCHIVES:-${_CACHE_LOG_ROTATE_MAX_ARCHIVES:-10}}"

    mkdir -p "$_LR_ARCHIVE_DIR"
}

# Check all log files in the logs directory and rotate any that exceed threshold
#
# Iterates *.log and *.jsonl files. Skips if rotation is disabled.
log_rotation_check_all() {
    [[ "$_LR_ENABLED" == "true" ]] || return 0
    [[ -n "$_LR_LOGS_DIR" ]] || return 0
    [[ -d "$_LR_LOGS_DIR" ]] || return 0

    local file
    for file in "$_LR_LOGS_DIR"/*.log "$_LR_LOGS_DIR"/*.jsonl; do
        [ -f "$file" ] || continue
        log_rotation_check "$file"
    done
}

# Check a single log file and rotate if it exceeds the line threshold
#
# Fast-path: skips wc -l if the file's byte size is below an estimated
# threshold (max_lines * 80 bytes/line).
#
# Args:
#   log_file - Path to the log file to check
log_rotation_check() {
    local log_file="$1"
    [ -f "$log_file" ] || return 0

    # Fast-path: skip wc -l if file is obviously small
    local file_size=0
    file_size=$(wc -c < "$log_file" 2>/dev/null) || return 0
    file_size="${file_size:-0}"
    local byte_threshold=$(( _LR_MAX_LINES * 80 ))
    if (( file_size < byte_threshold )); then
        return 0
    fi

    # File is large enough to warrant a line count check
    local line_count=0
    line_count=$(wc -l < "$log_file" 2>/dev/null) || return 0
    line_count="${line_count:-0}"
    # Trim whitespace (macOS wc pads output)
    line_count="${line_count// /}"

    if (( line_count > _LR_MAX_LINES )); then
        _log_rotation_rotate_file "$log_file"
    fi
}

# Rotate a single log file under flock
#
# Re-verifies line count inside the lock (another process may have rotated).
# Gzip-compresses contents to archive, then truncates the live file
# (preserving inode). Special handling for audit.log to preserve its header.
#
# Args:
#   log_file - Path to the log file to rotate
_log_rotation_rotate_file() {
    local log_file="$1"
    local lock_file="${log_file}.lock"
    local basename
    basename=$(basename "$log_file")

    (
        flock -w 5 200 || return 0

        # Re-verify under lock
        local line_count=0
        line_count=$(wc -l < "$log_file" 2>/dev/null) || return 0
        line_count="${line_count:-0}"
        line_count="${line_count// /}"
        if (( line_count <= _LR_MAX_LINES )); then
            return 0
        fi

        local epoch
        epoch=$(date +%s)
        local archive_file="$_LR_ARCHIVE_DIR/${basename}.${epoch}.gz"

        # Special handling for audit.log: preserve header
        if [[ "$basename" == "audit.log" ]]; then
            _log_rotation_rotate_audit "$log_file" "$archive_file"
        else
            # Compress entire file content to archive
            gzip -c "$log_file" > "$archive_file"
            # Truncate in place (preserves inode)
            : > "$log_file"
        fi

        # Prune old archives beyond max_archives limit
        _log_rotation_prune "$basename"

    ) 200>"$lock_file"
}

# Rotate audit.log preserving its header (lines up to and including ==== separator)
#
# Args:
#   log_file     - Path to the audit.log file
#   archive_file - Path to the archive .gz file
_log_rotation_rotate_audit() {
    local log_file="$1"
    local archive_file="$2"

    local header_end=0
    local line_num=0
    while IFS= read -r line; do
        ((++line_num))
        if [[ "$line" == ====* ]]; then
            header_end=$line_num
            break
        fi
    done < "$log_file"

    if (( header_end > 0 )); then
        # Archive only data lines (after header)
        tail -n +"$((header_end + 1))" "$log_file" | gzip -c > "$archive_file"
        # Keep header, truncate data
        local header
        header=$(head -n "$header_end" "$log_file")
        printf '%s\n' "$header" > "$log_file"
    else
        # No header found, rotate entire file
        gzip -c "$log_file" > "$archive_file"
        : > "$log_file"
    fi
}

# Remove oldest archives beyond max_archives limit for a given log basename
#
# Args:
#   basename - The log file basename (e.g., "orchestrator.log")
_log_rotation_prune() {
    local basename="$1"
    local archive_dir="$_LR_ARCHIVE_DIR"

    # Count existing archives for this basename
    local archives=()
    local f
    for f in "$archive_dir/${basename}".*.gz; do
        [ -f "$f" ] || continue
        archives+=("$f")
    done

    local count=${#archives[@]}
    if (( count <= _LR_MAX_ARCHIVES )); then
        return 0
    fi

    # Sort by epoch (extracted from filename) ascending, remove oldest
    local sorted
    sorted=$(printf '%s\n' "${archives[@]}" | sort)
    local to_remove=$(( count - _LR_MAX_ARCHIVES ))
    local removed=0
    while IFS= read -r archive; do
        [ -f "$archive" ] || continue
        rm -f "$archive"
        ((++removed))
        if (( removed >= to_remove )); then
            break
        fi
    done <<< "$sorted"
}
