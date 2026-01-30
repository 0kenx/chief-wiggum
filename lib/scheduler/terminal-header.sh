#!/usr/bin/env bash
# terminal-header.sh - htop-style full-screen header for wiggum run
#
# Provides an htop-style full-screen display with a fixed header at the top
# showing current worker status, and captured log output scrolling below.
#
# Uses alternate screen buffer (like htop, vim, less) for clean terminal handling:
#   - Top zone (fixed header): Compact worker status, refreshed each iteration
#   - Bottom zone (log area): Tail of captured log output
#
# All stdout/stderr is redirected to a temp buffer file while active.
# Each refresh composites header + log tail into a single write (no flicker).
#
# Disabled (all functions no-op) when:
#   - stdout is not a TTY
#   - $TERM is unset or "dumb"
#   - WIGGUM_NO_HEADER=1 is set
#
# shellcheck disable=SC2154  # _th_now, _th_entries set via dynamic scope
set -euo pipefail

[ -n "${_TERMINAL_HEADER_LOADED:-}" ] && return 0
_TERMINAL_HEADER_LOADED=1

# =============================================================================
# Module State
# =============================================================================

_TH_ENABLED=false
_TH_TERM_ROWS=0
_TH_TERM_COLS=0
_TH_LAST_CONTENT=""
_TH_RUN_MODE=""
_TH_MAX_LINES="${WIGGUM_HEADER_MAX_LINES:-12}"
_TH_LOG_FILE=""
_TH_FDS_REDIRECTED=false

# Cached status counts (set by terminal_header_set_status_data)
_TH_READY_COUNT=0
_TH_BLOCKED_COUNT=0
_TH_DEFERRED_COUNT=0
_TH_CYCLIC_COUNT=0
_TH_ERROR_COUNT=0
_TH_STUCK_COUNT=0

# =============================================================================
# Public API
# =============================================================================

# Initialize the terminal header
#
# Enters alternate screen buffer, hides cursor, redirects stdout/stderr
# to a temp log buffer file. No-ops if stdout is not a TTY, TERM is dumb,
# or WIGGUM_NO_HEADER=1.
#
# Args:
#   max_workers - Maximum concurrent workers
#   run_mode    - Run mode description (e.g., "standard", "plan mode")
terminal_header_init() {
    local max_workers="$1"
    local run_mode="$2"

    # Disable if not interactive or explicitly opted out
    if [[ ! -t 1 ]] || [[ -z "${TERM:-}" ]] || [[ "${TERM:-}" == "dumb" ]] \
       || [[ "${WIGGUM_NO_HEADER:-}" == "1" ]]; then
        _TH_ENABLED=false
        return 0
    fi

    # Verify /dev/tty is writable
    if ! printf '' > /dev/tty 2>/dev/null; then
        _TH_ENABLED=false
        return 0
    fi

    _TH_ENABLED=true
    _TH_RUN_MODE="$run_mode"

    _terminal_header_query_size

    # Create temp log buffer file
    _TH_LOG_FILE=$(mktemp "${TMPDIR:-/tmp}/wiggum-log.XXXXXX")

    # Save original stdout/stderr (fd 3/4) and redirect to log file
    exec 3>&1 4>&2
    exec 1>>"$_TH_LOG_FILE" 2>>"$_TH_LOG_FILE"
    _TH_FDS_REDIRECTED=true

    # Disable keyboard echo so arrow keys / scroll don't print ^[[A/^[[B
    stty -echo < /dev/tty 2>/dev/null || true

    # Enter alternate screen buffer and hide cursor
    printf '\033[?1049h\033[?25l' > /dev/tty 2>/dev/null || true
}

# Refresh the header with current worker status
#
# Rebuilds header content from the worker pool and composites a full
# frame (header + log tail) written to /dev/tty in a single call.
#
# Args:
#   iteration   - Current loop iteration number
#   max_workers - Maximum concurrent workers
terminal_header_refresh() {
    [[ "$_TH_ENABLED" == true ]] || return 0

    local iteration="$1"
    local max_workers="$2"

    _terminal_header_query_size

    local content
    content=$(_terminal_header_build_content "$iteration" "$max_workers")
    _TH_LAST_CONTENT="$content"

    _terminal_header_render_frame "$content"
}

# Force the next refresh to redraw (clear cached content)
terminal_header_force_redraw() {
    _TH_LAST_CONTENT=""
}

# Clean up terminal state
#
# Restores stdout/stderr, shows cursor, exits alternate screen buffer,
# and prints the last 20 lines of captured log output to the restored
# terminal. Safe to call multiple times.
terminal_header_cleanup() {
    [[ "$_TH_ENABLED" == true ]] || return 0
    _TH_ENABLED=false

    # Restore stdout/stderr before any other output
    if [[ "$_TH_FDS_REDIRECTED" == true ]]; then
        exec 1>&3 2>&4
        exec 3>&- 4>&-
        _TH_FDS_REDIRECTED=false
    fi

    # Show cursor and exit alternate screen buffer
    printf '\033[?25h\033[?1049l' > /dev/tty 2>/dev/null || true

    # Restore keyboard echo
    stty echo < /dev/tty 2>/dev/null || true

    # Print last 20 log lines to the restored terminal
    if [[ -n "$_TH_LOG_FILE" ]] && [[ -f "$_TH_LOG_FILE" ]]; then
        tail -n 20 "$_TH_LOG_FILE" 2>/dev/null || true
        rm -f "$_TH_LOG_FILE" 2>/dev/null || true
        _TH_LOG_FILE=""
    fi
}

# Check if header mode is active
#
# Returns: 0 if enabled, 1 if disabled
terminal_header_is_enabled() {
    [[ "$_TH_ENABLED" == true ]]
}

# Set cached status counts for header display
#
# Called by the scheduler on each scheduling event to update the status
# summary line shown in the fixed header.
#
# Args:
#   ready    - Ready task count
#   blocked  - Blocked task count
#   deferred - Deferred (file conflict) task count
#   cyclic   - Cyclic dependency task count
#   errors   - Recent error count
#   stuck    - Stuck worker count
terminal_header_set_status_data() {
    _TH_READY_COUNT="${1:-0}"
    _TH_BLOCKED_COUNT="${2:-0}"
    _TH_DEFERRED_COUNT="${3:-0}"
    _TH_CYCLIC_COUNT="${4:-0}"
    _TH_ERROR_COUNT="${5:-0}"
    _TH_STUCK_COUNT="${6:-0}"
}

# =============================================================================
# SIGWINCH Handler
# =============================================================================

# Handle terminal resize - re-query size, force redraw on next refresh
_terminal_header_on_resize() {
    [[ "$_TH_ENABLED" == true ]] || return 0

    _terminal_header_query_size
    _TH_LAST_CONTENT=""
}

# =============================================================================
# Internal Helpers
# =============================================================================

# Query terminal dimensions via /dev/tty (works with redirected stdout)
_terminal_header_query_size() {
    local size
    if size=$(stty size < /dev/tty 2>/dev/null); then
        _TH_TERM_ROWS="${size%% *}"
        _TH_TERM_COLS="${size##* }"
    else
        _TH_TERM_ROWS=${_TH_TERM_ROWS:-24}
        _TH_TERM_COLS=${_TH_TERM_COLS:-80}
    fi
}

# Render full screen: header content + tail of log buffer
#
# Builds the entire frame in a variable and writes it to /dev/tty in
# a single printf call, eliminating flicker.
#
# Args:
#   content - Multi-line header content string
_terminal_header_render_frame() {
    local content="$1"

    # Count header lines
    local header_lines
    header_lines=$(printf '%s\n' "$content" | wc -l)
    header_lines=$((header_lines))  # trim whitespace from wc

    # Calculate log area rows
    local log_rows=$((_TH_TERM_ROWS - header_lines))
    [[ "$log_rows" -ge 0 ]] || log_rows=0

    # Collect all frame lines into an array
    local -a frame_lines=()

    # Header lines
    while IFS= read -r line; do
        frame_lines+=("$line")
    done <<< "$content"

    # Log lines from buffer tail
    if [[ "$log_rows" -gt 0 ]] && [[ -n "$_TH_LOG_FILE" ]] && [[ -f "$_TH_LOG_FILE" ]]; then
        local -a log_lines=()
        mapfile -t log_lines < <(tail -n "$log_rows" "$_TH_LOG_FILE" 2>/dev/null || true)

        local i
        for ((i = 0; i < log_rows; i++)); do
            frame_lines+=("${log_lines[$i]:-}")
        done
    fi

    # Build frame: home cursor + hide cursor + lines with clear-to-EOL
    local frame=$'\033[H\033[?25l'
    local total=${#frame_lines[@]}
    local j
    for ((j = 0; j < total; j++)); do
        frame+="${frame_lines[$j]}"$'\033[K'
        if ((j < total - 1)); then
            frame+=$'\n'
        fi
    done

    # Single write of entire frame to terminal
    printf '%s' "$frame" > /dev/tty 2>/dev/null || true
}

# Callback for pool_foreach - collects worker entries into _th_entries array
#
# Uses dynamic scoping to access _th_entries and _th_now from
# _terminal_header_build_content.
#
# Args (from pool_foreach):
#   $1 - pid
#   $2 - type (main|fix|resolve)
#   $3 - task_id
#   $4 - start_time (epoch)
_th_collect_worker() {
    local pid="$1" type="$2" task_id="$3" start_time="$4"
    local elapsed=$((_th_now - start_time))
    local mins=$((elapsed / 60))
    local secs=$((elapsed % 60))
    local entry
    printf -v entry '%-10s %-7s PID:%-7s %dm%02ds' "$task_id" "$type" "$pid" "$mins" "$secs"
    _th_entries+=("$entry")
}

# Build header content as a multi-line string on stdout
#
# Args:
#   iteration   - Current loop iteration
#   max_workers - Maximum concurrent workers
_terminal_header_build_content() {
    local iteration="$1"
    local max_workers="$2"
    local _th_now
    _th_now=$(date +%s)

    # Gather worker counts
    local main_count fix_count resolve_count total_count
    main_count=$(pool_count "main")
    fix_count=$(pool_count "fix")
    resolve_count=$(pool_count "resolve")
    total_count=$((main_count + fix_count + resolve_count))

    # --- Banner line ---
    local banner
    printf -v banner '── Chief Wiggum ── %s ── workers: %d/%d ── fix:%d resolve:%d ── iter %d ──' \
        "$_TH_RUN_MODE" "$main_count" "$max_workers" "$fix_count" "$resolve_count" "$iteration"

    # Pad banner with ─ to terminal width
    local banner_len=${#banner}
    if [[ "$banner_len" -lt "$_TH_TERM_COLS" ]]; then
        local pad_count=$((_TH_TERM_COLS - banner_len))
        local padding
        printf -v padding '%*s' "$pad_count" ''
        padding="${padding// /─}"
        banner="${banner}${padding}"
    fi
    echo "$banner"

    # --- Worker detail lines (2 per row) ---
    if [[ "$total_count" -gt 0 ]]; then
        local -a _th_entries=()
        pool_foreach "all" _th_collect_worker

        local entry_count=${#_th_entries[@]}
        local max_worker_lines=$((_TH_MAX_LINES - 3))  # reserve banner + status + separator
        [[ "$max_worker_lines" -ge 1 ]] || max_worker_lines=1

        local worker_lines_needed=$(( (entry_count + 1) / 2 ))
        local show_overflow=false
        local overflow_count=0

        if [[ "$worker_lines_needed" -gt "$max_worker_lines" ]]; then
            show_overflow=true
            local visible_entries=$(( (max_worker_lines - 1) * 2 ))
            overflow_count=$((entry_count - visible_entries))
            worker_lines_needed="$max_worker_lines"
        fi

        local idx=0
        local row
        for ((row = 0; row < worker_lines_needed; row++)); do
            if [[ "$show_overflow" == true && "$row" -eq $((worker_lines_needed - 1)) ]]; then
                echo "  ... and $overflow_count more"
                break
            fi

            local line="  ${_th_entries[$idx]:-}"
            ((++idx)) || true

            if [[ "$idx" -lt "$entry_count" ]]; then
                line="${line}    ${_th_entries[$idx]:-}"
                ((++idx)) || true
            fi

            echo "$line"
        done
    fi

    # --- Status summary line ---
    local status_parts="┄ ready: ${_TH_READY_COUNT}  blocked: ${_TH_BLOCKED_COUNT}"
    [[ "$_TH_DEFERRED_COUNT" -gt 0 ]] && status_parts+="  deferred: ${_TH_DEFERRED_COUNT}"
    [[ "$_TH_CYCLIC_COUNT" -gt 0 ]] && status_parts+="  cyclic: ${_TH_CYCLIC_COUNT}"
    status_parts+="  errors: ${_TH_ERROR_COUNT}"
    [[ "$_TH_STUCK_COUNT" -gt 0 ]] && status_parts+="  stuck: ${_TH_STUCK_COUNT}"
    status_parts+=" "

    local status_len=${#status_parts}
    if [[ "$status_len" -lt "$_TH_TERM_COLS" ]]; then
        local status_pad_count=$((_TH_TERM_COLS - status_len))
        local status_padding
        printf -v status_padding '%*s' "$status_pad_count" ''
        status_padding="${status_padding// /┄}"
        status_parts="${status_parts}${status_padding}"
    fi
    echo "$status_parts"

    # --- Separator line ---
    local separator
    printf -v separator '%*s' "$_TH_TERM_COLS" ''
    separator="${separator// /─}"
    echo "$separator"
}
