#!/usr/bin/env bash
# defaults.sh - Centralized configuration defaults and path setup
#
# Source this file early in any wiggum script to get consistent defaults.
# All values can be overridden by environment variables.
set -euo pipefail

# Core paths
WIGGUM_HOME="${WIGGUM_HOME:-$HOME/.claude/chief-wiggum}"
PROJECT_DIR="${PROJECT_DIR:-$(pwd)}"
RALPH_DIR="${RALPH_DIR:-$PROJECT_DIR/.ralph}"

# Validate core paths are not empty after defaulting
if [[ -z "$WIGGUM_HOME" || "$WIGGUM_HOME" == "/" ]]; then
    echo "[FATAL] WIGGUM_HOME is empty or root — aborting" >&2
    exit 1
fi
if [[ -z "$PROJECT_DIR" || "$PROJECT_DIR" == "/" ]]; then
    echo "[FATAL] PROJECT_DIR is empty or root — aborting" >&2
    exit 1
fi
if [[ -z "$RALPH_DIR" || "$RALPH_DIR" == "/" ]]; then
    echo "[FATAL] RALPH_DIR is empty or root — aborting" >&2
    exit 1
fi

# Claude binary (allows specifying a different binary or path)
CLAUDE="${CLAUDE:-claude}"

# Pass through API configuration environment variables if set
# These allow custom API endpoints, authentication, and model selection
# Use ${VAR:-} syntax to handle set -u (nounset) mode
[ -n "${ANTHROPIC_BASE_URL:-}" ] && export ANTHROPIC_BASE_URL
[ -n "${API_TIMEOUT_MS:-}" ] && export API_TIMEOUT_MS
[ -n "${ANTHROPIC_DEFAULT_OPUS_MODEL:-}" ] && export ANTHROPIC_DEFAULT_OPUS_MODEL
[ -n "${ANTHROPIC_DEFAULT_SONNET_MODEL:-}" ] && export ANTHROPIC_DEFAULT_SONNET_MODEL
[ -n "${ANTHROPIC_DEFAULT_HAIKU_MODEL:-}" ] && export ANTHROPIC_DEFAULT_HAIKU_MODEL

# Security: Store auth token in non-exported variable to limit exposure
# Use run_claude() helper to pass token only to Claude CLI
_WIGGUM_AUTH_TOKEN="${ANTHROPIC_AUTH_TOKEN:-}"

# Helper to run Claude CLI with auth token scoped only to that process
# Usage: run_claude [claude args...]
# This prevents the token from being exposed to all child processes
run_claude() {
    if [ -n "$_WIGGUM_AUTH_TOKEN" ]; then
        ANTHROPIC_AUTH_TOKEN="$_WIGGUM_AUTH_TOKEN" "$CLAUDE" "$@"
    else
        "$CLAUDE" "$@"
    fi
}

# Logging configuration
# Map WIGGUM_LOG_LEVEL to LOG_LEVEL for logger.sh
if [ -n "${WIGGUM_LOG_LEVEL:-}" ]; then
    LOG_LEVEL="${WIGGUM_LOG_LEVEL^^}"  # Convert to uppercase
    export LOG_LEVEL
fi

# Worker configuration defaults
MAX_WORKERS="${WIGGUM_MAX_WORKERS:-4}"
export MAX_WORKERS

# Resolve worker timeout (seconds) - max runtime for conflict resolver workers
RESOLVE_WORKER_TIMEOUT="${WIGGUM_RESOLVE_TIMEOUT:-1800}"
export RESOLVE_WORKER_TIMEOUT

# Maximum merge attempts before giving up
MAX_MERGE_ATTEMPTS="${WIGGUM_MAX_MERGE_ATTEMPTS:-3}"
export MAX_MERGE_ATTEMPTS

# GitHub CLI timeout (seconds)
WIGGUM_GH_TIMEOUT="${WIGGUM_GH_TIMEOUT:-30}"
export WIGGUM_GH_TIMEOUT

# Error log max age for status display (seconds) - only show errors newer than this
ERROR_LOG_MAX_AGE="${WIGGUM_ERROR_LOG_MAX_AGE:-3600}"
export ERROR_LOG_MAX_AGE

# Stuck worker detection: warn if no activity for this many seconds (0 = disabled)
STUCK_WORKER_THRESHOLD="${WIGGUM_STUCK_WORKER_THRESHOLD:-1800}"
export STUCK_WORKER_THRESHOLD

# Circuit breaker threshold: max consecutive same non-terminal results before escalation
# Used by:
#   - Pipeline runner: consecutive FIX/UNKNOWN in single run -> escalate to FAIL
#   - Scheduler: consecutive failures at same step across resumes -> terminal
# CATEGORY 8 FIX: Unified to single variable (was WIGGUM_MAX_STEP_RETRIES + WIGGUM_CIRCUIT_BREAKER_THRESHOLD)
WIGGUM_CIRCUIT_BREAKER_THRESHOLD="${WIGGUM_CIRCUIT_BREAKER_THRESHOLD:-3}"
export WIGGUM_CIRCUIT_BREAKER_THRESHOLD

# Legacy alias for backward compatibility (maps to circuit breaker threshold)
WIGGUM_MAX_STEP_RETRIES="${WIGGUM_MAX_STEP_RETRIES:-$WIGGUM_CIRCUIT_BREAKER_THRESHOLD}"
export WIGGUM_MAX_STEP_RETRIES

# Max recovery attempts for failed workers before marking permanently failed
WIGGUM_MAX_RECOVERY_ATTEMPTS="${WIGGUM_MAX_RECOVERY_ATTEMPTS:-2}"
export WIGGUM_MAX_RECOVERY_ATTEMPTS

# Max cooldown for pre-worker check failures (seconds)
WIGGUM_PRE_WORKER_MAX_COOLDOWN="${WIGGUM_PRE_WORKER_MAX_COOLDOWN:-300}"
export WIGGUM_PRE_WORKER_MAX_COOLDOWN

# Per-worker cost limit in USD (0 or empty = unlimited)
WIGGUM_WORKER_COST_LIMIT="${WIGGUM_WORKER_COST_LIMIT:-}"
export WIGGUM_WORKER_COST_LIMIT

# Orchestrator and service state directories
ORCH_STATE_DIR="$RALPH_DIR/orchestrator"
SVC_STATE_DIR="$RALPH_DIR/services"

# Export for child processes
export WIGGUM_HOME
export PROJECT_DIR
export RALPH_DIR
export ORCH_STATE_DIR
export SVC_STATE_DIR
export CLAUDE

# =============================================================================
# UNIFIED CONFIG LOADING (Performance Optimization)
# =============================================================================
# Single jq call extracts all config values at once, caching the result.
# This reduces multiple jq invocations to a single call per session.

_CONFIG_CACHE_LOADED=0

# Internal: Load all config values in a single jq call
_load_config_cache() {
    [ "$_CONFIG_CACHE_LOADED" = "1" ] && return 0

    local config_file="$WIGGUM_HOME/config/config.json"
    if [ ! -f "$config_file" ]; then
        _CONFIG_CACHE_LOADED=1
        return 0
    fi

    # Single jq call extracts all values (performance optimization)
    # Uses RS (\x1e) separator instead of @tsv to avoid empty-field collapse
    # (bash treats tab as whitespace, so consecutive tabs merge)
    local extracted
    extracted=$(jq -r '[
        (.review.approved_user_ids // [] | map(tostring) | join(",")),
        (.review.fix_max_iterations // 10),
        (.review.fix_max_turns // 30),
        (.review.auto_commit_after_fix // true),
        (.rate_limit.threshold_prompts // 900),
        (.git.author_name // "Ralph Wiggum"),
        (.git.author_email // "ralph@wiggum.cc"),
        (.workers.fix_worker_limit // 2),
        (.log_rotation.enabled // true),
        (.log_rotation.max_lines // 10000),
        (.log_rotation.max_archives // 10),
        (.resume.max_attempts // 3),
        (.resume.cooldown_seconds // 3600),
        (.resume.initial_bonus // 20000),
        (.resume.fail_penalty // 8000),
        (.resume.min_retry_interval // 30),
        (.resume.max_decide_concurrent // 20),
        (.task_source.mode // "hybrid"),
        (.git.default_branch // "")
    ] | join("\u001e")' "$config_file" 2>/dev/null) || true

    if [ -n "$extracted" ]; then
        IFS=$'\x1e' read -r _CACHE_APPROVED_USER_IDS _CACHE_FIX_MAX_ITER _CACHE_FIX_MAX_TURNS \
                         _CACHE_AUTO_COMMIT _CACHE_RATE_LIMIT _CACHE_GIT_NAME _CACHE_GIT_EMAIL \
                         _CACHE_FIX_WORKER_LIMIT _CACHE_LOG_ROTATE_ENABLED _CACHE_LOG_ROTATE_LINES \
                         _CACHE_LOG_ROTATE_MAX_ARCHIVES _CACHE_RESUME_MAX_ATTEMPTS \
                         _CACHE_RESUME_COOLDOWN _CACHE_RESUME_INITIAL_BONUS \
                         _CACHE_RESUME_FAIL_PENALTY _CACHE_RESUME_MIN_RETRY \
                         _CACHE_RESUME_MAX_DECIDE _CACHE_TASK_SOURCE_MODE \
                         _CACHE_GIT_DEFAULT_BRANCH \
                         <<< "$extracted"
    fi

    _CONFIG_CACHE_LOADED=1
}

# Load review config from config.json (with env var overrides)
load_review_config() {
    _load_config_cache

    WIGGUM_APPROVED_USER_IDS="${WIGGUM_APPROVED_USER_IDS:-${_CACHE_APPROVED_USER_IDS:-}}"
    WIGGUM_COMMENT_FIX_MAX_ITERATIONS="${WIGGUM_COMMENT_FIX_MAX_ITERATIONS:-${_CACHE_FIX_MAX_ITER:-}}"
    WIGGUM_COMMENT_FIX_MAX_TURNS="${WIGGUM_COMMENT_FIX_MAX_TURNS:-${_CACHE_FIX_MAX_TURNS:-}}"
    WIGGUM_AUTO_COMMIT_AFTER_FIX="${WIGGUM_AUTO_COMMIT_AFTER_FIX:-${_CACHE_AUTO_COMMIT:-}}"

    # Fallback defaults if config doesn't exist or parsing fails
    WIGGUM_APPROVED_USER_IDS="${WIGGUM_APPROVED_USER_IDS:-}"
    WIGGUM_COMMENT_FIX_MAX_ITERATIONS="${WIGGUM_COMMENT_FIX_MAX_ITERATIONS:-10}"
    WIGGUM_COMMENT_FIX_MAX_TURNS="${WIGGUM_COMMENT_FIX_MAX_TURNS:-30}"
    WIGGUM_AUTO_COMMIT_AFTER_FIX="${WIGGUM_AUTO_COMMIT_AFTER_FIX:-true}"

    export WIGGUM_APPROVED_USER_IDS
    export WIGGUM_COMMENT_FIX_MAX_ITERATIONS
    export WIGGUM_COMMENT_FIX_MAX_TURNS
    export WIGGUM_AUTO_COMMIT_AFTER_FIX
}

# Load rate limit config from config.json (with env var overrides)
load_rate_limit_config() {
    _load_config_cache

    WIGGUM_RATE_LIMIT_THRESHOLD="${WIGGUM_RATE_LIMIT_THRESHOLD:-${_CACHE_RATE_LIMIT:-}}"
    WIGGUM_RATE_LIMIT_THRESHOLD="${WIGGUM_RATE_LIMIT_THRESHOLD:-900}"
    export WIGGUM_RATE_LIMIT_THRESHOLD
}

# Load git identity config from config.json (with env var overrides)
# Sets WIGGUM_GIT_AUTHOR_NAME and WIGGUM_GIT_AUTHOR_EMAIL
load_git_config() {
    _load_config_cache

    WIGGUM_GIT_AUTHOR_NAME="${WIGGUM_GIT_AUTHOR_NAME:-${_CACHE_GIT_NAME:-}}"
    WIGGUM_GIT_AUTHOR_EMAIL="${WIGGUM_GIT_AUTHOR_EMAIL:-${_CACHE_GIT_EMAIL:-}}"

    # Fallback defaults if config doesn't exist or parsing fails
    WIGGUM_GIT_AUTHOR_NAME="${WIGGUM_GIT_AUTHOR_NAME:-Ralph Wiggum}"
    WIGGUM_GIT_AUTHOR_EMAIL="${WIGGUM_GIT_AUTHOR_EMAIL:-ralph@wiggum.cc}"
    export WIGGUM_GIT_AUTHOR_NAME
    export WIGGUM_GIT_AUTHOR_EMAIL
}

# Detect the default branch for the current repository
#
# Priority: WIGGUM_DEFAULT_BRANCH env → config.json → git symbolic-ref → "main"
#
# Args:
#   project_dir (optional) - directory to run git commands in (default: $PROJECT_DIR)
#
# Echoes: branch name (e.g. "main" or "master")
get_default_branch() {
    # Return cached value if already resolved
    if [ -n "${WIGGUM_DEFAULT_BRANCH:-}" ]; then
        echo "$WIGGUM_DEFAULT_BRANCH"
        return 0
    fi

    local project_dir="${1:-${PROJECT_DIR:-.}}"

    # Try config.json
    _load_config_cache
    if [ -n "${_CACHE_GIT_DEFAULT_BRANCH:-}" ]; then
        WIGGUM_DEFAULT_BRANCH="$_CACHE_GIT_DEFAULT_BRANCH"
        export WIGGUM_DEFAULT_BRANCH
        echo "$WIGGUM_DEFAULT_BRANCH"
        return 0
    fi

    # Try git symbolic-ref
    local detected
    detected=$(git -C "$project_dir" symbolic-ref refs/remotes/origin/HEAD 2>/dev/null | \
        sed 's@^refs/remotes/origin/@@') || true
    if [ -n "$detected" ]; then
        WIGGUM_DEFAULT_BRANCH="$detected"
        export WIGGUM_DEFAULT_BRANCH
        echo "$WIGGUM_DEFAULT_BRANCH"
        return 0
    fi

    # Fallback
    WIGGUM_DEFAULT_BRANCH="main"
    export WIGGUM_DEFAULT_BRANCH
    echo "$WIGGUM_DEFAULT_BRANCH"
}

# Load workers config from config.json (with env var overrides)
# Sets WIGGUM_FIX_WORKER_LIMIT
load_workers_config() {
    _load_config_cache

    WIGGUM_FIX_WORKER_LIMIT="${WIGGUM_FIX_WORKER_LIMIT:-${_CACHE_FIX_WORKER_LIMIT:-}}"
    WIGGUM_FIX_WORKER_LIMIT="${WIGGUM_FIX_WORKER_LIMIT:-2}"
    export WIGGUM_FIX_WORKER_LIMIT
}

# Load log rotation config from config.json (with env var overrides)
# Sets WIGGUM_LOG_ROTATE_ENABLED, WIGGUM_LOG_ROTATE_LINES, WIGGUM_LOG_ROTATE_MAX_ARCHIVES
load_log_rotation_config() {
    _load_config_cache

    WIGGUM_LOG_ROTATE_ENABLED="${WIGGUM_LOG_ROTATE_ENABLED:-${_CACHE_LOG_ROTATE_ENABLED:-}}"
    WIGGUM_LOG_ROTATE_LINES="${WIGGUM_LOG_ROTATE_LINES:-${_CACHE_LOG_ROTATE_LINES:-}}"
    WIGGUM_LOG_ROTATE_MAX_ARCHIVES="${WIGGUM_LOG_ROTATE_MAX_ARCHIVES:-${_CACHE_LOG_ROTATE_MAX_ARCHIVES:-}}"

    # Fallback defaults if config doesn't exist or parsing fails
    WIGGUM_LOG_ROTATE_ENABLED="${WIGGUM_LOG_ROTATE_ENABLED:-true}"
    WIGGUM_LOG_ROTATE_LINES="${WIGGUM_LOG_ROTATE_LINES:-10000}"
    WIGGUM_LOG_ROTATE_MAX_ARCHIVES="${WIGGUM_LOG_ROTATE_MAX_ARCHIVES:-10}"
    export WIGGUM_LOG_ROTATE_ENABLED
    export WIGGUM_LOG_ROTATE_LINES
    export WIGGUM_LOG_ROTATE_MAX_ARCHIVES
}

# Load resume config from config.json (with env var overrides)
# Sets MAX_RESUME_ATTEMPTS and RESUME_COOLDOWN_SECONDS
load_resume_config() {
    _load_config_cache

    MAX_RESUME_ATTEMPTS="${WIGGUM_MAX_RESUME_ATTEMPTS:-${_CACHE_RESUME_MAX_ATTEMPTS:-}}"
    RESUME_COOLDOWN_SECONDS="${WIGGUM_RESUME_COOLDOWN:-${_CACHE_RESUME_COOLDOWN:-}}"

    RESUME_MAX_DECIDE_CONCURRENT="${WIGGUM_RESUME_MAX_DECIDE_CONCURRENT:-${_CACHE_RESUME_MAX_DECIDE:-}}"

    # Fallback defaults if config doesn't exist or parsing fails
    MAX_RESUME_ATTEMPTS="${MAX_RESUME_ATTEMPTS:-3}"
    RESUME_COOLDOWN_SECONDS="${RESUME_COOLDOWN_SECONDS:-3600}"
    RESUME_MAX_DECIDE_CONCURRENT="${RESUME_MAX_DECIDE_CONCURRENT:-20}"
    export MAX_RESUME_ATTEMPTS
    export RESUME_COOLDOWN_SECONDS
    export RESUME_MAX_DECIDE_CONCURRENT
}

# Load resume queue config from config.json (with env var overrides)
# Sets RESUME_INITIAL_BONUS, RESUME_FAIL_PENALTY, RESUME_MIN_RETRY_INTERVAL
load_resume_queue_config() {
    _load_config_cache

    RESUME_INITIAL_BONUS="${WIGGUM_RESUME_INITIAL_BONUS:-${_CACHE_RESUME_INITIAL_BONUS:-}}"
    RESUME_FAIL_PENALTY="${WIGGUM_RESUME_FAIL_PENALTY:-${_CACHE_RESUME_FAIL_PENALTY:-}}"
    RESUME_MIN_RETRY_INTERVAL="${WIGGUM_RESUME_MIN_RETRY_INTERVAL:-${_CACHE_RESUME_MIN_RETRY:-}}"

    # Fallback defaults if config doesn't exist or parsing fails
    RESUME_INITIAL_BONUS="${RESUME_INITIAL_BONUS:-20000}"
    RESUME_FAIL_PENALTY="${RESUME_FAIL_PENALTY:-8000}"
    RESUME_MIN_RETRY_INTERVAL="${RESUME_MIN_RETRY_INTERVAL:-30}"
    export RESUME_INITIAL_BONUS
    export RESUME_FAIL_PENALTY
    export RESUME_MIN_RETRY_INTERVAL
}

# Load task source config from config.json (with env var overrides)
# Sets WIGGUM_TASK_SOURCE_MODE, WIGGUM_SERVER_ID
load_task_source_config() {
    _load_config_cache

    # Mode: env → config → "hybrid"
    WIGGUM_TASK_SOURCE_MODE="${WIGGUM_TASK_SOURCE_MODE:-${_CACHE_TASK_SOURCE_MODE:-}}"
    WIGGUM_TASK_SOURCE_MODE="${WIGGUM_TASK_SOURCE_MODE:-hybrid}"
    export WIGGUM_TASK_SOURCE_MODE

    # Server ID: env → identity file → (auto-generated later by task_source_init)
    if [[ "$WIGGUM_TASK_SOURCE_MODE" != "local" ]] && [[ -z "${WIGGUM_SERVER_ID:-}" ]]; then
        local identity_file="$RALPH_DIR/server/identity.json"
        if [[ -f "$identity_file" ]]; then
            WIGGUM_SERVER_ID=$(jq -r '.server_id // ""' "$identity_file" 2>/dev/null) || true
        fi
    fi
    WIGGUM_SERVER_ID="${WIGGUM_SERVER_ID:-}"
    export WIGGUM_SERVER_ID
}
