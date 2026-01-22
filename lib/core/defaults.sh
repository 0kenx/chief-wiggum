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

# Claude binary (allows specifying a different binary or path)
CLAUDE="${CLAUDE:-claude}"

# Pass through API configuration environment variables if set
# These allow custom API endpoints, authentication, and model selection
# Use ${VAR:-} syntax to handle set -u (nounset) mode
[ -n "${ANTHROPIC_BASE_URL:-}" ] && export ANTHROPIC_BASE_URL
[ -n "${ANTHROPIC_AUTH_TOKEN:-}" ] && export ANTHROPIC_AUTH_TOKEN
[ -n "${API_TIMEOUT_MS:-}" ] && export API_TIMEOUT_MS
[ -n "${ANTHROPIC_DEFAULT_OPUS_MODEL:-}" ] && export ANTHROPIC_DEFAULT_OPUS_MODEL
[ -n "${ANTHROPIC_DEFAULT_SONNET_MODEL:-}" ] && export ANTHROPIC_DEFAULT_SONNET_MODEL
[ -n "${ANTHROPIC_DEFAULT_HAIKU_MODEL:-}" ] && export ANTHROPIC_DEFAULT_HAIKU_MODEL

# Worker configuration defaults
MAX_WORKERS="${WIGGUM_MAX_WORKERS:-4}"
export MAX_WORKERS
MAX_ITERATIONS="${WIGGUM_MAX_ITERATIONS:-20}"
MAX_TURNS="${WIGGUM_MAX_TURNS:-50}"

# GitHub CLI timeout (seconds)
WIGGUM_GH_TIMEOUT="${WIGGUM_GH_TIMEOUT:-30}"
export WIGGUM_GH_TIMEOUT

# Export for child processes
export WIGGUM_HOME
export PROJECT_DIR
export RALPH_DIR
export CLAUDE
export WIGGUM_MAX_ITERATIONS="$MAX_ITERATIONS"
export WIGGUM_MAX_TURNS="$MAX_TURNS"

# Load review config from config.json (with env var overrides)
load_review_config() {
    local config_file="$WIGGUM_HOME/config/config.json"
    if [ -f "$config_file" ]; then
        WIGGUM_APPROVED_AUTHORS="${WIGGUM_APPROVED_AUTHORS:-$(jq -r '.review.approved_authors // [] | join(",")' "$config_file" 2>/dev/null)}"
        WIGGUM_COMMENT_FIX_MAX_ITERATIONS="${WIGGUM_COMMENT_FIX_MAX_ITERATIONS:-$(jq -r '.review.fix_max_iterations // 10' "$config_file" 2>/dev/null)}"
        WIGGUM_COMMENT_FIX_MAX_TURNS="${WIGGUM_COMMENT_FIX_MAX_TURNS:-$(jq -r '.review.fix_max_turns // 30' "$config_file" 2>/dev/null)}"
        WIGGUM_AUTO_COMMIT_AFTER_FIX="${WIGGUM_AUTO_COMMIT_AFTER_FIX:-$(jq -r '.review.auto_commit_after_fix // true' "$config_file" 2>/dev/null)}"
    fi
    # Fallback defaults if config doesn't exist or parsing fails
    WIGGUM_APPROVED_AUTHORS="${WIGGUM_APPROVED_AUTHORS:-copilot,dependabot,github-actions[bot],dependabot[bot],renovate[bot],codecov[bot]}"
    WIGGUM_COMMENT_FIX_MAX_ITERATIONS="${WIGGUM_COMMENT_FIX_MAX_ITERATIONS:-10}"
    WIGGUM_COMMENT_FIX_MAX_TURNS="${WIGGUM_COMMENT_FIX_MAX_TURNS:-30}"
    WIGGUM_AUTO_COMMIT_AFTER_FIX="${WIGGUM_AUTO_COMMIT_AFTER_FIX:-true}"

    export WIGGUM_APPROVED_AUTHORS
    export WIGGUM_COMMENT_FIX_MAX_ITERATIONS
    export WIGGUM_COMMENT_FIX_MAX_TURNS
    export WIGGUM_AUTO_COMMIT_AFTER_FIX
}
