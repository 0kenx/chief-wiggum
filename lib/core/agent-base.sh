#!/usr/bin/env bash
# =============================================================================
# agent-base.sh - Base library for agent development
#
# Provides shared functions to reduce boilerplate across agents:
#   - Metadata setup (agent_init_metadata)
#   - Callback context management (agent_setup_context)
#   - Common dependency sourcing (agent_source_*)
#   - Default lifecycle hook implementations
#
# Usage:
#   source "$WIGGUM_HOME/lib/core/agent-base.sh"
#   agent_init_metadata "my-agent" "Description of what it does"
#   agent_source_core
#   agent_source_ralph
# =============================================================================

# Prevent double-sourcing
[ -n "${_AGENT_BASE_LOADED:-}" ] && return 0
_AGENT_BASE_LOADED=1

# =============================================================================
# METADATA SETUP
# =============================================================================

# Initialize agent metadata
#
# Args:
#   type        - Agent type identifier (e.g., "task-worker")
#   description - Human-readable description
#
# Sets and exports: AGENT_TYPE, AGENT_DESCRIPTION
agent_init_metadata() {
    local type="$1"
    local description="$2"

    AGENT_TYPE="$type"
    AGENT_DESCRIPTION="$description"
    export AGENT_TYPE AGENT_DESCRIPTION
}

# =============================================================================
# CALLBACK CONTEXT SETUP
# =============================================================================

# Agent context variables (set by agent_setup_context)
_AGENT_WORKER_DIR=""
_AGENT_WORKSPACE=""
_AGENT_PROJECT_DIR=""
_AGENT_TASK_ID=""

# Setup standard callback context for ralph loop
#
# Args:
#   worker_dir  - Worker directory path
#   workspace   - Workspace directory path (where code lives)
#   project_dir - Project root directory (optional)
#   task_id     - Task identifier (optional)
agent_setup_context() {
    _AGENT_WORKER_DIR="${1:-}"
    _AGENT_WORKSPACE="${2:-}"
    _AGENT_PROJECT_DIR="${3:-}"
    _AGENT_TASK_ID="${4:-}"
}

# Get context values (for use in callbacks)
agent_get_worker_dir() { echo "$_AGENT_WORKER_DIR"; }
agent_get_workspace() { echo "$_AGENT_WORKSPACE"; }
agent_get_project_dir() { echo "$_AGENT_PROJECT_DIR"; }
agent_get_task_id() { echo "$_AGENT_TASK_ID"; }

# =============================================================================
# DEPENDENCY SOURCING
# =============================================================================

# Source core dependencies (logger, defaults)
agent_source_core() {
    source "$WIGGUM_HOME/lib/core/logger.sh"
    source "$WIGGUM_HOME/lib/core/defaults.sh"
}

# Source ralph loop (main execution pattern)
agent_source_ralph() {
    source "$WIGGUM_HOME/lib/claude/run-claude-ralph-loop.sh"
}

# Source supervised ralph loop (with periodic supervisor intervention)
agent_source_ralph_supervised() {
    source "$WIGGUM_HOME/lib/claude/run-claude-ralph-loop-supervised.sh"
}

# Source one-shot agent execution (no iteration loop)
agent_source_once() {
    source "$WIGGUM_HOME/lib/claude/run-claude-once.sh"
}

# Source git operations
agent_source_git() {
    source "$WIGGUM_HOME/lib/git/worktree-helpers.sh"
    source "$WIGGUM_HOME/lib/git/git-operations.sh"
}

# Source task parsing utilities
agent_source_tasks() {
    source "$WIGGUM_HOME/lib/tasks/task-parser.sh"
}

# Source metrics and audit logging
agent_source_metrics() {
    source "$WIGGUM_HOME/lib/metrics/audit-logger.sh"
    source "$WIGGUM_HOME/lib/metrics/metrics-export.sh"
}

# Source violation monitoring
agent_source_violations() {
    source "$WIGGUM_HOME/lib/worker/violation-monitor.sh"
}

# Source agent registry (for sub-agent spawning)
agent_source_registry() {
    source "$WIGGUM_HOME/lib/worker/agent-registry.sh"
}

# Source file locking utilities
agent_source_lock() {
    source "$WIGGUM_HOME/lib/core/file-lock.sh"
}

# Source resume capabilities
agent_source_resume() {
    source "$WIGGUM_HOME/lib/claude/run-claude-resume.sh"
}

# =============================================================================
# LIFECYCLE HOOKS (Default Implementations)
# =============================================================================

# Called before PID file creation during agent initialization
# Override in agent to perform early setup
#
# Args:
#   worker_dir  - Worker directory path
#   project_dir - Project root directory
#
# Returns: 0 to continue, non-zero to abort
agent_on_init() {
    local worker_dir="$1"
    local project_dir="$2"
    # Default: no-op
    return 0
}

# Called after init, before agent_run
# Override in agent to perform pre-run setup
#
# Args:
#   worker_dir  - Worker directory path
#   project_dir - Project root directory
#
# Returns: 0 to continue, non-zero to abort
agent_on_ready() {
    local worker_dir="$1"
    local project_dir="$2"
    # Default: no-op
    return 0
}

# Called on validation/prerequisite failure
# Override in agent to handle errors
#
# Args:
#   worker_dir - Worker directory path
#   exit_code  - The exit code that will be returned
#   error_type - Type of error: "prereq", "output", "runtime"
agent_on_error() {
    local worker_dir="$1"
    local exit_code="$2"
    # shellcheck disable=SC2034  # error_type is available for subclass implementations
    local error_type="$3"
    # Default: no-op
    return 0
}

# Called on INT/TERM signal before cleanup
# Override in agent to handle graceful shutdown
#
# Args:
#   signal - Signal name: "INT" or "TERM"
agent_on_signal() {
    local signal="$1"
    # Default: no-op
    return 0
}

# =============================================================================
# AGENT CONFIGURATION
# =============================================================================

# Load agent-specific configuration from config/agents.json
#
# Args:
#   agent_type - The agent type to load config for
#
# Sets global variables based on config (with env var overrides):
#   AGENT_CONFIG_MAX_ITERATIONS
#   AGENT_CONFIG_MAX_TURNS
#   AGENT_CONFIG_TIMEOUT_SECONDS
#   AGENT_CONFIG_AUTO_COMMIT
#   AGENT_CONFIG_SUPERVISOR_INTERVAL
#   AGENT_CONFIG_MAX_RESTARTS
load_agent_config() {
    local agent_type="$1"
    local config_file="$WIGGUM_HOME/config/agents.json"

    # Initialize with defaults
    AGENT_CONFIG_MAX_ITERATIONS=10
    AGENT_CONFIG_MAX_TURNS=30
    AGENT_CONFIG_TIMEOUT_SECONDS=3600
    AGENT_CONFIG_AUTO_COMMIT=false
    AGENT_CONFIG_SUPERVISOR_INTERVAL=3
    AGENT_CONFIG_MAX_RESTARTS=2

    # Load from config file if it exists
    if [ -f "$config_file" ]; then
        # Load agent-specific config, falling back to defaults
        local agent_config default_config

        # Get defaults section
        default_config=$(jq -r '.defaults // {}' "$config_file" 2>/dev/null)
        if [ -n "$default_config" ] && [ "$default_config" != "null" ]; then
            AGENT_CONFIG_MAX_ITERATIONS=$(echo "$default_config" | jq -r '.max_iterations // 10')
            AGENT_CONFIG_MAX_TURNS=$(echo "$default_config" | jq -r '.max_turns // 30')
            AGENT_CONFIG_TIMEOUT_SECONDS=$(echo "$default_config" | jq -r '.timeout_seconds // 3600')
            AGENT_CONFIG_AUTO_COMMIT=$(echo "$default_config" | jq -r '.auto_commit // false')
            AGENT_CONFIG_SUPERVISOR_INTERVAL=$(echo "$default_config" | jq -r '.supervisor_interval // 3')
            AGENT_CONFIG_MAX_RESTARTS=$(echo "$default_config" | jq -r '.max_restarts // 2')
        fi

        # Override with agent-specific config
        agent_config=$(jq -r ".agents.\"$agent_type\" // {}" "$config_file" 2>/dev/null)
        if [ -n "$agent_config" ] && [ "$agent_config" != "null" ] && [ "$agent_config" != "{}" ]; then
            local val

            val=$(echo "$agent_config" | jq -r '.max_iterations // empty')
            [ -n "$val" ] && AGENT_CONFIG_MAX_ITERATIONS="$val"

            val=$(echo "$agent_config" | jq -r '.max_turns // empty')
            [ -n "$val" ] && AGENT_CONFIG_MAX_TURNS="$val"

            val=$(echo "$agent_config" | jq -r '.timeout_seconds // empty')
            [ -n "$val" ] && AGENT_CONFIG_TIMEOUT_SECONDS="$val"

            val=$(echo "$agent_config" | jq -r '.auto_commit // empty')
            [ -n "$val" ] && AGENT_CONFIG_AUTO_COMMIT="$val"

            val=$(echo "$agent_config" | jq -r '.supervisor_interval // empty')
            [ -n "$val" ] && AGENT_CONFIG_SUPERVISOR_INTERVAL="$val"

            val=$(echo "$agent_config" | jq -r '.max_restarts // empty')
            [ -n "$val" ] && AGENT_CONFIG_MAX_RESTARTS="$val"
        fi
    fi

    # Export for use by agent
    export AGENT_CONFIG_MAX_ITERATIONS
    export AGENT_CONFIG_MAX_TURNS
    export AGENT_CONFIG_TIMEOUT_SECONDS
    export AGENT_CONFIG_AUTO_COMMIT
    export AGENT_CONFIG_SUPERVISOR_INTERVAL
    export AGENT_CONFIG_MAX_RESTARTS
}

# =============================================================================
# UTILITY FUNCTIONS
# =============================================================================

# Create standard directory structure for an agent
#
# Args:
#   worker_dir - Worker directory path
agent_create_directories() {
    local worker_dir="$1"
    mkdir -p "$worker_dir/logs"
    mkdir -p "$worker_dir/summaries"
}

# Log agent start event
#
# Args:
#   worker_dir - Worker directory path
#   task_id    - Task identifier (optional)
agent_log_start() {
    local worker_dir="$1"
    local task_id="${2:-unknown}"
    local worker_id
    worker_id=$(basename "$worker_dir")

    echo "[$(date -Iseconds)] AGENT_STARTED agent=$AGENT_TYPE worker_id=$worker_id task_id=$task_id start_time=$(date +%s)" >> "$worker_dir/worker.log"
}

# Log agent completion event
#
# Args:
#   worker_dir - Worker directory path
#   exit_code  - Exit code from agent_run
#   start_time - Start timestamp (from date +%s)
agent_log_complete() {
    local worker_dir="$1"
    local exit_code="$2"
    local start_time="$3"

    local end_time duration
    end_time=$(date +%s)
    duration=$((end_time - start_time))

    echo "[$(date -Iseconds)] AGENT_COMPLETED agent=$AGENT_TYPE duration_sec=$duration exit_code=$exit_code" >> "$worker_dir/worker.log"
}

# =============================================================================
# STRUCTURED AGENT RESULTS
# =============================================================================
# Standard schema for agent results (agent-result.json):
# {
#   "agent_type": "task-worker",
#   "status": "success|failure|partial|unknown",
#   "exit_code": 0,
#   "started_at": "2024-01-15T10:30:00Z",
#   "completed_at": "2024-01-15T10:45:00Z",
#   "duration_seconds": 900,
#   "task_id": "TASK-001",
#   "worker_id": "worker-TASK-001-abc123",
#   "iterations_completed": 3,
#   "outputs": {
#     "pr_url": "https://github.com/...",
#     "branch": "task/TASK-001",
#     "commit_sha": "abc123...",
#     "validation_result": "PASS"
#   },
#   "errors": [],
#   "metadata": {}
# }

# Standard result file name
AGENT_RESULT_FILE="agent-result.json"

# Write agent result to JSON file
#
# Args:
#   worker_dir - Worker directory path
#   status     - Result status: success, failure, partial, unknown
#   exit_code  - Numeric exit code
#   outputs    - JSON object string of output values (optional)
#   errors     - JSON array string of error messages (optional)
#   metadata   - JSON object string of additional metadata (optional)
agent_write_result() {
    local worker_dir="$1"
    local result_status="$2"
    local exit_code="$3"
    local outputs="${4-}"
    local errors="${5-}"
    local metadata="${6-}"

    # Set defaults for optional JSON params (avoid shell expansion issues)
    [ -z "$outputs" ] && outputs='{}'
    [ -z "$errors" ] && errors='[]'
    [ -z "$metadata" ] && metadata='{}'

    local result_file="$worker_dir/$AGENT_RESULT_FILE"
    local worker_id task_id
    worker_id=$(basename "$worker_dir")
    task_id="${_AGENT_TASK_ID:-unknown}"

    # Get timing info from context or estimate
    local started_at completed_at duration_seconds
    completed_at=$(date -Iseconds)
    duration_seconds=0
    started_at="$completed_at"

    # Try to get start time from worker.log
    if [ -f "$worker_dir/worker.log" ]; then
        local start_epoch
        start_epoch=$(grep "AGENT_STARTED" "$worker_dir/worker.log" 2>/dev/null | tail -1 | grep -oP 'start_time=\K\d+' || true)
        if [ -n "$start_epoch" ] && [[ "$start_epoch" =~ ^[0-9]+$ ]]; then
            started_at=$(date -Iseconds -d "@$start_epoch" 2>/dev/null || date -Iseconds)
            duration_seconds=$(($(date +%s) - start_epoch))
        fi
    fi

    # Get iterations from logs directory
    local iterations_completed=0
    if [ -d "$worker_dir/logs" ]; then
        local count
        count=$(find "$worker_dir/logs" -maxdepth 1 \( -name "iteration-*.log" -o -name "validation-*.log" -o -name "fix-*.log" \) 2>/dev/null | wc -l || true)
        iterations_completed=$(echo "$count" | tr -d '[:space:]')
    fi
    # Ensure numeric values
    [[ "$iterations_completed" =~ ^[0-9]+$ ]] || iterations_completed=0
    [[ "$duration_seconds" =~ ^[0-9]+$ ]] || duration_seconds=0
    [[ "$exit_code" =~ ^[0-9]+$ ]] || exit_code=1

    # Build JSON result using a heredoc to avoid quoting issues
    cat > "$result_file" << JSONEOF
{
  "agent_type": "${AGENT_TYPE:-unknown}",
  "status": "$result_status",
  "exit_code": $exit_code,
  "started_at": "$started_at",
  "completed_at": "$completed_at",
  "duration_seconds": $duration_seconds,
  "task_id": "$task_id",
  "worker_id": "$worker_id",
  "iterations_completed": $iterations_completed,
  "outputs": $outputs,
  "errors": $errors,
  "metadata": $metadata
}
JSONEOF
}

# Read agent result from JSON file
#
# Args:
#   worker_dir - Worker directory path
#   field      - Optional: specific field to extract (uses jq path syntax)
#
# Returns: Full JSON or specific field value
agent_read_result() {
    local worker_dir="$1"
    local field="${2:-}"
    local result_file="$worker_dir/$AGENT_RESULT_FILE"

    if [ ! -f "$result_file" ]; then
        echo ""
        return 1
    fi

    if [ -n "$field" ]; then
        jq -r "$field // empty" "$result_file" 2>/dev/null
    else
        cat "$result_file"
    fi
}

# Check if agent result indicates success
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: 0 if success, 1 otherwise
agent_result_is_success() {
    local worker_dir="$1"
    local status
    status=$(agent_read_result "$worker_dir" ".status")
    [ "$status" = "success" ]
}

# Get specific output value from agent result
#
# Args:
#   worker_dir - Worker directory path
#   key        - Output key to retrieve
#
# Returns: Output value or empty string
agent_get_output() {
    local worker_dir="$1"
    local key="$2"
    agent_read_result "$worker_dir" ".outputs.$key"
}

# Set a single output value in existing result
#
# Args:
#   worker_dir - Worker directory path
#   key        - Output key
#   value      - Output value
agent_set_output() {
    local worker_dir="$1"
    local key="$2"
    local value="$3"
    local result_file="$worker_dir/$AGENT_RESULT_FILE"

    if [ -f "$result_file" ]; then
        local tmp_file
        tmp_file=$(mktemp)
        jq --arg key "$key" --arg value "$value" '.outputs[$key] = $value' "$result_file" > "$tmp_file"
        mv "$tmp_file" "$result_file"
    fi
}

# Add error to agent result
#
# Args:
#   worker_dir - Worker directory path
#   error_msg  - Error message to add
agent_add_error() {
    local worker_dir="$1"
    local error_msg="$2"
    local result_file="$worker_dir/$AGENT_RESULT_FILE"

    if [ -f "$result_file" ]; then
        local tmp_file
        tmp_file=$(mktemp)
        jq --arg err "$error_msg" '.errors += [$err]' "$result_file" > "$tmp_file"
        mv "$tmp_file" "$result_file"
    fi
}

# =============================================================================
# AGENT COMMUNICATION PROTOCOL
# =============================================================================
# Standard file paths for inter-agent communication.
# These replace hardcoded paths with consistent conventions.

# Get the standard path for a communication file
#
# Args:
#   worker_dir - Worker directory path
#   file_type  - Type of file: result, validation, status, comments, summary
#
# Returns: Full path to the file
agent_comm_path() {
    local worker_dir="$1"
    local file_type="$2"

    case "$file_type" in
        result)
            echo "$worker_dir/agent-result.json"
            ;;
        validation)
            echo "$worker_dir/validation-result.txt"
            ;;
        validation-review)
            echo "$worker_dir/validation-review.md"
            ;;
        status)
            echo "$worker_dir/comment-status.md"
            ;;
        comments)
            echo "$worker_dir/task-comments.md"
            ;;
        summary)
            echo "$worker_dir/summaries/summary.txt"
            ;;
        prd)
            echo "$worker_dir/prd.md"
            ;;
        workspace)
            echo "$worker_dir/workspace"
            ;;
        *)
            echo "$worker_dir/$file_type"
            ;;
    esac
}

# Check if a communication file exists and is non-empty
#
# Args:
#   worker_dir - Worker directory path
#   file_type  - Type of file
#
# Returns: 0 if exists and non-empty, 1 otherwise
agent_comm_exists() {
    local worker_dir="$1"
    local file_type="$2"
    local path
    path=$(agent_comm_path "$worker_dir" "$file_type")

    [ -e "$path" ] && [ -s "$path" ]
}

# Read validation result using standard protocol
#
# Args:
#   worker_dir - Worker directory path
#
# Returns: PASS, FAIL, or UNKNOWN
agent_read_validation() {
    local worker_dir="$1"
    local validation_file
    validation_file=$(agent_comm_path "$worker_dir" "validation")

    if [ -f "$validation_file" ]; then
        cat "$validation_file"
    else
        echo "UNKNOWN"
    fi
}

# Write validation result using standard protocol
#
# Args:
#   worker_dir - Worker directory path
#   result     - PASS, FAIL, or UNKNOWN
agent_write_validation() {
    local worker_dir="$1"
    local result="$2"
    local validation_file
    validation_file=$(agent_comm_path "$worker_dir" "validation")

    echo "$result" > "$validation_file"
}

# =============================================================================
# STREAM-JSON EXTRACTION UTILITIES
# =============================================================================
# These functions properly parse Claude CLI stream-JSON output format.
# Stream-JSON contains one JSON object per line, with assistant messages having
# the format: {"type":"assistant","message":{"content":[{"type":"text","text":"..."}]}}

# Extract all text content from assistant messages in a stream-JSON log file
#
# Args:
#   log_file - Path to the stream-JSON log file
#
# Returns: All text content from assistant messages, one per line
_extract_text_from_stream_json() {
    local log_file="$1"

    if [ ! -f "$log_file" ]; then
        return 1
    fi

    grep '"type":"assistant"' "$log_file" 2>/dev/null | \
        jq -r 'select(.message.content[]? | .type == "text") | .message.content[] | select(.type == "text") | .text' 2>/dev/null
}

# Extract the LAST occurrence of a result value from stream-JSON
# This fixes the bug where the first occurrence (from examples in prompts) was returned
#
# Args:
#   log_file     - Path to the stream-JSON log file
#   valid_values - Pipe-separated list of valid values (e.g., "PASS|FAIL")
#
# Returns: The LAST result value found, or empty string if none
_extract_result_value_from_stream_json() {
    local log_file="$1"
    local valid_values="$2"

    if [ ! -f "$log_file" ]; then
        return 1
    fi

    # Extract text, find all <result>VALUE</result> matches, take LAST one
    _extract_text_from_stream_json "$log_file" | \
        grep -oP "(?<=<result>)(${valid_values})(?=</result>)" 2>/dev/null | \
        tail -1
}

# Extract content between the LAST occurrence of XML-style tags from stream-JSON
# This fixes the bug where sed was trying to match tags in raw JSON instead of extracted text
#
# Args:
#   log_file - Path to the stream-JSON log file
#   tag      - Tag name without brackets (e.g., "review", "report")
#
# Returns: Content between the last occurrence of <tag> and </tag>
_extract_tag_content_from_stream_json() {
    local log_file="$1"
    local tag="$2"

    if [ ! -f "$log_file" ]; then
        return 1
    fi

    # Extract text content first, then find the last occurrence of the tag
    # Use tac to reverse lines, find first match (which is last in original), reverse back
    local extracted_text
    extracted_text=$(_extract_text_from_stream_json "$log_file")

    if [ -z "$extracted_text" ]; then
        return 1
    fi

    # Use awk to extract the last occurrence of tag content
    echo "$extracted_text" | awk -v tag="$tag" '
        BEGIN { content = ""; in_tag = 0 }
        $0 ~ "<" tag ">" { in_tag = 1; content = ""; next }
        $0 ~ "</" tag ">" { in_tag = 0 }
        in_tag { content = content (content ? "\n" : "") $0 }
        END { print content }
    '
}

# =============================================================================
# UNIFIED RESULT EXTRACTION AND WRITING
# =============================================================================

# Extract results from log files and write to standard output files
# This is the unified function that replaces per-agent extraction logic
#
# Args:
#   worker_dir    - Worker directory path
#   agent_name    - Agent name for logging (e.g., "VALIDATION", "SECURITY")
#   log_prefix    - Log file prefix (e.g., "validation", "audit", "test")
#   report_tag    - XML tag name for report content (e.g., "review", "report")
#   valid_values  - Pipe-separated valid result values (e.g., "PASS|FAIL")
#   result_file   - Output filename for result (e.g., "validation-result.txt")
#   report_file   - Output filename for report (e.g., "validation-review.md")
#
# Returns: Sets global variable ${agent_name}_RESULT (e.g., VALIDATION_RESULT)
agent_extract_and_write_result() {
    local worker_dir="$1"
    local agent_name="$2"
    local log_prefix="$3"
    local report_tag="$4"
    local valid_values="$5"
    local result_file="$6"
    local report_file="$7"

    local result="UNKNOWN"

    # Find the latest log file (excluding summary logs)
    # Pattern matches both old format (prefix-N.log) and new format (prefix-N-timestamp.log)
    local log_file
    log_file=$(find "$worker_dir/logs" -maxdepth 1 -name "${log_prefix}-*.log" ! -name "*summary*" -printf '%T@ %p\n' 2>/dev/null | sort -rn | head -1 | cut -d' ' -f2-)

    if [ -n "$log_file" ] && [ -f "$log_file" ]; then
        # Extract report content and save to .md file
        local report_path="$worker_dir/$report_file"
        local report_content
        report_content=$(_extract_tag_content_from_stream_json "$log_file" "$report_tag")

        if [ -n "$report_content" ]; then
            echo "$report_content" > "$report_path"
            log "${agent_name} report saved to $report_file"
        fi

        # Extract result value (LAST occurrence to avoid matching examples in prompts)
        result=$(_extract_result_value_from_stream_json "$log_file" "$valid_values")
        if [ -z "$result" ]; then
            result="UNKNOWN"
        fi
    fi

    # Write legacy result file for backward compatibility
    echo "$result" > "$worker_dir/$result_file"

    # Update agent-result.json outputs if it exists
    if [ -f "$worker_dir/$AGENT_RESULT_FILE" ]; then
        agent_set_output "$worker_dir" "${agent_name}_result" "$result"
    fi

    # Set global variable for the calling agent
    eval "${agent_name}_RESULT=\"$result\""

    log "${agent_name} result: $result"
}

# Read a sub-agent result, preferring agent-result.json outputs, falling back to legacy files
#
# Args:
#   worker_dir     - Worker directory path
#   output_key     - Key in agent-result.json outputs (e.g., "SECURITY_result")
#   legacy_file    - Legacy result filename (e.g., "security-result.txt")
#
# Returns: Result value or "UNKNOWN"
agent_read_subagent_result() {
    local worker_dir="$1"
    local output_key="$2"
    local legacy_file="$3"

    local result=""

    # Try agent-result.json first
    if [ -f "$worker_dir/$AGENT_RESULT_FILE" ]; then
        result=$(agent_get_output "$worker_dir" "$output_key")
    fi

    # Fall back to legacy file
    if [ -z "$result" ] && [ -f "$worker_dir/$legacy_file" ]; then
        result=$(cat "$worker_dir/$legacy_file" 2>/dev/null)
    fi

    # Default to UNKNOWN
    if [ -z "$result" ]; then
        result="UNKNOWN"
    fi

    echo "$result"
}
