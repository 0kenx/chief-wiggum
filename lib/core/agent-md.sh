#!/usr/bin/env bash
# =============================================================================
# agent-md.sh - Markdown agent definition parser and interpreter
#
# Parses declarative markdown agent definitions with YAML frontmatter and
# templated prompt sections. Converts them to executable agents using the
# existing execution patterns (ralph_loop, once, resume).
#
# Usage:
#   source "$WIGGUM_HOME/lib/core/agent-md.sh"
#   md_agent_run "/path/to/agent.md" "$worker_dir" "$project_dir"
#
# See docs/AGENT_DEV_GUIDE.md for the full specification.
# =============================================================================
set -euo pipefail

# Prevent double-sourcing
[ -n "${_AGENT_MD_LOADED:-}" ] && return 0
_AGENT_MD_LOADED=1

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/agent-base.sh"

# =============================================================================
# GLOBAL STATE (set during parsing)
# =============================================================================

# Frontmatter fields
declare -g _MD_TYPE=""
declare -g _MD_DESCRIPTION=""
declare -g _MD_MODE=""
declare -g _MD_READONLY=""
declare -g _MD_REPORT_TAG=""
declare -g _MD_RESULT_TAG=""
declare -g _MD_OUTPUT_PATH=""
declare -g _MD_WORKSPACE_OVERRIDE=""
declare -g _MD_COMPLETION_CHECK=""
declare -g _MD_SESSION_FROM=""
declare -gA _MD_REQUIRED_PATHS=()
declare -gA _MD_VALID_RESULTS=()
declare -gA _MD_OUTPUTS=()

# Prompt sections (raw templates)
declare -g _MD_SYSTEM_PROMPT=""
declare -g _MD_USER_PROMPT=""
declare -g _MD_CONTINUATION_PROMPT=""

# Runtime context (set by md_agent_run)
declare -g _MD_WORKER_DIR=""
declare -g _MD_PROJECT_DIR=""
declare -g _MD_WORKSPACE=""
declare -g _MD_TASK_ID=""

# =============================================================================
# YAML FRONTMATTER PARSING
# =============================================================================

# Parse YAML frontmatter from markdown file
#
# Extracts the YAML block between --- delimiters and parses key fields.
# Uses jq/yq if available, falls back to pure bash parsing.
#
# Args:
#   md_file - Path to the markdown agent definition
#
# Sets: _MD_* global variables
_md_parse_frontmatter() {
    local md_file="$1"

    # Extract frontmatter (content between first two --- lines)
    local frontmatter=""
    local in_frontmatter=false
    local line_num=0

    while IFS= read -r line || [[ -n "$line" ]]; do
        ((++line_num))
        if [[ "$line" == "---" ]]; then
            if [ "$in_frontmatter" = false ]; then
                in_frontmatter=true
                continue
            else
                break
            fi
        fi
        if [ "$in_frontmatter" = true ]; then
            frontmatter+="$line"$'\n'
        fi
    done < "$md_file"

    if [ -z "$frontmatter" ]; then
        log_error "No YAML frontmatter found in $md_file"
        return 1
    fi

    _md_parse_frontmatter_impl "$frontmatter"
}

# Extract a simple YAML value (key: value format)
# Handles quoted and unquoted values, returns empty string if not found
#
# Args:
#   frontmatter - The frontmatter content
#   key         - The key to extract
#   default     - Default value if key not found (optional)
#
# Returns: The value (echoed)
_yaml_get_value() {
    local frontmatter="$1"
    local key="$2"
    local default="${3:-}"

    local value
    # Match "key:" at start of line, capture everything after colon
    value=$(echo "$frontmatter" | grep -E "^${key}:" | head -1 | sed "s/^${key}:[[:space:]]*//" || true)

    # Remove surrounding quotes if present
    value="${value#\"}"
    value="${value%\"}"
    value="${value#\'}"
    value="${value%\'}"

    # Trim whitespace
    value="${value#"${value%%[![:space:]]*}"}"
    value="${value%"${value##*[![:space:]]}"}"

    if [ -z "$value" ]; then
        echo "$default"
    else
        echo "$value"
    fi
}

# Extract a YAML array value (key: [a, b, c] format)
# Populates the provided array variable name
#
# Args:
#   frontmatter - The frontmatter content
#   key         - The key to extract
#   array_name  - Name of the array variable to populate
_yaml_get_array() {
    local frontmatter="$1"
    local key="$2"
    local array_name="$3"

    # Clear the array
    eval "$array_name=()"

    local line
    line=$(echo "$frontmatter" | grep -E "^${key}:" | head -1 | sed "s/^${key}:[[:space:]]*//" || true)

    # Check if it's bracket notation: [a, b, c]
    if [[ "$line" =~ ^\[.*\]$ ]]; then
        # Remove brackets
        line="${line:1:-1}"

        # Split by comma, handling spaces
        local i=0
        local item
        while IFS= read -r -d ',' item || [ -n "$item" ]; do
            # Trim whitespace and quotes
            item="${item#"${item%%[![:space:]]*}"}"
            item="${item%"${item##*[![:space:]]}"}"
            item="${item#\"}"
            item="${item%\"}"
            item="${item#\'}"
            item="${item%\'}"

            if [ -n "$item" ]; then
                eval "${array_name}[$i]=\"\$item\""
                ((++i)) || true
            fi
        done <<< "$line,"
    fi
}

# Parse frontmatter using pure bash (no external dependencies like yq)
_md_parse_frontmatter_impl() {
    local frontmatter="$1"

    # Extract scalar values with defaults
    _MD_TYPE=$(_yaml_get_value "$frontmatter" "type" "")
    _MD_DESCRIPTION=$(_yaml_get_value "$frontmatter" "description" "")
    _MD_MODE=$(_yaml_get_value "$frontmatter" "mode" "ralph_loop")
    _MD_READONLY=$(_yaml_get_value "$frontmatter" "readonly" "false")
    _MD_REPORT_TAG=$(_yaml_get_value "$frontmatter" "report_tag" "report")
    _MD_RESULT_TAG=$(_yaml_get_value "$frontmatter" "result_tag" "result")
    _MD_OUTPUT_PATH=$(_yaml_get_value "$frontmatter" "output_path" "")
    _MD_WORKSPACE_OVERRIDE=$(_yaml_get_value "$frontmatter" "workspace_override" "")
    _MD_COMPLETION_CHECK=$(_yaml_get_value "$frontmatter" "completion_check" "result_tag")
    _MD_SESSION_FROM=$(_yaml_get_value "$frontmatter" "session_from" "")

    # Extract array values
    _yaml_get_array "$frontmatter" "required_paths" "_MD_REQUIRED_PATHS"
    _yaml_get_array "$frontmatter" "valid_results" "_MD_VALID_RESULTS"
    _yaml_get_array "$frontmatter" "outputs" "_MD_OUTPUTS"
}

# =============================================================================
# XML SECTION EXTRACTION
# =============================================================================

# Extract content between XML-style tags
#
# Args:
#   content - Full file content
#   tag     - Tag name (without brackets)
#
# Returns: Content between <TAG> and </TAG>, with tags removed
_md_extract_section() {
    local content="$1"
    local tag="$2"

    # Use awk for robust multiline extraction
    echo "$content" | awk -v tag="$tag" '
        BEGIN { in_tag = 0; content = "" }
        $0 ~ "<" tag ">" { in_tag = 1; next }
        $0 ~ "</" tag ">" { in_tag = 0 }
        in_tag { print }
    '
}

# Parse all prompt sections from markdown file
#
# Args:
#   md_file - Path to the markdown file
#
# Sets: _MD_SYSTEM_PROMPT, _MD_USER_PROMPT, _MD_CONTINUATION_PROMPT
_md_parse_sections() {
    local md_file="$1"
    local content
    content=$(cat "$md_file")

    _MD_SYSTEM_PROMPT=$(_md_extract_section "$content" "WIGGUM_SYSTEM_PROMPT")
    _MD_USER_PROMPT=$(_md_extract_section "$content" "WIGGUM_USER_PROMPT")
    _MD_CONTINUATION_PROMPT=$(_md_extract_section "$content" "WIGGUM_CONTINUATION_PROMPT")
}

# =============================================================================
# VARIABLE INTERPOLATION
# =============================================================================

# Interpolate variables in a template string
#
# Replaces {{variable}} patterns with actual values from the runtime context.
#
# Args:
#   template - Template string with {{variable}} placeholders
#
# Returns: Interpolated string
_md_interpolate() {
    local template="$1"
    local result="$template"

    # Path variables
    result="${result//\{\{workspace\}\}/$_MD_WORKSPACE}"
    result="${result//\{\{worker_dir\}\}/$_MD_WORKER_DIR}"
    result="${result//\{\{project_dir\}\}/$_MD_PROJECT_DIR}"

    # Task/step context
    result="${result//\{\{task_id\}\}/$_MD_TASK_ID}"
    result="${result//\{\{step_id\}\}/${WIGGUM_STEP_ID:-}}"
    result="${result//\{\{run_id\}\}/${RALPH_RUN_ID:-}}"

    # Parent step context (from pipeline)
    result="${result//\{\{parent.step_id\}\}/${WIGGUM_PARENT_STEP_ID:-}}"
    result="${result//\{\{parent.run_id\}\}/${WIGGUM_PARENT_RUN_ID:-}}"
    result="${result//\{\{parent.session_id\}\}/${WIGGUM_PARENT_SESSION_ID:-}}"
    result="${result//\{\{parent.result\}\}/${WIGGUM_PARENT_RESULT:-}}"
    result="${result//\{\{parent.report\}\}/${WIGGUM_PARENT_REPORT:-}}"
    result="${result//\{\{parent.output_dir\}\}/${WIGGUM_PARENT_OUTPUT_DIR:-}}"

    # Next step context
    result="${result//\{\{next.step_id\}\}/${WIGGUM_NEXT_STEP_ID:-}}"

    # Generated content
    if [[ "$result" == *"{{context_section}}"* ]]; then
        local context_section
        context_section=$(_md_generate_context_section)
        result="${result//\{\{context_section\}\}/$context_section}"
    fi

    if [[ "$result" == *"{{git_restrictions}}"* ]]; then
        local git_restrictions
        git_restrictions=$(_md_generate_git_restrictions)
        result="${result//\{\{git_restrictions\}\}/$git_restrictions}"
    fi

    echo "$result"
}

# Interpolate with iteration context (for ralph_loop callbacks)
#
# Args:
#   template  - Template string
#   iteration - Current iteration number
#   output_dir - Output directory for this run
#
# Returns: Interpolated string
_md_interpolate_iteration() {
    local template="$1"
    local iteration="$2"
    local output_dir="$3"

    # First do standard interpolation
    local result
    result=$(_md_interpolate "$template")

    # Then add iteration-specific variables
    result="${result//\{\{iteration\}\}/$iteration}"
    result="${result//\{\{prev_iteration\}\}/$((iteration - 1))}"
    result="${result//\{\{output_dir\}\}/$output_dir}"

    echo "$result"
}

# =============================================================================
# GENERATED CONTENT
# =============================================================================

# Generate context section based on available files
#
# Returns: Markdown section with available context files
_md_generate_context_section() {
    local section=""
    section+="## Context"$'\n'$'\n'
    section+="Before starting, understand what was implemented:"$'\n'$'\n'

    local item_num=1

    # Check for PRD
    if [ -f "$_MD_WORKER_DIR/prd.md" ]; then
        section+="${item_num}. **Read the PRD** (@../prd.md) - Understand what was supposed to be built"$'\n'
        ((++item_num))
    fi

    # Check for implementation summary
    if [ -f "$_MD_WORKER_DIR/summaries/summary.txt" ]; then
        section+="${item_num}. **Read the Implementation Summary** (@../summaries/summary.txt) - Understand what was actually built"$'\n'
        ((++item_num))
    fi

    # Check for parent report
    if [ -n "${WIGGUM_PARENT_REPORT:-}" ] && [ -f "$_MD_WORKER_DIR/$WIGGUM_PARENT_REPORT" ]; then
        section+="${item_num}. **Read the Previous Report** (@../$WIGGUM_PARENT_REPORT) - Understand findings from previous step"$'\n'
        ((++item_num))
    fi

    section+=$'\n'
    echo "$section"
}

# Generate git restrictions block for readonly agents
#
# Returns: Markdown block with git command restrictions
_md_generate_git_restrictions() {
    if [ "$_MD_READONLY" != "true" ]; then
        echo ""
        return
    fi

    cat << 'EOF'
## Git Restrictions (CRITICAL)

You are a READ-ONLY agent. The workspace contains uncommitted work that MUST NOT be destroyed.

**FORBIDDEN git commands (will terminate your session):**
- `git checkout` (any form)
- `git stash`
- `git reset`
- `git clean`
- `git restore`
- `git commit`
- `git add`

**ALLOWED git commands (read-only only):**
- `git status` - Check workspace state
- `git diff` - View changes
- `git log` - View history
- `git show` - View commits

You operate by READING files. Do NOT modify the workspace in any way.
EOF
}

# =============================================================================
# COMPLETION CHECK IMPLEMENTATIONS
# =============================================================================

# Completion check: result_tag (default)
# Returns 0 if a valid result tag is found in the latest log
_md_completion_check_result_tag() {
    local worker_dir="$_MD_WORKER_DIR"
    local step_id="${WIGGUM_STEP_ID:-agent}"

    # Build valid values regex
    local valid_regex=""
    local first=true
    for result in "${_MD_VALID_RESULTS[@]}"; do
        if [ "$first" = true ]; then
            valid_regex="$result"
            first=false
        else
            valid_regex="$valid_regex|$result"
        fi
    done

    # Find latest log
    local latest_log
    latest_log=$(find "$worker_dir/logs" -name "${step_id}-*.log" ! -name "*summary*" -printf '%T@ %p\n' 2>/dev/null | sort -rn | head -1 | cut -d' ' -f2-)

    if [ -n "$latest_log" ] && [ -f "$latest_log" ]; then
        local result_tag="${_MD_RESULT_TAG:-result}"
        if grep -qP "<${result_tag}>(${valid_regex})</${result_tag}>" "$latest_log" 2>/dev/null; then
            return 0  # Complete
        fi
    fi

    return 1  # Not complete
}

# Completion check: status_file
# Returns 0 if no pending items (- [ ]) remain in the status file
_md_completion_check_status_file() {
    local status_file="$1"

    # Interpolate path
    status_file=$(_md_interpolate "$status_file")

    if [ ! -f "$status_file" ]; then
        return 1  # File doesn't exist, not complete
    fi

    # Check for pending items
    if grep -q '\- \[ \]' "$status_file" 2>/dev/null; then
        return 1  # Has pending items
    fi

    return 0  # Complete
}

# Completion check: file_exists
# Returns 0 if the specified file exists and is non-empty
_md_completion_check_file_exists() {
    local file_path="$1"

    # Interpolate path
    file_path=$(_md_interpolate "$file_path")

    [ -f "$file_path" ] && [ -s "$file_path" ]
}

# Dispatch to appropriate completion check
_md_completion_check() {
    local check_type="${_MD_COMPLETION_CHECK:-result_tag}"

    case "$check_type" in
        result_tag)
            _md_completion_check_result_tag
            ;;
        status_file:*)
            local file_path="${check_type#status_file:}"
            _md_completion_check_status_file "$file_path"
            ;;
        file_exists:*)
            local file_path="${check_type#file_exists:}"
            _md_completion_check_file_exists "$file_path"
            ;;
        *)
            # Unknown check type - default to result_tag
            _md_completion_check_result_tag
            ;;
    esac
}

# =============================================================================
# RALPH LOOP CALLBACKS
# =============================================================================

# User prompt callback for ralph loop
# Implements the unified 4-arg signature
_md_user_prompt_callback() {
    local iteration="$1"
    local output_dir="$2"
    # shellcheck disable=SC2034  # supervisor args available for future use
    local supervisor_dir="${3:-}"
    # shellcheck disable=SC2034
    local supervisor_feedback="${4:-}"

    # Always output the user prompt (with interpolation)
    _md_interpolate_iteration "$_MD_USER_PROMPT" "$iteration" "$output_dir"

    # Append continuation prompt on iteration > 0
    if [ "$iteration" -gt 0 ] && [ -n "$_MD_CONTINUATION_PROMPT" ]; then
        echo ""
        _md_interpolate_iteration "$_MD_CONTINUATION_PROMPT" "$iteration" "$output_dir"
    fi
}

# =============================================================================
# RESULT EXTRACTION
# =============================================================================

# Extract result and write to epoch-named files
_md_extract_and_write_result() {
    local worker_dir="$1"
    local step_id="${WIGGUM_STEP_ID:-agent}"

    # Build valid values regex for extraction
    local valid_regex=""
    local first=true
    for result in "${_MD_VALID_RESULTS[@]}"; do
        if [ "$first" = true ]; then
            valid_regex="$result"
            first=false
        else
            valid_regex="$valid_regex|$result"
        fi
    done

    # Use the unified extraction function
    local agent_name
    agent_name=$(echo "$_MD_TYPE" | tr '[:lower:]' '[:upper:]' | tr '.' '_')

    agent_extract_and_write_result "$worker_dir" "$agent_name" "$step_id" "${_MD_REPORT_TAG:-report}" "$valid_regex"
}

# =============================================================================
# MAIN ENTRY POINTS
# =============================================================================

# Load and parse a markdown agent definition
#
# Args:
#   md_file - Path to the markdown agent definition
#
# Returns: 0 on success, 1 on parse error
md_agent_load() {
    local md_file="$1"

    if [ ! -f "$md_file" ]; then
        log_error "Markdown agent file not found: $md_file"
        return 1
    fi

    log_debug "Loading markdown agent: $md_file"

    # Parse frontmatter
    if ! _md_parse_frontmatter "$md_file"; then
        log_error "Failed to parse frontmatter in $md_file"
        return 1
    fi

    # Validate required fields
    if [ -z "$_MD_TYPE" ]; then
        log_error "Missing required field 'type' in $md_file"
        return 1
    fi

    if [ -z "$_MD_MODE" ]; then
        log_error "Missing required field 'mode' in $md_file"
        return 1
    fi

    if [ ${#_MD_REQUIRED_PATHS[@]} -eq 0 ]; then
        log_error "Missing required field 'required_paths' in $md_file"
        return 1
    fi

    if [ ${#_MD_VALID_RESULTS[@]} -eq 0 ]; then
        log_error "Missing required field 'valid_results' in $md_file"
        return 1
    fi

    # Parse prompt sections
    _md_parse_sections "$md_file"

    if [ -z "$_MD_USER_PROMPT" ]; then
        log_error "Missing <WIGGUM_USER_PROMPT> section in $md_file"
        return 1
    fi

    # System prompt is required for ralph_loop and once modes
    if [ "$_MD_MODE" != "resume" ] && [ -z "$_MD_SYSTEM_PROMPT" ]; then
        log_error "Missing <WIGGUM_SYSTEM_PROMPT> section in $md_file (required for mode=$_MD_MODE)"
        return 1
    fi

    log_debug "Loaded markdown agent: type=$_MD_TYPE mode=$_MD_MODE"
    return 0
}

# Execute a markdown agent
#
# Args:
#   md_file     - Path to the markdown agent definition
#   worker_dir  - Worker directory
#   project_dir - Project root directory
#
# Returns: Exit code from agent execution
md_agent_run() {
    local md_file="$1"
    local worker_dir="$2"
    local project_dir="$3"

    log_debug "md_agent_run: starting with md_file=$md_file worker_dir=$worker_dir project_dir=$project_dir"

    # Load the agent definition
    log_debug "md_agent_run: loading agent definition"
    if ! md_agent_load "$md_file"; then
        log_error "md_agent_run: md_agent_load failed for $md_file"
        return 1
    fi
    log_debug "md_agent_run: loaded type=$_MD_TYPE mode=$_MD_MODE workspace_override=$_MD_WORKSPACE_OVERRIDE"

    # Set runtime context
    _MD_WORKER_DIR="$worker_dir"
    _MD_PROJECT_DIR="$project_dir"

    # Determine workspace
    if [ "$_MD_WORKSPACE_OVERRIDE" = "project_dir" ]; then
        _MD_WORKSPACE="$project_dir"
    else
        _MD_WORKSPACE="$worker_dir/workspace"
    fi
    log_debug "md_agent_run: workspace set to $_MD_WORKSPACE"

    # Extract task ID from worker directory name
    local worker_id
    worker_id=$(basename "$worker_dir")
    _MD_TASK_ID=$(echo "$worker_id" | sed -E 's/worker-([A-Za-z]{2,10}-[0-9]{1,4})-.*/\1/' || echo "")
    log_debug "md_agent_run: task_id=$_MD_TASK_ID"

    # Initialize agent metadata for base library compatibility
    agent_init_metadata "$_MD_TYPE" "$_MD_DESCRIPTION"

    # Create standard directories
    log_debug "md_agent_run: creating directories"
    agent_create_directories "$worker_dir"

    # Set up callback context
    agent_setup_context "$worker_dir" "$_MD_WORKSPACE" "$project_dir" "$_MD_TASK_ID"

    log "Running markdown agent: $_MD_TYPE (mode=$_MD_MODE)"

    # Call agent_on_ready hook if defined (allows shell extensions to initialize state)
    if declare -f agent_on_ready &>/dev/null; then
        log_debug "Calling agent_on_ready hook"
        set +e
        agent_on_ready "$worker_dir" "$project_dir"
        local ready_exit=$?
        set -e
        if [ "$ready_exit" -ne 0 ]; then
            log_error "agent_on_ready hook failed with exit code: $ready_exit"
            return "$ready_exit"
        fi
        log_debug "agent_on_ready hook completed successfully"
    fi

    log_debug "md_agent_run: about to execute mode handler"

    # Execute based on mode
    log_debug "md_agent_run: entering case statement with mode=$_MD_MODE"
    case "$_MD_MODE" in
        ralph_loop)
            log_debug "md_agent_run: matched ralph_loop, calling _md_run_ralph_loop"
            _md_run_ralph_loop "$worker_dir"
            ;;
        once)
            log_debug "md_agent_run: matched once, calling _md_run_once"
            _md_run_once "$worker_dir"
            ;;
        resume)
            log_debug "md_agent_run: matched resume, calling _md_run_resume"
            _md_run_resume "$worker_dir"
            ;;
        *)
            log_error "Unknown execution mode: $_MD_MODE"
            return 1
            ;;
    esac

    local exit_code=$?
    log_debug "md_agent_run: case statement completed with exit_code=$exit_code"

    # Extract and write result
    _md_extract_and_write_result "$worker_dir"

    return $exit_code
}

# =============================================================================
# EXECUTION MODE IMPLEMENTATIONS
# =============================================================================

# Execute in ralph_loop mode
_md_run_ralph_loop() {
    local worker_dir="$1"

    log_debug "_md_run_ralph_loop: starting for worker_dir=$worker_dir"

    # Source ralph loop
    log_debug "_md_run_ralph_loop: sourcing run-claude-ralph-loop.sh"
    source "$WIGGUM_HOME/lib/claude/run-claude-ralph-loop.sh"

    # Get config values
    local agent_name_upper
    agent_name_upper=$(echo "$_MD_TYPE" | tr '[:lower:]' '[:upper:]' | tr '.' '_' | tr '-' '_')
    local max_turns_var="WIGGUM_${agent_name_upper}_MAX_TURNS"
    local max_iterations_var="WIGGUM_${agent_name_upper}_MAX_ITERATIONS"

    local max_turns="${!max_turns_var:-${AGENT_CONFIG_MAX_TURNS:-50}}"
    local max_iterations="${!max_iterations_var:-${AGENT_CONFIG_MAX_ITERATIONS:-5}}"

    # Use step ID from pipeline for session prefix
    local session_prefix="${WIGGUM_STEP_ID:-agent}"

    log_debug "_md_run_ralph_loop: max_turns=$max_turns max_iterations=$max_iterations session_prefix=$session_prefix"

    # Interpolate system prompt
    local system_prompt
    system_prompt=$(_md_interpolate "$_MD_SYSTEM_PROMPT")
    log_debug "_md_run_ralph_loop: system_prompt interpolated (${#system_prompt} chars)"

    # Verify callback functions exist
    if ! declare -F "_md_user_prompt_callback" > /dev/null 2>&1; then
        log_error "_md_run_ralph_loop: callback _md_user_prompt_callback not found!"
        return 1
    fi
    if ! declare -F "_md_completion_check" > /dev/null 2>&1; then
        log_error "_md_run_ralph_loop: callback _md_completion_check not found!"
        return 1
    fi
    log_debug "_md_run_ralph_loop: callback functions verified"

    # Run the loop
    log_debug "_md_run_ralph_loop: calling run_ralph_loop with workspace=$_MD_WORKSPACE"
    run_ralph_loop "$_MD_WORKSPACE" \
        "$system_prompt" \
        "_md_user_prompt_callback" \
        "_md_completion_check" \
        "$max_iterations" "$max_turns" "$worker_dir" "$session_prefix"
}

# Execute in once mode
_md_run_once() {
    local worker_dir="$1"

    # Source once execution
    source "$WIGGUM_HOME/lib/claude/run-claude-once.sh"

    # Get config values
    local agent_name_upper
    agent_name_upper=$(echo "$_MD_TYPE" | tr '[:lower:]' '[:upper:]' | tr '.' '_' | tr '-' '_')
    local max_turns_var="WIGGUM_${agent_name_upper}_MAX_TURNS"
    local max_turns="${!max_turns_var:-${AGENT_CONFIG_MAX_TURNS:-30}}"

    # Use step ID from pipeline for log naming
    local step_id="${WIGGUM_STEP_ID:-agent}"
    local log_timestamp
    log_timestamp=$(date +%s)
    local log_file="$worker_dir/logs/${step_id}-${log_timestamp}.log"

    # Interpolate prompts
    local system_prompt
    system_prompt=$(_md_interpolate "$_MD_SYSTEM_PROMPT")
    local user_prompt
    user_prompt=$(_md_interpolate "$_MD_USER_PROMPT")

    # Run once
    run_agent_once "$_MD_WORKSPACE" "$system_prompt" "$user_prompt" "$log_file" "$max_turns"
}

# Execute in resume mode
_md_run_resume() {
    local worker_dir="$1"

    # Source resume execution
    source "$WIGGUM_HOME/lib/claude/run-claude-resume.sh"

    # Get config values
    local agent_name_upper
    agent_name_upper=$(echo "$_MD_TYPE" | tr '[:lower:]' '[:upper:]' | tr '.' '_' | tr '-' '_')
    local max_turns_var="WIGGUM_${agent_name_upper}_MAX_TURNS"
    local max_turns="${!max_turns_var:-${AGENT_CONFIG_MAX_TURNS:-5}}"

    # Determine session to resume
    local session_id=""

    if [ "$_MD_SESSION_FROM" = "parent" ]; then
        session_id="${WIGGUM_PARENT_SESSION_ID:-}"
        if [ -z "$session_id" ]; then
            log_error "session_from=parent but WIGGUM_PARENT_SESSION_ID is not set"
            return 1
        fi
    else
        # Try to find session from parent result file
        if [ -n "${WIGGUM_PARENT_STEP_ID:-}" ]; then
            local parent_result
            parent_result=$(agent_find_latest_result "$worker_dir" "${WIGGUM_PARENT_STEP_ID}")
            if [ -n "$parent_result" ] && [ -f "$parent_result" ]; then
                session_id=$(jq -r '.outputs.session_id // ""' "$parent_result" 2>/dev/null)
            fi
        fi

        if [ -z "$session_id" ]; then
            log_error "Cannot determine session to resume for mode=resume"
            return 1
        fi
    fi

    # Use step ID from pipeline for log naming
    local step_id="${WIGGUM_STEP_ID:-agent}"
    local log_timestamp
    log_timestamp=$(date +%s)
    local log_file="$worker_dir/logs/${step_id}-${log_timestamp}.log"

    # Interpolate user prompt only (no system prompt for resume)
    local user_prompt
    user_prompt=$(_md_interpolate "$_MD_USER_PROMPT")

    log "Resuming session: $session_id"

    # Run resume
    run_agent_resume "$session_id" "$user_prompt" "$log_file" "$max_turns"
}

# =============================================================================
# AGENT INTERFACE COMPATIBILITY
# =============================================================================

# These functions are called by agent-registry.sh and need to be defined
# after md_agent_load() is called.

# Generate agent_required_paths function for loaded markdown agent
_md_define_required_paths() {
    # Define a function that returns the required paths
    agent_required_paths() {
        for path in "${_MD_REQUIRED_PATHS[@]}"; do
            echo "$path"
        done
    }
}

# Global to store the md_file path for the agent_run function
# (bash doesn't support closures - variables are resolved at call time, not definition time)
declare -g _MD_AGENT_FILE=""

# Generate agent_run function for loaded markdown agent
_md_define_agent_run() {
    local md_file="$1"

    # Store in global so agent_run can access it at call time
    _MD_AGENT_FILE="$md_file"

    agent_run() {
        local worker_dir="$1"
        local project_dir="$2"

        if [ -z "$_MD_AGENT_FILE" ]; then
            log_error "agent_run: _MD_AGENT_FILE not set (md_agent_init not called?)"
            return 1
        fi

        log_debug "agent_run wrapper: calling md_agent_run with file=$_MD_AGENT_FILE"
        md_agent_run "$_MD_AGENT_FILE" "$worker_dir" "$project_dir"
    }
}

# Load a markdown agent and define standard agent functions
#
# This is called by agent-registry.sh when loading .md agents
#
# Args:
#   md_file    - Path to the markdown agent definition
#   agent_type - Agent type (for metadata)
#
# Defines: agent_required_paths, agent_run
md_agent_init() {
    local md_file="$1"
    local agent_type="$2"

    # Load the definition
    if ! md_agent_load "$md_file"; then
        return 1
    fi

    # Define required interface functions
    _md_define_required_paths
    _md_define_agent_run "$md_file"

    log_debug "Initialized markdown agent interface: $agent_type"
    return 0
}
