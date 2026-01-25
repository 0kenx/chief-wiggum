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

    # Parse using yq if available, else use basic grep/sed parsing
    if command -v yq &>/dev/null; then
        _md_parse_frontmatter_yq "$frontmatter"
    else
        _md_parse_frontmatter_bash "$frontmatter"
    fi
}

# Parse frontmatter using yq (preferred)
_md_parse_frontmatter_yq() {
    local frontmatter="$1"

    _MD_TYPE=$(echo "$frontmatter" | yq -r '.type // ""')
    _MD_DESCRIPTION=$(echo "$frontmatter" | yq -r '.description // ""')
    _MD_MODE=$(echo "$frontmatter" | yq -r '.mode // "ralph_loop"')
    _MD_READONLY=$(echo "$frontmatter" | yq -r '.readonly // "false"')
    _MD_REPORT_TAG=$(echo "$frontmatter" | yq -r '.report_tag // "report"')
    _MD_RESULT_TAG=$(echo "$frontmatter" | yq -r '.result_tag // "result"')
    _MD_OUTPUT_PATH=$(echo "$frontmatter" | yq -r '.output_path // ""')
    _MD_WORKSPACE_OVERRIDE=$(echo "$frontmatter" | yq -r '.workspace_override // ""')
    _MD_COMPLETION_CHECK=$(echo "$frontmatter" | yq -r '.completion_check // "result_tag"')
    _MD_SESSION_FROM=$(echo "$frontmatter" | yq -r '.session_from // ""')

    # Parse arrays
    _MD_REQUIRED_PATHS=()
    local paths
    paths=$(echo "$frontmatter" | yq -r '.required_paths[]? // empty')
    local i=0
    while IFS= read -r path; do
        [ -n "$path" ] && _MD_REQUIRED_PATHS[$i]="$path"
        ((++i)) || true
    done <<< "$paths"

    _MD_VALID_RESULTS=()
    local results
    results=$(echo "$frontmatter" | yq -r '.valid_results[]? // empty')
    i=0
    while IFS= read -r result; do
        [ -n "$result" ] && _MD_VALID_RESULTS[$i]="$result"
        ((++i)) || true
    done <<< "$results"

    _MD_OUTPUTS=()
    local outputs
    outputs=$(echo "$frontmatter" | yq -r '.outputs[]? // empty')
    i=0
    while IFS= read -r output; do
        [ -n "$output" ] && _MD_OUTPUTS[$i]="$output"
        ((++i)) || true
    done <<< "$outputs"
}

# Parse frontmatter using pure bash (fallback)
_md_parse_frontmatter_bash() {
    local frontmatter="$1"

    # Simple key: value extraction
    _MD_TYPE=$(echo "$frontmatter" | grep -E '^type:' | sed 's/^type:\s*//' | tr -d '"' | tr -d "'")
    _MD_DESCRIPTION=$(echo "$frontmatter" | grep -E '^description:' | sed 's/^description:\s*//' | tr -d '"' | tr -d "'")
    _MD_MODE=$(echo "$frontmatter" | grep -E '^mode:' | sed 's/^mode:\s*//' | tr -d '"' | tr -d "'" || echo "ralph_loop")
    _MD_READONLY=$(echo "$frontmatter" | grep -E '^readonly:' | sed 's/^readonly:\s*//' | tr -d '"' | tr -d "'" || echo "false")
    _MD_REPORT_TAG=$(echo "$frontmatter" | grep -E '^report_tag:' | sed 's/^report_tag:\s*//' | tr -d '"' | tr -d "'" || echo "report")
    _MD_RESULT_TAG=$(echo "$frontmatter" | grep -E '^result_tag:' | sed 's/^result_tag:\s*//' | tr -d '"' | tr -d "'" || echo "result")
    _MD_OUTPUT_PATH=$(echo "$frontmatter" | grep -E '^output_path:' | sed 's/^output_path:\s*//' | tr -d '"' | tr -d "'" || echo "")
    _MD_WORKSPACE_OVERRIDE=$(echo "$frontmatter" | grep -E '^workspace_override:' | sed 's/^workspace_override:\s*//' | tr -d '"' | tr -d "'" || echo "")
    _MD_COMPLETION_CHECK=$(echo "$frontmatter" | grep -E '^completion_check:' | sed 's/^completion_check:\s*//' | tr -d '"' | tr -d "'" || echo "result_tag")
    _MD_SESSION_FROM=$(echo "$frontmatter" | grep -E '^session_from:' | sed 's/^session_from:\s*//' | tr -d '"' | tr -d "'" || echo "")

    # Parse arrays (simple bracket notation: [a, b, c])
    _MD_REQUIRED_PATHS=()
    local paths_line
    paths_line=$(echo "$frontmatter" | grep -E '^required_paths:' | sed 's/^required_paths:\s*//')
    if [[ "$paths_line" =~ ^\[.*\]$ ]]; then
        paths_line="${paths_line:1:-1}"  # Remove brackets
        IFS=', ' read -ra paths <<< "$paths_line"
        local i=0
        for path in "${paths[@]}"; do
            path=$(echo "$path" | tr -d '"' | tr -d "'" | xargs)
            [ -n "$path" ] && _MD_REQUIRED_PATHS[$i]="$path"
            ((++i)) || true
        done
    fi

    _MD_VALID_RESULTS=()
    local results_line
    results_line=$(echo "$frontmatter" | grep -E '^valid_results:' | sed 's/^valid_results:\s*//')
    if [[ "$results_line" =~ ^\[.*\]$ ]]; then
        results_line="${results_line:1:-1}"
        IFS=', ' read -ra results <<< "$results_line"
        local i=0
        for result in "${results[@]}"; do
            result=$(echo "$result" | tr -d '"' | tr -d "'" | xargs)
            [ -n "$result" ] && _MD_VALID_RESULTS[$i]="$result"
            ((++i)) || true
        done
    fi

    _MD_OUTPUTS=()
    local outputs_line
    outputs_line=$(echo "$frontmatter" | grep -E '^outputs:' | sed 's/^outputs:\s*//')
    if [[ "$outputs_line" =~ ^\[.*\]$ ]]; then
        outputs_line="${outputs_line:1:-1}"
        IFS=', ' read -ra outputs <<< "$outputs_line"
        local i=0
        for output in "${outputs[@]}"; do
            output=$(echo "$output" | tr -d '"' | tr -d "'" | xargs)
            [ -n "$output" ] && _MD_OUTPUTS[$i]="$output"
            ((++i)) || true
        done
    fi
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

    # Load the agent definition
    if ! md_agent_load "$md_file"; then
        return 1
    fi

    # Set runtime context
    _MD_WORKER_DIR="$worker_dir"
    _MD_PROJECT_DIR="$project_dir"

    # Determine workspace
    if [ "$_MD_WORKSPACE_OVERRIDE" = "project_dir" ]; then
        _MD_WORKSPACE="$project_dir"
    else
        _MD_WORKSPACE="$worker_dir/workspace"
    fi

    # Extract task ID from worker directory name
    local worker_id
    worker_id=$(basename "$worker_dir")
    _MD_TASK_ID=$(echo "$worker_id" | sed -E 's/worker-([A-Za-z]{2,10}-[0-9]{1,4})-.*/\1/' || echo "")

    # Initialize agent metadata for base library compatibility
    agent_init_metadata "$_MD_TYPE" "$_MD_DESCRIPTION"

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Set up callback context
    agent_setup_context "$worker_dir" "$_MD_WORKSPACE" "$project_dir" "$_MD_TASK_ID"

    log "Running markdown agent: $_MD_TYPE (mode=$_MD_MODE)"

    # Call agent_on_ready hook if defined (allows shell extensions to initialize state)
    if declare -f agent_on_ready &>/dev/null; then
        log_debug "Calling agent_on_ready hook"
        agent_on_ready "$worker_dir"
    fi

    # Execute based on mode
    case "$_MD_MODE" in
        ralph_loop)
            _md_run_ralph_loop "$worker_dir"
            ;;
        once)
            _md_run_once "$worker_dir"
            ;;
        resume)
            _md_run_resume "$worker_dir"
            ;;
        *)
            log_error "Unknown execution mode: $_MD_MODE"
            return 1
            ;;
    esac

    local exit_code=$?

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

    # Source ralph loop
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

    # Interpolate system prompt
    local system_prompt
    system_prompt=$(_md_interpolate "$_MD_SYSTEM_PROMPT")

    # Run the loop
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

# Generate agent_run function for loaded markdown agent
_md_define_agent_run() {
    local md_file="$1"

    agent_run() {
        local worker_dir="$1"
        local project_dir="$2"
        md_agent_run "$md_file" "$worker_dir" "$project_dir"
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
