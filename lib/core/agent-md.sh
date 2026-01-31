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
source "$WIGGUM_HOME/lib/core/platform.sh"
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
declare -g _MD_SUPERVISOR_INTERVAL=""
declare -g _MD_PLAN_FILE=""
declare -gA _MD_REQUIRED_PATHS=()
declare -gA _MD_VALID_RESULTS=()
declare -gA _MD_OUTPUTS=()

# Runtime state for callbacks
declare -g _MD_SUPERVISOR_FEEDBACK=""

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
#
# Security: Validates array_name against strict pattern before using eval
_yaml_get_array() {
    local frontmatter="$1"
    local key="$2"
    local array_name="$3"

    # Security: Validate array name contains only safe characters (alphanumeric and underscore)
    # This prevents code injection through malicious array names
    if [[ ! "$array_name" =~ ^[A-Za-z_][A-Za-z0-9_]*$ ]]; then
        log_error "_yaml_get_array: Invalid array name: $array_name"
        return 1
    fi

    # Clear the array (safe after validation)
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
                # Safe after array_name validation above
                # Use \$item to defer expansion until eval time for proper quoting
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
    _MD_SUPERVISOR_INTERVAL=$(_yaml_get_value "$frontmatter" "supervisor_interval" "0")
    _MD_PLAN_FILE=$(_yaml_get_value "$frontmatter" "plan_file" "")

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
    result="${result//\{\{ralph_dir\}\}/${RALPH_DIR:-$_MD_PROJECT_DIR/.ralph}}"

    # Task/step context
    result="${result//\{\{task_id\}\}/$_MD_TASK_ID}"
    result="${result//\{\{step_id\}\}/${WIGGUM_STEP_ID:-}}"
    result="${result//\{\{run_id\}\}/${RALPH_RUN_ID:-}}"

    # Plan file (from env or computed default)
    local plan_file_path="${WIGGUM_PLAN_FILE:-${RALPH_DIR:-$_MD_PROJECT_DIR/.ralph}/plans/${_MD_TASK_ID}.md}"
    result="${result//\{\{plan_file\}\}/$plan_file_path}"

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

    if [[ "$result" == *"{{plan_section}}"* ]]; then
        local plan_section
        plan_section=$(_md_generate_plan_section)
        result="${result//\{\{plan_section\}\}/$plan_section}"
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

    # Supervisor feedback variable
    result="${result//\{\{supervisor_feedback\}\}/${_MD_SUPERVISOR_FEEDBACK:-}}"

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

# Check if a prompt already contains result tag instructions
#
# Args:
#   prompt - The prompt text to check
#
# Returns: 0 if result tag instructions found, 1 otherwise
_md_has_result_tag_section() {
    local prompt="$1"
    local result_tag="${_MD_RESULT_TAG:-result}"

    # Check for common patterns indicating result tag instructions exist
    # Pattern 1: <result>VALUE</result>
    # Pattern 2: The <result> tag MUST be exactly
    if [[ "$prompt" == *"<${result_tag}>"* ]] || \
       [[ "$prompt" == *"<${result_tag}> tag"* ]] || \
       [[ "$prompt" == *"<${result_tag}> MUST"* ]]; then
        return 0
    fi
    return 1
}

# Generate result tag section from valid_results array
#
# Returns: Generated result tag section text
_md_generate_result_tag_section() {
    local result_tag="${_MD_RESULT_TAG:-result}"
    local section=""
    local values=""
    local first=true

    # Build the OR-separated list of valid result tags
    for result in "${_MD_VALID_RESULTS[@]}"; do
        if [ "$first" = true ]; then
            section+="<${result_tag}>${result}</${result_tag}>"
            values="$result"
            first=false
        else
            section+=$'\n'"OR"$'\n'"<${result_tag}>${result}</${result_tag}>"
            values+=", $result"
        fi
    done

    # Add the instruction line
    section+=$'\n'$'\n'"The <${result_tag}> tag MUST be exactly: ${values}."

    echo "$section"
}

# Generate result tag reminder for continuation prompts
#
# Returns: Generated reminder text
_md_generate_result_tag_reminder() {
    local result_tag="${_MD_RESULT_TAG:-result}"
    local values=""
    local first=true

    for result in "${_MD_VALID_RESULTS[@]}"; do
        if [ "$first" = true ]; then
            values="$result"
            first=false
        else
            values+=", $result"
        fi
    done

    echo "Remember: The <${result_tag}> tag must contain exactly ${values}."
}

# Augment prompts with result tag section if missing
#
# This ensures agents always know what valid results to output,
# even if the prompt author forgot to include the section.
_md_augment_prompts_with_result_tag() {
    # Skip if no valid results defined
    if [ ${#_MD_VALID_RESULTS[@]} -eq 0 ]; then
        return 0
    fi

    # Skip if user prompt is empty (let validation catch this)
    if [ -z "$_MD_USER_PROMPT" ]; then
        return 0
    fi

    # Augment user prompt if result tag section is missing
    if ! _md_has_result_tag_section "$_MD_USER_PROMPT"; then
        local result_section
        result_section=$(_md_generate_result_tag_section)
        _MD_USER_PROMPT="${_MD_USER_PROMPT}"$'\n'$'\n'"## Result (REQUIRED)"$'\n'$'\n'"${result_section}"
        log_debug "Auto-generated result tag section for user prompt"
    fi

    # Augment continuation prompt if it exists and lacks reminder
    if [ -n "$_MD_CONTINUATION_PROMPT" ] && ! _md_has_result_tag_section "$_MD_CONTINUATION_PROMPT"; then
        local reminder
        reminder=$(_md_generate_result_tag_reminder)
        _MD_CONTINUATION_PROMPT="${_MD_CONTINUATION_PROMPT}"$'\n'$'\n'"${reminder}"
        log_debug "Auto-generated result tag reminder for continuation prompt"
    fi
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

# Generate plan section if plan file exists
#
# Returns: Markdown section referencing the plan file, or empty string
_md_generate_plan_section() {
    local plan_file="${_MD_PLAN_FILE:-}"

    # Interpolate path variables in plan_file
    [ -n "$plan_file" ] && plan_file=$(_md_interpolate "$plan_file")

    # Return empty if no plan file specified or file doesn't exist
    [ -z "$plan_file" ] || [ ! -f "$plan_file" ] && { echo ""; return; }

    cat << EOF

IMPLEMENTATION PLAN AVAILABLE:

An implementation plan has been created for this task. Before starting:
1. Read the plan at: @$plan_file
2. Follow the implementation approach described in the plan
3. Pay attention to the Critical Files section
4. Consider the potential challenges identified

The plan provides guidance on:
- Existing patterns in the codebase to follow
- Recommended implementation approach
- Dependencies and sequencing
- Potential challenges to watch for
EOF
}

# =============================================================================
# CONDITIONAL SECTION PROCESSING
# =============================================================================

# Process conditional XML tags in template
#
# Supports:
#   <WIGGUM_IF_SUPERVISOR>content</WIGGUM_IF_SUPERVISOR> - Include if supervisor_feedback non-empty
#   <WIGGUM_IF_ITERATION_ZERO>content</WIGGUM_IF_ITERATION_ZERO> - Include on iteration 0 only
#   <WIGGUM_IF_ITERATION_NONZERO>content</WIGGUM_IF_ITERATION_NONZERO> - Include on iteration > 0
#   <WIGGUM_IF_FILE_EXISTS:path>content</WIGGUM_IF_FILE_EXISTS> - Include if path exists
#
# Args:
#   template  - Template string with conditional tags
#   iteration - Current iteration number
#
# Returns: Processed template string
_md_process_conditionals() {
    local template="$1"
    local iteration="$2"
    local result="$template"

    # Process <WIGGUM_IF_SUPERVISOR>
    if [ -n "${_MD_SUPERVISOR_FEEDBACK:-}" ]; then
        # Keep content, remove tags
        result=$(echo "$result" | sed 's/<WIGGUM_IF_SUPERVISOR>//g; s/<\/WIGGUM_IF_SUPERVISOR>//g')
    else
        # Remove entire block
        result=$(echo "$result" | awk '
            BEGIN { skip = 0 }
            /<WIGGUM_IF_SUPERVISOR>/ { skip = 1; next }
            /<\/WIGGUM_IF_SUPERVISOR>/ { skip = 0; next }
            !skip { print }
        ')
    fi

    # Process <WIGGUM_IF_ITERATION_ZERO>
    if [ "$iteration" -eq 0 ]; then
        # Keep content, remove tags
        result=$(echo "$result" | sed 's/<WIGGUM_IF_ITERATION_ZERO>//g; s/<\/WIGGUM_IF_ITERATION_ZERO>//g')
    else
        # Remove entire block
        result=$(echo "$result" | awk '
            BEGIN { skip = 0 }
            /<WIGGUM_IF_ITERATION_ZERO>/ { skip = 1; next }
            /<\/WIGGUM_IF_ITERATION_ZERO>/ { skip = 0; next }
            !skip { print }
        ')
    fi

    # Process <WIGGUM_IF_ITERATION_NONZERO>
    if [ "$iteration" -gt 0 ]; then
        # Keep content, remove tags
        result=$(echo "$result" | sed 's/<WIGGUM_IF_ITERATION_NONZERO>//g; s/<\/WIGGUM_IF_ITERATION_NONZERO>//g')
    else
        # Remove entire block
        result=$(echo "$result" | awk '
            BEGIN { skip = 0 }
            /<WIGGUM_IF_ITERATION_NONZERO>/ { skip = 1; next }
            /<\/WIGGUM_IF_ITERATION_NONZERO>/ { skip = 0; next }
            !skip { print }
        ')
    fi

    # Process <WIGGUM_IF_FILE_EXISTS:{path}> tags
    # Extract all WIGGUM_IF_FILE_EXISTS tags and process them
    while [[ "$result" =~ \<WIGGUM_IF_FILE_EXISTS:([^>]+)\> ]]; do
        local file_path="${BASH_REMATCH[1]}"
        local open_tag="<WIGGUM_IF_FILE_EXISTS:${file_path}>"
        local close_tag_pattern="</WIGGUM_IF_FILE_EXISTS>"

        # Interpolate the path
        local resolved_path
        resolved_path=$(_md_interpolate "$file_path")

        if [ -f "$resolved_path" ]; then
            # File exists - keep content, remove tags
            result=$(echo "$result" | sed "s|${open_tag}||g; s|${close_tag_pattern}||g")
        else
            # File doesn't exist - remove entire block using awk
            result=$(echo "$result" | awk -v open_tag="$open_tag" -v close_tag="$close_tag_pattern" '
                BEGIN { skip = 0 }
                index($0, open_tag) { skip = 1; next }
                index($0, close_tag) { skip = 0; next }
                !skip { print }
            ')
        fi
    done

    echo "$result"
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

    # Find latest log for this step (run-isolated via RALPH_RUN_ID)
    # RALPH_RUN_ID format: {step_id}-{epoch}, matching log dir naming
    local latest_log=""
    local run_id="${RALPH_RUN_ID:-}"
    if [ -n "$run_id" ] && [ -d "$worker_dir/logs/$run_id" ]; then
        latest_log=$(find_newest "$worker_dir/logs/$run_id" -name "${step_id}-*.log")
    fi

    if [ -n "$latest_log" ] && [ -f "$latest_log" ]; then
        local result_tag="${_MD_RESULT_TAG:-result}"
        # Only search assistant messages to avoid matching example tags in prompts
        if grep '"type":"assistant"' "$latest_log" 2>/dev/null | \
           grep_pcre_test "<${result_tag}>(${valid_regex})</${result_tag}>"; then
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
    # shellcheck disable=SC2034  # supervisor_dir available for custom prompt functions
    local supervisor_dir="${3:-}"
    local supervisor_feedback="${4:-}"

    # Store supervisor feedback for interpolation and conditional processing
    _MD_SUPERVISOR_FEEDBACK="$supervisor_feedback"

    # Interpolate and process conditionals in user prompt
    local user_prompt
    user_prompt=$(_md_interpolate_iteration "$_MD_USER_PROMPT" "$iteration" "$output_dir")
    user_prompt=$(_md_process_conditionals "$user_prompt" "$iteration")
    echo "$user_prompt"

    # Append continuation prompt on iteration > 0
    if [ "$iteration" -gt 0 ] && [ -n "$_MD_CONTINUATION_PROMPT" ]; then
        echo ""
        local cont_prompt
        cont_prompt=$(_md_interpolate_iteration "$_MD_CONTINUATION_PROMPT" "$iteration" "$output_dir")
        cont_prompt=$(_md_process_conditionals "$cont_prompt" "$iteration")
        echo "$cont_prompt"
    fi
}

# =============================================================================
# RESULT EXTRACTION
# =============================================================================

# Extract result from status file for status_file completion check
#
# Args:
#   status_file - Path to the status file (already interpolated)
#   valid_regex - Pipe-separated valid result values
#
# Returns: Result value (PASS, FAIL, etc.) or empty string
_md_extract_result_from_status_file() {
    local status_file="$1"
    local valid_regex="$2"

    if [ ! -f "$status_file" ]; then
        echo ""
        return
    fi

    # First try to extract <result>VALUE</result> tags from the file
    local result
    result=$(grep_pcre_match "(?<=<result>)(${valid_regex})(?=</result>)" "$status_file" | tail -1) || true

    if [ -n "$result" ]; then
        echo "$result"
        return
    fi

    # No result tag found - check markdown checklists
    # PASS if all items checked, FAIL if any unchecked
    if grep -q '\- \[ \]' "$status_file" 2>/dev/null; then
        echo "FAIL"
    else
        echo "PASS"
    fi
}

# Fallback result extraction from work logs (for supervisor STOP override)
#
# When the supervisor stops the loop, the PRD may have unchecked items even
# though the LLM reported a passing result. This function extracts the result
# from the latest work log as a fallback.
#
# Args:
#   worker_dir  - Worker directory
#   valid_regex - Pipe-separated valid result values
#
# Returns: Result value from log, or empty string if not found
_md_fallback_result_from_logs() {
    local worker_dir="$1"
    local valid_regex="$2"

    local run_id="${RALPH_RUN_ID:-}"
    if [ -z "$run_id" ] || [ ! -d "$worker_dir/logs/$run_id" ]; then
        return 0
    fi

    local step_id="${WIGGUM_STEP_ID:-agent}"
    local latest_log
    latest_log=$(find_newest "$worker_dir/logs/$run_id" -name "${step_id}-*.log")

    if [ -z "$latest_log" ] || [ ! -f "$latest_log" ]; then
        return 0
    fi

    _extract_result_value_from_stream_json "$latest_log" "$valid_regex" || true
}

# Extract result and write to epoch-named files
_md_extract_and_write_result() {
    local worker_dir="$1"
    local step_id="${WIGGUM_STEP_ID:-agent}"
    local check_type="${_MD_COMPLETION_CHECK:-result_tag}"

    local agent_name
    agent_name=$(echo "$_MD_TYPE" | tr '[:lower:]' '[:upper:]' | tr '.' '_')

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

    # For status_file completion check, derive result from the status file only
    if [[ "$check_type" == status_file:* ]]; then
        local file_path="${check_type#status_file:}"
        file_path=$(_md_interpolate "$file_path")

        local result
        result=$(_md_extract_result_from_status_file "$file_path" "$valid_regex")

        # Supervisor STOP override: if PRD says FAIL but supervisor stopped the loop,
        # check if the LLM actually reported a passing result in its work logs
        if [ "$result" = "FAIL" ] && [ "${RALPH_LOOP_STOP_REASON:-}" = "supervisor_stop" ]; then
            local log_result
            log_result=$(_md_fallback_result_from_logs "$worker_dir" "$valid_regex")
            if [ -n "$log_result" ] && [ "$log_result" != "FAIL" ]; then
                log_warn "Supervisor STOP override: LLM output indicates $log_result (PRD has unchecked items)"
                result="$log_result"
            fi
        fi

        if [ -z "$result" ]; then
            result="UNKNOWN"
        fi

        # Include session_id in extra_outputs for downstream steps (e.g., task-summarizer)
        local extra_outputs="{}"
        local session_id="${RALPH_LOOP_LAST_SESSION_ID:-}"
        if [ -n "$session_id" ]; then
            extra_outputs="{\"session_id\":\"$session_id\"}"
        fi

        agent_write_result "$worker_dir" "$result" "$extra_outputs"
        log "${agent_name} result: $result"
        return
    fi

    # For other completion checks, use log extraction
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

    # Augment prompts with result tag section if missing
    _md_augment_prompts_with_result_tag

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
        live)
            log_debug "md_agent_run: matched live, calling _md_run_live"
            _md_run_live "$worker_dir"
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
    log_debug "_md_run_ralph_loop: sourcing runtime"
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"
    source "$WIGGUM_HOME/lib/runtime/runtime-loop.sh"

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

    # Get supervisor interval (0 = disabled)
    local supervisor_interval="${_MD_SUPERVISOR_INTERVAL:-0}"

    # Run the loop
    log_debug "_md_run_ralph_loop: calling run_ralph_loop with workspace=$_MD_WORKSPACE supervisor_interval=$supervisor_interval"
    run_ralph_loop "$_MD_WORKSPACE" \
        "$system_prompt" \
        "_md_user_prompt_callback" \
        "_md_completion_check" \
        "$max_iterations" "$max_turns" "$worker_dir" "$session_prefix" \
        "$supervisor_interval"
}

# Execute in once mode
_md_run_once() {
    local worker_dir="$1"

    # Source runtime
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"

    # Get config values
    local agent_name_upper
    agent_name_upper=$(echo "$_MD_TYPE" | tr '[:lower:]' '[:upper:]' | tr '.' '_' | tr '-' '_')
    local max_turns_var="WIGGUM_${agent_name_upper}_MAX_TURNS"
    local max_turns="${!max_turns_var:-${AGENT_CONFIG_MAX_TURNS:-30}}"

    # Use step ID from pipeline for log naming
    local step_id="${WIGGUM_STEP_ID:-agent}"
    local log_timestamp
    log_timestamp=$(epoch_now)
    local run_id="${step_id}-${log_timestamp}"

    # Set RALPH_RUN_ID for result extraction compatibility
    export RALPH_RUN_ID="$run_id"

    # Create log directory (matching ralph_loop convention)
    mkdir -p "$worker_dir/logs/$run_id"
    local log_file="$worker_dir/logs/$run_id/${step_id}-0-${log_timestamp}.log"

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

    # Source runtime
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"

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
    log_timestamp=$(epoch_now)
    local run_id="${step_id}-${log_timestamp}"

    # Set RALPH_RUN_ID for result extraction compatibility
    export RALPH_RUN_ID="$run_id"

    # Create log directory (matching ralph_loop convention)
    mkdir -p "$worker_dir/logs/$run_id"
    local log_file="$worker_dir/logs/$run_id/${step_id}-0-${log_timestamp}.log"

    # Interpolate user prompt only (no system prompt for resume)
    local user_prompt
    user_prompt=$(_md_interpolate "$_MD_USER_PROMPT")

    log "Resuming session: $session_id"

    # Run resume
    run_agent_resume "$session_id" "$user_prompt" "$log_file" "$max_turns"
}

# Execute in live mode (persistent session across invocations)
#
# Live mode maintains Claude context across multiple invocations within the same worker.
# First call creates a named session; subsequent calls resume it.
#
# Session persistence:
#   - Session file: $worker_dir/live_sessions/{step_id}.session
#   - Contains the session UUID for resumption
#
# Behavior:
#   - First run: Generate UUID, create new session, persist session_id
#   - Subsequent runs: Read session_id, resume existing session
#   - Session expiry: If resume fails, create new session automatically
_md_run_live() {
    local worker_dir="$1"

    # Source runtime (provides both once and resume)
    source "$WIGGUM_HOME/lib/runtime/runtime.sh"

    # Get config values
    local agent_name_upper
    agent_name_upper=$(echo "$_MD_TYPE" | tr '[:lower:]' '[:upper:]' | tr '.' '_' | tr '-' '_')
    local max_turns_var="WIGGUM_${agent_name_upper}_MAX_TURNS"
    local max_turns="${!max_turns_var:-${AGENT_CONFIG_MAX_TURNS:-30}}"

    # Use step ID from pipeline for session naming
    local step_id="${WIGGUM_STEP_ID:-agent}"
    local log_timestamp
    log_timestamp=$(epoch_now)
    local run_id="${step_id}-${log_timestamp}"

    # Set RALPH_RUN_ID for result extraction compatibility
    export RALPH_RUN_ID="$run_id"

    # Create log directory
    mkdir -p "$worker_dir/logs/$run_id"
    local log_file="$worker_dir/logs/$run_id/${step_id}-0-${log_timestamp}.log"

    # Session persistence directory and file
    local session_dir="$worker_dir/live_sessions"
    local session_file="$session_dir/${step_id}.session"
    mkdir -p "$session_dir"

    # Check if we have an existing session
    local session_id=""
    local is_first_run=true

    if [ -f "$session_file" ]; then
        session_id=$(cat "$session_file" 2>/dev/null || true)
        if [ -n "$session_id" ]; then
            is_first_run=false
            log_debug "Live mode: found existing session $session_id"
        fi
    fi

    # Interpolate prompts
    local user_prompt
    user_prompt=$(_md_interpolate "$_MD_USER_PROMPT")

    local exit_code=0

    if [ "$is_first_run" = true ]; then
        # First run: create new named session
        session_id=$(uuidgen 2>/dev/null || cat /proc/sys/kernel/random/uuid 2>/dev/null || echo "$(epoch_now)-$$-$RANDOM")
        log "Live mode: creating new session $session_id"

        # Interpolate system prompt (only needed for first run)
        local system_prompt
        system_prompt=$(_md_interpolate "$_MD_SYSTEM_PROMPT")

        # Create named session
        run_agent_once_with_session "$_MD_WORKSPACE" "$system_prompt" "$user_prompt" "$log_file" "$max_turns" "$session_id" || exit_code=$?

        # Persist session ID on success
        if [ "$exit_code" -eq 0 ]; then
            echo "$session_id" > "$session_file"
            log_debug "Live mode: persisted session to $session_file"
        fi
    else
        # Subsequent run: resume existing session
        log "Live mode: resuming session $session_id"

        run_agent_resume "$session_id" "$user_prompt" "$log_file" "$max_turns" || exit_code=$?

        # Handle session expiry: if resume fails with specific errors, create new session
        if [ "$exit_code" -ne 0 ]; then
            # Check if this looks like a session error (session not found, expired, etc.)
            if grep -q -i -E "(session.*not found|session.*expired|invalid.*session|unknown.*session)" "$log_file" 2>/dev/null; then
                log_warn "Live mode: session expired or invalid, creating new session"

                # Generate new session ID
                session_id=$(uuidgen 2>/dev/null || cat /proc/sys/kernel/random/uuid 2>/dev/null || echo "$(epoch_now)-$$-$RANDOM")

                # Create new log file for retry
                local retry_timestamp
                retry_timestamp=$(epoch_now)
                local retry_log_file="$worker_dir/logs/$run_id/${step_id}-0-${retry_timestamp}-retry.log"

                # Interpolate system prompt for new session
                local system_prompt
                system_prompt=$(_md_interpolate "$_MD_SYSTEM_PROMPT")

                # Create new session
                exit_code=0
                run_agent_once_with_session "$_MD_WORKSPACE" "$system_prompt" "$user_prompt" "$retry_log_file" "$max_turns" "$session_id" || exit_code=$?

                # Persist new session ID on success
                if [ "$exit_code" -eq 0 ]; then
                    echo "$session_id" > "$session_file"
                    log_debug "Live mode: persisted new session to $session_file"
                fi
            fi
        fi
    fi

    return $exit_code
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
