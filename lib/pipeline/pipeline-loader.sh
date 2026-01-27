#!/usr/bin/env bash
# =============================================================================
# pipeline-loader.sh - Load and query pipeline JSON on-demand via jq
#
# Provides:
#   pipeline_load(file)              - Validate JSON, set source, count steps
#   pipeline_load_builtin_defaults() - Store inline JSON for builtin pipeline
#   pipeline_resolve(project_dir, task_id, cli_pipeline_name) - Resolve config path
#   pipeline_find_step_index(step_id) - Return index for a step ID
#   pipeline_step_count()            - Return number of steps
#   pipeline_get(idx, field, default) - Get scalar field from step
#   pipeline_get_json(idx, field, default) - Get compact JSON from step
#   pipeline_get_on_result(idx, result_value) - Get on_result handler
#   pipeline_get_on_max(idx)         - Get on_max jump target
#   pipeline_get_max(idx)            - Get max visits
# =============================================================================

# Prevent double-sourcing
[ -n "${_PIPELINE_LOADER_LOADED:-}" ] && return 0
_PIPELINE_LOADER_LOADED=1

# Pipeline state
_PIPELINE_JSON_FILE=""   # Path to loaded JSON file (empty if using inline)
_PIPELINE_JSON=""        # Inline JSON string (for builtin defaults)
_PIPELINE_STEP_COUNT=0

# Pipeline metadata
PIPELINE_NAME=""

# Internal: run jq against the pipeline source (file or inline string)
_pipeline_jq() {
    local filter="$1"
    shift

    if [ -n "$_PIPELINE_JSON_FILE" ]; then
        jq "$@" "$filter" "$_PIPELINE_JSON_FILE"
    else
        echo "$_PIPELINE_JSON" | jq "$@" "$filter"
    fi
}

# Get a scalar field from a pipeline step
#
# Args:
#   idx     - Step index (0-based)
#   field   - jq field path (e.g., ".agent", ".enabled_by")
#   default - Default value if field is null/missing (default: "")
#
# Returns: Field value via stdout
pipeline_get() {
    local idx="$1"
    local field="$2"
    local default="${3:-}"

    local result
    result=$(_pipeline_jq ".steps[$idx]${field} // null" -r)

    if [ "$result" = "null" ] || [ -z "$result" ]; then
        echo "$default"
    else
        echo "$result"
    fi
}

# Get compact JSON from a pipeline step field
#
# Useful for hooks arrays, config objects, etc.
#
# Args:
#   idx     - Step index (0-based)
#   field   - jq field path (e.g., ".hooks.pre", ".config")
#   default - Default JSON value if null (default: "{}")
#
# Returns: Compact JSON string via stdout
pipeline_get_json() {
    local idx="$1"
    local field="$2"
    local default="${3-}"
    if [ -z "$default" ]; then default="{}"; fi

    local result
    result=$(_pipeline_jq ".steps[$idx]${field} // null" -c)

    if [ "$result" = "null" ]; then
        echo "$default"
    else
        echo "$result"
    fi
}

# Get on_result handler for a specific gate result value
#
# Args:
#   idx          - Step index (0-based)
#   result_value - Gate result value (e.g., "FIX", "FAIL")
#
# Returns: Compact JSON handler via stdout, or empty string if no handler defined
pipeline_get_on_result() {
    local idx="$1"
    local result_value="$2"

    local result
    result=$(_pipeline_jq ".steps[$idx].on_result.\"$result_value\" // null" -c)

    if [ "$result" = "null" ]; then
        echo ""
    else
        echo "$result"
    fi
}

# Get on_max jump target for a step
#
# Args:
#   idx - Step index (0-based)
#
# Returns: Jump target string (default: "next")
pipeline_get_on_max() {
    local idx="$1"
    pipeline_get "$idx" ".on_max" "next"
}

# Get max visits for a step
#
# Args:
#   idx - Step index (0-based)
#
# Returns: Max visit count (0 = unlimited)
pipeline_get_max() {
    local idx="$1"
    local val
    val=$(pipeline_get "$idx" ".max" "0")
    echo "$val"
}

# Load pipeline configuration from a JSON file
#
# Validates JSON structure, checks for unique IDs, valid agents, and
# valid on_result jump targets.
#
# Args:
#   file - Path to pipeline JSON file
#
# Returns: 0 on success, 1 on error
pipeline_load() {
    local file="$1"

    log "DEBUG pipeline_load: checking file existence: $file"
    if [ ! -f "$file" ]; then
        log_error "Pipeline config not found: $file"
        return 1
    fi
    log "DEBUG pipeline_load: file exists"

    # Validate JSON
    log "DEBUG pipeline_load: validating JSON..."
    if ! jq empty "$file" 2>/dev/null; then
        log_error "Invalid JSON in pipeline config: $file"
        return 1
    fi
    log "DEBUG pipeline_load: JSON valid"

    # Read pipeline name
    log "DEBUG pipeline_load: reading pipeline name..."
    PIPELINE_NAME=$(jq -r '.name // "unnamed"' "$file")
    log "DEBUG pipeline_load: name=$PIPELINE_NAME"

    # Get step count
    local step_count
    step_count=$(jq '.steps | length' "$file")

    if [ "$step_count" -eq 0 ]; then
        log_error "Pipeline has no steps: $file"
        return 1
    fi

    # Validate unique IDs
    local dup_check
    dup_check=$(jq -r '[.steps[].id] | group_by(.) | map(select(length > 1)) | .[0][0] // empty' "$file")
    if [ -n "$dup_check" ]; then
        log_error "Duplicate pipeline step ID: $dup_check"
        return 1
    fi

    # Validate all steps have id and agent
    local missing_id
    missing_id=$(jq -r '.steps | to_entries[] | select(.value.id == null or .value.id == "") | .key' "$file" | head -1)
    if [ -n "$missing_id" ]; then
        log_error "Pipeline step missing required 'id' field (index $missing_id)"
        return 1
    fi

    local missing_agent
    missing_agent=$(jq -r '.steps | to_entries[] | select(.value.agent == null or .value.agent == "") | .key' "$file" | head -1)
    if [ -n "$missing_agent" ]; then
        log_error "Pipeline step missing required 'agent' field (index $missing_agent)"
        return 1
    fi

    # Validate on_result jump targets reference valid step IDs or special targets
    local bad_jump
    bad_jump=$(jq -r '
        [.steps[].id] as $ids |
        ["self","prev","next","abort"] as $special |
        [.steps[].on_result // {} | to_entries[].value | select(.jump != null) | .jump] |
        .[] | select(. as $t | ($special | index($t)) == null and ($ids | index($t)) == null)
    ' "$file" 2>/dev/null | head -1)
    if [ -n "$bad_jump" ]; then
        log_error "Pipeline on_result references unknown jump target: $bad_jump"
        return 1
    fi

    # Store source
    _PIPELINE_JSON_FILE="$file"
    _PIPELINE_JSON=""
    _PIPELINE_STEP_COUNT="$step_count"

    log "Loaded pipeline '$PIPELINE_NAME' with $step_count steps"
    return 0
}

# Load built-in defaults matching the new jump-based schema
# Used as fallback when no pipeline config file exists
pipeline_load_builtin_defaults() {
    PIPELINE_NAME="builtin-default"

    _PIPELINE_JSON_FILE=""
    _PIPELINE_JSON='{
  "name": "builtin-default",
  "steps": [
    {"id":"planning","agent":"product.plan-mode","readonly":true,"enabled_by":"WIGGUM_PLAN_MODE"},
    {"id":"execution","agent":"engineering.software-engineer","max":3,"commit_after":true,"config":{"max_iterations":20,"max_turns":50,"supervisor_interval":2}},
    {"id":"summary","agent":"general.task-summarizer","readonly":true},
    {"id":"audit","agent":"engineering.security-audit","max":3,"readonly":true,"on_result":{"FIX":{"id":"audit-fix","agent":"engineering.security-fix","max":2,"commit_after":true}}},
    {"id":"test","agent":"engineering.test-coverage","max":2,"commit_after":true,"on_result":{"FIX":{"id":"test-fix","agent":"engineering.generic-fix","max":2,"commit_after":true}}},
    {"id":"docs","agent":"general.documentation-writer","commit_after":true},
    {"id":"validation","agent":"engineering.validation-review","readonly":true}
  ]
}'
    _PIPELINE_STEP_COUNT=7

    log "Loaded built-in default pipeline with $_PIPELINE_STEP_COUNT steps"
}

# Resolve the pipeline config file path using priority order:
#   1. CLI flag (--pipeline <name>) -> config/pipelines/<name>.json or .ralph/pipelines/<name>.json
#   2. Per-task override -> .ralph/pipelines/<task-id>.json
#   3. Project default -> config/pipeline.json
#   4. Built-in fallback (returns empty string, caller uses pipeline_load_builtin_defaults)
#
# Args:
#   project_dir       - Project root directory
#   task_id           - Task ID (e.g., TASK-001)
#   cli_pipeline_name - Pipeline name from --pipeline flag (can be empty)
#
# Returns: Path to pipeline config file (stdout), or empty string for builtin
pipeline_resolve() {
    local project_dir="$1"
    local task_id="$2"
    local cli_pipeline_name="${3:-}"
    local ralph_dir="${RALPH_DIR:-$project_dir/.ralph}"

    # 1. CLI flag: --pipeline <name>
    if [ -n "$cli_pipeline_name" ]; then
        # Check project config/pipelines/ first
        local cli_path="$WIGGUM_HOME/config/pipelines/${cli_pipeline_name}.json"
        if [ -f "$cli_path" ]; then
            echo "$cli_path"
            return 0
        fi
        # Check .ralph/pipelines/
        cli_path="$ralph_dir/pipelines/${cli_pipeline_name}.json"
        if [ -f "$cli_path" ]; then
            echo "$cli_path"
            return 0
        fi
        log_warn "Pipeline '$cli_pipeline_name' not found, falling back to defaults"
    fi

    # 2. Per-task override
    local task_path="$ralph_dir/pipelines/${task_id}.json"
    if [ -f "$task_path" ]; then
        echo "$task_path"
        return 0
    fi

    # 3. Project default
    local default_path="$WIGGUM_HOME/config/pipeline.json"
    if [ -f "$default_path" ]; then
        echo "$default_path"
        return 0
    fi

    # 4. No config found - return empty (caller will use builtin defaults)
    echo ""
    return 0
}

# Find the index for a given step ID
#
# Args:
#   step_id - The step ID to find
#
# Returns: Index (0-based) via stdout, or -1 if not found
pipeline_find_step_index() {
    local step_id="$1"

    local result
    result=$(_pipeline_jq '.steps | to_entries[] | select(.value.id == "'"$step_id"'") | .key' -r | head -1)

    if [ -n "$result" ]; then
        echo "$result"
        return 0
    fi

    echo "-1"
    return 1
}

# Get the number of steps in the loaded pipeline
pipeline_step_count() {
    echo "$_PIPELINE_STEP_COUNT"
}

# Get a result mapping field value with per-agent and pipeline override support
#
# Resolution order:
#   1. Pipeline-level result_mappings (highest priority)
#   2. Per-agent result_mappings in config/agents.json
#   3. defaults.result_mappings in config/agents.json (lowest priority)
#
# Args:
#   result     - Gate result value (e.g., PASS, FAIL, FIX)
#   field      - Field name: status, exit_code, or default_jump
#   agent_type - Agent type (e.g., "engineering.security-audit") for per-agent lookup
#
# Returns: Field value, or empty string if not found
pipeline_get_result_mapping() {
    local result="$1"
    local field="$2"
    local agent_type="${3:-}"

    # 1. Try pipeline-level override first
    local pipeline_value=""
    pipeline_value=$(_pipeline_jq ".result_mappings.\"$result\".$field // null" -r 2>/dev/null)

    if [ -n "$pipeline_value" ] && [ "$pipeline_value" != "null" ]; then
        echo "$pipeline_value"
        return 0
    fi

    local config_file="$WIGGUM_HOME/config/agents.json"
    if [ -f "$config_file" ]; then
        # 2. Try per-agent result_mappings
        if [ -n "$agent_type" ]; then
            local agent_value
            agent_value=$(jq -r ".agents.\"$agent_type\".result_mappings.\"$result\".$field // null" "$config_file" 2>/dev/null)
            if [ -n "$agent_value" ] && [ "$agent_value" != "null" ]; then
                echo "$agent_value"
                return 0
            fi
        fi

        # 3. Fall back to defaults.result_mappings
        local default_value
        default_value=$(jq -r ".defaults.result_mappings.\"$result\".$field // null" "$config_file" 2>/dev/null)
        if [ -n "$default_value" ] && [ "$default_value" != "null" ]; then
            echo "$default_value"
            return 0
        fi
    fi

    echo ""
    return 1
}
