#!/usr/bin/env bash
# issue-parser.sh - Parse GitHub issue JSON into kanban fields
#
# Extracts structured fields from issue title and body.
# All content handling uses jq --arg for safe variable binding.
# No eval, no shell expansion of issue content.
set -euo pipefail

# Prevent double-sourcing
[ -n "${_GITHUB_ISSUE_PARSER_LOADED:-}" ] && return 0
_GITHUB_ISSUE_PARSER_LOADED=1

source "$WIGGUM_HOME/lib/core/safe-path.sh"

# =============================================================================
# Task ID Extraction
# =============================================================================

# Extract task ID from issue title
#
# Matches [A-Za-z]{2,10}-[0-9]{1,4} inside brackets.
# Supports both **[ID]** and [ID] formats.
#
# Args:
#   title - Issue title string
#
# Returns: task ID on stdout (e.g., "GH-42"), or empty if no match
github_issue_parse_task_id() {
    local title="$1"

    # Extract task ID from brackets in title
    # Handles: [GH-42], **[GH-42]**, **[FEAT-7]**
    local task_id=""
    if [[ "$title" =~ \[([A-Za-z]{2,10}-[0-9]{1,4})\] ]]; then
        task_id="${BASH_REMATCH[1]}"
    fi

    echo "$task_id"
}

# Extract brief description from issue title (everything after the task ID)
#
# Args:
#   title - Issue title string
#
# Returns: brief description on stdout
github_issue_parse_brief() {
    local title="$1"

    # Remove task ID pattern (with optional bold wrapper) and trim
    local brief
    brief=$(echo "$title" | sed -E 's/\*?\*?\[([A-Za-z]{2,10}-[0-9]{1,4})\]\*?\*?//' | \
            sed 's/^[[:space:]]*//' | sed 's/[[:space:]]*$//')

    echo "$brief"
}

# =============================================================================
# Issue Body Parsing
# =============================================================================

# Table-driven inline field names (case-insensitive)
_ISSUE_INLINE_FIELDS="priority|complexity|dependencies"

# Section heading names (case-insensitive)
_ISSUE_SECTION_FIELDS="scope|out of scope|acceptance criteria"

# Parse all structured fields from issue body into a temp directory
#
# Uses awk to write each field to a separate file, avoiding newline
# issues with TSV transport of multi-line content.
#
# Args:
#   body    - Issue body text
#   out_dir - Directory to write field files into
#
# Writes files: description, priority, complexity, dependencies,
#               scope, out_of_scope, acceptance_criteria
_github_issue_parse_body_to_files() {
    local body="$1"
    local out_dir="$2"

    echo "$body" | awk -v out_dir="$out_dir" '
    BEGIN {
        current_section = ""
        pending_field = ""   # single-value heading field awaiting next non-blank line
        past_preamble = 0    # set once any heading is seen; prevents unrecognized
                             # section content (e.g. ## Checklist) leaking into description
    }

    # Skip title heading produced by extract_task (e.g., "# Task: OPT-004 - ...")
    /^#[[:space:]]+[Tt]ask:/ { past_preamble = 1; next }

    # Inline fields: "Priority: HIGH" (case-insensitive)
    /^[Pp]riority[[:space:]]*:/ {
        sub(/^[Pp]riority[[:space:]]*:[[:space:]]*/, "")
        gsub(/^[[:space:]]+|[[:space:]]+$/, "")
        print toupper($0) > out_dir "/priority"
        current_section = ""; pending_field = ""
        next
    }
    /^[Cc]omplexity[[:space:]]*:/ {
        sub(/^[Cc]omplexity[[:space:]]*:[[:space:]]*/, "")
        gsub(/^[[:space:]]+|[[:space:]]+$/, "")
        print toupper($0) > out_dir "/complexity"
        current_section = ""; pending_field = ""
        next
    }
    /^[Dd]ependencies[[:space:]]*:/ {
        sub(/^[Dd]ependencies[[:space:]]*:[[:space:]]*/, "")
        gsub(/^[[:space:]]+|[[:space:]]+$/, "")
        print > out_dir "/dependencies"
        current_section = ""; pending_field = ""
        next
    }

    # Heading-based single-value fields: "## Priority" then value on next line
    /^#{2,3}[[:space:]]+[Pp]riority[[:space:]]*$/ {
        current_section = ""; pending_field = "priority"; past_preamble = 1
        next
    }
    /^#{2,3}[[:space:]]+[Cc]omplexity[[:space:]]*$/ {
        current_section = ""; pending_field = "complexity"; past_preamble = 1
        next
    }
    /^#{2,3}[[:space:]]+[Dd]ependencies[[:space:]]*$/ {
        current_section = ""; pending_field = "dependencies"; past_preamble = 1
        next
    }

    # Heading-based multi-line sections
    /^#{2,3}[[:space:]]+[Dd]escription[[:space:]]*$/ {
        current_section = "description"; pending_field = ""; past_preamble = 1
        next
    }
    /^#{2,3}[[:space:]]+[Ss]cope[[:space:]]*$/ {
        current_section = "scope"; pending_field = ""; past_preamble = 1
        next
    }
    /^#{2,3}[[:space:]]+[Oo]ut [Oo]f [Ss]cope[[:space:]]*$/ {
        current_section = "out_of_scope"; pending_field = ""; past_preamble = 1
        next
    }
    /^#{2,3}[[:space:]]+[Aa]cceptance [Cc]riteria[[:space:]]*$/ {
        current_section = "acceptance_criteria"; pending_field = ""; past_preamble = 1
        next
    }

    # Any other heading resets state (content is discarded, not dumped to description)
    /^#{1,6}[[:space:]]/ {
        current_section = ""; pending_field = ""; past_preamble = 1
        next
    }

    # Accumulate content
    {
        # Capture single-value heading field (first non-blank line after heading)
        if (pending_field != "") {
            if ($0 !~ /^[[:space:]]*$/) {
                val = $0
                gsub(/^[[:space:]]+|[[:space:]]+$/, "", val)
                if (pending_field == "priority" || pending_field == "complexity") {
                    print toupper(val) > out_dir "/" pending_field
                } else {
                    print val > out_dir "/" pending_field
                }
                pending_field = ""
            }
            next
        }

        if (current_section != "") {
            print >> out_dir "/" current_section
        } else if (!past_preamble) {
            print >> out_dir "/description"
        }
        # else: discard (content under unrecognized heading like ## Checklist)
    }
    '
}

# Parse issue body and return a JSON object with all fields
#
# This is the main entry point for body parsing. Returns a clean JSON object.
# Uses temp directory for multi-line field handling.
#
# Args:
#   body - Issue body text
#
# Returns: JSON object on stdout
github_issue_parse_body_json() {
    local body="$1"

    local tmp_dir
    tmp_dir=$(mktemp -d /tmp/wiggum-parse-XXXXXX)

    _github_issue_parse_body_to_files "$body" "$tmp_dir"

    # Read fields from files (trim leading/trailing blank lines)
    local description="" priority="" complexity="" dependencies=""
    local scope="" out_of_scope="" acceptance_criteria=""

    [ -f "$tmp_dir/description" ] && description=$(sed '/./,$!d' "$tmp_dir/description" | sed -e :a -e '/^[[:space:]]*$/{ $d; N; ba; }')
    [ -f "$tmp_dir/priority" ] && priority=$(cat "$tmp_dir/priority")
    [ -f "$tmp_dir/complexity" ] && complexity=$(cat "$tmp_dir/complexity")
    [ -f "$tmp_dir/dependencies" ] && dependencies=$(cat "$tmp_dir/dependencies")
    [ -f "$tmp_dir/scope" ] && scope=$(sed '/./,$!d' "$tmp_dir/scope" | sed -e :a -e '/^[[:space:]]*$/{ $d; N; ba; }')
    [ -f "$tmp_dir/out_of_scope" ] && out_of_scope=$(sed '/./,$!d' "$tmp_dir/out_of_scope" | sed -e :a -e '/^[[:space:]]*$/{ $d; N; ba; }')
    [ -f "$tmp_dir/acceptance_criteria" ] && acceptance_criteria=$(sed '/./,$!d' "$tmp_dir/acceptance_criteria" | sed -e :a -e '/^[[:space:]]*$/{ $d; N; ba; }')

    safe_path "$tmp_dir" "tmp_dir" || return 1
    rm -rf "$tmp_dir"

    jq -n \
        --arg desc "${description:-}" \
        --arg pri "${priority:-}" \
        --arg comp "${complexity:-}" \
        --arg deps "${dependencies:-}" \
        --arg scope "${scope:-}" \
        --arg oos "${out_of_scope:-}" \
        --arg ac "${acceptance_criteria:-}" \
        '{
            description: $desc,
            priority: $pri,
            complexity: $comp,
            dependencies: $deps,
            scope: $scope,
            out_of_scope: $oos,
            acceptance_criteria: $ac
        }'
}

# Validate dependency references
#
# Filters dependency list to only valid task ID references.
#
# Args:
#   deps_string - Comma-separated dependency string (e.g., "GH-10, GH-15, invalid")
#
# Returns: cleaned dependency string on stdout (e.g., "GH-10, GH-15")
github_issue_validate_deps() {
    local deps_string="$1"

    # Handle "none" or empty
    if [ -z "$deps_string" ] || [[ "${deps_string,,}" == "none" ]]; then
        echo "none"
        return 0
    fi

    local valid_deps=""
    local IFS=','
    local dep
    for dep in $deps_string; do
        # Trim whitespace
        dep=$(echo "$dep" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')
        # Validate against task ID regex
        if [[ "$dep" =~ ^[A-Za-z]{2,10}-[0-9]{1,4}$ ]]; then
            if [ -n "$valid_deps" ]; then
                valid_deps="$valid_deps, $dep"
            else
                valid_deps="$dep"
            fi
        fi
    done

    if [ -z "$valid_deps" ]; then
        echo "none"
    else
        echo "$valid_deps"
    fi
}

# Parse a full GitHub issue JSON into kanban-ready fields
#
# This is the top-level entry point. Takes a single issue JSON object
# (as returned by gh issue list --json) and returns all kanban fields.
#
# Args:
#   issue_json - JSON object with: number, title, body, labels, author, state, updatedAt
#
# Returns: JSON object on stdout with all parsed fields, or empty on skip
github_issue_parse() {
    local issue_json="$1"

    # Extract basic fields via jq
    local number title body updated_at state author_id author_login labels_json
    number=$(echo "$issue_json" | jq -r '.number')
    title=$(echo "$issue_json" | jq -r '.title // ""')
    body=$(echo "$issue_json" | jq -r '.body // ""')
    updated_at=$(echo "$issue_json" | jq -r '.updatedAt // ""')
    state=$(echo "$issue_json" | jq -r '.state // "OPEN"' | tr '[:upper:]' '[:lower:]')

    # Author: gh returns .author.login and .author.id
    author_login=$(echo "$issue_json" | jq -r '.author.login // ""')
    author_id=$(echo "$issue_json" | jq -r '.author.id // ""')

    labels_json=$(echo "$issue_json" | jq '.labels // []')

    # Parse task ID from title
    local task_id
    task_id=$(github_issue_parse_task_id "$title")
    if [ -z "$task_id" ]; then
        return 1  # No valid task ID — skip
    fi

    # Parse brief description from title
    local brief
    brief=$(github_issue_parse_brief "$title")

    # Parse body fields
    local body_fields
    body_fields=$(github_issue_parse_body_json "$body")

    local description priority complexity dependencies
    local scope out_of_scope acceptance_criteria
    description=$(echo "$body_fields" | jq -r '.description // ""')
    priority=$(echo "$body_fields" | jq -r '.priority // ""')
    complexity=$(echo "$body_fields" | jq -r '.complexity // ""')
    dependencies=$(echo "$body_fields" | jq -r '.dependencies // ""')
    scope=$(echo "$body_fields" | jq -r '.scope // ""')
    out_of_scope=$(echo "$body_fields" | jq -r '.out_of_scope // ""')
    acceptance_criteria=$(echo "$body_fields" | jq -r '.acceptance_criteria // ""')

    # Validate dependencies
    dependencies=$(github_issue_validate_deps "$dependencies")

    # Build result JSON
    jq -n \
        --arg number "$number" \
        --arg task_id "$task_id" \
        --arg brief "$brief" \
        --arg description "$description" \
        --arg priority "$priority" \
        --arg complexity "$complexity" \
        --arg dependencies "$dependencies" \
        --arg scope "$scope" \
        --arg out_of_scope "$out_of_scope" \
        --arg acceptance_criteria "$acceptance_criteria" \
        --arg updated_at "$updated_at" \
        --arg state "$state" \
        --arg author_login "$author_login" \
        --arg author_id "$author_id" \
        --argjson labels "$labels_json" \
        '{
            number: ($number | tonumber),
            task_id: $task_id,
            brief: $brief,
            description: $description,
            priority: $priority,
            complexity: $complexity,
            dependencies: $dependencies,
            scope: $scope,
            out_of_scope: $out_of_scope,
            acceptance_criteria: $acceptance_criteria,
            updated_at: $updated_at,
            state: $state,
            author_login: $author_login,
            author_id: $author_id,
            labels: $labels
        }'
}
