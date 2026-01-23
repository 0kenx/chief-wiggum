#!/usr/bin/env bash
# Task parser for markdown kanban and PRD files
set -euo pipefail

has_incomplete_tasks() {
    local file="$1"
    grep -q -- '- \[ \]' "$file"
}

get_prd_status() {
    local file="$1"

    # Check for failed tasks first
    if grep -q -- '- \[\*\]' "$file"; then
        echo "FAILED"
        return
    fi

    # Check for incomplete tasks
    if grep -q -- '- \[ \]' "$file"; then
        echo "INCOMPLETE"
        return
    fi

    # All tasks must be complete
    echo "COMPLETE"
}

get_todo_tasks() {
    local kanban="$1"
    # Extract task IDs - ONLY incomplete tasks (- [ ]) matching the task format
    awk '/^- \[ \] \*\*\[[A-Za-z]{2,8}-[0-9]+\]\*\*/{
            match($0, /\[[A-Za-z]{2,8}-[0-9]+\]/)
            print substr($0, RSTART+1, RLENGTH-2)
        }' "$kanban"
}

get_failed_tasks() {
    local kanban="$1"
    # Extract task IDs - ONLY failed tasks (- [*]) matching the task format
    awk '/^- \[\*\] \*\*\[[A-Za-z]{2,8}-[0-9]+\]\*\*/{
            match($0, /\[[A-Za-z]{2,8}-[0-9]+\]/)
            print substr($0, RSTART+1, RLENGTH-2)
        }' "$kanban"
}

get_pending_approval_tasks() {
    local kanban="$1"
    # Extract task IDs - ONLY pending approval tasks (- [P]) matching the task format
    awk '/^- \[P\] \*\*\[[A-Za-z]{2,8}-[0-9]+\]\*\*/{
            match($0, /\[[A-Za-z]{2,8}-[0-9]+\]/)
            print substr($0, RSTART+1, RLENGTH-2)
        }' "$kanban"
}

get_completed_tasks() {
    local kanban="$1"
    # Extract task IDs - ONLY completed/merged tasks (- [x]) matching the task format
    awk '/^- \[x\] \*\*\[[A-Za-z]{2,8}-[0-9]+\]\*\*/{
            match($0, /\[[A-Za-z]{2,8}-[0-9]+\]/)
            print substr($0, RSTART+1, RLENGTH-2)
        }' "$kanban"
}

# Get all tasks (any status) with their metadata
# Output format: task_id|status|priority|dependencies
get_all_tasks_with_metadata() {
    local kanban="$1"
    awk '
        /^- \[.\] \*\*\[[A-Za-z]{2,8}-[0-9]+\]\*\*/ {
            # Extract status
            match($0, /\[.\]/)
            status = substr($0, RSTART+1, 1)

            # Extract task ID
            match($0, /\*\*\[[A-Za-z]{2,8}-[0-9]+\]\*\*/)
            task_id = substr($0, RSTART+3, RLENGTH-6)

            current_task = task_id
            tasks[task_id] = status
            priority[task_id] = "MEDIUM"  # default
            deps[task_id] = ""
            next
        }
        current_task && /^  - Priority:/ {
            sub(/^  - Priority: */, "")
            gsub(/[[:space:]]+$/, "")
            priority[current_task] = $0
            next
        }
        current_task && /^  - Dependencies:/ {
            sub(/^  - Dependencies: */, "")
            gsub(/[[:space:]]+$/, "")
            if ($0 != "none" && $0 != "None" && $0 != "") {
                deps[current_task] = $0
            }
            next
        }
        current_task && /^- \[/ {
            current_task = ""
        }
        current_task && /^## / {
            current_task = ""
        }
        END {
            for (t in tasks) {
                print t "|" tasks[t] "|" priority[t] "|" deps[t]
            }
        }
    ' "$kanban"
}

# Get task dependencies as "task_id:dep1,dep2,dep3" lines
get_task_dependencies() {
    local kanban="$1"
    local task_id="$2"

    get_all_tasks_with_metadata "$kanban" | awk -F'|' -v task="$task_id" '
        $1 == task { print $4 }
    '
}

# Get task priority (HIGH, MEDIUM, LOW)
get_task_priority() {
    local kanban="$1"
    local task_id="$2"

    get_all_tasks_with_metadata "$kanban" | awk -F'|' -v task="$task_id" '
        $1 == task { print $3 }
    '
}

# Get task status character (space, =, x, *)
get_task_status() {
    local kanban="$1"
    local task_id="$2"

    get_all_tasks_with_metadata "$kanban" | awk -F'|' -v task="$task_id" '
        $1 == task { print $2 }
    '
}

# Check if a task's dependencies are satisfied (all deps merged/complete)
# Returns 0 if satisfied, 1 if not
# Note: Dependencies must be complete [x] (merged), not just pending approval [P]
are_dependencies_satisfied() {
    local kanban="$1"
    local task_id="$2"

    local deps
    deps=$(get_task_dependencies "$kanban" "$task_id")

    # No dependencies = satisfied
    if [ -z "$deps" ]; then
        return 0
    fi

    # Parse comma-separated dependencies
    local all_metadata
    all_metadata=$(get_all_tasks_with_metadata "$kanban")

    # Check each dependency using parameter expansion to avoid IFS issues
    local dep
    local dep_status
    local remaining="$deps"
    while [ -n "$remaining" ]; do
        # Extract first dependency (before comma)
        dep="${remaining%%,*}"
        # Remove processed dependency from remaining
        if [ "$dep" = "$remaining" ]; then
            remaining=""
        else
            remaining="${remaining#*,}"
        fi
        # Trim whitespace
        dep=$(echo "$dep" | xargs)
        [ -z "$dep" ] && continue

        # Get status of dependency
        dep_status=$(echo "$all_metadata" | awk -F'|' -v d="$dep" '$1 == d { print $2 }')

        # If dependency is not complete/merged (x), then not satisfied
        if [ "$dep_status" != "x" ]; then
            return 1
        fi
    done

    return 0
}

# Count transitively dependent tasks (tasks blocked by this one, directly or indirectly)
# BFS through reverse dependency graph
# Args: kanban_file task_id
# Returns: count of all transitive dependents
get_dependency_depth() {
    local kanban="$1"
    local target_task="$2"

    local all_metadata
    all_metadata=$(get_all_tasks_with_metadata "$kanban")

    # Build reverse dependency map: for each task, find who depends on it
    # Format: task_id -> list of tasks that have task_id as a dependency
    declare -A reverse_deps
    while IFS='|' read -r tid _status _priority deps; do
        [ -z "$tid" ] && continue
        [ -z "$deps" ] && continue
        # Parse comma-separated deps
        local remaining="$deps"
        while [ -n "$remaining" ]; do
            local dep="${remaining%%,*}"
            if [ "$dep" = "$remaining" ]; then
                remaining=""
            else
                remaining="${remaining#*,}"
            fi
            dep=$(echo "$dep" | xargs)
            [ -z "$dep" ] && continue
            reverse_deps[$dep]="${reverse_deps[$dep]:-} $tid"
        done
    done <<< "$all_metadata"

    # BFS from target_task through reverse_deps
    local -A visited
    local queue=("$target_task")
    visited[$target_task]=1
    local count=0

    while [ ${#queue[@]} -gt 0 ]; do
        local current="${queue[0]}"
        queue=("${queue[@]:1}")

        for neighbor in ${reverse_deps[$current]:-}; do
            if [ -z "${visited[$neighbor]+x}" ]; then
                visited[$neighbor]=1
                ((++count))
                queue+=("$neighbor")
            fi
        done
    done

    echo "$count"
}

# Compute effective priority with aging
# Args: base_priority (HIGH|MEDIUM|LOW), iterations_waiting, aging_factor
# Returns: numeric priority (lower = higher priority), floored at 0
get_effective_priority() {
    local base_priority="$1"
    local iterations_waiting="${2:-0}"
    local aging_factor="${3:-10}"

    local numeric
    case "$base_priority" in
        HIGH)   numeric=1 ;;
        MEDIUM) numeric=2 ;;
        LOW)    numeric=3 ;;
        *)      numeric=2 ;;
    esac

    # Subtract aging bonus (integer division)
    if [ "$aging_factor" -gt 0 ] && [ "$iterations_waiting" -gt 0 ]; then
        local aging_bonus=$(( iterations_waiting / aging_factor ))
        numeric=$(( numeric - aging_bonus ))
    fi

    # Floor at 0
    if [ "$numeric" -lt 0 ]; then
        numeric=0
    fi

    echo "$numeric"
}

# Get tasks that are ready to run (pending, with satisfied dependencies)
# Sorted by priority: HIGH > MEDIUM > LOW
# Optional args: ready_since_file aging_factor
get_ready_tasks() {
    local kanban="$1"
    local ready_since_file="${2:-}"
    local aging_factor="${3:-10}"

    local all_metadata
    all_metadata=$(get_all_tasks_with_metadata "$kanban")

    # Get all pending tasks (status = space)
    local pending_tasks
    pending_tasks=$(echo "$all_metadata" | awk -F'|' '$2 == " " { print $1 }')

    # Filter to tasks with satisfied dependencies and sort by priority
    for task_id in $pending_tasks; do
        if are_dependencies_satisfied "$kanban" "$task_id"; then
            local priority
            priority=$(echo "$all_metadata" | awk -F'|' -v t="$task_id" '$1 == t { print $3 }')

            local effective_pri
            if [ -n "$ready_since_file" ] && [ -f "$ready_since_file" ]; then
                # Look up iterations waiting from ready-since file
                local iters_waiting
                iters_waiting=$(awk -F'|' -v t="$task_id" '$1 == t { print $2 }' "$ready_since_file")
                iters_waiting=${iters_waiting:-0}
                effective_pri=$(get_effective_priority "$priority" "$iters_waiting" "$aging_factor")
            else
                # No aging - use static priority
                case "$priority" in
                    HIGH)   effective_pri=1 ;;
                    MEDIUM) effective_pri=2 ;;
                    LOW)    effective_pri=3 ;;
                    *)      effective_pri=2 ;;
                esac
            fi

            # Compute dependency depth for tiebreaking (higher depth = higher priority)
            local dep_depth
            dep_depth=$(get_dependency_depth "$kanban" "$task_id")
            # Invert depth for ascending sort (subtract from large number)
            local inverted_depth=$(( 9999 - dep_depth ))

            echo "$effective_pri|$inverted_depth|$task_id"
        fi
    done | sort -t'|' -k1,1n -k2,2n | cut -d'|' -f3
}

# Get blocked tasks (pending but dependencies not satisfied)
get_blocked_tasks() {
    local kanban="$1"

    local all_metadata
    all_metadata=$(get_all_tasks_with_metadata "$kanban")

    # Get all pending tasks
    local pending_tasks
    pending_tasks=$(echo "$all_metadata" | awk -F'|' '$2 == " " { print $1 }')

    for task_id in $pending_tasks; do
        if ! are_dependencies_satisfied "$kanban" "$task_id"; then
            echo "$task_id"
        fi
    done
}

# Get unsatisfied dependencies for a task
get_unsatisfied_dependencies() {
    local kanban="$1"
    local task_id="$2"

    local deps
    deps=$(get_task_dependencies "$kanban" "$task_id")

    if [ -z "$deps" ]; then
        return
    fi

    local all_metadata
    all_metadata=$(get_all_tasks_with_metadata "$kanban")

    # Parse using parameter expansion to avoid IFS issues
    local dep
    local dep_status
    local remaining="$deps"
    while [ -n "$remaining" ]; do
        dep="${remaining%%,*}"
        if [ "$dep" = "$remaining" ]; then
            remaining=""
        else
            remaining="${remaining#*,}"
        fi
        dep=$(echo "$dep" | xargs)
        [ -z "$dep" ] && continue

        dep_status=$(echo "$all_metadata" | awk -F'|' -v d="$dep" '$1 == d { print $2 }')

        if [ "$dep_status" != "x" ]; then
            echo "$dep"
        fi
    done
}

# Detect circular dependencies
# Returns 0 if no cycles, 1 if cycles detected (prints cycle path)
detect_circular_dependencies() {
    local kanban="$1"

    local all_metadata
    all_metadata=$(get_all_tasks_with_metadata "$kanban")

    local tasks
    tasks=$(echo "$all_metadata" | cut -d'|' -f1)

    # Create temp files for cycle detection
    local visited_file stack_file cycle_file
    visited_file=$(mktemp)
    stack_file=$(mktemp)
    cycle_file=$(mktemp)

    # Cleanup function
    _cleanup_cycle_files() {
        rm -f "$visited_file" "$stack_file" "$cycle_file"
    }

    # DFS using iterative approach with explicit stack to avoid subshell issues
    # We use a simple Kahn's algorithm approach instead
    local -A in_degree
    local -A adj_list

    # Initialize
    for task_id in $tasks; do
        in_degree[$task_id]=0
        adj_list[$task_id]=""
    done

    # Build graph
    for task_id in $tasks; do
        local deps
        deps=$(echo "$all_metadata" | awk -F'|' -v t="$task_id" '$1 == t { print $4 }')
        if [ -n "$deps" ]; then
            # Parse using parameter expansion to avoid IFS issues
            local dep
            local remaining="$deps"
            while [ -n "$remaining" ]; do
                dep="${remaining%%,*}"
                if [ "$dep" = "$remaining" ]; then
                    remaining=""
                else
                    remaining="${remaining#*,}"
                fi
                dep=$(echo "$dep" | xargs)
                [ -z "$dep" ] && continue
                # task_id depends on dep, so edge is dep -> task_id
                if [ -n "${in_degree[$dep]+x}" ]; then
                    adj_list[$dep]="${adj_list[$dep]} $task_id"
                    ((++in_degree[$task_id]))
                fi
            done
        fi
    done

    # Kahn's algorithm - if we can't visit all nodes, there's a cycle
    local queue=()
    local visited_count=0
    local total_count=0

    for task_id in $tasks; do
        ((++total_count))
        if [ "${in_degree[$task_id]}" -eq 0 ]; then
            queue+=("$task_id")
        fi
    done

    while [ ${#queue[@]} -gt 0 ]; do
        local node="${queue[0]}"
        queue=("${queue[@]:1}")
        ((++visited_count))

        for neighbor in ${adj_list[$node]}; do
            ((in_degree[$neighbor]--)) || true
            if [ "${in_degree[$neighbor]}" -eq 0 ]; then
                queue+=("$neighbor")
            fi
        done
    done

    _cleanup_cycle_files

    if [ "$visited_count" -ne "$total_count" ]; then
        # Find tasks that are part of the cycle
        local cycle_tasks=""
        for task_id in $tasks; do
            if [ "${in_degree[$task_id]}" -gt 0 ]; then
                cycle_tasks="$cycle_tasks $task_id"
            fi
        done
        echo "Circular dependency involving:$cycle_tasks"
        return 1
    fi

    return 0
}

# Resolve a partial task ID to full task ID from kanban
# Args: <kanban_file> <partial_id>
# Returns: full task ID on stdout, or error message on stderr
# Exit: 0 on exact match, 1 on no match or multiple matches
resolve_task_id() {
    local kanban="$1"
    local partial="$2"
    local matches=()

    if [ ! -f "$kanban" ]; then
        echo "Error: No kanban file found at $kanban" >&2
        return 1
    fi

    # Get all task IDs from kanban
    local all_tasks
    all_tasks=$(get_all_tasks_with_metadata "$kanban" | cut -d'|' -f1)

    for task_id in $all_tasks; do
        # Check if partial matches any part of task_id (case insensitive)
        if [[ "${task_id^^}" == *"${partial^^}"* ]]; then
            matches+=("$task_id")
        fi
    done

    case ${#matches[@]} in
        0)
            echo "Error: No task matches '$partial'" >&2
            echo "Check .ralph/kanban.md for available tasks." >&2
            return 1
            ;;
        1)
            echo "${matches[0]}"
            return 0
            ;;
        *)
            echo "Error: Multiple tasks match '$partial':" >&2
            for m in "${matches[@]}"; do
                echo "  - $m" >&2
            done
            echo "Please be more specific." >&2
            return 1
            ;;
    esac
}

extract_task() {
    local task_id="$1"
    local kanban="$2"

    # Extract task title from the first line matching the task ID
    local task_title
    task_title=$(awk -v task="$task_id" '
        $0 ~ "\\*\\*\\[" task "\\]\\*\\*" {
            # Extract everything after **[TASK-ID]**
            sub(/.*\*\*\[[A-Za-z]{2,8}-[0-9]+\]\*\* */, "")
            print
            exit
        }' "$kanban")

    # Extract task details and create a PRD for worker
    cat <<EOF
# Task: $task_id${task_title:+ - $task_title}

$(awk -v task="$task_id" '
    /\*\*\['"$task_id"'\]\*\*/ {found=1; next}
    found && /^  - Description:/ {sub(/^  - Description: /, ""); desc=$0; next}
    found && /^  - Priority:/ {sub(/^  - Priority: /, ""); priority=$0; next}
    found && /^  - Dependencies:/ {sub(/^  - Dependencies: /, ""); deps=$0; next}
    found && /^  - Scope:?/ {in_scope=1; in_oos=0; in_ac=0; next}
    found && /^  - Out of Scope:?/ {in_scope=0; in_oos=1; in_ac=0; next}
    found && /^  - Acceptance Criteria:?/ {in_scope=0; in_oos=0; in_ac=1; next}
    found && in_scope && /^    - / {
        sub(/^    - /, "");
        scope[++scope_count] = $0
        next
    }
    found && in_oos && /^    - / {
        sub(/^    - /, "");
        oos[++oos_count] = $0
        next
    }
    found && in_ac && /^    - / {
        sub(/^    - /, "");
        ac[++ac_count] = $0
        next
    }
    found && /^  - / && !/^  - (Description|Priority|Dependencies|Scope|Out of Scope|Acceptance Criteria):?/ {
        in_scope=0; in_oos=0; in_ac=0
    }
    found && /^- \[/ {exit}
    found && /^## / {exit}
    END {
        if (desc) print "## Description\n" desc "\n"
        if (priority) print "## Priority\n" priority "\n"
        if (deps && deps != "none") print "## Dependencies\n" deps "\n"

        # Output Scope items (what to do)
        if (scope_count > 0) {
            print "## Scope\n"
            for (i = 1; i <= scope_count; i++) {
                print "- " scope[i]
            }
            print ""
        }

        # Output Out of Scope items (what NOT to do)
        if (oos_count > 0) {
            print "## Out of Scope\n"
            for (i = 1; i <= oos_count; i++) {
                print "- " oos[i]
            }
            print ""
        }

        # Output Acceptance Criteria for validation reference
        if (ac_count > 0) {
            print "## Acceptance Criteria\n"
            for (i = 1; i <= ac_count; i++) {
                print "- " ac[i]
            }
            print ""
        }

        # Output Scope as the working checklist
        print "## Checklist\n"
        if (scope_count > 0) {
            for (i = 1; i <= scope_count; i++) {
                print "- [ ] " scope[i]
            }
        } else {
            print "- [ ] Complete the task as described"
            print "- [ ] Test the implementation"
        }
        print "- [ ] Mark this PRD as complete"
    }
' "$kanban")
EOF
}
