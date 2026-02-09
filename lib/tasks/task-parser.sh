#!/usr/bin/env bash
# Task parser for markdown kanban and PRD files
set -euo pipefail

# =============================================================================
# KANBAN METADATA CACHING
# =============================================================================
# Session-scoped cache with mtime invalidation to avoid O(n²) behavior
# when get_all_tasks_with_metadata() is called per-task.

_KANBAN_CACHE=""
_KANBAN_CACHE_FILE=""
_KANBAN_CACHE_MTIME=""

# Get cached metadata, refreshing if file changed
#
# Args:
#   kanban - Path to kanban file
#
# Returns: Cached metadata output (task_id|status|priority|dependencies)
_get_cached_metadata() {
    local kanban="$1"

    # Get current file mtime
    local current_mtime
    current_mtime=$(stat -c %Y "$kanban" 2>/dev/null || stat -f %m "$kanban" 2>/dev/null || echo "0")

    # Check if cache is valid (same file and same mtime)
    if [ "$_KANBAN_CACHE_FILE" = "$kanban" ] && [ "$_KANBAN_CACHE_MTIME" = "$current_mtime" ] && [ -n "$_KANBAN_CACHE" ]; then
        echo "$_KANBAN_CACHE"
        return 0
    fi

    # Cache miss - refresh
    _KANBAN_CACHE=$(get_all_tasks_with_metadata "$kanban")
    _KANBAN_CACHE_FILE="$kanban"
    _KANBAN_CACHE_MTIME="$current_mtime"

    echo "$_KANBAN_CACHE"
}

# Validate task ID matches expected format: [A-Za-z]{2,10}-[0-9]{1,4}
# This prevents regex/awk injection when task IDs are used in grep -E or awk patterns.
#
# Args:
#   task_id - Task ID to validate
#
# Returns: 0 if valid, 1 if invalid
_validate_task_id() {
    local task_id="$1"
    [[ "$task_id" =~ ^[A-Za-z]{2,10}-[0-9]{1,4}$ ]]
}

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
    awk '/^- \[ \] \*\*\[[A-Za-z]{2,10}-[0-9]{1,4}\]\*\*/{
            match($0, /\[[A-Za-z]{2,10}-[0-9]{1,4}\]/)
            print substr($0, RSTART+1, RLENGTH-2)
        }' "$kanban"
}

get_failed_tasks() {
    local kanban="$1"
    # Extract task IDs - ONLY failed tasks (- [*]) matching the task format
    awk '/^- \[\*\] \*\*\[[A-Za-z]{2,10}-[0-9]{1,4}\]\*\*/{
            match($0, /\[[A-Za-z]{2,10}-[0-9]{1,4}\]/)
            print substr($0, RSTART+1, RLENGTH-2)
        }' "$kanban"
}

get_in_progress_tasks() {
    local kanban="$1"
    # Extract task IDs - ONLY in-progress tasks (- [=]) matching the task format
    awk '/^- \[=\] \*\*\[[A-Za-z]{2,10}-[0-9]{1,4}\]\*\*/{
            match($0, /\[[A-Za-z]{2,10}-[0-9]{1,4}\]/)
            print substr($0, RSTART+1, RLENGTH-2)
        }' "$kanban"
}

get_pending_approval_tasks() {
    local kanban="$1"
    # Extract task IDs - ONLY pending approval tasks (- [P]) matching the task format
    awk '/^- \[P\] \*\*\[[A-Za-z]{2,10}-[0-9]{1,4}\]\*\*/{
            match($0, /\[[A-Za-z]{2,10}-[0-9]{1,4}\]/)
            print substr($0, RSTART+1, RLENGTH-2)
        }' "$kanban"
}

get_completed_tasks() {
    local kanban="$1"
    # Extract task IDs - ONLY completed/merged tasks (- [x]) matching the task format
    awk '/^- \[x\] \*\*\[[A-Za-z]{2,10}-[0-9]{1,4}\]\*\*/{
            match($0, /\[[A-Za-z]{2,10}-[0-9]{1,4}\]/)
            print substr($0, RSTART+1, RLENGTH-2)
        }' "$kanban"
}

# Get all tasks (any status) with their metadata
# Output format: task_id|status|priority|dependencies
get_all_tasks_with_metadata() {
    local kanban="$1"
    awk '
        /^- \[.\] \*\*\[[A-Za-z]{2,10}-[0-9]{1,4}\]\*\*/ {
            # Extract status
            match($0, /\[.\]/)
            status = substr($0, RSTART+1, 1)

            # Extract task ID
            match($0, /\*\*\[[A-Za-z]{2,10}-[0-9]{1,4}\]\*\*/)
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

    _get_cached_metadata "$kanban" | awk -F'|' -v task="$task_id" '
        $1 == task { print $4 }
    '
}

# Get task priority (HIGH, MEDIUM, LOW)
get_task_priority() {
    local kanban="$1"
    local task_id="$2"

    _get_cached_metadata "$kanban" | awk -F'|' -v task="$task_id" '
        $1 == task { print $3 }
    '
}

# Check if a task is listed in the done comment
# The done comment format: <!-- done: TASK-001, TASK-002, ... -->
#
# Args:
#   kanban  - Path to kanban file
#   task_id - Task ID to check
#
# Returns: 0 if in done comment, 1 if not
is_task_in_done_comment() {
    local kanban="$1"
    local task_id="$2"

    # Validate task_id to prevent regex injection in grep -E
    _validate_task_id "$task_id" || return 1

    # Look for task ID in done comment (comma or space separated, word boundaries)
    grep -qE "^<!-- done:.*[, ]${task_id}([, ]|$)" "$kanban" 2>/dev/null
}

# Get task status character (space, =, x, *, P, N)
# Returns "x" for tasks in the done comment (archived completed tasks)
get_task_status() {
    local kanban="$1"
    local task_id="$2"

    # First check the metadata cache for active task lines
    local _task_status
    _task_status=$(_get_cached_metadata "$kanban" | awk -F'|' -v task="$task_id" '
        $1 == task { print $2 }
    ')

    if [ -n "$_task_status" ]; then
        echo "$_task_status"
        return
    fi

    # Task not found in active lines - check done comment
    if is_task_in_done_comment "$kanban" "$task_id"; then
        echo "x"
        return
    fi

    # Task truly doesn't exist - return empty
    echo ""
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
    all_metadata=$(_get_cached_metadata "$kanban")

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

# Build reverse dependency graph from metadata
# Serializes the graph as pipe-delimited text for reuse across multiple BFS calls.
#
# Args:
#   all_metadata - Output from _get_cached_metadata (task_id|status|priority|deps lines)
#
# Returns: Serialized reverse dep graph (one line per node: task_id|dependent1 dependent2 ...)
_build_reverse_dep_graph() {
    local all_metadata="$1"

    local -A reverse_deps=()
    while IFS='|' read -r tid _status _priority deps; do
        [ -z "$tid" ] && continue
        [ -z "$deps" ] && continue
        local remaining="$deps"
        while [ -n "$remaining" ]; do
            local dep="${remaining%%,*}"
            if [ "$dep" = "$remaining" ]; then
                remaining=""
            else
                remaining="${remaining#*,}"
            fi
            # Trim whitespace using parameter expansion (no subprocess)
            dep="${dep#"${dep%%[![:space:]]*}"}"
            dep="${dep%"${dep##*[![:space:]]}"}"
            [ -z "$dep" ] && continue
            reverse_deps[$dep]="${reverse_deps[$dep]:-} $tid"
        done
    done <<< "$all_metadata"

    # Serialize: one line per node that has dependents
    local key
    for key in "${!reverse_deps[@]}"; do
        echo "$key|${reverse_deps[$key]}"
    done
}

# BFS count of transitive dependents from a pre-built serialized reverse dep graph
#
# Args:
#   graph_data  - Serialized graph from _build_reverse_dep_graph
#   target_task - Task ID to count dependents from
#
# Returns: Count of all transitive dependents
_bfs_count_from_graph() {
    local graph_data="$1"
    local target_task="$2"

    # Deserialize graph
    local -A reverse_deps=()
    if [ -n "$graph_data" ]; then
        while IFS='|' read -r key dependents; do
            [ -z "$key" ] && continue
            reverse_deps[$key]="$dependents"
        done <<< "$graph_data"
    fi

    # BFS from target_task through reverse_deps
    local -A visited
    local queue=("$target_task")
    visited[$target_task]=1
    local count=0

    # Security: Bound BFS depth to prevent runaway traversal on malformed graphs
    local max_depth=1000
    while [ ${#queue[@]} -gt 0 ]; do
        if [ "$count" -ge "$max_depth" ]; then
            log_warn "_bfs_count_from_graph: Depth limit ($max_depth) reached for $target_task"
            break
        fi
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

# Count transitively dependent tasks (tasks blocked by this one, directly or indirectly)
# BFS through reverse dependency graph
# Args: kanban_file task_id
# Returns: count of all transitive dependents
get_dependency_depth() {
    local kanban="$1"
    local target_task="$2"

    local all_metadata
    all_metadata=$(_get_cached_metadata "$kanban")

    local graph_data
    graph_data=$(_build_reverse_dep_graph "$all_metadata")

    _bfs_count_from_graph "$graph_data" "$target_task"
}

# Compute effective priority with aging (fixed-point arithmetic)
# Args: base_priority (CRITICAL|HIGH|MEDIUM|LOW), iterations_waiting, aging_factor
# Returns: fixed-point priority (lower = higher priority), floored at 0
# Scale: 10000 = 1.0000, so HIGH=10000, MEDIUM=20000, LOW=30000
get_effective_priority() {
    local base_priority="$1"
    local iterations_waiting="${2:-0}"
    local aging_factor="${3:-10}"

    local numeric
    case "$base_priority" in
        CRITICAL) numeric=0 ;;
        HIGH)     numeric=10000 ;;
        MEDIUM)   numeric=20000 ;;
        LOW)      numeric=30000 ;;
        *)        numeric=20000 ;;
    esac

    # Subtract aging bonus: -0.8 levels per aging_factor iterations = -8000 per cycle
    if [ "$aging_factor" -gt 0 ] && [ "$iterations_waiting" -gt 0 ]; then
        local aging_bonus=$(( (iterations_waiting * 8000) / aging_factor ))
        numeric=$(( numeric - aging_bonus ))
    fi

    # Floor at 0
    if [ "$numeric" -lt 0 ]; then
        numeric=0
    fi

    echo "$numeric"
}

# Extract task prefix from task ID (e.g., "CORTEX" from "CORTEX-001")
# Args: task_id
# Returns: prefix string
get_task_prefix() {
    local task_id="$1"
    echo "${task_id%-*}"
}

# Calculate sibling penalty based on number of active siblings (fixed-point)
# (in-progress, pending approval, or failed - anything except pending/complete/not-planned)
# Penalty scales with sqrt(N) where N is the count of active siblings
# Args: kanban_file task_id all_metadata base_penalty_fp (fixed-point, 10000=1.0)
# Returns: calculated penalty in fixed-point (0 if no active siblings)
get_sibling_penalty() {
    local task_id="$2"
    local all_metadata="$3"
    local base_penalty="${4:-20000}"  # Default 2.0 in fixed-point

    local prefix
    prefix=$(get_task_prefix "$task_id")

    # Count tasks with same prefix that have an active status and calculate sqrt penalty
    # "=" (in-progress), "P" (pending approval), "*" (failed)
    # Excludes: " " (pending), "x" (complete), "N" (not planned)
    echo "$all_metadata" | awk -F'|' -v prefix="$prefix" -v self="$task_id" -v base="$base_penalty" '
        BEGIN { count = 0 }
        $1 != self && ($2 == "=" || $2 == "P" || $2 == "*") {
            # Extract prefix from this task ID (remove trailing -NNN)
            task_prefix = $1
            sub(/-[0-9]+$/, "", task_prefix)
            if (task_prefix == prefix) {
                count++
            }
        }
        END {
            if (count > 0) {
                # Penalty = floor(sqrt(N) * base_penalty)
                # Result is in fixed-point (base is already fixed-point)
                print int(sqrt(count) * base)
            } else {
                print 0
            }
        }
    '
}

# Check if a task has an implementation plan
# Args: ralph_dir task_id
# Returns: 0 if plan exists, 1 otherwise
task_has_plan() {
    local ralph_dir="$1"
    local task_id="$2"
    local plan_file="$ralph_dir/plans/${task_id}.md"

    [ -f "$plan_file" ]
}

# Get tasks that are ready to run (pending, with satisfied dependencies)
# Sorted by priority: CRITICAL > HIGH > MEDIUM > LOW
# Uses fixed-point arithmetic (10000 = 1.0000)
# Optional args: ready_since_file aging_factor sibling_wip_penalty_fp ralph_dir plan_bonus_fp dep_bonus_fp _metadata
# When _metadata (8th param) is provided, uses it instead of calling _get_cached_metadata()
# and returns "effective_pri|task_id" lines; otherwise returns just task_id for backward compat.
get_ready_tasks() {
    local kanban="$1"
    local ready_since_file="${2:-}"
    local aging_factor="${3:-10}"
    local sibling_wip_penalty="${4:-20000}"  # 2.0 in fixed-point (penalty when sibling is WIP)
    local ralph_dir="${5:-}"                  # Optional: .ralph directory for plan lookup
    local plan_bonus="${6:-15000}"            # 1.5 in fixed-point (bonus for having a plan)
    local dep_bonus_per_task="${7:-7000}"     # 0.7 in fixed-point (bonus per task blocked)
    local _metadata="${8:-}"                  # Optional: pre-fetched metadata (avoids subshell cache loss)

    local all_metadata
    if [ -n "$_metadata" ]; then
        all_metadata="$_metadata"
    else
        all_metadata=$(_get_cached_metadata "$kanban")
    fi

    # Get all pending tasks (status = space)
    local pending_tasks
    pending_tasks=$(echo "$all_metadata" | awk -F'|' '$2 == " " { print $1 }')

    # Build reverse dependency graph ONCE for all tasks (avoids O(N^2) rebuild per task)
    local reverse_graph
    reverse_graph=$(_build_reverse_dep_graph "$all_metadata")

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
                # No aging - use static priority (fixed-point: 10000 = 1.0)
                case "$priority" in
                    CRITICAL) effective_pri=0 ;;
                    HIGH)     effective_pri=10000 ;;
                    MEDIUM)   effective_pri=20000 ;;
                    LOW)      effective_pri=30000 ;;
                    *)        effective_pri=20000 ;;
                esac
            fi

            # Apply penalty if sibling tasks (same prefix) are active
            # Penalty scales with sqrt(N) where N is count of active siblings
            # This discourages parallel work on related features that might conflict
            if [ "$sibling_wip_penalty" -gt 0 ]; then
                local penalty
                penalty=$(get_sibling_penalty "$kanban" "$task_id" "$all_metadata" "$sibling_wip_penalty")
                effective_pri=$(( effective_pri + penalty ))
            fi

            # Apply bonus if task has an implementation plan
            # Tasks with plans are more likely to succeed, so prioritize them
            if [ -n "$ralph_dir" ] && [ "$plan_bonus" -gt 0 ]; then
                if task_has_plan "$ralph_dir" "$task_id"; then
                    effective_pri=$(( effective_pri - plan_bonus ))
                fi
            fi

            # Apply dependency depth bonus (more tasks blocked = higher priority)
            # Each blocked task gives a bonus to prioritize unblocking work
            if [ "$dep_bonus_per_task" -gt 0 ]; then
                local dep_depth
                dep_depth=$(_bfs_count_from_graph "$reverse_graph" "$task_id")
                local dep_bonus=$(( dep_depth * dep_bonus_per_task ))
                effective_pri=$(( effective_pri - dep_bonus ))
            fi

            # Floor at 0
            if [ "$effective_pri" -lt 0 ]; then
                effective_pri=0
            fi

            echo "$effective_pri|$task_id"
        fi
    done | LC_ALL=C sort -t'|' -k1,1 -n | {
        # When pre-fetched metadata is passed, return pri|id for caller reuse;
        # otherwise strip priorities for backward compatibility
        if [ -n "${_metadata:-}" ]; then cat; else cut -d'|' -f2; fi
    }
}

# Get blocked tasks (pending but dependencies not satisfied)
# Optional 2nd param: pre-fetched metadata (avoids subshell cache loss)
get_blocked_tasks() {
    local kanban="$1"
    local _metadata="${2:-}"

    local all_metadata
    if [ -n "$_metadata" ]; then
        all_metadata="$_metadata"
    else
        all_metadata=$(_get_cached_metadata "$kanban")
    fi

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
    all_metadata=$(_get_cached_metadata "$kanban")

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

# Detect self and circular dependencies
# Returns 0 if no issues, 1 if issues detected
# Output format (one per line):
#   SELF:<task_id>                    - task depends on itself
#   CYCLE:<task1> <task2> ...         - tasks involved in a cycle
detect_circular_dependencies() {
    local kanban="$1"

    local all_metadata
    all_metadata=$(_get_cached_metadata "$kanban")

    local tasks
    tasks=$(echo "$all_metadata" | cut -d'|' -f1)

    local -A in_degree=()
    local -A adj_list=()
    local self_deps=""
    local has_errors=0

    # Initialize
    for task_id in $tasks; do
        in_degree[$task_id]=0
        adj_list[$task_id]=""
    done

    # Build graph and detect self-dependencies
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

                # Check for self-dependency
                if [ "$dep" = "$task_id" ]; then
                    echo "SELF:$task_id"
                    self_deps="$self_deps $task_id"
                    has_errors=1
                    continue
                fi

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

    if [ "$visited_count" -ne "$total_count" ]; then
        # Find tasks that are part of the cycle (excluding self-deps already reported)
        local cycle_tasks=""
        for task_id in $tasks; do
            if [ "${in_degree[$task_id]}" -gt 0 ]; then
                # Skip if already reported as self-dependency
                if [[ ! "$self_deps" =~ (^| )$task_id($| ) ]]; then
                    cycle_tasks="$cycle_tasks $task_id"
                fi
            fi
        done
        if [ -n "$cycle_tasks" ]; then
            echo "CYCLE:$cycle_tasks"
            has_errors=1
        fi
    fi

    return $has_errors
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
    all_tasks=$(_get_cached_metadata "$kanban" | cut -d'|' -f1)

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

    # Validate task_id format to prevent awk/regex injection
    if ! _validate_task_id "$task_id"; then
        log_error "extract_task: invalid task_id format: $task_id"
        return 1
    fi

    # Extract task title from the first line matching the task ID
    local task_title
    task_title=$(awk -v task="$task_id" '
        $0 ~ "\\*\\*\\[" task "\\]\\*\\*" {
            # Extract everything after **[TASK-ID]**
            sub(/.*\*\*\[[A-Za-z]{2,10}-[0-9]{1,4}\]\*\* */, "")
            print
            exit
        }' "$kanban")

    # Extract task details and create a PRD for worker
    cat <<EOF
# Task: $task_id${task_title:+ - $task_title}

$(awk -v task="$task_id" '
    $0 ~ "\\*\\*\\[" task "\\]\\*\\*" {found=1; next}
    found && /^  - Description:/ {sub(/^  - Description: /, ""); desc=$0; next}
    found && /^  - Priority:/ {sub(/^  - Priority: /, ""); priority=$0; next}
    found && /^  - Complexity:/ {sub(/^  - Complexity: /, ""); complexity=$0; next}
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
    found && /^  - / && !/^  - (Description|Priority|Complexity|Dependencies|Scope|Out of Scope|Acceptance Criteria):?/ {
        in_scope=0; in_oos=0; in_ac=0
    }
    found && /^- \[/ {exit}
    found && /^## / {exit}
    END {
        if (desc) print "## Description\n" desc "\n"
        if (priority) print "## Priority\n" priority "\n"
        if (complexity) print "## Complexity\n" complexity "\n"
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
