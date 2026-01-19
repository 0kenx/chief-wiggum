#!/usr/bin/env bash
# Task parser for markdown kanban and PRD files

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
