#!/usr/bin/env bash
# Task parser for markdown kanban and PRD files

# Escape special regex characters for use in sed/grep patterns (BRE - Basic Regular Expressions)
# Usage: escape_regex_chars "TASK-012.foo[bar]"
escape_regex_chars() {
    local str="$1"
    # Escape special regex characters for Basic Regular Expressions (BRE)
    # In BRE: . * [ ] ^ $ \ / are special and need escaping
    # In BRE: ( ) { } + ? | are literal unless escaped, so we DON'T escape them
    echo "$str" | sed 's/[]\.\*\[\^\$\\/]/\\&/g'
}

# Escape special regex characters for use in awk patterns (ERE - Extended Regular Expressions)
# Usage: escape_regex_chars_ere "TASK-012.foo[bar]"
escape_regex_chars_ere() {
    local str="$1"
    # Escape special regex characters for Extended Regular Expressions (ERE)
    # In ERE: . * [ ] ^ $ \ / ( ) { } + ? | are all special and need escaping
    echo "$str" | sed 's/[]\.\*\[\^\$\\/(){}+?|]/\\&/g'
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
    # Extract task IDs from TASKS section - ONLY incomplete tasks (- [ ])
    awk 'BEGIN{in_tasks=0}
        /^## TASKS$/{in_tasks=1; next}
        /^## / && in_tasks{in_tasks=0}
        in_tasks && /^- \[ \] \*\*\[[A-Za-z]{2,8}-[0-9]+\]\*\*/{
            match($0, /\[[A-Za-z]{2,8}-[0-9]+\]/)
            print substr($0, RSTART+1, RLENGTH-2)
        }' "$kanban"
}

get_failed_tasks() {
    local kanban="$1"
    # Extract task IDs from TASKS section - ONLY failed tasks (- [*])
    awk 'BEGIN{in_tasks=0}
        /^## TASKS$/{in_tasks=1; next}
        /^## / && in_tasks{in_tasks=0}
        in_tasks && /^- \[\*\] \*\*\[[A-Za-z]{2,8}-[0-9]+\]\*\*/{
            match($0, /\[[A-Za-z]{2,8}-[0-9]+\]/)
            print substr($0, RSTART+1, RLENGTH-2)
        }' "$kanban"
}

extract_task() {
    local task_id="$1"
    local kanban="$2"

    # Escape special regex characters in task_id for safe pattern matching in awk (ERE)
    local escaped_task_id=$(escape_regex_chars_ere "$task_id")

    # Extract task details and create a PRD for worker
    cat <<EOF
# Task: $task_id

$(awk -v task="$task_id" '
    /\*\*\['"$escaped_task_id"'\]\*\*/ {found=1; next}
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
