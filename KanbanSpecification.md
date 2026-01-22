# Kanban Specification for Chief Wiggum

This document defines the structure and format requirements for the `kanban.md` file used by Chief Wiggum's autonomous worker system.

## Overview

The `kanban.md` file serves as the central task registry for Chief Wiggum. It contains a list of tasks that workers will automatically pick up, process, and complete. The system uses this file to:

- Track which tasks are pending, in-progress, or complete
- Extract task metadata (description, priority, dependencies)
- Generate PRD (Product Requirement Document) files for each worker
- Update task status as workers complete their work
- Coordinate dependencies between tasks

## File Structure

### Required Sections

The kanban file MUST contain a `## TASKS` section header. All tasks must be listed under this section.

```markdown
# Project Name Kanban

## TASKS

[Task entries go here]
```

### Task Entry Format

Each task entry follows this exact structure:

```markdown
- [ ] **[TASK-ID]** Brief task description
  - Description: Detailed description of what needs to be done
  - Priority: CRITICAL|HIGH|MEDIUM|LOW
  - Complexity: HIGH|MEDIUM|LOW (optional)
  - Dependencies: TASK-ID-1, TASK-ID-2 | none
```

#### Optional Extended Fields

Tasks can include additional optional fields for more detailed specifications:

```markdown
- [ ] **[TASK-ID]** Brief task description
  - Description: Detailed description of what needs to be done
  - Priority: CRITICAL|HIGH|MEDIUM|LOW
  - Complexity: HIGH|MEDIUM|LOW
  - Dependencies: TASK-ID-1, TASK-ID-2 | none
  - Scope:
    - Specific item to implement or deliver
    - Another item in scope
    - Third deliverable item
  - Out of Scope:
    - Thing NOT to implement
    - Another exclusion
  - Acceptance Criteria:
    - Validation point 1
    - Validation point 2
```

## Field Specifications

### Task ID

**Format**: `[PREFIX-NUMBER]`

**Pattern**: `[A-Za-z]{2,8}-[0-9]+`

**Examples**:
- `[TASK-001]`
- `[FEATURE-042]`
- `[BUG-123]`
- `[REFACTOR-5]`

**Requirements**:
- Prefix: 2-8 uppercase letters
- Number: One or more digits
- Must be unique across the kanban file
- Wrapped in square brackets and bold markers: `**[TASK-ID]**`

### Status Checkbox

Tasks use markdown checkboxes to indicate their status:

| Marker | Status | Description |
|--------|--------|-------------|
| `- [ ]` | Pending | Not started |
| `- [=]` | In-progress | Worker actively processing |
| `- [P]` | Pending Approval | PR created, awaiting review/merge |
| `- [x]` | Complete | PR merged, task finished |
| `- [N]` | Not Planned | Task won't be done |
| `- [*]` | Failed | Worker encountered errors |

**Dependency Resolution**: Tasks are only considered satisfied (for dependency purposes) when they reach the `[x]` (Complete/Merged) status. Tasks in `[P]` (Pending Approval) do NOT satisfy dependencies - the PR must be merged first.

**Important**: Workers automatically update these status markers via file locking to prevent race conditions.

### Brief Description

- Appears immediately after the task ID on the same line
- Should be concise (ideally under 80 characters)
- Used in commit messages, PR titles, and changelogs
- Written as an imperative statement (e.g., "Create README file" not "Creating README")

### Description (Required)

- Indented with 2 spaces: `  - Description:`
- Provides detailed context about what needs to be implemented
- Should be specific enough for a worker to understand requirements
- Single line or paragraph (no multi-line formatting in this field)

### Priority (Required)

- Indented with 2 spaces: `  - Priority:`
- Valid values: `CRITICAL`, `HIGH`, `MEDIUM`, `LOW`
- Used for task ordering and commit metadata
- Case-sensitive (must be uppercase)

### Complexity (Optional)

- Indented with 2 spaces: `  - Complexity:`
- Valid values: `HIGH`, `MEDIUM`, `LOW`
- Indicates the estimated effort and scope of the task
- Case-sensitive (must be uppercase)
- Guidelines:
  - **HIGH**: Large scope, many files, architectural changes, significant risk
  - **MEDIUM**: Moderate scope, several files, standard implementation
  - **LOW**: Small scope, few files, straightforward changes

### Dependencies (Required)

- Indented with 2 spaces: `  - Dependencies:`
- Lists task IDs that must complete before this task can start
- Format: Comma-separated task IDs or the word `none`
- Examples:
  - `none` - No dependencies
  - `TASK-001` - Single dependency
  - `TASK-001, TASK-002, TASK-003` - Multiple dependencies

**Note**: Chief Wiggum currently processes dependencies by task order, not by automatic dependency resolution.

### Scope (Optional)

- Indented with 2 spaces: `  - Scope:`
- Defines what should be implemented or delivered
- Each item indented with 4 spaces: `    - Item description`
- Items become checklist items in the worker's PRD
- Use for breaking down larger tasks into specific deliverables

### Out of Scope (Optional)

- Indented with 2 spaces: `  - Out of Scope:`
- Defines what should NOT be implemented
- Each item indented with 4 spaces: `    - Item description`
- Helps prevent scope creep and clarify boundaries
- Included in PRD for worker reference

### Acceptance Criteria (Optional)

- Indented with 2 spaces: `  - Acceptance Criteria:`
- Defines success criteria and validation points
- Each item indented with 4 spaces: `    - Criterion description`
- Included in PRD for worker reference
- Not converted to checklist items

## Parsing Rules

### Task Extraction

The system uses `lib/task-parser.sh` with the following logic:

1. **Task Detection**: Finds lines matching `^- \[[ =PxN*T]\] \*\*\[[A-Za-z]{2,8}-[0-9]+\]\*\*` in the TASKS section
2. **Field Parsing**: Extracts fields using indentation:
   - Top-level fields: 2-space indent (`  - Field:`)
   - Sub-items: 4-space indent (`    - Item`)
3. **Section Boundary**: Parsing stops when encountering:
   - Another task line (`^- \[`)
   - Another section header (`^## `)
4. **PRD Generation**: Converts parsed data into a structured PRD file

### Status Updates

Status updates use file locking (`lib/file-lock.sh`) to safely modify the checkbox:

```bash
# Mark task as in-progress
update_kanban_status "$kanban" "$task_id" "="

# Mark task as pending approval (PR created)
update_kanban_pending_approval "$kanban" "$task_id"

# Mark task as complete (PR merged)
update_kanban "$kanban" "$task_id"

# Mark task as failed
update_kanban_failed "$kanban" "$task_id"

# Mark task as not planned
update_kanban_not_planned "$kanban" "$task_id"
```

The `wiggum review sync` command automatically updates tasks from `[P]` to `[x]` when their PRs are merged.

### PRD Generation from Scope

When a task includes Scope items, they are converted to a checklist:

```markdown
## Checklist

- [ ] First scope item
- [ ] Second scope item
- [ ] Third scope item
- [ ] Mark this PRD as complete
```

If no Scope is provided, default checklist items are generated:

```markdown
## Checklist

- [ ] Complete the task as described
- [ ] Test the implementation
- [ ] Mark this PRD as complete
```

## Complete Examples

### Minimal Task

```markdown
- [ ] **[TASK-001]** Create README file
  - Description: Create a README.md with project description, installation instructions, and usage guide
  - Priority: HIGH
  - Dependencies: none
```

### Full-Featured Task

```markdown
- [ ] **[FEATURE-042]** Implement user authentication system
  - Description: Add JWT-based authentication with login, logout, and token refresh endpoints
  - Priority: HIGH
  - Complexity: HIGH
  - Dependencies: TASK-001, TASK-002
  - Scope:
    - Create authentication middleware
    - Implement login endpoint with JWT generation
    - Implement logout endpoint with token invalidation
    - Add token refresh mechanism
    - Create user session management
  - Out of Scope:
    - OAuth integration (future enhancement)
    - Two-factor authentication
    - Password reset functionality
  - Acceptance Criteria:
    - All endpoints return appropriate HTTP status codes
    - JWTs expire after configured timeout
    - Invalid tokens are rejected
    - Unit tests achieve 80% coverage
```

## Integration Points

### worker.sh Integration

The `worker.sh` script references kanban.md at these locations:

1. **Line 148**: Extracts task description for commit messages
   ```bash
   grep "**\[$TASK_ID\]**" "$PROJECT_DIR/.ralph/kanban.md"
   ```

2. **Line 151**: Extracts task priority
   ```bash
   grep -A2 "**\[$TASK_ID\]**" "$PROJECT_DIR/.ralph/kanban.md" | grep "Priority:"
   ```

3. **Line 154**: Extracts task dependencies
   ```bash
   grep -A3 "**\[$TASK_ID\]**" "$PROJECT_DIR/.ralph/kanban.md" | grep "Dependencies:"
   ```

4. **Lines 253, 278**: Updates task status to complete or failed
   ```bash
   update_kanban "$PROJECT_DIR/.ralph/kanban.md" "$TASK_ID"
   update_kanban_failed "$PROJECT_DIR/.ralph/kanban.md" "$TASK_ID"
   ```

### task-parser.sh Integration

The `lib/task-parser.sh` script provides these functions:

- `get_todo_tasks <kanban>`: Returns list of incomplete task IDs
- `extract_task <task_id> <kanban>`: Generates PRD from task entry
- Uses AWK to parse the hierarchical structure and extract all fields

## Best Practices

### Task IDs

- Use consistent prefixes (e.g., all TASK- or organized by type: FEATURE-, BUG-, etc.)
- Number sequentially for easier tracking
- Never reuse IDs, even for failed or deleted tasks

### Descriptions

- Be specific and actionable
- Include context about why the task is needed
- Reference related files, endpoints, or components
- Avoid ambiguous terms like "improve" or "fix" without details

### Scope Items

- Use Scope to break complex tasks into clear deliverables
- Each scope item should be testable or verifiable
- Order items logically (dependencies first)
- Keep items focused and atomic

### Dependencies

- List all prerequisite tasks explicitly
- Consider both technical dependencies (shared code) and logical dependencies (requires data from another task)
- Use `none` explicitly rather than omitting the field
- Order tasks in the kanban file to respect dependencies when possible

### Priority Guidelines

- **CRITICAL**: Security vulnerabilities, data loss risks, system-breaking bugs
- **HIGH**: Blocking other work, critical bugs, or foundational features
- **MEDIUM**: Important features, non-critical bugs, enhancements
- **LOW**: Nice-to-haves, optimizations, documentation improvements

## Common Pitfalls

### Incorrect Indentation

**Wrong**:
```markdown
- [ ] **[TASK-001]** Do something
- Description: Details here
```

**Correct**:
```markdown
- [ ] **[TASK-001]** Do something
  - Description: Details here
```

### Missing Required Fields

**Wrong**:
```markdown
- [ ] **[TASK-001]** Do something
  - Description: Details here
```

**Correct**:
```markdown
- [ ] **[TASK-001]** Do something
  - Description: Details here
  - Priority: MEDIUM
  - Dependencies: none
```

### Invalid Task ID Format

**Wrong**:
```markdown
- [ ] **TASK-001** Do something
- [ ] **[T-1]** Do something
- [ ] **[VERYLONGTASKPREFIX-001]** Do something
```

**Correct**:
```markdown
- [ ] **[TASK-001]** Do something
- [ ] **[FEAT-1]** Do something
- [ ] **[BUG-001]** Do something
```

### Incorrect Scope Indentation

**Wrong**:
```markdown
  - Scope:
  - First item
  - Second item
```

**Correct**:
```markdown
  - Scope:
    - First item
    - Second item
```

## File Location

The kanban file must be located at:

```
<PROJECT_ROOT>/.ralph/kanban.md
```

This location is hardcoded in `worker.sh` and expected by the file locking utilities.

## Concurrency Handling

Multiple workers may access the kanban file simultaneously. The system handles this through:

1. **File Locking**: Using `flock` with 10-second timeout
2. **Retry Logic**: Up to 5 retries with exponential backoff
3. **Atomic Updates**: Single sed command per status change
4. **Lock Files**: Temporary `.lock` files prevent concurrent writes

Workers should never manually edit the kanban file while Chief Wiggum is running.

## Version History

- **v1.0** (Initial): Basic task structure with Description, Priority, Dependencies
- **v1.1**: Added Scope, Out of Scope, and Acceptance Criteria fields
- **v1.2**: Added optional Complexity field (HIGH/MEDIUM/LOW)
- **v1.3** (Current): Added new status flags for PR workflow:
  - `[P]` - Pending Approval (PR created, awaiting review/merge)
  - `[N]` - Not Planned (task won't be done)
  - Dependencies now require `[x]` (merged) status, not just `[P]` (pending approval)

## See Also

- `config/examples/simple-kanban.md` - Minimal example
- `config/examples/web-app-kanban.md` - Full-featured example
- `lib/task-parser.sh` - Parsing implementation
- `lib/file-lock.sh` - Concurrent access handling
- `lib/worker.sh` - Worker integration logic
