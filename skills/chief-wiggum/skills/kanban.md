---
description: Generate Kanban task entries from user description
---

# Kanban Task Generator

This skill helps you generate properly formatted task entries for Chief Wiggum's `kanban.md` file.

## What it does

Converts a user's natural language task description into a structured Kanban task entry that follows the KanbanSpecification format.

## Usage

When a user wants to add tasks to their kanban board, use this skill to generate properly formatted task entries.

## Task Format Requirements

Each task must follow this structure:

```markdown
- [ ] **[TASK-ID]** Brief task description
  - Description: Detailed description of what needs to be done
  - Priority: HIGH|MEDIUM|LOW
  - Dependencies: TASK-ID-1, TASK-ID-2 | none
```

### Optional Extended Fields

```markdown
  - Scope:
    - Specific item to implement or deliver
    - Another item in scope
  - Out of Scope:
    - Thing NOT to implement
    - Another exclusion
  - Acceptance Criteria:
    - Validation point 1
    - Validation point 2
```

## Task ID Guidelines

- **Format**: `[PREFIX-NUMBER]`
- **Pattern**: `[A-Za-z]{2,8}-[0-9]+`
- **Examples**: `[TASK-001]`, `[FEATURE-042]`, `[BUG-123]`
- Prefix: 2-8 uppercase letters
- Number: Sequential numbering
- Must be unique across the kanban file

## Priority Levels

- **HIGH**: Blocking other work, critical bugs, foundational features
- **MEDIUM**: Important features, non-critical bugs, enhancements
- **LOW**: Nice-to-haves, optimizations, documentation

## Instructions

When generating kanban tasks:

1. **Ask clarifying questions** if the user's description is vague:
   - What is the specific goal or outcome?
   - Are there any dependencies on other tasks?
   - What should be included/excluded from scope?
   - What priority level is appropriate?

2. **Determine the next task ID**:
   - Read the existing `.ralph/kanban.md` file
   - Find the highest task number
   - Increment by 1 for the new task
   - Use the same prefix pattern (typically `TASK-`)

3. **Generate task structure**:
   - Write a clear, imperative brief description (e.g., "Create README file")
   - Provide detailed context in the Description field
   - Set appropriate priority (HIGH/MEDIUM/LOW)
   - List dependencies or use "none"
   - Break complex tasks into Scope items
   - Define what's Out of Scope to prevent scope creep
   - Add Acceptance Criteria for validation

4. **Output the formatted task**:
   - Present the complete task entry
   - Ensure proper indentation (2 spaces for fields, 4 spaces for sub-items)
   - Verify all required fields are present
   - Ask if the user wants to add it to their kanban.md

## Example Interaction

**User**: "I need to add authentication to the app"

**Assistant**: Let me help you create a kanban task for that. I have a few questions:

1. What authentication method? (JWT, OAuth, session-based?)
2. What features should be included? (login, register, logout, password reset?)
3. Are there any dependencies on other tasks?
4. What's the priority level?

**User**: "JWT authentication with login and register. No dependencies. High priority."

**Assistant**: Here's your kanban task entry:

```markdown
- [ ] **[TASK-015]** Implement JWT authentication system
  - Description: Add JWT-based authentication with login and register endpoints, password hashing, and protected route middleware
  - Priority: HIGH
  - Dependencies: none
  - Scope:
    - Create authentication middleware for protected routes
    - Implement login endpoint with JWT generation
    - Implement register endpoint with input validation
    - Add password hashing with bcrypt
    - Create token validation and refresh mechanism
  - Out of Scope:
    - OAuth integration
    - Password reset functionality
    - Two-factor authentication
  - Acceptance Criteria:
    - Passwords are hashed before storage
    - JWT tokens expire after configured timeout
    - Invalid tokens return 401 Unauthorized
    - Protected routes require valid JWT token
```

Would you like me to add this to your `.ralph/kanban.md` file?

## Best Practices

1. **Be specific**: Vague descriptions lead to unclear tasks
2. **Use Scope for complex tasks**: Break down into concrete deliverables
3. **Define boundaries**: Use Out of Scope to prevent feature creep
4. **Set realistic priorities**: Not everything can be HIGH priority
5. **Order dependencies**: List prerequisite tasks in the Dependencies field
6. **Write imperative descriptions**: "Create API endpoint" not "Creating API endpoint"
7. **Keep brief descriptions under 80 chars**: They appear in commit messages

## Common Task Patterns

### Simple Task (Minimal)
```markdown
- [ ] **[TASK-001]** Create README file
  - Description: Create a README.md with project description, installation instructions, and usage guide
  - Priority: MEDIUM
  - Dependencies: none
```

### Feature Task (With Scope)
```markdown
- [ ] **[FEATURE-042]** Implement user dashboard
  - Description: Create user dashboard with profile info, activity feed, and settings
  - Priority: HIGH
  - Dependencies: TASK-001, TASK-003
  - Scope:
    - Create dashboard layout component
    - Add profile information panel
    - Implement activity feed with pagination
    - Add user settings form
  - Out of Scope:
    - Admin dashboard
    - Analytics charts
  - Acceptance Criteria:
    - Dashboard loads in under 2 seconds
    - All data updates in real-time
    - Responsive design works on mobile
```

### Bug Fix Task
```markdown
- [ ] **[BUG-123]** Fix login form validation
  - Description: Login form allows empty passwords and doesn't show error messages properly
  - Priority: HIGH
  - Dependencies: none
  - Scope:
    - Add client-side validation for email and password
    - Display error messages below form fields
    - Prevent form submission when invalid
  - Acceptance Criteria:
    - Empty fields show validation errors
    - Invalid email format is rejected
    - Error messages are user-friendly
```

## Adding Tasks to Kanban

After generating a task, offer to add it to the kanban file:

1. Read the current `.ralph/kanban.md`
2. Find the `## TASKS` section
3. Add the new task entry at the end of the pending tasks
4. Maintain proper formatting and spacing
5. Save the file

Always verify the task ID is unique before adding!
