# Invalid Kanban - Bad Dependencies

## TASKS

- [ ] **[TASK-001]** Valid task
  - Description: This task is valid
  - Priority: HIGH
  - Dependencies: none

- [ ] **[TASK-002]** Task with non-existent dependency
  - Description: References a task that doesn't exist
  - Priority: MEDIUM
  - Dependencies: TASK-999

- [ ] **[TASK-003]** Task with multiple bad dependencies
  - Description: References multiple non-existent tasks
  - Priority: LOW
  - Dependencies: TASK-100, TASK-200, TASK-001
