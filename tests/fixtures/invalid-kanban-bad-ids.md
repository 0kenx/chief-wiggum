# Invalid Kanban - Bad Task IDs

## TASKS

- [ ] **[T-001]** ID too short (prefix < 2 chars)
  - Description: Task ID prefix must be 2-8 characters
  - Priority: HIGH
  - Dependencies: none

- [ ] **[VERYLONGPREFIX-001]** ID prefix too long (> 8 chars)
  - Description: Task ID prefix must be 2-8 characters
  - Priority: HIGH
  - Dependencies: none

- [ ] **[TASK-abc]** Non-numeric ID
  - Description: Task ID number must be numeric
  - Priority: MEDIUM
  - Dependencies: none
