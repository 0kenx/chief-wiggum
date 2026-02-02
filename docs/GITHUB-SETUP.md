# GitHub Issue Sync Setup

Two-way sync between GitHub Issues and `.ralph/kanban.md`. Create tasks as GitHub issues; wiggum pulls them into the kanban, assigns workers, and pushes status updates back.

## Prerequisites

- `gh` CLI installed and authenticated (`gh auth login`)
- A GitHub repository with Issues enabled

## 1. Create Repository Labels

Wiggum does **not** create labels automatically. Create these before enabling sync.

### Gate Label (required)

| Label | Purpose |
|-------|---------|
| `wiggum` | Only issues with this label are synced. Configurable via `label_filter`. |

### Priority Labels (optional)

| Label | Kanban Priority |
|-------|-----------------|
| `priority:critical` | CRITICAL |
| `priority:high` | HIGH |
| `priority:medium` | MEDIUM |
| `priority:low` | LOW |

If no priority label is present, `default_priority` (MEDIUM) is used. If multiple exist, the highest wins.

### Status Labels (managed by wiggum)

These are applied automatically during up-sync. Do not add or remove them manually.

| Label | Kanban Status | Meaning |
|-------|---------------|---------|
| _(none)_ | `[ ]` pending | New task, not yet started |
| `wiggum:in-progress` | `[=]` | Worker is running |
| `wiggum:pending-approval` | `[P]` | PR created, awaiting review |
| `wiggum:failed` | `[*]` | Worker failed (retryable) |
| `wiggum:completed` | `[x]` | Task done |
| `wiggum:not-planned` | `[N]` | Task won't be done |

Status labels are mutually exclusive: when wiggum applies one, it removes any other.

Quick-create all labels:

```bash
gh label create wiggum --color 0052CC --description "Wiggum-managed task"
gh label create "priority:critical" --color B60205
gh label create "priority:high" --color D93F0B
gh label create "priority:medium" --color FBCA04
gh label create "priority:low" --color 0E8A16
gh label create "wiggum:in-progress" --color 1D76DB
gh label create "wiggum:pending-approval" --color 5319E7
gh label create "wiggum:failed" --color E4E669
gh label create "wiggum:completed" --color 0E8A16
gh label create "wiggum:not-planned" --color FFFFFF
```

## 2. Configure Sync

Add to `.ralph/config.json`:

```json
{
  "github": {
    "issue_sync": {
      "enabled": true,
      "allowed_user_ids": [12345678]
    }
  }
}
```

Find your numeric user ID:

```bash
gh api user --jq '.id'
```

### Full Configuration Reference

All fields with defaults shown:

```json
{
  "github": {
    "issue_sync": {
      "enabled": false,
      "allowed_user_ids": [],
      "label_filter": "wiggum",
      "default_priority": "MEDIUM",
      "priority_labels": {
        "priority:critical": "CRITICAL",
        "priority:high": "HIGH",
        "priority:medium": "MEDIUM",
        "priority:low": "LOW"
      },
      "status_labels": {
        "wiggum:in-progress": "=",
        "wiggum:pending-approval": "P",
        "wiggum:failed": "*",
        "wiggum:completed": "x",
        "wiggum:not-planned": "N"
      },
      "close_on": ["x"]
    }
  }
}
```

| Field | Type | Description |
|-------|------|-------------|
| `enabled` | bool | Master switch. Must be `true` to activate sync. |
| `allowed_user_ids` | int[] | Numeric GitHub user IDs whose issues are synced. |
| `label_filter` | string | Gate label. Only issues with this label are synced. |
| `default_priority` | string | Priority when no priority label is present. |
| `priority_labels` | object | Maps GitHub label name to kanban priority string. |
| `status_labels` | object | Maps GitHub label name to kanban status char. |
| `close_on` | string[] | Kanban status chars that also close the issue. Default: only `x` (completed). |

### Environment Variable Overrides

| Variable | Overrides |
|----------|-----------|
| `WIGGUM_GITHUB_ISSUE_SYNC=true` | `enabled` |
| `WIGGUM_GITHUB_ALLOWED_USER_IDS=123,456` | `allowed_user_ids` |
| `WIGGUM_GITHUB_LABEL_FILTER=wiggum` | `label_filter` |
| `WIGGUM_GITHUB_DEFAULT_PRIORITY=HIGH` | `default_priority` |

## 3. Issue Title Format

The issue title **must** contain a task ID in brackets matching the kanban regex `[A-Za-z]{2,10}-[0-9]{1,4}`:

```
[GH-42] Add dark mode support
[FEAT-7] Implement OAuth login
[BUG-123] Fix race condition in worker pool
```

- The prefix (2-10 letters) is chosen by the issue creator.
- The number (1-4 digits) uniquely identifies the task.
- Brackets can optionally be bold: `**[GH-42]**`
- Issues without a valid task ID in the title are silently skipped.

## 4. Issue Body Format

Wiggum extracts structured fields from the body. Unrecognized text becomes the Description.

### Inline Fields

Single-line, anywhere in body (case-insensitive):

```
Priority: HIGH
Complexity: MEDIUM
Dependencies: GH-10, GH-15
Dependencies: none
```

- `Priority` in the body is a fallback; priority labels take precedence.
- `Dependencies` are validated against the task ID regex. Invalid refs are silently dropped.

### Section Fields

Multi-line, under markdown headings (`##` or `###`):

```markdown
## Scope
- Deliverable item one
- Deliverable item two

## Out of Scope
- Thing NOT to implement

## Acceptance Criteria
- Must pass integration tests
- Must handle edge case X
```

### Example Issue

```markdown
Title: [GH-42] Add dark mode support

Body:
Support dark/light theme toggling for the web UI.

Priority: HIGH
Complexity: MEDIUM
Dependencies: GH-30

## Scope
- Add theme toggle to settings page
- Persist preference in local storage

## Out of Scope
- Custom color themes

## Acceptance Criteria
- Toggle switches between dark and light themes
- Preference persists across page reloads
```

## 5. Running Sync

### Manual

```bash
wiggum github                         # Full sync cycle (down + up)
wiggum github down                    # Pull new issues into kanban
wiggum github up                      # Push status changes to GitHub
wiggum github sync up TASK-333        # Create issue for untracked task
wiggum github sync up all             # Create issues for all untracked tasks
wiggum github sync up all -y          # Skip confirmation prompt
wiggum github status                  # Show sync state summary
wiggum github --dry-run               # Preview changes without writing
```

### Automatic

When the orchestrator is running (`wiggum run`), sync runs automatically every 2 minutes as a periodic service.

## Authority Model

| Kanban Status | Content authority | State authority |
|---------------|-------------------|-----------------|
| `[ ]` pending | Remote (GitHub) | Remote |
| `[=]` in-progress | Local (kanban) | Local |
| `[P]` pending-approval | Local | Local |
| `[*]` failed | Local | Local |
| `[x]` completed | Local | Local |
| `[N]` not-planned | Local | Local |

- **Pending tasks**: Edits on GitHub (body, priority labels) update the local kanban.
- **In-progress and beyond**: Local kanban is authoritative. GitHub edits are ignored until the task is reset to pending.

## Issue State Mapping

| Kanban Status | GitHub Issue State |
|---------------|--------------------|
| `[ ]` pending | Open |
| `[=]` in-progress | Open |
| `[P]` pending-approval | Open |
| `[*]` failed | Open |
| `[x]` completed | **Closed** |
| `[N]` not-planned | Open |

Only `[x]` (completed) closes the issue. Failed and not-planned tasks stay open with their status label.

### Human Actions on GitHub

| Local Status | Human closes issue | Result |
|--------------|-------------------|--------|
| `[ ]` pending | Closed | Marked `[N]` locally |
| `[*]` failed | Closed | Marked `[N]` locally |
| `[=]` in-progress | Closed | No change (local-authoritative) |
| `[N]` not-planned | Reopened | Reset to `[ ]` pending |
| `[x]` completed | Reopened | No change (file new issue instead) |

## Troubleshooting

**Sync is disabled**
```
GitHub issue sync is disabled.
```
Set `enabled: true` in `.ralph/config.json` or `WIGGUM_GITHUB_ISSUE_SYNC=true`.

**No allowed users configured**
```
GitHub sync: no allowed users configured
```
Add `allowed_user_ids` to config. Find your ID with `gh api user --jq '.id'`.

**Issue not syncing**
- Verify the issue has the gate label (`wiggum` by default).
- Verify the issue title contains a valid task ID in brackets.
- Verify the issue author is in the allowed users list.

**gh CLI not authenticated**
```
GitHub CLI (gh) not found in PATH
```
Install `gh` and run `gh auth login`.
