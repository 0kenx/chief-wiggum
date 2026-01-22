# Inter-Agent Communication Protocol

This document describes how agents communicate and share information in Chief Wiggum.

## Overview

Chief Wiggum agents operate in isolated worker directories but need to share state, results, and context. This protocol defines the communication patterns and file-based interfaces.

## Worker Directory Structure

```
.ralph/workers/worker-TASK-001-1234567890/
├── prd.md                    # Input: Product Requirements Document
├── workspace/                # Git worktree for isolated work
├── agent.pid                 # PID of running agent
├── agent-result.json         # Structured output from agent
├── logs/
│   ├── iteration-0.log       # Claude conversation log (iteration 0)
│   ├── iteration-1.log       # Claude conversation log (iteration 1)
│   └── ...
├── summaries/
│   ├── iteration-0-summary.txt  # Progress summary (iteration 0)
│   ├── iteration-1-summary.txt  # Progress summary (iteration 1)
│   └── summary.txt              # Final summary (work complete)
├── checkpoints/              # Structured checkpoint data
│   ├── checkpoint-0.json
│   └── checkpoint-1.json
└── (agent-specific files)
```

## Result Communication

### Primary: agent-result.json

The preferred method for agents to communicate results:

```json
{
  "agent_type": "validation-review",
  "completed_at": "2024-01-15T10:30:00Z",
  "exit_code": 0,
  "outputs": {
    "VALIDATION_result": "PASS",
    "review_notes": "All requirements met",
    "files_reviewed": 15
  }
}
```

### Writing Results

```bash
# Using agent-base.sh helper
agent_write_result "$worker_dir" "VALIDATION_result" "PASS"
agent_write_result "$worker_dir" "pr_url" "https://github.com/..."

# Result is appended to outputs object
```

### Reading Results

```bash
# Read from sub-agent with fallback
result=$(agent_read_subagent_result "$worker_dir" "VALIDATION_result" "validation-result.txt")

# Direct jq access
result=$(jq -r '.outputs.VALIDATION_result' "$worker_dir/agent-result.json")
```

### Legacy: Text Files

Some agents still use text file output for simplicity:

| File | Agent | Values |
|------|-------|--------|
| `validation-result.txt` | validation-review | PASS, FAIL, UNKNOWN |
| `security-result.txt` | security-audit | PASS, FIX, STOP |
| `review-result.txt` | code-review | APPROVE, REQUEST_CHANGES, COMMENT |
| `test-result.txt` | test-coverage | PASS, FAIL, SKIP |

## Progress Communication

### Iteration Summaries

Each iteration writes a summary to `summaries/iteration-N-summary.txt`:

```markdown
## Iteration 3 Summary

### Completed
- Implemented user authentication endpoint
- Added password hashing with bcrypt

### In Progress
- Writing unit tests for auth module

### Blocked
- Waiting for database schema from DBA

### Next Steps
1. Complete unit tests
2. Add integration tests
3. Update API documentation
```

### Structured Checkpoints

JSON checkpoints at `checkpoints/checkpoint-N.json`:

```json
{
  "version": "1.0",
  "iteration": 3,
  "session_id": "abc123",
  "timestamp": "2024-01-15T10:30:00Z",
  "status": "in_progress",
  "files_modified": [
    "src/auth/handler.ts",
    "src/auth/middleware.ts"
  ],
  "completed_tasks": [
    "Implement auth endpoint",
    "Add password hashing"
  ],
  "next_steps": [
    "Write unit tests",
    "Add integration tests"
  ],
  "prose_summary": "..."
}
```

## Sub-Agent Invocation

### Pattern: Parent → Sub-Agent

```bash
# Parent agent (task-worker.sh)
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"

    # ... main work ...

    # Invoke validation as sub-agent
    run_sub_agent "validation-review" "$worker_dir" "$project_dir"
    local validation_exit=$?

    # Read sub-agent result
    local result
    result=$(agent_read_subagent_result "$worker_dir" "VALIDATION_result" "validation-result.txt")

    if [ "$result" = "PASS" ]; then
        # Proceed with commit/PR
    else
        # Handle failure
    fi
}
```

### Sub-Agent Constraints

- Sub-agents do NOT manage PID files
- Sub-agents do NOT set up signal handlers
- Sub-agents share the parent's workspace
- Sub-agents write to the same worker directory

## Event Communication

### Event Log Format

Events written to `.ralph/logs/events.jsonl`:

```json
{"timestamp":"2024-01-15T10:30:00Z","event_type":"task.started","worker_id":"worker-TASK-001-123","task_id":"TASK-001"}
{"timestamp":"2024-01-15T10:35:00Z","event_type":"iteration.completed","worker_id":"worker-TASK-001-123","iteration":1,"exit_code":0}
{"timestamp":"2024-01-15T10:40:00Z","event_type":"error","worker_id":"worker-TASK-001-123","error_type":"timeout","message":"API call exceeded 30s"}
{"timestamp":"2024-01-15T10:45:00Z","event_type":"task.completed","worker_id":"worker-TASK-001-123","task_id":"TASK-001","result":"PASS"}
```

### Emitting Events

```bash
source "$WIGGUM_HOME/lib/metrics/event-emitter.sh"

emit_task_started "$task_id" "$worker_id"
emit_iteration_completed "$worker_id" "$iteration" "$exit_code"
emit_error "$worker_id" "timeout" "API call exceeded 30s"
emit_task_completed "$task_id" "$worker_id" "PASS"
```

### Querying Events

```bash
# All events for a task
jq 'select(.task_id == "TASK-001")' .ralph/logs/events.jsonl

# All errors
jq 'select(.event_type == "error")' .ralph/logs/events.jsonl

# Events in time range
jq 'select(.timestamp >= "2024-01-15T10:00:00Z")' .ralph/logs/events.jsonl
```

## Kanban State Communication

### Status Updates

Agents update task status in `.ralph/kanban.md`:

| Marker | Status | Set By |
|--------|--------|--------|
| `[ ]` | TODO | Initial state |
| `[=]` | In Progress | task-worker start |
| `[x]` | Complete | post-PR merge |
| `[P]` | Pending Approval | PR created |
| `[*]` | Failed | validation failed |
| `[N]` | Not Planned | manual |

### Status Update Functions

```bash
source "$WIGGUM_HOME/lib/tasks/task-parser.sh"

update_kanban_status "$kanban_file" "$task_id" "="   # In progress
update_kanban_pending_approval "$kanban_file" "$task_id"  # [P]
update_kanban "$kanban_file" "$task_id"             # [x] Complete
update_kanban_failed "$kanban_file" "$task_id"      # [*] Failed
```

## File Locking

### Concurrent Access

Use file locks for shared resource access:

```bash
source "$WIGGUM_HOME/lib/core/file-lock.sh"

# Lock kanban.md during update
with_file_lock "$kanban_file.lock" 5 \
    update_kanban_status "$kanban_file" "$task_id" "="

# Retry with backoff
with_file_lock_retry "$pid_file.lock" 10 3 \
    register_pid "$pid_file" "$$"
```

### Lock Files

Existence of a file with .lock extension marks the underlying file locked and cannot be written to.

| Resource | Lock File |
|----------|-----------|
| kanban.md | `.ralph/kanban.md.lock` |
| PID operations | `.ralph/.pid-ops.lock` |
| Events log | `.ralph/logs/events.jsonl.lock` |

## Workspace Boundary Protocol

### Violation Detection

The violation monitor checks for:
- Edit operations outside `$worker_dir/workspace`
- Destructive git commands in main repo
- File modifications in `.ralph/` from agents

### On Violation

1. Agent process terminated (SIGTERM)
2. `violation_status.txt` created with `WORKSPACE_VIOLATION`
3. Violation logged to `.ralph/logs/violations.log`
4. Task marked as failed in kanban

### Recovery

```bash
# Review violation
cat .ralph/logs/violations.log

# Force resume after manual fix
wiggum resume TASK-001 -f
```

## Best Practices

1. **Always use structured results** - Prefer `agent-result.json` over text files
2. **Write checkpoints regularly** - Enables resume after interruption
3. **Emit events for observability** - Makes debugging easier
4. **Use file locks for shared resources** - Prevents race conditions
5. **Respect workspace boundaries** - Never modify files outside workspace
6. **Read before assuming** - Check if result file exists before reading
