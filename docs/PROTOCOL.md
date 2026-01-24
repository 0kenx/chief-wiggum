# Inter-Agent Communication Protocol

This document describes how agents communicate and share information in Chief Wiggum.

## Overview

Chief Wiggum agents operate in isolated worker directories but need to share state, results, and context. This protocol defines the communication patterns and file-based interfaces.

## Inter-Agent Data Passing

Agents can pass state and data through two scopes: **sequential** (to the next pipeline step) and **arbitrary** (to any agent regardless of order).

### Sequential: Next Agent in Pipeline (5 mechanisms)

| # | Mechanism | How It Works | Key Location |
|---|-----------|-------------|--------------|
| 1 | **Gate result files** | Each agent writes `outputs.gate_result` (PASS/FAIL/FIX/STOP/SKIP) to its epoch-named result JSON. The pipeline runner reads this to decide whether to continue, skip, or trigger a fix loop. | `lib/pipeline/pipeline-runner.sh:160` |
| 2 | **Step dependencies (`depends_on`)** | A pipeline step declares `"depends_on": "step_id"` in `config/pipeline.json`. If the dependency's gate result is FAIL or UNKNOWN, the step is skipped. | `lib/pipeline/pipeline-runner.sh:68-79` |
| 3 | **Environment variable inheritance** | Parent exports context vars (`PIPELINE_PLAN_FILE`, `PIPELINE_RESUME_INSTRUCTIONS`, `WIGGUM_STEP_ID`, etc.) that sub-agents inherit via `run_sub_agent()`. | `lib/worker/agent-registry.sh:220-230` |
| 4 | **Git state globals** | Git operations set shell globals (`GIT_COMMIT_BRANCH`, `GIT_PR_URL`, `GIT_SAFETY_CHECKPOINT_SHA`) consumed by subsequent steps in the same process. | `lib/git/git-operations.sh:72,211,289` |
| 5 | **Fix-retry loop** | When an agent returns `FIX`, the pipeline invokes a nested fix agent, then re-runs the original agent to verify. State flows: audit result → fix agent → re-audit. | `lib/pipeline/pipeline-runner.sh:216` |

### Arbitrary: Any Agent to Any Agent (7 mechanisms)

| # | Mechanism | How It Works | Key Location |
|---|-----------|-------------|--------------|
| 1 | **`agent_comm_*` interface** | Unified lookup API. Any agent calls `agent_comm_path(worker_dir, type)` to resolve paths to another agent's result, report, summary, comments, prd, or workspace. | `lib/core/agent-base.sh:651-708` |
| 2 | **Result file reads by agent name** | `agent_read_subagent_result(worker_dir, agent_name)` and `agent_find_latest_result()` let any agent read any other agent's epoch-named result JSON. | `lib/core/agent-base.sh:860,428` |
| 3 | **Shared workspace** | All agents in a task share `worker_dir/workspace/` (a git worktree). Code changes committed by one agent are visible to all subsequent agents. | `lib/worker/agent-registry.sh:376-387` |
| 4 | **Event log (JSONL)** | Append-only stream at `.ralph/logs/events.jsonl`. Any agent can emit events (`emit_task_started`, `emit_agent_completed`, `emit_pr_created`, etc.) and query by type/task/worker. | `lib/utils/event-emitter.sh:271-311` |
| 5 | **Checkpoint files** | Structured JSON at `checkpoints/checkpoint-N.json` containing `files_modified`, `completed_tasks`, `next_steps`, and `prose_summary`. Readable by any agent in the worker. | `lib/core/checkpoint.sh:100-113` |
| 6 | **Kanban status** | Shared `.ralph/kanban.md` with file-locked status markers (`[=]`, `[x]`, `[*]`, `[P]`). Any agent can read task status set by any other agent. | `lib/tasks/task-parser.sh` |
| 7 | **Reports, summaries, and logs** | Markdown reports (`reports/`), iteration summaries (`summaries/`), and conversation logs (`logs/`) in the shared worker directory are readable by any agent. | worker directory convention |

### Architectural Notes

- **No message broker.** All communication is file-based (POSIX filesystem + `flock` for atomicity).
- **Worker directory = shared memory.** The worker dir is the namespace boundary for inter-agent state.
- **Epoch naming prevents collisions.** Multiple runs of the same agent produce distinct result files.
- **Read-only agents are safe.** `readonly: true` agents get a git checkpoint that is restored after they exit, preventing unintended state leakage.

## Worker Directory Structure

```
.ralph/workers/worker-TASK-001-1234567890/
├── prd.md                    # Input: Product Requirements Document
├── workspace/                # Git worktree for isolated work
├── agent.pid                 # PID of running agent
├── results/
│   ├── 1705312200-engineering.security-audit-result.json   # Gate decision + metadata
│   ├── 1705312500-engineering.security-fix-result.json     # Gate decision + metadata
│   ├── 1705312800-engineering.validation-review-result.json
│   └── 1705313100-system.task-worker-result.json
├── reports/
│   ├── 1705312200-engineering.security-audit-report.md     # Analysis output
│   ├── 1705312500-engineering.security-fix-report.md       # Status output
│   └── 1705312800-engineering.validation-review-report.md
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

**Naming Convention:** `results/<epoch>-<agent-type>-result.json` and `reports/<epoch>-<agent-type>-report.md` where epoch is the unix timestamp at agent start.

## Result Communication

### Epoch-Named Result Files

All agent results are written to epoch-named JSON files in `results/`:

```json
{
  "agent_type": "engineering.security-audit",
  "status": "success",
  "exit_code": 0,
  "started_at": "2024-01-15T10:30:00Z",
  "completed_at": "2024-01-15T10:45:00Z",
  "duration_seconds": 900,
  "task_id": "TASK-001",
  "worker_id": "worker-TASK-001-abc123",
  "iterations_completed": 3,
  "outputs": {
    "gate_result": "PASS"
  },
  "errors": [],
  "metadata": {}
}
```

The `outputs.gate_result` field contains the standardized gate decision (PASS/FAIL/STOP/SKIP/FIX).

### Writing Results

```bash
# Write result with gate_result in outputs
agent_write_result "$worker_dir" "success" 0 '{"gate_result":"PASS"}'

# Write result with additional output fields
local outputs_json='{"gate_result":"PASS","pr_url":"https://github.com/..."}'
agent_write_result "$worker_dir" "success" 0 "$outputs_json"

# Write a report (analysis/status markdown)
agent_write_report "$worker_dir" "$report_content"
```

### Reading Results

```bash
# Read gate_result from a sub-agent (2-arg signature)
result=$(agent_read_subagent_result "$worker_dir" "engineering.security-audit")

# Find the latest result file for an agent type
result_file=$(agent_find_latest_result "$worker_dir" "engineering.security-audit")

# Find the latest report file for an agent type
report_file=$(agent_find_latest_report "$worker_dir" "engineering.security-audit")
```

### Gate Result Values

All gate agents produce a `gate_result` field with one of four standardized values, PASS, FIX, FAIL, or SKIP.

| Agent | gate_result Values |
|-------|-------------------|
| engineering.validation-review | PASS, FAIL |
| engineering.security-audit | PASS, FIX, STOP |
| engineering.code-review | PASS, FAIL, FIX |
| engineering.test-coverage | PASS, FAIL, SKIP |
| product.documentation-writer | PASS, SKIP |
| engineering.security-fix | PASS, FIX, FAIL |
| engineering.git-conflict-resolver | PASS, FAIL, SKIP |
| engineering.pr-comment-fix | PASS, FIX, FAIL, SKIP |
| product.plan-mode | PASS, FAIL |
| system.resume-decide | PASS, STOP, FAIL |

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
# Parent agent (system/task-worker.sh)
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"

    # ... main work ...

    # Invoke validation as sub-agent
    run_sub_agent "engineering.validation-review" "$worker_dir" "$project_dir"

    # Read sub-agent gate_result (2-arg signature)
    local result
    result=$(agent_read_subagent_result "$worker_dir" "engineering.validation-review")

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
source "$WIGGUM_HOME/lib/utils/event-emitter.sh"

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
| `[=]` | In Progress | system.task-worker start |
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

1. **Always use epoch-named results** - Use `agent_write_result` which writes to `results/<epoch>-<type>-result.json`
2. **Write checkpoints regularly** - Enables resume after interruption
3. **Emit events for observability** - Makes debugging easier
4. **Use file locks for shared resources** - Prevents race conditions
5. **Respect workspace boundaries** - Never modify files outside workspace
6. **Read before assuming** - Check if result file exists before reading
