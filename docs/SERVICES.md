# Services Specification

This document provides the complete specification for the Chief Wiggum service scheduler system.

## Overview

The service scheduler (`lib/service/`) provides a systemd-like approach to orchestrator responsibilities. Periodic tasks are defined as declarative "services" with configurable schedules, execution types, and advanced features like circuit breakers and health checks.

### Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                      SERVICE SCHEDULER                          │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │         config/services.json (declarative config)          │  │
│  │              .ralph/services.json (overrides)              │  │
│  └───────────────────────────────────────────────────────────┘  │
│                              │                                   │
│       ┌──────────────────────┼──────────────────────┐           │
│       ▼                      ▼                      ▼           │
│  service-loader.sh     service-scheduler.sh    service-runner.sh │
│  (config parsing)      (timing/coordination)   (execution)       │
│                              │                                   │
│                      service-state.sh                            │
│                    (persistence/recovery)                        │
└─────────────────────────────────────────────────────────────────┘
```

### Modules

| Module | Lines | Purpose |
|--------|-------|---------|
| `lib/service/service-loader.sh` | 982 | Load and validate service JSON configuration |
| `lib/service/service-scheduler.sh` | 890 | Service timing, interval calculation, execution coordination |
| `lib/service/service-runner.sh` | 800+ | Execute services by type (command, function, pipeline, agent) |
| `lib/service/service-state.sh` | 870 | Persistent state management for scheduler recovery |

---

## Configuration Schema

Service configuration uses JSON Schema draft 2020-12. The full schema is at `config/schemas/service.schema.json`.

### Root Structure

```json
{
  "version": "2.0",
  "defaults": { ... },
  "groups": { ... },
  "services": [ ... ]
}
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `version` | string | Yes | Schema version (`"1.0"`, `"1.1"`, or `"2.0"`) |
| `defaults` | object | No | Default configuration applied to all services |
| `groups` | object | No | Named groups for bulk operations |
| `services` | array | Yes | Array of service definitions |

### Defaults

```json
{
  "defaults": {
    "timeout": 300,
    "restart_policy": {
      "on_failure": "skip",
      "max_retries": 2,
      "backoff": {
        "initial": 5,
        "multiplier": 2,
        "max": 300
      }
    },
    "circuit_breaker": {
      "enabled": false,
      "threshold": 5,
      "cooldown": 300,
      "half_open_requests": 1
    }
  }
}
```

---

## Service Definition

Each service requires `id`, `schedule`, and `execution` fields.

### Required Fields

| Field | Type | Description |
|-------|------|-------------|
| `id` | string | Unique identifier (pattern: `^[a-z][a-z0-9_-]*$`) |
| `schedule` | object | When to run the service |
| `execution` | object | How to run the service |

### Optional Fields

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `description` | string | - | Human-readable description |
| `enabled` | boolean | `true` | Whether the service is enabled |
| `phase` | string | `"periodic"` | Execution phase (v2.0): `startup`, `pre`, `periodic`, `post`, `shutdown` |
| `order` | integer | `50` | Execution order within phase (lower = first, v2.0) |
| `required` | boolean | `false` | Abort orchestrator on failure (startup/shutdown only, v2.0) |
| `groups` | array | `[]` | Groups this service belongs to |
| `depends_on` | array | `[]` | Services that must complete first |
| `condition` | object | - | Conditions for execution |
| `concurrency` | object | - | Concurrency control |
| `timeout` | integer | `300` | Execution timeout in seconds |
| `restart_policy` | object | - | Failure handling policy |
| `circuit_breaker` | object | - | Circuit breaker configuration |
| `health` | object | - | Health check configuration |
| `limits` | object | - | Resource limits |
| `metrics` | object | - | Metrics collection settings |

### Phases (v2.0)

Services are organized into five execution phases:

| Phase | When | Execution Model |
|-------|------|-----------------|
| `startup` | Once, before main loop | Sequential by `order`, synchronous. Failure in `required` service aborts orchestrator. |
| `pre` | Every tick, before periodic | Sequential by `order`, synchronous (direct function call). |
| `periodic` | Interval/cron/event-based | Dispatched by service scheduler (subprocess, async). |
| `post` | Every tick, after periodic | Sequential by `order`, synchronous (direct function call). |
| `shutdown` | Once, on exit | Sequential by reverse `order`, synchronous. |

**Pre/post tick services** run synchronously because they are file I/O operations completing in <10ms. The scheduler calls `svc_*` functions directly — no subprocess fork. Each function reads files, does work, writes files, with no shared in-process state.

**Startup/shutdown** services run sequentially. A `required: true` startup service that fails aborts the orchestrator. Shutdown services run in reverse order.

### Example Service

```json
{
  "id": "pr-sync",
  "description": "Sync PR statuses and detect new comments",
  "enabled": true,
  "groups": ["github", "sync"],
  "schedule": {
    "type": "interval",
    "interval": 180,
    "jitter": 10,
    "run_on_startup": true
  },
  "execution": {
    "type": "command",
    "command": "wiggum-review sync"
  },
  "concurrency": {
    "max_instances": 1,
    "if_running": "skip"
  },
  "timeout": 120,
  "circuit_breaker": {
    "enabled": true,
    "threshold": 3,
    "cooldown": 600
  }
}
```

---

## Schedule Types

### Interval Schedule

Run at fixed time intervals.

```json
{
  "type": "interval",
  "interval": 60,
  "jitter": 5,
  "run_on_startup": true
}
```

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `type` | const | Yes | - | Must be `"interval"` |
| `interval` | integer | Yes | - | Interval in seconds between executions |
| `jitter` | integer | No | `0` | Random jitter in seconds (prevents thundering herd) |
| `run_on_startup` | boolean | No | `false` | Run immediately on scheduler startup |

### Cron Schedule

Run based on cron expressions.

```json
{
  "type": "cron",
  "cron": "0 */6 * * *",
  "timezone": "America/New_York",
  "run_on_startup": false
}
```

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `type` | const | Yes | - | Must be `"cron"` |
| `cron` | string | Yes | - | Cron expression (minute hour day month weekday) |
| `timezone` | string | No | `"UTC"` | Timezone for cron evaluation |
| `run_on_startup` | boolean | No | `false` | Run immediately on startup |

**Cron Expression Format**: `minute hour day month weekday`
- Supports: `*`, ranges (`1-5`), lists (`1,3,5`), steps (`*/15`)
- Pattern: `^[0-9*,/-]+\s+[0-9*,/-]+\s+[0-9*,/-]+\s+[0-9*,/-]+\s+[0-9*,/-]+$`

### Event Schedule

Run when a named event is triggered.

```json
{
  "type": "event",
  "trigger": "worker.completed"
}
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `type` | const | Yes | Must be `"event"` |
| `trigger` | string | Yes | Event name that triggers execution |

**Common Events**:
- `worker.completed` - A worker finished execution
- `scheduling_event` - Scheduler tick occurred
- `pr.merged` - A PR was merged
- Custom events via `service_trigger_event()`

### Continuous Schedule

Run continuously, restarting after completion.

```json
{
  "type": "continuous",
  "restart_delay": 5
}
```

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `type` | const | Yes | - | Must be `"continuous"` |
| `restart_delay` | integer | No | `5` | Delay in seconds before restarting |

### Tick Schedule (v2.0)

Run every orchestrator loop iteration (~1s cadence). Tick services execute synchronously as direct function calls (not subprocesses), completing in <10ms. Used for pre/post phase services that do file I/O.

```json
{
  "type": "tick"
}
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `type` | const | Yes | Must be `"tick"` |

No interval or jitter — runs every tick. Only valid with `phase: "pre"` or `phase: "post"`.

---

## Execution Types

### Command Execution

Execute a shell command.

```json
{
  "type": "command",
  "command": "wiggum-review sync",
  "working_dir": "/path/to/dir"
}
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `type` | const | Yes | Must be `"command"` |
| `command` | string | Yes | Shell command to execute |
| `working_dir` | string | No | Working directory for execution |

### Function Execution

Call a Bash function.

```json
{
  "type": "function",
  "function": "svc_orch_spawn_fix_workers",
  "args": ["--verbose", "--dry-run"]
}
```

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `type` | const | Yes | - | Must be `"function"` |
| `function` | string | Yes | - | Bash function name |
| `args` | array | No | `[]` | Arguments to pass |

**Security Restriction**: Only functions with the `svc_*` prefix can be invoked via services. This is enforced by `service-runner.sh`.

### Pipeline Execution

Execute a named pipeline.

```json
{
  "type": "pipeline",
  "pipeline": "security-audit"
}
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `type` | const | Yes | Must be `"pipeline"` |
| `pipeline` | string | Yes | Pipeline name to execute |

### Agent Execution

Execute an agent directly via the agent registry.

```json
{
  "type": "agent",
  "agent": "engineering.security-audit",
  "worker_dir": ".ralph/workers/audit-worker",
  "max_iterations": 10,
  "max_turns": 30,
  "monitor_interval": 60
}
```

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `type` | const | Yes | - | Must be `"agent"` |
| `agent` | string | Yes | - | Agent type (dotted name, e.g., `"system.task-worker"`) |
| `worker_dir` | string | No | auto-generated | Worker directory for agent state |
| `max_iterations` | integer | No | `20` | Maximum outer loop iterations |
| `max_turns` | integer | No | `50` | Maximum turns per Claude session |
| `monitor_interval` | integer | No | `30` | Violation monitor interval in seconds |

**Worker Directory**: If not specified, a directory is auto-generated at `.ralph/workers/service-{id}-{timestamp}/`.

**Example: Scheduled Security Audit**

```json
{
  "id": "scheduled-audit",
  "description": "Run security audit every 6 hours",
  "schedule": {
    "type": "cron",
    "cron": "0 */6 * * *"
  },
  "execution": {
    "type": "agent",
    "agent": "engineering.security-audit",
    "max_iterations": 5,
    "max_turns": 20
  },
  "timeout": 1800,
  "concurrency": {
    "max_instances": 1,
    "if_running": "skip"
  }
}
```

---

## Advanced Features

### Concurrency Control

Control how many instances can run and what to do when already running.

```json
{
  "concurrency": {
    "max_instances": 1,
    "if_running": "queue",
    "queue_max": 10,
    "priority": "high"
  }
}
```

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `max_instances` | integer | `1` | Maximum concurrent instances |
| `if_running` | string | `"skip"` | Action when running: `skip`, `queue`, `kill` |
| `queue_max` | integer | `10` | Max queued executions (when `if_running=queue`) |
| `priority` | string | `"normal"` | Queue priority: `low`, `normal`, `high`, `critical` |

**`if_running` Actions**:
- `skip` - Don't start, wait for next scheduled time
- `queue` - Add to execution queue
- `kill` - Stop the running instance and start new

### Circuit Breaker

Automatically disable services that fail repeatedly.

```json
{
  "circuit_breaker": {
    "enabled": true,
    "threshold": 5,
    "cooldown": 300,
    "half_open_requests": 1
  }
}
```

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `enabled` | boolean | `false` | Enable circuit breaker |
| `threshold` | integer | `5` | Consecutive failures before opening |
| `cooldown` | integer | `300` | Seconds before attempting recovery |
| `half_open_requests` | integer | `1` | Test requests in half-open state |

**Circuit States**:
- `closed` - Normal operation
- `open` - Service disabled due to failures
- `half-open` - Testing if service recovered

### Restart Policy

Configure failure handling behavior.

```json
{
  "restart_policy": {
    "on_failure": "retry",
    "max_retries": 3,
    "backoff": {
      "initial": 5,
      "multiplier": 2,
      "max": 300
    }
  }
}
```

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `on_failure` | string | `"skip"` | Action on failure: `retry`, `skip`, `abort` |
| `max_retries` | integer | `2` | Maximum retry attempts |
| `backoff` | object | - | Exponential backoff configuration |

**Backoff Configuration**:

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `initial` | integer | `5` | Initial delay in seconds |
| `multiplier` | number | `2` | Multiplier per retry |
| `max` | integer | `300` | Maximum delay in seconds |

### Conditional Execution

Only run when conditions are met.

```json
{
  "condition": {
    "file_exists": ".ralph/workers/worker-*",
    "env_set": "GITHUB_TOKEN",
    "env_equals": {
      "WIGGUM_MODE": "production"
    },
    "env_not_equals": {
      "WIGGUM_RUN_MODE": "merge-only"
    },
    "command": "git status --porcelain | grep -q ."
  }
}
```

| Field | Type | Description |
|-------|------|-------------|
| `file_exists` | string | Glob pattern - run only if matches exist |
| `file_not_exists` | string | Glob pattern - run only if no matches |
| `env_set` | string | Environment variable must be set |
| `env_equals` | object | Environment variables must equal values |
| `env_not_equals` | object | Environment variables must NOT equal values (v2.0) |
| `command` | string | Shell command must exit 0 |

All specified conditions must pass for the service to run.

### Health Checks

Monitor service health and detect stuck processes.

```json
{
  "health": {
    "type": "file",
    "path": ".ralph/services/heartbeat",
    "max_age": 60,
    "interval": 30,
    "on_unhealthy": "restart"
  }
}
```

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `type` | string | - | Check type: `file`, `command`, `heartbeat` |
| `path` | string | - | File path for `file` type |
| `command` | string | - | Command for `command` type |
| `max_age` | integer | `60` | Max age in seconds before unhealthy |
| `interval` | integer | `30` | How often to check (seconds) |
| `on_unhealthy` | string | `"log"` | Action: `restart`, `kill`, `log` |

**Health Check Types**:
- `file` - Check file modification time
- `command` - Run command, expect exit 0
- `heartbeat` - Service must call heartbeat function

### Resource Limits

Constrain service resource usage.

```json
{
  "limits": {
    "memory": "512M",
    "cpu": 50,
    "nice": 10,
    "timeout_kill": true
  }
}
```

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `memory` | string | - | Memory limit (e.g., `512M`, `1G`) |
| `cpu` | number | - | CPU limit as percentage (0.1-100) |
| `nice` | integer | `0` | Process niceness (-20 to 19) |
| `timeout_kill` | boolean | `true` | Kill process if timeout exceeded |

### Metrics Configuration

Control metrics collection.

```json
{
  "metrics": {
    "enabled": true,
    "emit_to": "both",
    "include_output": false
  }
}
```

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `enabled` | boolean | `true` | Enable metrics collection |
| `emit_to` | string | `"activity"` | Destination: `activity`, `metrics`, `both` |
| `include_output` | boolean | `false` | Include service output in metrics |

---

## Service Groups

Define named groups for bulk operations.

### Group Definition

```json
{
  "groups": {
    "github": {
      "description": "GitHub-related services",
      "enabled": true
    },
    "cleanup": {
      "description": "Worker cleanup services",
      "enabled": true
    }
  }
}
```

### Assigning Services to Groups

```json
{
  "id": "pr-sync",
  "groups": ["github", "sync"],
  ...
}
```

### Group Operations

```bash
# Disable all services in a group
wiggum service disable-group github

# Enable all services in a group
wiggum service enable-group github
```

---

## Dependencies

Services can depend on other services.

```json
{
  "id": "task-spawner",
  "depends_on": ["pr-sync", "usage-tracker"],
  ...
}
```

A service will only run after all dependencies have completed successfully in the current scheduler tick.

---

## State Management

Service state is persisted to `.ralph/services/state.json`.

### State Structure

```json
{
  "saved_at": "2024-01-27T12:00:00Z",
  "services": {
    "pr-sync": {
      "last_run": 1706356800,
      "status": "stopped",
      "run_count": 42,
      "fail_count": 1,
      "consecutive_failures": 0,
      "circuit_state": "closed",
      "metrics": {
        "total_duration": 3600,
        "success_count": 41,
        "min_duration": 45,
        "max_duration": 120
      }
    }
  },
  "queues": {
    "pr-optimizer": [
      {"priority": "high", "args": [], "queued_at": 1706356800}
    ]
  },
  "backoff": {
    "pr-sync": {
      "attempts": 0,
      "next_allowed": 0
    }
  }
}
```

### Tracked State Per Service

| Field | Description |
|-------|-------------|
| `last_run` | Unix timestamp of last execution |
| `status` | Current status: `stopped`, `running`, `failed`, `skipped` |
| `run_count` | Total successful executions |
| `fail_count` | Total failed executions |
| `consecutive_failures` | Failures since last success |
| `circuit_state` | Circuit breaker state |
| `metrics` | Execution metrics |

---

## Project Overrides

Projects can override or add services via `.ralph/services.json`.

### Override Example

```json
{
  "version": "2.0",
  "services": [
    {
      "id": "pr-sync",
      "schedule": {
        "type": "interval",
        "interval": 300
      }
    },
    {
      "id": "custom-service",
      "enabled": true,
      "phase": "periodic",
      "schedule": {
        "type": "interval",
        "interval": 120
      },
      "execution": {
        "type": "command",
        "command": "./scripts/custom-task.sh"
      }
    }
  ]
}
```

Override rules:
- Existing services: fields are merged (override replaces individual fields)
- New services: added to the service list
- Use `"enabled": false` to disable a default service

---

## CLI Reference

Manage services via `wiggum service`:

### List Services

```bash
wiggum service list
```

Output shows all configured services with intervals and status.

### Service Status

```bash
# Status of all services
wiggum service status

# Status of specific service
wiggum service status pr-sync

# JSON output
wiggum service status --json
```

### Run Service

```bash
# Trigger service (async)
wiggum service run pr-sync

# Trigger and wait for completion
wiggum service run pr-sync --sync
```

### Stop Service

```bash
wiggum service stop pr-sync
```

### View Configuration

```bash
# Single service config
wiggum service config pr-sync

# All services as JSON
wiggum service config --json
```

---

## Security Model

### Function Execution Restriction

The service runner enforces a `svc_*` prefix requirement for function execution:

1. Functions referenced in `execution.function` must start with `svc_`
2. Handler functions are defined in `lib/services/*.sh`
3. Handlers wrap internal functions, providing a security boundary

### Handler Pattern

```bash
# lib/services/orchestrator-handlers.sh

# Thin wrapper around internal function
svc_orch_spawn_fix_workers() {
    orch_spawn_fix_workers "$@"
}
```

This pattern:
- Creates an explicit allowlist of callable functions
- Prevents arbitrary function execution via configuration
- Centralizes all service entry points

### Adding New Handlers

1. Create handler in `lib/services/*.sh` with `svc_*` prefix
2. Implement as thin wrapper around internal function
3. Reference in service configuration

---

## Default Services

The default `config/services.json` defines services organized by phase:

### Startup Phase (run once, sequential)

| ID | Order | Description |
|----|-------|-------------|
| `validate-kanban` | 10 | Validate kanban format |
| `init-scheduler` | 20 | Initialize scheduler, detect dependency cycles |
| `preflight-git` | 30 | Check clean git state, pull main |
| `preflight-ssh` | 40 | Test SSH connection |
| `preflight-gh` | 50 | Test GitHub CLI auth |
| `restore-workers` | 60 | Restore worker pool from worker directories |
| `init-terminal` | 80 | Initialize terminal header |

### Pre Phase (every tick, sequential)

| ID | Order | Description |
|----|-------|-------------|
| `pool-ingest` | 10 | Read pool-pending, merge into pool.json |
| `resume-poll` | 20 | Check pending-resumes.json for finished PIDs |
| `worker-cleanup` | 30 | Reap finished workers, update pool.json |

### Periodic Phase (interval/cron/event-based)

| ID | Interval | Description |
|----|----------|-------------|
| `pr-sync` | 180s | Sync PR statuses and detect new comments |
| `usage-tracker` | 180s | Update shared usage data for rate limiting |
| `orphan-workspace` | 180s | Create workspaces for orphaned PRs |
| `pr-optimizer` | 900s | Optimize and execute PR merges |
| `multi-pr-planner` | 900s | Check for conflict batches |
| `fix-workers` | 60s | Spawn fix workers for PR comment issues |
| `resume-workers` | 300s | Resume stopped WIP workers |
| `resolve-workers` | 60s | Spawn resolve workers for merge conflicts |
| `pr-optimizer-check` | 60s | Check for completed PR optimizer |

### Post Phase (every tick, sequential)

| ID | Order | Description |
|----|-------|-------------|
| `completion-check` | 10 | Write should-exit file if all tasks done |
| `rate-limit-guard` | 20 | Check rate limits, write pause file if needed |
| `scheduler-tick` | 30 | Parse kanban, write scheduler-state.json |
| `task-spawner` | 40 | Read scheduler state, spawn workers |
| `skip-decay` | 50 | Decay skip-tasks.json (every 180 ticks) |
| `orphan-detection` | 60 | Detect orphan workers (every 60 ticks) |
| `aging-update` | 70 | Update task-ready-since aging |
| `status-display` | 80 | Update terminal header |
| `state-save` | 90 | Persist service state.json |

### Shutdown Phase (run once, reverse order)

| ID | Order | Description |
|----|-------|-------------|
| `final-state-save` | 10 | Final service state persistence |
| `terminal-cleanup` | 20 | Clean up terminal header |
| `lock-cleanup` | 30 | Remove orchestrator.pid |

---

## API Reference

### Loader Functions (`service-loader.sh`)

| Function | Description |
|----------|-------------|
| `service_load(file)` | Load and validate service configuration |
| `service_load_override(file)` | Merge project-level overrides |
| `service_get_enabled()` | List enabled service IDs |
| `service_get_by_id(id)` | Get service definition as JSON |
| `service_get_schedule(id)` | Get schedule configuration |
| `service_get_execution(id)` | Get execution configuration |
| `service_get_dependencies(id)` | Get service dependencies |
| `service_get_condition(id)` | Get conditional execution rules |
| `service_get_health_check(id)` | Get health check configuration |
| `service_get_limits(id)` | Get resource limits |
| `service_get_circuit_breaker(id)` | Get circuit breaker configuration |
| `service_get_groups(id)` | Get groups service belongs to |
| `service_get_jitter(id)` | Get jitter for interval scheduling |
| `service_get_backoff(id)` | Get backoff configuration |
| `service_cron_matches_now(expr, tz)` | Check if cron expression matches now |

### Scheduler Functions (`service-scheduler.sh`)

| Function | Description |
|----------|-------------|
| `service_scheduler_init(ralph_dir, project_dir)` | Initialize scheduler, load services |
| `service_scheduler_tick()` | Check and run due periodic services |
| `service_scheduler_run_phase(phase)` | Run all services for a phase (startup/pre/periodic/post/shutdown) |
| `service_is_due(id)` | Check if service should run |
| `service_trigger_event(event, args...)` | Trigger event-based services |
| `service_scheduler_status()` | Get scheduler status summary |
| `service_scheduler_service_status(id)` | Get specific service status |
| `service_scheduler_set_group_enabled(group, enabled)` | Enable/disable groups |

### Runner Functions (`service-runner.sh`)

| Function | Description |
|----------|-------------|
| `service_run(id, args...)` | Execute a service asynchronously |
| `service_run_sync(id, args...)` | Execute service synchronously |
| `service_run_command(cmd, timeout, dir, limits, args)` | Run shell command |
| `service_run_function(func, timeout, args, limits, extra)` | Call bash function |
| `service_wait(id, timeout)` | Wait for background service |
| `service_stop(id, signal)` | Stop a running service |
| `service_stop_all()` | Stop all running services |

### State Functions (`service-state.sh`)

| Function | Description |
|----------|-------------|
| `service_state_init(ralph_dir)` | Initialize state tracking |
| `service_state_save()` | Persist state to disk |
| `service_state_restore()` | Load state from disk |
| `service_state_get_last_run(id)` | Get last run timestamp |
| `service_state_mark_started(id, pid)` | Mark service as started |
| `service_state_mark_completed(id)` | Mark service as completed |
| `service_state_mark_failed(id)` | Mark service as failed |
| `service_state_record_execution(id, duration, exit)` | Record execution metrics |
| `service_state_get_metrics(id)` | Get execution metrics |
| `service_state_queue_add(id, priority, args)` | Add to execution queue |
| `service_state_queue_pop(id)` | Pop from execution queue |
| `service_state_set_circuit_state(id, state)` | Set circuit breaker state |

---

## Debugging

```bash
# View service state
cat .ralph/services/state.json | jq .

# Check which services are due
wiggum service status --json | jq '.[] | select(.status != "running")'

# View service configuration
wiggum service config --json | jq '.[] | {id, interval: .schedule.interval}'

# Enable debug logging
WIGGUM_LOG_LEVEL=debug wiggum run

# Manually trigger with verbose output
wiggum service run pr-sync --sync --verbose
```

