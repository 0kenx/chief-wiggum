# Architecture

This document describes the internal architecture of Chief Wiggum for developers who want to understand, extend, or debug the system.

## Directory Structure

```
chief-wiggum/
├── bin/                    # CLI entry points (17 commands)
│   ├── wiggum              # Main dispatcher
│   ├── wiggum-clean        # Cleanup utility
│   ├── wiggum-doctor       # Pre-flight health checks
│   ├── wiggum-init         # Project initialization
│   ├── wiggum-inspect      # Worker/pipeline inspection
│   ├── wiggum-kill         # Force kill workers (SIGKILL)
│   ├── wiggum-monitor      # Real-time log viewer / TUI
│   ├── wiggum-plan         # Read-only implementation planning
│   ├── wiggum-resume       # Resume stopped workers
│   ├── wiggum-review       # PR/task review management
│   ├── wiggum-run          # Orchestrator (continuous loop)
│   ├── wiggum-service      # Service management CLI
│   ├── wiggum-start        # Single worker spawner
│   ├── wiggum-status       # Worker status display
│   ├── wiggum-stop         # Graceful worker stop (SIGTERM)
│   ├── wiggum-util         # Utility subcommands
│   └── wiggum-validate     # Kanban validator
├── lib/
│   ├── agents/             # Agent implementations
│   │   ├── system/         # Core system agents
│   │   ├── engineering/    # Code quality agents
│   │   └── product/        # Product/docs agents
│   ├── claude/             # Claude Code invocation
│   ├── core/               # Shared utilities
│   ├── git/                # Git operations
│   ├── pipeline/           # Pipeline engine
│   ├── tasks/              # Kanban parsing
│   ├── utils/              # Logging, metrics
│   ├── worker/             # Worker lifecycle
│   ├── scheduler/          # Task scheduling, PR merge optimization
│   └── service/            # Service-based scheduler (systemd-like)
├── config/
│   ├── pipeline.json       # Default pipeline
│   ├── agents.json         # Agent registry
│   ├── services.json       # Service definitions
│   └── schemas/            # JSON schemas
├── tests/                  # Test suite
└── docs/                   # Documentation
```

## Component Overview

### Orchestrator (`bin/wiggum`)

The main entry point that:
1. Parses the Kanban board (`.ralph/kanban.md`)
2. Identifies pending tasks
3. Spawns workers up to the concurrency limit
4. Monitors worker completion
5. Updates task status in Kanban

### Workers

Each worker is an isolated process that:
1. Runs in a dedicated git worktree (`.ralph/workers/worker-TASK-XXX-<timestamp>/`)
2. Executes a pipeline of agents
3. Creates a PR on completion
4. Reports status back to orchestrator

Workers are fully isolated—they share no state and can run in parallel.

### Pipeline Engine

The pipeline (`lib/pipeline/`) is a jump-based state machine that sequences agent execution.

```
┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐
│ planning │───►│execution │───►│  audit   │───►│   test   │───►...
└──────────┘    └──────────┘    └──────────┘    └──────────┘
                     │               │
                     │ FAIL          │ FIX
                     ▼               ▼
                  [abort]       [audit-fix]
                                     │
                                     │ re-run parent
                                     ▼
                                 [audit]
```

Key concepts:
- **Steps**: Ordered array of agent invocations
- **on_result**: Per-result handlers (jump or inline agent)
- **max**: Visit limit to prevent infinite loops
- **on_max**: Fallback target when max exceeded (default: `next`)

See [PIPELINE-SCHEMA.md](PIPELINE-SCHEMA.md) for the full specification.

### Agents

Agents are bash scripts that implement a standard interface:

```bash
agent_run(worker_dir, project_dir, workspace, output_dir)
```

Agents invoke Claude Code to perform work. Each agent focuses on a single responsibility:

| Agent | Purpose |
|-------|---------|
| `engineering.software-engineer` | Main implementation work via Ralph Loop |
| `system.task-summarizer` | Generate completion summary |
| `engineering.security-audit` | Security review (readonly) |
| `engineering.security-fix` | Fix security issues |
| `engineering.test-coverage` | Run and fix tests |
| `engineering.validation-review` | Final validation against PRD |
| `product.plan-mode` | Interactive planning (optional) |
| `product.documentation-writer` | Update docs |

See [AGENT_DEV_GUIDE.md](AGENT_DEV_GUIDE.md) for writing custom agents.

## Claude Invocation Patterns

Agents invoke Claude Code through three patterns in `lib/claude/`:

### 1. Single Execution (`run-claude-once.sh`)

One-shot prompts with no session continuity:

```bash
run_agent_once "$workspace" "$system_prompt" "$user_prompt" "$output_file" "$max_turns"
```

Used for: validation, summarization, simple tasks.

### 2. Ralph Loop (`run-claude-ralph-loop.sh`)

Iterative work with context preservation between iterations:

```bash
run_ralph_loop "$workspace" "$system_prompt" \
    "_user_prompt_callback" \
    "_completion_check_callback" \
    "$max_iterations" "$max_turns" "$output_dir"
```

Each iteration:
1. Check completion callback
2. Generate prompt via callback
3. Claude executes with turn limit
4. Resume session to generate summary
5. Summary becomes context for next iteration

This prevents context bloat by starting fresh sessions while carrying forward summaries.

### 3. Supervised Ralph Loop (`run-claude-ralph-loop-supervised.sh`)

Ralph Loop with periodic intervention checkpoints:

```bash
run_ralph_loop_supervised "$workspace" "$system_prompt" \
    "_user_prompt_callback" \
    "_completion_check_callback" \
    "$max_iterations" "$max_turns" "$output_dir" \
    "$supervisor_interval" "$supervisor_agent"
```

Every N iterations, a supervisor agent reviews progress and can redirect work.

## Data Flow

### Task Lifecycle

```
┌─────────────────────────────────────────────────────────────────┐
│                        ORCHESTRATOR                              │
│  .ralph/kanban.md ──► Task Parser ──► Worker Spawner            │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                          WORKER                                  │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │ Git Worktree: .ralph/workers/worker-TASK-XXX-<ts>/      │    │
│  │   ├── workspace/     # Cloned project                    │    │
│  │   ├── prd.md         # Generated requirements            │    │
│  │   ├── output/        # Agent outputs                     │    │
│  │   └── activity.jsonl # Event log                         │    │
│  └─────────────────────────────────────────────────────────┘    │
│                              │                                   │
│                              ▼                                   │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                    PIPELINE                              │    │
│  │  planning ─► execution ─► summary ─► audit ─► test ─►...│    │
│  └─────────────────────────────────────────────────────────┘    │
│                              │                                   │
│                              ▼                                   │
│                         Create PR                                │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                        ORCHESTRATOR                              │
│              Update kanban: [ ] ──► [=] ──► [x]                 │
└─────────────────────────────────────────────────────────────────┘
```

### Agent Execution

```
┌─────────────────────────────────────────────────────────────────┐
│                         AGENT                                    │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                    RALPH LOOP                            │    │
│  │  ┌──────────┐    ┌──────────┐    ┌──────────┐           │    │
│  │  │ Iter 0   │───►│ Iter 1   │───►│ Iter N   │           │    │
│  │  │ Work     │    │ Work     │    │ Work     │           │    │
│  │  │ Summary  │    │ Summary  │    │ Summary  │           │    │
│  │  └──────────┘    └──────────┘    └──────────┘           │    │
│  │       │               │               │                  │    │
│  │       ▼               ▼               ▼                  │    │
│  │   [context]──────►[context]──────►[context]              │    │
│  └─────────────────────────────────────────────────────────┘    │
│                              │                                   │
│                              ▼                                   │
│                    Gate Result: PASS/FAIL/FIX                    │
└─────────────────────────────────────────────────────────────────┘
```

## File Conventions

### Worker Directory

```
.ralph/workers/worker-TASK-001-1234567890/
├── workspace/              # Git worktree (project clone)
├── prd.md                  # Product requirements document
├── output/                 # Agent outputs
│   ├── execution/          # Per-agent output directories
│   ├── audit/
│   └── ...
├── pipeline-config.json    # Full pipeline config with all steps and runtime context
├── activity.jsonl          # Event log (NDJSON)
├── agent.pid               # Running agent PID
└── gate_result             # Last agent result (PASS/FAIL/FIX/SKIP)
```

### Activity Log Format

Events are logged to `activity.jsonl` in NDJSON format:

```json
{"ts":"2024-01-15T10:30:00Z","event":"step.started","step":"execution","agent":"engineering.software-engineer"}
{"ts":"2024-01-15T10:35:00Z","event":"step.completed","step":"execution","result":"PASS"}
```

## Configuration

### Pipeline Configuration

`config/pipeline.json` defines the agent sequence:

```json
{
  "name": "default",
  "steps": [
    {"id": "execution", "agent": "engineering.software-engineer", "max": 3},
    {"id": "audit", "agent": "engineering.security-audit", "readonly": true}
  ]
}
```

Override per-project in `.ralph/pipeline.json` or per-task in `.ralph/pipelines/<task-id>.json`.

### Agent Registry

`config/agents.json` maps agent names to implementations:

```json
{
  "engineering.software-engineer": "lib/agents/engineering/software-engineer.md",
  "engineering.security-audit": "lib/agents/engineering/security-audit.sh"
}
```

### Configuration Precedence

Configuration follows a precedence hierarchy (later overrides earlier):

1. **Defaults** (`config/pipeline.json`, `config/agents.json`)
2. **Project overrides** (`.ralph/config.json`, `.ralph/pipeline.json`)
3. **Task-specific overrides** (`.ralph/pipelines/<TASK-ID>.json`)
4. **Environment variables** (`WIGGUM_*` prefix)

Environment variable naming convention for agent config:
```bash
WIGGUM_{AGENT_NAME}_MAX_ITERATIONS   # e.g., WIGGUM_SECURITY_AUDIT_MAX_ITERATIONS
WIGGUM_{AGENT_NAME}_MAX_TURNS        # e.g., WIGGUM_TEST_COVERAGE_MAX_TURNS
```

### Markdown Agent Discovery

Agents can be defined in two formats with automatic discovery:

1. **Markdown agents** (`lib/agents/<category>/<name>.md`) - Declarative definition
2. **Shell agents** (`lib/agents/<category>/<name>.sh`) - Imperative implementation

Discovery order for `engineering.software-engineer`:
1. Check for `lib/agents/engineering/software-engineer.md`
2. Check for `lib/agents/engineering/software-engineer.sh`
3. If both exist: shell script is loaded, markdown provides base behavior

Markdown agents use a structured format:
```markdown
# Agent: engineering.software-engineer

## Purpose
Main implementation agent

## System Prompt
<system-prompt>
You are a senior software engineer...
</system-prompt>

## User Prompt Template
<user-prompt>
Work on the task: {{task_id}}
</user-prompt>
```

## Key Libraries

| Library | Purpose |
|---------|---------|
| `lib/core/logger.sh` | Structured logging with levels |
| `lib/core/exit-codes.sh` | Standardized exit codes |
| `lib/core/file-lock.sh` | File-based locking |
| `lib/pipeline/pipeline-loader.sh` | Load and validate pipeline config |
| `lib/pipeline/pipeline-runner.sh` | Execute pipeline state machine |
| `lib/worker/agent-registry.sh` | Resolve agent names to scripts |
| `lib/worker/agent-runner.sh` | Agent lifecycle management |
| `lib/claude/run-claude-ralph-loop.sh` | Iterative Claude execution |
| `lib/git/worktree-helpers.sh` | Git worktree operations |
| `lib/tasks/task-parser.sh` | Kanban markdown parsing |
| `lib/utils/activity-log.sh` | Event logging |
| `lib/scheduler/pr-merge-optimizer.sh` | Global PR merge optimization |
| `lib/scheduler/conflict-queue.sh` | Multi-PR conflict batching |
| `lib/scheduler/conflict-registry.sh` | Per-file conflict tracking |
| `lib/service/service-loader.sh` | Load service JSON configuration |
| `lib/service/service-scheduler.sh` | Service timing and execution |
| `lib/service/service-runner.sh` | Execute services by type |
| `lib/service/service-state.sh` | Persist service state |

## Exit Codes

Defined in `lib/core/exit-codes.sh`:

| Code | Meaning |
|------|---------|
| 0 | Success |
| 1 | General error |
| 2 | Invalid arguments |
| 3 | Configuration error |
| 4 | Git error |
| 5 | Claude error |
| 10 | Agent FAIL result |
| 12 | Max iterations exceeded |

## Testing

Run the test suite:

```bash
./tests/test-runner.sh           # All tests
bash tests/test_pipeline_*.sh    # Pipeline tests only
```

Tests use a lightweight assertion framework defined in each test file.

## Debugging

### Inspect Command

The `wiggum inspect` command provides debugging utilities:

```bash
# Inspect a worker's state
wiggum inspect worker TASK-001

# Show pipeline configuration
wiggum inspect pipeline
wiggum inspect pipeline config/pipeline.json

# List available agents with configs
wiggum inspect agents

# View activity log (global or per-worker)
wiggum inspect activity
wiggum inspect activity TASK-001

# Show current pipeline step for a worker
wiggum inspect step TASK-001
```

### Verbose Logging

```bash
WIGGUM_LOG_LEVEL=debug wiggum run
```

### Manual Inspection

```bash
# List active workers
ls -la .ralph/workers/

# View worker logs
tail -f .ralph/workers/worker-TASK-001-*/output/*/claude.log

# Check activity log
cat .ralph/workers/worker-TASK-001-*/activity.jsonl | jq .
```

### Manual Pipeline Execution

```bash
# Load pipeline functions
source lib/pipeline/pipeline-loader.sh
source lib/pipeline/pipeline-runner.sh

# Load a pipeline
pipeline_load config/pipeline.json

# Inspect loaded state
echo "Steps: $(pipeline_step_count)"
echo "Step 0: $(pipeline_get_id 0) -> $(pipeline_get_agent 0)"
```

## PR Merge Optimization

When multiple PRs from different workers need to be merged, the orchestrator uses a global optimization strategy to maximize successful merges and minimize conflicts.

### The Problem

Naive per-PR processing leads to suboptimal decisions:

```
Task A: Check conflicts → "No conflicts" → Merge ✓
Task B: Check conflicts → "Conflict with main!" (because A just merged)
Task C: Check conflicts → "Multi-PR conflict!" (sees B but A already gone)
```

Each PR is evaluated in isolation without knowledge of the global state.

### The Solution

The PR Merge Optimizer (`lib/scheduler/pr-merge-optimizer.sh`) implements a five-phase approach:

```
┌─────────────────────────────────────────────────────────────────┐
│                    pr_merge_optimize_and_execute                │
└─────────────────────────────────────────────────────────────────┘
                              │
        ┌─────────────────────┼─────────────────────┐
        ▼                     ▼                     ▼
┌───────────────┐    ┌───────────────┐    ┌───────────────┐
│  Phase 1:     │    │  Phase 2:     │    │  Phase 3:     │
│  GATHER       │───▶│  ANALYZE      │───▶│  OPTIMIZE     │
│               │    │               │    │               │
│ • Sync all PRs│    │ • Build       │    │ • Calculate   │
│ • Get files   │    │   conflict    │    │   priority    │
│   modified    │    │   graph       │    │   scores      │
│ • Check merge │    │ • Find file   │    │ • Sort by     │
│   status      │    │   overlaps    │    │   merge-first │
└───────────────┘    └───────────────┘    └───────────────┘
                                                  │
        ┌─────────────────────────────────────────┘
        ▼
┌───────────────┐    ┌───────────────┐
│  Phase 4:     │    │  Phase 5:     │
│  EXECUTE      │───▶│  RESOLVE      │
│               │    │               │
│ • Multi-pass  │    │ • Categorize  │
│   merge loop  │    │   remaining:  │
│ • Re-evaluate │    │   - needs_fix │
│   after each  │    │   - needs_    │
│   merge       │    │     resolve   │
│ • Until no    │    │   - needs_    │
│   progress    │    │     multi_    │
└───────────────┘    │     resolve   │
                     └───────────────┘
```

### Phase Details

#### Phase 1: Gather

Collects comprehensive data for ALL pending PRs before making any decisions:

```bash
pr_merge_gather_all "$ralph_dir" "$project_dir"
```

For each `[P]` status task:
- Sync PR comments from GitHub
- Get list of files modified (compared to merge-base with main)
- Check if PR has new unaddressed comments
- Check if Copilot has reviewed
- Test merge-ability against current main
- Record any conflict files

#### Phase 2: Analyze

Builds a conflict graph showing which PRs conflict with each other:

```bash
pr_merge_build_conflict_graph "$ralph_dir"
```

Two PRs conflict if they modify any of the same files:

```
PR_A modifies: [src/api.ts, src/utils.ts]
PR_B modifies: [src/api.ts, tests/api.test.ts]
PR_C modifies: [docs/README.md]

Conflict Graph:
  A ←──→ B  (both modify src/api.ts)
  C       (independent - no conflicts)
```

#### Phase 3: Optimize

Uses **Maximum Independent Set (MIS)** dynamic programming to find the optimal merge batch:

```bash
pr_merge_find_optimal_order "$ralph_dir"
```

**Algorithm**: This is the Maximum Independent Set problem on the conflict graph.
- For n ≤ 18 PRs: Exact bitmask DP solution (O(2^n) subsets)
- For n > 18 PRs: Greedy approximation (minimum degree heuristic)

**MIS Selection Criteria** (in order of priority):
1. Maximize count of currently-mergeable PRs in the set
2. Maximize total PRs in the set

**Example** - Chain conflict A↔B↔C:
```
Conflict graph:     A ── B ── C

MIS options:        {A, C} ✓  (size 2, no internal conflicts)
                    {B}       (size 1)
                    {A}, {C}  (size 1 each)

Optimal: {A, C} - merge both in one pass
```

Within the MIS, PRs are ordered by a tiebreaker priority:
| Factor | Score Impact |
|--------|--------------|
| Base score | +1000 |
| Per conflict with other PR | -50 |
| Per file modified | -10 |

Simpler PRs (fewer files, fewer conflicts) merge first within the batch.

#### Phase 4: Execute

Merges PRs in the optimized order with re-evaluation:

```bash
pr_merge_execute "$ralph_dir" "$project_dir"
```

```
Pass 1:
  TASK-004: Mergeable → Merge ✓
  TASK-002: Mergeable → Merge ✓
  TASK-001: Has conflicts → Skip

  [Re-evaluate remaining PRs against new main]

Pass 2:
  TASK-001: Now mergeable! → Merge ✓
  TASK-003: Still has conflicts → Skip

Pass 3:
  TASK-003: Still has conflicts → Stop
```

The multi-pass loop continues until no more PRs can be merged.

#### Phase 5: Resolve

Categorizes remaining PRs and queues them for appropriate handling:

```bash
pr_merge_handle_remaining "$ralph_dir"
```

| Category | Condition | Action |
|----------|-----------|--------|
| `needs_fix` | Has unaddressed PR comments | Queue for fix pipeline |
| `needs_resolve` | Conflicts only with main | Queue for simple rebase |
| `needs_multi_resolve` | Conflicts with other unmerged PRs | Queue for coordinated resolution |
| `waiting` | Awaiting Copilot review | No action, check next cycle |

### State File

The optimizer maintains state in `.ralph/pr-merge-state.json`:

```json
{
  "prs": {
    "FEAT-001": {
      "pr_number": 20,
      "worker_dir": "/path/to/worker",
      "branch": "feat-001-branch",
      "files_modified": ["src/api.ts", "src/utils.ts"],
      "base_commit": "abc123",
      "has_new_comments": false,
      "copilot_reviewed": true,
      "mergeable_to_main": false,
      "conflict_files_with_main": ["src/api.ts"]
    }
  },
  "conflict_graph": {
    "FEAT-001": ["FEAT-003"],
    "FEAT-003": ["FEAT-001"]
  },
  "optimal_batch": ["TEST-002", "TEST-003"],
  "merge_order": ["TEST-002", "TEST-003", "FEAT-003", "FEAT-001"],
  "merged_this_cycle": ["TEST-002"],
  "last_updated": "2024-01-27T12:00:00Z"
}
```

| Field | Description |
|-------|-------------|
| `prs` | Per-PR metadata including files modified and merge status |
| `conflict_graph` | Adjacency list of PR conflicts (bidirectional) |
| `optimal_batch` | Maximum Independent Set - PRs that can merge without conflicts |
| `merge_order` | Full ordering: MIS first, then remaining PRs |
| `merged_this_cycle` | PRs successfully merged in this optimization run |

### Integration

The optimizer is called from `wiggum-run` at startup and during periodic sync:

```bash
# In _schedule_pending_pr_fixes()
pr_merge_optimize_and_execute "$RALPH_DIR" "$PROJECT_DIR"
```

### Debugging

```bash
# View current optimizer state
cat .ralph/pr-merge-state.json | jq .

# Check conflict graph
jq '.conflict_graph' .ralph/pr-merge-state.json

# See merge order
jq '.merge_order' .ralph/pr-merge-state.json

# Check which PRs were merged
jq '.merged_this_cycle' .ralph/pr-merge-state.json
```

## Service Scheduler (Optional)

The service scheduler (`lib/service/`) provides a systemd-like approach to orchestrator responsibilities. Instead of hardcoded intervals and counter-based scheduling, periodic tasks are defined as declarative "services" with configurable intervals.

### Enabling

Enable via environment variable:

```bash
WIGGUM_USE_SERVICE_SCHEDULER=true wiggum run
```

### Architecture

```
┌─────────────────────────────────────────────────────┐
│              SERVICE SCHEDULER                       │
│  ┌───────────────────────────────────────────────┐  │
│  │      config/services.json (declarative)       │  │
│  └───────────────────────────────────────────────┘  │
│                        │                            │
│    ┌───────────┬───────┴───────┬───────────┐       │
│    ▼           ▼               ▼           ▼       │
│ pr-sync   pr-optimizer   task-spawner  worker-cleanup │
│ (180s)      (900s)         (60s)        (60s)      │
└─────────────────────────────────────────────────────┘
```

### Modules

| Module | Purpose |
|--------|---------|
| `lib/service/service-loader.sh` | Load and validate JSON configs |
| `lib/service/service-state.sh` | Persist state across restarts |
| `lib/service/service-scheduler.sh` | Timing and execution coordination |
| `lib/service/service-runner.sh` | Execute services by type |

### Service Configuration

Services are defined in `config/services.json`:

```json
{
  "version": "1.0",
  "defaults": {
    "timeout": 300,
    "concurrency": { "max_instances": 1, "if_running": "skip" }
  },
  "services": [
    {
      "id": "pr-sync",
      "description": "Sync PR statuses from GitHub",
      "schedule": { "type": "interval", "interval": 180, "run_on_startup": true },
      "execution": { "type": "function", "function": "orch_run_periodic_sync" }
    },
    {
      "id": "task-spawner",
      "schedule": { "type": "interval", "interval": 60 },
      "execution": { "type": "function", "function": "orch_spawn_ready_tasks" }
    }
  ]
}
```

### Schedule Types

| Type | Description | Example |
|------|-------------|---------|
| `interval` | Run at fixed intervals | `{"type": "interval", "interval": 60}` |
| `event` | Run when triggered | `{"type": "event", "trigger": "worker.completed"}` |
| `continuous` | Run continuously | `{"type": "continuous", "restart_delay": 5}` |

### Execution Types

| Type | Description | Example |
|------|-------------|---------|
| `function` | Call a bash function | `{"type": "function", "function": "my_func"}` |
| `command` | Run shell command | `{"type": "command", "command": "wiggum-review sync"}` |

### Project Overrides

Override or add services per-project via `.ralph/services.json`:

```json
{
  "version": "1.0",
  "services": [
    {
      "id": "pr-sync",
      "schedule": { "type": "interval", "interval": 300 }
    },
    {
      "id": "custom-service",
      "enabled": true,
      "schedule": { "type": "interval", "interval": 120 },
      "execution": { "type": "command", "command": "./scripts/my-task.sh" }
    }
  ]
}
```

### Service CLI

Manage services via `wiggum service`:

```bash
# List all services
wiggum service list

# Check service status
wiggum service status
wiggum service status pr-sync

# Manually trigger a service
wiggum service run pr-sync
wiggum service run pr-sync --sync  # Wait for completion

# Stop a running service
wiggum service stop pr-sync

# View service configuration
wiggum service config pr-sync
```

### State Persistence

Service state is stored in `.ralph/.service-state.json`:

```json
{
  "saved_at": "2024-01-27T12:00:00Z",
  "services": {
    "pr-sync": {
      "last_run": 1706356800,
      "status": "stopped",
      "run_count": 42,
      "fail_count": 1
    }
  }
}
```

State survives orchestrator restarts, allowing services to resume where they left off.

### Comparison

| Aspect | Counter-Based (Default) | Service-Based |
|--------|------------------------|---------------|
| Configuration | Hardcoded in wiggum-run | Declarative JSON |
| Adding tasks | Modify core loop | Add to services.json |
| Per-project intervals | Environment variables | .ralph/services.json |
| Observability | Log inspection | `wiggum service status` |
| State persistence | None | Automatic |

### Debugging

```bash
# View service state
cat .ralph/.service-state.json | jq .

# Check which services are due
wiggum service status --json | jq '.[] | select(.status != "running")'

# View service configuration
wiggum service config --json | jq '.[] | {id, interval: .schedule.interval}'
```
