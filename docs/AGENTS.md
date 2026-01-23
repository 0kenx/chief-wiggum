# Agent Development Guide

This document describes how to create and configure agents in Chief Wiggum.

## Overview

Agents are self-contained Bash scripts that implement specific workflows.
There are two agent patterns, each in its own directory:

- **Orchestrator agents** (`lib/agents/pipeline/`) — `task-worker`, `task-worker-plan-mode` —
  manage the full task pipeline, spawn sub-agents, use supervised ralph loops, and handle
  commits/PRs.
- **Leaf agents** (`lib/agents/`) — all others — perform a single focused task (audit,
  review, test, etc.), invoked as sub-agents by orchestrators, using unsupervised ralph
  loops or single-run execution.

## Agent Lifecycle

```
┌─────────────────────────────────────────────────────────────────┐
│                      AGENT LIFECYCLE                            │
├─────────────────────────────────────────────────────────────────┤
│  1. LOADING                                                     │
│     └── Agent script sourced by agent-registry.sh               │
│                                                                 │
│  2. INIT (agent_on_init)                                        │
│     ├── PID file created: $worker_dir/agent.pid                 │
│     ├── Signal handlers registered (INT, TERM)                  │
│     └── Logs directory setup                                    │
│                                                                 │
│  3. PREREQUISITE CHECK (agent_required_paths)                   │
│     └── Validates required files/directories exist              │
│                                                                 │
│  4. READY (agent_on_ready)                                      │
│     └── Custom pre-run initialization                           │
│                                                                 │
│  5. EXECUTION (agent_run)                                       │
│     ├── Main agent logic executes                               │
│     ├── Ralph loop iterations (if applicable)                   │
│     └── Sub-agents may be spawned                               │
│                                                                 │
│  6. OUTPUT VALIDATION (validate_agent_outputs)                  │
│     └── Verifies epoch-named result JSON exists and is valid    │
│                                                                 │
│  7. CLEANUP (agent_cleanup)                                     │
│     ├── Custom cleanup logic                                    │
│     ├── PID file removed                                        │
│     └── Violation monitor stopped                               │
└─────────────────────────────────────────────────────────────────┘
```

## Creating a New Agent

### Step 1: Create Agent File

Create a new file with the naming convention `{agent-name}.sh`:
- Leaf agents → `lib/agents/`
- Orchestrator agents → `lib/agents/pipeline/`

#### Leaf Agent Template (most common)

For agents invoked as sub-agents by the orchestrator (audit, review, test, etc.):

```bash
#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: my-agent
# AGENT_DESCRIPTION: Brief description of what the agent does.
# REQUIRED_PATHS:
#   - workspace : Directory containing the code to operate on
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "my-agent" "Brief description"

# Required paths before agent can run
agent_required_paths() {
    echo "workspace"
}

# Source dependencies using base library helpers
agent_source_core
agent_source_ralph

# Main agent execution
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    local max_turns="${WIGGUM_MY_AGENT_MAX_TURNS:-${AGENT_CONFIG_MAX_TURNS:-50}}"
    local max_iterations="${WIGGUM_MY_AGENT_MAX_ITERATIONS:-${AGENT_CONFIG_MAX_ITERATIONS:-5}}"

    local workspace="$worker_dir/workspace"

    # Create standard directories
    agent_create_directories "$worker_dir"

    # Set up callback context
    agent_setup_context "$worker_dir" "$workspace" "$project_dir"

    # Run unsupervised ralph loop
    run_ralph_loop "$workspace" \
        "$(_get_system_prompt "$workspace")" \
        "_my_user_prompt" \
        "_my_completion_check" \
        "$max_iterations" "$max_turns" "$worker_dir" "my-prefix"

    # Extract result and write epoch-named result/report
    # (5-arg: worker_dir, name, log_prefix, report_tag, valid_values)
    agent_extract_and_write_result "$worker_dir" "MY" "my-prefix" "report" "PASS|FAIL|SKIP"

    return $?
}
```

#### Orchestrator Agent Template

For pipeline agents that manage sub-agents (like `task-worker`):

```bash
#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: my-orchestrator
# AGENT_DESCRIPTION: Orchestrator that manages the full task lifecycle.
# REQUIRED_PATHS:
#   - prd.md : Product Requirements Document
# OUTPUT_FILES:
#   - worker.log : Main worker log
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "my-orchestrator" "Orchestrator description"

agent_required_paths() {
    echo "prd.md"
}

agent_output_files() {
    echo "worker.log"
}

# Source dependencies
agent_source_core
agent_source_ralph_supervised
agent_source_tasks
agent_source_git

source "$WIGGUM_HOME/lib/core/exit-codes.sh"

# Main agent execution
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    local max_iterations="${3:-${AGENT_CONFIG_MAX_ITERATIONS:-20}}"
    local max_turns="${4:-${AGENT_CONFIG_MAX_TURNS:-50}}"
    local start_from_step="${5:-execution}"
    local resume_instructions="${6:-}"

    # Lifecycle logging
    local start_time
    start_time=$(date +%s)
    agent_log_start "$worker_dir" "$task_id"

    # Set up context (4-arg form with task_id)
    agent_setup_context "$worker_dir" "$workspace" "$project_dir" "$task_id"

    # Supervised ralph loop for main execution
    local supervisor_interval="${WIGGUM_SUPERVISOR_INTERVAL:-2}"
    run_ralph_loop_supervised "$workspace" \
        "$system_prompt" \
        "my_user_prompt_fn" \
        "my_completion_check_fn" \
        "$max_iterations" "$max_turns" "$worker_dir" "iteration" \
        "$supervisor_interval"

    local loop_result=$?

    # Spawn sub-agents for quality gates
    run_sub_agent "security-audit" "$worker_dir" "$project_dir"

    # Write structured result
    agent_write_result "$worker_dir" "$result_status" "$loop_result" "$outputs_json"
    agent_log_complete "$worker_dir" "$loop_result" "$start_time"

    return $loop_result
}
```

### Step 2: Define Lifecycle Hooks (Optional)

```bash
# Called before PID file creation
agent_on_init() {
    local worker_dir="$1"
    local project_dir="$2"
    # Custom initialization
}

# Called after init, before agent_run
agent_on_ready() {
    local worker_dir="$1"
    local project_dir="$2"
    # Pre-execution setup
}

# Called on validation/prerequisite failure
agent_on_error() {
    local worker_dir="$1"
    local exit_code="$2"
    local error_type="$3"  # "prereq" or "output"
    # Error handling
}

# Called on INT/TERM signal before cleanup
agent_on_signal() {
    local signal="$1"
    # Graceful shutdown logic
}

# Called after agent_run completes
agent_cleanup() {
    local worker_dir="$1"
    # Cleanup resources
}
```

### Step 3: Register in agents.json

Add configuration in `config/agents.json`:

```json
{
  "agents": {
    "my-agent": {
      "max_iterations": 10,
      "max_turns": 30,
      "timeout_seconds": 1800
    }
  }
}
```

## Agent Base Library Functions

The `agent-base.sh` library provides shared functionality:

### Metadata Functions

```bash
# Initialize agent metadata (required)
agent_init_metadata "agent-name" "Description"

# Get agent metadata
agent_get_name       # Returns agent name
agent_get_desc       # Returns description
```

### Context Setup

```bash
# Orchestrator agents: full 4-arg call with task ID
agent_setup_context "$worker_dir" "$workspace" "$project_dir" "$task_id"

# Leaf/sub-agents: 3-arg call (task_id is optional, defaults to "")
agent_setup_context "$worker_dir" "$workspace" "$project_dir"

# Access context variables
echo "$AGENT_WORKER_DIR"
echo "$AGENT_WORKSPACE"
echo "$AGENT_PROJECT_DIR"
echo "$AGENT_TASK_ID"        # Empty string for leaf agents
```

### Dependency Sourcing

```bash
# Source common dependencies
agent_source_core              # logger, defaults, exit-codes
agent_source_ralph             # unsupervised ralph loop (for leaf agents)
agent_source_ralph_supervised  # supervised ralph loop (for orchestrator agents)
agent_source_once              # single-run agent execution (run_agent_once)
agent_source_resume            # session resume support
agent_source_violations        # workspace violation monitoring
agent_source_tasks             # task/PRD parser
agent_source_git               # git operations (worktree, commit, PR)
agent_source_lock              # file locking primitives
agent_source_metrics           # metrics collection and export
agent_source_registry          # agent registry lookups
```

### Lifecycle Logging

Used by orchestrator agents and top-level agents (e.g., `plan-mode`, `pr-comment-fix`)
for timing and structured results. Leaf sub-agents can skip these since the parent
orchestrator tracks phase timing via `_phase_start`/`_phase_end`.

```bash
# Record agent start (creates start timestamp in worker dir)
agent_log_start "$worker_dir" "$task_id"

# Record agent completion (calculates duration from start)
agent_log_complete "$worker_dir" "$loop_result" "$start_time"

# Create standard subdirectories (logs/, summaries/)
agent_create_directories "$worker_dir"
```

### Result Management

```bash
# Write epoch-named result to results/<epoch>-<agent-type>-result.json
# Args: worker_dir, status ("success"|"failure"|"partial"), exit_code, outputs_json
agent_write_result "$worker_dir" "success" 0 '{"gate_result":"PASS"}'

# Write epoch-named report to reports/<epoch>-<agent-type>-report.md
# Returns: path to the written report file
report_path=$(agent_write_report "$worker_dir" "$markdown_content")

# Read gate_result from a sub-agent's latest epoch-named result
# Args: worker_dir, agent_name
result=$(agent_read_subagent_result "$worker_dir" "security-audit")

# Find the latest result/report file for an agent type
result_file=$(agent_find_latest_result "$worker_dir" "security-audit")
report_file=$(agent_find_latest_report "$worker_dir" "security-audit")

# Get the result path for the current agent (uses _AGENT_START_EPOCH)
my_result_path=$(agent_get_result_path "$worker_dir")

# Unified extraction from log files (extracts both report and gate_result)
# Args: worker_dir, agent_name, log_prefix, report_tag, valid_values
agent_extract_and_write_result "$worker_dir" "SECURITY" "audit" "report" "PASS|FIX|STOP"
```

### Result JSON Schema

```json
{
  "agent_type": "security-audit",
  "status": "success|failure|partial|unknown",
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

The `outputs.gate_result` field replaces legacy text-file values (PASS/FAIL/FIX/SKIP/STOP).
Agents never delete from `logs/`, `results/`, `reports/`, or `summaries/` — they only append new epoch-named entries.

## Execution Patterns

### Unsupervised Ralph Loop

Used by leaf agents for iterative execution without a supervisor.
Sources: `agent_source_ralph`.

```bash
run_ralph_loop "$workspace" \
    "$system_prompt" \
    "user_prompt_callback_fn" \
    "completion_check_fn" \
    "$max_iterations" "$max_turns" "$worker_dir" "audit"
```

| # | Arg | Description |
|---|-----|-------------|
| 1 | workspace | Working directory for Claude sessions |
| 2 | system_prompt | System prompt string |
| 3 | user_prompt_fn | Name of callback function for user prompt |
| 4 | completion_check_fn | Name of callback that returns 0 when done |
| 5 | max_iterations | Max ralph loop iterations |
| 6 | max_turns | Max turns per Claude session |
| 7 | worker_dir | Worker directory for logs/output |
| 8 | log_prefix | Prefix for log filenames (e.g. "audit", "test") |

**User prompt callback** (2 args — no supervisor context):

```bash
my_user_prompt_fn() {
    local iteration="$1"   # Current iteration number (0-based)
    local output_dir="$2"  # Worker directory
    # Echo/cat the prompt content to stdout
}
```

### Single-Run Agent

Used by agents that need only one Claude session (no iteration loop).
Sources: `agent_source_once`.

```bash
run_agent_once "$workspace" "$system_prompt" "$user_prompt" "$log_file" "$max_turns"
```

| # | Arg | Description |
|---|-----|-------------|
| 1 | workspace | Working directory for Claude session |
| 2 | system_prompt | System prompt string |
| 3 | user_prompt | Full user prompt string (not a callback) |
| 4 | log_file | Path to write the JSON stream log |
| 5 | max_turns | Max turns for the session |

Used by: `documentation-writer`, `resume-decide`.

### Supervised Ralph Loop

Used by orchestrator agents for iterative execution with a supervisor agent
that provides guidance between iterations.
Sources: `agent_source_ralph_supervised`.

### Positional Arguments

```bash
run_ralph_loop_supervised "$workspace" \
    "$system_prompt" \
    "user_prompt_callback_fn" \
    "completion_check_fn" \
    "$max_iterations" "$max_turns" "$worker_dir" "iteration" \
    "$supervisor_interval"
```

| # | Arg | Description |
|---|-----|-------------|
| 1 | workspace | Working directory for Claude sessions |
| 2 | system_prompt | System prompt string |
| 3 | user_prompt_fn | Name of callback function for user prompt |
| 4 | completion_check_fn | Name of callback that returns 0 when done |
| 5 | max_iterations | Max ralph loop iterations |
| 6 | max_turns | Max turns per Claude session |
| 7 | worker_dir | Worker directory for logs/output |
| 8 | log_prefix | Prefix for log filenames (e.g. "iteration") |
| 9 | supervisor_interval | Run supervisor every N iterations |

### Callback Signatures

**User prompt callback** — called each iteration to build the user prompt:

```bash
my_user_prompt_fn() {
    local iteration="$1"           # Current iteration number (0-based)
    local output_dir="$2"          # Worker directory
    local supervisor_dir="$3"      # Supervisor output directory
    local supervisor_feedback="$4" # Feedback from supervisor (empty on first run)
    # Echo/cat the prompt content to stdout
}
```

**Completion check callback** — returns 0 if work is complete, non-zero to continue:

```bash
my_completion_check_fn() {
    # Return 0 when all work is done
    ! has_incomplete_tasks "$PRD_FILE"
}
```

## Invocation Modes

### Top-Level Agent (run_agent)

Used when starting a new agent from orchestrator or CLI:

```bash
run_agent "my-agent" "$worker_dir" "$project_dir"
```

Includes:
- PID file management
- Signal handling
- Violation monitoring
- Full lifecycle hooks

### Sub-Agent (run_sub_agent)

Used when nesting agents within another agent:

```bash
run_sub_agent "validation-review" "$worker_dir" "$project_dir"
```

Excludes lifecycle management - just executes `agent_run()`.

## Configuration

### Orchestrator Parameters

Orchestrator agents (`task-worker`, `task-worker-plan-mode`) receive positional
arguments for configuration and resume support:

```bash
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    local max_iterations="${3:-${AGENT_CONFIG_MAX_ITERATIONS:-20}}"
    local max_turns="${4:-${AGENT_CONFIG_MAX_TURNS:-50}}"
    local start_from_step="${5:-execution}"       # Pipeline phase to resume from
    local resume_instructions="${6:-}"            # Path to resume context file
    ...
}
```

- `max_iterations` / `max_turns`: Originate from CLI flags (`--max-iters`, `--max-turns`)
  passed to `wiggum start`, `wiggum run`, or `wiggum resume`, and flow through
  `run_agent()` in agent-registry.sh.
- `start_from_step`: Which pipeline phase to begin from (used for resuming
  interrupted workers). Valid values match the `TASK_PIPELINE` array:
  `execution`, `audit`, `test`, `docs`, `validation`, `finalization`.
- `resume_instructions`: Path to a file containing context from a previous
  interrupted session, passed to the user prompt on iteration 0.

### Leaf Agent Parameters

Leaf agents are invoked via `run_sub_agent` which only passes `worker_dir` and
`project_dir`. They read iteration/turn limits from environment variables set by
`load_agent_config` in agent-registry, with optional per-agent env var overrides:

```bash
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    # Read from agent-specific env var, falling back to config, then default
    local max_turns="${WIGGUM_SECURITY_AUDIT_MAX_TURNS:-${AGENT_CONFIG_MAX_TURNS:-60}}"
    local max_iterations="${WIGGUM_SECURITY_AUDIT_MAX_ITERATIONS:-${AGENT_CONFIG_MAX_ITERATIONS:-8}}"
    ...
}
```

Naming convention for env var overrides: `WIGGUM_{AGENT_NAME}_MAX_TURNS` where
`AGENT_NAME` is the uppercased, underscore-separated agent name (e.g.,
`WIGGUM_TEST_COVERAGE_MAX_TURNS`, `WIGGUM_CONFLICT_RESOLVER_MAX_TURNS`).

Worker and task IDs are derived from the worker directory name:

```bash
worker_id=$(basename "$worker_dir")
task_id=$(echo "$worker_id" | sed -E 's/worker-([A-Z]+-[0-9]+)-.*/\1/')
```

### Agent-Specific Config

Agents read configuration from `config/agents.json`:

```json
{
  "agents": {
    "task-worker": {
      "max_iterations": 20,
      "max_turns": 50,
      "timeout_seconds": 3600
    }
  },
  "defaults": {
    "max_iterations": 10,
    "max_turns": 30,
    "timeout_seconds": 3600
  }
}
```

## Built-in Agents

### Orchestrator Agents

| Agent | Purpose |
|-------|---------|
| `task-worker` | Main task execution from PRD |
| `task-worker-plan-mode` | Task execution with planning phase |

### Leaf Agents

| Agent | Execution | Purpose |
|-------|-----------|---------|
| `plan-mode` | `run_ralph_loop` | Read-only codebase exploration and planning |
| `validation-review` | `run_ralph_loop` | Code review against PRD requirements |
| `security-audit` | `run_ralph_loop` | Security vulnerability scanning |
| `security-fix` | `run_ralph_loop` | Fix security vulnerabilities |
| `test-coverage` | `run_ralph_loop` | Generate tests for changes |
| `code-review` | `run_ralph_loop` | Code quality review |
| `git-conflict-resolver` | `run_ralph_loop` | Resolve merge conflicts |
| `pr-comment-fix` | `run_ralph_loop` | Address PR review comments |
| `documentation-writer` | `run_agent_once` | Update documentation |
| `resume-decide` | `run_agent_once` | Analyze logs to decide resume step |

## Testing Agents

### Manual Testing

```bash
# Create test worker directory
mkdir -p /tmp/test-worker
echo "# Test PRD" > /tmp/test-worker/prd.md

# Run agent directly
WIGGUM_HOME=/path/to/chief-wiggum \
run_agent "my-agent" "/tmp/test-worker" "$(pwd)"
```

### Integration Testing

See `tests/integration/test-agent-lifecycle.sh` for examples of testing agent lifecycle hooks.
