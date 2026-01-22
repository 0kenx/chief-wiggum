# Agent Development Guide

This document describes how to create and configure agents in Chief Wiggum.

## Overview

Agents are self-contained Bash scripts in `lib/agents/` that implement specific workflows. Each agent uses the ralph loop pattern for iterative task execution with Claude Code CLI.

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
│  6. OUTPUT VALIDATION (agent_output_files)                      │
│     └── Verifies required output files were created             │
│                                                                 │
│  7. CLEANUP (agent_cleanup)                                     │
│     ├── Custom cleanup logic                                    │
│     ├── PID file removed                                        │
│     └── Violation monitor stopped                               │
└─────────────────────────────────────────────────────────────────┘
```

## Creating a New Agent

### Step 1: Create Agent File

Create a new file in `lib/agents/` with the naming convention `{agent-name}.sh`:

```bash
#!/usr/bin/env bash
set -euo pipefail
# =============================================================================
# AGENT METADATA
# =============================================================================
# AGENT_TYPE: my-agent
# AGENT_DESCRIPTION: Brief description of what the agent does.
#   Can span multiple lines with indentation.
# REQUIRED_PATHS:
#   - prd.md      : Description of why this file is needed
#   - workspace   : Description of the workspace requirement
# OUTPUT_FILES:
#   - result.txt  : Description of output file
# =============================================================================

# Source base library and initialize metadata
source "$WIGGUM_HOME/lib/core/agent-base.sh"
agent_init_metadata "my-agent" "Brief description"

# Required paths before agent can run
agent_required_paths() {
    echo "prd.md"
    echo "workspace"
}

# Output files that must exist after successful run
agent_output_files() {
    echo "result.txt"
}

# Main agent execution
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"

    # Your agent logic here

    # Use ralph loop for iterative execution
    source "$WIGGUM_HOME/lib/claude/run-claude-ralph-loop.sh"
    run_ralph_loop \
        --worker-dir "$worker_dir" \
        --workspace "$worker_dir/workspace" \
        --system-prompt "$system_prompt" \
        --user-prompt-fn "my_prompt_fn" \
        --max-iterations "$max_iterations"

    return $?
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
# Set up callback context with worker/project directories
agent_setup_context "$worker_dir" "$project_dir"

# Access context variables
echo "$AGENT_WORKER_DIR"
echo "$AGENT_PROJECT_DIR"
```

### Dependency Sourcing

```bash
# Source common dependencies
agent_source_core     # logger, defaults, exit-codes
agent_source_ralph    # ralph loop primitives
agent_source_git      # git operations
agent_source_tasks    # task parser
```

### Result Management

```bash
# Write structured result to agent-result.json
agent_write_result "$worker_dir" "VALIDATION_result" "PASS"

# Read result from sub-agent
result=$(agent_read_subagent_result "$worker_dir" "VALIDATION_result" "fallback.txt")
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

### Parameters

`max_iterations` and `max_turns` are passed as function arguments to `agent_run()`:

```bash
agent_run() {
    local worker_dir="$1"
    local project_dir="$2"
    local max_iterations="${3:-${AGENT_CONFIG_MAX_ITERATIONS:-20}}"
    local max_turns="${4:-${AGENT_CONFIG_MAX_TURNS:-50}}"
    ...
}
```

These values originate from CLI flags (`--max-iters`, `--max-turns`) passed to
`wiggum start`, `wiggum run`, or `wiggum resume`, and flow through `run_agent()`
in agent-registry.sh.

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

| Agent | Purpose |
|-------|---------|
| `task-worker` | Main task execution from PRD |
| `task-worker-plan-mode` | Task execution with planning phase |
| `plan-mode` | Read-only codebase exploration and planning |
| `validation-review` | Code review against PRD requirements |
| `pr-comment-fix` | Address PR review comments |
| `security-audit` | Security vulnerability scanning |
| `security-fix` | Fix security vulnerabilities |
| `git-conflict-resolver` | Resolve merge conflicts |
| `code-review` | Code quality review |
| `test-coverage` | Generate tests for changes |
| `documentation-writer` | Update documentation |

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
