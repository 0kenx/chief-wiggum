# Agent Development Guide

This document describes how to create and configure agents in Chief Wiggum.

## Overview

Agents in Chief Wiggum can be implemented in two formats:

1. **Declarative Markdown Agents** (recommended) — `.md` files with YAML frontmatter and templated prompts
2. **Shell Script Agents** (legacy) — `.sh` files with full Bash implementation

Markdown agents are recommended for most use cases as they reduce boilerplate, make prompts easier to maintain, and ensure consistent behavior. Shell agents remain available for complex orchestration logic.

There are two agent patterns:

- **Orchestrator agents** (`lib/agents/system/`) — `system.task-worker` —
  manage the full task pipeline, spawn sub-agents, and handle commits/PRs.
  The orchestrator controls workflow only and never calls `claude/*` directly.
  Plan mode is enabled via `WIGGUM_PLAN_MODE=true` or config `plan_mode: true`.
- **Leaf agents** (`lib/agents/definitions/` or `lib/agents/`) — all others — perform a single focused task (audit,
  review, test, execution, etc.), invoked as sub-agents by orchestrators, using
  unsupervised/supervised ralph loops or single-run execution.

---

## Declarative Markdown Agents

Markdown agents define agent behavior declaratively using YAML frontmatter and templated prompt sections. The interpreter (`lib/core/agent-md.sh`) handles all execution logic.

### File Location

Markdown agent definitions are stored alongside shell agents in `lib/agents/`. Both formats can coexist for the same agent with an inheritance pattern:

```
lib/agents/
├── engineering/
│   ├── security-audit.md    # Markdown base
│   ├── security-audit.sh    # Shell overrides (optional, extends .md)
│   ├── security-fix.md      # Markdown only
│   ├── validation-review.md
│   └── test-coverage.md
├── product/
│   ├── documentation-writer.md
│   └── plan-mode.md
└── system/
    ├── task-worker.sh       # Shell only (complex orchestrator)
    ├── task-executor.md
    └── task-summarizer.md
```

### Inheritance Model

When both `.md` and `.sh` exist for the same agent:

1. **Markdown loads first** - defines base behavior (prompts, config)
2. **Shell loads second** - can override any function from markdown

This allows:
- Standard prompts/config defined declaratively in markdown
- Custom hooks, special logic defined in shell
- Gradual migration: start with shell, add markdown, keep custom overrides

```bash
# security-audit.md defines: agent_run, agent_required_paths
# security-audit.sh can override: agent_on_ready, agent_cleanup, etc.
```

### Basic Structure

```markdown
---
type: engineering.security-audit
description: Security vulnerability scanner
required_paths: [workspace]
valid_results: [PASS, FIX, FAIL]
mode: ralph_loop
readonly: true
report_tag: report
---

<WIGGUM_SYSTEM_PROMPT>
You are a security auditor...
WORKSPACE: {{workspace}}

## Audit Philosophy
...
</WIGGUM_SYSTEM_PROMPT>

<WIGGUM_USER_PROMPT>
{{context_section}}

SECURITY AUDIT TASK:
...
</WIGGUM_USER_PROMPT>

<WIGGUM_CONTINUATION_PROMPT>
CONTINUATION CONTEXT (Iteration {{iteration}}):
Your previous work: @../summaries/{{run_id}}/{{step_id}}-{{prev_iteration}}-summary.txt
</WIGGUM_CONTINUATION_PROMPT>
```

### Frontmatter Fields

| Field | Type | Required | Default | Description |
|-------|------|----------|---------|-------------|
| `type` | string | yes | - | Agent type (dotted path, e.g., `engineering.security-audit`) |
| `description` | string | yes | - | Human-readable description |
| `required_paths` | array | yes | - | Input paths that must exist (relative to worker_dir) |
| `valid_results` | array | yes | - | Valid result tag values (e.g., `[PASS, FAIL, FIX]`) |
| `mode` | string | yes | - | Execution mode: `ralph_loop`, `once`, or `resume` |
| `readonly` | bool | no | false | If true, inject git restrictions into prompts |
| `report_tag` | string | no | `report` | XML tag to extract for report |
| `result_tag` | string | no | `result` | XML tag containing result |
| `output_path` | string | no | - | Custom output file path (for plan-mode style agents) |
| `workspace_override` | string | no | - | Use `project_dir` instead of `workspace` |
| `completion_check` | string | no | `result_tag` | Completion check type (see below) |
| `session_from` | string | no | - | For resume mode: `parent` to use parent session |
| `outputs` | array | no | - | Output keys to expose for downstream steps |

### Prompt Sections

Three XML-tagged sections define the prompts:

| Section | Required | Usage |
|---------|----------|-------|
| `<WIGGUM_SYSTEM_PROMPT>` | yes | System prompt - sets context and behavior |
| `<WIGGUM_USER_PROMPT>` | yes | User prompt - the task to perform |
| `<WIGGUM_CONTINUATION_PROMPT>` | no | Appended on iteration > 0 (ralph_loop mode only) |

### Variable Interpolation

Variables use `{{name}}` syntax and are replaced at runtime.

#### Path Variables

| Variable | Source | Description |
|----------|--------|-------------|
| `{{workspace}}` | `$worker_dir/workspace` | Git worktree containing code |
| `{{worker_dir}}` | arg 1 to `agent_run()` | Worker directory root |
| `{{project_dir}}` | arg 2 to `agent_run()` | Original project root |

#### Current Step Context

| Variable | Source | Description |
|----------|--------|-------------|
| `{{task_id}}` | Extracted from worker_dir | Task identifier (e.g., `TASK-001`) |
| `{{step_id}}` | `$WIGGUM_STEP_ID` | Current pipeline step ID |
| `{{run_id}}` | `$RALPH_RUN_ID` | Current run ID (`step_id-epoch`) |
| `{{session_id}}` | Generated per-iteration | Claude session ID for current iteration |

#### Parent Step Context (Pipeline Chaining)

These variables enable modular agents that consume outputs from upstream steps:

| Variable | Source | Description |
|----------|--------|-------------|
| `{{parent.step_id}}` | `$WIGGUM_PARENT_STEP_ID` | Parent step's ID |
| `{{parent.run_id}}` | `$WIGGUM_PARENT_RUN_ID` | Parent step's run ID |
| `{{parent.session_id}}` | Parent result outputs | Claude session from parent |
| `{{parent.result}}` | `$WIGGUM_PARENT_RESULT` | Parent's gate result |
| `{{parent.output_dir}}` | Computed | Parent's output directory |
| `{{parent.report}}` | `$WIGGUM_PARENT_REPORT` | Path to parent's report file |

#### Next Step Context

| Variable | Source | Description |
|----------|--------|-------------|
| `{{next.step_id}}` | `$WIGGUM_NEXT_STEP_ID` | Next step's ID (for output naming) |

#### Iteration Variables (ralph_loop mode only)

| Variable | Source | Description |
|----------|--------|-------------|
| `{{iteration}}` | Callback arg 1 | Current iteration (0-based) |
| `{{prev_iteration}}` | Computed | Previous iteration number |
| `{{output_dir}}` | Callback arg 2 | Output directory for this run |

#### Generated Content Variables

| Variable | Generated By | Description |
|----------|--------------|-------------|
| `{{context_section}}` | `_md_generate_context_section()` | Dynamic context based on available files |
| `{{git_restrictions}}` | `_md_generate_git_restrictions()` | Forbidden/allowed git commands block |

### Execution Modes

#### Mode: `ralph_loop` (default)

Iterative execution with optional supervision. Uses all three prompt sections.

```yaml
mode: ralph_loop
```

The continuation prompt section is only appended when `iteration > 0`.

#### Mode: `once`

Single-shot execution. Only uses system prompt and user prompt (no continuation).

```yaml
mode: once
```

#### Mode: `resume`

Resume a prior Claude session. Requires `session_from` config.

```yaml
mode: resume
session_from: parent  # Use parent step's session_id
```

### Completion Check Types

| Check Type | Declaration | Behavior |
|------------|-------------|----------|
| `result_tag` (default) | `completion_check: result_tag` | Looks for `<result>VALUE</result>` in logs |
| `status_file` | `completion_check: status_file:path` | Checks for `- [ ]` items in specified file |
| `file_exists` | `completion_check: file_exists:{{output_path}}` | Checks output file exists and non-empty |

### Output Declaration for Chaining

Agents declare what outputs they provide for downstream steps:

```yaml
outputs:
  - session_id      # For resume-mode consumers
  - report_file     # For report consumers
  - plan_file       # Custom output
```

The pipeline runner reads these from the agent result and makes them available as environment variables for downstream steps.

### Example: Security Audit Agent

```markdown
---
type: engineering.security-audit
description: Security vulnerability scanner that audits codebase for security issues
required_paths: [workspace]
valid_results: [PASS, FIX, FAIL]
mode: ralph_loop
readonly: true
report_tag: report
outputs: [session_id, report_file]
---

<WIGGUM_SYSTEM_PROMPT>
SECURITY AUDITOR:

You scan code for security vulnerabilities. Your job is to find REAL issues, not theoretical ones.

WORKSPACE: {{workspace}}

## Audit Philosophy

* HIGH CONFIDENCE ONLY - Only report issues you're confident are real vulnerabilities
* VERIFY BEFORE REPORTING - Check context; what looks dangerous might be safe
* EVIDENCE REQUIRED - Every finding needs concrete evidence (file, line, code snippet)

{{git_restrictions}}
</WIGGUM_SYSTEM_PROMPT>

<WIGGUM_USER_PROMPT>
{{context_section}}

SECURITY AUDIT TASK:

Scan the codebase for security vulnerabilities...

## Output Format

<report>
...
</report>

<result>PASS</result>
OR
<result>FIX</result>
OR
<result>FAIL</result>
</WIGGUM_USER_PROMPT>

<WIGGUM_CONTINUATION_PROMPT>
CONTINUATION CONTEXT (Iteration {{iteration}}):

Your previous audit work is summarized in @../summaries/{{run_id}}/{{step_id}}-{{prev_iteration}}-summary.txt.

Please continue your audit and provide the final <report> and <result> tags when complete.
</WIGGUM_CONTINUATION_PROMPT>
```

### Example: Task Summarizer (Resume Mode)

```markdown
---
type: system.task-summarizer
description: Generate final summary by resuming executor session
required_paths: [workspace]
valid_results: [PASS, SKIP]
mode: resume
session_from: parent
output_path: summaries/summary.txt
outputs: [summary_file]
---

<WIGGUM_USER_PROMPT>
FINAL COMPREHENSIVE SUMMARY REQUEST:

Please provide a comprehensive summary of all the work completed in this session.
Write the summary to {{output_path}}.
</WIGGUM_USER_PROMPT>
```

### When to Use Shell vs Markdown Agents

**Use Markdown Agents for:**
- Standard audit/review agents (security-audit, validation-review, test-coverage)
- Documentation generation (documentation-writer)
- Plan generation (plan-mode)
- Any agent with straightforward prompt-based logic

**Keep as Shell Agents:**
- Orchestrators that manage sub-agents (task-worker)
- Agents with complex state management (resume-decide)
- Agents with custom pre/post processing (git-conflict-resolver)
- Agents that need dynamic pipeline loading

### Migration Guide

To convert an existing shell agent to markdown:

1. **Extract frontmatter** from the agent metadata comments:
   ```yaml
   type: engineering.my-agent
   description: <from AGENT_DESCRIPTION>
   required_paths: <from agent_required_paths()>
   valid_results: <from agent_extract_and_write_result call>
   mode: ralph_loop  # or once/resume
   ```

2. **Move prompts** from `_get_system_prompt()` and `_get_user_prompt()` functions into XML sections

3. **Replace hardcoded paths** with variables:
   - `$workspace` → `{{workspace}}`
   - `$worker_dir` → `{{worker_dir}}`

4. **Extract continuation logic** to `<WIGGUM_CONTINUATION_PROMPT>` section

5. **Remove boilerplate** - the interpreter handles:
   - `agent_setup_context()`
   - `run_ralph_loop()` invocation
   - `agent_extract_and_write_result()`
   - Completion checking

---

## Shell Script Agents (Legacy)

Shell agents provide full control over agent behavior but require more boilerplate code.

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
- System agents → `lib/agents/system/`

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

For pipeline agents that manage sub-agents (like `system.task-worker`).
Orchestrators control workflow only — they never call `claude/*` directly.
Instead, they delegate execution to leaf agents via `run_sub_agent`:

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

# Source dependencies (no ralph/resume - orchestrators don't call Claude directly)
agent_source_core
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

    # Write config for executor sub-agent
    _write_executor_config "$worker_dir" "$max_iterations" "$max_turns" ...

    # Delegate execution to leaf agents
    run_sub_agent "system.task-executor" "$worker_dir" "$project_dir"
    local loop_result=$?

    # Generate summary via sub-agent
    if [ $loop_result -eq 0 ]; then
        run_sub_agent "system.task-summarizer" "$worker_dir" "$project_dir"
    fi

    # Spawn sub-agents for quality gates
    run_sub_agent "engineering.security-audit" "$worker_dir" "$project_dir"

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

Used by orchestrator agents and top-level agents (e.g., `product.plan-mode`, `engineering.pr-comment-fix`)
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
result=$(agent_read_subagent_result "$worker_dir" "engineering.security-audit")

# Find the latest result/report file for an agent type
result_file=$(agent_find_latest_result "$worker_dir" "engineering.security-audit")
report_file=$(agent_find_latest_report "$worker_dir" "engineering.security-audit")

# Get the result path for the current agent (uses _AGENT_START_EPOCH)
my_result_path=$(agent_get_result_path "$worker_dir")

# Unified extraction from log files (extracts both report and gate_result)
# Args: worker_dir, agent_name, log_prefix, report_tag, valid_values
agent_extract_and_write_result "$worker_dir" "SECURITY" "audit" "report" "PASS|FIX|FAIL"
```

### Result JSON Schema

```json
{
  "agent_type": "engineering.security-audit",
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

Used by: `product.documentation-writer`, `system.resume-decide`.

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
run_sub_agent "engineering.validation-review" "$worker_dir" "$project_dir"
```

Excludes lifecycle management - just executes `agent_run()`.

## Configuration

### Orchestrator Parameters

Orchestrator agents (`system.task-worker`) receive positional arguments for
configuration and resume support:

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
task_id=$(echo "$worker_id" | sed -E 's/worker-([A-Za-z]{2,10}-[0-9]{1,4})-.*/\1/')
```

### Agent-Specific Config

Agents read configuration from `config/agents.json`:

```json
{
  "agents": {
    "system.task-worker": {
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
| `system.task-worker` | Main task execution from PRD (supports plan mode via `WIGGUM_PLAN_MODE`) |

### Leaf Agents

| Agent | Execution | Purpose |
|-------|-----------|---------|
| `system.task-executor` | `run_ralph_loop_supervised` | Main code-writing agent (supervised ralph loop) |
| `system.task-summarizer` | `run_agent_resume` | Generate final summary by resuming executor session |
| `system.resume-decide` | `run_agent_once` | Analyze logs to decide resume step |
| `product.plan-mode` | `run_ralph_loop` | Read-only codebase exploration and planning |
| `product.documentation-writer` | `run_agent_once` | Update documentation |
| `engineering.validation-review` | `run_ralph_loop` | Code review against PRD requirements |
| `engineering.security-audit` | `run_ralph_loop` | Security vulnerability scanning |
| `engineering.security-fix` | `run_ralph_loop` | Fix security vulnerabilities |
| `engineering.test-coverage` | `run_ralph_loop` | Generate tests for changes |
| `engineering.code-review` | `run_ralph_loop` | Code quality review |
| `engineering.git-conflict-resolver` | `run_ralph_loop` | Resolve merge conflicts |
| `engineering.pr-comment-fix` | `run_ralph_loop` | Address PR review comments |

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
