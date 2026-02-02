# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Chief Wiggum is an autonomous task runner that orchestrates workers to execute software engineering tasks using Claude Code. It parses tasks from a Kanban board (`.ralph/kanban.md`), spawns isolated workers via git worktrees, runs multi-stage pipelines of specialized agents, and creates pull requests.

**Language**: Bash 4.0+ with Python TUI component

## Commands

### Running Tests
```bash
./tests/test-runner.sh                      # Run all Bash tests
./tests/test-runner.sh --filter <pattern>   # Run filtered tests
./tests/run-all-tests.sh                    # Run ALL tests (Bash + TUI)
./tests/run-all-tests.sh --quick            # Quick mode (skip slow tests)
./tests/tui-test-runner.sh                  # Run TUI tests only
./tests/run-coverage.sh                     # Code coverage
./tests/run-shellcheck.sh                   # Bash linting
bash tests/test_<name>.sh                   # Run specific test file
```

### Development
```bash
export WIGGUM_HOME=$(pwd)
export PATH="$WIGGUM_HOME/bin:$PATH"
```

### Debugging
```bash
wiggum inspect worker TASK-001              # Inspect worker state
wiggum inspect pipeline                     # Show pipeline config
wiggum inspect agents                       # List agents
wiggum inspect activity [TASK-ID]           # View activity logs
WIGGUM_LOG_LEVEL=debug wiggum run           # Verbose logging
```

## Architecture

### Directory Structure

| Directory | Purpose |
|-----------|---------|
| `bin/` | CLI entry points (15 command scripts) |
| `lib/core/` | Shared utilities (logger, exit codes, file locking, preflight) |
| `lib/runtime/` | Backend-agnostic runtime abstraction (execution, retry, loop) |
| `lib/backend/` | Backend implementations (claude, opencode) |
| `lib/agents/` | Agent implementations (system, engineering, product) |
| `lib/pipeline/` | Pipeline engine (loader, runner - state machine) |
| `lib/worker/` | Worker lifecycle management |
| `lib/scheduler/` | Task scheduling, worker pool, priority, orchestrator functions |
| `lib/orchestrator/` | Orchestrator lifecycle, arg parsing, directory migration |
| `lib/tasks/` | Kanban parsing, task parsing |
| `lib/git/` | Git worktree operations, PR creation |
| `lib/utils/` | Logging, metrics, cost calculation |
| `config/` | Pipeline, agents, and schema definitions (JSON) |
| `docs/` | Architecture, pipeline schema, agent dev guide, protocol |
| `tests/` | Test suite (35+ test files) |
| `skills/` | Claude Code skill definitions |
| `tui/` | Python Textual-based monitoring UI |

### Runtime Abstraction (`lib/runtime/`)

Backend-agnostic execution layer. See `docs/RUNTIME-SCHEMA.md` for the full specification.

1. **runtime.sh** - Backend loader + public API (`run_agent_once`, `run_agent_resume`)
2. **runtime-loop.sh** - Iterative loop with optional supervision (`run_ralph_loop`)
   - `supervisor_interval=0` (default): Pure iterative loop with summaries
   - `supervisor_interval=N`: Supervisor reviews every N iterations (CONTINUE/STOP/RESTART)
3. **runtime-retry.sh** - Exponential backoff retry (`runtime_exec_with_retry`)
4. **backend-interface.sh** - Contract for backend implementations

**Backends** (`lib/backend/`):
- `claude/claude-backend.sh` - Claude Code CLI backend (default)
- `opencode/opencode-backend.sh` - OpenCode skeleton (stub)

**Backend selection** (priority): `WIGGUM_RUNTIME_BACKEND` env → `.ralph/config.json` → `config/config.json` → `"claude"`

### Pipeline Engine

Jump-based state machine defined in `config/pipelines/default.json`. Steps have `on_result` handlers (PASS/FAIL/FIX/SKIP) controlling flow via jump targets: `self`, `prev`, `next`, `abort`, or step ID.

Default pipeline: planning → execution (supervised) → summary → audit → audit-fix → test → docs → validation

### Agent Architecture

All agents source `lib/core/agent-base.sh` and implement:
```bash
agent_run(worker_dir, project_dir)
# Returns: 0=PASS, 10=FAIL, 12=MAX_ITERATIONS
```

**Agent Categories**:
- `lib/agents/system/` - task-worker, task-summarizer, resume-decide
- `lib/agents/engineering/` - software-engineer, security-audit, security-fix, test-coverage, validation-review
- `lib/agents/product/` - plan-mode, documentation-writer

### Worker Structure

Each worker operates in `.ralph/workers/worker-TASK-XXX-<timestamp>/` with:
- `workspace/` - Git worktree
- `prd.md` - Generated requirements
- `activity.jsonl` - Event log (NDJSON)
- `output/<agent>/` - Per-agent outputs
- `gate_result` - Last agent result (PASS/FAIL/FIX/SKIP)

### Exit Codes (`lib/core/exit-codes.sh`)

| Code | Meaning |
|------|---------|
| 0 | Success/PASS |
| 1 | General error |
| 2 | Invalid arguments |
| 3 | Configuration error |
| 4 | Git error |
| 5 | Claude error |
| 10 | Agent FAIL |
| 12 | Max iterations exceeded |

### Configuration

- `config/pipelines/default.json` - Default pipeline definition
- `config/agents.json` - Agent registry with iteration/turn limits and per-agent result_mappings
- `.ralph/config.json` - Project-specific overrides
- `.ralph/pipeline.json` - Project pipeline override
- `.ralph/pipelines/<TASK-ID>.json` - Task-specific pipeline

### Kanban Format (`.ralph/kanban.md`)

**Specification**: `skills/kanban/references/task-format.md`

```markdown
- [ ] **[TASK-001]** Brief description
  - Description: Detailed explanation
  - Priority: CRITICAL|HIGH|MEDIUM|LOW
  - Dependencies: TASK-002, TASK-003 | none
```

**Easy to get wrong**:
- Task ID pattern: `[A-Za-z]{2,10}-[0-9]{1,4}` (prefix 2-10 letters, number 1-4 digits)
- Fields must be 2-space indented under task line
- Priority and Dependencies are **required**
- Only `[x]` (Complete) satisfies dependencies - `[P]` does NOT
- Status markers: `[ ]` Pending, `[=]` In-progress, `[P]` Pending approval, `[x]` Complete, `[*]` Failed, `[N]` Not planned

### Task Prioritization

Tasks are sorted by effective priority using fixed-point arithmetic (10000 = 1.0000):

| Priority | Value | Decimal |
|----------|-------|---------|
| CRITICAL | 0 | 0.0 |
| HIGH | 10000 | 1.0 |
| MEDIUM | 20000 | 2.0 |
| LOW | 30000 | 3.0 |

**Bonuses (subtract from priority)**:
| Modifier | Value | Condition |
|----------|-------|-----------|
| Plan bonus | -15000 (-1.5) | Task has `.ralph/plans/<TASK-ID>.md` |
| Aging bonus | -8000/level (-0.8) | Per `AGING_FACTOR` (7) scheduling events waiting |
| Dependency bonus | -7000/task (-0.7) | Per task transitively blocked by this one |

**Penalties (add to priority)**:
| Modifier | Formula | Example |
|----------|---------|---------|
| Sibling WIP | `sqrt(N) * 20000` | N=1: +20000, N=4: +40000 |

**Example calculation**:
- HIGH task with plan, blocking 3 tasks, 1 sibling WIP:
  - Base: 10000
  - Plan: -15000
  - Dep bonus: -21000 (3 × 7000)
  - Sibling: +20000
  - **Effective: -6000 → 0** (floored)

## Testing Patterns

Test framework uses custom assertions:
```bash
assert_exit_code 0
assert_equals "expected" "$actual"
assert_match "regex" "$output"
assert_file_exists "/path"
```

## Documentation

| Document | Purpose |
|----------|---------|
| `docs/ARCHITECTURE.md` | Developer guide, component overview, internals |
| `docs/PIPELINE-SCHEMA.md` | Pipeline configuration schema and step definitions |
| `docs/AGENT_DEV_GUIDE.md` | Writing custom agents, lifecycle hooks |
| `docs/PROTOCOL.md` | Inter-agent communication, data passing mechanisms |
| `docs/AUDIT_LOG.md` | Security audit trail format and events |
| `docs/RUNTIME-SCHEMA.md` | Runtime abstraction, backend interface, execution patterns |

## Spec-Driven Development

Chief Wiggum follows spec-driven development: specifications define behavior before implementation, and code is validated against specs.

### Core Principles

1. **Specs are authoritative** - When code and spec disagree, determine which is correct; don't let drift persist
2. **Document patterns, not implementations** - Specs describe *what* and *why*, code handles *how*
3. **Extract emergent patterns** - When 3+ files share a pattern, consider adding it to a spec
4. **Preserve behavior during refactoring** - Spec compliance changes should not alter functionality

### Spec Document Hierarchy

| Document | Scope | Examples |
|----------|-------|----------|
| `CLAUDE.md` | Project-wide conventions | Coding style, exit codes, file structure |
| `docs/ARCHITECTURE.md` | System design | Component boundaries, data flow |
| `docs/PIPELINE-SCHEMA.md` | Pipeline contracts | Step definitions, result mappings |
| `docs/AGENT_DEV_GUIDE.md` | Agent interfaces | `agent_run()` signature, lifecycle hooks |
| `docs/PROTOCOL.md` | Inter-component communication | File formats, event schemas |
| `docs/SERVICES.md` | Service definitions | `wiggum run` schedular managed services |
| `docs/RUNTIME-SCHEMA.md` | Runtime abstraction | Backend interface, execution patterns |
| `config/agents.json` | Agent configuration | Iteration limits, result mappings |

### When Writing New Code

1. **Check existing specs** - Find relevant spec documents before implementing
2. **Follow established patterns** - Match conventions from spec, not just nearby code
3. **Flag deviations** - If you must deviate, document why (comment + potential spec update)

### When Reviewing Code

Look for:
- **Extra parameters** not in spec → extend spec or remove
- **Missing behavior** spec requires → implement it
- **Different defaults** than spec → align or document exception
- **Naming mismatches** with spec terminology → rename for consistency

### Periodic Refactoring

Use `/wiggum-refactor` to analyze modules after multiple PRs:
- Identifies patterns that should be added to specs
- Finds code that deviates from existing specs
- Suggests simplifications for accumulated complexity

Output goes to `.ralph/refactor-plans/<module>-<timestamp>.md`.

## Bash Coding Style

### Script Header
```bash
#!/usr/bin/env bash
set -euo pipefail
```

### Double-Source Prevention
```bash
[ -n "${_MODULE_LOADED:-}" ] && return 0
_MODULE_LOADED=1
```

### Variables
- Always quote variables: `"$var"` not `$var`
- Use `${var:-default}` for defaults
- Use `local` for function variables: `local foo="bar"`
- Declare associative arrays: `local -A map=()`

### Arithmetic
- Use `(( ))` for arithmetic: `((++count))`, `((i + 1))`
- Prefer pre-increment `((++count))` over post-increment `((count++))` — post-increment evaluates to the old value, so `((0++))` is falsy and kills the script under `set -e`. Pre-increment evaluates to the new value, avoiding this entirely.

### Conditionals
- Use `[[ ]]` for tests: `[[ -n "$var" ]]`, `[[ "$a" == "$b" ]]`
- Use `[ ]` only for simple existence checks in one-liners: `[ -n "${VAR:-}" ] && return 0`

### Functions
```bash
# Brief description of what the function does
#
# Args:
#   arg1 - Description
#   arg2 - Description
#
# Returns: exit code or echoes value
function_name() {
    local arg1="$1"
    local arg2="$2"
    ...
}
```

### Functions That Return Values via stdout
- **Never call `log()` or `log_info()` in functions that echo return values** — `log()` writes to stdout and contaminates values captured via `$()`. Move the log call to the caller after capturing the value.
- `log_debug()`, `log_warn()`, and `log_error()` are safe (they use stderr).

```bash
# BAD - log() output captured into $result
get_id() {
    local id="batch-$(date +%s)"
    echo "$id"
    log "Created $id"   # BREAKS: contaminates stdout capture
}
result=$(get_id)        # result = "batch-123\n[...] INFO: Created batch-123"

# GOOD - caller logs after capture
get_id() {
    local id="batch-$(date +%s)"
    echo "$id"
}
result=$(get_id)
log "Created $result"   # Safe: log after capture
```

### `set -e` and Background Process Exit Codes
- **Always guard `wait` with `|| exit_code=$?`** — bare `wait "$pid"` returns the process exit code, which under `set -e` kills the calling script before the next line can capture it.

```bash
# BAD - set -e kills script if process exited non-zero
wait "$pid" 2>/dev/null
local exit_code=$?         # Never reached if wait returns non-zero

# GOOD - || disables set -e for the wait
local exit_code=0
wait "$pid" 2>/dev/null || exit_code=$?
```

### `bash -c` Subprocesses and `local`
- **Never use `local` at the top level of a `bash -c` or `setsid bash -c` block** — `local` is only valid inside bash functions. At the top level of a `bash -c` subprocess it causes `bash: local: can only be used in a function`, which under `set -e` kills the subprocess.
- Also apply the `|| exit_code=$?` guard pattern (above) inside `bash -c` blocks — bare commands with non-zero exits are fatal under `set -e` before the next line can capture `$?`.

```bash
# BAD - local at top level of bash -c, bare command under set -e
setsid bash -c '
    set -euo pipefail
    some_command "$@"
    local exit_code=$?         # BREAKS: "local: can only be used in a function"
    echo "exit: $exit_code"    # Never reached
' ...

# GOOD - plain variable, || guard
setsid bash -c '
    set -euo pipefail
    exit_code=0
    some_command "$@" || exit_code=$?
    echo "exit: $exit_code"
' ...
```

### `IFS` and TSV Parsing with `read`
- **Never use `IFS=$'\t'` with `read` to parse TSV** — bash treats tab as whitespace, so consecutive tabs (empty fields) collapse into a single delimiter, silently shifting all subsequent fields.
- Use a non-whitespace record separator instead (e.g., ASCII RS `\x1e`):

```bash
# BAD - empty fields collapse, downstream variables get wrong values
while IFS=$'\t' read -r name type value; do
    echo "$value"                    # WRONG: shifted if 'type' was empty
done < <(jq -r '[.name, .type, .value] | @tsv' file.json)

# GOOD - \x1e is non-whitespace, empty fields preserved
while IFS=$'\x1e' read -r name type value; do
    echo "$value"                    # Correct even when 'type' is ""
done < <(jq -r '[.name, .type, .value] | join("\u001e")' file.json)
```

### `jq` Output in Integer Comparisons
- **Always guard `jq` output with `${var:-0}` before using it in `[ ]` integer tests** — if `jq` fails to parse a file (truncated, corrupt, missing), it returns an empty string even with `// 0` fallback, causing `[: : integer expected` under `[ "$var" -gt 0 ]`.

```bash
# BAD - empty string if jq fails to parse the file
count=$(jq '.items | length' "$file" 2>/dev/null)
[ "$count" -gt 0 ]          # BREAKS: "[: : integer expected"

# GOOD - default ensures integer even when jq fails entirely
count=$(jq '.items | length' "$file" 2>/dev/null)
count="${count:-0}"
[ "$count" -gt 0 ]
```

### Platform Compatibility
- Code must work on both Linux and macOS — use `lib/core/platform.sh` for OS-specific operations (e.g., `stat`, `date`, `sed -i`)
- Never use GNU-only flags directly; call the platform abstraction instead

### Shellcheck
- Run `./tests/run-shellcheck.sh` before committing
- All scripts must pass shellcheck
- Use `# shellcheck disable=SC####` with justification when necessary

## Python TUI Development

The TUI component uses Python 3.10+ with [uv](https://docs.astral.sh/uv/) for dependency management.

## Critical Constraints & Gotchas

### Agent Rules
- **Orchestrators never call `claude/*` directly** - they delegate via `run_sub_agent`
- **Sub-agents don't manage PID files or signal handlers** - only top-level agents do
- **`readonly: true` agents get git checkpoint restored after exit** - changes are discarded
- **Agents must write epoch-named results** - use `agent_write_result`, never delete from `results/`, `reports/`, `logs/`, `summaries/`
- **Ralph loop callbacks use unified 4-arg signature**: `user_prompt_fn(iteration, output_dir, supervisor_dir, supervisor_feedback)` - agents not using supervision can ignore the last 2 args

### Pipeline Rules
- **Every cycle needs a bounded `max`** - termination guarantee requires `max` on any step in a loop
- **Unhandled results use `default_jump` from result_mappings** - explicit handlers needed for custom behavior
- **Inline agent handlers implicitly jump to parent (`prev`)** after completion
- **`on_max` default is `next`** - pipeline continues even if step hit iteration limit

### Concurrency
- **Always use `flock` for shared resources** - kanban, PID files, event logs
- **Worker directory is the namespace boundary** - all inter-agent state scoped here
- **Epoch naming prevents collisions** - multiple runs of same agent produce distinct files

### Gate Result Values (easy to forget)
| Agent | Possible Values |
|-------|-----------------|
| `security-audit` | PASS, FIX, FAIL |
| `security-fix` | PASS, FIX, FAIL |
| `generic-fix` | PASS, FIX, FAIL |
| `validation-review` | PASS, FAIL |
| `test-coverage` | PASS, FIX, FAIL, SKIP |
| `plan-mode` | PASS, FAIL |

**Result Mappings** (defined per-agent in `config/agents.json`):
| Result | Status | Exit Code | Default Jump |
|--------|--------|-----------|--------------|
| `PASS` | success | 0 | next |
| `FAIL` | failure | 10 | abort |
| `FIX` | partial | 0 | prev |
| `SKIP` | success | 0 | next |

Each agent defines its own `result_mappings` in `config/agents.json`. Fallback mappings are in `defaults.result_mappings`. Pipeline-level overrides are also supported.

### Environment Variables for Config Override
Pattern: `WIGGUM_{AGENT_NAME}_MAX_TURNS` (uppercase, underscores)
- `WIGGUM_SECURITY_AUDIT_MAX_TURNS`
- `WIGGUM_TEST_COVERAGE_MAX_ITERATIONS`
