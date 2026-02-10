# Chief Wiggum

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Bash](https://img.shields.io/badge/Language-Bash-blue)](https://www.gnu.org/software/bash/)

**Specs are the new source code.** Compilers turned C into assembly. Chief Wiggum turns Kanban tasks and GitHub issues into production-ready pull requests. Be the 1000x engineer and ship 200+ features per day.

![Chief Wiggum](docs/img/chief_wiggum.jpeg)

> *Bake 'em away, Toys!*

We used to write code and compile it into binaries. Now we write specs and compile them into code. In the AI era, the unit of engineering work isn't a function, it's a task definition: what to build, why it matters, and what "done" looks like. The code is a build artifact.

Chief Wiggum is the compiler. Feed it a Markdown Kanban board or GitHub issues. Each task gets picked up by an isolated worker powered by Claude Code and driven through a full engineering pipeline (planning, implementation, security audit, tests, documentation, and a validation gate) until a merge-ready PR comes out the other end. When Copilot reviewer leave comments, it addresses them, resolves conflicts and merges into main. You write the spec. The AI writes the code, tests it, audits it, and ships it.

### In Action

<table>
<tr>
<td width="50%">

<p align="center"><strong>Live Monitor</strong></p>

<img src="docs/img/kanban.png" width="100%" alt="TUI monitor showing kanban columns with tasks flowing through Pending, In Progress, Pending Approval, and Complete">

<p><em>Real-time TUI tracks every task across the pipeline — pending, in progress, awaiting approval, complete.</em></p>

</td>
<td width="50%">

<p align="center"><strong>GitHub Issues Integration</strong></p>

<img src="docs/img/issue.png" width="100%" alt="GitHub Issue created from a kanban task with description, priority, dependencies, and scope">

<p><em>Tasks sync to GitHub Issues with full spec: description, priority, dependencies, scope, and acceptance criteria.</em></p>

</td>
</tr>
<tr>
<td width="50%">

<p align="center"><strong>Production-Ready PRs</strong></p>

<img src="docs/img/pr.png" width="100%" alt="Merged PR showing implementation checklist, changelog, and detailed cost metrics">

<p><em>Every PR ships with an implementation checklist, changelog, and full metrics — tokens, cost, time spent.</em></p>

</td>
<td width="50%">

<p align="center"><strong>Automated PR Lifecycle</strong></p>

<img src="docs/img/pr-automation.png" width="100%" alt="GitHub Issue activity showing automated label changes and project board transitions">

<p><em>Labels, project board status, and issue lifecycle managed automatically from start to merge.</em></p>

</td>
</tr>
</table>

### Why It's Different

Other tools give you autocomplete or one-shot code generation. Chief Wiggum gives you a **software engineering pipeline**:

- **Plan before coding** — Optional planning stage generates implementation strategy before writing a line of code
- **Security audit built in** — Every PR gets a security review; findings are automatically fixed and re-audited
- **Test coverage enforcement** — Tests are run, failures are fixed, coverage gaps are flagged
- **Validation gate** — A final independent review catches issues the implementation agent missed
- **Self-correcting loops** — When audit finds a vulnerability, it fixes and re-audits. When tests fail, it fixes and re-runs. The pipeline doesn't stop at "good enough"

### What It Does

- **Parallel execution** — Run up to N tasks concurrently, each in its own git worktree with zero cross-contamination
- **Full engineering pipeline** — Plan, implement, audit, test, document, validate — every PR goes through the same rigorous process
- **Self-healing** — Crashed workers auto-resume from their last step; flaky failures retry with exponential backoff
- **PR lifecycle management** — Addresses reviewer comments, syncs with main, resolves merge conflicts, merges approved PRs
- **Priority scheduling** — Tasks with plans, more dependents, and higher urgency run first; stale tasks age into higher priority
- **Dependency-aware** — Tasks respect their dependency graph and execute in the right order
- **Configurable pipelines** — Full pipeline for critical work, fast pipeline for simple tasks, or define your own per-task
- **Distributed mode** — Multiple machines pull tasks from the same GitHub Issues board

### Who It's For

- **Vibe developers** who want the speed of AI coding with the rigor of a real engineering process
- **Teams** offloading well-defined work (migrations, CRUD endpoints, test coverage, refactors) to an agent that follows the same standards they do
- **Anyone** building production software who refuses to trade quality for velocity

## Prerequisites

- **Linux/macOS** (Bash 4.0+)
- **Git** (2.20+)
- **Claude Code** (`claude` CLI installed and authenticated)
- **GitHub CLI** (`gh` installed and authenticated)
- **jq** (JSON processor)
- **setsid** (worker process isolation; macOS users: `brew install util-linux`)

## Installation

### Option 1: Global Install

```bash
./install.sh
export PATH="$HOME/.claude/chief-wiggum/bin:$PATH"
```

### Option 2: Run from Source

```bash
export WIGGUM_HOME=$(pwd)
export PATH="$WIGGUM_HOME/bin:$PATH"
```

## Quick Start

### 1. Initialize

```bash
cd /path/to/your/project
wiggum init
```

Creates `.ralph/kanban.md` for task definitions.

### 2. Define Tasks

Edit `.ralph/kanban.md`:

```markdown
## TASKS

- [ ] **[TASK-001]** Add user authentication
  - Description: Implement JWT-based auth with login/logout endpoints
  - Priority: HIGH
  - Dependencies: none

- [ ] **[TASK-002]** Add password reset flow
  - Description: Email-based password reset with token expiration
  - Priority: MEDIUM
  - Dependencies: TASK-001
```

Task markers: `[ ]` Pending, `[=]` In Progress, `[P]` Pending Approval, `[x]` Complete, `[*]` Failed, `[N]` Not Planned

### 3. Run

```bash
wiggum run                         # Start workers for pending tasks
wiggum run --max-workers 8         # Limit concurrent workers
wiggum run --plan                  # Enable planning step before execution
wiggum run --pipeline fast         # Use a specific pipeline
wiggum run --mode github           # Distributed mode with GitHub Issues
```

### 4. Monitor

```bash
wiggum status                      # Overview of all workers
wiggum monitor                     # Live combined logs
wiggum monitor split               # Split pane per worker
wiggum tui                         # Python-based monitoring UI
```

### 5. Review and Merge

```bash
wiggum pr list                     # List open PRs
wiggum pr view 123                 # View specific PR
wiggum pr merge 123                # Merge a specific PR
wiggum pr merge-all                # Merge all worker PRs
```

## Commands

| Command | Description |
|---------|-------------|
| `wiggum init` | Initialize project with `.ralph/` directory |
| `wiggum run` | Orchestrate workers for pending tasks |
| `wiggum status` | Show worker status overview |
| `wiggum monitor` | Live log viewer |
| `wiggum pr` | PR management (list, merge, sync, resolve, reset) |
| `wiggum worker` | Worker lifecycle (start, stop, resume, fix, merge) |
| `wiggum inspect` | Debug workers, pipelines, agents, activity logs |
| `wiggum validate` | Validate kanban format |
| `wiggum plan` | Create task plans in `.ralph/plans/` |
| `wiggum doctor` | Check environment and diagnose issues |
| `wiggum clean` | Remove worker worktrees |

## How It Works

### Worker Pipeline

For each task, Chief Wiggum:

1. Creates an isolated **git worktree**
2. Generates a **PRD** from the task specification
3. Runs a configurable **pipeline** of agents:
   - **Planning** (optional) — generates an implementation plan
   - **Execution** — implements the feature with supervised iteration
   - **Summary** — summarizes changes for PR description
   - **Security Audit** — reviews for vulnerabilities, auto-fixes findings
   - **Tests** — runs test coverage, fixes failures
   - **Documentation** — updates docs for changed code
   - **Validation** — final review gate
4. Creates a **Pull Request** with the changes

### Orchestrator Lifecycle

The orchestrator continuously manages workers beyond initial execution:

- **Auto-resume** — stopped/crashed workers are automatically resumed from their last pipeline step
- **Fix workers** — when PRs receive review comments, fix workers address them and push updates
- **Merge management** — PRs are automatically merged after approval, with conflict detection
- **Conflict resolution** — merge conflicts spawn resolver workers that rebase and fix
- **Priority scheduling** — tasks are prioritized by urgency, dependency depth, plan availability, and age

### Task Dependencies

Tasks can declare dependencies. A task only starts when all its dependencies are complete (`[x]`):

```markdown
- [ ] **[TASK-003]** Add API rate limiting
  - Dependencies: TASK-001, TASK-002
```

## Configuration

### Pipeline

Customize the agent pipeline in `config/pipelines/default.json`. Built-in pipelines:

| Pipeline | Use Case |
|----------|----------|
| `default` | Full pipeline: plan → execute → audit → test → docs → validate |
| `fast` | Streamlined: execute → followup → validate |
| `fix` | PR fix: address comments → sync main → test → push → merge |

Override per-project in `.ralph/pipeline.json` or per-task in `.ralph/pipelines/<TASK-ID>.json`.

### Project Settings

Override defaults in `.ralph/config.json`:

```json
{
  "max_workers": 4,
  "max_iterations": 20,
  "max_turns": 50,
  "runtime": {
    "backend": "claude"
  }
}
```

### Orchestrator Options

```bash
wiggum run --max-workers 4         # Concurrent worker limit (default: 4)
wiggum run --plan                  # Enable planning step
wiggum run --no-resume             # Don't auto-resume stopped workers
wiggum run --no-fix                # Don't spawn fix workers
wiggum run --no-merge              # Don't auto-merge PRs
wiggum run --mode github           # Distributed mode with GitHub Issues
wiggum run --fix-only              # Only fix existing PRs, don't start new tasks
```

## Debugging

```bash
wiggum inspect worker TASK-001     # Inspect worker state and files
wiggum inspect pipeline            # Show pipeline configuration
wiggum inspect agents              # List agents with configs
wiggum inspect activity            # View activity logs
wiggum inspect step TASK-001       # Show current pipeline step
wiggum run -vvv                    # Verbose logging
```

## Documentation

- [Pipeline Schema](spec/PIPELINE_SCHEMA.md) — Pipeline configuration and step types
- [Architecture](spec/ARCHITECTURE.md) — System design and internals
- [Agent Protocol](spec/AGENT_PROTOCOL.md) — Agent communication contract
- [Agent Development](docs/AGENT_DEV_GUIDE.md) — Writing custom agents
- [Runtime Schema](spec/RUNTIME_SCHEMA.md) — Backend-agnostic execution layer
- [GitHub Setup](docs/GITHUB_SETUP.md) — GitHub integration configuration

## License

MIT
