# Chief Wiggum

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Bash](https://img.shields.io/badge/Language-Bash-blue)](https://www.gnu.org/software/bash/)

**Chief Wiggum** is an agentic task runner that autonomously executes software engineering tasks using Claude Code. Define tasks in a Kanban board, and Chief Wiggum spawns isolated workers that implement features, run tests, and create pull requests.

![Chief Wiggum](docs/chief_wiggum.jpeg)

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
```

Task markers:
- `[ ]` Pending
- `[=]` In Progress
- `[x]` Complete
- `[*]` Failed

### 3. Run

```bash
wiggum run                    # Start workers for pending tasks
wiggum run --max-workers 8    # Limit concurrent workers
```

### 4. Monitor

```bash
wiggum status          # Overview of all workers
wiggum monitor         # Live combined logs
wiggum monitor split   # Split pane per worker
```

### 5. Review

```bash
wiggum review list           # List open PRs
wiggum review pr 123 view    # View specific PR
wiggum review merge-all      # Merge all worker PRs
```

## Commands

| Command | Description |
|---------|-------------|
| `wiggum init` | Initialize project with `.ralph/` directory |
| `wiggum run` | Start workers for pending tasks |
| `wiggum status` | Show worker status overview |
| `wiggum monitor` | Live log viewer |
| `wiggum review` | PR management |
| `wiggum validate` | Validate kanban format |
| `wiggum clean` | Remove worker worktrees |
| `wiggum inspect` | Debug workers, pipelines, agents |

## How It Works

For each task, Chief Wiggum:

1. Creates an isolated **git worktree**
2. Generates a **PRD** from the task specification
3. Runs a **pipeline** of agents (execution → audit → test → docs → validation)
4. Creates a **Pull Request** with the changes

Workers are fully isolated and can run in parallel without conflicts.

## Configuration

### Pipeline

Customize the agent pipeline in `config/pipelines/default.json`. See [docs/PIPELINE-SCHEMA.md](docs/PIPELINE-SCHEMA.md).

### Project Settings

Override defaults in `.ralph/config.json`:

```json
{
  "max_workers": 4,
  "max_iterations": 20,
  "max_turns": 50
}
```

## Documentation

- [Pipeline Schema](docs/PIPELINE-SCHEMA.md) - Configure agent pipelines
- [Architecture](docs/ARCHITECTURE.md) - Developer guide and internals
- [Agent Development](docs/AGENT_DEV_GUIDE.md) - Writing custom agents

## License

MIT
