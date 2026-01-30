# Runtime Schema

## Overview

The runtime module (`lib/runtime/`) provides a backend-agnostic execution layer for Chief Wiggum. It abstracts the CLI invocation, retry strategy, session management, and output parsing behind a defined interface, allowing the system to support multiple backends (Claude Code, OpenCode, etc.) without agents knowing which backend is active.

## Architecture

```
lib/runtime/
  backend-interface.sh    # Backend contract: all functions a backend must implement
  runtime.sh              # Backend loader + public API facade
  runtime-loop.sh         # Ralph loop (generic orchestration, delegates to backend)
  runtime-retry.sh        # Generic retry with backoff (delegates error classification)

lib/backend/
  claude/
    claude-backend.sh     # Implements backend-interface.sh for Claude Code
    usage-tracker.sh      # Claude-specific usage tracking
  opencode/
    opencode-backend.sh   # Skeleton stub with documented TODOs
```

## Backend Selection

The runtime discovers which backend to use at initialization. Priority order (highest first):

| Priority | Source | Example |
|----------|--------|---------|
| 1 | `WIGGUM_RUNTIME_BACKEND` env var | `WIGGUM_RUNTIME_BACKEND=opencode` |
| 2 | `.ralph/config.json` → `.runtime.backend` | `{"runtime": {"backend": "opencode"}}` |
| 3 | `config/config.json` → `.runtime.backend` | `{"runtime": {"backend": "claude"}}` |
| 4 | Default | `"claude"` |

## Public API

### `runtime_init()`

Initialize the runtime. Discovers and loads the backend. Safe to call multiple times (idempotent). Automatically called when `runtime.sh` is sourced.

### `run_agent_once(workspace, system_prompt, user_prompt, output_file, max_turns, session_id)`

Single-shot execution. Validates parameters, changes to workspace, builds CLI arguments via the backend, and executes with retry.

| Arg | Type | Description |
|-----|------|-------------|
| workspace | string | Directory to run in |
| system_prompt | string | System prompt for context |
| user_prompt | string | User prompt (the task) |
| output_file | string | Where to save output |
| max_turns | int | Max turns (default: 3) |
| session_id | string | Optional session ID for resume |

**Returns:** Exit code from backend.

### `run_agent_once_with_session(workspace, system_prompt, user_prompt, output_file, max_turns, session_id)`

Creates a new named session. Uses `--session-id` (not `--resume`) to create a session with a specific UUID. Used by live mode for initial session creation.

**Returns:** Exit code from backend.

### `run_agent_resume(session_id, prompt, output_file, max_turns)`

Resume an existing session with a new prompt. Used for generating summaries or continuing a conversation after the main work loop completes.

| Arg | Type | Description |
|-----|------|-------------|
| session_id | string | The session ID to resume |
| prompt | string | The prompt to send |
| output_file | string | Where to save output |
| max_turns | int | Maximum turns (default: 3) |

**Returns:** Exit code from backend.

### `run_ralph_loop(...)`

Iterative execution loop with optional supervision. See [Execution Patterns](#iterative-loop-ralph-loop) below.

### `run_ralph_loop_supervised(...)`

Backward-compatibility alias for `run_ralph_loop` with `supervisor_interval` defaulting to 2.

### `runtime_exec_with_retry(args...)`

Retry-wrapped backend invocation. Wraps `runtime_backend_invoke` with exponential backoff. Error classification is delegated to the backend via `runtime_backend_is_retryable()`.

**Backward-compat alias:** `run_claude_with_retry(args...)`

## Backend Interface

### Required Functions

Every backend **must** implement these functions. The interface file (`backend-interface.sh`) provides error-returning defaults.

#### `runtime_backend_init()`

Initialize the backend. Called once during `runtime_init()`. Load config, set env vars, validate binary exists.

#### `runtime_backend_invoke(args...)`

Raw CLI invocation primitive. No retry, no parsing. All CLI arguments passed as array elements. Returns exit code from the CLI.

#### `runtime_backend_build_exec_args(_out_args, workspace, system_prompt, user_prompt, output_file, max_turns, session_id)`

Build CLI arguments for single-shot execution using the nameref array pattern. Populates the caller's array by reference to avoid word-splitting issues.

```bash
local -a cli_args=()
runtime_backend_build_exec_args cli_args "$workspace" "$prompt" ...
runtime_exec_with_retry "${cli_args[@]}"
```

#### `runtime_backend_build_resume_args(_out_args, session_id, prompt, output_file, max_turns)`

Build CLI arguments for session resume using the nameref array pattern.

#### `runtime_backend_is_retryable(exit_code, stderr_file)`

Classify whether an error is retryable. Returns 0 if retryable, 1 if not.

#### `runtime_backend_extract_text(log_file)`

Extract plain text from backend-specific output format. Echoes the extracted text content.

#### `runtime_backend_extract_session_id(log_file)`

Extract session ID from backend output log. Echoes the session ID string (or empty if not supported).

### Optional Functions

Default implementations are provided in `backend-interface.sh`. Override as needed.

| Function | Default | Description |
|----------|---------|-------------|
| `runtime_backend_supports_sessions()` | `return 1` (no) | Whether backend supports session resumption |
| `runtime_backend_usage_update(ralph_dir)` | no-op | Update usage statistics |
| `runtime_backend_rate_limit_check(ralph_dir)` | `return 1` (OK) | Check if rate limited |
| `runtime_backend_rate_limit_wait()` | `sleep 60` | Wait for rate limit window to reset |
| `runtime_backend_generate_session_id()` | `uuidgen` | Generate a new unique session ID |
| `runtime_backend_name()` | `"unknown"` | Backend name for logging/config |

## Execution Patterns

### Single-Shot

```
Caller
  → run_agent_once()
    → runtime_backend_build_exec_args()  (populate CLI args array)
    → runtime_exec_with_retry()
      → runtime_backend_invoke()          (raw CLI call)
      → runtime_backend_is_retryable()    (on failure: retry or give up)
```

### Iterative Loop (Ralph Loop)

```
run_ralph_loop()
  ├─ runtime_backend_rate_limit_check()
  ├─ completion_check_fn()
  ├─ runtime_backend_generate_session_id()
  ├─ WORK PHASE
  │   ├─ runtime_backend_build_exec_args()
  │   └─ runtime_exec_with_retry()
  ├─ SUMMARY PHASE
  │   ├─ [sessions] runtime_backend_build_resume_args()
  │   ├─ [no sessions] runtime_backend_build_exec_args() with context
  │   └─ runtime_exec_with_retry()
  ├─ SUPERVISOR PHASE (every N iterations)
  │   ├─ runtime_backend_build_exec_args()
  │   └─ runtime_exec_with_retry()
  └─ sleep 2
```

**Session-less backends:** If `runtime_backend_supports_sessions()` returns 1 (no sessions), the summary phase runs a fresh invocation with the previous output included in the prompt context, instead of resuming the work session.

### Session Resume

```
Caller
  → run_agent_resume()
    → runtime_backend_build_resume_args()
    → runtime_exec_with_retry()
```

If the backend does not support sessions, `run_agent_resume` will fail. Callers should check `runtime_backend_supports_sessions()` first.

## Retry Strategy

Exponential backoff with configurable limits. Error classification is delegated to the backend.

### Backoff Formula

```
delay = min(initial_backoff * multiplier^attempt, max_backoff)
```

### Configuration Resolution

| Priority | Source | Key |
|----------|--------|-----|
| 1 | Env var | `WIGGUM_RUNTIME_MAX_RETRIES` |
| 2 | Env var (compat) | `WIGGUM_CLAUDE_MAX_RETRIES` |
| 3 | Config | `.runtime.backends.<backend>.max_retries` |
| 4 | Config (compat) | `.claude.max_retries` |
| 5 | Default | `3` |

### Default Retry Parameters

| Parameter | Default | Env Var |
|-----------|---------|---------|
| Max retries | 3 | `WIGGUM_RUNTIME_MAX_RETRIES` |
| Initial backoff | 5s | `WIGGUM_RUNTIME_INITIAL_BACKOFF` |
| Max backoff | 60s | `WIGGUM_RUNTIME_MAX_BACKOFF` |
| Backoff multiplier | 2 | `WIGGUM_RUNTIME_BACKOFF_MULTIPLIER` |

## Usage & Rate Limiting

The runtime provides a generic framework for usage tracking and rate limiting. Backend-specific implementations provide the actual data.

| Function | Claude Implementation | Default |
|----------|----------------------|---------|
| `runtime_backend_usage_update(ralph_dir)` | Parses `~/.claude/projects/` JSONL logs | no-op |
| `runtime_backend_rate_limit_check(ralph_dir)` | Checks 5-hour cycle prompt count vs threshold | never limited |
| `runtime_backend_rate_limit_wait()` | Waits for 5-hour cycle to reset | sleep 60 |

## Configuration

### `config/config.json`

```json
{
  "runtime": {
    "backend": "claude",
    "backends": {
      "claude": {
        "binary": "claude",
        "max_retries": 3,
        "initial_backoff": 5,
        "max_backoff": 60,
        "backoff_multiplier": 2
      }
    }
  },
  "claude": {
    "max_retries": 3,
    "initial_backoff_seconds": 5,
    "max_backoff_seconds": 60,
    "backoff_multiplier": 2
  }
}
```

The `claude` section is retained for backward compatibility. New configuration should use `runtime.backends.<name>`.

### `.ralph/config.json` (Project Override)

```json
{
  "runtime": {
    "backend": "opencode"
  }
}
```

### Environment Variable Override

`WIGGUM_RUNTIME_BACKEND=opencode` takes highest priority.

## Writing a New Backend

1. Create `lib/backend/<name>/<name>-backend.sh`
2. Source `backend-interface.sh` is already done by `runtime.sh` before your file loads
3. Implement all **required** functions (see [Required Functions](#required-functions))
4. Override any **optional** functions as needed
5. Test with: `WIGGUM_RUNTIME_BACKEND=<name> wiggum run`

### Skeleton Example

```bash
#!/usr/bin/env bash
set -euo pipefail

[ -n "${_MYBACKEND_LOADED:-}" ] && return 0
_MYBACKEND_LOADED=1

source "$WIGGUM_HOME/lib/core/logger.sh"

runtime_backend_name() { echo "mybackend"; }

runtime_backend_init() {
    MYBACKEND="${MYBACKEND:-mybackend}"
    log_debug "MyBackend initialized"
}

runtime_backend_invoke() {
    "$MYBACKEND" "$@"
}

runtime_backend_build_exec_args() {
    local -n _args="$1"
    local workspace="$2" system_prompt="$3" user_prompt="$4"
    local output_file="$5" max_turns="$6" session_id="${7:-}"
    _args=(--workspace "$workspace" --prompt "$user_prompt")
}

runtime_backend_build_resume_args() {
    local -n _args="$1"
    _args=(--resume "$2" --prompt "$3")
}

runtime_backend_is_retryable() {
    [[ "$1" -eq 5 ]] && return 0
    return 1
}

runtime_backend_extract_text() {
    cat "$1"  # Adjust for actual output format
}

runtime_backend_extract_session_id() {
    echo ""
}
```

## Backend Capabilities Matrix

| Capability | Claude | OpenCode |
|------------|--------|----------|
| Session support | Yes | TBD |
| Session resume | Yes | TBD |
| Usage tracking | Yes | No |
| Rate limiting | Yes | No |
| Output format | stream-JSON | TBD |
| Auth scoping | `ANTHROPIC_AUTH_TOKEN` | TBD |

## Backward Compatibility

Old `lib/claude/` files are preserved as thin shims that source from the runtime module:

| Old Path | Shim Target |
|----------|-------------|
| `lib/claude/run-claude-once.sh` | `lib/runtime/runtime.sh` |
| `lib/claude/run-claude-ralph-loop.sh` | `lib/runtime/runtime.sh` + `lib/runtime/runtime-loop.sh` |
| `lib/claude/run-claude-resume.sh` | `lib/runtime/runtime.sh` |
| `lib/claude/retry-strategy.sh` | `lib/runtime/runtime-retry.sh` |
| `lib/claude/usage-tracker.sh` | `lib/backend/claude/usage-tracker.sh` |

All existing function names (`run_agent_once`, `run_agent_resume`, `run_ralph_loop`, `run_claude_with_retry`, etc.) are preserved and work through both old and new source paths.
