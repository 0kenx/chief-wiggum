# Pipeline Schema Specification

## Overview

The pipeline is an ordered array of steps. Steps execute sequentially by default.
Each step can optionally define result-based handlers (`on_result`) that override
the default control flow. The system is a bounded state machine where unhandled
results default to `PASS -> jump:next, FIX -> jump:prev , FAIL -> abort, SKIP -> jump:next`.

## Schema

```json
{
  "name": "<pipeline-name>",
  "steps": [ <step>, ... ]
}
```

### Step

```json
{
  "id": "<unique-step-id>",
  "agent": "<agent-type>",
  "max": <uint>,
  "on_max": "<jump-target>",
  "on_result": { <result-handlers> },
  "readonly": <bool>,
  "enabled_by": "<env-var>",
  "commit_after": <bool>,
  "config": { <agent-config> },
  "hooks": { "pre": [...], "post": [...] }
}
```

| Field | Required | Default | Description |
|-------|----------|---------|-------------|
| `id` | yes | — | Unique step identifier |
| `agent` | yes | — | Agent type to execute |
| `max` | no | 0 (unlimited) | Max times this step can be visited |
| `on_max` | no | `next` | Jump target when `max` is exceeded |
| `on_result` | no | `{}` | Per-result handlers (see below) |
| `readonly` | no | `false` | Git checkpoint before, restore after |
| `enabled_by` | no | — | Env var that must be `"true"` for step to run |
| `commit_after` | no | `false` | Auto-commit workspace changes after step |
| `config` | no | `{}` | Agent-specific configuration passed via step-config.json |
| `hooks` | no | `{}` | Pre/post hook functions |

### on_result

Maps gate result values to handlers. Unhandled results default to `jump:next`.

```json
"on_result": {
  "<RESULT_VALUE>": <handler>,
  ...
}
```

A handler is one of:

#### Jump Handler

```json
{ "jump": "<target>" }
```

#### Inline Agent Handler

```json
{
  "id": "<handler-step-id>",
  "agent": "<agent-type>",
  "max": <uint>,
  "on_max": "<jump-target>",
  "on_result": { <result-handlers> },
  "readonly": <bool>,
  "commit_after": <bool>,
  "config": { <agent-config> }
}
```

An inline agent handler runs a sub-step. After the inline agent completes:
- If the inline handler has its own `on_result`, dispatch on the inline agent's result.
- If no matching handler exists, default to re-running the parent step (implicit `jump:prev`
  since the handler was triggered by a result that needed remediation).

The `max` on an inline handler bounds how many times that handler can fire (global for workflow).

### Jump Targets

| Target | Meaning |
|--------|---------|
| `self` | Re-run the current step |
| `prev` | Jump to the previous step in array order |
| `next` | Continue to the next step (default for unhandled results) |
| `<id>` | Jump to step with matching `id` |
| `abort` | Halt pipeline with failure |

### Max Visits

The `max` field on a step bounds total visits across the pipeline run. When a step
has been visited `max` times and control would transfer to it again, the pipeline
jumps to the `on_max` target (default: `next`).

```json
{ "id": "audit", "agent": "...", "max": 3, "on_max": "next" }
```

| `on_max` value | Behavior when max exceeded |
|----------------|---------------------------|
| `next` | Give up on this step, continue pipeline (default) |
| `abort` | Halt pipeline with failure |
| `<id>` | Jump to a specific step |

Without `max`, a step can be visited unboundedly (not recommended — use `max` on
any step that participates in loops).

## Control Flow Rules

1. Steps execute in array order by default.
2. After a step completes, check `on_result` for the agent's gate result.
3. If a handler exists for the result, execute it (jump or inline agent).
4. If no handler exists, `jump:next`.
5. If `max` is exceeded on any step, jump to `on_max` target (default: `next`).
6. If control reaches past the last step, pipeline succeeds.
7. `abort` halts the pipeline immediately with failure status.

## Gate Result Values

Agents produce a `gate_result` in their output JSON. Standard values:

| Value | Typical Meaning |
|-------|-----------------|
| `PASS` | Quality check passed |
| `FAIL` | Quality check failed |
| `FIX` | Fixable issues found |
| `SKIP` | Not applicable |

Any string is valid as a gate result — agents and handlers are not limited to
these values. The pipeline dispatches on exact string match against `on_result` keys.

## Execution Semantics

### Default Behavior (no on_result)

```json
{ "id": "test", "agent": "engineering.test-coverage" }
```

Agent runs. Regardless of result, continue to next step.

### Jump on Failure

```json
{
  "id": "test",
  "agent": "engineering.test-coverage",
  "on_result": {
    "FAIL": { "jump": "abort" }
  }
}
```

FAIL aborts. All other results continue to next.

### Fix Loop (Inline Agent)

```json
{
  "id": "audit",
  "agent": "engineering.security-audit",
  "max": 3,
  "on_result": {
    "FIX": {
      "id": "audit-fix",
      "agent": "engineering.security-fix",
      "commit_after": true,
      "max": 2
    },
    "FAIL": { "jump": "abort" }
  }
}
```

Execution:
1. Run `security-audit`.
2. Result is FIX → run inline `security-fix`.
3. After fix, re-run `security-audit` (parent step, implicit `jump:prev`).
4. If audit returns PASS → `jump:next` (unhandled = default).
5. If audit returns FIX again → run fix again (if within `max`).
6. If `max` on audit (3) or fix (2) exceeded → `on_max` target (default: `next`).

### Inline Agent with its own on_result

```json
{
  "id": "audit",
  "agent": "engineering.security-audit",
  "max": 3,
  "on_result": {
    "FIX": {
      "id": "audit-fix",
      "agent": "engineering.security-fix",
      "max": 2,
      "on_result": {
        "PASS": { "jump": "self" },
        "FAIL": { "jump": "abort" }
      }
    }
  }
}
```

Here the fix agent's result controls flow:
- Fix returns PASS → `jump:self` (re-run parent audit to verify).
- Fix returns FAIL → abort.
- Fix returns FIX → unhandled in fix's on_result, so default = re-run parent (implicit `jump:prev`).

### Backward Jump

```json
{
  "id": "validation",
  "agent": "engineering.validation-review",
  "on_result": {
    "FAIL": { "jump": "execution" }
  }
}
```

Validation failure jumps back to execution step. Must have `max` on either
step to prevent infinite loops.

### Multi-Way Branch

```json
{
  "id": "triage",
  "agent": "system.triage",
  "on_result": {
    "SECURITY": { "jump": "audit" },
    "QUALITY":  { "jump": "review" },
    "TESTS":    { "jump": "test" },
    "PASS":     { "jump": "next" }
  }
}
```

Agent-computed multi-way dispatch. The agent acts as a router.

## Flattening Inline Agents

Inline agent handlers are syntactic sugar. Any inline handler can be flattened
into a top-level step with explicit jumps:

**Nested:**
```json
{
  "id": "audit",
  "agent": "engineering.security-audit",
  "max": 3,
  "on_result": {
    "FIX": { "id": "fix", "agent": "engineering.security-fix", "max": 2, "commit_after": true }
  }
}
```

**Flattened equivalent:**
```json
[
  {
    "id": "audit",
    "agent": "engineering.security-audit",
    "max": 3,
    "on_result": {
      "FIX": { "jump": "fix" }
    }
  },
  {
    "id": "fix",
    "agent": "engineering.security-fix",
    "max": 2,
    "commit_after": true,
    "on_result": {
      "PASS": { "jump": "audit" }
    }
  }
]
```

The inline form is preferred when the handler step is only reachable from one parent.

## Termination Guarantee

The pipeline guarantees termination if and only if every cycle in the step graph
has at least one step with a finite `max` whose `on_max` target breaks the cycle
(i.e., jumps forward or aborts). An `on_max` that jumps backward into the same
cycle does not guarantee termination unless the target also has a bounded `max`.

Recommended: set `max` on any step that can be the target of a backward jump
or self-reference. The default `on_max: "next"` degrades gracefully; use
`on_max: "abort"` to fail fast.

## Legacy Compatibility

The previous schema fields map to this model:

| Legacy Field | Equivalent |
|-------------|------------|
| `"blocking": true` | `"on_result": { "FAIL": {"jump":"abort"}, "STOP": {"jump":"abort"} }` |
| `"blocking": false` | (default — no on_result for FAIL) |
| `"fix": {...}` | `"on_result": { "FIX": { <inline-agent> } }` |
| `"depends_on": "X"` | Step X has `"on_result": { "FAIL": {"jump":"<skip-past-dependents>"} }` |

## Example: Full Pipeline

```json
{
  "name": "default",
  "steps": [
    {
      "id": "planning",
      "agent": "product.plan-mode",
      "readonly": true,
      "enabled_by": "WIGGUM_PLAN_MODE",
      "on_result": {
        "FAIL": { "jump": "abort" }
      }
    },
    {
      "id": "execution",
      "agent": "system.task-executor",
      "max": 3,
      "config": { "max_iterations": 20, "max_turns": 50, "supervisor_interval": 2 },
      "on_result": {
        "FAIL": { "jump": "abort" }
      }
    },
    {
      "id": "summary",
      "agent": "system.task-summarizer",
      "readonly": true
    },
    {
      "id": "audit",
      "agent": "engineering.security-audit",
      "max": 3,
      "readonly": true,
      "on_result": {
        "FIX": {
          "id": "audit-fix",
          "agent": "engineering.security-fix",
          "max": 2,
          "commit_after": true
        },
        "STOP": { "jump": "abort" }
      }
    },
    {
      "id": "test",
      "agent": "engineering.test-coverage",
      "max": 2,
      "commit_after": true,
      "on_result": {
        "FAIL": { "jump": "execution" }
      }
    },
    {
      "id": "docs",
      "agent": "product.documentation-writer",
      "commit_after": true
    },
    {
      "id": "validation",
      "agent": "engineering.validation-review",
      "readonly": true,
      "on_result": {
        "FAIL": { "jump": "execution" }
      }
    }
  ]
}
```
