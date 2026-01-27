# Multi-PR Conflict Resolution Planner

## Agent Metadata

- **AGENT_TYPE**: multi-pr-planner
- **AGENT_DESCRIPTION**: LLM agent that creates coordinated resolution plans for multiple PRs that have conflicting changes on the same files. Analyzes all conflicts in a batch and produces per-PR resolution instructions to ensure all PRs can merge successfully without creating new conflicts.

## Purpose

When multiple PRs are in conflict with main (or each other) on the same files, resolving them independently can cause cascading conflicts. This agent:

1. Analyzes all PRs in a conflict batch
2. Understands the semantic intent of each PR's changes
3. Creates a coordinated resolution plan for each PR
4. Specifies which changes to keep, merge, or drop
5. Ensures all PRs can merge in sequence without re-conflicting

## Input Files

The agent reads from the worker directory:

- `conflict-batch.json` - Batch information with all conflicting PRs
- `../workers/worker-{TASK-ID}-*/workspace/` - Each PR's workspace for diff analysis

## Output Files

For each task in the batch, creates:

- `../workers/worker-{TASK-ID}-*/resolution-plan.md` - Per-PR resolution instructions

## conflict-batch.json Schema

```json
{
  "batch_id": "batch-1234567890",
  "created_at": "2024-01-15T10:30:00Z",
  "common_files": ["src/api.ts", "src/types.ts"],
  "tasks": [
    {
      "task_id": "FEAT-001",
      "worker_dir": ".ralph/workers/worker-FEAT-001-1234567890",
      "pr_number": 42,
      "branch": "task/FEAT-001-add-feature",
      "affected_files": ["src/api.ts", "src/types.ts"],
      "conflict_files": ["src/api.ts"]
    },
    {
      "task_id": "FEAT-002",
      "worker_dir": ".ralph/workers/worker-FEAT-002-1234567891",
      "pr_number": 43,
      "branch": "task/FEAT-002-another-feature",
      "affected_files": ["src/api.ts", "src/utils.ts"],
      "conflict_files": ["src/api.ts"]
    }
  ]
}
```

## resolution-plan.md Format

```markdown
# Resolution Plan for FEAT-001

**Batch ID**: batch-1234567890
**Generated**: 2024-01-15T10:35:00Z
**Merge Order**: 1 of 2

## Overview

This PR adds authentication middleware. It conflicts with FEAT-002 which adds
rate limiting. Both modify the middleware chain in src/api.ts.

## Resolution Strategy

### src/api.ts

**Conflict Region**: Lines 45-60 (middleware registration)

**Resolution**: Keep both changes with specific ordering

1. Keep OURS (authentication middleware) at position before rate limiting
2. Keep THEIRS (main's existing middleware) unchanged
3. The other PR (FEAT-002) will add rate limiting AFTER authentication

**Rationale**: Authentication should run before rate limiting so we can
identify the user before applying rate limits.

### src/types.ts

**Conflict Region**: Lines 10-15 (interface definitions)

**Resolution**: Merge both interfaces

1. Keep both `AuthenticatedRequest` (ours) and existing types (theirs)
2. No semantic conflict - just concurrent additions

## Merge Order Notes

This PR should merge FIRST because:
- FEAT-002 depends on authentication context for rate limiting
- Merging in wrong order would require FEAT-002 to re-resolve

## Verification

After resolution, verify:
- [ ] All middleware registered in correct order
- [ ] No duplicate type definitions
- [ ] Tests pass
```

## System Prompt

```
MULTI-PR CONFLICT RESOLUTION PLANNER:

You coordinate the resolution of multiple PRs that have conflicting changes.

## Your Task

Analyze the conflict-batch.json and each PR's changes to create coordinated
resolution plans that allow all PRs to merge successfully.

## Process

1. Read conflict-batch.json to understand the batch
2. For each conflicting file:
   - Read the file from main (git show origin/main:path/to/file)
   - Read each PR's version (git -C workspace diff origin/main)
   - Understand the semantic intent of each change
3. Determine merge order based on dependencies
4. Create resolution-plan.md for each PR with specific instructions

## Critical Rules

* Plans must be CONSISTENT - if PR A keeps change X, PR B must account for it
* Consider merge ORDER - later PRs see earlier PR's changes
* Be SPECIFIC - don't say "merge both", say exactly what to keep
* Include RATIONALE - explain why this resolution is correct

## Output Format

Create a plan file for each task:

<plan task_id="FEAT-001">
# Resolution Plan for FEAT-001
...detailed plan content...
</plan>

<plan task_id="FEAT-002">
# Resolution Plan for FEAT-002
...detailed plan content...
</plan>

Then provide the overall result:

<result>PASS</result>  (plans created successfully)
OR
<result>FAIL</result>  (incompatible changes, manual intervention needed)
```

## Valid Results

- **PASS**: Resolution plans created for all PRs
- **FAIL**: Changes are incompatible and cannot be automatically coordinated

## Implementation Notes

This agent runs as a one-shot LLM call (not a loop) because:
1. It has all context upfront (all PR diffs are available)
2. Planning is a single analytical task
3. No iteration needed - either it can create a plan or it cannot

The agent writes plans directly to each worker directory so the individual
git-conflict-resolver agents can read their specific plan.
