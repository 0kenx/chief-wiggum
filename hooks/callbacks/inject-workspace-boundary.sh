#!/usr/bin/env bash
# inject-workspace-boundary.sh - Inject workspace boundary instructions into Task tool prompts
#
# This hook intercepts Task tool calls (subagent spawns) and modifies the prompt
# to include workspace boundary constraints. This ensures subagents stay within
# the worker's isolated workspace.
#
# Exit codes: 0 = success (modified input returned)

set -euo pipefail

# Read JSON input from stdin
input=$(cat)

# Get workspace directory (WORKER_WORKSPACE set by worker, CLAUDE_PROJECT_DIR set by Claude Code)
workspace="${WORKER_WORKSPACE:-${CLAUDE_PROJECT_DIR:-}}"
worker_dir="${WORKER_DIR:-}"

# If no workspace is set, allow without modification
if [[ -z "$workspace" ]]; then
    echo '{"hookSpecificOutput":{"hookEventName":"PreToolUse","permissionDecision":"allow"}}'
    exit 0
fi

# Extract original prompt and other fields
original_prompt=$(echo "$input" | jq -r '.tool_input.prompt // empty')
subagent_type=$(echo "$input" | jq -r '.tool_input.subagent_type // empty')
description=$(echo "$input" | jq -r '.tool_input.description // empty')

# If no prompt, allow without modification
if [[ -z "$original_prompt" ]]; then
    echo '{"hookSpecificOutput":{"hookEventName":"PreToolUse","permissionDecision":"allow"}}'
    exit 0
fi

# Build the workspace boundary instruction
boundary_instruction="CRITICAL WORKSPACE BOUNDARY CONSTRAINT:

You are operating within a restricted workspace. Your workspace boundary is:
  ${workspace}

SECURITY RULES - YOU MUST FOLLOW THESE:
1. Do NOT explore, read, list, or reference files outside this workspace
2. Do NOT use absolute paths that don't start with your workspace path
3. Use ONLY relative paths (e.g., ./src, ../prd.md) for file operations
4. If you discover absolute paths outside your workspace, do NOT use them
5. The parent directory '../' is allowed ONLY for accessing ../prd.md
6. The .ralph/plans/ directory is readable for implementation plans (read-only)
7. The .ralph/memory/ directory is readable for project memory and lessons learned (read-only)

Any file paths you return or suggest MUST be within: ${workspace}

---

"

# Combine boundary instruction with original prompt
modified_prompt="${boundary_instruction}${original_prompt}"

# Log the modification if worker_dir is set
if [[ -n "$worker_dir" ]]; then
    log_file="$worker_dir/hook-decisions.log"
    timestamp=$(date -Iseconds)
    echo "[$timestamp] MODIFY | tool=Task | subagent=$subagent_type | injected workspace boundary" >> "$log_file" 2>/dev/null || true
fi

# Build the response JSON with modified input
# Using jq to properly escape the modified prompt
jq -n \
    --arg prompt "$modified_prompt" \
    --arg subagent_type "$subagent_type" \
    --arg description "$description" \
    '{
        "hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "permissionDecision": "allow",
            "updatedInput": {
                "prompt": $prompt,
                "subagent_type": $subagent_type,
                "description": $description
            }
        }
    }'
