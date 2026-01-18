#!/usr/bin/env bash
# Validates that tool operations stay within workspace boundaries
# Exit codes: 0 = allow, 2 = block with error

# Read JSON input from stdin
input=$(cat)

# Extract tool name and parameters from tool_input
tool=$(echo "$input" | jq -r '.tool // empty')
file_path=$(echo "$input" | jq -r '.tool_input.file_path // empty')
command=$(echo "$input" | jq -r '.tool_input.command // empty')

# Get workspace directory (passed as env var by worker)
workspace="$WORKER_WORKSPACE"

# Debug logging (if enabled)
if [[ "${DEBUG_HOOKS:-false}" == "true" ]]; then
    echo "[HOOK DEBUG] Tool: $tool" >&2
    echo "[HOOK DEBUG] File path: $file_path" >&2
    echo "[HOOK DEBUG] Workspace: $workspace" >&2
fi

# If no workspace is set, something is wrong - allow but log warning
if [[ -z "$workspace" ]]; then
    echo "WARNING: WORKER_WORKSPACE not set - path validation disabled" >&2
    exit 0
fi

# If no file_path and no command, allow (e.g., some tools don't have paths)
if [[ -z "$file_path" && -z "$command" ]]; then
    exit 0
fi

# Validate file_path if present (Edit, Write, Read tools)
if [[ -n "$file_path" ]]; then
    # Resolve to absolute path (use -m to allow non-existent files)
    abs_path=$(realpath -m "$file_path" 2>/dev/null || echo "$file_path")
    workspace_abs=$(realpath "$workspace" 2>/dev/null)

    # Check if path is the PRD file (allowed exception)
    prd_path="$workspace/../prd.md"
    prd_abs=$(realpath -m "$prd_path" 2>/dev/null)

    if [[ "$abs_path" == "$prd_abs" ]]; then
        # Allow PRD access (needed to mark tasks complete)
        exit 0
    elif [[ "$abs_path" != "$workspace_abs"* ]]; then
        # Path is outside workspace - BLOCK
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        echo "❌ WORKSPACE BOUNDARY VIOLATION BLOCKED" >&2
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        echo "" >&2
        echo "Tool: $tool" >&2
        echo "Attempted path: $abs_path" >&2
        echo "Workspace boundary: $workspace_abs" >&2
        echo "" >&2
        echo "You can only access files within your workspace directory." >&2
        echo "Exception: ../prd.md is allowed for task tracking." >&2
        echo "" >&2
        echo "Use relative paths (e.g., ./file.txt or file.txt) instead." >&2
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        exit 2  # Block with error
    fi
fi

# Validate Bash commands for dangerous path operations
if [[ "$tool" == "Bash" && -n "$command" ]]; then
    # Check for cd commands that try to escape workspace
    if echo "$command" | grep -qE 'cd[[:space:]]+(/|\.\./)'; then
        # Check if cd target is outside workspace
        cd_target=$(echo "$command" | grep -oE 'cd[[:space:]]+[^;|&]+' | sed 's/cd[[:space:]]*//' | head -1)

        if [[ -n "$cd_target" ]]; then
            # Resolve cd target
            if [[ "$cd_target" == /* ]]; then
                # Absolute path
                abs_cd=$(realpath -m "$cd_target" 2>/dev/null || echo "$cd_target")
                workspace_abs=$(realpath "$workspace" 2>/dev/null)

                if [[ "$abs_cd" != "$workspace_abs"* ]]; then
                    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                    echo "❌ WORKSPACE BOUNDARY VIOLATION BLOCKED" >&2
                    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                    echo "" >&2
                    echo "Tool: Bash (cd command)" >&2
                    echo "Attempted to cd to: $abs_cd" >&2
                    echo "Workspace boundary: $workspace_abs" >&2
                    echo "" >&2
                    echo "You must stay within your workspace directory." >&2
                    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                    exit 2  # Block
                fi
            fi
        fi
    fi

    # Check for file operations with absolute paths outside workspace
    # Look for common patterns like: cat /path, vim /path, echo > /path, etc.
    if echo "$command" | grep -qoE '[[:space:]]\/[^[:space:]]+'; then
        # Extract absolute paths from command
        for abs_cmd_path in $(echo "$command" | grep -oE '[[:space:]]\/[^[:space:]]+' | sed 's/^[[:space:]]*//'); do
            # Skip common system paths that are safe
            if [[ "$abs_cmd_path" =~ ^/(bin|usr|lib|etc|dev|proc|sys)/ ]]; then
                continue
            fi

            # Check if this path is within workspace
            resolved=$(realpath -m "$abs_cmd_path" 2>/dev/null || echo "$abs_cmd_path")
            workspace_abs=$(realpath "$workspace" 2>/dev/null)

            if [[ "$resolved" != "$workspace_abs"* ]]; then
                echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                echo "❌ WORKSPACE BOUNDARY VIOLATION BLOCKED" >&2
                echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                echo "" >&2
                echo "Tool: Bash" >&2
                echo "Command contains path outside workspace: $abs_cmd_path" >&2
                echo "Resolved to: $resolved" >&2
                echo "Workspace boundary: $workspace_abs" >&2
                echo "" >&2
                echo "Use relative paths or stay within your workspace." >&2
                echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                exit 2  # Block
            fi
        done
    fi
fi

# Allow if all checks pass
exit 0
