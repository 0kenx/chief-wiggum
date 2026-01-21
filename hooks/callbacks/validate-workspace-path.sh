#!/usr/bin/env bash
# Validates that tool operations stay within workspace boundaries
# Exit codes: 0 = allow, 2 = block with error

# Read JSON input from stdin
input=$(cat)

# Extract tool name and parameters from tool_input
tool=$(echo "$input" | jq -r '.tool // empty')
file_path=$(echo "$input" | jq -r '.tool_input.file_path // empty')
command=$(echo "$input" | jq -r '.tool_input.command // empty')
# For Glob/Grep tools, extract the 'path' parameter
search_path=$(echo "$input" | jq -r '.tool_input.path // empty')

# Get workspace directory (passed as env var by worker)
workspace="$WORKER_WORKSPACE"
worker_dir="${WORKER_DIR:-}"

# Audit trail logging function
# Logs all hook decisions (allow/block) to worker's hook-decisions.log
log_hook_decision() {
    local decision="$1"  # ALLOW or BLOCK
    local tool="$2"
    local path="$3"
    local reason="${4:-}"

    # Only log if WORKER_DIR is set (we're in a worker context)
    if [[ -n "$worker_dir" ]]; then
        local log_file="$worker_dir/hook-decisions.log"
        local timestamp
        timestamp=$(date -Iseconds)
        if [[ -n "$reason" ]]; then
            echo "[$timestamp] $decision | tool=$tool | path=$path | reason=$reason" >> "$log_file"
        else
            echo "[$timestamp] $decision | tool=$tool | path=$path" >> "$log_file"
        fi
    fi
}

# Debug logging (if enabled)
if [[ "${DEBUG_HOOKS:-false}" == "true" ]]; then
    echo "[HOOK DEBUG] Tool: $tool" >&2
    echo "[HOOK DEBUG] File path: $file_path" >&2
    echo "[HOOK DEBUG] Search path: $search_path" >&2
    echo "[HOOK DEBUG] Workspace: $workspace" >&2
fi

# If no workspace is set, something is wrong - allow but log warning
if [[ -z "$workspace" ]]; then
    echo "WARNING: WORKER_WORKSPACE not set - path validation disabled" >&2
    exit 0
fi

# If no file_path, no search_path, and no command, allow (e.g., some tools don't have paths)
if [[ -z "$file_path" && -z "$search_path" && -z "$command" ]]; then
    exit 0
fi

# Helper function to validate path is within workspace
# Returns 0 if valid, 1 if invalid
validate_path_within_workspace() {
    local path="$1"
    local workspace_abs
    workspace_abs=$(realpath "$workspace" 2>/dev/null)

    # Check for path traversal patterns
    if [[ "$path" =~ \.\. ]]; then
        echo "[VALIDATION] Path contains .. traversal: $path" >&2
        # Still resolve and check, but log the attempt
    fi

    # Resolve to absolute path (use -m to allow non-existent files)
    local abs_path
    abs_path=$(realpath -m "$path" 2>/dev/null || echo "$path")

    # Check if it's a symlink and resolve it
    if [[ -L "$path" ]]; then
        # Symlink detected - resolve to actual target
        local link_target
        link_target=$(readlink -f "$path" 2>/dev/null || readlink "$path" 2>/dev/null)
        if [[ -n "$link_target" ]]; then
            echo "[VALIDATION] Symlink detected: $path -> $link_target" >&2
            abs_path=$(realpath -m "$link_target" 2>/dev/null || echo "$link_target")
        fi
    fi

    # Check if path is the PRD file (allowed exception)
    local prd_path="$workspace/../prd.md"
    local prd_abs
    prd_abs=$(realpath -m "$prd_path" 2>/dev/null)

    if [[ "$abs_path" == "$prd_abs" ]]; then
        # Allow PRD access (needed to mark tasks complete)
        return 0
    elif [[ "$abs_path" != "$workspace_abs"* ]]; then
        # Path is outside workspace
        return 1
    fi

    return 0
}

# Validate file_path if present (Edit, Write, Read tools)
if [[ -n "$file_path" ]]; then
    workspace_abs=$(realpath "$workspace" 2>/dev/null)

    # Check for path traversal attempts with ..
    if [[ "$file_path" =~ \.\. ]]; then
        echo "[SECURITY] Path traversal attempt detected: $file_path" >&2
    fi

    # Check if path is a symlink before resolution
    if [[ -L "$file_path" ]]; then
        link_target=$(readlink -f "$file_path" 2>/dev/null || readlink "$file_path" 2>/dev/null)
        echo "[SECURITY] Symlink resolution: $file_path -> $link_target" >&2
    fi

    # Use validation helper function
    if ! validate_path_within_workspace "$file_path"; then
        # Get resolved paths for error message
        abs_path=$(realpath -m "$file_path" 2>/dev/null || echo "$file_path")

        # Check for symlink target
        if [[ -L "$file_path" ]]; then
            link_target=$(readlink -f "$file_path" 2>/dev/null || readlink "$file_path" 2>/dev/null)
            if [[ -n "$link_target" ]]; then
                abs_path="$abs_path (symlink -> $(realpath -m "$link_target" 2>/dev/null || echo "$link_target"))"
            fi
        fi

        # Path is outside workspace - BLOCK
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        echo "❌ WORKSPACE BOUNDARY VIOLATION BLOCKED" >&2
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        echo "" >&2
        echo "Tool: $tool" >&2
        echo "Attempted path: $abs_path" >&2
        echo "Workspace boundary: $workspace_abs" >&2
        echo "" >&2

        # Additional context for specific bypass attempts
        if [[ "$file_path" =~ \.\. ]]; then
            echo "⚠️  Path traversal (..) detected in path" >&2
        fi
        if [[ -L "$file_path" ]]; then
            echo "⚠️  Symlink bypass attempt detected" >&2
        fi

        echo "" >&2
        echo "You can only access files within your workspace directory." >&2
        echo "Exception: ../prd.md is allowed for task tracking." >&2
        echo "" >&2
        echo "Use relative paths (e.g., ./file.txt or file.txt) instead." >&2
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        log_hook_decision "BLOCK" "$tool" "$file_path" "file path outside workspace"
        exit 2  # Block with error
    fi
fi

# Validate search_path if present (Glob, Grep tools)
if [[ -n "$search_path" ]]; then
    workspace_abs=$(realpath "$workspace" 2>/dev/null)

    # Use validation helper function
    if ! validate_path_within_workspace "$search_path"; then
        # Get resolved paths for error message
        abs_path=$(realpath -m "$search_path" 2>/dev/null || echo "$search_path")

        # Path is outside workspace - BLOCK
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        echo "❌ WORKSPACE BOUNDARY VIOLATION BLOCKED" >&2
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        echo "" >&2
        echo "Tool: $tool" >&2
        echo "Attempted search path: $abs_path" >&2
        echo "Workspace boundary: $workspace_abs" >&2
        echo "" >&2
        echo "You can only search files within your workspace directory." >&2
        echo "Use relative paths (e.g., ./src or src) instead." >&2
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        log_hook_decision "BLOCK" "$tool" "$search_path" "search path outside workspace"
        exit 2  # Block with error
    fi
fi

# Validate Bash commands for dangerous path operations
if [[ "$tool" == "Bash" && -n "$command" ]]; then
    workspace_abs=$(realpath "$workspace" 2>/dev/null)

    # Block ALL git commands - git operations are handled by worker scripts
    # Workers should not use git directly as it can cause confusion and conflicts
    if echo "$command" | grep -qE '(^|[;&|])[[:space:]]*(git[[:space:]]|git$)'; then
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        echo "❌ GIT COMMAND BLOCKED" >&2
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        echo "" >&2
        echo "Tool: Bash" >&2
        echo "Command: $command" >&2
        echo "" >&2
        echo "Git commands are not allowed in worker sessions." >&2
        echo "" >&2
        echo "Reasons:" >&2
        echo "  - Git commits and PRs are handled automatically by worker scripts" >&2
        echo "  - Git status in worktrees can be misleading" >&2
        echo "  - Direct git usage can cause conflicts with the orchestration system" >&2
        echo "" >&2
        echo "If you need version control information, check the PRD or task description." >&2
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        log_hook_decision "BLOCK" "$tool" "git" "git commands not allowed in workers"
        exit 2  # Block
    fi

    # Check for path traversal patterns in commands
    if echo "$command" | grep -qE '\.\./|\.\.[[:space:]]|/\.\.'; then
        echo "[SECURITY] Path traversal pattern (..) detected in command: $command" >&2
    fi

    # Check for symlink manipulation commands
    if echo "$command" | grep -qE '^[[:space:]]*(ln[[:space:]]+-s|readlink|realpath)'; then
        echo "[SECURITY] Symlink operation detected in command" >&2
    fi

    # Check for cd commands that try to escape workspace
    if echo "$command" | grep -qE 'cd[[:space:]]+'; then
        # Extract cd target - handle various formats
        cd_target=$(echo "$command" | grep -oE 'cd[[:space:]]+("[^"]+"|'\''[^'\'']+'\''|[^;|&[:space:]]+)' | sed -E 's/cd[[:space:]]+//; s/^["'\'']//; s/["'\'']$//' | head -1)

        if [[ -n "$cd_target" ]]; then
            # Resolve cd target relative to current workspace
            if [[ "$cd_target" == /* ]]; then
                # Absolute path
                abs_cd=$(realpath -m "$cd_target" 2>/dev/null || echo "$cd_target")
            else
                # Relative path - resolve from workspace
                abs_cd=$(realpath -m "$workspace/$cd_target" 2>/dev/null || echo "$workspace/$cd_target")
            fi

            # Check if resolved path is outside workspace
            if [[ "$abs_cd" != "$workspace_abs"* ]]; then
                echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                echo "❌ WORKSPACE BOUNDARY VIOLATION BLOCKED" >&2
                echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                echo "" >&2
                echo "Tool: Bash (cd command)" >&2
                echo "Attempted to cd to: $cd_target" >&2
                echo "Resolved path: $abs_cd" >&2
                echo "Workspace boundary: $workspace_abs" >&2
                echo "" >&2

                if [[ "$cd_target" =~ \.\. ]]; then
                    echo "⚠️  Path traversal (..) detected in cd command" >&2
                    echo "" >&2
                fi

                echo "You must stay within your workspace directory." >&2
                echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                log_hook_decision "BLOCK" "$tool" "$cd_target" "cd target outside workspace"
                exit 2  # Block
            fi
        fi
    fi

    # Check for file operations with absolute paths outside workspace
    # Look for common patterns like: cat /path, vim /path, echo > /path, etc.
    if echo "$command" | grep -qoE '[[:space:]]\/[^[:space:]]+'; then
        # Extract absolute paths from command
        for abs_cmd_path in $(echo "$command" | grep -oE '[[:space:]]\/[^[:space:]]+' | sed 's/^[[:space:]]*//'); do
            # Skip common system paths that are safe
            if [[ "$abs_cmd_path" =~ ^/(bin|usr|lib|etc|dev|proc|sys|tmp)/ ]]; then
                continue
            fi

            # Skip if it's a flag (starts with -)
            if [[ "$abs_cmd_path" =~ ^/- ]]; then
                continue
            fi

            # Check if this path is within workspace (validate using helper)
            if ! validate_path_within_workspace "$abs_cmd_path"; then
                resolved=$(realpath -m "$abs_cmd_path" 2>/dev/null || echo "$abs_cmd_path")

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
                log_hook_decision "BLOCK" "$tool" "$abs_cmd_path" "absolute path outside workspace"
                exit 2  # Block
            fi
        done
    fi

    # Check for relative path patterns that could escape workspace
    # Look for patterns like ../../, ../../../, etc.
    if echo "$command" | grep -qE '(\.\./){2,}'; then
        # Extract and validate these patterns
        echo "[SECURITY] Multiple path traversal patterns detected in command" >&2

        # Try to extract specific paths with multiple ../ patterns
        for suspicious_path in $(echo "$command" | grep -oE '(\.\./)+(\.\./?|[^[:space:]]+)' || true); do
            if [[ -n "$suspicious_path" ]]; then
                # Resolve relative to workspace
                resolved=$(realpath -m "$workspace/$suspicious_path" 2>/dev/null || echo "$workspace/$suspicious_path")

                if [[ "$resolved" != "$workspace_abs"* ]]; then
                    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                    echo "❌ WORKSPACE BOUNDARY VIOLATION BLOCKED" >&2
                    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                    echo "" >&2
                    echo "Tool: Bash" >&2
                    echo "Path traversal attempt detected: $suspicious_path" >&2
                    echo "Resolved to: $resolved" >&2
                    echo "Workspace boundary: $workspace_abs" >&2
                    echo "" >&2
                    echo "⚠️  Multiple path traversal (..) components detected" >&2
                    echo "" >&2
                    echo "Use paths relative to workspace without .. traversal." >&2
                    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                    log_hook_decision "BLOCK" "$tool" "$suspicious_path" "path traversal escape"
                    exit 2  # Block
                fi
            fi
        done
    fi

    # Check for command substitution that might access paths outside workspace
    # Patterns: $(command) and `command`
    if echo "$command" | grep -qE '\$\([^)]+\)|`[^`]+`'; then
        echo "[SECURITY] Command substitution detected - checking for path escapes" >&2

        # Extract paths from within command substitutions
        # Look for cat, read, source, or file access patterns inside $() or ``
        for subst_path in $(echo "$command" | grep -oE '\$\([^)]*\/[^)]+\)|`[^`]*\/[^`]+`' | grep -oE '\/[^[:space:])"`]+' || true); do
            # Skip safe system paths
            if [[ "$subst_path" =~ ^/(bin|usr|lib|dev|proc|sys|tmp)/ ]]; then
                continue
            fi

            # Check if path is outside workspace
            if ! validate_path_within_workspace "$subst_path"; then
                resolved=$(realpath -m "$subst_path" 2>/dev/null || echo "$subst_path")

                echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                echo "❌ WORKSPACE BOUNDARY VIOLATION BLOCKED" >&2
                echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                echo "" >&2
                echo "Tool: Bash" >&2
                echo "Command substitution contains path outside workspace: $subst_path" >&2
                echo "Resolved to: $resolved" >&2
                echo "Workspace boundary: $workspace_abs" >&2
                echo "" >&2
                echo "⚠️  Path access within \$() or backticks detected" >&2
                echo "" >&2
                echo "You cannot access files outside your workspace, even within command substitutions." >&2
                echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                log_hook_decision "BLOCK" "$tool" "$subst_path" "path in command substitution outside workspace"
                exit 2  # Block
            fi
        done
    fi

    # Check for process substitution that might access paths outside workspace
    # Patterns: <(command) and >(command)
    if echo "$command" | grep -qE '<\([^)]+\)|>\([^)]+\)'; then
        echo "[SECURITY] Process substitution detected - checking for path escapes" >&2

        # Extract paths from within process substitutions
        for proc_path in $(echo "$command" | grep -oE '[<>]\([^)]*\/[^)]+\)' | grep -oE '\/[^[:space:])]+' || true); do
            # Skip safe system paths
            if [[ "$proc_path" =~ ^/(bin|usr|lib|dev|proc|sys|tmp)/ ]]; then
                continue
            fi

            # Check if path is outside workspace
            if ! validate_path_within_workspace "$proc_path"; then
                resolved=$(realpath -m "$proc_path" 2>/dev/null || echo "$proc_path")

                echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                echo "❌ WORKSPACE BOUNDARY VIOLATION BLOCKED" >&2
                echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                echo "" >&2
                echo "Tool: Bash" >&2
                echo "Process substitution contains path outside workspace: $proc_path" >&2
                echo "Resolved to: $resolved" >&2
                echo "Workspace boundary: $workspace_abs" >&2
                echo "" >&2
                echo "⚠️  Path access within <() or >() detected" >&2
                echo "" >&2
                echo "You cannot access files outside your workspace, even within process substitutions." >&2
                echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                log_hook_decision "BLOCK" "$tool" "$proc_path" "path in process substitution outside workspace"
                exit 2  # Block
            fi
        done
    fi

    # Check for environment variable paths that might escape workspace
    # Common patterns: $HOME, $PWD/../, ${HOME}, etc.
    if echo "$command" | grep -qE '\$HOME|\$\{HOME\}|\$PWD|\$\{PWD\}'; then
        echo "[SECURITY] Environment variable path reference detected" >&2

        # $HOME is almost always outside the workspace, so check for file access patterns with it
        if echo "$command" | grep -qE '(cat|less|more|head|tail|vim|nano|source|\.) [^|;&]*\$HOME|\$\{HOME\}'; then
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
            echo "❌ WORKSPACE BOUNDARY VIOLATION BLOCKED" >&2
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
            echo "" >&2
            echo "Tool: Bash" >&2
            echo "Command accesses files via \$HOME environment variable" >&2
            echo "Workspace boundary: $workspace_abs" >&2
            echo "" >&2
            echo "⚠️  \$HOME typically points outside your workspace" >&2
            echo "" >&2
            echo "Use paths relative to your workspace instead of \$HOME." >&2
            echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
            log_hook_decision "BLOCK" "$tool" "\$HOME" "file access via HOME env var"
            exit 2  # Block
        fi
    fi
fi

# Allow if all checks pass
log_hook_decision "ALLOW" "$tool" "${file_path:-${search_path:-$command}}"
exit 0
