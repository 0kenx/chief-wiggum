#!/usr/bin/env bash
# Validates that tool operations stay within allowed boundaries
# Exit codes: 0 = allow, 2 = block with error
#
# Allowed paths:
#   - ralph_dir/plans       (.ralph/plans/)
#   - ralph_dir/results     (.ralph/results/)
#   - ralph_dir/docs        (.ralph/docs/ - read-only, wdoc documentation)
#   - worker_dir/workspace  (the git worktree)
#   - worker_dir/*          with restrictions below
#
# Read-only paths in worker_dir (Read/Glob/Grep allowed, Write/Edit blocked):
#   - checkpoints/  (internal state)
#   - logs/         (raw claude logs)
#   - worker.log    (internal logging)
#
# Always-blocked paths in worker_dir:
#   - agent.pid     (process management)

# Read JSON input from stdin
input=$(cat)

# Extract tool name and parameters from tool_input
tool=$(echo "$input" | jq -r '.tool // empty')
file_path=$(echo "$input" | jq -r '.tool_input.file_path // empty')
command=$(echo "$input" | jq -r '.tool_input.command // empty')
# For Glob/Grep tools, extract the 'path' parameter
search_path=$(echo "$input" | jq -r '.tool_input.path // empty')

# Get workspace directory (WORKER_WORKSPACE set by worker, CLAUDE_PROJECT_DIR set by Claude Code)
workspace="${WORKER_WORKSPACE:-${CLAUDE_PROJECT_DIR:-}}"
worker_dir="${WORKER_DIR:-}"

# Audit trail logging function
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
    echo "[HOOK DEBUG] Worker dir: $worker_dir" >&2
fi

# If no workspace is set, fail closed - block the operation
if [[ -z "$workspace" ]]; then
    echo "ERROR: WORKER_WORKSPACE not set - blocking operation (fail-closed)" >&2
    exit 2
fi

# If no file_path, no search_path, and no command, allow (e.g., some tools don't have paths)
if [[ -z "$file_path" && -z "$search_path" && -z "$command" ]]; then
    exit 0
fi

# Compute directory boundaries
workspace_abs=$(realpath "$workspace" 2>/dev/null)
worker_dir_abs=""
ralph_dir_abs=""

if [[ -n "$worker_dir" ]]; then
    worker_dir_abs=$(realpath "$worker_dir" 2>/dev/null)
    # ralph_dir is two levels up from worker_dir (.ralph/workers/worker-XXX -> .ralph)
    ralph_dir_abs=$(realpath "$worker_dir/../.." 2>/dev/null)
elif [[ -n "$workspace_abs" ]]; then
    # Infer worker_dir from workspace (workspace is worker_dir/workspace)
    worker_dir_abs=$(realpath "$workspace/.." 2>/dev/null)
    ralph_dir_abs=$(realpath "$workspace/../../.." 2>/dev/null)
fi

# Helper function to check if path is in blocked worker_dir locations
# Returns 0 if blocked, 1 if allowed
#
# Args:
#   abs_path - Absolute path to check
#   tool     - Tool name (Read/Glob/Grep are read-only, Write/Edit are write)
#
# Read-only paths (blocked for Write/Edit, allowed for Read/Glob/Grep):
#   - worker.log, logs/, checkpoints/
# Always-blocked paths:
#   - agent.pid (process management - never readable by agent)
is_blocked_worker_path() {
    local abs_path="$1"
    local check_tool="${2:-}"

    # Must have worker_dir to check
    [[ -z "$worker_dir_abs" ]] && return 1

    # agent.pid is always blocked (process management)
    if [[ "$abs_path" == "$worker_dir_abs/agent.pid" ]]; then
        return 0  # Blocked
    fi

    # Read-only paths: checkpoints/, logs/, worker.log
    # Blocked for write tools, allowed for read tools
    local is_readonly_path=false
    if [[ "$abs_path" == "$worker_dir_abs/checkpoints"* ]]; then
        is_readonly_path=true
    elif [[ "$abs_path" == "$worker_dir_abs/logs"* ]]; then
        is_readonly_path=true
    elif [[ "$abs_path" == "$worker_dir_abs/worker.log" ]]; then
        is_readonly_path=true
    fi

    if [[ "$is_readonly_path" == "true" ]]; then
        # Allow read-only tools
        case "$check_tool" in
            Read|Glob|Grep)
                return 1  # Allowed (read-only access)
                ;;
            *)
                return 0  # Blocked (write access)
                ;;
        esac
    fi

    return 1  # Not blocked
}

# Helper function to validate path against allowed boundaries
# Returns 0 if valid, 1 if invalid
validate_path() {
    local path="$1"

    # Check for path traversal patterns (log but continue validation)
    if [[ "$path" =~ \.\. ]]; then
        echo "[VALIDATION] Path contains .. traversal: $path" >&2
    fi

    # Resolve to absolute path (use -m to allow non-existent files)
    local abs_path
    abs_path=$(realpath -m "$path" 2>/dev/null || echo "$path")

    # Check if it's a symlink and resolve it
    if [[ -L "$path" ]]; then
        local link_target
        link_target=$(readlink -f "$path" 2>/dev/null || readlink "$path" 2>/dev/null)
        if [[ -n "$link_target" ]]; then
            echo "[VALIDATION] Symlink detected: $path -> $link_target" >&2
            abs_path=$(realpath -m "$link_target" 2>/dev/null || echo "$link_target")
        fi
    fi

    # Check allowed locations in order:

    # 1. workspace (worker_dir/workspace) - always allowed
    if [[ "$abs_path" == "$workspace_abs"* ]]; then
        return 0
    fi

    # 2. ralph_dir/plans - allowed
    if [[ -n "$ralph_dir_abs" && "$abs_path" == "$ralph_dir_abs/plans"* ]]; then
        return 0
    fi

    # 3. ralph_dir/results - allowed
    if [[ -n "$ralph_dir_abs" && "$abs_path" == "$ralph_dir_abs/results"* ]]; then
        return 0
    fi

    # 4. ralph_dir/memory - read-only access for agents
    if [[ -n "$ralph_dir_abs" && "$abs_path" == "$ralph_dir_abs/memory"* ]]; then
        case "$tool" in
            Read|Glob|Grep) return 0 ;;
            *) return 1 ;;
        esac
    fi

    # 5. ralph_dir/docs - read-only access for agents (wdoc documentation)
    if [[ -n "$ralph_dir_abs" && "$abs_path" == "$ralph_dir_abs/docs"* ]]; then
        case "$tool" in
            Read|Glob|Grep) return 0 ;;
            *) return 1 ;;
        esac
    fi

    # 6. worker_dir/* (except blocked paths) - allowed
    if [[ -n "$worker_dir_abs" && "$abs_path" == "$worker_dir_abs"* ]]; then
        # Check if it's a blocked path (pass tool for read/write distinction)
        if is_blocked_worker_path "$abs_path" "$tool"; then
            return 1  # Blocked worker path
        fi
        return 0  # Allowed worker path
    fi

    # Path is outside all allowed boundaries
    return 1
}

# Generate error message for blocked paths
emit_block_error() {
    local tool="$1"
    local path="$2"
    local abs_path="$3"
    local reason="${4:-}"

    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
    echo "❌ PATH ACCESS BLOCKED" >&2
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
    echo "" >&2
    echo "Tool: $tool" >&2
    echo "Path: $abs_path" >&2
    echo "" >&2

    # Check if it's a blocked worker path
    if is_blocked_worker_path "$abs_path" "$tool"; then
        echo "This path is restricted within the worker directory:" >&2
        echo "  - agent.pid     (process management - always blocked)" >&2
        echo "  - checkpoints/  (read-only)" >&2
        echo "  - logs/         (read-only)" >&2
        echo "  - worker.log    (read-only)" >&2
    else
        echo "Allowed paths:" >&2
        echo "  - workspace/           (your working directory)" >&2
        echo "  - worker files         (../reports/, ../prd.md, etc.)" >&2
        echo "  - .ralph/plans/        (implementation plans)" >&2
        echo "  - .ralph/results/      (task results)" >&2
        echo "  - .ralph/docs/         (wdoc documentation, read-only)" >&2
    fi

    if [[ "$path" =~ \.\. ]]; then
        echo "" >&2
        echo "Tip: Use relative paths from workspace (e.g., ./file.txt)" >&2
    fi

    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
}

# Validate file_path if present (Edit, Write, Read tools)
if [[ -n "$file_path" ]]; then
    # Check for symlink before resolution
    if [[ -L "$file_path" ]]; then
        link_target=$(readlink -f "$file_path" 2>/dev/null || readlink "$file_path" 2>/dev/null)
        echo "[SECURITY] Symlink resolution: $file_path -> $link_target" >&2
    fi

    if ! validate_path "$file_path"; then
        abs_path=$(realpath -m "$file_path" 2>/dev/null || echo "$file_path")
        emit_block_error "$tool" "$file_path" "$abs_path"
        log_hook_decision "BLOCK" "$tool" "$file_path" "path outside allowed boundaries"
        exit 2
    fi
fi

# Validate search_path if present (Glob, Grep tools)
if [[ -n "$search_path" ]]; then
    if ! validate_path "$search_path"; then
        abs_path=$(realpath -m "$search_path" 2>/dev/null || echo "$search_path")
        emit_block_error "$tool" "$search_path" "$abs_path"
        log_hook_decision "BLOCK" "$tool" "$search_path" "search path outside allowed boundaries"
        exit 2
    fi
fi

# Validate Bash commands for dangerous path operations
if [[ "$tool" == "Bash" && -n "$command" ]]; then

    # Block ALL git commands - git operations are handled by worker scripts
    if echo "$command" | grep -qE '(^|[;&|])[[:space:]]*(git[[:space:]]|git$)'; then
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        echo "❌ GIT COMMAND BLOCKED" >&2
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        echo "" >&2
        echo "Command: $command" >&2
        echo "" >&2
        echo "Git commands are not allowed in worker sessions." >&2
        echo "Git commits and PRs are handled automatically by the orchestration system." >&2
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        log_hook_decision "BLOCK" "$tool" "git" "git commands not allowed"
        exit 2
    fi

    # Block commands that may leak secret tokens
    if echo "$command" | grep -qE 'ANTHROPIC_AUTH_TOKEN|GITHUB_PAT_TOKEN|WIGGUM_SECRET_'; then
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        echo "❌ SECRET LEAK BLOCKED" >&2
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        echo "" >&2
        echo "Command references secret environment variables." >&2
        echo "Commands must not access or expose authentication tokens." >&2
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        log_hook_decision "BLOCK" "$tool" "secret-ref" "command references secret token"
        exit 2
    fi

    # Check for cd commands that try to escape allowed boundaries
    if echo "$command" | grep -qE 'cd[[:space:]]+'; then
        cd_target=$(echo "$command" | grep -oE 'cd[[:space:]]+("[^"]+"|'\''[^'\'']+'\''|[^;|&[:space:]]+)' | sed -E 's/cd[[:space:]]+//; s/^["'\'']//; s/["'\'']$//' | head -1)

        if [[ -n "$cd_target" ]]; then
            # Resolve cd target
            if [[ "$cd_target" == /* ]]; then
                abs_cd=$(realpath -m "$cd_target" 2>/dev/null || echo "$cd_target")
            else
                abs_cd=$(realpath -m "$workspace/$cd_target" 2>/dev/null || echo "$workspace/$cd_target")
            fi

            # Only allow cd within workspace (not broader worker_dir for cd)
            if [[ "$abs_cd" != "$workspace_abs"* ]]; then
                echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                echo "❌ CD OUTSIDE WORKSPACE BLOCKED" >&2
                echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                echo "" >&2
                echo "Attempted: cd $cd_target" >&2
                echo "Resolved: $abs_cd" >&2
                echo "" >&2
                echo "You must stay within your workspace directory." >&2
                echo "Use file paths (e.g., cat ../reports/file.md) instead of cd." >&2
                echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
                log_hook_decision "BLOCK" "$tool" "$cd_target" "cd outside workspace"
                exit 2
            fi
        fi
    fi

    # Check for file operations with absolute paths
    if echo "$command" | grep -qoE '[[:space:]]\/[^[:space:]]+'; then
        for abs_cmd_path in $(echo "$command" | grep -oE '[[:space:]]\/[^[:space:]]+' | sed 's/^[[:space:]]*//'); do
            # Skip common system paths that are safe
            if [[ "$abs_cmd_path" =~ ^/(bin|usr|lib|etc|dev|proc|sys|tmp)/ ]]; then
                continue
            fi
            # Skip flags
            if [[ "$abs_cmd_path" =~ ^/- ]]; then
                continue
            fi

            if ! validate_path "$abs_cmd_path"; then
                resolved=$(realpath -m "$abs_cmd_path" 2>/dev/null || echo "$abs_cmd_path")
                emit_block_error "Bash" "$abs_cmd_path" "$resolved"
                log_hook_decision "BLOCK" "$tool" "$abs_cmd_path" "absolute path outside boundaries"
                exit 2
            fi
        done
    fi

    # Check for relative paths with .. that might escape
    # Extract paths containing ../ and validate them
    for rel_path in $(echo "$command" | grep -oE '[^[:space:]]*\.\./[^[:space:]]*' || true); do
        if [[ -n "$rel_path" ]]; then
            # Resolve relative to workspace
            resolved=$(realpath -m "$workspace/$rel_path" 2>/dev/null || echo "$workspace/$rel_path")

            if ! validate_path "$resolved"; then
                emit_block_error "Bash" "$rel_path" "$resolved"
                log_hook_decision "BLOCK" "$tool" "$rel_path" "relative path escapes boundaries"
                exit 2
            fi
        fi
    done

    # Check for $HOME usage in file access
    # shellcheck disable=SC2016  # We want to match literal $HOME in the command
    if echo "$command" | grep -qE '(cat|less|more|head|tail|vim|nano|source|\.) [^|;&]*\$HOME|\$\{HOME\}'; then
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        echo "❌ HOME DIRECTORY ACCESS BLOCKED" >&2
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        echo "" >&2
        echo "Command accesses files via \$HOME" >&2
        echo "Use paths relative to your workspace instead." >&2
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
        log_hook_decision "BLOCK" "$tool" "\$HOME" "home directory access"
        exit 2
    fi
fi

# Allow if all checks pass
log_hook_decision "ALLOW" "$tool" "${file_path:-${search_path:-$command}}"
exit 0
