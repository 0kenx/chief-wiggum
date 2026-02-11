#!/usr/bin/env bash
# preflight.sh - Pre-flight environment checks for Chief Wiggum
#
# Provides validation functions to ensure the environment is properly
# configured before running wiggum commands.
set -euo pipefail

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/exit-codes.sh"
source "$WIGGUM_HOME/lib/core/config-validator.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"

# Terminal colors (if supported)
if [ -t 1 ]; then
    RED='\033[0;31m'
    GREEN='\033[0;32m'
    YELLOW='\033[0;33m'
    BLUE='\033[0;34m'
    NC='\033[0m' # No Color
else
    RED=''
    GREEN=''
    YELLOW=''
    BLUE=''
    NC=''
fi

# Check result tracking
declare -i CHECK_PASSED=0
declare -i CHECK_FAILED=0
declare -i CHECK_WARNED=0

# Print a check result
_print_check() {
    local status="$1"
    local name="$2"
    local message="$3"

    case "$status" in
        pass)
            echo -e "${GREEN}[PASS]${NC} $name"
            [ -n "$message" ] && echo "       $message"
            ((++CHECK_PASSED))
            ;;
        fail)
            echo -e "${RED}[FAIL]${NC} $name"
            [ -n "$message" ] && echo "       $message"
            ((++CHECK_FAILED))
            ;;
        warn)
            echo -e "${YELLOW}[WARN]${NC} $name"
            [ -n "$message" ] && echo "       $message"
            ((++CHECK_WARNED))
            ;;
        info)
            echo -e "${BLUE}[INFO]${NC} $name"
            [ -n "$message" ] && echo "       $message"
            ;;
    esac
}

# Check if a command exists
# Args: <command>
# Returns: 0 if exists, 1 otherwise
check_command_exists() {
    command -v "$1" &> /dev/null
}

# Check gh CLI is installed and authenticated
check_gh_cli() {
    local name="GitHub CLI (gh)"

    if ! check_command_exists gh; then
        _print_check "fail" "$name" "Not installed. Install from: https://cli.github.com/"
        return 1
    fi

    # Check version
    local version
    version=$(gh --version 2>/dev/null | head -1 | awk '{print $3}')

    # Check authentication
    if ! timeout "${WIGGUM_GH_TIMEOUT:-30}" gh auth status &>/dev/null; then
        _print_check "fail" "$name" "Not authenticated. Run: gh auth login"
        return 1
    fi

    local auth_user
    auth_user=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh api user --jq '.login' 2>/dev/null || echo "unknown")

    _print_check "pass" "$name" "v$version (authenticated as: $auth_user)"
    return 0
}

# Check Claude CLI is available and responsive
check_claude_cli() {
    local name="Claude CLI"
    local claude="${CLAUDE:-claude}"

    if ! check_command_exists "$claude"; then
        _print_check "fail" "$name" "Not found. Install Claude Code CLI."
        return 1
    fi

    # Get version
    local version
    version=$($claude --version 2>/dev/null | head -1 || echo "unknown")

    # Quick responsiveness check (just verify it doesn't hang)
    if ! timeout 5 "$claude" --version &>/dev/null; then
        _print_check "fail" "$name" "CLI not responding (timeout after 5s)"
        return 1
    fi

    _print_check "pass" "$name" "$version"
    return 0
}

# Check jq is installed
check_jq() {
    local name="jq (JSON processor)"

    if ! check_command_exists jq; then
        _print_check "fail" "$name" "Not installed. Install with your package manager."
        return 1
    fi

    local version
    version=$(jq --version 2>/dev/null || echo "unknown")

    _print_check "pass" "$name" "$version"
    return 0
}

# Check git version (2.5+ for worktrees)
check_git() {
    local name="Git"
    local min_major=2
    local min_minor=5

    if ! check_command_exists git; then
        _print_check "fail" "$name" "Not installed."
        return 1
    fi

    local version
    version=$(git --version | awk '{print $3}')
    local major minor
    major=$(echo "$version" | cut -d. -f1)
    minor=$(echo "$version" | cut -d. -f2)

    if [ "$major" -lt "$min_major" ] || { [ "$major" -eq "$min_major" ] && [ "$minor" -lt "$min_minor" ]; }; then
        _print_check "fail" "$name" "v$version (requires $min_major.$min_minor+ for worktrees)"
        return 1
    fi

    _print_check "pass" "$name" "v$version"
    return 0
}

# Check disk space (minimum 500MB)
check_disk_space() {
    local name="Disk space"
    local min_mb=500
    local path="${1:-.}"

    # Get available space in KB and convert to MB
    local available_kb available_mb
    available_kb=$(df -P "$path" | tail -1 | awk '{print $4}')
    available_mb=$((available_kb / 1024))

    if [ "$available_mb" -lt "$min_mb" ]; then
        _print_check "fail" "$name" "${available_mb}MB available (minimum: ${min_mb}MB)"
        return 1
    fi

    local available_display
    if [ "$available_mb" -gt 1024 ]; then
        available_display="$((available_mb / 1024))GB"
    else
        available_display="${available_mb}MB"
    fi

    _print_check "pass" "$name" "$available_display available"
    return 0
}

# Check if project setup (.ralph directory) exists
check_project_setup() {
    local name="Project setup"
    local ralph_dir="${RALPH_DIR:-.ralph}"

    if [ ! -d "$ralph_dir" ]; then
        _print_check "info" "$name" "Not initialized (run: wiggum init)"
        return 0  # Not a failure, just info
    fi

    # Check for kanban.md
    if [ ! -f "$ralph_dir/kanban.md" ]; then
        _print_check "warn" "$name" ".ralph exists but kanban.md is missing"
        return 0
    fi

    # Count tasks
    local task_count
    task_count=$(grep -c -- '- \[.\] \*\*\[' "$ralph_dir/kanban.md" 2>/dev/null) || task_count=0

    _print_check "pass" "$name" ".ralph initialized ($task_count tasks in kanban)"
    return 0
}

# Check WIGGUM_HOME is valid
check_wiggum_home() {
    local name="WIGGUM_HOME"

    if [ -z "${WIGGUM_HOME:-}" ]; then
        _print_check "fail" "$name" "Not set"
        return 1
    fi

    if [ ! -d "$WIGGUM_HOME" ]; then
        _print_check "fail" "$name" "Directory does not exist: $WIGGUM_HOME"
        return 1
    fi

    # Check for required subdirectories
    local required_dirs=("bin" "lib" "config")
    local missing=()

    for dir in "${required_dirs[@]}"; do
        if [ ! -d "$WIGGUM_HOME/$dir" ]; then
            missing+=("$dir")
        fi
    done

    if [ ${#missing[@]} -gt 0 ]; then
        _print_check "fail" "$name" "Missing directories: ${missing[*]}"
        return 1
    fi

    _print_check "pass" "$name" "$WIGGUM_HOME"
    return 0
}

# Check configuration files
check_config_files() {
    local name="Configuration"

    if [ ! -f "$WIGGUM_HOME/config/config.json" ]; then
        _print_check "warn" "$name" "config.json not found (using defaults)"
        return 0
    fi

    if [ ! -f "$WIGGUM_HOME/config/agents.json" ]; then
        _print_check "warn" "$name" "agents.json not found (using defaults)"
        return 0
    fi

    # Validate config.json structure and values
    if ! validate_config "$WIGGUM_HOME/config/config.json" 2>/dev/null; then
        _print_check "fail" "$name" "config.json validation failed"
        return 1
    fi

    # Validate agents.json structure and values
    if ! validate_agents_config "$WIGGUM_HOME/config/agents.json" 2>/dev/null; then
        _print_check "fail" "$name" "agents.json validation failed"
        return 1
    fi

    _print_check "pass" "$name" "config.json and agents.json valid"
    return 0
}

# Check timeout command exists
check_timeout() {
    local name="timeout command"

    if ! check_command_exists timeout; then
        _print_check "fail" "$name" "Not found (required for API timeouts)"
        return 1
    fi

    _print_check "pass" "$name" "Available"
    return 0
}

# Check curl is installed
check_curl() {
    local name="curl"

    if ! check_command_exists curl; then
        _print_check "fail" "$name" "Not installed. Install with your package manager."
        return 1
    fi

    _print_check "pass" "$name" "Available"
    return 0
}

# Check uuidgen is installed (used for session IDs)
check_uuidgen() {
    local name="uuidgen"

    if ! check_command_exists uuidgen; then
        _print_check "fail" "$name" "Not installed. Install: apt install uuid-runtime / pacman -S util-linux"
        return 1
    fi

    _print_check "pass" "$name" "Available"
    return 0
}

# Check setsid is installed (used for worker process isolation)
check_setsid() {
    local name="setsid"

    if ! check_command_exists setsid; then
        _print_check "fail" "$name" "Not installed. Install: apt install util-linux / brew install util-linux (macOS)"
        return 1
    fi

    _print_check "pass" "$name" "Available"
    return 0
}

# Check bc is installed (used for floating-point arithmetic in metrics/cost)
check_bc() {
    local name="bc (calculator)"

    if ! check_command_exists bc; then
        _print_check "fail" "$name" "Not installed. Required for metrics/cost calculations. Install: apt install bc / nix-env -iA nixpkgs.bc"
        return 1
    fi

    _print_check "pass" "$name" "Available"
    return 0
}

# Check flock is installed (used for concurrent file access)
check_flock() {
    local name="flock (file locking)"

    if ! check_command_exists flock; then
        _print_check "fail" "$name" "Not installed. Required for concurrent access. Install: apt install util-linux"
        return 1
    fi

    _print_check "pass" "$name" "Available"
    return 0
}

# Check Bash version is 4.0+ (required for associative arrays)
check_bash_version() {
    local name="Bash version"
    local min_major=4

    local major="${BASH_VERSINFO[0]}"
    local minor="${BASH_VERSINFO[1]}"
    local version="$major.$minor"

    if [ "$major" -lt "$min_major" ]; then
        _print_check "fail" "$name" "v$version (requires $min_major.0+ for associative arrays)"
        return 1
    fi

    _print_check "pass" "$name" "v$version"
    return 0
}

# Check sha256sum or shasum is available (used for content hashing)
check_sha256() {
    local name="sha256sum/shasum"

    if check_command_exists sha256sum; then
        _print_check "pass" "$name" "sha256sum available"
        return 0
    fi

    if check_command_exists shasum; then
        _print_check "pass" "$name" "shasum available (fallback)"
        return 0
    fi

    _print_check "warn" "$name" "Neither sha256sum nor shasum found (content hashing degraded)"
    return 0
}

# Check nproc is available (used for parallel job count)
check_nproc() {
    local name="nproc"

    if check_command_exists nproc; then
        local cpus
        cpus=$(nproc 2>/dev/null || echo "?")
        _print_check "pass" "$name" "Available ($cpus CPUs)"
        return 0
    fi

    # macOS fallback
    if check_command_exists sysctl; then
        _print_check "pass" "$name" "Not found, but sysctl available (macOS)"
        return 0
    fi

    _print_check "warn" "$name" "Not found. Usage tracker may default to 1 parallel job."
    return 0
}

# Check uv (Python package manager, needed for TUI)
check_uv() {
    local name="uv (Python package manager)"

    if ! check_command_exists uv; then
        _print_check "warn" "$name" "Not installed. Install: curl -LsSf https://astral.sh/uv/install.sh | sh"
        return 0  # Warning only - TUI is optional
    fi

    local version
    version=$(uv --version 2>/dev/null | head -1 || echo "unknown")

    _print_check "pass" "$name" "$version"
    return 0
}

# Check POSIX utilities required by the scripts
check_posix_utilities() {
    local name="POSIX utilities"
    local posix_bins=(grep cat date sed rm head find awk basename sort mkdir kill cut ls tail sleep mv xargs tr wc tee ps dirname tac stat)
    local missing=()

    for bin in "${posix_bins[@]}"; do
        if ! check_command_exists "$bin"; then
            missing+=("$bin")
        fi
    done

    if [ ${#missing[@]} -gt 0 ]; then
        _print_check "fail" "$name" "Missing: ${missing[*]}"
        return 1
    fi

    _print_check "pass" "$name" "All ${#posix_bins[@]} utilities found"
    return 0
}

# Check WIGGUM_HOME/bin is in PATH
check_path() {
    local name="PATH"

    if [ -z "${WIGGUM_HOME:-}" ]; then
        _print_check "fail" "$name" "WIGGUM_HOME not set, cannot verify PATH"
        return 1
    fi

    if [[ ":$PATH:" == *":$WIGGUM_HOME/bin:"* ]]; then
        _print_check "pass" "$name" "$WIGGUM_HOME/bin is in PATH"
        return 0
    fi

    _print_check "fail" "$name" "$WIGGUM_HOME/bin not in PATH. Add to your shell rc file."
    return 1
}

# Check hooks directory and executability
check_hooks() {
    local name="Hooks"
    local hooks_dir="$WIGGUM_HOME/hooks/callbacks"

    if [ ! -d "$hooks_dir" ]; then
        _print_check "warn" "$name" "hooks/callbacks directory not found"
        return 0
    fi

    local non_exec=()
    for hook in "$hooks_dir"/*.sh; do
        [ -f "$hook" ] || continue
        if [ ! -x "$hook" ]; then
            non_exec+=("$(basename "$hook")")
        fi
    done

    if [ ${#non_exec[@]} -gt 0 ]; then
        _print_check "warn" "$name" "Not executable: ${non_exec[*]}"
        return 0
    fi

    local count
    # Use -perm /111 for portability (macOS and modern Linux)
    # -perm +111 is deprecated and may not work on all systems
    count=$(find "$hooks_dir" -maxdepth 1 -name "*.sh" -perm /111 2>/dev/null | wc -l | tr -d '[:space:]')
    _print_check "pass" "$name" "$count hook scripts executable"
    return 0
}

# Check TUI Python environment
check_tui() {
    local name="TUI environment"
    local tui_dir="$WIGGUM_HOME/tui"

    if [ ! -d "$tui_dir" ]; then
        _print_check "info" "$name" "TUI directory not found (optional)"
        return 0
    fi

    if [ ! -f "$tui_dir/pyproject.toml" ]; then
        _print_check "warn" "$name" "pyproject.toml missing"
        return 0
    fi

    if [ ! -d "$tui_dir/.venv" ]; then
        _print_check "warn" "$name" "Virtual environment not set up (run: cd $tui_dir && uv sync)"
        return 0
    fi

    _print_check "pass" "$name" "Virtual environment present"
    return 0
}

# =============================================================================
# Git & GitHub Checks
# =============================================================================

# Check and display the resolved default branch
check_default_branch() {
    local name="Default branch"
    local branch
    branch=$(get_default_branch)
    _print_check "pass" "$name" "$branch"
}

# Check git remote is configured and reachable
check_git_remote() {
    local name="Git remote"

    local git_remote
    git_remote=$(git remote get-url origin 2>/dev/null) || true

    if [ -z "$git_remote" ]; then
        _print_check "warn" "$name" "No 'origin' remote configured"
        return 0
    fi

    # Extract host for SSH test
    local git_host=""
    if [[ "$git_remote" =~ ^git@([^:]+): ]]; then
        git_host="${BASH_REMATCH[1]}"
    elif [[ "$git_remote" =~ ^ssh://git@([^/]+)/ ]]; then
        git_host="${BASH_REMATCH[1]}"
    fi

    if [ -n "$git_host" ]; then
        local ssh_output
        ssh_output=$(timeout 10 ssh -o BatchMode=yes -o ConnectTimeout=5 -T "git@$git_host" 2>&1) || true
        if echo "$ssh_output" | grep -qi "successfully authenticated"; then
            _print_check "pass" "$name" "$git_remote (SSH authenticated)"
        else
            _print_check "fail" "$name" "SSH auth failed to $git_host. Check SSH keys / ssh-agent."
            return 1
        fi
    else
        # HTTPS remote — just report it
        _print_check "pass" "$name" "$git_remote"
    fi

    return 0
}

# Check git worktree support works
check_git_worktree() {
    local name="Git worktree"

    if ! git rev-parse --git-dir &>/dev/null; then
        _print_check "info" "$name" "Not in a git repository (skipped)"
        return 0
    fi

    local worktree_output
    worktree_output=$(git worktree list 2>&1) || true

    if [ -z "$worktree_output" ]; then
        _print_check "fail" "$name" "git worktree list returned empty (worktrees may be unsupported)"
        return 1
    fi

    local wt_count
    wt_count=$(echo "$worktree_output" | wc -l | tr -d '[:space:]')
    _print_check "pass" "$name" "$wt_count worktree(s) active"
    return 0
}

# Check gh token has required scopes
check_gh_token_scopes() {
    local name="GitHub token scopes"

    if ! check_command_exists gh; then
        _print_check "info" "$name" "gh not installed (skipped)"
        return 0
    fi

    if ! timeout "${WIGGUM_GH_TIMEOUT:-30}" gh auth status &>/dev/null; then
        _print_check "info" "$name" "gh not authenticated (skipped)"
        return 0
    fi

    # Get token scopes via API header inspection
    local scopes
    scopes=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh api -i user 2>/dev/null | grep -i 'x-oauth-scopes:' | sed 's/x-oauth-scopes: *//i' | tr -d '\r') || true

    if [ -z "$scopes" ]; then
        # Fine-grained tokens don't expose scopes header — check permissions directly
        local can_read_issues
        can_read_issues=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh api repos/:owner/:repo/issues --jq 'length' 2>/dev/null) || true
        if [ -n "$can_read_issues" ]; then
            _print_check "pass" "$name" "Fine-grained token (repo access verified)"
        else
            _print_check "warn" "$name" "Could not verify token permissions"
        fi
        return 0
    fi

    local missing=()
    # Check for 'repo' scope (covers issues, PRs, labels, commits)
    if ! echo "$scopes" | grep -q '\brepo\b'; then
        missing+=("repo")
    fi

    if [ ${#missing[@]} -gt 0 ]; then
        _print_check "fail" "$name" "Missing scopes: ${missing[*]} (re-run: gh auth login --scopes repo)"
        return 1
    fi

    _print_check "pass" "$name" "$scopes"
    return 0
}

# Check required GitHub labels exist in the repo
check_github_labels() {
    local name="GitHub labels"

    if ! check_command_exists gh; then
        _print_check "info" "$name" "gh not installed (skipped)"
        return 0
    fi

    if ! timeout "${WIGGUM_GH_TIMEOUT:-30}" gh auth status &>/dev/null; then
        _print_check "info" "$name" "gh not authenticated (skipped)"
        return 0
    fi

    # Check if we're in a GitHub repo
    local repo_info
    repo_info=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh repo view --json nameWithOwner -q '.nameWithOwner' 2>/dev/null) || true
    if [ -z "$repo_info" ]; then
        _print_check "info" "$name" "Not a GitHub repository (skipped)"
        return 0
    fi

    # Fetch all repo labels
    local repo_labels
    repo_labels=$(timeout "${WIGGUM_GH_TIMEOUT:-30}" gh label list --json name -q '.[].name' --limit 200 2>/dev/null) || true

    if [ -z "$repo_labels" ]; then
        _print_check "warn" "$name" "Could not fetch labels from $repo_info"
        return 0
    fi

    # Required labels for Wiggum operation
    local required_labels=(
        "wiggum"
        "wiggum:in-progress"
        "wiggum:completed"
        "wiggum:failed"
        "wiggum:resume-request"
        "priority:critical"
        "priority:high"
        "priority:medium"
        "priority:low"
    )

    local missing=()
    for label in "${required_labels[@]}"; do
        if ! echo "$repo_labels" | grep -qx "$label"; then
            missing+=("$label")
        fi
    done

    if [ ${#missing[@]} -gt 0 ]; then
        _print_check "fail" "$name" "Missing ${#missing[@]} label(s): ${missing[*]}"
        echo "       Run: wiggum github init"
        return 1
    fi

    _print_check "pass" "$name" "All ${#required_labels[@]} required labels present"
    return 0
}

# =============================================================================
# Pipeline & Agent Validation
# =============================================================================

# Check default pipeline is valid and references existing agents
check_pipeline_config() {
    local name="Pipeline config"
    local pipeline_file="$WIGGUM_HOME/config/pipelines/default.json"
    local agents_file="$WIGGUM_HOME/config/agents.json"

    if [ ! -f "$pipeline_file" ]; then
        _print_check "fail" "$name" "default.json not found at $pipeline_file"
        return 1
    fi

    # Validate JSON syntax
    if ! jq empty "$pipeline_file" 2>/dev/null; then
        _print_check "fail" "$name" "Invalid JSON in default.json"
        return 1
    fi

    # Check pipeline has steps
    local step_count
    step_count=$(jq '.steps | length' "$pipeline_file" 2>/dev/null)
    step_count="${step_count:-0}"
    if [ "$step_count" -eq 0 ]; then
        _print_check "fail" "$name" "Pipeline has no steps"
        return 1
    fi

    # Cross-reference agents in pipeline against agents.json
    if [ -f "$agents_file" ]; then
        local pipeline_agents
        pipeline_agents=$(jq -r '.steps[].agent // empty' "$pipeline_file" 2>/dev/null | sort -u)
        local known_agents
        known_agents=$(jq -r '.agents | keys[]' "$agents_file" 2>/dev/null)

        local unknown=()
        while IFS= read -r agent; do
            [ -z "$agent" ] && continue
            if ! echo "$known_agents" | grep -qx "$agent"; then
                unknown+=("$agent")
            fi
        done <<< "$pipeline_agents"

        if [ ${#unknown[@]} -gt 0 ]; then
            _print_check "warn" "$name" "Pipeline references unknown agents: ${unknown[*]}"
            return 0
        fi
    fi

    _print_check "pass" "$name" "$step_count steps in default pipeline"
    return 0
}

# Run all pre-flight checks
# Returns: 0 if all pass, 1 if any fail
run_preflight_checks() {
    echo "Running pre-flight checks..."
    echo ""

    echo "=== Shell & Required Tools ==="
    check_bash_version
    check_wiggum_home
    check_git
    check_jq
    check_bc
    check_curl
    check_uuidgen
    check_setsid
    check_flock
    check_timeout
    check_sha256
    check_nproc
    check_gh_cli
    check_claude_cli
    echo ""

    echo "=== POSIX Utilities ==="
    check_posix_utilities
    echo ""

    echo "=== Environment ==="
    check_path
    check_disk_space "."
    check_config_files
    check_pipeline_config
    check_uv
    check_tui
    check_hooks
    echo ""

    echo "=== Git & GitHub ==="
    check_default_branch
    check_git_remote
    check_git_worktree
    check_gh_token_scopes
    check_github_labels
    echo ""

    echo "=== Project ==="
    check_project_setup
    echo ""

    echo "=== Summary ==="
    echo -e "  ${GREEN}Passed:${NC} $CHECK_PASSED"
    echo -e "  ${YELLOW}Warnings:${NC} $CHECK_WARNED"
    echo -e "  ${RED}Failed:${NC} $CHECK_FAILED"
    echo ""

    if [ $CHECK_FAILED -gt 0 ]; then
        echo -e "${RED}Pre-flight checks failed. Please fix the issues above.${NC}"
        return 1
    fi

    if [ $CHECK_WARNED -gt 0 ]; then
        echo -e "${YELLOW}Pre-flight checks passed with warnings.${NC}"
    else
        echo -e "${GREEN}All pre-flight checks passed.${NC}"
    fi

    return 0
}
