#!/usr/bin/env bash
# preflight.sh - Pre-flight environment checks for Chief Wiggum
#
# Provides validation functions to ensure the environment is properly
# configured before running wiggum commands.
set -euo pipefail

source "$WIGGUM_HOME/lib/core/logger.sh"
source "$WIGGUM_HOME/lib/core/exit-codes.sh"

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
declare -a CHECK_RESULTS=()
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
    if ! timeout 5 $claude --version &>/dev/null; then
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
    task_count=$(grep -c -- '- \[.\] \*\*\[' "$ralph_dir/kanban.md" 2>/dev/null || echo "0")

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

    # Validate JSON syntax
    if ! jq empty "$WIGGUM_HOME/config/config.json" 2>/dev/null; then
        _print_check "fail" "$name" "config.json has invalid JSON"
        return 1
    fi

    if ! jq empty "$WIGGUM_HOME/config/agents.json" 2>/dev/null; then
        _print_check "fail" "$name" "agents.json has invalid JSON"
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

# Run all pre-flight checks
# Returns: 0 if all pass, 1 if any fail
run_preflight_checks() {
    echo "Running pre-flight checks..."
    echo ""

    echo "=== Required Tools ==="
    check_wiggum_home
    check_git
    check_jq
    check_timeout
    check_gh_cli
    check_claude_cli
    echo ""

    echo "=== Environment ==="
    check_disk_space "."
    check_config_files
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
