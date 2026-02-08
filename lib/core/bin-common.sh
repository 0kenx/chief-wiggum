#!/usr/bin/env bash
# =============================================================================
# bin-common.sh - Common boilerplate for bin/* scripts
#
# Consolidates repeated patterns from 15+ bin scripts:
#   - WIGGUM_HOME validation
#   - PROJECT_DIR and RALPH_DIR setup
#   - Core library sourcing
#
# Usage:
#   WIGGUM_HOME="${WIGGUM_HOME:-$HOME/.claude/chief-wiggum}"
#   source "$WIGGUM_HOME/lib/core/bin-common.sh"
#
# After sourcing, the following are available:
#   - WIGGUM_HOME (validated)
#   - PROJECT_DIR (current directory)
#   - RALPH_DIR (PROJECT_DIR/.ralph)
#   - Exit codes from exit-codes.sh
#   - Verbose flag parsing from verbose-flags.sh
#   - Defaults from defaults.sh
# =============================================================================
set -euo pipefail

# Security: Validate WIGGUM_HOME contains expected structure before sourcing
# This prevents sourcing malicious scripts from an attacker-controlled path
_validate_wiggum_home() {
    local home="$1"
    local required_files=(
        "lib/core/exit-codes.sh"
        "lib/core/logger.sh"
        "lib/core/verbose-flags.sh"
    )
    for f in "${required_files[@]}"; do
        if [ ! -f "$home/$f" ]; then
            echo "Error: Invalid WIGGUM_HOME - missing $f" >&2
            echo "WIGGUM_HOME='$home' does not appear to be a valid Chief Wiggum installation" >&2
            return 1
        fi
    done
}
_validate_wiggum_home "$WIGGUM_HOME" || exit 1

# Set up standard paths
PROJECT_DIR="${PROJECT_DIR:-$(pwd)}"
RALPH_DIR="${RALPH_DIR:-$PROJECT_DIR/.ralph}"
export PROJECT_DIR RALPH_DIR

# Source core libraries
source "$WIGGUM_HOME/lib/core/exit-codes.sh"
source "$WIGGUM_HOME/lib/core/verbose-flags.sh"
source "$WIGGUM_HOME/lib/core/defaults.sh"
