#!/usr/bin/env bash
# usage-tracker.sh - Backward compatibility shim
#
# DEPRECATED: This file now delegates to lib/backend/claude/usage-tracker.sh
# Direct sourcing of this file still works for backward compatibility.
# New code should source lib/backend/claude/usage-tracker.sh directly.
set -euo pipefail

WIGGUM_HOME="${WIGGUM_HOME:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"
source "$WIGGUM_HOME/lib/backend/claude/usage-tracker.sh"
