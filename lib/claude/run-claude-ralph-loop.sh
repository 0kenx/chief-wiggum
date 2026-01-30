#!/usr/bin/env bash
# run-claude-ralph-loop.sh - Backward compatibility shim
#
# DEPRECATED: This file now delegates to lib/runtime/runtime-loop.sh
# Direct sourcing of this file still works for backward compatibility.
# New code should source lib/runtime/runtime-loop.sh directly.
set -euo pipefail

# The runtime module provides run_ralph_loop and run_ralph_loop_supervised
source "$WIGGUM_HOME/lib/runtime/runtime.sh"
source "$WIGGUM_HOME/lib/runtime/runtime-loop.sh"
