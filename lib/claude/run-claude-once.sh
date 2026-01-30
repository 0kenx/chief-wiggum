#!/usr/bin/env bash
# run-claude-once.sh - Backward compatibility shim
#
# DEPRECATED: This file now delegates to lib/runtime/runtime.sh
# Direct sourcing of this file still works for backward compatibility.
# New code should source lib/runtime/runtime.sh directly.
set -euo pipefail

# The runtime module provides run_agent_once and run_agent_once_with_session
source "$WIGGUM_HOME/lib/runtime/runtime.sh"
