#!/usr/bin/env bash
# retry-strategy.sh - Backward compatibility shim
#
# DEPRECATED: This file now delegates to lib/runtime/runtime-retry.sh
# Direct sourcing of this file still works for backward compatibility.
# New code should source lib/runtime/runtime.sh directly.
set -euo pipefail

[ -n "${_RETRY_STRATEGY_LOADED:-}" ] && return 0
_RETRY_STRATEGY_LOADED=1

# Source runtime (loads backend + retry module)
source "$WIGGUM_HOME/lib/runtime/runtime.sh"
