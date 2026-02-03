#!/usr/bin/env bash
# mock-git.sh - Mock Git CLI for testing
#
# Intercepts git commands to allow:
# - Logging of invocations
# - Injection of failures (exit codes, error messages)
# - Simulation of specific scenarios (e.g., merge conflicts)
# - Passthrough to real git for "working" commands
#
# Environment Variables:
#   MOCK_GIT_LOG_DIR       - Directory to store logs (required)
#   MOCK_GIT_EXIT_CODE     - Force exit code (overrides real git)
#   MOCK_GIT_OUTPUT        - Force stdout (overrides real git)
#   MOCK_GIT_SCENARIO      - Activate a specific scenario logic
#   MOCK_GIT_VERBOSE       - Enable debug logging to stderr
#   MOCK_GIT_PASSTHROUGH   - If "false", do NOT call real git (default: "true")

set -euo pipefail

# =============================================================================
# Logging Setup
# =============================================================================

if [ -z "${MOCK_GIT_LOG_DIR:-}" ]; then
    echo "Error: MOCK_GIT_LOG_DIR is not set" >&2
    exit 1
fi

mkdir -p "$MOCK_GIT_LOG_DIR"
mkdir -p "$MOCK_GIT_LOG_DIR/args"

# Generate invocation ID
INVOCATION_ID=1
if [ -f "$MOCK_GIT_LOG_DIR/mock-git-invocations" ]; then
    INVOCATION_ID=$(($(cat "$MOCK_GIT_LOG_DIR/mock-git-invocations") + 1))
fi
echo "$INVOCATION_ID" > "$MOCK_GIT_LOG_DIR/mock-git-invocations"

LOG_FILE="$MOCK_GIT_LOG_DIR/mock-git-invocation-$INVOCATION_ID.log"
ARGS_FILE="$MOCK_GIT_LOG_DIR/args/invocation-$INVOCATION_ID.args"

# Log arguments
echo "$@" > "$ARGS_FILE"
printf "args: %s\n" "$*" >> "$LOG_FILE"
printf "cwd: %s\n" "$(pwd)" >> "$LOG_FILE"

# Debug helper
debug_log() {
    if [ "${MOCK_GIT_VERBOSE:-}" = "true" ]; then
        echo "[mock-git] $*" >&2
    fi
}

debug_log "Invoked with: $*"

# =============================================================================
# Scenario Logic
# =============================================================================

# Default state
EXIT_CODE="${MOCK_GIT_EXIT_CODE:-}"
OUTPUT="${MOCK_GIT_OUTPUT:-}"
PASSTHROUGH="${MOCK_GIT_PASSTHROUGH:-true}"

SCENARIO="${MOCK_GIT_SCENARIO:-}"

if [ "$SCENARIO" = "merge-conflict" ]; then
    # If the command is 'merge', simulate a conflict
    if [[ "$1" == "merge" ]]; then
        debug_log "Simulating merge conflict"
        PASSTHROUGH="false"
        EXIT_CODE=1
        
        # Create a fake conflict in a file if specified, or just generic
        # To be really useful, tests should setup the files such that we can just
        # overwrite them with markers.
        # But for now, we'll just fail standard out
        echo "Auto-merging file.txt"
        echo "CONFLICT (content): Merge conflict in file.txt"
        echo "Automatic merge failed; fix conflicts and then commit the result."
        
        # Optional: Actually write conflict markers to a file if requested via env
        if [ -n "${MOCK_GIT_CONFLICT_FILE:-}" ] && [ -f "${MOCK_GIT_CONFLICT_FILE}" ]; then
             cat <<EOF > "${MOCK_GIT_CONFLICT_FILE}"
<<<<<<< HEAD
Current content
=======
Incoming content
>>>>>>> MERGE_HEAD
EOF
        fi
    fi
elif [ "$SCENARIO" = "network-error" ]; then
    if [[ "$1" == "fetch" ]] || [[ "$1" == "pull" ]] || [[ "$1" == "push" ]] || [[ "$1" == "clone" ]]; then
       debug_log "Simulating network error"
       PASSTHROUGH="false"
       EXIT_CODE=128
       echo "fatal: unable to access 'https://github.com/fake/repo.git/': Verified cert fail" >&2
    fi
fi

# =============================================================================
# Execution
# =============================================================================

# If output is forced, print it
if [ -n "$OUTPUT" ]; then
    echo -e "$OUTPUT"
fi

# If passthrough is enabled (and no forced exit code that implies skipping), runs real git
if [ "$PASSTHROUGH" = "true" ]; then
    # We use 'command git' to bypass any shell functions/aliases named git
    # But we need to be careful not to call THIS script recursively if it's in PATH as 'git'
    # The test setup should likely alias `git` to this script, or put this script in PATH_PREPEND.
    # To run REAL git, we might need an absolute path or assume 'git' is in system path.
    # We'll assume /usr/bin/git or similar involves a lookup that skips the current dir if set up right.
    # HOWEVER, safe bet is asking `which -a git` and picking the one that isn't us.
    # Or just assume the user set REAL_GIT_PATH env var.
    
    REAL_GIT="${REAL_GIT_PATH:-/usr/bin/git}"
    
    if [ ! -x "$REAL_GIT" ]; then
         # Fallback search
         REAL_GIT=$(type -aP git | grep -v "$0" | head -n 1)
    fi

    debug_log "Passing through to: $REAL_GIT"
    "$REAL_GIT" "$@"
    RET=$?
    
    # If explicit exit code wasn't set, use the real one
    if [ -z "$EXIT_CODE" ]; then
        EXIT_CODE=$RET
    fi
fi

# Default exit code 0 if not set
if [ -z "$EXIT_CODE" ]; then
    EXIT_CODE=0
fi

exit "$EXIT_CODE"
