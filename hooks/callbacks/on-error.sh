#!/usr/bin/env bash
# Callback: Log errors to central error log

WORKER_ID="$1"
MESSAGE="$2"

# Ensure log directory exists (callbacks run from project root)
mkdir -p .ralph/logs 2>/dev/null || true

# Log with format matching logger.sh
echo "[$(date -Iseconds)] ERROR: Worker $WORKER_ID: $MESSAGE" >> .ralph/logs/errors.log
