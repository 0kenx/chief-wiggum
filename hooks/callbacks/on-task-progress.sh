#!/usr/bin/env bash
# Callback: Log worker progress to central workers log

WORKER_ID="$1"

# Ensure log directory exists (callbacks run from project root)
mkdir -p .ralph/logs 2>/dev/null || true

# Log with format matching logger.sh
echo "[$(date -Iseconds)] INFO: Worker $WORKER_ID made progress" >> .ralph/logs/workers.log
