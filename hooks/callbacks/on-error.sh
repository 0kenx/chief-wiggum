#!/usr/bin/env bash
# Callback: Log errors to central error log
# Runs from workspace dir: .ralph/workers/<worker_id>/workspace

MESSAGE="$1"

WORKER_DIR="$(dirname "$PWD")"
WORKER_ID="$(basename "$WORKER_DIR")"
RALPH_DIR="$(dirname "$(dirname "$WORKER_DIR")")"

mkdir -p "$RALPH_DIR/logs" 2>/dev/null || true
echo "[$(date -Iseconds)] ERROR: Worker $WORKER_ID: $MESSAGE" >> "$RALPH_DIR/logs/errors.log"
