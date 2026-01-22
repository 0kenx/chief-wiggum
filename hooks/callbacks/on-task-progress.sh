#!/usr/bin/env bash
# Callback: Log worker progress to central workers log
# Runs from workspace dir: .ralph/workers/<worker_id>/workspace

WORKER_DIR="$(dirname "$PWD")"
WORKER_ID="$(basename "$WORKER_DIR")"
RALPH_DIR="$(dirname "$(dirname "$WORKER_DIR")")"

mkdir -p "$RALPH_DIR/logs" 2>/dev/null || true
echo "[$(date -Iseconds)] INFO: Worker $WORKER_ID made progress" >> "$RALPH_DIR/logs/workers.log"
