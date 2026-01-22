#!/usr/bin/env bash
# Shared exit codes for Chief Wiggum
#
# Exit code ranges:
#   0       - Success
#   1       - Generic/unspecified error
#   2       - Usage/argument error
#   3-5     - Init errors (wiggum-init)
#   10-19   - Worker start errors (wiggum start)
#   20-29   - Run/orchestration errors (wiggum-run)
#   30-39   - Validation errors (wiggum-validate)
#   40-49   - Review errors (wiggum-review)
#   50-55   - Clean errors (wiggum-clean)
#   56-63   - Agent errors (agent lifecycle)
#   64-127  - (reserved - some systems use these)
#   128+N   - Terminated by signal N (standard convention)
set -euo pipefail

# === OS Generic ===
export EXIT_OK=0
export EXIT_ERROR=1
export EXIT_USAGE=2

# === User Defined 3-63 ===
# === Init errors (3-5)
export EXIT_INIT_NOT_GIT_REPO=3

# === Worker start errors (10-19) ===
export EXIT_WORKER_MISSING_TASK_ID=10
export EXIT_WORKER_INVALID_TASK_FORMAT=11
export EXIT_WORKER_NO_RALPH_DIR=12
export EXIT_WORKER_NO_KANBAN=13
export EXIT_WORKER_TASK_NOT_FOUND=14
export EXIT_WORKER_ALREADY_EXISTS=15
export EXIT_WORKER_NOT_RUNNING=16
export EXIT_WORKER_PID_NOT_CREATED=17

# === Run/orchestration errors (20-29) ===
export EXIT_RUN_NO_RALPH_DIR=20
export EXIT_RUN_NO_KANBAN=21
export EXIT_RUN_VALIDATION_FAILED=22
export EXIT_RUN_GIT_DIRTY=23
export EXIT_RUN_SSH_FAILED=24
export EXIT_RUN_GPG_FAILED=25
export EXIT_RUN_ORCHESTRATOR_RUNNING=26
export EXIT_RUN_SPAWN_FAILED=27

# === Validation errors (30-39) ===
export EXIT_VALIDATE_FILE_NOT_FOUND=30
export EXIT_VALIDATE_ERRORS_FOUND=31

# === Review errors (40-49) ===
export EXIT_REVIEW_NO_RALPH_DIR=40
export EXIT_REVIEW_NO_WORKERS=41
export EXIT_REVIEW_PR_FAILED=42
export EXIT_REVIEW_MERGE_FAILED=43

# === Clean errors (50-59) ===
export EXIT_CLEAN_NO_RALPH_DIR=50
export EXIT_CLEAN_WORKERS_RUNNING=51
export EXIT_CLEAN_PATTERN_NOT_FOUND=52

# === Agent errors (56-63) ===
export EXIT_AGENT_INIT_FAILED=56       # agent_on_init hook failed
export EXIT_AGENT_PREREQ_FAILED=57     # Required paths missing before agent run
export EXIT_AGENT_READY_FAILED=58      # agent_on_ready hook failed
export EXIT_AGENT_OUTPUT_MISSING=59    # Required output files missing/empty after run
export EXIT_AGENT_VALIDATION_FAILED=60 # Agent validation review returned FAIL
export EXIT_AGENT_VIOLATION=61         # Workspace boundary violation detected
export EXIT_AGENT_TIMEOUT=62           # Agent exceeded timeout_seconds
export EXIT_AGENT_MAX_ITERATIONS=63    # Agent hit max_iterations limit

# === Signal exit codes (standard: 128 + signal number) ===
export EXIT_SIGINT=130   # 128 + 2 (SIGINT)
export EXIT_SIGTERM=143  # 128 + 15 (SIGTERM)
