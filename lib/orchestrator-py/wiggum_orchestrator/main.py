"""Main entry point — arg parsing, main loop, signal handling."""

from __future__ import annotations

import argparse
import os
import signal
import sys
import time
import threading

from wiggum_orchestrator import logging_bridge as log
from wiggum_orchestrator.circuit_breaker import CircuitBreaker
from wiggum_orchestrator.config import (
    ServiceRegistry,
    apply_run_mode_filters,
    load_services,
)
from wiggum_orchestrator.service_executor import ServiceExecutor
from wiggum_orchestrator.service_scheduler import ServiceScheduler
from wiggum_orchestrator.service_state import ServiceState
from wiggum_orchestrator.worker_pool import WorkerPool

# Graceful shutdown event
_exit_event = threading.Event()


def _handle_signal(signum: int, frame: object) -> None:
    """Signal handler for SIGINT/SIGTERM."""
    sig_name = signal.Signals(signum).name
    log.log(f"Received {sig_name}, shutting down...")
    _exit_event.set()


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="wiggum-orchestrator-py",
        description="Python service scheduler for Chief Wiggum",
    )
    parser.add_argument(
        "mode", nargs="?", default=None,
        choices=["plan"],
        help="Optional positional mode (plan)",
    )
    parser.add_argument(
        "--run-mode",
        default=os.environ.get("WIGGUM_RUN_MODE", "default"),
        choices=["default", "fix-only", "merge-only", "resume-only"],
        help="Orchestrator run mode",
    )
    parser.add_argument(
        "--max-workers", type=int,
        default=None,
        help="Maximum concurrent workers (default: 4)",
    )
    parser.add_argument(
        "--max-iters", type=int,
        default=None,
        help="Maximum iterations per worker (default: 20)",
    )
    parser.add_argument(
        "--max-turns", type=int,
        default=None,
        help="Maximum turns per Claude session (default: 50)",
    )
    parser.add_argument(
        "--fix-agents", type=int,
        default=None,
        help="Maximum concurrent fix/resolve workers (default: 2)",
    )
    parser.add_argument(
        "--pipeline",
        default=None,
        help="Pipeline config to use",
    )
    parser.add_argument(
        "--smart", action="store_true",
        default=os.environ.get("WIGGUM_SMART_MODE", "false") == "true",
        help="Dynamically select pipeline per task based on complexity",
    )
    parser.add_argument(
        "--force", action="store_true",
        default=False,
        help="Override stale orchestrator lock",
    )
    parser.add_argument(
        "--no-resume", action="store_true",
        default=os.environ.get("WIGGUM_NO_RESUME", "false") == "true",
    )
    parser.add_argument(
        "--no-fix", action="store_true",
        default=os.environ.get("WIGGUM_NO_FIX", "false") == "true",
    )
    parser.add_argument(
        "--no-merge", action="store_true",
        default=os.environ.get("WIGGUM_NO_MERGE", "false") == "true",
    )
    parser.add_argument(
        "--no-sync", action="store_true",
        default=os.environ.get("WIGGUM_NO_SYNC", "false") == "true",
    )
    parser.add_argument(
        "--tick-interval",
        type=float,
        default=5.0,
        help="Seconds between main loop ticks (default: 5)",
    )
    return parser.parse_args()


def _get_required_env(name: str) -> str:
    val = os.environ.get(name)
    if not val:
        print(f"ERROR: {name} not set", file=sys.stderr)
        sys.exit(1)
    return val


def run(args: argparse.Namespace) -> int:
    """Main orchestrator loop.

    Returns:
        Exit code (0 = clean shutdown).
    """
    wiggum_home = _get_required_env("WIGGUM_HOME")
    project_dir = _get_required_env("PROJECT_DIR")
    ralph_dir = os.environ.get("RALPH_DIR", os.path.join(project_dir, ".ralph"))

    # Initialize logging
    log_file = os.environ.get("LOG_FILE")
    if not log_file:
        log_dir = os.path.join(ralph_dir, "logs")
        os.makedirs(log_dir, exist_ok=True)
        log_file = os.path.join(log_dir, "orchestrator.log")
        os.environ["LOG_FILE"] = log_file
    log.init(log_file=log_file)

    log.log("Python orchestrator starting")

    # Load service configuration
    services = load_services(wiggum_home, ralph_dir)

    no_flags = {
        "no_resume": args.no_resume,
        "no_fix": args.no_fix,
        "no_merge": args.no_merge,
        "no_sync": args.no_sync,
    }
    services = apply_run_mode_filters(services, args.run_mode, no_flags)

    registry = ServiceRegistry(services)
    log.log(f"Loaded {registry.count()} services")

    # Initialize state
    state = ServiceState(ralph_dir)
    if state.restore():
        log.log("Restored previous service state")

    # Propagate CLI args into environment so bridge picks them up.
    # CLI args take precedence over env vars.
    if args.max_workers is not None:
        os.environ["MAX_WORKERS"] = str(args.max_workers)
    if args.max_iters is not None:
        os.environ["MAX_ITERATIONS"] = str(args.max_iters)
    if args.max_turns is not None:
        os.environ["MAX_TURNS"] = str(args.max_turns)
    if args.fix_agents is not None:
        os.environ["FIX_WORKER_LIMIT"] = str(args.fix_agents)
    if args.pipeline is not None:
        os.environ["WIGGUM_PIPELINE"] = args.pipeline
    if args.mode == "plan":
        os.environ["WIGGUM_PLAN_MODE"] = "true"
    if args.smart:
        os.environ["WIGGUM_SMART_MODE"] = "true"

    # Build env overrides for bridge
    env_overrides: dict[str, str] = {}
    for key in (
        "MAX_WORKERS", "MAX_ITERATIONS", "MAX_TURNS", "AGENT_TYPE",
        "WIGGUM_RUN_MODE", "WIGGUM_NO_RESUME", "WIGGUM_NO_FIX",
        "WIGGUM_NO_MERGE", "WIGGUM_NO_SYNC", "FIX_WORKER_LIMIT",
        "FIX_WORKER_TIMEOUT", "RESOLVE_WORKER_TIMEOUT", "AGING_FACTOR",
        "SIBLING_WIP_PENALTY", "PLAN_BONUS", "DEP_BONUS_PER_TASK",
        "RESUME_INITIAL_BONUS", "RESUME_FAIL_PENALTY",
        "RESUME_MIN_RETRY_INTERVAL", "MAX_SKIP_RETRIES",
        "PID_WAIT_TIMEOUT", "LOG_FILE",
        "RESUME_MAX_DECIDE_CONCURRENT",
        "WIGGUM_PIPELINE", "WIGGUM_PLAN_MODE", "WIGGUM_SMART_MODE",
    ):
        val = os.environ.get(key)
        if val is not None:
            env_overrides[key] = val

    executor = ServiceExecutor(wiggum_home, ralph_dir, project_dir, env_overrides)
    cb = CircuitBreaker(state)
    scheduler = ServiceScheduler(registry, state, executor, cb)

    # Worker pool (for tracking)
    pool = WorkerPool(ralph_dir)
    pool.restore()

    # Startup phase
    log.log("Running startup phase...")
    if not scheduler.run_phase("startup"):
        log.log_error("Startup phase failed, aborting")
        return 1

    # Clear stale exit signal
    exit_file = os.path.join(ralph_dir, "orchestrator", "should-exit")
    try:
        os.unlink(exit_file)
    except FileNotFoundError:
        pass

    iteration = 0
    log.log("Starting service-based scheduler (Python)")

    # Main loop
    while not _exit_event.is_set():
        iteration += 1

        # Check for exit signal from bash handlers
        if os.path.isfile(exit_file):
            log.log("Exit signal detected, shutting down")
            break

        # Pre-phase
        scheduler.run_phase("pre")

        # Periodic phase (interval checks + execution)
        scheduler.run_phase("periodic")

        # Post-phase
        scheduler.run_phase("post")

        # Persist state
        state.save_if_dirty()

        # Sleep with early wake on signal
        _exit_event.wait(timeout=args.tick_interval)

    # Shutdown phase
    log.log("Running shutdown phase...")
    scheduler.run_phase("shutdown")
    state.save()
    pool.save()

    log.log("Python orchestrator stopped")
    return 0


def main() -> None:
    """CLI entry point."""
    signal.signal(signal.SIGINT, _handle_signal)
    signal.signal(signal.SIGTERM, _handle_signal)

    args = _parse_args()
    sys.exit(run(args))
