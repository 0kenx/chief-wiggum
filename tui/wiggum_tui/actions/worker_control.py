"""Worker control actions - stop, kill, verify via wiggum CLI."""

import os
import subprocess
from pathlib import Path


def stop_worker(worker_id: str) -> bool:
    """Stop a worker gracefully via wiggum worker stop.

    Args:
        worker_id: Worker ID (e.g., worker-TASK-001-123456).

    Returns:
        True if command succeeded, False otherwise.
    """
    try:
        result = subprocess.run(
            ["wiggum", "worker", "stop", worker_id],
            capture_output=True,
            timeout=35,  # wiggum worker stop has 30s internal timeout
        )
        return result.returncode == 0
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError):
        return False


def kill_worker(worker_id: str) -> bool:
    """Kill a worker forcefully via wiggum worker kill.

    Args:
        worker_id: Worker ID (e.g., worker-TASK-001-123456).

    Returns:
        True if command succeeded, False otherwise.
    """
    try:
        result = subprocess.run(
            ["wiggum", "worker", "kill", worker_id],
            capture_output=True,
            timeout=10,
        )
        return result.returncode == 0
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError):
        return False


def verify_worker_process(pid: int) -> bool:
    """Verify PID is actually a worker process.

    Args:
        pid: Process ID to verify.

    Returns:
        True if the process is a worker, False otherwise.
    """
    try:
        cmdline_path = Path(f"/proc/{pid}/cmdline")
        if cmdline_path.exists():
            cmdline = cmdline_path.read_text()
            # Agents run in bash subshells via run_agent()
            return "bash" in cmdline
        return False
    except (OSError, PermissionError):
        return False


def is_process_running(pid: int) -> bool:
    """Check if a process is running.

    Args:
        pid: Process ID to check.

    Returns:
        True if process exists, False otherwise.
    """
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        # Process exists but we can't signal it
        return True
