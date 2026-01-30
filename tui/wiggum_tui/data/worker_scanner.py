"""Worker scanner - ported from TypeScript."""

import json
import os
import re
import subprocess
from pathlib import Path
from .models import PipelineInfo, Worker, WorkerStatus


# Pattern: worker-TASK-XXX-TIMESTAMP
WORKER_PATTERN = re.compile(r"^worker-([A-Za-z]{2,10}-\d{1,4})-(\d+)$")

# Cache for completed/failed workers: worker_dir_name -> Worker
# These workers' state never changes, so we can skip re-scanning them.
_completed_workers_cache: dict[str, Worker] = {}

# Cache for pipeline-config.json: worker_dir -> (mtime, PipelineInfo)
_pipeline_config_cache: dict[str, tuple[float, PipelineInfo | None]] = {}


def clear_completed_workers_cache() -> None:
    """Clear the completed workers cache.

    This is primarily used for testing to ensure a clean state between tests.
    """
    global _completed_workers_cache
    _completed_workers_cache.clear()
    _pipeline_config_cache.clear()


def read_pipeline_config(worker_dir: Path) -> PipelineInfo | None:
    """Read pipeline-config.json from a worker directory.

    Uses mtime-based caching to avoid re-reading unchanged files.

    Args:
        worker_dir: Path to the worker directory.

    Returns:
        PipelineInfo if file exists and is valid, None otherwise.
    """
    config_path = worker_dir / "pipeline-config.json"
    cache_key = str(worker_dir)

    try:
        mtime = config_path.stat().st_mtime
    except OSError:
        # File doesn't exist, clear cache entry if present
        _pipeline_config_cache.pop(cache_key, None)
        return None

    # Check cache
    cached = _pipeline_config_cache.get(cache_key)
    if cached and cached[0] == mtime:
        return cached[1]

    # Parse file
    try:
        data = json.loads(config_path.read_text())
        pipeline_name = data.get("pipeline", {}).get("name", "")
        current = data.get("current", {})
        step_id = current.get("step_id", "")
        step_idx = current.get("step_idx", 0)

        # Look up agent from the steps map
        agent = ""
        steps = data.get("steps", {})
        if step_id and step_id in steps:
            agent = steps[step_id].get("agent", "")

        info = PipelineInfo(
            pipeline_name=pipeline_name,
            step_id=step_id,
            step_idx=step_idx,
            agent=agent,
        )
        _pipeline_config_cache[cache_key] = (mtime, info)
        return info
    except (json.JSONDecodeError, OSError, KeyError):
        _pipeline_config_cache[cache_key] = (mtime, None)
        return None


def is_process_running(pid: int) -> bool:
    """Check if a process is running."""
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


def batch_check_processes(pids: list[int]) -> dict[int, str]:
    """Check multiple PIDs in a single ps call.

    Args:
        pids: List of process IDs to check.

    Returns:
        Dictionary mapping running PIDs to their command args.
        PIDs not in the dict are not running.
    """
    if not pids:
        return {}

    try:
        # Single ps call for all PIDs - much faster than per-PID calls
        result = subprocess.run(
            ["ps", "-p", ",".join(str(p) for p in pids), "-o", "pid=,args="],
            capture_output=True,
            text=True,
            timeout=5,
        )
        process_info: dict[int, str] = {}
        for line in result.stdout.strip().split("\n"):
            if not line.strip():
                continue
            parts = line.strip().split(None, 1)
            if len(parts) >= 2:
                try:
                    pid = int(parts[0])
                    args = parts[1]
                    process_info[pid] = args
                except ValueError:
                    continue
        return process_info
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return {}


def is_worker_process(pid: int, process_info: dict[int, str] | None = None) -> bool:
    """Check if PID is actually a worker process.

    Args:
        pid: Process ID to check.
        process_info: Optional pre-fetched process info from batch_check_processes().
            If not provided, will make a subprocess call (slower).
    """
    if process_info is not None:
        args = process_info.get(pid, "")
        return "bash" in args

    # Fallback to single-PID check
    try:
        result = subprocess.run(
            ["ps", "-p", str(pid), "-o", "args="],
            capture_output=True,
            text=True,
            timeout=5,
        )
        # Agents run in bash subshells via run_agent()
        return "bash" in result.stdout
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return False


def is_orchestrator_process(pid: int, process_info: dict[int, str] | None = None) -> bool:
    """Check if PID is actually an orchestrator process.

    Args:
        pid: Process ID to check.
        process_info: Optional pre-fetched process info from batch_check_processes().
            If not provided, will make a subprocess call (slower).
    """
    if process_info is not None:
        args = process_info.get(pid, "")
        return "wiggum-run" in args

    # Fallback to single-PID check
    try:
        result = subprocess.run(
            ["ps", "-p", str(pid), "-o", "args="],
            capture_output=True,
            text=True,
            timeout=5,
        )
        return "wiggum-run" in result.stdout
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return False


def get_prd_status(prd_path: Path) -> str:
    """Get status from PRD file content.

    Returns: 'complete', 'failed', or 'incomplete'
    """
    try:
        content = prd_path.read_text()
        if "- [*]" in content:
            return "failed"
        if "- [ ]" in content:
            return "incomplete"
        return "complete"
    except (OSError, FileNotFoundError):
        return "incomplete"


def scan_workers(ralph_dir: Path) -> list[Worker]:
    """Scan .ralph/workers directory for workers.

    Args:
        ralph_dir: Path to .ralph directory.

    Returns:
        List of Worker objects, sorted by timestamp (newest first).
    """
    global _completed_workers_cache

    workers_dir = ralph_dir / "workers"
    workers: list[Worker] = []

    if not workers_dir.is_dir():
        return workers

    # First pass: collect worker directories, using cache for completed workers
    # (dir, task_id, dir_timestamp, pid, pid_mtime, has_pid_file)
    worker_entries: list[tuple[Path, str, int, int | None, int | None, bool]] = []

    for entry in workers_dir.iterdir():
        if not entry.name.startswith("worker-"):
            continue
        if not entry.is_dir():
            continue

        # Parse worker ID
        match = WORKER_PATTERN.match(entry.name)
        if not match:
            continue

        # Use full path as cache key to avoid conflicts across different ralph directories
        cache_key = str(entry.resolve())

        # Check if this worker is already cached as completed/failed
        if cache_key in _completed_workers_cache:
            workers.append(_completed_workers_cache[cache_key])
            continue

        task_id, ts_str = match.groups()
        # Use timestamp from directory name as fallback (original creation time)
        try:
            dir_timestamp = int(ts_str)
        except ValueError:
            dir_timestamp = 0

        pid_path = entry / "agent.pid"
        pid: int | None = None
        pid_mtime: int | None = None
        has_pid_file = pid_path.exists()

        if has_pid_file:
            try:
                pid_content = pid_path.read_text().strip()
                pid = int(pid_content)
                # Get agent.pid mtime - this is when the current agent started
                pid_mtime = int(pid_path.stat().st_mtime)
            except (ValueError, OSError):
                pass

        worker_entries.append((entry, task_id, dir_timestamp, pid, pid_mtime, has_pid_file))

    # Second pass: build Worker objects
    for entry, task_id, dir_timestamp, pid, pid_mtime, has_pid_file in worker_entries:
        prd_path = entry / "prd.md"
        log_path = entry / "worker.log"
        workspace_path = entry / "workspace"
        pr_url_path = entry / "pr_url.txt"

        status = WorkerStatus.STOPPED

        # Online status based solely on agent.pid file presence
        if has_pid_file:
            status = WorkerStatus.RUNNING

        # If not running, check PRD status
        if status != WorkerStatus.RUNNING:
            prd_status = get_prd_status(prd_path)
            if prd_status == "complete":
                status = WorkerStatus.COMPLETED
            elif prd_status == "failed":
                status = WorkerStatus.FAILED

        # For running workers, use agent.pid mtime (current agent start time)
        # For completed/stopped workers, use directory timestamp (original creation time)
        if status == WorkerStatus.RUNNING and pid_mtime is not None:
            timestamp = pid_mtime
        else:
            timestamp = dir_timestamp

        # Check for PR URL
        pr_url: str | None = None
        if pr_url_path.exists():
            try:
                pr_url = pr_url_path.read_text().strip()
                if not pr_url:
                    pr_url = None
            except OSError:
                pass

        worker = Worker(
            id=entry.name,
            task_id=task_id,
            timestamp=timestamp,
            pid=pid,
            status=status,
            prd_path=str(prd_path),
            log_path=str(log_path),
            workspace_path=str(workspace_path),
            pr_url=pr_url,
            pipeline_info=read_pipeline_config(entry),
        )

        # Cache completed/failed workers since their state never changes
        # Use full path as cache key to avoid conflicts
        cache_key = str(entry.resolve())
        if status in (WorkerStatus.COMPLETED, WorkerStatus.FAILED):
            _completed_workers_cache[cache_key] = worker

        workers.append(worker)

    # Sort by timestamp descending (newest first)
    workers.sort(key=lambda w: w.timestamp, reverse=True)

    return workers


def get_orchestrator_status(ralph_dir: Path) -> tuple[bool, int | None]:
    """Get orchestrator status.

    Args:
        ralph_dir: Path to .ralph directory.

    Returns:
        Tuple of (running: bool, pid: int | None).
    """
    pid_path = ralph_dir / ".orchestrator.pid"

    if not pid_path.exists():
        return False, None

    try:
        pid_content = pid_path.read_text().strip()
        pid = int(pid_content)

        if is_process_running(pid) and is_orchestrator_process(pid):
            return True, pid
    except (ValueError, OSError):
        pass

    return False, None


def get_worker_counts(workers: list[Worker]) -> dict[str, int]:
    """Get count of workers in each status.

    Args:
        workers: List of workers.

    Returns:
        Dictionary with counts for each status.
    """
    counts = {
        "running": 0,
        "stopped": 0,
        "completed": 0,
        "failed": 0,
        "total": len(workers),
    }
    for worker in workers:
        counts[worker.status.value] += 1
    return counts


def get_running_worker_for_task(ralph_dir: Path, task_id: str) -> Worker | None:
    """Find a running worker for a specific task ID.

    Args:
        ralph_dir: Path to .ralph directory.
        task_id: Task ID to search for (e.g., "TASK-001").

    Returns:
        Worker if a running worker is found for the task, None otherwise.
    """
    workers = scan_workers(ralph_dir)
    for worker in workers:
        if worker.task_id == task_id and worker.status == WorkerStatus.RUNNING:
            return worker
    return None


def get_task_running_status(ralph_dir: Path, task_ids: list[str]) -> dict[str, tuple[bool, int | None]]:
    """Get running status for multiple tasks at once (more efficient).

    Args:
        ralph_dir: Path to .ralph directory.
        task_ids: List of task IDs to check.

    Returns:
        Dictionary mapping task_id to (is_running, start_timestamp).
        start_timestamp is the agent.pid mtime (current agent start time) when running.
    """
    workers = scan_workers(ralph_dir)
    result: dict[str, tuple[bool, int | None]] = {}

    # Build a map of task_id -> running worker
    running_workers: dict[str, Worker] = {}
    for worker in workers:
        if worker.status == WorkerStatus.RUNNING:
            # Use the most recent worker for each task
            if worker.task_id not in running_workers:
                running_workers[worker.task_id] = worker

    for task_id in task_ids:
        if task_id in running_workers:
            worker = running_workers[task_id]
            result[task_id] = (True, worker.timestamp)
        else:
            result[task_id] = (False, None)

    return result
