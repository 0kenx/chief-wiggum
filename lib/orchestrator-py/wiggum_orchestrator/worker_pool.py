"""Worker pool — zero-fork PID tracking.

Tracks spawned worker PIDs, detects completion via os.kill(pid, 0),
and persists pool state to pool.json for cross-process compatibility.
"""

from __future__ import annotations

import json
import os
import tempfile
import time
from dataclasses import dataclass, field


@dataclass
class WorkerEntry:
    """State for a tracked worker process."""

    pid: int
    worker_type: str  # main|fix|resolve
    task_id: str
    started_at: float = field(default_factory=time.time)


class WorkerPool:
    """PID-based worker tracking with os.kill liveness checks."""

    def __init__(self, ralph_dir: str) -> None:
        self._ralph_dir = ralph_dir
        self._pool_file = os.path.join(ralph_dir, "orchestrator", "pool.json")
        self._workers: dict[int, WorkerEntry] = {}

    def add(self, pid: int, worker_type: str, task_id: str) -> None:
        self._workers[pid] = WorkerEntry(
            pid=pid,
            worker_type=worker_type,
            task_id=task_id,
        )

    def remove(self, pid: int) -> WorkerEntry | None:
        return self._workers.pop(pid, None)

    def count(self, worker_type: str | None = None) -> int:
        if worker_type is None:
            return len(self._workers)
        return sum(1 for w in self._workers.values() if w.worker_type == worker_type)

    def get_by_type(self, worker_type: str) -> list[WorkerEntry]:
        return [w for w in self._workers.values() if w.worker_type == worker_type]

    def cleanup_finished(
        self,
        on_complete: callable | None = None,
    ) -> list[WorkerEntry]:
        """Check all workers, remove finished ones.

        Uses os.kill(pid, 0) for zero-fork liveness check.

        Args:
            on_complete: Callback(entry) for each finished worker.

        Returns:
            List of completed WorkerEntry objects.
        """
        completed = []
        for pid in list(self._workers.keys()):
            entry = self._workers[pid]
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                completed.append(entry)
                del self._workers[pid]
                if on_complete:
                    on_complete(entry)
            except PermissionError:
                # Process exists but we can't signal it — still alive
                pass
        return completed

    def is_alive(self, pid: int) -> bool:
        try:
            os.kill(pid, 0)
            return True
        except (ProcessLookupError, PermissionError):
            return False

    def all_pids(self) -> list[int]:
        return list(self._workers.keys())

    def save(self) -> None:
        """Persist pool state to pool.json (atomic write)."""
        os.makedirs(os.path.dirname(self._pool_file), exist_ok=True)
        entries = {}
        for pid, w in self._workers.items():
            entries[str(pid)] = {
                "type": w.worker_type,
                "task_id": w.task_id,
                "started_at": int(w.started_at),
            }
        data = {"workers": entries}
        fd, tmp = tempfile.mkstemp(dir=os.path.dirname(self._pool_file))
        try:
            with os.fdopen(fd, "w") as f:
                json.dump(data, f)
            os.rename(tmp, self._pool_file)
        except BaseException:
            try:
                os.unlink(tmp)
            except OSError:
                pass
            raise

    def restore(self) -> int:
        """Restore pool from pool.json, verifying PIDs.

        Returns:
            Number of live workers restored.
        """
        if not os.path.isfile(self._pool_file):
            return 0
        try:
            with open(self._pool_file) as f:
                data = json.load(f)
        except (json.JSONDecodeError, OSError):
            return 0

        count = 0
        for pid_str, info in data.get("workers", {}).items():
            pid = int(pid_str)
            try:
                os.kill(pid, 0)
            except (ProcessLookupError, PermissionError):
                continue
            self._workers[pid] = WorkerEntry(
                pid=pid,
                worker_type=info.get("type", "main"),
                task_id=info.get("task_id", ""),
                started_at=info.get("started_at", time.time()),
            )
            count += 1
        return count
