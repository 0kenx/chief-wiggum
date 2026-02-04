"""Service state persistence — read/write state.json.

Same JSON schema as bash service-state.sh for bidirectional compatibility:
a user can stop the Python orchestrator and restart with bash (or vice versa).
"""

from __future__ import annotations

import json
import os
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class ServiceEntry:
    """In-memory state for one service."""

    last_run: float = 0.0
    status: str = "stopped"  # running|stopped|failed|skipped
    run_count: int = 0
    fail_count: int = 0
    pid: int | None = None
    success_count: int = 0
    last_success: float = 0.0
    retry_count: int = 0
    backoff_until: float = 0.0

    # Circuit breaker
    circuit_state: str = "closed"  # closed|open|half-open
    circuit_opened_at: float = 0.0
    half_open_attempts: int = 0

    # Metrics
    total_duration_ms: int = 0
    last_duration_ms: int = 0
    min_duration_ms: int = 0
    max_duration_ms: int = 0

    # Queue (stored as list of dicts)
    queue: list[dict] = field(default_factory=list)


class ServiceState:
    """Manages in-memory service state with JSON persistence.

    State file: {ralph_dir}/services/state.json
    """

    def __init__(self, ralph_dir: str) -> None:
        self._ralph_dir = ralph_dir
        self._state_dir = os.path.join(ralph_dir, "services")
        self._state_file = os.path.join(self._state_dir, "state.json")
        self._entries: dict[str, ServiceEntry] = {}
        self._dirty = False

    def get(self, service_id: str) -> ServiceEntry:
        """Get or create state entry for a service."""
        if service_id not in self._entries:
            self._entries[service_id] = ServiceEntry()
        return self._entries[service_id]

    def mark_dirty(self) -> None:
        self._dirty = True

    # ------------------------------------------------------------------
    # Lifecycle marks
    # ------------------------------------------------------------------

    def mark_started(self, service_id: str, pid: int | None = None) -> None:
        entry = self.get(service_id)
        entry.status = "running"
        entry.last_run = time.time()
        entry.run_count += 1
        entry.pid = pid
        self._dirty = True

    def mark_completed(self, service_id: str) -> None:
        entry = self.get(service_id)
        entry.status = "stopped"
        entry.fail_count = 0
        entry.retry_count = 0
        entry.backoff_until = 0.0
        entry.last_success = time.time()
        entry.success_count += 1
        entry.pid = None
        # Reset circuit breaker on success
        if entry.circuit_state != "closed":
            entry.circuit_state = "closed"
            entry.half_open_attempts = 0
        self._dirty = True

    def mark_failed(self, service_id: str) -> None:
        entry = self.get(service_id)
        entry.status = "failed"
        entry.fail_count += 1
        entry.pid = None
        self._dirty = True

    def mark_skipped(self, service_id: str) -> None:
        entry = self.get(service_id)
        entry.status = "skipped"

    def is_running(self, service_id: str) -> bool:
        entry = self.get(service_id)
        if entry.status != "running" or entry.pid is None:
            return False
        # Verify PID is alive
        try:
            os.kill(entry.pid, 0)
            return True
        except (ProcessLookupError, PermissionError):
            entry.status = "stopped"
            entry.pid = None
            return False

    def record_execution(
        self, service_id: str, duration_ms: int, exit_code: int,
    ) -> None:
        entry = self.get(service_id)
        entry.last_duration_ms = duration_ms
        entry.total_duration_ms += duration_ms
        if entry.min_duration_ms == 0 or duration_ms < entry.min_duration_ms:
            entry.min_duration_ms = duration_ms
        if duration_ms > entry.max_duration_ms:
            entry.max_duration_ms = duration_ms
        self._dirty = True

    # ------------------------------------------------------------------
    # Backoff
    # ------------------------------------------------------------------

    def is_in_backoff(self, service_id: str) -> bool:
        return time.time() < self.get(service_id).backoff_until

    def set_backoff(self, service_id: str, duration: float) -> None:
        self.get(service_id).backoff_until = time.time() + duration
        self._dirty = True

    # ------------------------------------------------------------------
    # Persistence
    # ------------------------------------------------------------------

    def save(self) -> None:
        """Write state.json atomically. Same schema as bash."""
        os.makedirs(self._state_dir, exist_ok=True)
        now = int(time.time())
        services = {}
        for sid, e in self._entries.items():
            services[sid] = {
                "last_run": int(e.last_run),
                "status": e.status,
                "run_count": e.run_count,
                "fail_count": e.fail_count,
                "pid": e.pid,
                "circuit": {
                    "state": e.circuit_state,
                    "opened_at": int(e.circuit_opened_at),
                    "half_open_attempts": e.half_open_attempts,
                },
                "metrics": {
                    "total_duration_ms": e.total_duration_ms,
                    "success_count": e.success_count,
                    "last_duration_ms": e.last_duration_ms,
                    "min_duration_ms": e.min_duration_ms,
                    "max_duration_ms": e.max_duration_ms,
                },
                "queue": e.queue,
                "backoff_until": int(e.backoff_until),
                "retry_count": e.retry_count,
                "last_success": int(e.last_success),
            }
        state = {"version": "1.0", "saved_at": now, "services": services}
        fd, tmp = tempfile.mkstemp(dir=self._state_dir)
        try:
            with os.fdopen(fd, "w") as f:
                json.dump(state, f)
            os.rename(tmp, self._state_file)
        except BaseException:
            try:
                os.unlink(tmp)
            except OSError:
                pass
            raise
        self._dirty = False

    def save_if_dirty(self) -> None:
        if self._dirty:
            self.save()

    def restore(self) -> bool:
        """Load state.json, verify PIDs with os.kill(pid, 0).

        Returns:
            True if state was restored, False if no state file.
        """
        if not os.path.isfile(self._state_file):
            return False
        try:
            with open(self._state_file) as f:
                data = json.load(f)
        except (json.JSONDecodeError, OSError):
            return False

        for sid, raw in data.get("services", {}).items():
            e = self.get(sid)
            e.last_run = raw.get("last_run", 0)
            e.run_count = raw.get("run_count", 0)
            e.fail_count = raw.get("fail_count", 0)
            e.last_success = raw.get("last_success", 0)
            e.retry_count = raw.get("retry_count", 0)
            e.backoff_until = raw.get("backoff_until", 0)
            e.success_count = raw.get("metrics", {}).get("success_count", 0)
            e.total_duration_ms = raw.get("metrics", {}).get("total_duration_ms", 0)
            e.last_duration_ms = raw.get("metrics", {}).get("last_duration_ms", 0)
            e.min_duration_ms = raw.get("metrics", {}).get("min_duration_ms", 0)
            e.max_duration_ms = raw.get("metrics", {}).get("max_duration_ms", 0)
            e.queue = raw.get("queue", [])

            circuit = raw.get("circuit", {})
            e.circuit_state = circuit.get("state", "closed")
            e.circuit_opened_at = circuit.get("opened_at", 0)
            e.half_open_attempts = circuit.get("half_open_attempts", 0)

            # Verify running PIDs
            saved_status = raw.get("status", "stopped")
            saved_pid = raw.get("pid")
            if saved_status == "running" and saved_pid is not None:
                try:
                    os.kill(saved_pid, 0)
                    e.status = "running"
                    e.pid = saved_pid
                except (ProcessLookupError, PermissionError):
                    e.status = "stopped"
                    e.pid = None
            else:
                e.status = "stopped"
                e.pid = None

        return True
