"""Service configuration loading and dataclasses.

Parses config/services.json and .ralph/services.json overrides into
typed dataclasses used by the scheduler.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


@dataclass
class ServiceConfig:
    """Configuration for a single service."""

    id: str
    description: str = ""
    phase: str = "periodic"
    order: int = 0
    enabled: bool = True
    required: bool = False
    schedule: dict[str, Any] = field(default_factory=lambda: {"type": "tick"})
    execution: dict[str, Any] = field(default_factory=dict)
    concurrency: dict[str, Any] = field(default_factory=lambda: {
        "max_instances": 1,
        "if_running": "skip",
    })
    condition: dict[str, Any] | None = None
    circuit_breaker: dict[str, Any] | None = None
    triggers: dict[str, list[str]] | None = None
    timeout: int = 300
    restart_policy: dict[str, Any] = field(default_factory=lambda: {
        "on_failure": "skip",
        "max_retries": 2,
    })

    @property
    def schedule_type(self) -> str:
        return self.schedule.get("type", "tick")

    @property
    def interval(self) -> int:
        return self.schedule.get("interval", 0)

    @property
    def jitter(self) -> int:
        return self.schedule.get("jitter", 0)

    @property
    def run_on_startup(self) -> bool:
        return self.schedule.get("run_on_startup", False)

    @property
    def exec_type(self) -> str:
        return self.execution.get("type", "function")

    @property
    def exec_function(self) -> str:
        return self.execution.get("function", "")

    @property
    def exec_command(self) -> str:
        return self.execution.get("command", "")

    @property
    def cb_enabled(self) -> bool:
        if self.circuit_breaker is None:
            return False
        return self.circuit_breaker.get("enabled", False)

    @property
    def cb_threshold(self) -> int:
        if self.circuit_breaker is None:
            return 5
        return self.circuit_breaker.get("threshold", 5)

    @property
    def cb_cooldown(self) -> int:
        if self.circuit_breaker is None:
            return 300
        return self.circuit_breaker.get("cooldown", 300)


def _parse_service(raw: dict[str, Any], defaults: dict[str, Any]) -> ServiceConfig:
    """Parse a raw service dict into ServiceConfig."""
    restart_policy = raw.get("restart_policy", defaults.get("restart_policy", {
        "on_failure": "skip",
        "max_retries": 2,
    }))
    timeout = raw.get("timeout", defaults.get("timeout", 300))

    return ServiceConfig(
        id=raw["id"],
        description=raw.get("description", ""),
        phase=raw.get("phase", "periodic"),
        order=raw.get("order", 0),
        enabled=raw.get("enabled", True),
        required=raw.get("required", False),
        schedule=raw.get("schedule", {"type": "tick"}),
        execution=raw.get("execution", {}),
        concurrency=raw.get("concurrency", {"max_instances": 1, "if_running": "skip"}),
        condition=raw.get("condition"),
        circuit_breaker=raw.get("circuit_breaker"),
        triggers=raw.get("triggers"),
        timeout=timeout,
        restart_policy=restart_policy,
    )


def load_services(
    wiggum_home: str,
    ralph_dir: str,
) -> list[ServiceConfig]:
    """Load service configs from config/services.json + .ralph/services.json.

    Args:
        wiggum_home: WIGGUM_HOME path.
        ralph_dir: RALPH_DIR path (.ralph directory).

    Returns:
        List of ServiceConfig sorted by (phase_order, service order).
    """
    config_path = Path(wiggum_home) / "config" / "services.json"
    override_path = Path(ralph_dir) / "services.json"

    if not config_path.exists():
        raise FileNotFoundError(f"services.json not found: {config_path}")

    with open(config_path) as f:
        raw_config = json.load(f)

    defaults = raw_config.get("defaults", {})
    services = [_parse_service(s, defaults) for s in raw_config.get("services", [])]

    # Apply project overrides
    if override_path.exists():
        with open(override_path) as f:
            overrides = json.load(f)
        _apply_overrides(services, overrides)

    return services


def _apply_overrides(
    services: list[ServiceConfig],
    overrides: dict[str, Any],
) -> None:
    """Apply .ralph/services.json overrides in-place."""
    by_id = {s.id: s for s in services}

    for override in overrides.get("services", []):
        sid = override.get("id", "")
        if sid in by_id:
            svc = by_id[sid]
            if "enabled" in override:
                svc.enabled = override["enabled"]
            if "schedule" in override:
                svc.schedule.update(override["schedule"])
            if "concurrency" in override:
                svc.concurrency.update(override["concurrency"])


def apply_run_mode_filters(
    services: list[ServiceConfig],
    run_mode: str,
    no_flags: dict[str, bool],
) -> list[ServiceConfig]:
    """Disable services based on run mode and --no-* flags.

    Args:
        services: List of services to filter.
        run_mode: One of default, fix-only, merge-only, resume-only.
        no_flags: Dict with keys no_resume, no_fix, no_merge, no_sync.

    Returns:
        Same list (modified in-place) with .enabled toggled.
    """
    by_id = {s.id: s for s in services}

    if run_mode == "merge-only":
        for sid in ("fix-workers", "multi-pr-planner"):
            if sid in by_id:
                by_id[sid].enabled = False
    elif run_mode == "resume-only":
        for sid in ("fix-workers", "multi-pr-planner", "resolve-workers",
                     "orphan-workspace"):
            if sid in by_id:
                by_id[sid].enabled = False

    if no_flags.get("no_resume"):
        for sid in ("resume-poll", "resume-decide"):
            if sid in by_id:
                by_id[sid].enabled = False
    if no_flags.get("no_fix"):
        for sid in ("fix-workers", "multi-pr-planner"):
            if sid in by_id:
                by_id[sid].enabled = False
    if no_flags.get("no_merge"):
        if "resolve-workers" in by_id:
            by_id["resolve-workers"].enabled = False
    if no_flags.get("no_sync"):
        for sid in ("github-issue-sync", "github-plan-sync", "pr-sync"):
            if sid in by_id:
                by_id[sid].enabled = False

    return services


# Phase ordering for sorting
_PHASE_ORDER = {
    "startup": 0,
    "pre": 1,
    "periodic": 2,
    "post": 3,
    "shutdown": 4,
}


class ServiceRegistry:
    """In-memory registry of services with phase-based lookups."""

    def __init__(self, services: list[ServiceConfig]) -> None:
        self._services = {s.id: s for s in services}
        self._by_phase: dict[str, list[ServiceConfig]] = {}
        self._rebuild_phase_index()

    def _rebuild_phase_index(self) -> None:
        self._by_phase = {}
        for svc in self._services.values():
            phase = svc.phase
            if phase not in self._by_phase:
                self._by_phase[phase] = []
            self._by_phase[phase].append(svc)
        # Sort each phase by order
        for phase in self._by_phase:
            self._by_phase[phase].sort(key=lambda s: s.order)

    def get(self, service_id: str) -> ServiceConfig | None:
        return self._services.get(service_id)

    def get_phase_services(self, phase: str) -> list[ServiceConfig]:
        """Get enabled services for a phase, sorted by order."""
        return [s for s in self._by_phase.get(phase, []) if s.enabled]

    def get_enabled(self) -> list[ServiceConfig]:
        """Get all enabled services."""
        return [s for s in self._services.values() if s.enabled]

    def get_periodic_services(self) -> list[ServiceConfig]:
        """Get enabled periodic services (interval/cron/event scheduled)."""
        return [s for s in self.get_phase_services("periodic") if s.enabled]

    def all_ids(self) -> list[str]:
        return list(self._services.keys())

    def count(self) -> int:
        return len(self._services)
