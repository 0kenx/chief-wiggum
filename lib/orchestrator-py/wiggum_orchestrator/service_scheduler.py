"""Service scheduler — phase dispatch + periodic interval scheduling.

Replaces the bash service_scheduler_tick / service_scheduler_run_phase
with in-memory scheduling (time.time() + dict lookup, zero forks).
"""

from __future__ import annotations

import random
import subprocess
import time

from wiggum_orchestrator import logging_bridge as log
from wiggum_orchestrator.circuit_breaker import CircuitBreaker
from wiggum_orchestrator.config import ServiceConfig, ServiceRegistry
from wiggum_orchestrator.service_executor import ServiceExecutor
from wiggum_orchestrator.service_state import ServiceState


class ServiceScheduler:
    """Core scheduling engine."""

    def __init__(
        self,
        registry: ServiceRegistry,
        state: ServiceState,
        executor: ServiceExecutor,
        circuit_breaker: CircuitBreaker,
    ) -> None:
        self._registry = registry
        self._state = state
        self._executor = executor
        self._cb = circuit_breaker
        self._startup_complete = False
        # Background processes: service_id -> (Popen, ServiceConfig)
        self._background_procs: dict[str, tuple[subprocess.Popen, ServiceConfig]] = {}

    def run_phase(self, phase: str) -> bool:
        """Run services for a phase.

        - startup/shutdown/pre/post: collect functions, call bridge once.
        - periodic: check intervals, call each individually.

        Returns:
            True on success, False if a required startup service fails.
        """
        if phase == "periodic":
            return self._tick_periodic()

        return self._run_tick_phase(phase)

    def _run_tick_phase(self, phase: str) -> bool:
        """Run all tick-scheduled services in a phase via single bridge call."""
        services = self._registry.get_phase_services(phase)
        if not services:
            return True

        # Shutdown runs in reverse order
        if phase == "shutdown":
            services = list(reversed(services))

        functions: list[str] = []
        func_svc_map: list[ServiceConfig] = []

        for svc in services:
            if not self._conditions_met(svc):
                log.log_debug(f"Phase {phase}: skipping {svc.id} (conditions)")
                continue
            if svc.exec_type == "function" and svc.exec_function:
                functions.append(svc.exec_function)
                func_svc_map.append(svc)

        if not functions:
            return True

        # Mark all as started
        for svc in func_svc_map:
            self._state.mark_started(svc.id)

        success = self._executor.run_phase(phase, functions)

        # Mark all as completed/failed based on bridge exit
        for svc in func_svc_map:
            if success:
                self._state.mark_completed(svc.id)
            else:
                self._state.mark_failed(svc.id)

        # Startup phase: failure in required service is fatal
        if phase == "startup" and not success:
            for svc in func_svc_map:
                if svc.required:
                    log.log_error(
                        f"Required startup service '{svc.id}' failed",
                    )
                    return False
            log.log_warn(
                f"Optional startup services failed in phase {phase}",
            )

        return True

    def _tick_periodic(self) -> bool:
        """Check periodic services and run those that are due.

        Each service runs in its own subprocess (as in bash). Scheduling
        decisions (interval math, jitter, circuit breaker) are pure Python.
        """
        now = time.time()

        # Run startup services on first periodic tick
        if not self._startup_complete:
            self._run_startup_services(now)
            self._startup_complete = True

        # Poll background processes for completion
        self._poll_background_procs()

        for svc in self._registry.get_periodic_services():
            if not self._should_run_periodic(svc, now):
                continue

            self._run_single_service(svc)

        return True

    def _run_startup_services(self, now: float) -> None:
        """Run periodic services with run_on_startup on first tick.

        Services with timeout > 60s run in background to avoid blocking
        the scheduler. Their results are checked on subsequent ticks.
        """
        for svc in self._registry.get_periodic_services():
            if not svc.run_on_startup:
                continue
            if svc.schedule_type not in ("interval", "cron"):
                continue

            # Long-timeout services run in background to avoid blocking
            if svc.timeout > 60:
                log.log_debug(f"Startup run (background): {svc.id}")
                self._run_single_service_background(svc)
            else:
                log.log_debug(f"Startup run: {svc.id}")
                self._run_single_service(svc)

    def _should_run_periodic(self, svc: ServiceConfig, now: float) -> bool:
        """Check if a periodic service should run this tick."""
        # Circuit breaker
        if self._cb.blocks(svc):
            log.log_debug(f"Service {svc.id} blocked by circuit breaker")
            return False

        # Backoff
        if self._state.is_in_backoff(svc.id):
            return False

        # Conditions
        if not self._conditions_met(svc):
            return False

        # Concurrency check
        if self._state.is_running(svc.id):
            max_instances = svc.concurrency.get("max_instances", 1)
            if_running = svc.concurrency.get("if_running", "skip")
            if max_instances <= 1 and if_running == "skip":
                self._state.mark_skipped(svc.id)
                return False

        # Schedule type
        if svc.schedule_type == "interval":
            return self._interval_is_due(svc, now)

        if svc.schedule_type == "event":
            return False  # events are triggered externally

        return False

    def _interval_is_due(self, svc: ServiceConfig, now: float) -> bool:
        """Check if an interval-scheduled service is due."""
        interval = svc.interval
        if interval <= 0:
            return False

        entry = self._state.get(svc.id)
        elapsed = now - entry.last_run

        effective_interval = interval
        if svc.jitter > 0:
            effective_interval += random.randint(0, svc.jitter)

        return elapsed >= effective_interval

    def _run_single_service(self, svc: ServiceConfig) -> None:
        """Execute one periodic service."""
        self._state.mark_started(svc.id)

        if svc.exec_type == "function":
            rc = self._executor.run_function(svc)
        elif svc.exec_type == "command":
            rc = self._executor.run_command(svc)
        else:
            log.log_warn(f"Unknown exec type for {svc.id}: {svc.exec_type}")
            self._state.mark_failed(svc.id)
            return

        if rc == 0:
            self._state.mark_completed(svc.id)
            self._cb.record_success(svc)
        else:
            self._state.mark_failed(svc.id)
            self._cb.record_failure(svc)

    def _run_single_service_background(self, svc: ServiceConfig) -> None:
        """Execute a service in background (non-blocking)."""
        # Skip if already running in background
        if svc.id in self._background_procs:
            proc, _ = self._background_procs[svc.id]
            if proc.poll() is None:
                log.log_debug(f"Service {svc.id} already running in background")
                return

        proc = None
        if svc.exec_type == "function":
            proc = self._executor.run_function_background(svc)
        elif svc.exec_type == "command":
            proc = self._executor.run_command_background(svc)

        if proc:
            self._background_procs[svc.id] = (proc, svc)
            self._state.mark_started(svc.id, pid=proc.pid)
            log.log_debug(f"Started {svc.id} in background (PID {proc.pid})")
        else:
            log.log_warn(f"Background not supported for {svc.exec_type}, running sync")
            self._run_single_service(svc)

    def _poll_background_procs(self) -> None:
        """Check background processes for completion."""
        completed = []
        for svc_id, (proc, svc) in self._background_procs.items():
            rc = proc.poll()
            if rc is not None:
                # Process completed
                completed.append(svc_id)
                if rc == 0:
                    self._state.mark_completed(svc.id)
                    self._cb.record_success(svc)
                    log.log_debug(f"Background service {svc.id} completed (rc=0)")
                else:
                    self._state.mark_failed(svc.id)
                    self._cb.record_failure(svc)
                    log.log_warn(f"Background service {svc.id} failed (rc={rc})")

        # Remove completed from tracking
        for svc_id in completed:
            del self._background_procs[svc_id]

    def interrupt(self) -> None:
        """Interrupt the current foreground subprocess."""
        self._executor.interrupt()

    def terminate_all(self) -> None:
        """Terminate all running processes (foreground + background)."""
        self._executor.interrupt()
        for svc_id, (proc, _svc) in list(self._background_procs.items()):
            try:
                proc.terminate()
            except ProcessLookupError:
                pass

    def _conditions_met(self, svc: ServiceConfig) -> bool:
        """Check service conditions (env vars, file existence)."""
        if svc.condition is None:
            return True

        # env_not_equals: { "VAR": "value" } -> skip if VAR == value
        env_ne = svc.condition.get("env_not_equals")
        if env_ne:
            import os
            for var, val in env_ne.items():
                if os.environ.get(var) == val:
                    return False

        # file_exists: path -> skip if file doesn't exist
        file_exists = svc.condition.get("file_exists")
        if file_exists:
            import os
            ralph_dir = os.environ.get("RALPH_DIR", "")
            path = os.path.join(ralph_dir, file_exists) if not os.path.isabs(file_exists) else file_exists
            if not os.path.exists(path):
                return False

        return True
