"""Circuit breaker state machine: closed -> open -> half-open -> closed.

Operates on ServiceEntry instances from service_state.py. No subprocesses.
"""

from __future__ import annotations

import time

from wiggum_orchestrator.config import ServiceConfig
from wiggum_orchestrator.service_state import ServiceState


class CircuitBreaker:
    """Manages circuit breaker logic for all services."""

    def __init__(self, state: ServiceState) -> None:
        self._state = state

    def blocks(self, svc: ServiceConfig) -> bool:
        """Return True if the circuit breaker prevents execution."""
        if not svc.cb_enabled:
            return False

        entry = self._state.get(svc.id)
        now = time.time()

        if entry.circuit_state == "closed":
            return False

        if entry.circuit_state == "open":
            if now - entry.circuit_opened_at >= svc.cb_cooldown:
                entry.circuit_state = "half-open"
                entry.half_open_attempts = 0
                return False  # allow test request
            return True  # still cooling down

        if entry.circuit_state == "half-open":
            half_open_max = svc.circuit_breaker.get("half_open_requests", 1) if svc.circuit_breaker else 1
            if entry.half_open_attempts < half_open_max:
                entry.half_open_attempts += 1
                return False  # allow test request
            return True  # block additional

        return False

    def record_failure(self, svc: ServiceConfig) -> None:
        """Update circuit breaker after a service failure."""
        if not svc.cb_enabled:
            return

        entry = self._state.get(svc.id)

        if entry.circuit_state == "half-open":
            entry.circuit_state = "open"
            entry.circuit_opened_at = time.time()
        elif entry.fail_count >= svc.cb_threshold:
            entry.circuit_state = "open"
            entry.circuit_opened_at = time.time()

    def record_success(self, svc: ServiceConfig) -> None:
        """Reset circuit breaker after a service success."""
        if not svc.cb_enabled:
            return
        entry = self._state.get(svc.id)
        if entry.circuit_state != "closed":
            entry.circuit_state = "closed"
            entry.half_open_attempts = 0
