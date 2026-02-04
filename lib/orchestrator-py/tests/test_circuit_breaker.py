"""Tests for circuit_breaker.py — closed/open/half-open state machine."""

import time

import pytest

from wiggum_orchestrator.circuit_breaker import CircuitBreaker
from wiggum_orchestrator.config import ServiceConfig
from wiggum_orchestrator.service_state import ServiceState


@pytest.fixture()
def state(tmp_path):
    return ServiceState(str(tmp_path))


@pytest.fixture()
def cb(state):
    return CircuitBreaker(state)


def _make_svc(cb_enabled=True, threshold=3, cooldown=300):
    return ServiceConfig(
        id="test-svc",
        circuit_breaker={
            "enabled": cb_enabled,
            "threshold": threshold,
            "cooldown": cooldown,
        } if cb_enabled else None,
    )


def test_closed_allows(cb, state):
    svc = _make_svc()
    assert cb.blocks(svc) is False


def test_disabled_allows(cb, state):
    svc = _make_svc(cb_enabled=False)
    state.get("test-svc").circuit_state = "open"
    assert cb.blocks(svc) is False


def test_open_blocks(cb, state):
    svc = _make_svc(cooldown=300)
    entry = state.get("test-svc")
    entry.circuit_state = "open"
    entry.circuit_opened_at = time.time()
    assert cb.blocks(svc) is True


def test_open_to_half_open_after_cooldown(cb, state):
    svc = _make_svc(cooldown=1)
    entry = state.get("test-svc")
    entry.circuit_state = "open"
    entry.circuit_opened_at = time.time() - 2  # expired
    assert cb.blocks(svc) is False
    assert entry.circuit_state == "half-open"


def test_half_open_allows_limited(cb, state):
    svc = _make_svc()
    entry = state.get("test-svc")
    entry.circuit_state = "half-open"
    entry.half_open_attempts = 0

    # First request allowed
    assert cb.blocks(svc) is False
    assert entry.half_open_attempts == 1

    # Second request blocked (default max is 1)
    assert cb.blocks(svc) is True


def test_record_failure_opens_circuit(cb, state):
    svc = _make_svc(threshold=3)
    entry = state.get("test-svc")
    entry.fail_count = 3
    cb.record_failure(svc)
    assert entry.circuit_state == "open"


def test_record_failure_half_open_reopens(cb, state):
    svc = _make_svc()
    entry = state.get("test-svc")
    entry.circuit_state = "half-open"
    cb.record_failure(svc)
    assert entry.circuit_state == "open"


def test_record_success_closes(cb, state):
    svc = _make_svc()
    entry = state.get("test-svc")
    entry.circuit_state = "open"
    cb.record_success(svc)
    assert entry.circuit_state == "closed"
    assert entry.half_open_attempts == 0
