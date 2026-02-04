"""Tests for service_state.py — state persistence and lifecycle marks."""

import json
import os
import time

import pytest

from wiggum_orchestrator.service_state import ServiceState


@pytest.fixture()
def state(tmp_path):
    return ServiceState(str(tmp_path))


def test_get_creates_entry(state):
    entry = state.get("test-svc")
    assert entry.status == "stopped"
    assert entry.last_run == 0.0
    assert entry.run_count == 0


def test_mark_started(state):
    state.mark_started("test-svc", pid=12345)
    entry = state.get("test-svc")
    assert entry.status == "running"
    assert entry.pid == 12345
    assert entry.run_count == 1
    assert entry.last_run > 0


def test_mark_completed(state):
    state.mark_started("test-svc")
    state.mark_completed("test-svc")
    entry = state.get("test-svc")
    assert entry.status == "stopped"
    assert entry.fail_count == 0
    assert entry.pid is None
    assert entry.success_count == 1
    assert entry.last_success > 0


def test_mark_failed(state):
    state.mark_started("test-svc")
    state.mark_failed("test-svc")
    entry = state.get("test-svc")
    assert entry.status == "failed"
    assert entry.fail_count == 1
    assert entry.pid is None


def test_mark_failed_increments(state):
    state.mark_failed("test-svc")
    state.mark_failed("test-svc")
    state.mark_failed("test-svc")
    assert state.get("test-svc").fail_count == 3


def test_mark_completed_resets_circuit(state):
    entry = state.get("test-svc")
    entry.circuit_state = "open"
    entry.half_open_attempts = 3
    state.mark_completed("test-svc")
    assert entry.circuit_state == "closed"
    assert entry.half_open_attempts == 0


def test_backoff(state):
    state.set_backoff("test-svc", 10.0)
    assert state.is_in_backoff("test-svc") is True

    state.get("test-svc").backoff_until = time.time() - 1
    assert state.is_in_backoff("test-svc") is False


def test_record_execution(state):
    state.record_execution("test-svc", 150, 0)
    entry = state.get("test-svc")
    assert entry.last_duration_ms == 150
    assert entry.total_duration_ms == 150
    assert entry.min_duration_ms == 150
    assert entry.max_duration_ms == 150

    state.record_execution("test-svc", 50, 0)
    assert entry.min_duration_ms == 50
    assert entry.max_duration_ms == 150
    assert entry.total_duration_ms == 200


def test_save_and_restore(state, tmp_path):
    state.mark_started("svc-a", pid=99999)
    state.mark_completed("svc-a")
    state.mark_started("svc-b")
    state.mark_failed("svc-b")
    state.get("svc-b").circuit_state = "open"
    state.get("svc-b").circuit_opened_at = time.time()
    state.record_execution("svc-a", 100, 0)
    state.save()

    # Restore into new instance
    state2 = ServiceState(str(tmp_path))
    assert state2.restore() is True

    a = state2.get("svc-a")
    assert a.run_count == 1
    assert a.success_count == 1
    assert a.total_duration_ms == 100
    assert a.status == "stopped"  # was completed, pid gone

    b = state2.get("svc-b")
    assert b.fail_count == 1
    assert b.circuit_state == "open"


def test_save_json_format(state, tmp_path):
    """Verify JSON schema matches bash service-state.sh format."""
    state.mark_started("test-svc")
    state.mark_completed("test-svc")
    state.save()

    state_file = tmp_path / "services" / "state.json"
    assert state_file.exists()

    data = json.loads(state_file.read_text())
    assert data["version"] == "1.0"
    assert "saved_at" in data
    assert "services" in data

    svc = data["services"]["test-svc"]
    assert "last_run" in svc
    assert "status" in svc
    assert "run_count" in svc
    assert "fail_count" in svc
    assert "pid" in svc
    assert "circuit" in svc
    assert svc["circuit"]["state"] == "closed"
    assert "metrics" in svc
    assert "queue" in svc
    assert "backoff_until" in svc
    assert "retry_count" in svc
    assert "last_success" in svc


def test_save_if_dirty(state):
    """save_if_dirty should only write when dirty."""
    state.mark_started("test-svc")
    state.save_if_dirty()
    assert state._dirty is False

    # Not dirty now — save_if_dirty should be a no-op
    state.save_if_dirty()


def test_is_running_dead_pid(state):
    """is_running should detect dead PIDs and reset status."""
    state.mark_started("test-svc", pid=999999999)  # unlikely to exist
    assert state.is_running("test-svc") is False
    assert state.get("test-svc").status == "stopped"
