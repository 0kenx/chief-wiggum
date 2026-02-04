"""Tests for config.py — service config loading and registry."""

import json
import os
import tempfile

import pytest

from wiggum_orchestrator.config import (
    ServiceConfig,
    ServiceRegistry,
    apply_run_mode_filters,
    load_services,
)


@pytest.fixture()
def services_json(tmp_path):
    """Create a minimal services.json for testing."""
    config = {
        "version": "2.0",
        "defaults": {
            "timeout": 300,
            "restart_policy": {"on_failure": "skip", "max_retries": 2},
        },
        "services": [
            {
                "id": "validate-kanban",
                "description": "Validate kanban",
                "phase": "startup",
                "order": 10,
                "required": True,
                "schedule": {"type": "tick"},
                "execution": {"type": "function", "function": "svc_orch_validate_kanban"},
            },
            {
                "id": "worker-cleanup",
                "description": "Cleanup workers",
                "phase": "pre",
                "order": 30,
                "schedule": {"type": "tick"},
                "execution": {"type": "function", "function": "svc_orch_worker_cleanup"},
            },
            {
                "id": "github-issue-sync",
                "description": "Sync issues",
                "phase": "periodic",
                "order": 5,
                "schedule": {"type": "interval", "interval": 120, "jitter": 15, "run_on_startup": True},
                "execution": {"type": "function", "function": "svc_orch_github_issue_sync"},
                "concurrency": {"max_instances": 1, "if_running": "skip"},
                "circuit_breaker": {"enabled": True, "threshold": 3, "cooldown": 300},
            },
            {
                "id": "fix-workers",
                "description": "Spawn fix workers",
                "phase": "periodic",
                "order": 60,
                "schedule": {"type": "interval", "interval": 60, "run_on_startup": True},
                "execution": {"type": "function", "function": "svc_orch_spawn_fix_workers"},
                "condition": {"env_not_equals": {"WIGGUM_RUN_MODE": "merge-only"}},
            },
            {
                "id": "task-spawner",
                "description": "Spawn tasks",
                "phase": "post",
                "order": 45,
                "schedule": {"type": "tick"},
                "execution": {"type": "function", "function": "svc_orch_task_spawner"},
            },
            {
                "id": "state-save",
                "description": "Save state",
                "phase": "shutdown",
                "order": 10,
                "schedule": {"type": "tick"},
                "execution": {"type": "function", "function": "svc_orch_state_save"},
            },
        ],
    }
    config_dir = tmp_path / "config"
    config_dir.mkdir()
    config_file = config_dir / "services.json"
    config_file.write_text(json.dumps(config))
    return tmp_path


def test_load_services(services_json):
    """Loading services.json should parse all entries."""
    wiggum_home = str(services_json)
    ralph_dir = str(services_json / "ralph")
    os.makedirs(ralph_dir, exist_ok=True)

    services = load_services(wiggum_home, ralph_dir)
    assert len(services) == 6
    assert services[0].id == "validate-kanban"


def test_service_config_properties():
    """ServiceConfig properties should return correct values."""
    svc = ServiceConfig(
        id="test",
        schedule={"type": "interval", "interval": 120, "jitter": 15, "run_on_startup": True},
        execution={"type": "function", "function": "svc_test"},
        circuit_breaker={"enabled": True, "threshold": 3, "cooldown": 300},
    )
    assert svc.schedule_type == "interval"
    assert svc.interval == 120
    assert svc.jitter == 15
    assert svc.run_on_startup is True
    assert svc.exec_type == "function"
    assert svc.exec_function == "svc_test"
    assert svc.cb_enabled is True
    assert svc.cb_threshold == 3
    assert svc.cb_cooldown == 300


def test_service_registry_phases(services_json):
    wiggum_home = str(services_json)
    ralph_dir = str(services_json / "ralph")
    os.makedirs(ralph_dir, exist_ok=True)

    services = load_services(wiggum_home, ralph_dir)
    registry = ServiceRegistry(services)

    startup = registry.get_phase_services("startup")
    assert len(startup) == 1
    assert startup[0].id == "validate-kanban"

    pre = registry.get_phase_services("pre")
    assert len(pre) == 1

    periodic = registry.get_phase_services("periodic")
    assert len(periodic) == 2

    post = registry.get_phase_services("post")
    assert len(post) == 1

    shutdown = registry.get_phase_services("shutdown")
    assert len(shutdown) == 1


def test_registry_sorted_by_order(services_json):
    """Services within a phase should be sorted by order."""
    wiggum_home = str(services_json)
    ralph_dir = str(services_json / "ralph")
    os.makedirs(ralph_dir, exist_ok=True)

    services = load_services(wiggum_home, ralph_dir)
    registry = ServiceRegistry(services)

    periodic = registry.get_phase_services("periodic")
    orders = [s.order for s in periodic]
    assert orders == sorted(orders)


def test_apply_run_mode_merge_only():
    """merge-only mode should disable fix-workers and multi-pr-planner."""
    services = [
        ServiceConfig(id="fix-workers"),
        ServiceConfig(id="multi-pr-planner"),
        ServiceConfig(id="task-spawner"),
    ]
    apply_run_mode_filters(services, "merge-only", {})
    by_id = {s.id: s for s in services}
    assert by_id["fix-workers"].enabled is False
    assert by_id["multi-pr-planner"].enabled is False
    assert by_id["task-spawner"].enabled is True


def test_apply_run_mode_resume_only():
    """resume-only should disable fix, resolve, planner, orphan."""
    services = [
        ServiceConfig(id="fix-workers"),
        ServiceConfig(id="multi-pr-planner"),
        ServiceConfig(id="resolve-workers"),
        ServiceConfig(id="orphan-workspace"),
        ServiceConfig(id="task-spawner"),
    ]
    apply_run_mode_filters(services, "resume-only", {})
    by_id = {s.id: s for s in services}
    assert by_id["fix-workers"].enabled is False
    assert by_id["multi-pr-planner"].enabled is False
    assert by_id["resolve-workers"].enabled is False
    assert by_id["orphan-workspace"].enabled is False
    assert by_id["task-spawner"].enabled is True


def test_apply_no_flags():
    """--no-* flags should disable respective services."""
    services = [
        ServiceConfig(id="resume-poll"),
        ServiceConfig(id="resume-decide"),
        ServiceConfig(id="github-issue-sync"),
        ServiceConfig(id="github-plan-sync"),
        ServiceConfig(id="pr-sync"),
        ServiceConfig(id="resolve-workers"),
        ServiceConfig(id="fix-workers"),
        ServiceConfig(id="multi-pr-planner"),
    ]
    no_flags = {
        "no_resume": True,
        "no_fix": True,
        "no_merge": True,
        "no_sync": True,
    }
    apply_run_mode_filters(services, "default", no_flags)
    for s in services:
        assert s.enabled is False, f"{s.id} should be disabled"


def test_override_services(services_json):
    """Project overrides should modify service config."""
    ralph_dir = services_json / "ralph"
    ralph_dir.mkdir(exist_ok=True)
    override = {
        "services": [
            {"id": "github-issue-sync", "enabled": False},
        ]
    }
    (ralph_dir / "services.json").write_text(json.dumps(override))

    wiggum_home = str(services_json)
    services = load_services(wiggum_home, str(ralph_dir))
    by_id = {s.id: s for s in services}
    assert by_id["github-issue-sync"].enabled is False
