"""Tests for worker_pool.py — PID tracking and persistence."""

import json
import os

import pytest

from wiggum_orchestrator.worker_pool import WorkerPool


@pytest.fixture()
def pool(tmp_path):
    ralph_dir = str(tmp_path)
    os.makedirs(os.path.join(ralph_dir, "orchestrator"), exist_ok=True)
    return WorkerPool(ralph_dir)


def test_add_and_count(pool):
    pool.add(100, "main", "TASK-001")
    pool.add(200, "fix", "TASK-002")
    pool.add(300, "main", "TASK-003")

    assert pool.count() == 3
    assert pool.count("main") == 2
    assert pool.count("fix") == 1
    assert pool.count("resolve") == 0


def test_remove(pool):
    pool.add(100, "main", "TASK-001")
    entry = pool.remove(100)
    assert entry is not None
    assert entry.task_id == "TASK-001"
    assert pool.count() == 0


def test_remove_nonexistent(pool):
    assert pool.remove(999) is None


def test_get_by_type(pool):
    pool.add(100, "main", "TASK-001")
    pool.add(200, "fix", "TASK-002")
    pool.add(300, "main", "TASK-003")

    main_workers = pool.get_by_type("main")
    assert len(main_workers) == 2

    fix_workers = pool.get_by_type("fix")
    assert len(fix_workers) == 1
    assert fix_workers[0].task_id == "TASK-002"


def test_cleanup_finished(pool):
    # Use PIDs that definitely don't exist
    pool.add(999999991, "main", "TASK-001")
    pool.add(999999992, "fix", "TASK-002")

    completed = []
    pool.cleanup_finished(on_complete=lambda e: completed.append(e))

    assert len(completed) == 2
    assert pool.count() == 0


def test_cleanup_preserves_running(pool):
    # Use our own PID (guaranteed to be running)
    our_pid = os.getpid()
    pool.add(our_pid, "main", "TASK-001")
    pool.add(999999991, "fix", "TASK-002")  # dead

    completed = pool.cleanup_finished()
    assert len(completed) == 1
    assert completed[0].task_id == "TASK-002"
    assert pool.count() == 1  # our PID still tracked


def test_save_and_restore(pool, tmp_path):
    pool.add(os.getpid(), "main", "TASK-001")
    pool.save()

    pool_file = os.path.join(str(tmp_path), "orchestrator", "pool.json")
    assert os.path.isfile(pool_file)

    # Restore into new pool
    pool2 = WorkerPool(str(tmp_path))
    restored = pool2.restore()
    assert restored == 1  # our PID is alive
    assert pool2.count() == 1


def test_restore_skips_dead_pids(pool, tmp_path):
    pool.add(999999991, "main", "TASK-001")
    pool.save()

    pool2 = WorkerPool(str(tmp_path))
    restored = pool2.restore()
    assert restored == 0
    assert pool2.count() == 0


def test_all_pids(pool):
    pool.add(100, "main", "TASK-001")
    pool.add(200, "fix", "TASK-002")
    pids = pool.all_pids()
    assert set(pids) == {100, 200}
