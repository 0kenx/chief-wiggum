"""Tests for logging_bridge.py — log format and level filtering."""

import os
import tempfile

from wiggum_orchestrator import logging_bridge


def test_format():
    line = logging_bridge._format("INFO", "test message")
    assert "] INFO: test message" in line
    assert line.startswith("[")


def test_level_filtering():
    logging_bridge.init(log_level="WARN")
    # After setting WARN, INFO and DEBUG should be suppressed
    assert logging_bridge._min_level == 3  # WARN = 3

    logging_bridge.init(log_level="DEBUG")
    assert logging_bridge._min_level == 1  # DEBUG = 1

    logging_bridge.init(log_level="INFO")
    assert logging_bridge._min_level == 2  # INFO = 2


def test_file_logging(tmp_path):
    log_file = str(tmp_path / "test.log")
    logging_bridge.init(log_level="INFO", log_file=log_file)
    logging_bridge.log("file test message")

    with open(log_file) as f:
        content = f.read()
    assert "file test message" in content
    assert "INFO" in content


def test_debug_env_override():
    old_debug = os.environ.get("DEBUG")
    try:
        os.environ["DEBUG"] = "1"
        logging_bridge.init(log_level="INFO")
        assert logging_bridge._min_level == 1  # Should be DEBUG
    finally:
        if old_debug is not None:
            os.environ["DEBUG"] = old_debug
        else:
            os.environ.pop("DEBUG", None)
        # Reset
        logging_bridge.init(log_level="INFO")
