"""Logging bridge — emit logs in the same format as bash logger.sh.

Format: [YYYY-MM-DD HH:MM:SS] LEVEL: message
Writes to both stderr and LOG_FILE (if set).
"""

from __future__ import annotations

import os
import sys
import time


# Map bash LOG_LEVEL names to numeric severity
_LEVEL_VALUES = {
    "TRACE": 0,
    "DEBUG": 1,
    "INFO": 2,
    "WARN": 3,
    "ERROR": 4,
}

_min_level: int = 2  # INFO by default
_log_file: str | None = None


def init(log_level: str | None = None, log_file: str | None = None) -> None:
    """Initialize logging from env or explicit args."""
    global _min_level, _log_file

    level = log_level or os.environ.get("LOG_LEVEL", "INFO")
    if os.environ.get("DEBUG") == "1" and level not in ("TRACE", "DEBUG"):
        level = "DEBUG"
    _min_level = _LEVEL_VALUES.get(level.upper(), 2)
    _log_file = log_file or os.environ.get("LOG_FILE")


def _format(level: str, msg: str) -> str:
    ts = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime())
    return f"[{ts}] {level}: {msg}"


def _emit(level: str, msg: str) -> None:
    level_val = _LEVEL_VALUES.get(level, 2)
    if level_val < _min_level:
        return
    line = _format(level, msg)
    # INFO goes to stdout, others to stderr (matching bash logger)
    stream = sys.stdout if level == "INFO" else sys.stderr
    print(line, file=stream, flush=True)
    if _log_file:
        try:
            with open(_log_file, "a") as f:
                f.write(line + "\n")
        except OSError:
            pass


def log(msg: str) -> None:
    _emit("INFO", msg)


def log_debug(msg: str) -> None:
    _emit("DEBUG", msg)


def log_warn(msg: str) -> None:
    _emit("WARN", msg)


def log_error(msg: str) -> None:
    _emit("ERROR", msg)


def log_trace(msg: str) -> None:
    _emit("TRACE", msg)
