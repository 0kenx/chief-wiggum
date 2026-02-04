"""Service executor — call bash bridge from Python.

Runs bash functions/commands via the bash-bridge.sh script. Two modes:

- Phase mode: all functions in a phase run in one bash process (shared state).
- Function mode: individual service runs in its own subprocess.
"""

from __future__ import annotations

import os
import subprocess

from wiggum_orchestrator import logging_bridge as log
from wiggum_orchestrator.config import ServiceConfig


class ServiceExecutor:
    """Execute bash services via the bridge script."""

    def __init__(
        self,
        wiggum_home: str,
        ralph_dir: str,
        project_dir: str,
        env_overrides: dict[str, str] | None = None,
    ) -> None:
        self._bridge = os.path.join(
            wiggum_home, "lib", "orchestrator-py", "bash-bridge.sh",
        )
        self._env = self._build_env(wiggum_home, ralph_dir, project_dir,
                                     env_overrides)

    @staticmethod
    def _build_env(
        wiggum_home: str,
        ralph_dir: str,
        project_dir: str,
        overrides: dict[str, str] | None,
    ) -> dict[str, str]:
        """Build environment dict with all globals the bridge needs."""
        env = os.environ.copy()
        env["WIGGUM_HOME"] = wiggum_home
        env["PROJECT_DIR"] = project_dir
        env["RALPH_DIR"] = ralph_dir
        if overrides:
            env.update(overrides)
        return env

    def run_phase(self, phase: str, functions: list[str]) -> bool:
        """Run all phase functions in a single bash process.

        Args:
            phase: Phase name (for logging).
            functions: List of svc_* function names to call in order.

        Returns:
            True if all succeeded, False on any failure.
        """
        if not functions:
            return True

        cmd = ["bash", self._bridge, "phase", phase] + functions
        log.log_debug(f"Bridge phase {phase}: {' '.join(functions)}")

        result = subprocess.run(
            cmd,
            env=self._env,
            cwd=self._env.get("PROJECT_DIR"),
            capture_output=False,
            timeout=600,
        )
        if result.returncode != 0:
            log.log_error(
                f"Bridge phase {phase} failed (exit {result.returncode})",
            )
            return False
        return True

    def run_function(
        self,
        svc: ServiceConfig,
        extra_args: list[str] | None = None,
    ) -> int:
        """Run a single svc_* function via the bridge.

        Args:
            svc: Service config with execution.function.
            extra_args: Additional arguments to pass.

        Returns:
            Exit code from the subprocess.
        """
        func = svc.exec_function
        if not func:
            log.log_error(f"Service {svc.id} has no function defined")
            return 1

        cmd = ["bash", self._bridge, "function", func]
        if extra_args:
            cmd.extend(extra_args)

        log.log_debug(f"Bridge function: {func}")
        result = subprocess.run(
            cmd,
            env=self._env,
            cwd=self._env.get("PROJECT_DIR"),
            capture_output=False,
            timeout=svc.timeout or 600,
        )
        return result.returncode

    def run_command(self, svc: ServiceConfig) -> int:
        """Run a command-type service.

        Args:
            svc: Service config with execution.command.

        Returns:
            Exit code.
        """
        cmd_str = svc.exec_command
        if not cmd_str:
            log.log_error(f"Service {svc.id} has no command defined")
            return 1

        log.log_debug(f"Bridge command: {cmd_str}")
        result = subprocess.run(
            ["bash", "-c", cmd_str],
            env=self._env,
            cwd=self._env.get("PROJECT_DIR"),
            capture_output=False,
            timeout=svc.timeout or 600,
        )
        return result.returncode

    def run_function_background(
        self,
        svc: ServiceConfig,
        extra_args: list[str] | None = None,
    ) -> subprocess.Popen:
        """Run a single svc_* function in background.

        Returns:
            Popen handle for the background process.
        """
        func = svc.exec_function
        cmd = ["bash", self._bridge, "function", func]
        if extra_args:
            cmd.extend(extra_args)

        log.log_debug(f"Bridge background: {func}")
        proc = subprocess.Popen(
            cmd,
            env=self._env,
            cwd=self._env.get("PROJECT_DIR"),
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        return proc
