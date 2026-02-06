"""Service executor — call bash bridge from Python.

Runs bash functions/commands via the bash-bridge.sh script. Two modes:

- Phase mode: all functions in a phase run in one bash process (shared state).
- Function mode: individual service runs in its own subprocess.
"""

from __future__ import annotations

import os
import subprocess
import threading

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
        self._proc_lock = threading.Lock()
        self._current_proc: subprocess.Popen | None = None

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
        # Ensure $WIGGUM_HOME/bin is on PATH so command-type services
        # (e.g. pr-sync running "wiggum-pr sync") can find CLI tools.
        bin_dir = os.path.join(wiggum_home, "bin")
        path = env.get("PATH", "")
        if bin_dir not in path.split(os.pathsep):
            env["PATH"] = bin_dir + os.pathsep + path if path else bin_dir
        if overrides:
            env.update(overrides)
        return env

    def interrupt(self) -> None:
        """Terminate the currently running foreground subprocess, if any."""
        with self._proc_lock:
            proc = self._current_proc
        if proc is not None:
            try:
                proc.terminate()
            except ProcessLookupError:
                pass

    def run_phase(self, phase: str, functions: list[str]) -> bool:
        """Run all phase functions in a single bash process.

        Args:
            phase: Phase name (for logging).
            functions: List of svc_* function names to call in order.

        Returns:
            True if all succeeded, False on any failure or timeout.
        """
        if not functions:
            return True

        cmd = ["bash", self._bridge, "phase", phase] + functions
        log.log_debug(f"Bridge phase {phase}: {' '.join(functions)}")

        proc = subprocess.Popen(
            cmd,
            env=self._env,
            cwd=self._env.get("PROJECT_DIR"),
        )
        with self._proc_lock:
            self._current_proc = proc
        try:
            proc.wait(timeout=600)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait()
            log.log_error(f"Bridge phase {phase} timed out after 600s")
            return False
        finally:
            with self._proc_lock:
                self._current_proc = None
        if proc.returncode != 0:
            log.log_error(
                f"Bridge phase {phase} failed (exit {proc.returncode})",
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
            Exit code from the subprocess (124 on timeout, like GNU timeout).
        """
        func = svc.exec_function
        if not func:
            log.log_error(f"Service {svc.id} has no function defined")
            return 1

        cmd = ["bash", self._bridge, "function", func]
        if extra_args:
            cmd.extend(extra_args)

        log.log_debug(f"Bridge function: {func}")
        timeout = svc.timeout or 600
        proc = subprocess.Popen(
            cmd,
            env=self._env,
            cwd=self._env.get("PROJECT_DIR"),
        )
        with self._proc_lock:
            self._current_proc = proc
        try:
            proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait()
            log.log_warn(f"Service {svc.id} timed out after {timeout}s")
            return 124  # GNU timeout exit code
        finally:
            with self._proc_lock:
                self._current_proc = None
        return proc.returncode

    def run_command(self, svc: ServiceConfig) -> int:
        """Run a command-type service.

        Args:
            svc: Service config with execution.command.

        Returns:
            Exit code (124 on timeout, like GNU timeout).
        """
        cmd_str = svc.exec_command
        if not cmd_str:
            log.log_error(f"Service {svc.id} has no command defined")
            return 1

        log.log_debug(f"Bridge command: {cmd_str}")
        timeout = svc.timeout or 600
        proc = subprocess.Popen(
            ["bash", "-c", cmd_str],
            env=self._env,
            cwd=self._env.get("PROJECT_DIR"),
        )
        with self._proc_lock:
            self._current_proc = proc
        try:
            proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait()
            log.log_warn(f"Service {svc.id} timed out after {timeout}s")
            return 124  # GNU timeout exit code
        finally:
            with self._proc_lock:
                self._current_proc = None
        return proc.returncode

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

    def run_command_background(self, svc: ServiceConfig) -> subprocess.Popen:
        """Run a command-type service in background.

        Returns:
            Popen handle for the background process.
        """
        cmd_str = svc.exec_command
        log.log_debug(f"Command background: {cmd_str}")
        proc = subprocess.Popen(
            ["bash", "-c", cmd_str],
            env=self._env,
            cwd=self._env.get("PROJECT_DIR"),
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        return proc
