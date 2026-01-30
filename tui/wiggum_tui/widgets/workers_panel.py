"""Workers panel widget with DataTable."""

import time
from pathlib import Path
from datetime import datetime
from textual.app import ComposeResult
from textual.widgets import DataTable, Static
from textual.widget import Widget
from textual.binding import Binding
from textual.message import Message

from ..data.worker_scanner import scan_workers, get_worker_counts
from ..data.models import Worker, WorkerStatus
from ..actions.worker_control import stop_worker, kill_worker


def format_duration(seconds: int) -> str:
    """Format duration in human-readable format.

    Args:
        seconds: Duration in seconds.

    Returns:
        Formatted string like "2h 15m" or "45m 30s" or "10s".
    """
    if seconds < 0:
        return "-"
    hours, remainder = divmod(seconds, 3600)
    minutes, secs = divmod(remainder, 60)
    if hours > 0:
        return f"{hours}h {minutes}m"
    elif minutes > 0:
        return f"{minutes}m {secs}s"
    else:
        return f"{secs}s"


class WorkersPanel(Widget):
    """Workers panel showing all workers in a table."""

    DEFAULT_CSS = """
    WorkersPanel {
        height: 1fr;
        width: 100%;
        layout: vertical;
    }

    WorkersPanel .workers-header {
        height: 1;
        background: #181825;
        padding: 0 1;
    }

    WorkersPanel DataTable {
        height: 1fr;
    }

    WorkersPanel .empty-message {
        text-align: center;
        color: #7f849c;
        padding: 2;
    }
    """

    BINDINGS = [
        Binding("s", "stop_worker", "Stop"),
        Binding("K", "kill_worker", "Kill"),  # Uppercase to avoid conflict with vim k
        Binding("c", "view_conversation", "View Chat"),
        Binding("L", "view_logs", "View Logs"),  # Uppercase to avoid conflict with vim l
        # Vim-style navigation
        Binding("j", "cursor_down", "Down", show=False),
        Binding("k", "cursor_up", "Up", show=False),
        Binding("g", "goto_top", "Top", show=False),
        Binding("G", "goto_bottom", "Bottom", show=False),
        Binding("ctrl+d", "half_page_down", "Half Page Down", show=False),
        Binding("ctrl+u", "half_page_up", "Half Page Up", show=False),
    ]

    class WorkerSelected(Message):
        """Message sent when a worker is selected."""

        def __init__(self, worker: Worker) -> None:
            super().__init__()
            self.worker = worker

    def __init__(self, ralph_dir: Path) -> None:
        super().__init__()
        self.ralph_dir = ralph_dir
        self._workers_list: list[Worker] = []
        self._selected_worker: Worker | None = None
        self._last_data_hash: str = ""

    def _compute_data_hash(self, workers: list[Worker]) -> str:
        """Compute a hash of worker data for change detection."""
        data = [
            (
                w.id, w.task_id, w.status.value, w.pid, w.pr_url,
                (w.pipeline_info.pipeline_name, w.pipeline_info.step_id, w.pipeline_info.agent)
                if w.pipeline_info else None,
            )
            for w in workers
        ]
        return str(data)

    def compose(self) -> ComposeResult:
        self._load_workers()
        counts = get_worker_counts(self._workers_list)

        yield Static(
            f"[bold]Workers[/] │ "
            f"[#a6e3a1]Running: {counts['running']}[/] │ "
            f"[#89b4fa]Completed: {counts['completed']}[/] │ "
            f"[#f38ba8]Failed: {counts['failed']}[/] │ "
            f"Total: {counts['total']}",
            classes="workers-header",
        )

        if not self._workers_list:
            yield Static(
                "No workers found. Run 'wiggum run' to start workers.",
                classes="empty-message",
            )
            return

        table = DataTable(id="workers-table")
        table.cursor_type = "row"
        table.zebra_stripes = True
        yield table

    def on_mount(self) -> None:
        """Set up the data table."""
        if not self._workers_list:
            return
        try:
            table = self.query_one("#workers-table", DataTable)
            table.add_columns("Status", "Worker ID", "Task", "PID", "Pipeline", "Step", "Agent", "Duration", "PR URL")
            self._populate_table(table)
        except Exception as e:
            self.log.error(f"Failed to populate workers table: {e}")

    def _load_workers(self) -> None:
        """Load workers from .ralph/workers directory."""
        # Use shared worker service if available, otherwise fall back to direct scan
        try:
            self._workers_list = self.app.worker_service.get_workers()
        except AttributeError:
            self._workers_list = scan_workers(self.ralph_dir)

    def _populate_table(self, table: DataTable, preserve_cursor: bool = False) -> None:
        """Populate the table with worker data."""
        # Save cursor position by worker ID before clearing
        cursor_worker_id = None
        if preserve_cursor and table.cursor_row is not None:
            try:
                row_key = table.get_row_at(table.cursor_row)
                cursor_worker_id = str(row_key) if row_key else None
            except Exception:
                pass

        table.clear()
        now_ts = int(time.time())
        for worker in self._workers_list:
            status_style = self._get_status_style(worker.status)
            status_text = f"[{status_style}]{worker.status.value.upper()}[/]"

            # Format duration from start timestamp
            try:
                duration_secs = now_ts - worker.timestamp
                duration = format_duration(duration_secs)
            except (ValueError, OSError):
                duration = "-"

            # Format PID
            pid_str = str(worker.pid) if worker.pid else "-"

            # Truncate worker ID and PR URL for display
            worker_id = worker.id
            if len(worker_id) > 25:
                worker_id = worker_id[:22] + "..."

            pr_url = worker.pr_url or ""
            if len(pr_url) > 30:
                pr_url = pr_url[:27] + "..."

            # Pipeline info columns
            pi = worker.pipeline_info
            pipeline_name = pi.pipeline_name if pi else ""
            step_id = pi.step_id if pi else ""
            agent_short = pi.agent_short if pi else ""

            table.add_row(
                status_text,
                worker_id,
                worker.task_id,
                pid_str,
                pipeline_name,
                step_id,
                agent_short,
                duration,
                pr_url,
                key=worker.id,
            )

        # Restore cursor position by worker ID
        if cursor_worker_id:
            for i, worker in enumerate(self._workers_list):
                if worker.id == cursor_worker_id:
                    table.move_cursor(row=i)
                    break

    def _get_status_style(self, status: WorkerStatus) -> str:
        """Get Rich style for a status."""
        return {
            WorkerStatus.RUNNING: "#a6e3a1",
            WorkerStatus.STOPPED: "#7f849c",
            WorkerStatus.COMPLETED: "#89b4fa",
            WorkerStatus.FAILED: "#f38ba8",
        }.get(status, "#7f849c")

    def _get_selected_worker(self) -> Worker | None:
        """Get the currently selected worker."""
        try:
            table = self.query_one("#workers-table", DataTable)
            if table.cursor_row is not None and table.cursor_row < len(self._workers_list):
                return self._workers_list[table.cursor_row]
        except Exception:
            pass
        return None

    def action_stop_worker(self) -> None:
        """Stop the selected worker."""
        worker = self._get_selected_worker()
        if not worker:
            self.app.notify("No worker selected", severity="warning")
            return

        if worker.status != WorkerStatus.RUNNING:
            self.app.notify("Worker is not running", severity="warning")
            return

        if stop_worker(worker.id):
            self.app.notify(f"Stopping {worker.id}")
            self.refresh_data()
        else:
            self.app.notify(f"Failed to stop {worker.id}", severity="error")

    def action_kill_worker(self) -> None:
        """Kill the selected worker."""
        worker = self._get_selected_worker()
        if not worker:
            self.app.notify("No worker selected", severity="warning")
            return

        if worker.status != WorkerStatus.RUNNING:
            self.app.notify("Worker is not running", severity="warning")
            return

        if kill_worker(worker.id):
            self.app.notify(f"Killed {worker.id}")
            self.refresh_data()
        else:
            self.app.notify(f"Failed to kill {worker.id}", severity="error")

    def action_view_conversation(self) -> None:
        """View conversation for selected worker."""
        worker = self._get_selected_worker()
        if worker:
            # Switch to conversations tab and select this worker
            self.app.action_switch_tab("conversations")
            self.post_message(self.WorkerSelected(worker))

    def action_view_logs(self) -> None:
        """View logs for selected worker."""
        worker = self._get_selected_worker()
        if worker:
            self.app.action_switch_tab("logs")
            # Could emit a message to switch log source

    def action_cursor_down(self) -> None:
        """Move cursor down (vim j)."""
        try:
            table = self.query_one("#workers-table", DataTable)
            table.action_cursor_down()
        except Exception:
            pass

    def action_cursor_up(self) -> None:
        """Move cursor up (vim k)."""
        try:
            table = self.query_one("#workers-table", DataTable)
            table.action_cursor_up()
        except Exception:
            pass

    def action_goto_top(self) -> None:
        """Go to first row (vim gg)."""
        try:
            table = self.query_one("#workers-table", DataTable)
            table.move_cursor(row=0)
        except Exception:
            pass

    def action_goto_bottom(self) -> None:
        """Go to last row (vim G)."""
        try:
            table = self.query_one("#workers-table", DataTable)
            if self._workers_list:
                table.move_cursor(row=len(self._workers_list) - 1)
        except Exception:
            pass

    def action_half_page_down(self) -> None:
        """Move half page down (vim ctrl+d)."""
        try:
            table = self.query_one("#workers-table", DataTable)
            current = table.cursor_row or 0
            new_row = min(current + 10, len(self._workers_list) - 1)
            table.move_cursor(row=new_row)
        except Exception:
            pass

    def action_half_page_up(self) -> None:
        """Move half page up (vim ctrl+u)."""
        try:
            table = self.query_one("#workers-table", DataTable)
            current = table.cursor_row or 0
            new_row = max(current - 10, 0)
            table.move_cursor(row=new_row)
        except Exception:
            pass

    def refresh_data(self) -> None:
        """Refresh worker data and re-render."""
        self._load_workers()

        # Check if worker state (not duration) actually changed
        new_hash = self._compute_data_hash(self._workers_list)
        state_changed = new_hash != self._last_data_hash
        if state_changed:
            self._last_data_hash = new_hash

        # Update header only when worker state changes (not duration)
        if state_changed:
            try:
                counts = get_worker_counts(self._workers_list)
                header = self.query_one(".workers-header", Static)
                header.update(
                    f"[bold]Workers[/] │ "
                    f"[#a6e3a1]Running: {counts['running']}[/] │ "
                    f"[#89b4fa]Completed: {counts['completed']}[/] │ "
                    f"[#f38ba8]Failed: {counts['failed']}[/] │ "
                    f"Total: {counts['total']}"
                )
            except Exception:
                pass

        # Update table while preserving cursor position
        try:
            table = self.query_one("#workers-table", DataTable)
            self._populate_table(table, preserve_cursor=True)
        except Exception:
            pass
