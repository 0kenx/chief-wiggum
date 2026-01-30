"""Kanban board panel widget."""

import time
from pathlib import Path
from textual.app import ComposeResult
from textual.containers import Horizontal, Vertical, VerticalScroll, Center
from textual.widgets import Static, Button
from textual.widget import Widget
from textual.screen import ModalScreen
from textual.binding import Binding
from textual import events

from ..data.kanban_parser import parse_kanban_with_status, group_tasks_by_status
from ..data.models import Task, TaskStatus
from ..messages import NavigateToTask


def format_duration(start_timestamp: int) -> str:
    """Format duration from start timestamp to now as HH:MM:SS or MM:SS."""
    now = int(time.time())
    elapsed = now - start_timestamp
    if elapsed < 0:
        elapsed = 0

    hours = elapsed // 3600
    minutes = (elapsed % 3600) // 60
    seconds = elapsed % 60

    if hours > 0:
        return f"{hours}:{minutes:02d}:{seconds:02d}"
    else:
        return f"{minutes}:{seconds:02d}"


class TaskDetailModal(ModalScreen[tuple | None]):
    """Modal screen showing task details."""

    DEFAULT_CSS = """
    TaskDetailModal {
        align: center middle;
    }

    TaskDetailModal > Vertical {
        width: 80;
        max-width: 90%;
        height: auto;
        max-height: 80%;
        background: #181825;
        border: solid #cba6f7;
        padding: 1 2;
    }

    TaskDetailModal .modal-title {
        text-align: center;
        text-style: bold;
        color: #cba6f7;
        padding: 0 0 1 0;
    }

    TaskDetailModal .detail-section {
        margin: 1 0 0 0;
    }

    TaskDetailModal .detail-label {
        color: #a6adc8;
        text-style: bold;
    }

    TaskDetailModal .detail-value {
        color: #cdd6f4;
        padding: 0 0 0 2;
    }

    TaskDetailModal .detail-list-item {
        color: #cdd6f4;
        padding: 0 0 0 4;
    }

    TaskDetailModal .status-pending {
        color: #a6adc8;
    }

    TaskDetailModal .status-in_progress {
        color: #fab387;
    }

    TaskDetailModal .status-pending_approval {
        color: #cba6f7;
    }

    TaskDetailModal .status-complete {
        color: #a6e3a1;
    }

    TaskDetailModal .status-not_planned {
        color: #7f849c;
    }

    TaskDetailModal .status-failed {
        color: #f38ba8;
    }

    TaskDetailModal .priority-critical {
        color: #f38ba8;
        text-style: bold;
    }

    TaskDetailModal .priority-high {
        color: #fab387;
    }

    TaskDetailModal .priority-medium {
        color: #89b4fa;
    }

    TaskDetailModal .priority-low {
        color: #7f849c;
    }

    TaskDetailModal Button {
        margin: 1 0 0 0;
        width: 100%;
    }
    """

    BINDINGS = [
        Binding("escape", "close", "Close"),
        Binding("enter", "close", "Close"),
        Binding("q", "close", "Close"),
    ]

    def __init__(self, task: Task, ralph_dir: Path | None = None) -> None:
        super().__init__()
        self._task_info = task
        self._ralph_dir = ralph_dir

    def compose(self) -> ComposeResult:
        task = self._task_info
        status_class = f"status-{task.status.value}"
        priority_class = f"priority-{task.priority.lower()}"

        with Vertical():
            yield Static(f"{task.id}: {task.title}", classes="modal-title")

            # Status and Priority row
            yield Static(
                f"[{status_class}]Status: {task.status.value.upper()}[/]  │  "
                f"[{priority_class}]Priority: {task.priority}[/]",
            )

            # Plan indicator
            if self._ralph_dir:
                plan_path = self._ralph_dir / "plans" / f"{task.id}.md"
                if plan_path.exists():
                    yield Static("[#a6e3a1]Plan: available[/]")

            # Description
            if task.description:
                yield Static("[bold #a6adc8]Description[/]", classes="detail-section")
                yield Static(f"  {task.description}", classes="detail-value")

            # Dependencies
            if task.dependencies:
                yield Static("[bold #a6adc8]Dependencies[/]", classes="detail-section")
                for dep in task.dependencies:
                    yield Static(f"  • {dep}", classes="detail-list-item")

            # Scope
            if task.scope:
                yield Static("[bold #a6adc8]Scope[/]", classes="detail-section")
                for item in task.scope:
                    yield Static(f"  • {item}", classes="detail-list-item")

            # Out of Scope
            if task.out_of_scope:
                yield Static("[bold #a6adc8]Out of Scope[/]", classes="detail-section")
                for item in task.out_of_scope:
                    yield Static(f"  • {item}", classes="detail-list-item")

            # Acceptance Criteria
            if task.acceptance_criteria:
                yield Static("[bold #a6adc8]Acceptance Criteria[/]", classes="detail-section")
                for item in task.acceptance_criteria:
                    yield Static(f"  • {item}", classes="detail-list-item")

            # Navigation buttons
            has_plan = False
            if self._ralph_dir:
                plan_path = self._ralph_dir / "plans" / f"{task.id}.md"
                has_plan = plan_path.exists()

            if has_plan:
                yield Button("View Plan", id="btn-view-plan")
            yield Button("View Conversations", id="btn-view-conversations")
            yield Button("Close [Esc]", variant="primary", id="btn-close")

    def on_button_pressed(self, event: Button.Pressed) -> None:
        button_id = event.button.id
        if button_id == "btn-view-plan":
            self.dismiss((self._task_info.id, "plans"))
        elif button_id == "btn-view-conversations":
            self.dismiss((self._task_info.id, "conversations"))
        else:
            self.dismiss(None)

    def action_close(self) -> None:
        self.dismiss(None)


class TaskCard(Static):
    """A single task card in the kanban board."""

    DEFAULT_CSS = """
    TaskCard {
        background: #181825;
        border: solid #45475a;
        margin: 0;
        padding: 0 0;
        height: auto;
        min-height: 3;
    }

    TaskCard:hover {
        border: solid #cba6f7;
        background: #313244;
    }

    TaskCard:focus {
        border: solid #cba6f7;
    }

    TaskCard .task-id {
        color: #cba6f7;
        text-style: bold;
    }

    TaskCard .task-title {
        color: #cdd6f4;
    }

    TaskCard .task-priority-critical {
        color: #f38ba8;
    }

    TaskCard .task-priority-high {
        color: #fab387;
    }

    TaskCard .task-priority-medium {
        color: #89b4fa;
    }

    TaskCard .task-priority-low {
        color: #7f849c;
    }
    """

    can_focus = True

    def __init__(self, task_data: Task) -> None:
        super().__init__()
        self._task_data = task_data

    def render(self) -> str:
        """Render task card content."""
        priority_indicator = {
            "CRITICAL": "❗",
            "HIGH": "[#f38ba8]▲[/]",
            "MEDIUM": "[#89b4fa]●[/]",
            "LOW": "[#a6e3a1]▽[/]",
        }.get(self._task_data.priority, "")

        title = self._task_data.title
        if len(title) > 30:
            title = title[:27] + "..."

        # Build the first line with priority indicator and task ID
        first_line = f"{priority_indicator} [bold #cba6f7]{self._task_data.id}[/]"

        # For in-progress tasks, show running status indicator, agent info and duration
        if self._task_data.status == TaskStatus.IN_PROGRESS and self._task_data.is_running is not None:
            if self._task_data.is_running:
                pi = self._task_data.pipeline_info
                agent_label = pi.agent_short if pi else ""
                duration = ""
                if self._task_data.start_time:
                    duration = f" {format_duration(self._task_data.start_time)}"
                if agent_label:
                    first_line += f" [bold #a6e3a1]● {agent_label}{duration}[/]"
                else:
                    first_line += f" [bold #a6e3a1]●{duration}[/]"
            else:
                first_line += " [bold #f38ba8]●[/]"

        # For pending approval tasks with a running worker, show agent info with green dot
        if self._task_data.status == TaskStatus.PENDING_APPROVAL and self._task_data.is_running:
            pi = self._task_data.pipeline_info
            agent_label = pi.agent_short if pi else ""
            duration = ""
            if self._task_data.start_time:
                duration = f" {format_duration(self._task_data.start_time)}"
            if agent_label:
                first_line += f" [bold #a6e3a1]● {agent_label}{duration}[/]"
            else:
                first_line += f" [bold #a6e3a1]●{duration}[/]"

        lines = [
            first_line,
            f"[#cdd6f4]{title}[/]",
        ]
        return "\n".join(lines)

    def _handle_modal_result(self, result: tuple | None) -> None:
        """Handle modal dismiss result for cross-tab navigation."""
        if result is not None:
            task_id, target_tab = result
            self.app.post_message(NavigateToTask(task_id, target_tab))

    def on_click(self) -> None:
        """Handle click to show task details."""
        ralph_dir = getattr(self.app, "ralph_dir", None)
        self.app.push_screen(
            TaskDetailModal(self._task_data, ralph_dir=ralph_dir),
            callback=self._handle_modal_result,
        )

    def key_enter(self) -> None:
        """Handle Enter key to show task details."""
        ralph_dir = getattr(self.app, "ralph_dir", None)
        self.app.push_screen(
            TaskDetailModal(self._task_data, ralph_dir=ralph_dir),
            callback=self._handle_modal_result,
        )


class KanbanColumn(Widget):
    """A single column in the kanban board."""

    DEFAULT_CSS = """
    KanbanColumn {
        width: 1fr;
        height: 100%;
        border: solid #45475a;
    }

    KanbanColumn .column-header {
        background: #181825;
        text-align: center;
        text-style: bold;
        height: 1;
        padding: 0 1;
    }

    KanbanColumn .column-header-pending {
        color: #a6adc8;
    }

    KanbanColumn .column-header-in_progress {
        color: #fab387;
    }

    KanbanColumn .column-header-pending_approval {
        color: #cba6f7;
    }

    KanbanColumn .column-header-complete {
        color: #a6e3a1;
    }

    KanbanColumn .column-header-not_planned {
        color: #7f849c;
    }

    KanbanColumn .column-header-failed {
        color: #f38ba8;
    }

    KanbanColumn .column-content {
        padding: 1;
    }
    """

    def __init__(self, status: TaskStatus, tasks_list: list[Task], header_suffix: str = "") -> None:
        super().__init__(id=f"col-{status.value}")
        self._status = status
        self._tasks_list = tasks_list
        self._header_suffix = header_suffix

    COLUMN_EMOJI = {
        TaskStatus.PENDING: "📋",
        TaskStatus.IN_PROGRESS: "⚡",
        TaskStatus.PENDING_APPROVAL: "👀",
        TaskStatus.COMPLETE: "✅",
        TaskStatus.FAILED: "❌",
        TaskStatus.NOT_PLANNED: "🚫",
    }

    def compose(self) -> ComposeResult:
        status_name = self._status.value.replace("_", " ").upper()
        header_class = f"column-header-{self._status.value}"
        emoji = self.COLUMN_EMOJI.get(self._status, "")
        suffix = f" [#7f849c]{self._header_suffix}[/]" if self._header_suffix else ""
        yield Static(
            f"[{header_class}]{emoji} {status_name} ({len(self._tasks_list)}){suffix}[/]",
            classes="column-header",
        )
        with VerticalScroll(classes="column-content"):
            for task_item in self._tasks_list:
                yield TaskCard(task_item)

    def update_tasks(self, tasks: list[Task], header_suffix: str = "") -> None:
        """Update column tasks in-place, minimizing DOM changes."""
        old_task_ids = [t.id for t in self._tasks_list]
        new_task_ids = [t.id for t in tasks]

        self._tasks_list = tasks
        self._header_suffix = header_suffix

        # Update header text
        status_name = self._status.value.replace("_", " ").upper()
        header_class = f"column-header-{self._status.value}"
        emoji = self.COLUMN_EMOJI.get(self._status, "")
        suffix = f" [#7f849c]{self._header_suffix}[/]" if self._header_suffix else ""
        try:
            header = self.query_one(".column-header", Static)
            header.update(
                f"[{header_class}]{emoji} {status_name} ({len(tasks)}){suffix}[/]"
            )
        except Exception:
            pass

        # If same task IDs in same order, update card data in-place (no DOM changes)
        if old_task_ids == new_task_ids:
            try:
                cards = list(self.query(TaskCard))
                for card, task in zip(cards, tasks):
                    card._task_data = task
                    card.refresh()
            except Exception:
                pass
            return

        # Structural change: rebuild cards within the scroll container
        try:
            scroll = self.query_one(VerticalScroll)
            for card in list(scroll.query(TaskCard)):
                card.remove()
            for task in tasks:
                scroll.mount(TaskCard(task))
        except Exception:
            pass


class KanbanPanel(Widget):
    """Kanban board panel showing tasks in columns."""

    DEFAULT_CSS = """
    KanbanPanel {
        height: 1fr;
        width: 100%;
        layout: vertical;
    }

    KanbanPanel .kanban-header {
        height: 1;
        background: #181825;
        padding: 0 1;
    }

    KanbanPanel .kanban-board {
        height: 1fr;
        width: 100%;
    }

    KanbanPanel .empty-message {
        text-align: center;
        color: #7f849c;
        padding: 2;
    }
    """

    PENDING_SORT_MODES = ["default", "priority", "score", "name"]

    BINDINGS = [
        # Vim-style navigation
        Binding("j", "next_card", "Next Card", show=False),
        Binding("k", "prev_card", "Prev Card", show=False),
        Binding("h", "prev_column", "Prev Column", show=False),
        Binding("l", "next_column", "Next Column", show=False),
        Binding("g", "first_card", "First Card", show=False),
        Binding("G", "last_card", "Last Card", show=False),
        Binding("enter", "open_card", "Open Card", show=False),
        Binding("p", "cycle_pending_sort", "Pending Sort", show=True),
    ]

    def __init__(self, ralph_dir: Path) -> None:
        super().__init__()
        self.ralph_dir = ralph_dir
        self.kanban_path = ralph_dir / "kanban.md"
        self._tasks_list: list[Task] = []
        self._timer = None
        self._last_data_hash: str = ""
        self._pending_sort_mode: int = 0  # index into PENDING_SORT_MODES

    def _compute_data_hash(self, tasks: list[Task]) -> str:
        """Compute a hash of task data for change detection."""
        # Include fields that affect display (excluding start_time which changes constantly)
        data = [
            (
                t.id, t.title, t.status.value, t.priority, t.is_running,
                (t.pipeline_info.step_id, t.pipeline_info.agent) if t.pipeline_info else None,
            )
            for t in tasks
        ]
        return str(data)

    def on_mount(self) -> None:
        """Start the timer for updating running task durations."""
        self._timer = self.set_interval(1, self._update_running_cards)

    def on_unmount(self) -> None:
        """Stop the timer when unmounted."""
        if self._timer:
            self._timer.stop()

    def _update_running_cards(self) -> None:
        """Update only the running task cards to refresh their duration display."""
        try:
            for card in self.query(TaskCard):
                task = card._task_data
                if task.is_running and task.status in (TaskStatus.IN_PROGRESS, TaskStatus.PENDING_APPROVAL):
                    card.refresh()
        except Exception:
            pass

    def compose(self) -> ComposeResult:
        self._load_tasks()
        grouped = group_tasks_by_status(self._tasks_list)

        yield Static(
            f"[bold]Kanban[/] │ "
            f"[#a6adc8]Pending: {len(grouped[TaskStatus.PENDING])}[/] │ "
            f"[#fab387]In Progress: {len(grouped[TaskStatus.IN_PROGRESS])}[/] │ "
            f"[#cba6f7]Pending Approval: {len(grouped[TaskStatus.PENDING_APPROVAL])}[/] │ "
            f"[#a6e3a1]Complete: {len(grouped[TaskStatus.COMPLETE])}[/] │ "
            f"[#f38ba8]Failed: {len(grouped[TaskStatus.FAILED])}[/]",
            classes="kanban-header",
        )

        if not self._tasks_list:
            yield Static(
                f"No tasks found at {self.kanban_path}",
                classes="empty-message",
            )
            return

        # Sort pending tasks based on current sort mode
        pending_tasks = self._sort_pending_tasks(grouped[TaskStatus.PENDING])

        # Sort pending approval: running tasks first
        pa_tasks = sorted(
            grouped[TaskStatus.PENDING_APPROVAL],
            key=lambda t: (0 if t.is_running else 1),
        )

        pending_header = self._get_pending_column_header()

        columns = [
            KanbanColumn(TaskStatus.PENDING, pending_tasks, header_suffix=pending_header),
            KanbanColumn(TaskStatus.IN_PROGRESS, grouped[TaskStatus.IN_PROGRESS]),
            KanbanColumn(TaskStatus.PENDING_APPROVAL, pa_tasks),
            KanbanColumn(TaskStatus.COMPLETE, grouped[TaskStatus.COMPLETE]),
        ]
        if grouped[TaskStatus.FAILED]:
            columns.append(KanbanColumn(TaskStatus.FAILED, grouped[TaskStatus.FAILED]))

        yield Horizontal(*columns, classes="kanban-board")

    def _load_tasks(self) -> None:
        """Load tasks from kanban.md with running status."""
        # Use shared worker service if available
        try:
            worker_service = self.app.worker_service
        except AttributeError:
            worker_service = None
        self._tasks_list = parse_kanban_with_status(
            self.kanban_path, self.ralph_dir, worker_service=worker_service
        )

    def _get_focused_task_id(self) -> str | None:
        """Get the task ID of the currently focused card."""
        try:
            for card in self.query(TaskCard):
                if card.has_focus:
                    return card._task_data.id
        except Exception:
            pass
        return None

    def _restore_focus_by_task_id(self, task_id: str | None) -> None:
        """Restore focus to a card with the given task ID.

        Only restores focus if the kanban tab is currently active to avoid
        stealing focus from other tabs during background refreshes.
        """
        if not task_id:
            return
        # Don't steal focus if kanban tab isn't active
        try:
            if getattr(self.app, "_active_tab", "kanban") != "kanban":
                return
        except Exception:
            pass
        try:
            for card in self.query(TaskCard):
                if card._task_data.id == task_id:
                    card.focus()
                    return
        except Exception:
            pass

    def refresh_data(self) -> None:
        """Refresh task data incrementally, only updating changed elements."""
        self._load_tasks()

        # Check if data actually changed
        new_hash = self._compute_data_hash(self._tasks_list)
        if new_hash == self._last_data_hash:
            return  # No change, skip refresh
        self._last_data_hash = new_hash

        # Save focused card's task ID before updating
        focused_task_id = self._get_focused_task_id()

        grouped = group_tasks_by_status(self._tasks_list)

        # Update header counts
        try:
            header = self.query_one(".kanban-header", Static)
            header.update(
                f"[bold]Kanban[/] │ "
                f"[#a6adc8]Pending: {len(grouped[TaskStatus.PENDING])}[/] │ "
                f"[#fab387]In Progress: {len(grouped[TaskStatus.IN_PROGRESS])}[/] │ "
                f"[#cba6f7]Pending Approval: {len(grouped[TaskStatus.PENDING_APPROVAL])}[/] │ "
                f"[#a6e3a1]Complete: {len(grouped[TaskStatus.COMPLETE])}[/] │ "
                f"[#f38ba8]Failed: {len(grouped[TaskStatus.FAILED])}[/]"
            )
        except Exception:
            pass

        if not self._tasks_list:
            # No tasks — remove board if present
            try:
                self.query_one(".kanban-board", Horizontal).remove()
            except Exception:
                pass
            self._restore_focus_by_task_id(focused_task_id)
            return

        # Prepare sorted task lists
        pending_tasks = self._sort_pending_tasks(grouped[TaskStatus.PENDING])
        pa_tasks = sorted(
            grouped[TaskStatus.PENDING_APPROVAL],
            key=lambda t: (0 if t.is_running else 1),
        )
        pending_header = self._get_pending_column_header()

        # Try incremental column updates (no DOM tear-down)
        incremental_ok = True
        column_updates = [
            (TaskStatus.PENDING, pending_tasks, pending_header),
            (TaskStatus.IN_PROGRESS, grouped[TaskStatus.IN_PROGRESS], ""),
            (TaskStatus.PENDING_APPROVAL, pa_tasks, ""),
            (TaskStatus.COMPLETE, grouped[TaskStatus.COMPLETE], ""),
        ]
        for status, tasks, suffix in column_updates:
            try:
                col = self.query_one(f"#col-{status.value}", KanbanColumn)
                col.update_tasks(tasks, suffix)
            except Exception:
                incremental_ok = False
                break

        if incremental_ok:
            # Handle FAILED column (may appear or disappear)
            failed_tasks = grouped[TaskStatus.FAILED]
            try:
                failed_col = self.query_one("#col-failed", KanbanColumn)
                if failed_tasks:
                    failed_col.update_tasks(failed_tasks)
                else:
                    failed_col.remove()
            except Exception:
                if failed_tasks:
                    try:
                        board = self.query_one(".kanban-board", Horizontal)
                        board.mount(KanbanColumn(TaskStatus.FAILED, failed_tasks))
                    except Exception:
                        incremental_ok = False

        if not incremental_ok:
            # Fallback: full rebuild (first render after empty state, etc.)
            try:
                self.query_one(".kanban-board", Horizontal).remove()
            except Exception:
                pass

            columns = [
                KanbanColumn(TaskStatus.PENDING, pending_tasks, header_suffix=pending_header),
                KanbanColumn(TaskStatus.IN_PROGRESS, grouped[TaskStatus.IN_PROGRESS]),
                KanbanColumn(TaskStatus.PENDING_APPROVAL, pa_tasks),
                KanbanColumn(TaskStatus.COMPLETE, grouped[TaskStatus.COMPLETE]),
            ]
            if grouped[TaskStatus.FAILED]:
                columns.append(KanbanColumn(TaskStatus.FAILED, grouped[TaskStatus.FAILED]))

            self.mount(Horizontal(*columns, classes="kanban-board"))

        self._restore_focus_by_task_id(focused_task_id)

    def _get_pending_column_header(self) -> str:
        """Get header suffix for the pending column showing current sort mode."""
        mode = self.PENDING_SORT_MODES[self._pending_sort_mode]
        if mode == "default":
            return ""
        return f" [{mode}]"

    def _sort_pending_tasks(self, tasks: list[Task]) -> list[Task]:
        """Sort pending tasks based on current sort mode.

        Args:
            tasks: List of pending tasks to sort.

        Returns:
            Sorted list.
        """
        mode = self.PENDING_SORT_MODES[self._pending_sort_mode]
        if mode == "default":
            return tasks
        elif mode == "priority":
            priority_order = {"CRITICAL": 0, "HIGH": 1, "MEDIUM": 2, "LOW": 3}
            return sorted(tasks, key=lambda t: priority_order.get(t.priority, 9))
        elif mode == "score":
            return sorted(tasks, key=lambda t: t.scheduling_score if t.scheduling_score is not None else 99999)
        elif mode == "name":
            return sorted(tasks, key=lambda t: t.title.lower())
        return tasks

    def action_cycle_pending_sort(self) -> None:
        """Cycle through pending column sort modes."""
        self._pending_sort_mode = (self._pending_sort_mode + 1) % len(self.PENDING_SORT_MODES)
        mode_name = self.PENDING_SORT_MODES[self._pending_sort_mode].title()
        self.app.notify(f"Pending sort: {mode_name}", timeout=2)
        # Force a full refresh
        self._last_data_hash = ""
        self.refresh_data()

    def _get_all_cards(self) -> list[TaskCard]:
        """Get all TaskCard widgets in order."""
        try:
            return list(self.query(TaskCard))
        except Exception:
            return []

    def _get_focused_card_index(self) -> int:
        """Get index of currently focused card, or -1 if none."""
        cards = self._get_all_cards()
        for i, card in enumerate(cards):
            if card.has_focus:
                return i
        return -1

    def action_next_card(self) -> None:
        """Move to next card (vim j)."""
        cards = self._get_all_cards()
        if not cards:
            return
        current = self._get_focused_card_index()
        next_idx = (current + 1) % len(cards) if current >= 0 else 0
        cards[next_idx].focus()

    def action_prev_card(self) -> None:
        """Move to previous card (vim k)."""
        cards = self._get_all_cards()
        if not cards:
            return
        current = self._get_focused_card_index()
        prev_idx = (current - 1) % len(cards) if current >= 0 else len(cards) - 1
        cards[prev_idx].focus()

    def action_first_card(self) -> None:
        """Move to first card (vim gg)."""
        cards = self._get_all_cards()
        if cards:
            cards[0].focus()

    def action_last_card(self) -> None:
        """Move to last card (vim G)."""
        cards = self._get_all_cards()
        if cards:
            cards[-1].focus()

    def _get_column_cards(self) -> list[list[TaskCard]]:
        """Get cards grouped by column."""
        try:
            columns = list(self.query(KanbanColumn))
            result = []
            for col in columns:
                col_cards = list(col.query(TaskCard))
                result.append(col_cards)
            return result
        except Exception:
            return []

    def action_prev_column(self) -> None:
        """Move to previous column (vim h)."""
        column_cards = self._get_column_cards()
        if not column_cards:
            return

        # Find current column
        current_col = -1
        current_row = 0
        for col_idx, cards in enumerate(column_cards):
            for row_idx, card in enumerate(cards):
                if card.has_focus:
                    current_col = col_idx
                    current_row = row_idx
                    break

        if current_col <= 0:
            # Already at first column or no focus
            return

        # Move to previous column, same row or last card
        prev_col = column_cards[current_col - 1]
        if prev_col:
            target_row = min(current_row, len(prev_col) - 1)
            prev_col[target_row].focus()

    def action_next_column(self) -> None:
        """Move to next column (vim l)."""
        column_cards = self._get_column_cards()
        if not column_cards:
            return

        # Find current column
        current_col = -1
        current_row = 0
        for col_idx, cards in enumerate(column_cards):
            for row_idx, card in enumerate(cards):
                if card.has_focus:
                    current_col = col_idx
                    current_row = row_idx
                    break

        if current_col < 0 or current_col >= len(column_cards) - 1:
            # No focus or already at last column
            return

        # Move to next column, same row or last card
        next_col = column_cards[current_col + 1]
        if next_col:
            target_row = min(current_row, len(next_col) - 1)
            next_col[target_row].focus()

    def action_open_card(self) -> None:
        """Open focused card details (vim enter)."""
        cards = self._get_all_cards()
        for card in cards:
            if card.has_focus:
                self.app.push_screen(TaskDetailModal(card._task_data, ralph_dir=self.ralph_dir))
                break
