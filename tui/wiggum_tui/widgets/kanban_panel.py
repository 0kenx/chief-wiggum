"""Kanban board panel widget."""

from pathlib import Path
from textual.app import ComposeResult
from textual.containers import Horizontal, Vertical, VerticalScroll, Center
from textual.widgets import Static, Button
from textual.widget import Widget
from textual.screen import ModalScreen
from textual.binding import Binding

from ..data.kanban_parser import parse_kanban, group_tasks_by_status
from ..data.models import Task, TaskStatus


class TaskDetailModal(ModalScreen[None]):
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
        background: #1e293b;
        border: solid #f59e0b;
        padding: 1 2;
    }

    TaskDetailModal .modal-title {
        text-align: center;
        text-style: bold;
        color: #f59e0b;
        padding: 0 0 1 0;
    }

    TaskDetailModal .detail-section {
        margin: 1 0 0 0;
    }

    TaskDetailModal .detail-label {
        color: #94a3b8;
        text-style: bold;
    }

    TaskDetailModal .detail-value {
        color: #e2e8f0;
        padding: 0 0 0 2;
    }

    TaskDetailModal .detail-list-item {
        color: #e2e8f0;
        padding: 0 0 0 4;
    }

    TaskDetailModal .status-pending {
        color: #94a3b8;
    }

    TaskDetailModal .status-in_progress {
        color: #f59e0b;
    }

    TaskDetailModal .status-complete {
        color: #22c55e;
    }

    TaskDetailModal .status-failed {
        color: #dc2626;
    }

    TaskDetailModal .priority-critical {
        color: #dc2626;
        text-style: bold;
    }

    TaskDetailModal .priority-high {
        color: #f59e0b;
    }

    TaskDetailModal .priority-medium {
        color: #3b82f6;
    }

    TaskDetailModal .priority-low {
        color: #64748b;
    }

    TaskDetailModal Button {
        margin: 1 0 0 0;
        width: 100%;
    }
    """

    BINDINGS = [
        Binding("escape", "close", "Close"),
        Binding("enter", "close", "Close"),
    ]

    def __init__(self, task: Task) -> None:
        super().__init__()
        self._task = task

    def compose(self) -> ComposeResult:
        task = self._task
        status_class = f"status-{task.status.value}"
        priority_class = f"priority-{task.priority.lower()}"

        with Vertical():
            yield Static(f"{task.id}: {task.title}", classes="modal-title")

            # Status and Priority row
            yield Static(
                f"[{status_class}]Status: {task.status.value.upper()}[/]  │  "
                f"[{priority_class}]Priority: {task.priority}[/]",
            )

            # Description
            if task.description:
                yield Static("[bold #94a3b8]Description[/]", classes="detail-section")
                yield Static(f"  {task.description}", classes="detail-value")

            # Dependencies
            if task.dependencies:
                yield Static("[bold #94a3b8]Dependencies[/]", classes="detail-section")
                for dep in task.dependencies:
                    yield Static(f"  • {dep}", classes="detail-list-item")

            # Scope
            if task.scope:
                yield Static("[bold #94a3b8]Scope[/]", classes="detail-section")
                for item in task.scope:
                    yield Static(f"  • {item}", classes="detail-list-item")

            # Out of Scope
            if task.out_of_scope:
                yield Static("[bold #94a3b8]Out of Scope[/]", classes="detail-section")
                for item in task.out_of_scope:
                    yield Static(f"  • {item}", classes="detail-list-item")

            # Acceptance Criteria
            if task.acceptance_criteria:
                yield Static("[bold #94a3b8]Acceptance Criteria[/]", classes="detail-section")
                for item in task.acceptance_criteria:
                    yield Static(f"  • {item}", classes="detail-list-item")

            yield Button("Close [Esc]", variant="primary")

    def on_button_pressed(self, event: Button.Pressed) -> None:
        self.dismiss()

    def action_close(self) -> None:
        self.dismiss()


class TaskCard(Static):
    """A single task card in the kanban board."""

    DEFAULT_CSS = """
    TaskCard {
        background: #1e293b;
        border: solid #334155;
        margin: 0 0 1 0;
        padding: 0 1;
        height: auto;
        min-height: 3;
    }

    TaskCard:hover {
        border: solid #f59e0b;
        background: #334155;
    }

    TaskCard:focus {
        border: solid #f59e0b;
    }

    TaskCard .task-id {
        color: #f59e0b;
        text-style: bold;
    }

    TaskCard .task-title {
        color: #e2e8f0;
    }

    TaskCard .task-priority-critical {
        color: #dc2626;
    }

    TaskCard .task-priority-high {
        color: #f59e0b;
    }

    TaskCard .task-priority-medium {
        color: #3b82f6;
    }

    TaskCard .task-priority-low {
        color: #64748b;
    }
    """

    can_focus = True

    def __init__(self, task_data: Task) -> None:
        super().__init__()
        self._task_data = task_data

    def render(self) -> str:
        """Render task card content."""
        priority_class = f"task-priority-{self._task_data.priority.lower()}"
        priority_indicator = {
            "CRITICAL": "!!!",
            "HIGH": "!!",
            "MEDIUM": "!",
            "LOW": "",
        }.get(self._task_data.priority, "")

        title = self._task_data.title
        if len(title) > 30:
            title = title[:27] + "..."

        lines = [
            f"[bold #f59e0b]{self._task_data.id}[/] [{priority_class}]{priority_indicator}[/]",
            f"[#e2e8f0]{title}[/]",
        ]
        return "\n".join(lines)

    def on_click(self) -> None:
        """Handle click to show task details."""
        self.app.push_screen(TaskDetailModal(self._task_data))

    def key_enter(self) -> None:
        """Handle Enter key to show task details."""
        self.app.push_screen(TaskDetailModal(self._task_data))


class KanbanColumn(Widget):
    """A single column in the kanban board."""

    DEFAULT_CSS = """
    KanbanColumn {
        width: 1fr;
        height: 100%;
        border: solid #334155;
    }

    KanbanColumn .column-header {
        background: #1e293b;
        text-align: center;
        text-style: bold;
        height: 1;
        padding: 0 1;
    }

    KanbanColumn .column-header-pending {
        color: #94a3b8;
    }

    KanbanColumn .column-header-in_progress {
        color: #f59e0b;
    }

    KanbanColumn .column-header-complete {
        color: #22c55e;
    }

    KanbanColumn .column-header-failed {
        color: #dc2626;
    }

    KanbanColumn .column-content {
        padding: 1;
    }
    """

    def __init__(self, status: TaskStatus, tasks_list: list[Task]) -> None:
        super().__init__()
        self._status = status
        self._tasks_list = tasks_list

    def compose(self) -> ComposeResult:
        status_name = self._status.value.replace("_", " ").upper()
        header_class = f"column-header-{self._status.value}"
        yield Static(
            f"[{header_class}]{status_name} ({len(self._tasks_list)})[/]",
            classes="column-header",
        )
        with VerticalScroll(classes="column-content"):
            for task_item in self._tasks_list:
                yield TaskCard(task_item)


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
        background: #1e293b;
        padding: 0 1;
    }

    KanbanPanel .kanban-board {
        height: 1fr;
        width: 100%;
    }

    KanbanPanel .empty-message {
        text-align: center;
        color: #64748b;
        padding: 2;
    }
    """

    def __init__(self, ralph_dir: Path) -> None:
        super().__init__()
        self.ralph_dir = ralph_dir
        self.kanban_path = ralph_dir / "kanban.md"
        self._tasks_list: list[Task] = []

    def compose(self) -> ComposeResult:
        self._load_tasks()
        grouped = group_tasks_by_status(self._tasks_list)

        yield Static(
            f"[bold]Kanban[/] │ "
            f"[#94a3b8]Pending: {len(grouped[TaskStatus.PENDING])}[/] │ "
            f"[#f59e0b]In Progress: {len(grouped[TaskStatus.IN_PROGRESS])}[/] │ "
            f"[#22c55e]Complete: {len(grouped[TaskStatus.COMPLETE])}[/] │ "
            f"[#dc2626]Failed: {len(grouped[TaskStatus.FAILED])}[/]",
            classes="kanban-header",
        )

        if not self._tasks_list:
            yield Static(
                f"No tasks found at {self.kanban_path}",
                classes="empty-message",
            )
            return

        yield Horizontal(
            KanbanColumn(TaskStatus.PENDING, grouped[TaskStatus.PENDING]),
            KanbanColumn(TaskStatus.IN_PROGRESS, grouped[TaskStatus.IN_PROGRESS]),
            KanbanColumn(TaskStatus.COMPLETE, grouped[TaskStatus.COMPLETE]),
            KanbanColumn(TaskStatus.FAILED, grouped[TaskStatus.FAILED]),
            classes="kanban-board",
        )

    def _load_tasks(self) -> None:
        """Load tasks from kanban.md."""
        self._tasks_list = parse_kanban(self.kanban_path)

    def refresh_data(self) -> None:
        """Refresh task data and re-render."""
        self._load_tasks()
        grouped = group_tasks_by_status(self._tasks_list)

        # Update header
        try:
            header = self.query_one(".kanban-header", Static)
            header.update(
                f"[bold]Kanban[/] │ "
                f"[#94a3b8]Pending: {len(grouped[TaskStatus.PENDING])}[/] │ "
                f"[#f59e0b]In Progress: {len(grouped[TaskStatus.IN_PROGRESS])}[/] │ "
                f"[#22c55e]Complete: {len(grouped[TaskStatus.COMPLETE])}[/] │ "
                f"[#dc2626]Failed: {len(grouped[TaskStatus.FAILED])}[/]"
            )
        except Exception:
            pass

        # Remove old board and recompose columns
        try:
            old_board = self.query_one(".kanban-board", Horizontal)
            old_board.remove()
        except Exception:
            pass

        if self._tasks_list:
            self.mount(
                Horizontal(
                    KanbanColumn(TaskStatus.PENDING, grouped[TaskStatus.PENDING]),
                    KanbanColumn(TaskStatus.IN_PROGRESS, grouped[TaskStatus.IN_PROGRESS]),
                    KanbanColumn(TaskStatus.COMPLETE, grouped[TaskStatus.COMPLETE]),
                    KanbanColumn(TaskStatus.FAILED, grouped[TaskStatus.FAILED]),
                    classes="kanban-board",
                )
            )
