"""Kanban parser - ported from TypeScript."""

import re
from pathlib import Path
from .models import Task, TaskStatus


STATUS_MAP = {
    "[ ]": TaskStatus.PENDING,
    "[=]": TaskStatus.IN_PROGRESS,
    "[P]": TaskStatus.PENDING_APPROVAL,
    "[x]": TaskStatus.COMPLETE,
    "[N]": TaskStatus.NOT_PLANNED,
    "[*]": TaskStatus.FAILED,
    "[T]": TaskStatus.FAILED,  # Timeout treated as failed
}

# Pattern: - [ ] **[TASK-ID]** Title
# Status chars: space (pending), = (in progress), P (pending approval),
#               x (complete), N (not planned), * (failed), T (timeout/failed)
TASK_PATTERN = re.compile(r"^- \[([ =PxN*T])\] \*\*\[([A-Za-z]{2,8}-\d+)\]\*\*\s*(.*)")


def parse_kanban(file_path: Path) -> list[Task]:
    """Parse kanban.md file into Task objects.

    Args:
        file_path: Path to kanban.md file.

    Returns:
        List of Task objects parsed from the file.
    """
    try:
        content = file_path.read_text()
    except (OSError, FileNotFoundError):
        return []

    lines = content.split("\n")
    tasks: list[Task] = []
    current_task: Task | None = None
    current_field: str | None = None

    for line in lines:
        # Check for task line
        task_match = TASK_PATTERN.match(line)

        if task_match:
            # Save previous task
            if current_task:
                tasks.append(current_task)

            status_char, task_id, title = task_match.groups()
            status = STATUS_MAP.get(f"[{status_char}]", TaskStatus.PENDING)

            current_task = Task(
                id=task_id,
                title=title.strip(),
                status=status,
            )
            current_field = None
            continue

        if not current_task:
            continue

        # Check for field lines (2-space indent)
        if line.startswith("  - "):
            field_line = line[4:]

            if field_line.startswith("Description:"):
                current_task.description = field_line[12:].strip()
                current_field = None
            elif field_line.startswith("Priority:"):
                priority = field_line[9:].strip().upper()
                if priority in ("CRITICAL", "HIGH", "MEDIUM", "LOW"):
                    current_task.priority = priority
                current_field = None
            elif field_line.startswith("Complexity:"):
                complexity = field_line[11:].strip().upper()
                if complexity in ("HIGH", "MEDIUM", "LOW"):
                    current_task.complexity = complexity
                current_field = None
            elif field_line.startswith("Dependencies:"):
                deps = field_line[13:].strip()
                if deps and deps.lower() != "none":
                    current_task.dependencies = [d.strip() for d in deps.split(",")]
                current_field = None
            elif field_line.startswith("Scope:") or field_line == "Scope":
                current_field = "scope"
            elif field_line.startswith("Out of Scope:") or field_line == "Out of Scope":
                current_field = "out_of_scope"
            elif (
                field_line.startswith("Acceptance Criteria:")
                or field_line == "Acceptance Criteria"
            ):
                current_field = "acceptance_criteria"
            continue

        # Check for sub-items (4-space indent)
        if line.startswith("    - ") and current_field:
            item = line[6:].strip()
            getattr(current_task, current_field).append(item)

    # Don't forget the last task
    if current_task:
        tasks.append(current_task)

    return tasks


def group_tasks_by_status(tasks: list[Task]) -> dict[TaskStatus, list[Task]]:
    """Group tasks by their status.

    Args:
        tasks: List of tasks to group.

    Returns:
        Dictionary mapping status to list of tasks.
    """
    return {
        TaskStatus.PENDING: [t for t in tasks if t.status == TaskStatus.PENDING],
        TaskStatus.IN_PROGRESS: [t for t in tasks if t.status == TaskStatus.IN_PROGRESS],
        TaskStatus.PENDING_APPROVAL: [t for t in tasks if t.status == TaskStatus.PENDING_APPROVAL],
        TaskStatus.COMPLETE: [t for t in tasks if t.status == TaskStatus.COMPLETE],
        TaskStatus.NOT_PLANNED: [t for t in tasks if t.status == TaskStatus.NOT_PLANNED],
        TaskStatus.FAILED: [t for t in tasks if t.status == TaskStatus.FAILED],
    }


def get_task_counts(tasks: list[Task]) -> dict[str, int]:
    """Get count of tasks in each status.

    Args:
        tasks: List of tasks.

    Returns:
        Dictionary with counts for each status and total.
    """
    grouped = group_tasks_by_status(tasks)
    return {
        "pending": len(grouped[TaskStatus.PENDING]),
        "in_progress": len(grouped[TaskStatus.IN_PROGRESS]),
        "pending_approval": len(grouped[TaskStatus.PENDING_APPROVAL]),
        "complete": len(grouped[TaskStatus.COMPLETE]),
        "not_planned": len(grouped[TaskStatus.NOT_PLANNED]),
        "failed": len(grouped[TaskStatus.FAILED]),
        "total": len(tasks),
    }
