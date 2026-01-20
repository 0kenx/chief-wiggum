"""Conversation panel widget showing worker chat history."""

from pathlib import Path
from typing import Any
from textual.app import ComposeResult
from textual.containers import Horizontal, Vertical, VerticalScroll
from textual.widgets import Static, Select, Tree
from textual.widgets.tree import TreeNode
from textual.widget import Widget

from ..data.conversation_parser import (
    parse_iteration_logs,
    get_conversation_summary,
    truncate_text,
    format_tool_result,
)
from ..data.worker_scanner import scan_workers
from ..data.models import Conversation, ConversationTurn, ToolCall

import json


def format_content(text: str, width: int = 100) -> list[str]:
    """Format content for display. Detects JSON and formats it, otherwise wraps text."""
    text = text.strip()

    # Try to detect and format JSON
    if text.startswith(("{", "[", '"')):
        try:
            parsed = json.loads(text)
            formatted = json.dumps(parsed, indent=2, ensure_ascii=False)
            return formatted.split("\n")
        except (json.JSONDecodeError, ValueError):
            pass

    # Not JSON, wrap text
    return wrap_text(text, width)


def wrap_text(text: str, width: int = 100) -> list[str]:
    """Wrap text to specified width, preserving existing line breaks."""
    lines = []
    for line in text.split("\n"):
        if not line:
            lines.append("")
            continue
        while len(line) > width:
            # Find a good break point
            break_at = line.rfind(" ", 0, width)
            if break_at == -1:
                break_at = width
            lines.append(line[:break_at])
            line = line[break_at:].lstrip()
        lines.append(line)
    return lines


class ConversationPanel(Widget):
    """Conversation panel showing worker chat history in a tree view."""

    BINDINGS = [
        ("e", "expand_all", "Expand all"),
        ("c", "collapse_all", "Collapse all"),
        ("+", "expand_selected", "Expand selected"),
        ("-", "collapse_selected", "Collapse selected"),
    ]

    DEFAULT_CSS = """
    ConversationPanel {
        height: 1fr;
        width: 100%;
        layout: vertical;
    }

    ConversationPanel .conv-header {
        height: 1;
        background: #1e293b;
        padding: 0 1;
    }

    ConversationPanel .conv-controls {
        height: 3;
        background: #1e293b;
        padding: 0 1;
    }

    ConversationPanel Select {
        width: 40;
    }

    ConversationPanel Tree {
        height: 1fr;
        background: #0f172a;
        border: solid #334155;
    }

    ConversationPanel .empty-message {
        text-align: center;
        color: #64748b;
        padding: 2;
    }

    ConversationPanel .prompt-section {
        height: auto;
        max-height: 10;
        background: #1e293b;
        border: solid #334155;
        padding: 1;
        margin-bottom: 1;
    }

    ConversationPanel .prompt-label {
        color: #f59e0b;
        text-style: bold;
    }

    ConversationPanel .prompt-text {
        color: #94a3b8;
    }
    """

    def __init__(self, ralph_dir: Path) -> None:
        super().__init__()
        self.ralph_dir = ralph_dir
        self._workers_list: list[tuple[str, str]] = []  # (id, label)
        self.current_worker: str | None = None
        self.conversation: Conversation | None = None

    def compose(self) -> ComposeResult:
        self._load_workers()

        yield Static(
            "[bold]Conversation[/] │ Select a worker to view chat history",
            classes="conv-header",
            id="conv-header",
        )

        with Horizontal(classes="conv-controls"):
            yield Select(
                [(label, worker_id) for worker_id, label in self._workers_list],
                prompt="Select worker...",
                id="worker-select",
            )

        if not self._workers_list:
            yield Static(
                "No workers with conversation logs found.",
                classes="empty-message",
            )
            return

        yield Tree("Conversation", id="conv-tree")

    def on_mount(self) -> None:
        """Initialize panel."""
        if self._workers_list:
            # Auto-select first worker
            first_worker_id = self._workers_list[0][0]
            self._load_conversation(first_worker_id)

    def _load_workers(self) -> None:
        """Load list of workers with conversations."""
        workers = scan_workers(self.ralph_dir)
        self._workers_list = []

        for worker in workers:
            worker_dir = self.ralph_dir / "workers" / worker.id
            logs_dir = worker_dir / "logs"
            if logs_dir.is_dir() and list(logs_dir.glob("iteration-*.log")):
                label = f"{worker.task_id} - {worker.status.value}"
                self._workers_list.append((worker.id, label))

    def _load_conversation(self, worker_id: str) -> None:
        """Load conversation for a worker."""
        self.current_worker = worker_id
        worker_dir = self.ralph_dir / "workers" / worker_id
        self.conversation = parse_iteration_logs(worker_dir)
        self._populate_tree()
        self._update_header()

    def _populate_tree(self) -> None:
        """Populate the tree with conversation turns."""
        try:
            tree = self.query_one("#conv-tree", Tree)
            tree.clear()

            if not self.conversation or not self.conversation.turns:
                tree.root.add_leaf("No conversation data available")
                return

            # Add summary
            summary = get_conversation_summary(self.conversation)
            tree.root.label = (
                f"Conversation │ {summary['turns']} turns │ "
                f"{summary['tool_calls']} tool calls │ "
                f"${summary['cost_usd']:.2f}"
            )

            # Group turns by iteration
            current_iteration = -1
            iteration_node: TreeNode | None = None

            for i, turn in enumerate(self.conversation.turns):
                if turn.iteration != current_iteration:
                    current_iteration = turn.iteration
                    # Find iteration result for this iteration
                    result = next(
                        (r for r in self.conversation.results if r.iteration == current_iteration),
                        None,
                    )
                    result_info = ""
                    if result:
                        result_info = f" │ {result.num_turns} turns │ ${result.total_cost_usd:.2f}"

                    iteration_node = tree.root.add(
                        f"[#f59e0b]Iteration {current_iteration}[/]{result_info}",
                        expand=current_iteration == 0,
                    )

                if iteration_node:
                    self._add_turn_to_tree(iteration_node, turn, i)

            tree.root.expand()

        except Exception:
            pass

    def _add_turn_to_tree(self, parent: TreeNode, turn: ConversationTurn, index: int) -> None:
        """Add a conversation turn to the tree."""
        # Create assistant node that groups text and tool calls
        tool_count = len(turn.tool_calls)
        tool_info = f" │ {tool_count} tool{'s' if tool_count != 1 else ''}" if tool_count else ""

        text_preview = ""
        if turn.assistant_text:
            text_preview = truncate_text(turn.assistant_text, 60)

        assistant_label = f"[#3b82f6]Assistant[/]{tool_info}"
        if text_preview:
            assistant_label += f" [#64748b]{text_preview}[/]"

        assistant_node = parent.add(assistant_label, expand=False)

        # Add full assistant text as expandable child if truncated
        if turn.assistant_text:
            if len(turn.assistant_text) > 60:
                # Add expandable node for full text with line wrapping
                text_node = assistant_node.add("[#3b82f6]Full message[/]", expand=False)
                for line in format_content(turn.assistant_text, 100):
                    text_node.add_leaf(f"[#94a3b8]{line}[/]")
            else:
                assistant_node.add_leaf(f"[#94a3b8]{turn.assistant_text}[/]")

        # Add tool calls as children of assistant node
        for tool_call in turn.tool_calls:
            # Format tool label with input preview
            input_preview = self._format_tool_input(tool_call)
            if input_preview:
                tool_label = f"[#22c55e]{tool_call.name}[/] [#64748b]{input_preview}[/]"
            else:
                tool_label = f"[#22c55e]{tool_call.name}[/]"

            tool_node = assistant_node.add(tool_label, expand=False)

            # Add full tool input as expandable child
            self._add_tool_input_details(tool_node, tool_call)

            # Add result if present
            if tool_call.result is not None:
                self._add_tool_result(tool_node, tool_call)

    def _format_tool_input(self, tool_call: ToolCall) -> str:
        """Format tool input for display."""
        if not tool_call.input:
            return ""

        # Handle common tool types
        if tool_call.name == "Read":
            return tool_call.input.get("file_path", "")[:60]
        elif tool_call.name == "Write":
            path = tool_call.input.get("file_path", "")
            return f"{path[:50]}..."
        elif tool_call.name == "Edit":
            path = tool_call.input.get("file_path", "")
            return path[:60]
        elif tool_call.name == "Bash":
            cmd = tool_call.input.get("command", "")
            return truncate_text(cmd, 60)
        elif tool_call.name == "Glob":
            return tool_call.input.get("pattern", "")[:60]
        elif tool_call.name == "Grep":
            return tool_call.input.get("pattern", "")[:60]
        elif tool_call.name == "TodoWrite":
            todos = tool_call.input.get("todos", [])
            return f"{len(todos)} todos"
        else:
            # Generic handling
            first_key = next(iter(tool_call.input.keys()), None)
            if first_key:
                value = str(tool_call.input[first_key])
                return truncate_text(value, 60)
        return ""

    def _add_tool_input_details(self, tool_node: TreeNode, tool_call: ToolCall) -> None:
        """Add expandable tool input details."""
        if not tool_call.input:
            return

        if tool_call.name == "TodoWrite":
            # Show each todo with status
            todos = tool_call.input.get("todos", [])
            if todos:
                input_node = tool_node.add("[#64748b]Todos[/]", expand=False)
                for todo in todos:
                    status = todo.get("status", "pending")
                    content = todo.get("content", "")
                    status_icon = {"pending": "○", "in_progress": "◐", "completed": "●"}.get(status, "?")
                    status_color = {"pending": "#64748b", "in_progress": "#f59e0b", "completed": "#22c55e"}.get(status, "#64748b")
                    input_node.add_leaf(f"[{status_color}]{status_icon}[/] {content}")

        elif tool_call.name == "Edit":
            # Show old_string and new_string with full content
            old_str = tool_call.input.get("old_string", "")
            new_str = tool_call.input.get("new_string", "")
            if old_str or new_str:
                input_node = tool_node.add("[#64748b]Edit details[/]", expand=False)
                if old_str:
                    old_node = input_node.add("[#dc2626]Old string[/]", expand=False)
                    for line in wrap_text(old_str, 100):
                        old_node.add_leaf(f"[#dc2626]{line}[/]")
                if new_str:
                    new_node = input_node.add("[#22c55e]New string[/]", expand=False)
                    for line in wrap_text(new_str, 100):
                        new_node.add_leaf(f"[#22c55e]{line}[/]")

        elif tool_call.name == "Write":
            # Show full content with wrapping
            content = tool_call.input.get("content", "")
            if content:
                input_node = tool_node.add(f"[#64748b]Content ({len(content.splitlines())} lines)[/]", expand=False)
                for line in wrap_text(content, 100):
                    input_node.add_leaf(f"[#94a3b8]{line}[/]")

        elif tool_call.name == "Bash":
            # Show full command with wrapping
            cmd = tool_call.input.get("command", "")
            if len(cmd) > 60:
                input_node = tool_node.add("[#64748b]Full command[/]", expand=False)
                for line in wrap_text(cmd, 100):
                    input_node.add_leaf(f"[#94a3b8]{line}[/]")

        elif tool_call.name == "Task":
            # Show full prompt with formatting
            prompt = tool_call.input.get("prompt", "")
            if prompt:
                input_node = tool_node.add("[#64748b]Prompt[/]", expand=False)
                for line in format_content(prompt, 100):
                    input_node.add_leaf(f"[#94a3b8]{line}[/]")

    def _add_tool_result(self, tool_node: TreeNode, tool_call: ToolCall) -> None:
        """Add tool result with expandable details."""
        result = tool_call.result

        # For Write tool, just show success/failure - content already shown in input
        if tool_call.name == "Write":
            if isinstance(result, dict):
                if result.get("success") or result.get("type") == "text":
                    tool_node.add_leaf("[#22c55e]Success[/]")
                elif "error" in result:
                    tool_node.add_leaf(f"[#dc2626]Error: {result['error']}[/]")
                else:
                    tool_node.add_leaf("[#22c55e]Success[/]")
            else:
                tool_node.add_leaf("[#22c55e]Success[/]")
            return

        result_preview = format_tool_result(result, 80)

        # Determine color
        if "Error" in result_preview:
            color = "#dc2626"
        elif result_preview == "Success":
            color = "#22c55e"
        else:
            color = "#94a3b8"

        # Check if result needs expansion
        needs_expansion = False
        if isinstance(result, dict):
            # Check for content that was truncated
            if "{...}" in result_preview:
                needs_expansion = True
            elif result.get("stdout") and len(str(result["stdout"])) > 80:
                needs_expansion = True
            elif result.get("content") and len(str(result.get("content", ""))) > 80:
                needs_expansion = True
        elif isinstance(result, str) and len(result) > 80:
            needs_expansion = True

        if needs_expansion:
            result_node = tool_node.add(f"[{color}]{result_preview}[/]", expand=False)
            self._add_full_result(result_node, result)
        else:
            tool_node.add_leaf(f"[{color}]{result_preview}[/]")

    def _add_full_result(self, result_node: TreeNode, result: Any) -> None:
        """Add full result content as expandable children."""
        if isinstance(result, dict):
            if "stdout" in result:
                content = str(result["stdout"])
                for line in format_content(content, 100):
                    result_node.add_leaf(f"[#94a3b8]{line}[/]")
            elif "content" in result:
                content = str(result["content"])
                for line in format_content(content, 100):
                    result_node.add_leaf(f"[#94a3b8]{line}[/]")
            elif "error" in result:
                error = str(result["error"])
                for line in format_content(error, 100):
                    result_node.add_leaf(f"[#dc2626]{line}[/]")
            else:
                # Show all keys with full values
                for key, value in result.items():
                    # Convert dict/list to JSON string for proper formatting
                    if isinstance(value, (dict, list)):
                        val_str = json.dumps(value, indent=2, ensure_ascii=False)
                    else:
                        val_str = str(value)

                    if len(val_str) > 100 or "\n" in val_str:
                        key_node = result_node.add(f"[#64748b]{key}[/]", expand=False)
                        for line in val_str.split("\n"):
                            key_node.add_leaf(f"[#94a3b8]{line}[/]")
                    else:
                        result_node.add_leaf(f"[#64748b]{key}:[/] [#94a3b8]{val_str}[/]")
        elif isinstance(result, (dict, list)):
            # Result is a raw dict/list, format as JSON
            formatted = json.dumps(result, indent=2, ensure_ascii=False)
            for line in formatted.split("\n"):
                result_node.add_leaf(f"[#94a3b8]{line}[/]")
        elif isinstance(result, str):
            for line in format_content(result, 100):
                result_node.add_leaf(f"[#94a3b8]{line}[/]")

    def _update_header(self) -> None:
        """Update header with current worker info."""
        try:
            header = self.query_one("#conv-header", Static)
            if self.conversation:
                summary = get_conversation_summary(self.conversation)
                header.update(
                    f"[bold]Conversation[/] │ {self.current_worker} │ "
                    f"{summary['turns']} turns │ ${summary['cost_usd']:.2f}"
                )
            else:
                header.update("[bold]Conversation[/] │ Select a worker")
        except Exception:
            pass

    def on_select_changed(self, event: Select.Changed) -> None:
        """Handle worker selection change."""
        if event.select.id == "worker-select" and event.value:
            self._load_conversation(str(event.value))

    def refresh_data(self) -> None:
        """Refresh conversation data."""
        if self.current_worker:
            self._load_conversation(self.current_worker)

    def select_worker(self, worker_id: str) -> None:
        """Select a specific worker programmatically."""
        try:
            select = self.query_one("#worker-select", Select)
            select.value = worker_id
            self._load_conversation(worker_id)
        except Exception:
            pass

    def action_expand_all(self) -> None:
        """Expand all nodes in the tree."""
        try:
            tree = self.query_one("#conv-tree", Tree)
            self._expand_node_recursive(tree.root)
        except Exception:
            pass

    def action_collapse_all(self) -> None:
        """Collapse all nodes in the tree."""
        try:
            tree = self.query_one("#conv-tree", Tree)
            self._collapse_node_recursive(tree.root)
            tree.root.expand()  # Keep root expanded
        except Exception:
            pass

    def _expand_node_recursive(self, node: TreeNode) -> None:
        """Expand a node and all its children recursively."""
        node.expand()
        for child in node.children:
            self._expand_node_recursive(child)

    def _collapse_node_recursive(self, node: TreeNode) -> None:
        """Collapse a node and all its children recursively."""
        for child in node.children:
            self._collapse_node_recursive(child)
        node.collapse()


    def action_expand_selected(self) -> None:
        """Expand all children of the currently selected node."""
        try:
            tree = self.query_one("#conv-tree", Tree)
            if tree.cursor_node:
                self._expand_node_recursive(tree.cursor_node)
        except Exception:
            pass

    def action_collapse_selected(self) -> None:
        """Collapse all children of the currently selected node."""
        try:
            tree = self.query_one("#conv-tree", Tree)
            if tree.cursor_node:
                for child in tree.cursor_node.children:
                    self._collapse_node_recursive(child)
                tree.cursor_node.expand()  # Keep selected node open
        except Exception:
            pass
