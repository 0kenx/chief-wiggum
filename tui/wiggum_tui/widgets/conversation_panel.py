"""Conversation panel widget showing worker chat history."""

from pathlib import Path
from typing import Any
from textual.app import ComposeResult
from textual.binding import Binding
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


import re


def format_markdown_to_rich(text: str) -> list[str]:
    """Convert markdown text to Rich markup lines for tree display."""
    lines = []
    for line in text.split("\n"):
        stripped = line.strip()
        if not stripped:
            lines.append("")
        elif stripped.startswith("### "):
            lines.append(f"[bold #a6adc8]{stripped[4:]}[/]")
        elif stripped.startswith("## "):
            lines.append(f"[bold #89b4fa]{stripped[3:]}[/]")
        elif stripped.startswith("# "):
            lines.append(f"[bold #cba6f7]{stripped[2:]}[/]")
        elif stripped.startswith(("- ", "* ")):
            content = stripped[2:]
            content = re.sub(r'\*\*(.+?)\*\*', r'[bold]\1[/]', content)
            content = re.sub(r'`(.+?)`', r'[#a6e3a1]\1[/]', content)
            lines.append(f"  [#f9e2af]•[/] {content}")
        elif stripped.startswith(("1.", "2.", "3.", "4.", "5.", "6.", "7.", "8.", "9.")):
            num_end = stripped.index(".") + 1
            content = stripped[num_end:].strip()
            content = re.sub(r'\*\*(.+?)\*\*', r'[bold]\1[/]', content)
            content = re.sub(r'`(.+?)`', r'[#a6e3a1]\1[/]', content)
            lines.append(f"  [#f9e2af]{stripped[:num_end]}[/] {content}")
        else:
            formatted = re.sub(r'\*\*(.+?)\*\*', r'[bold]\1[/]', stripped)
            formatted = re.sub(r'`(.+?)`', r'[#a6e3a1]\1[/]', formatted)
            lines.append(f"[#a6adc8]{formatted}[/]")
    return lines


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
        ("C", "collapse_all", "Collapse all"),  # Uppercase to avoid conflict
        ("+", "expand_selected", "Expand selected"),
        ("-", "collapse_selected", "Collapse selected"),
        # Vim-style navigation
        Binding("j", "cursor_down", "Down", show=False),
        Binding("k", "cursor_up", "Up", show=False),
        Binding("h", "collapse_node", "Collapse", show=False),
        Binding("l", "expand_node", "Expand", show=False),
        Binding("o", "toggle_node", "Toggle", show=False),
        Binding("g", "goto_top", "Top", show=False),
        Binding("G", "goto_bottom", "Bottom", show=False),
        Binding("ctrl+d", "half_page_down", "Half Page Down", show=False),
        Binding("ctrl+u", "half_page_up", "Half Page Up", show=False),
    ]

    DEFAULT_CSS = """
    ConversationPanel {
        height: 1fr;
        width: 100%;
        layout: vertical;
    }

    ConversationPanel .conv-controls {
        height: 3;
        background: #181825;
        padding: 0 1;
    }

    ConversationPanel Select {
        width: 48;
        margin-top: -1;
    }

    ConversationPanel Tree {
        height: 1fr;
        width: 100%;
        background: #1e1e2e;
        border: solid #45475a;
    }

    ConversationPanel .empty-message {
        text-align: center;
        color: #7f849c;
        padding: 2;
    }

    ConversationPanel .prompt-section {
        height: auto;
        max-height: 10;
        background: #181825;
        border: solid #45475a;
        padding: 1;
        margin-bottom: 1;
    }

    ConversationPanel .prompt-label {
        color: #cba6f7;
        text-style: bold;
    }

    ConversationPanel .prompt-text {
        color: #a6adc8;
    }
    """

    # Max tools to show individually before summarizing
    MAX_TOOLS_BEFORE_SUMMARY = 5

    def __init__(self, ralph_dir: Path) -> None:
        super().__init__()
        self.ralph_dir = ralph_dir
        self._workers_list: list[tuple[str, str]] = []  # (id, label)
        self.current_worker: str | None = None
        self.conversation: Conversation | None = None
        self._last_data_hash: str = ""

    def _compute_data_hash(self, conversation: Conversation | None) -> str:
        """Compute a hash of conversation data for change detection."""
        if not conversation:
            return ""
        # Include turn count and tool call count for quick change detection
        data = (
            len(conversation.turns),
            sum(len(t.tool_calls) for t in conversation.turns),
            len(conversation.results),
            sum(r.total_cost_usd for r in conversation.results),
        )
        return str(data)

    def compose(self) -> ComposeResult:
        self._load_workers()

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
        self.set_interval(3, self._refresh_workers_list)

    def _load_workers(self) -> None:
        """Load list of workers with conversations."""
        workers = scan_workers(self.ralph_dir)
        workers_with_mtime: list[tuple[str, str, float]] = []  # (id, label, mtime)

        for worker in workers:
            worker_dir = self.ralph_dir / "workers" / worker.id
            logs_dir = worker_dir / "logs"
            if logs_dir.is_dir():
                log_files = list(logs_dir.glob("*.log"))
                if log_files:
                    # Get the earliest log creation time
                    min_mtime = min(f.stat().st_mtime for f in log_files)
                    label = f"{worker.task_id} - {worker.status.value}"
                    workers_with_mtime.append((worker.id, label, min_mtime))

        # Sort by creation time ascending (oldest first)
        workers_with_mtime.sort(key=lambda x: x[2])
        self._workers_list = [(w[0], w[1]) for w in workers_with_mtime]

    def _refresh_workers_list(self) -> None:
        """Periodically refresh the worker dropdown options."""
        old_list = self._workers_list[:]
        self._load_workers()
        if old_list != self._workers_list:
            try:
                select = self.query_one("#worker-select", Select)
                select.set_options(
                    [(label, worker_id) for worker_id, label in self._workers_list]
                )
                # Restore selection if still valid
                new_ids = [w[0] for w in self._workers_list]
                if self.current_worker and self.current_worker in new_ids:
                    select.value = self.current_worker
            except Exception:
                pass

    def _load_conversation(self, worker_id: str) -> None:
        """Load conversation for a worker."""
        self.current_worker = worker_id
        worker_dir = self.ralph_dir / "workers" / worker_id
        self.conversation = parse_iteration_logs(worker_dir)
        self._last_data_hash = self._compute_data_hash(self.conversation)
        self._populate_tree()

    def _get_expanded_paths(self, node: TreeNode, path: str = "") -> set[str]:
        """Get set of paths for all expanded nodes."""
        expanded = set()
        if node.is_expanded:
            expanded.add(path)
        for i, child in enumerate(node.children):
            child_path = f"{path}/{i}"
            expanded.update(self._get_expanded_paths(child, child_path))
        return expanded

    def _restore_expanded_paths(self, node: TreeNode, expanded_paths: set[str], path: str = "") -> None:
        """Restore expanded state from saved paths."""
        if path in expanded_paths:
            node.expand()
        else:
            node.collapse()
        for i, child in enumerate(node.children):
            child_path = f"{path}/{i}"
            self._restore_expanded_paths(child, expanded_paths, child_path)

    def _populate_tree(self) -> None:
        """Populate the tree with conversation turns."""
        try:
            tree = self.query_one("#conv-tree", Tree)

            # Save expanded state before clearing
            expanded_paths = self._get_expanded_paths(tree.root)
            had_content = bool(tree.root.children)

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

            # Add initial prompt if available
            if self.conversation.user_prompt:
                prompt_node = tree.root.add("[#cba6f7]Initial Prompt[/]", expand=False)
                for line in format_content(self.conversation.user_prompt, 100):
                    prompt_node.add_leaf(f"[#a6adc8]{line}[/]")

            # Group turns by log file
            current_log_name = ""
            log_node: TreeNode | None = None
            first_log = True

            first_turn_in_log = False

            for i, turn in enumerate(self.conversation.turns):
                if turn.log_name != current_log_name:
                    current_log_name = turn.log_name
                    first_turn_in_log = True
                    # Find result for this log file
                    result = next(
                        (r for r in self.conversation.results if r.log_name == current_log_name),
                        None,
                    )
                    result_info = ""
                    if result:
                        result_info = f" │ {result.num_turns} turns │ ${result.total_cost_usd:.2f}"

                    log_node = tree.root.add(
                        f"[#cba6f7]{current_log_name}[/]{result_info}",
                        expand=first_log,
                    )
                    first_log = False
                else:
                    first_turn_in_log = False

                if log_node:
                    self._add_turn_to_tree(log_node, turn, i, first_turn_in_log)

            # Restore expanded state if we had content before, otherwise use defaults
            if had_content and expanded_paths:
                self._restore_expanded_paths(tree.root, expanded_paths)
            else:
                tree.root.expand()

        except Exception:
            pass

    def _add_turn_to_tree(self, parent: TreeNode, turn: ConversationTurn, index: int, first_in_log: bool = False) -> None:
        """Add a conversation turn to the tree."""
        # Create assistant node that groups text and tool calls
        tool_count = len(turn.tool_calls)

        # Build tool info with tool names
        if tool_count > 0:
            tool_names = sorted(set(tc.name for tc in turn.tool_calls))
            tool_info = f" │ {tool_count} tools ({','.join(tool_names)})"
        else:
            tool_info = ""

        text_preview = ""
        if turn.assistant_text:
            text_preview = truncate_text(turn.assistant_text, 60)

        assistant_label = f"[#89b4fa]Assistant[/]{tool_info}"
        if text_preview:
            assistant_label += f" [#7f849c]{text_preview}[/]"

        assistant_node = parent.add(assistant_label, expand=False)

        # Add full assistant text as expandable child if truncated
        if turn.assistant_text:
            if len(turn.assistant_text) > 60:
                # Add expandable node for full text
                text_node = assistant_node.add("[#89b4fa]Full message[/]", expand=False)
                if first_in_log:
                    for line in format_markdown_to_rich(turn.assistant_text):
                        text_node.add_leaf(line)
                else:
                    for line in format_content(turn.assistant_text, 100):
                        text_node.add_leaf(f"[#a6adc8]{line}[/]")
            else:
                if first_in_log:
                    for line in format_markdown_to_rich(turn.assistant_text):
                        assistant_node.add_leaf(line)
                else:
                    assistant_node.add_leaf(f"[#a6adc8]{turn.assistant_text}[/]")

        # Add tool calls as children of assistant node
        for tool_call in turn.tool_calls:
            # Format tool label with input preview
            input_preview = self._format_tool_input(tool_call)
            if input_preview:
                tool_label = f"[#a6e3a1]{tool_call.name}[/] [#7f849c]{input_preview}[/]"
            else:
                tool_label = f"[#a6e3a1]{tool_call.name}[/]"

            tool_node = assistant_node.add(tool_label, expand=False)

            # Add full tool input as expandable child
            self._add_tool_input_details(tool_node, tool_call)

            # Add result if present
            if tool_call.result is not None:
                self._add_tool_result(tool_node, tool_call)

    def _get_two_line_preview(self, text: str, first_line_width: int = 100, second_line_width: int = 100) -> tuple[str, str]:
        """Get a 2-line preview of text, wrapping as needed.

        Returns tuple of (line1, line2) where line2 may be empty.
        """
        text = text.strip().replace('\n', ' ').replace('  ', ' ')

        if len(text) <= first_line_width:
            return (text, "")

        # First line
        line1 = text[:first_line_width]
        remaining = text[first_line_width:].lstrip()

        # Second line (truncated with ...)
        if not remaining:
            return (line1, "")

        if len(remaining) > second_line_width - 3:
            line2 = remaining[:second_line_width - 3] + "..."
        else:
            line2 = remaining

        return (line1, line2)

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
                input_node = tool_node.add("[#7f849c]Todos[/]", expand=False)
                for todo in todos:
                    status = todo.get("status", "pending")
                    content = todo.get("content", "")
                    status_icon = {"pending": "○", "in_progress": "◐", "completed": "●"}.get(status, "?")
                    status_color = {"pending": "#7f849c", "in_progress": "#fab387", "completed": "#a6e3a1"}.get(status, "#7f849c")
                    input_node.add_leaf(f"[{status_color}]{status_icon}[/] {content}")

        elif tool_call.name == "Edit":
            # Show old_string and new_string with full content
            old_str = tool_call.input.get("old_string", "")
            new_str = tool_call.input.get("new_string", "")
            if old_str or new_str:
                input_node = tool_node.add("[#7f849c]Edit details[/]", expand=False)
                if old_str:
                    old_node = input_node.add("[#f38ba8]Old string[/]", expand=False)
                    for line in wrap_text(old_str, 100):
                        old_node.add_leaf(f"[#f38ba8]{line}[/]")
                if new_str:
                    new_node = input_node.add("[#a6e3a1]New string[/]", expand=False)
                    for line in wrap_text(new_str, 100):
                        new_node.add_leaf(f"[#a6e3a1]{line}[/]")

        elif tool_call.name == "Write":
            # Show full content with wrapping
            content = tool_call.input.get("content", "")
            if content:
                input_node = tool_node.add(f"[#7f849c]Content ({len(content.splitlines())} lines)[/]", expand=False)
                for line in wrap_text(content, 100):
                    input_node.add_leaf(f"[#a6adc8]{line}[/]")

        elif tool_call.name == "Bash":
            # Show full command with wrapping
            cmd = tool_call.input.get("command", "")
            if len(cmd) > 60:
                input_node = tool_node.add("[#7f849c]Full command[/]", expand=False)
                for line in wrap_text(cmd, 100):
                    input_node.add_leaf(f"[#a6adc8]{line}[/]")

        elif tool_call.name == "Task":
            # Show full prompt with formatting
            prompt = tool_call.input.get("prompt", "")
            if prompt:
                input_node = tool_node.add("[#7f849c]Prompt[/]", expand=False)
                for line in format_content(prompt, 100):
                    input_node.add_leaf(f"[#a6adc8]{line}[/]")

    def _add_tool_result(self, tool_node: TreeNode, tool_call: ToolCall) -> None:
        """Add tool result with expandable details."""
        result = tool_call.result

        # For Write tool, just show success/failure - content already shown in input
        if tool_call.name == "Write":
            if isinstance(result, dict):
                if result.get("success") or result.get("type") == "text":
                    tool_node.add_leaf("[#a6e3a1]Success[/]")
                elif "error" in result:
                    tool_node.add_leaf(f"[#f38ba8]Error: {result['error']}[/]")
                else:
                    tool_node.add_leaf("[#a6e3a1]Success[/]")
            else:
                tool_node.add_leaf("[#a6e3a1]Success[/]")
            return

        result_preview = format_tool_result(result, 80)

        # Determine color
        if "Error" in result_preview:
            color = "#f38ba8"
        elif result_preview == "Success":
            color = "#a6e3a1"
        else:
            color = "#a6adc8"

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
                    result_node.add_leaf(f"[#a6adc8]{line}[/]")
            elif "content" in result:
                content = str(result["content"])
                for line in format_content(content, 100):
                    result_node.add_leaf(f"[#a6adc8]{line}[/]")
            elif "error" in result:
                error = str(result["error"])
                for line in format_content(error, 100):
                    result_node.add_leaf(f"[#f38ba8]{line}[/]")
            else:
                # Show all keys with full values
                for key, value in result.items():
                    # Convert dict/list to JSON string for proper formatting
                    if isinstance(value, (dict, list)):
                        val_str = json.dumps(value, indent=2, ensure_ascii=False)
                    else:
                        val_str = str(value)

                    if len(val_str) > 100 or "\n" in val_str:
                        key_node = result_node.add(f"[#7f849c]{key}[/]", expand=False)
                        for line in val_str.split("\n"):
                            key_node.add_leaf(f"[#a6adc8]{line}[/]")
                    else:
                        result_node.add_leaf(f"[#7f849c]{key}:[/] [#a6adc8]{val_str}[/]")
        elif isinstance(result, (dict, list)):
            # Result is a raw dict/list, format as JSON
            formatted = json.dumps(result, indent=2, ensure_ascii=False)
            for line in formatted.split("\n"):
                result_node.add_leaf(f"[#a6adc8]{line}[/]")
        elif isinstance(result, str):
            for line in format_content(result, 100):
                result_node.add_leaf(f"[#a6adc8]{line}[/]")

    def on_select_changed(self, event: Select.Changed) -> None:
        """Handle worker selection change."""
        if event.select.id == "worker-select" and event.value:
            self._load_conversation(str(event.value))

    def refresh_data(self) -> None:
        """Refresh conversation data only if data changed."""
        if not self.current_worker:
            return

        worker_dir = self.ralph_dir / "workers" / self.current_worker
        new_conversation = parse_iteration_logs(worker_dir)

        # Check if data actually changed
        new_hash = self._compute_data_hash(new_conversation)
        if new_hash == self._last_data_hash:
            return  # No change, skip refresh
        self._last_data_hash = new_hash

        self.conversation = new_conversation
        self._populate_tree()

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

    def action_cursor_down(self) -> None:
        """Move cursor down (vim j)."""
        try:
            tree = self.query_one("#conv-tree", Tree)
            tree.action_cursor_down()
        except Exception:
            pass

    def action_cursor_up(self) -> None:
        """Move cursor up (vim k)."""
        try:
            tree = self.query_one("#conv-tree", Tree)
            tree.action_cursor_up()
        except Exception:
            pass

    def action_collapse_node(self) -> None:
        """Collapse current node (vim h)."""
        try:
            tree = self.query_one("#conv-tree", Tree)
            if tree.cursor_node:
                if tree.cursor_node.is_expanded:
                    tree.cursor_node.collapse()
                elif tree.cursor_node.parent:
                    # Move to parent if already collapsed
                    tree.select_node(tree.cursor_node.parent)
        except Exception:
            pass

    def action_expand_node(self) -> None:
        """Expand current node (vim l)."""
        try:
            tree = self.query_one("#conv-tree", Tree)
            if tree.cursor_node:
                if not tree.cursor_node.is_expanded and tree.cursor_node.children:
                    tree.cursor_node.expand()
                elif tree.cursor_node.children:
                    # Move to first child if already expanded
                    tree.select_node(tree.cursor_node.children[0])
        except Exception:
            pass

    def action_toggle_node(self) -> None:
        """Toggle expand/collapse current node (vim o)."""
        try:
            tree = self.query_one("#conv-tree", Tree)
            if tree.cursor_node:
                tree.cursor_node.toggle()
        except Exception:
            pass

    def action_goto_top(self) -> None:
        """Go to first node (vim gg)."""
        try:
            tree = self.query_one("#conv-tree", Tree)
            tree.select_node(tree.root)
        except Exception:
            pass

    def action_goto_bottom(self) -> None:
        """Go to last visible node (vim G)."""
        try:
            tree = self.query_one("#conv-tree", Tree)
            # Find last visible node
            last_node = tree.root
            while last_node.is_expanded and last_node.children:
                last_node = last_node.children[-1]
            tree.select_node(last_node)
        except Exception:
            pass

    def action_half_page_down(self) -> None:
        """Move half page down (vim ctrl+d)."""
        try:
            tree = self.query_one("#conv-tree", Tree)
            for _ in range(10):
                tree.action_cursor_down()
        except Exception:
            pass

    def action_half_page_up(self) -> None:
        """Move half page up (vim ctrl+u)."""
        try:
            tree = self.query_one("#conv-tree", Tree)
            for _ in range(10):
                tree.action_cursor_up()
        except Exception:
            pass
