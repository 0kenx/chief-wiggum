"""Conversation parser for iteration log files."""

import json
from pathlib import Path
from typing import Any
from .models import (
    Conversation,
    ConversationTurn,
    ToolCall,
    IterationResult,
    TokenUsage,
)


def parse_iteration_logs(worker_dir: Path) -> Conversation:
    """Parse all iteration logs for a worker.

    Args:
        worker_dir: Path to worker directory.

    Returns:
        Conversation object with all turns and results.
    """
    logs_dir = worker_dir / "logs"
    worker_id = worker_dir.name

    conversation = Conversation(worker_id=worker_id)

    if not logs_dir.is_dir():
        return conversation

    # Sort base logs by mtime, then insert -summary logs directly after their base.
    # A -summary file is only paired if a matching base log exists; otherwise it's
    # treated as a regular log and sorted by its own mtime.
    all_logs = list(logs_dir.glob("*.log"))
    base_stems = {f.stem for f in all_logs if not f.stem.endswith("-summary")}
    summary_by_base: dict[str, Path] = {}
    non_summary: list[Path] = []
    for f in all_logs:
        if f.stem.endswith("-summary"):
            base_name = f.stem.removesuffix("-summary")
            if base_name in base_stems:
                summary_by_base[base_name] = f
            else:
                non_summary.append(f)
        else:
            non_summary.append(f)
    non_summary.sort(key=lambda f: f.stat().st_mtime)
    log_files: list[Path] = []
    for base in non_summary:
        log_files.append(base)
        if base.stem in summary_by_base:
            log_files.append(summary_by_base[base.stem])

    all_entries: list[dict[str, Any]] = []
    results: list[IterationResult] = []

    for idx, log_file in enumerate(log_files):
        log_name = log_file.stem  # e.g., "iteration-0", "validation-review"
        try:
            content = log_file.read_text()
            for line in content.split("\n"):
                if not line.strip():
                    continue
                try:
                    entry = json.loads(line)
                    entry_type = entry.get("type")
                    # Tag entry with its iteration index and log name
                    entry["_iteration_idx"] = idx
                    entry["_log_name"] = log_name

                    if entry_type == "iteration_start":
                        if not conversation.system_prompt:
                            conversation.system_prompt = entry.get("system_prompt", "")
                            conversation.user_prompt = entry.get("user_prompt", "")
                    elif entry_type == "result":
                        result = _parse_result(entry)
                        result.iteration = idx  # Override with mtime-based index
                        result.log_name = log_name
                        results.append(result)
                    elif entry_type in ("assistant", "user"):
                        all_entries.append(entry)
                except json.JSONDecodeError:
                    continue
        except OSError:
            continue

    # Group messages into turns
    conversation.turns = _group_into_turns(all_entries)
    conversation.results = results

    return conversation


def _parse_result(entry: dict[str, Any]) -> IterationResult:
    """Parse a result entry into IterationResult."""
    usage_data = entry.get("usage", {})
    usage = TokenUsage(
        input=usage_data.get("input_tokens", 0),
        output=usage_data.get("output_tokens", 0),
        cache_creation=usage_data.get("cache_creation_input_tokens", 0),
        cache_read=usage_data.get("cache_read_input_tokens", 0),
    )
    usage.total = usage.input + usage.output

    return IterationResult(
        iteration=entry.get("iteration", 0),
        subtype=entry.get("subtype", ""),
        duration_ms=entry.get("duration_ms", 0),
        duration_api_ms=entry.get("duration_api_ms", 0),
        num_turns=entry.get("num_turns", 0),
        total_cost_usd=entry.get("total_cost_usd", 0.0),
        is_error=entry.get("is_error", False),
        usage=usage,
    )


def _group_into_turns(entries: list[dict[str, Any]]) -> list[ConversationTurn]:
    """Group messages into conversation turns.

    A turn consists of an assistant message (text and/or tool calls) followed by tool results.
    """
    turns: list[ConversationTurn] = []

    # Track all tool calls by ID for result linking
    all_tool_calls: dict[str, ToolCall] = {}
    # Track pending tool calls that need results (in order)
    pending_tool_ids: list[str] = []

    current_text: str | None = None
    current_tool_calls: list[ToolCall] = []
    current_timestamp: str | None = None
    current_iteration = 0
    current_log_name = ""

    def save_turn():
        nonlocal current_text, current_tool_calls, current_timestamp
        if current_text or current_tool_calls:
            turns.append(ConversationTurn(
                iteration=current_iteration,
                assistant_text=current_text,
                tool_calls=current_tool_calls.copy(),
                timestamp=current_timestamp,
                log_name=current_log_name,
            ))
        current_text = None
        current_tool_calls = []
        current_timestamp = None

    for entry in entries:
        entry_type = entry.get("type")
        entry_iteration = entry.get("_iteration_idx", 0)
        entry_log_name = entry.get("_log_name", "")

        # Skip nested messages from subagents (Task tool execution)
        # These have parent_tool_use_id set to the Task tool's ID
        if entry.get("parent_tool_use_id"):
            continue

        if entry_type == "assistant":
            current_iteration = entry_iteration
            current_log_name = entry_log_name
            message_content = entry.get("message", {}).get("content", [])

            for block in message_content:
                block_type = block.get("type")

                if block_type == "text":
                    # Text block - save previous turn and start new one
                    save_turn()
                    current_text = block.get("text", "")
                    current_timestamp = entry.get("timestamp")

                elif block_type == "tool_use":
                    # Tool use block - add to current turn
                    tool_id = block.get("id", "")
                    tool_call = ToolCall(
                        name=block.get("name", ""),
                        input=block.get("input", {}),
                    )
                    all_tool_calls[tool_id] = tool_call
                    pending_tool_ids.append(tool_id)
                    current_tool_calls.append(tool_call)
                    if not current_timestamp:
                        current_timestamp = entry.get("timestamp")

        elif entry_type == "user":
            # Tool result
            result = entry.get("tool_use_result")
            parent_id = entry.get("parent_tool_use_id")

            # If parent_tool_use_id is not set, try to extract from message.content
            if not parent_id:
                message_content = entry.get("message", {}).get("content", [])
                for block in message_content:
                    if block.get("type") == "tool_result":
                        parent_id = block.get("tool_use_id")
                        break

            if parent_id and parent_id in all_tool_calls:
                # Explicit parent ID - link to that tool call
                all_tool_calls[parent_id].result = result
                if parent_id in pending_tool_ids:
                    pending_tool_ids.remove(parent_id)
            elif pending_tool_ids:
                # No parent ID - link to first pending tool call
                first_pending = pending_tool_ids.pop(0)
                all_tool_calls[first_pending].result = result

    # Save final turn
    save_turn()

    return turns


def get_conversation_summary(conversation: Conversation) -> dict[str, Any]:
    """Get summary statistics for a conversation.

    Args:
        conversation: Conversation to summarize.

    Returns:
        Dictionary with summary statistics.
    """
    total_turns = len(conversation.turns)
    total_tool_calls = sum(len(t.tool_calls) for t in conversation.turns)

    total_cost = sum(r.total_cost_usd for r in conversation.results)
    total_duration_ms = sum(r.duration_ms for r in conversation.results)
    total_tokens = sum(
        r.usage.input + r.usage.output for r in conversation.results
    )

    return {
        "turns": total_turns,
        "tool_calls": total_tool_calls,
        "cost_usd": total_cost,
        "duration_ms": total_duration_ms,
        "tokens": total_tokens,
        "iterations": len(conversation.results),
    }


def truncate_text(text: str, max_length: int = 100) -> str:
    """Truncate text for display.

    Args:
        text: Text to truncate.
        max_length: Maximum length.

    Returns:
        Truncated text with ellipsis if needed.
    """
    if len(text) <= max_length:
        return text
    return text[: max_length - 3] + "..."


def format_tool_result(result: Any, max_length: int = 200) -> str:
    """Format a tool result for display.

    Args:
        result: The tool result (can be dict, str, or None).
        max_length: Maximum length of output.

    Returns:
        Formatted string representation.
    """
    if result is None:
        return "(no result)"

    if isinstance(result, dict):
        # Handle common result types
        if "type" in result:
            result_type = result.get("type")
            if result_type == "text":
                # File read result
                file_info = result.get("file", {})
                file_path = file_info.get("filePath", "")
                if file_path:
                    return f"Read: {file_path}"
            elif result_type == "tool_result":
                content = result.get("content", "")
                if isinstance(content, str):
                    return truncate_text(content, max_length)

        if "stdout" in result:
            return truncate_text(result["stdout"], max_length)
        if "error" in result:
            return f"Error: {truncate_text(str(result['error']), max_length)}"
        if "success" in result:
            return "Success" if result["success"] else "Failed"

        # Generic dict - show keys
        keys = list(result.keys())[:5]
        return f"{{...}} ({', '.join(keys)})"

    return truncate_text(str(result), max_length)
