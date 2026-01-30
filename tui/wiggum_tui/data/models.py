"""Data models for wiggum TUI."""

from dataclasses import dataclass, field
from enum import Enum
from typing import Any


class TaskStatus(Enum):
    """Task status in kanban board."""

    PENDING = "pending"
    IN_PROGRESS = "in_progress"
    PENDING_APPROVAL = "pending_approval"
    COMPLETE = "complete"
    NOT_PLANNED = "not_planned"
    FAILED = "failed"


class WorkerStatus(Enum):
    """Worker execution status."""

    RUNNING = "running"
    STOPPED = "stopped"
    COMPLETED = "completed"
    FAILED = "failed"


class LogLevel(Enum):
    """Log severity levels."""

    DEBUG = "DEBUG"
    INFO = "INFO"
    WARN = "WARN"
    ERROR = "ERROR"


@dataclass
class PipelineInfo:
    """Pipeline execution state from pipeline-config.json."""

    pipeline_name: str = ""
    step_id: str = ""
    step_idx: int = 0
    agent: str = ""  # e.g. "engineering.test-runner"

    @property
    def agent_short(self) -> str:
        """Get agent name without category prefix."""
        if "." in self.agent:
            return self.agent.split(".", 1)[1]
        return self.agent


@dataclass
class Task:
    """A task from the kanban board."""

    id: str
    title: str
    status: TaskStatus
    description: str = ""
    priority: str = "MEDIUM"  # CRITICAL, HIGH, MEDIUM, LOW
    complexity: str | None = None  # HIGH, MEDIUM, LOW (optional)
    dependencies: list[str] = field(default_factory=list)
    scope: list[str] = field(default_factory=list)
    out_of_scope: list[str] = field(default_factory=list)
    acceptance_criteria: list[str] = field(default_factory=list)
    # Runtime status for in-progress tasks
    is_running: bool | None = None  # None = not checked, True = process running, False = not running
    start_time: int | None = None  # Unix timestamp when worker started
    pipeline_info: PipelineInfo | None = None


@dataclass
class Worker:
    """A worker process."""

    id: str
    task_id: str
    timestamp: int
    pid: int | None
    status: WorkerStatus
    prd_path: str
    log_path: str
    workspace_path: str
    pr_url: str | None = None
    pipeline_info: PipelineInfo | None = None


@dataclass
class LogLine:
    """A parsed log line."""

    raw: str
    timestamp: str | None = None
    level: LogLevel | None = None
    message: str = ""


@dataclass
class TokenUsage:
    """Token usage breakdown."""

    input: int = 0
    output: int = 0
    cache_creation: int = 0
    cache_read: int = 0
    total: int = 0


@dataclass
class ContextUsage:
    """Context window usage."""

    tokens: int = 0
    size: int = 200000  # Default 200k context window
    percent: float = 0.0


@dataclass
class CostBreakdown:
    """Cost breakdown in USD."""

    input: float = 0.0
    output: float = 0.0
    cache_creation: float = 0.0
    cache_read: float = 0.0
    total: float = 0.0


@dataclass
class WorkerMetrics:
    """Metrics for a single worker."""

    worker_id: str
    status: str  # success, failed, in_progress
    time_spent: str
    time_seconds: int
    tokens: TokenUsage
    cost: float
    pr_url: str = ""
    context: ContextUsage = field(default_factory=ContextUsage)


@dataclass
class Metrics:
    """Aggregated metrics from metrics.json."""

    total_workers: int = 0
    successful_workers: int = 0
    failed_workers: int = 0
    success_rate: float = 0.0
    total_time: str = "00:00:00"
    total_time_seconds: int = 0
    total_cost: float = 0.0
    tokens: TokenUsage = field(default_factory=TokenUsage)
    cost_breakdown: CostBreakdown = field(default_factory=CostBreakdown)
    context: ContextUsage = field(default_factory=ContextUsage)
    workers: list[WorkerMetrics] = field(default_factory=list)


@dataclass
class ToolCall:
    """A tool call in a conversation."""

    name: str
    input: dict[str, Any]
    result: Any = None


@dataclass
class ConversationTurn:
    """A turn in a conversation (assistant + tool calls)."""

    iteration: int
    assistant_text: str | None = None
    tool_calls: list[ToolCall] = field(default_factory=list)
    timestamp: str | None = None
    log_name: str = ""


@dataclass
class IterationResult:
    """Result metrics for an iteration."""

    iteration: int
    subtype: str  # success, max_turns_reached, etc.
    duration_ms: int = 0
    duration_api_ms: int = 0
    num_turns: int = 0
    total_cost_usd: float = 0.0
    is_error: bool = False
    usage: TokenUsage = field(default_factory=TokenUsage)
    log_name: str = ""


@dataclass
class Conversation:
    """Full conversation for a worker."""

    worker_id: str
    system_prompt: str = ""
    user_prompt: str = ""
    turns: list[ConversationTurn] = field(default_factory=list)
    results: list[IterationResult] = field(default_factory=list)
