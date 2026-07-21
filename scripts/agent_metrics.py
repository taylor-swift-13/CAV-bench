#!/usr/bin/env python3
"""Shared time/token accounting for stage runners.

Every stage runner (contract, verify, eval, audit) records the same two things
in its workspace ``logs/metrics.md``:

  * wall-clock time — measured by the runner around the whole stage;
  * token usage — read from the agent CLI's own structured output.

This module owns the token side so the four runners stop carrying divergent
copies. It provides:

  * ``parse_usage(agent, path)`` — agent-aware usage extraction. ``codex`` keeps
    the last ``turn.completed.usage`` in the JSONL stream; ``claude`` reads
    either result usage or assistant-message usage from stream JSON; ``kimicode``
    reads saved local session Wire ``StatusUpdate.token_usage`` events, falling
    back to context ``_usage.token_count`` entries when Wire usage is missing.
  * ``add_usage(acc, new)`` — sum usage across rounds. Solver stages
    (contract/verify) run multiple rounds; previously only the last round's
    tokens were reported. Each round is a fresh agent session, so summing the
    per-round totals gives the stage total.
  * ``usage_lines(...)`` — render the unified key set (or the approx fallback)
    as ``metrics.md`` lines, with a single ``Agent CLI`` prefix.
  * ``read_metrics_file`` / ``write_pipeline_cost_summary`` — parse the per-stage
    ``metrics.md`` files and roll them up into one pipeline-level cost summary.
"""
from __future__ import annotations

from dataclasses import dataclass, field
import json
from pathlib import Path
import re
import shutil
import time


# Canonical order for token fields. codex emits ``cached_input_tokens``; claude
# emits ``cache_creation_input_tokens`` / ``cache_read_input_tokens``. We render
# whichever are present, always in this order, then any extra int fields.
UNIFIED_USAGE_KEYS = (
    "input_tokens",
    "output_tokens",
    "total_tokens",
    "reasoning_output_tokens",
    "uncached_input_tokens",
    "cached_input_tokens",
    "cache_creation_input_tokens",
    "cache_read_input_tokens",
    "claude_stream_input_tokens",
    "claude_stream_output_tokens",
    "claude_stream_cache_creation_input_tokens",
    "claude_stream_cache_read_input_tokens",
    "claude_stream_assistant_events",
    "kimi_status_update_events",
    "kimi_context_token_count_first",
    "kimi_context_token_count_last",
    "kimi_context_token_count_max",
    "kimi_context_token_count_delta_sum",
    "kimi_context_usage_events",
    "opencode_usage_events",
)

CLAUDE_INPUT_DETAIL_KEYS = ("cache_creation_input_tokens", "cache_read_input_tokens")
CLAUDE_STREAM_INPUT_DETAIL_KEYS = (
    "claude_stream_input_tokens",
    "claude_stream_cache_creation_input_tokens",
    "claude_stream_cache_read_input_tokens",
)


def normalize_usage_totals(usage: dict[str, int] | None, agent: str) -> dict[str, int] | None:
    """Expose comparable ``input_tokens``, ``output_tokens`` and ``total_tokens``."""
    if not usage:
        return usage
    out = dict(usage)
    if agent == "claude":
        if "input_tokens" in out:
            input_detail = sum(out.get(k, 0) for k in CLAUDE_INPUT_DETAIL_KEYS)
            if input_detail:
                out.setdefault("uncached_input_tokens", out["input_tokens"])
                out["input_tokens"] = out["input_tokens"] + input_detail
        elif any(k in out for k in CLAUDE_STREAM_INPUT_DETAIL_KEYS):
            out["input_tokens"] = sum(out.get(k, 0) for k in CLAUDE_STREAM_INPUT_DETAIL_KEYS)
            out["output_tokens"] = out.get("claude_stream_output_tokens", 0)
    if not isinstance(out.get("total_tokens"), int):
        input_tokens = out.get("input_tokens")
        output_tokens = out.get("output_tokens")
        if isinstance(input_tokens, int) or isinstance(output_tokens, int):
            out["total_tokens"] = (input_tokens if isinstance(input_tokens, int) else 0) + (
                output_tokens if isinstance(output_tokens, int) else 0
            )
    return out


def token_count(path: Path | None) -> int:
    """Whitespace word count — the approximate-token fallback when no CLI usage."""
    if path is None or not path.exists():
        return 0
    return len(path.read_text(encoding="utf-8", errors="replace").split())


def parse_codex_usage(stdout_jsonl: Path | None) -> dict[str, int] | None:
    """Last ``turn.completed.usage`` object in a codex ``exec --json`` stream."""
    if stdout_jsonl is None or not stdout_jsonl.exists():
        return None
    usage = None
    for raw in stdout_jsonl.read_text(encoding="utf-8", errors="replace").splitlines():
        if not raw.strip().startswith("{"):
            continue
        try:
            obj = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if obj.get("type") == "turn.completed" and isinstance(obj.get("usage"), dict):
            usage = obj["usage"]
    if usage is None:
        return None
    return normalize_usage_totals({k: v for k, v in usage.items() if isinstance(v, int)}, "codex")


def parse_claude_usage(stdout_path: Path | None) -> dict[str, int] | None:
    """Token usage from a claude ``--print`` result.

    Handles both output formats:

      * ``--output-format json`` — one object with a top-level ``usage``;
      * ``--output-format stream-json`` — a JSONL event stream whose final
        ``{"type": "result", ...}`` event carries the cumulative ``usage``.
    """
    if stdout_path is None or not stdout_path.exists():
        return None
    text = stdout_path.read_text(encoding="utf-8", errors="replace").strip()
    if not text:
        return None
    # --output-format json: the whole file is one object.
    try:
        obj = json.loads(text)
    except json.JSONDecodeError:
        obj = None
    if isinstance(obj, dict):
        usage = obj.get("usage")
        if isinstance(usage, dict):
            return normalize_usage_totals({k: v for k, v in usage.items() if isinstance(v, int)}, "claude")
        return None
    # --output-format stream-json: prefer the final `result` event's cumulative
    # usage when present, and also expose the assistant-message stream totals.
    result_usage = None
    stream_usage: dict[str, int] = {}
    assistant_events = 0
    for raw in text.splitlines():
        raw = raw.strip()
        if not raw.startswith("{"):
            continue
        try:
            ev = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if not isinstance(ev, dict):
            continue
        if ev.get("type") == "result" and isinstance(ev.get("usage"), dict):
            result_usage = ev["usage"]
        message = ev.get("message")
        if ev.get("type") == "assistant" and isinstance(message, dict) and isinstance(message.get("usage"), dict):
            assistant_events += 1
            for key, value in message["usage"].items():
                if isinstance(value, int):
                    stream_usage[key] = stream_usage.get(key, 0) + value
    usage: dict[str, int] = {}
    if isinstance(result_usage, dict):
        usage.update({k: v for k, v in result_usage.items() if isinstance(v, int)})
    for key, value in stream_usage.items():
        usage[f"claude_stream_{key}"] = value
    if assistant_events:
        usage["claude_stream_assistant_events"] = assistant_events
    if not usage:
        return None
    return normalize_usage_totals(usage, "claude")


def parse_kimicode_wire_usage(wire_jsonl: Path | None) -> dict[str, int] | None:
    """Kimi Code token accounting from saved Wire ``StatusUpdate`` events."""
    if wire_jsonl is None or not wire_jsonl.exists():
        return None
    input_other = 0
    output = 0
    input_cache_read = 0
    input_cache_creation = 0
    events = 0
    for raw in wire_jsonl.read_text(encoding="utf-8", errors="replace").splitlines():
        raw = raw.strip()
        if not raw.startswith("{"):
            continue
        try:
            obj = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if not isinstance(obj, dict):
            continue
        message = obj.get("message")
        if not isinstance(message, dict) or message.get("type") != "StatusUpdate":
            continue
        payload = message.get("payload")
        if not isinstance(payload, dict) or not isinstance(payload.get("token_usage"), dict):
            continue
        token_usage = payload["token_usage"]
        input_other += token_usage.get("input_other", 0) if isinstance(token_usage.get("input_other"), int) else 0
        output += token_usage.get("output", 0) if isinstance(token_usage.get("output"), int) else 0
        input_cache_read += (
            token_usage.get("input_cache_read", 0) if isinstance(token_usage.get("input_cache_read"), int) else 0
        )
        input_cache_creation += (
            token_usage.get("input_cache_creation", 0)
            if isinstance(token_usage.get("input_cache_creation"), int)
            else 0
        )
        events += 1
    if not events:
        return None
    return normalize_usage_totals(
        {
            "input_tokens": input_other + input_cache_read + input_cache_creation,
            "output_tokens": output,
            "uncached_input_tokens": input_other,
            "cached_input_tokens": input_cache_read,
            "cache_creation_input_tokens": input_cache_creation,
            "kimi_status_update_events": events,
        },
        "kimicode",
    )


def parse_kimicode_context_usage(context_jsonl: Path | None) -> dict[str, int] | None:
    """Kimi Code context-token accounting from a saved ``context*.jsonl``.

    Kimi 1.41.0 does not emit input/output token usage in ``--output-format
    stream-json``. Its local session context records ``{"role": "_usage",
    "token_count": ...}`` entries instead. These are cumulative context-token
    counts. We attribute each usage delta to output when the preceding message
    is an assistant message, and to input otherwise; first/last/max are kept as
    Kimi-specific detail fields.
    """
    if context_jsonl is None or not context_jsonl.exists():
        return None
    counts: list[int] = []
    input_tokens = 0
    output_tokens = 0
    previous_count: int | None = None
    previous_role: str | None = None
    for raw in context_jsonl.read_text(encoding="utf-8", errors="replace").splitlines():
        raw = raw.strip()
        if not raw.startswith("{"):
            continue
        try:
            obj = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if not isinstance(obj, dict):
            continue
        role = obj.get("role")
        if role == "_usage" and isinstance(obj.get("token_count"), int):
            current = obj["token_count"]
            counts.append(current)
            delta = current if previous_count is None else max(0, current - previous_count)
            if previous_role == "assistant":
                output_tokens += delta
            else:
                input_tokens += delta
            previous_count = current
        elif isinstance(role, str) and role != "_usage":
            previous_role = role
    if not counts:
        return None
    delta_sum = 0
    prev = counts[0]
    for current in counts[1:]:
        if current >= prev:
            delta_sum += current - prev
        prev = current
    return normalize_usage_totals({
        "input_tokens": input_tokens,
        "output_tokens": output_tokens,
        "kimi_context_token_count_first": counts[0],
        "kimi_context_token_count_last": counts[-1],
        "kimi_context_token_count_max": max(counts),
        "kimi_context_token_count_delta_sum": delta_sum,
        "kimi_context_usage_events": len(counts),
    }, "kimicode")


def parse_opencode_usage(stdout_jsonl: Path | None) -> dict[str, int] | None:
    """Sum token deltas from OpenCode ``step-finish`` JSON events."""
    if stdout_jsonl is None or not stdout_jsonl.exists():
        return None
    uncached_input = 0
    output = 0
    reasoning = 0
    cache_read = 0
    cache_write = 0
    events = 0
    for raw in stdout_jsonl.read_text(encoding="utf-8", errors="replace").splitlines():
        raw = raw.strip()
        if not raw.startswith("{"):
            continue
        try:
            obj = json.loads(raw)
        except json.JSONDecodeError:
            continue
        part = obj.get("part") if isinstance(obj, dict) else None
        if not isinstance(part, dict) or part.get("type") != "step-finish":
            continue
        tokens = part.get("tokens")
        if not isinstance(tokens, dict):
            continue
        events += 1
        uncached_input += tokens.get("input", 0) if isinstance(tokens.get("input"), int) else 0
        output += tokens.get("output", 0) if isinstance(tokens.get("output"), int) else 0
        reasoning += tokens.get("reasoning", 0) if isinstance(tokens.get("reasoning"), int) else 0
        cache = tokens.get("cache")
        if isinstance(cache, dict):
            cache_read += cache.get("read", 0) if isinstance(cache.get("read"), int) else 0
            cache_write += cache.get("write", 0) if isinstance(cache.get("write"), int) else 0
    if not events:
        return None
    input_tokens = uncached_input + cache_read + cache_write
    return {
        "input_tokens": input_tokens,
        "output_tokens": output,
        "total_tokens": input_tokens + output + reasoning,
        "reasoning_output_tokens": reasoning,
        "uncached_input_tokens": uncached_input,
        "cached_input_tokens": cache_read,
        "cache_creation_input_tokens": cache_write,
        "opencode_usage_events": events,
    }


def find_saved_kimicode_context(logs_dir: Path) -> Path | None:
    candidates = sorted(
        logs_dir.glob("kimi_session_context_*.jsonl"),
        key=lambda p: p.stat().st_mtime if p.exists() else 0,
        reverse=True,
    )
    return candidates[0] if candidates else None


def find_saved_kimicode_wire(logs_dir: Path) -> Path | None:
    candidates = sorted(
        logs_dir.glob("kimi_session_wire_*.jsonl"),
        key=lambda p: p.stat().st_mtime if p.exists() else 0,
        reverse=True,
    )
    return candidates[0] if candidates else None


def capture_kimicode_context_usage(
    *,
    logs_dir: Path,
    started_at: float,
    ended_at: float | None = None,
    needles: list[str] | None = None,
) -> Path | None:
    """Copy Kimi session usage files touched by this run into ``logs_dir``.

    Kimi currently stores session files under ``~/.kimi/sessions`` even when
    XDG dirs are redirected. We select context files modified during the agent
    run window, copy the matching ``context*.jsonl`` and sibling ``wire.jsonl``,
    and parse the saved copies later without depending on global Kimi state.
    """
    kimi_sessions = Path.home() / ".kimi" / "sessions"
    if not kimi_sessions.exists():
        return None
    upper = ended_at if ended_at is not None else time.time()
    candidates: list[Path] = []
    for path in kimi_sessions.glob("*/*/context*.jsonl"):
        try:
            mtime = path.stat().st_mtime
        except OSError:
            continue
        if started_at - 5 <= mtime <= upper + 30:
            candidates.append(path)
    if not candidates:
        return None
    matched: list[Path] = []
    for path in candidates:
        if not needles:
            break
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        if any(needle and needle in text for needle in needles):
            matched.append(path)
    source = max(matched or candidates, key=lambda p: p.stat().st_mtime)
    out = logs_dir / f"kimi_session_context_{int(source.stat().st_mtime)}.jsonl"
    try:
        shutil.copy2(source, out)
    except OSError:
        return None
    wire_source = source.parent / "wire.jsonl"
    if wire_source.exists():
        wire_out = logs_dir / f"kimi_session_wire_{int(wire_source.stat().st_mtime)}.jsonl"
        try:
            shutil.copy2(wire_source, wire_out)
        except OSError:
            pass
    return out


def extract_claude_last_message(stdout_path: Path | None) -> str | None:
    """Final assistant text from a claude ``--print`` result file.

    For ``--output-format json`` it is the object's ``result``; for
    ``--output-format stream-json`` it is the ``result`` event's ``result``.
    Returns None when no result text is present (caller falls back to raw stdout).
    """
    if stdout_path is None or not stdout_path.exists():
        return None
    text = stdout_path.read_text(encoding="utf-8", errors="replace").strip()
    if not text:
        return None
    try:
        obj = json.loads(text)
    except json.JSONDecodeError:
        obj = None
    if isinstance(obj, dict):
        result = obj.get("result")
        return result if isinstance(result, str) else None
    last = None
    for raw in text.splitlines():
        raw = raw.strip()
        if not raw.startswith("{"):
            continue
        try:
            ev = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if isinstance(ev, dict) and ev.get("type") == "result" and isinstance(ev.get("result"), str):
            last = ev["result"]
    return last


def extract_opencode_last_message(stdout_path: Path | None) -> str | None:
    """Best-effort final assistant text from OpenCode JSON events."""
    if stdout_path is None or not stdout_path.exists():
        return None
    last: str | None = None
    for raw in stdout_path.read_text(encoding="utf-8", errors="replace").splitlines():
        raw = raw.strip()
        if not raw.startswith("{"):
            continue
        try:
            obj = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if not isinstance(obj, dict):
            continue
        candidates: list[str] = []
        for key in ("result", "text", "content"):
            value = obj.get(key)
            if isinstance(value, str) and value.strip():
                candidates.append(value)
        message = obj.get("message")
        if isinstance(message, str) and message.strip():
            candidates.append(message)
        elif isinstance(message, dict):
            for key in ("text", "content"):
                value = message.get(key)
                if isinstance(value, str) and value.strip():
                    candidates.append(value)
        if candidates:
            last = candidates[-1]
    return last


def cleanup_opencode_heavy_artifacts(
    *,
    logs_dir: Path,
    data_home: str | None,
    config_home: str | None = None,
    state_home: str | None = None,
    cache_home: str | None = None,
) -> list[Path]:
    """Remove task-local OpenCode caches after stdout and timeline capture."""
    removed: list[Path] = []
    logs_root = logs_dir.resolve(strict=False)
    candidates = [logs_dir / "opencode_artifacts", logs_dir / ".tmp"]
    for home in (data_home, config_home, state_home, cache_home):
        if not home:
            continue
        path = Path(home)
        try:
            path.resolve(strict=False).relative_to(logs_root)
        except (OSError, ValueError):
            candidates.extend((path / "opencode", path / ".bun"))
        else:
            candidates.append(path)
    seen: set[str] = set()
    for path in sorted(candidates, key=lambda item: len(item.parts), reverse=True):
        key = str(path)
        if key in seen or (not path.exists() and not path.is_symlink()):
            continue
        seen.add(key)
        try:
            if path.is_dir() and not path.is_symlink():
                shutil.rmtree(path)
            else:
                path.unlink()
        except OSError:
            continue
        removed.append(path)
    return removed


def parse_usage(agent: str, stdout_path: Path | None) -> dict[str, int] | None:
    """Dispatch usage parsing by agent backend."""
    if agent == "claude":
        return parse_claude_usage(stdout_path)
    if agent == "kimicode":
        if stdout_path is None:
            return None
        return parse_kimicode_wire_usage(find_saved_kimicode_wire(stdout_path.parent)) or parse_kimicode_context_usage(
            find_saved_kimicode_context(stdout_path.parent)
        )
    if agent == "opencode":
        return parse_opencode_usage(stdout_path)
    return parse_codex_usage(stdout_path)


def add_usage(acc: dict[str, int] | None, new: dict[str, int] | None) -> dict[str, int] | None:
    """Sum two usage dicts field-by-field. None-safe; returns None iff both None."""
    if not acc and not new:
        return None
    out: dict[str, int] = dict(acc) if acc else {}
    for key, value in (new or {}).items():
        if isinstance(value, int):
            out[key] = out.get(key, 0) + value
    return out


def usage_lines(
    usage: dict[str, int] | None,
    *,
    prefix: str = "Agent CLI",
    prompt_path: Path | None = None,
    last_message_path: Path | None = None,
) -> list[str]:
    """metrics.md lines for token usage, or the approx fallback when unavailable."""
    if usage:
        ordered = [k for k in UNIFIED_USAGE_KEYS if k in usage]
        extras = sorted(k for k in usage if k not in UNIFIED_USAGE_KEYS)
        return [f"- {prefix} {key}: `{usage[key]}`" for key in (*ordered, *extras)]
    lines = []
    if prompt_path is not None:
        lines.append(f"- Approx prompt tokens: `{token_count(prompt_path)}`")
    if last_message_path is not None:
        lines.append(f"- Approx last-message tokens: `{token_count(last_message_path)}`")
    return lines


# --- pipeline roll-up -------------------------------------------------------

_STAGE_RE = re.compile(r"^- Stage:\s*`([^`]*)`")
_STATUS_RE = re.compile(r"^- Status:\s*`([^`]*)`")
_AGENT_RE = re.compile(r"^- Agent:\s*`([^`]*)`")
_MODEL_RE = re.compile(r"^- Model:\s*`([^`]*)`")
_REASONING_RE = re.compile(r"^- Reasoning effort:\s*`([^`]*)`")
_WALL_RE = re.compile(r"^- Wall-clock time \(seconds\):\s*`([0-9.]+)`")
# matches "- Agent CLI input_tokens: `123`" and the legacy "- Codex CLI ..." form
_USAGE_RE = re.compile(r"^- (?:Agent|Codex) CLI (\w+):\s*`(\d+)`")
_APPROX_RE = re.compile(r"^- Approx .*tokens:\s*`(\d+)`")


@dataclass
class StageMetrics:
    workspace: Path
    stage: str = "?"
    status: str | None = None
    agent: str | None = None
    model: str | None = None
    reasoning_effort: str | None = None
    wall_seconds: float = 0.0
    usage: dict[str, int] = field(default_factory=dict)
    usage_is_approx: bool = False


def read_metrics_file(workspace: Path) -> StageMetrics | None:
    """Parse ``<workspace>/logs/metrics.md`` into a StageMetrics, or None."""
    metrics = workspace / "logs" / "metrics.md"
    if not metrics.exists():
        return None
    sm = StageMetrics(workspace=workspace)
    for line in metrics.read_text(encoding="utf-8", errors="replace").splitlines():
        if m := _STAGE_RE.match(line):
            sm.stage = m.group(1)
        elif m := _STATUS_RE.match(line):
            sm.status = m.group(1)
        elif m := _AGENT_RE.match(line):
            sm.agent = m.group(1)
        elif m := _MODEL_RE.match(line):
            sm.model = m.group(1)
        elif m := _REASONING_RE.match(line):
            sm.reasoning_effort = m.group(1)
        elif m := _WALL_RE.match(line):
            sm.wall_seconds = float(m.group(1))
        elif m := _USAGE_RE.match(line):
            sm.usage[m.group(1)] = int(m.group(2))
        elif _APPROX_RE.match(line):
            sm.usage_is_approx = True
    return sm


def write_pipeline_cost_summary(workspaces: list[Path], out_path: Path) -> Path:
    """Sum wall-clock + tokens across stage workspaces into one cost_summary.md.

    Stages run serially in the pipeline, so the wall-clock total is the sum of
    per-stage wall-clock (orchestrator overhead excluded).
    Token totals cover only stages that reported real CLI usage; stages that
    only had word-count approximations are flagged, not summed into the total.
    """
    stages: list[StageMetrics] = []
    seen: set[Path] = set()
    for ws in workspaces:
        if ws in seen:
            continue
        seen.add(ws)
        sm = read_metrics_file(ws)
        if sm is not None:
            stages.append(sm)

    total_wall = sum(s.wall_seconds for s in stages)
    total_usage: dict[str, int] | None = None
    for s in stages:
        if s.usage:
            total_usage = add_usage(total_usage, s.usage)
    approx_only = [s for s in stages if not s.usage and s.usage_is_approx]

    key_order = [k for k in UNIFIED_USAGE_KEYS if total_usage and k in total_usage]
    if total_usage:
        key_order += sorted(k for k in total_usage if k not in UNIFIED_USAGE_KEYS)

    header = ["Stage", "Agent", "Model", "Reasoning effort", "Status", "Wall (s)", *key_order]
    body_rows = [
        [
            s.stage,
            s.agent or "?",
            s.model if s.model is not None else "?",
            s.reasoning_effort or "?",
            s.status or "?",
            f"{s.wall_seconds:.2f}",
         *[str(s.usage.get(k, "—")) for k in key_order]]
        for s in stages
    ]
    body_rows.append([
        "**total**", "", "", "", "", f"**{total_wall:.2f}**",
        *[f"**{(total_usage or {}).get(k, 0)}**" for k in key_order],
    ])

    lines = [
        "# Pipeline Cost Summary",
        "",
        f"- Stages accounted: `{len(stages)}`",
        f"- Total wall-clock (sum of serial stages, seconds): `{total_wall:.2f}`",
    ]
    if total_usage:
        lines.append("- Total tokens: " + ", ".join(f"{k}=`{total_usage[k]}`" for k in key_order))
    else:
        lines.append("- Total tokens: `0` (no stage reported CLI usage)")
    if approx_only:
        names = ", ".join(f"{s.stage} (`{s.workspace.name}`)" for s in approx_only)
        lines.append(f"- Approx-only stages (excluded from token total): {names}")
    lines.append("")
    lines.append("| " + " | ".join(header) + " |")
    lines.append("|" + "|".join("---" for _ in header) + "|")
    for row in body_rows:
        lines.append("| " + " | ".join(row) + " |")
    lines.append("")

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return out_path
