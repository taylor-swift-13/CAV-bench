#!/usr/bin/env python3
"""Generate paper figures from the current CAV-Bench result directories."""

from __future__ import annotations

import csv
import difflib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import matplotlib.patches as patches
import matplotlib.pyplot as plt
import numpy as np
import requests
from cairosvg import svg2png
from matplotlib.offsetbox import AnnotationBbox, OffsetImage
from matplotlib.path import Path as MplPath
from PIL import Image, ImageDraw


PROJECT_ROOT = Path(__file__).resolve().parents[1]
RESULTS_ROOT = Path("/home/yangfp/CAV/C/CAV-bench/results")
CAV_BENCH_ROOT = RESULTS_ROOT.parent
FIGURES_DIR = PROJECT_ROOT / "figures"
ICONS_DIR = FIGURES_DIR / "icons"

# ---------------------------------------------------------------------------
# Unified figure palette: steel-blue + warm gold.
#
# One harmonized family drives every result chart and the task-design diagram:
# an analogous cool ramp (steel-blue -> slate -> teal) plus a single warm gold
# accent. Brand icons keep their identity, while the bars they sit next to use
# these coordinated tones so nothing clashes. (Figure 2's raster illustration
# and its code-panel colors are intentionally left untouched in LaTeX.)
# ---------------------------------------------------------------------------

# Steel-blue ramp for ordered / quantitative encodings.
STEEL_900 = "#1B3A5B"   # deepest steel
STEEL_700 = "#2C5F8A"   # primary steel
STEEL_500 = "#5A8CB5"   # light steel
STEEL_300 = "#9FBDD8"
STEEL_100 = "#D6E4F0"
SLATE = "#64748B"       # neutral cool
TEAL = "#5B9BB5"        # secondary blue (name retained for compatibility)
GOLD = "#82B6CA"        # light blue accent (name retained for compatibility)

# Model colors. GPT variants use steel-blue tints and GLM a neutral slate, so
# they sit inside the harmonized family; DeepSeek and Kimi use their official
# brand blues (the DeepSeek icon is rendered in this exact color).
GPT_BLACK = STEEL_900       # legacy name; GPT-5.5 xhigh
GPT_XHIGH = STEEL_900
GPT_MEDIUM = STEEL_700
GPT_LEGACY = STEEL_500
GPT_MINI = "#7A8FA0"       # muted blue-gray
CLAUDE_ORANGE = GOLD
GLM_GRAY = SLATE
KIMI_BLUE = "#3F8EC7"        # muted Kimi blue
DEEPSEEK_BLUE = "#506FAF"    # muted DeepSeek blue

# Shared paper palette (legacy names retained, harmonized values).
PAPER_BLUE = STEEL_700
PAPER_BLUE_DARK = STEEL_900
PAPER_BLUE_LIGHT = STEEL_100
PAPER_GRAY_DARK = "#52606D"
PAPER_GRAY_MID = "#93A1B0"
PAPER_GRAY_LIGHT = "#E4E7EB"

# Verification-stage ramp: contract -> annotation -> proof (steel ramp), plus a
# neutral gray for the deterministic audit so it reads as mechanical, not
# generative. These solid tones are used for stage bars (branch figure); the
# task-design boxes pair them with pale fills.
TASK_CONTRACT = "#2F6F8A"
TASK_CONTRACT_LIGHT = "#E8F0F7"
TASK_ANNOTATION = "#5B9BB5"
TASK_ANNOTATION_LIGHT = "#CFE0EF"
TASK_PROOF = "#82B6CA"
TASK_PROOF_LIGHT = "#A9C4DE"
TASK_AUDIT = "#94A3B8"
TASK_AUDIT_LIGHT = "#ECEFF2"
TASK_SCOPE_END_TO_END = "#2F6F8A"
TASK_SCOPE_PRIMARY = "#5B9BB5"
TASK_SCOPE_PROOF_ONLY = "#82B6CA"

# Outcome ramp: correct (deep steel) -> wrong (mid steel-gray) -> timeout
# (light steel-gray + hatch). Single-hue ordinal ramp validated for light-end
# contrast (>=2:1 on white) and monotone lightness.
OUTCOME_CORRECT = STEEL_700
OUTCOME_WRONG = "#7A92A8"
OUTCOME_TIMEOUT = "#A3B4C6"
OUTCOME_REMAINDER = "#E4E7EB"
OK_GREEN = OUTCOME_CORRECT
OK_LIGHT = STEEL_100
ISSUE_BLUE = STEEL_700
ISSUE_LIGHT = STEEL_100
MISMATCH_YELLOW = PAPER_GRAY_MID
FAIL_RED = OUTCOME_TIMEOUT
FAIL_LIGHT = PAPER_GRAY_LIGHT
NEUTRAL_DARK = "#1F2933"
NEUTRAL_GRAY = SLATE
NEUTRAL_LIGHT = "#DDE3EA"
PANEL_EDGE = "#52606D"

# Harness triad: three well-separated tones from the same family.
HARNESS_CODEX_GRAY = STEEL_900
HARNESS_OPENCODE_BLUE = TEAL
HARNESS_CLAUDE_ORANGE = GOLD

# Canonical visual identities.  Paper figures import these dictionaries so a
# model never changes color when the harness or reasoning effort changes, and
# harness identity remains separate from model identity.
CLAUDE_BRAND = "#82B6CA"  # paper-facing Claude blue
OPENAI_INK = "#111111"

MODEL_STYLES = {
    "GPT-5.5": {"color": GPT_XHIGH, "icon": "openai"},
    "GPT-5.4": {"color": GPT_LEGACY, "icon": "openai"},
    "GPT-5.4-mini": {"color": GPT_MINI, "icon": "openai"},
    "GLM-5.2": {"color": GLM_GRAY, "icon": "zhipu"},
    "DeepSeek-V4-Pro": {"color": DEEPSEEK_BLUE, "icon": "deepseek"},
    "Kimi for Coding": {"color": KIMI_BLUE, "icon": "kimi"},
}

HARNESS_STYLES = {
    "Codex": {"color": HARNESS_CODEX_GRAY, "icon": "codex", "icon_color": OPENAI_INK},
    "Codex CLI": {"color": HARNESS_CODEX_GRAY, "icon": "codex", "icon_color": OPENAI_INK},
    "OpenCode": {"color": HARNESS_OPENCODE_BLUE, "icon": "opencode", "icon_color": OPENAI_INK},
    "Claude Code": {"color": HARNESS_CLAUDE_ORANGE, "icon": "claude_code", "icon_color": CLAUDE_BRAND},
    "Kimi Code": {"color": KIMI_BLUE, "icon": "kimi", "icon_color": KIMI_BLUE},
}

TEXT_DARK = "#1F2933"
TEXT_MID = "#3E4C59"
TEXT_MUTED = "#7B8794"
GRID = "#E4E7EB"
FRAME = "#CBD2D9"
WRONG_FILL = OUTCOME_WRONG
TIMEOUT_FILL = OUTCOME_TIMEOUT

# Cost columns share one steel ramp (dark -> light across the metric columns)
# so every row reads in the same family; model identity stays with the icon
# and the row label instead of the bar hue.
COST_COLUMN_RAMP = [STEEL_900, STEEL_700, STEEL_500, STEEL_300]

# Shared table / panel chrome.
PANEL_HEADER = "#EEF2F6"   # header band
PANEL_ZEBRA = "#F7F9FB"    # alternating-row tint
PANEL_RULE = "#CBD5E1"     # thin rules / axes
HIGHLIGHT_BAND = "#EEF6F9" # faint blue band for the primary-task highlight
HIGHLIGHT_ACCENT = GOLD
COLUMN_WIDTH_IN = 3.35
FIGSIZE_OUTCOMES = (COLUMN_WIDTH_IN, 2.35)
FIGSIZE_COST = (COLUMN_WIDTH_IN, 2.30)
FIGSIZE_BRANCH = (COLUMN_WIDTH_IN, 2.35)
FIGSIZE_HARNESS = (COLUMN_WIDTH_IN, 1.75)
FIG_DPI = 220

plt.rcParams.update(
    {
        "font.family": "serif",
        "font.serif": ["Times New Roman", "Nimbus Roman", "DejaVu Serif"],
        "font.size": 8.2,
        "text.color": TEXT_DARK,
        "axes.labelcolor": TEXT_MID,
        "axes.linewidth": 0.6,
        "axes.edgecolor": PANEL_EDGE,
        "xtick.color": TEXT_MUTED,
        "ytick.color": TEXT_DARK,
        "grid.color": GRID,
        "grid.linewidth": 0.55,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
        "hatch.linewidth": 0.35,
    }
)


@dataclass(frozen=True)
class Series:
    label: str
    short_label: str
    result_dir: Path
    color: str
    icon: str


@dataclass(frozen=True)
class HarnessSeries:
    model: str
    harness: str
    result_dir: Path
    color: str


SERIES = [
    Series(
        label="Codex GPT-5.5 xhigh",
        short_label="5.5-X",
        result_dir=RESULTS_ROOT / "codex/gpt-5.5/xhigh",
        color=MODEL_STYLES["GPT-5.5"]["color"],
        icon="openai",
    ),
    Series(
        label="Codex GPT-5.5 medium",
        short_label="5.5-M",
        result_dir=RESULTS_ROOT / "codex/gpt-5.5/medium",
        color=MODEL_STYLES["GPT-5.5"]["color"],
        icon="openai",
    ),
    Series(
        label="Codex GPT-5.4 medium",
        short_label="5.4-M",
        result_dir=RESULTS_ROOT / "codex/gpt-5.4/medium",
        color=MODEL_STYLES["GPT-5.4"]["color"],
        icon="openai",
    ),
    Series(
        label="Claude Code GLM-5.2",
        short_label="GLM",
        result_dir=RESULTS_ROOT / "claude/glm-5.2/api",
        color=MODEL_STYLES["GLM-5.2"]["color"],
        icon="zhipu",
    ),
    Series(
        label="Claude Code DeepSeek-V4-Pro",
        short_label="DS",
        result_dir=RESULTS_ROOT / "claude/deepseek-v4-pro/api",
        color=MODEL_STYLES["DeepSeek-V4-Pro"]["color"],
        icon="deepseek",
    ),
    Series(
        label="Kimi Code",
        short_label="Kimi",
        result_dir=RESULTS_ROOT / "kimicode/kimi-code__kimi-for-coding/thinking",
        color=MODEL_STYLES["Kimi for Coding"]["color"],
        icon="kimi",
    ),
]

MODEL_ORDER = {series.label: index for index, series in enumerate(SERIES)}


HARNESS_SERIES = [
    HarnessSeries(
        model="GLM-5.2",
        harness="Codex CLI",
        result_dir=RESULTS_ROOT / "codex/glm-5.2/api",
        color=HARNESS_CODEX_GRAY,
    ),
    HarnessSeries(
        model="GLM-5.2",
        harness="OpenCode",
        result_dir=RESULTS_ROOT / "opencode/glm-5.2/api",
        color=HARNESS_OPENCODE_BLUE,
    ),
    HarnessSeries(
        model="GLM-5.2",
        harness="Claude Code",
        result_dir=RESULTS_ROOT / "claude/glm-5.2/api",
        color=HARNESS_CLAUDE_ORANGE,
    ),
    HarnessSeries(
        model="DeepSeek-V4-Pro",
        harness="Codex CLI",
        result_dir=RESULTS_ROOT / "codex/deepseek-v4-pro/api",
        color=HARNESS_CODEX_GRAY,
    ),
    HarnessSeries(
        model="DeepSeek-V4-Pro",
        harness="OpenCode",
        result_dir=RESULTS_ROOT / "opencode/deepseek-v4-pro/api",
        color=HARNESS_OPENCODE_BLUE,
    ),
    HarnessSeries(
        model="DeepSeek-V4-Pro",
        harness="Claude Code",
        result_dir=RESULTS_ROOT / "claude/deepseek-v4-pro/api",
        color=HARNESS_CLAUDE_ORANGE,
    ),
]

HARNESS_CLAUDE_SHARED_TASKS = [
    "p052_below_threshold",
    "p082_prime_length",
    "p138_is_equal_to_sum_even",
    "p139_special_factorial",
]

GLM52_HARNESS_SERIES = [
    HarnessSeries(
        model="GLM-5.2",
        harness="Codex CLI",
        result_dir=RESULTS_ROOT / "codex/glm-5.2/api",
        color=HARNESS_CODEX_GRAY,
    ),
    HarnessSeries(
        model="GLM-5.2",
        harness="OpenCode",
        result_dir=RESULTS_ROOT / "opencode/glm-5.2/api",
        color=HARNESS_OPENCODE_BLUE,
    ),
    HarnessSeries(
        model="GLM-5.2",
        harness="Claude Code",
        result_dir=RESULTS_ROOT / "claude/glm-5.2/api",
        color=HARNESS_CLAUDE_ORANGE,
    ),
]


ICON_URLS = {
    "openai": "https://cdn.jsdelivr.net/npm/simple-icons/icons/openai.svg",
    "codex": "https://cdn.jsdelivr.net/npm/@lobehub/icons-static-svg/icons/codex-color.svg",
    "claude": "https://cdn.jsdelivr.net/npm/simple-icons/icons/claude.svg",
    "deepseek": "https://cdn.jsdelivr.net/npm/simple-icons/icons/deepseek.svg",
    "zhipu": "https://z-cdn.chatglm.cn/z-blog/z-icon.svg",
    "kimi": "https://moonshotai.github.io/Branding-Guide/scenarios/03-icon-without-kimi/kimi-icon-round.png",
    # Official OpenCode application mark from the project's source tree.
    "opencode": "https://raw.githubusercontent.com/anomalyco/opencode/dev/packages/ui/src/assets/favicon/favicon-v3.svg",
}

# Primary-outcomes table cells: harness (official mark), model (official mark),
# and reasoning-effort chip per benchmark configuration.
PRIMARY_ROW_META = {
    "Codex GPT-5.5 xhigh": ("Codex", ("codex", OPENAI_INK), "GPT-5.5", ("openai", MODEL_STYLES["GPT-5.5"]["color"]), "xhigh"),
    "Codex GPT-5.5 medium": ("Codex", ("codex", OPENAI_INK), "GPT-5.5", ("openai", MODEL_STYLES["GPT-5.5"]["color"]), "medium"),
    "Codex GPT-5.4 medium": ("Codex", ("codex", OPENAI_INK), "GPT-5.4", ("openai", MODEL_STYLES["GPT-5.4"]["color"]), "medium"),
    "Claude Code GLM-5.2": ("Claude Code", ("claude_code", CLAUDE_BRAND), "GLM-5.2", ("zhipu", MODEL_STYLES["GLM-5.2"]["color"]), "default"),
    "Claude Code DeepSeek-V4-Pro": (
        "Claude Code",
        ("claude_code", CLAUDE_BRAND),
        "DeepSeek-V4-Pro",
        ("deepseek", DEEPSEEK_BLUE),
        "default",
    ),
    "Kimi Code": ("Kimi Code", ("kimi", KIMI_BLUE), "Kimi for Coding", ("kimi", KIMI_BLUE), "default"),
}

# Effort chips: darker steel = more reasoning; thinking mode teal, API default slate.
EFFORT_CHIP = {
    "xhigh": (STEEL_900, "#E8F0F7"),
    "high": (STEEL_700, "#EAF1F8"),
    "medium": (STEEL_500, "#EDF3F9"),
    "low": (STEEL_300, "#F1F5FA"),
    "thinking": (TEAL, "#E9F3F2"),
    "default": (SLATE, "#F0F2F5"),
}

# Shared x-coordinates of the harness / model / effort cells in the primary
# tables. Both tables use the same data-unit scale (~0.036 in per unit), so the
# left block reads identically across figures.
CONFIG_HARNESS_X = -68.0
CONFIG_MODEL_X = -45.0
CONFIG_EFFORT_CX = -9.0


def draw_config_header(ax, header_y: float) -> None:
    ax.text(CONFIG_HARNESS_X, header_y, "Harness", ha="left", va="center", fontsize=7.5, color=TEXT_MID)
    ax.text(CONFIG_MODEL_X, header_y, "Model", ha="left", va="center", fontsize=7.5, color=TEXT_MID)
    ax.text(CONFIG_EFFORT_CX, header_y, "Effort", ha="center", va="center", fontsize=7.5, color=TEXT_MID)


def draw_config_cells(ax, y: float, label: str) -> None:
    """Draw the harness / model / effort cells shared by the primary tables."""
    harness, harness_icon, model, model_icon, effort = PRIMARY_ROW_META.get(
        label, (label, ("", ""), "", ("", ""), "")
    )
    for cell_x, cell_text, (icon, icon_color) in (
        (CONFIG_HARNESS_X, harness, harness_icon),
        (CONFIG_MODEL_X, model, model_icon),
    ):
        if icon:
            image = OffsetImage(load_icon(icon, icon_color), zoom=0.048)
            ax.add_artist(
                AnnotationBbox(image, (cell_x + 1.4, y), frameon=False, box_alignment=(0.5, 0.5), zorder=5)
            )
        ax.text(cell_x + 3.7, y, cell_text, ha="left", va="center", fontsize=6.9, color=TEXT_DARK)
    if effort:
        chip_ink, chip_fill = EFFORT_CHIP[effort]
        ax.text(
            CONFIG_EFFORT_CX,
            y,
            effort,
            ha="center",
            va="center",
            fontsize=6.2,
            color=chip_ink,
            bbox={
                "boxstyle": "round,pad=0.30",
                "facecolor": chip_fill,
                "edgecolor": chip_ink,
                "linewidth": 0.6,
            },
            zorder=5,
        )


def metric_value(text: str, key: str) -> str:
    prefix = f"- {key}: `"
    values: list[str] = []
    for line in text.splitlines():
        if line.startswith(prefix) and line.endswith("`"):
            values.append(line[len(prefix) : -1])
    return values[-1] if values else ""


def metric_float(text: str, key: str) -> float | None:
    value = metric_value(text, key)
    if not value:
        return None
    try:
        return float(value)
    except ValueError:
        return None


def final_result(text: str) -> str:
    for line in reversed(text.splitlines()):
        if line.startswith("Final Result:"):
            return line.split(":", 1)[1].strip()
    return ""


def problem_name(workspace: Path) -> str:
    return re.sub(r"^verify_[0-9]{8}_[0-9]{6}[0-9]*_", "", workspace.name)


def latest_workspaces(result_dir: Path) -> dict[str, Path]:
    latest: dict[str, Path] = {}
    for workspace in result_dir.glob("verify_*"):
        if not workspace.is_dir():
            continue
        name = problem_name(workspace)
        prev = latest.get(name)
        if prev is None or workspace.stat().st_mtime > prev.stat().st_mtime:
            latest[name] = workspace
    return latest


def classify(metrics_text: str) -> str:
    if final_result(metrics_text) == "Success":
        return "correct"
    if metric_value(metrics_text, "Last agent exit code") == "124":
        return "timeout"
    if metric_value(metrics_text, "Status") == "Timeout":
        return "timeout"
    return "wrong"


def mean(values: Iterable[float]) -> float:
    values = list(values)
    return sum(values) / len(values) if values else 0.0


def added_nonblank_lines(before_path: Path, after_path: Path) -> int:
    if not before_path.exists() or not after_path.exists():
        return 0
    before = [line.strip() for line in before_path.read_text(encoding="utf-8", errors="replace").splitlines()]
    after = [line.strip() for line in after_path.read_text(encoding="utf-8", errors="replace").splitlines()]
    added = 0
    matcher = difflib.SequenceMatcher(a=before, b=after, autojunk=False)
    for tag, _i1, _i2, j1, j2 in matcher.get_opcodes():
        if tag in {"insert", "replace"}:
            added += sum(1 for line in after[j1:j2] if line)
    return added


def annotation_added_lines(workspace: Path) -> int:
    original_paths = sorted((workspace / "original").glob("*.c"))
    annotated_paths = sorted((workspace / "annotated").glob("*.c"))
    if not original_paths or not annotated_paths:
        return 0
    return added_nonblank_lines(original_paths[0], annotated_paths[0])


def manual_proof_body_lines(path: Path) -> int:
    if not path.exists():
        return 0

    count = 0
    in_proof = False
    for raw_line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = raw_line.strip()
        if not line:
            continue

        if not in_proof:
            if re.match(r"^(Proof|Next Obligation)\b", line):
                in_proof = True
                line = re.sub(r"^(Proof|Next Obligation)\.?", "", line, count=1).strip()
                if not line:
                    continue
            else:
                continue

        terminator = re.search(r"\b(Qed|Admitted|Abort|Defined)\.", line)
        if terminator:
            before_terminator = line[: terminator.start()].strip()
            if before_terminator and not before_terminator.startswith("(*"):
                count += 1
            in_proof = False
            continue

        if line.startswith("(*") and line.endswith("*)"):
            continue
        count += 1
    return count


def manual_proof_added_lines(workspace: Path) -> int:
    proof_paths = list((workspace / "coq" / "generated").glob("*_proof_manual.v"))
    return sum(manual_proof_body_lines(path) for path in proof_paths)


def added_code_lines(workspace: Path) -> dict[str, int]:
    annotation_lines = annotation_added_lines(workspace)
    proof_lines = manual_proof_added_lines(workspace)
    return {
        "annotation_added_lines": annotation_lines,
        "manual_proof_lines": proof_lines,
        "total_added_lines": annotation_lines + proof_lines,
    }


def agent_stdout_jsonl(workspace: Path) -> list[Path]:
    logs_dir = workspace / "logs"
    return sorted(
        path
        for path in logs_dir.glob("agent_stdout_*.jsonl")
        if not path.name.endswith(".timeline.tsv")
    )


def trace_counts(workspace: Path, harness: str) -> int | None:
    paths = agent_stdout_jsonl(workspace)
    if not paths:
        return None

    tool_calls = 0
    saw_json = False
    for path in paths:
        with path.open(encoding="utf-8", errors="replace") as handle:
            for line in handle:
                try:
                    event = json.loads(line)
                except json.JSONDecodeError:
                    continue
                saw_json = True
                event_type = event.get("type")

                if harness == "Codex CLI":
                    item = event.get("item") or {}
                    if event_type == "item.completed" and item.get("type") == "command_execution":
                        tool_calls += 1

                elif harness == "OpenCode":
                    if event_type == "tool_use":
                        tool_calls += 1

                elif harness == "Claude Code":
                    if event_type == "assistant":
                        message = event.get("message") or {}
                        content = message.get("content") or []
                        for block in content:
                            if isinstance(block, dict) and block.get("type") == "tool_use":
                                tool_calls += 1

                elif harness == "Kimi Code":
                    calls = event.get("tool_calls") or []
                    if isinstance(calls, list):
                        tool_calls += len(calls)

    if not saw_json:
        return None
    return tool_calls


def summarize_harness_subset(series: HarnessSeries, tasks: list[str]) -> dict[str, object]:
    latest = latest_workspaces(series.result_dir)
    task_rows: list[dict[str, object]] = []
    for task in tasks:
        workspace = latest.get(task)
        if workspace is None:
            task_rows.append(
                {
                    "task": task,
                    "workspace": "",
                    "status": "missing",
                    "correct": 0,
                    "wall_seconds": None,
                    "total_tokens": None,
                    "input_tokens": None,
                    "output_tokens": None,
                    "tool_calls": None,
                    "annotation_added_lines": None,
                    "manual_proof_lines": None,
                    "generated_code_lines": None,
                }
            )
            continue

        metrics_path = workspace / "logs" / "metrics.md"
        metrics_text = metrics_path.read_text(encoding="utf-8", errors="replace") if metrics_path.exists() else ""
        outcome = classify(metrics_text) if metrics_text else "wrong"
        tool_calls = trace_counts(workspace, series.harness)
        code_lines = added_code_lines(workspace)
        task_rows.append(
            {
                "task": task,
                "workspace": workspace.name,
                "status": outcome,
                "correct": 1 if outcome == "correct" else 0,
                "wall_seconds": metric_float(metrics_text, "Wall-clock time (seconds)"),
                "total_tokens": metric_float(metrics_text, "Agent CLI total_tokens"),
                "input_tokens": metric_float(metrics_text, "Agent CLI input_tokens"),
                "output_tokens": metric_float(metrics_text, "Agent CLI output_tokens"),
                "tool_calls": tool_calls,
                "annotation_added_lines": code_lines["annotation_added_lines"],
                "manual_proof_lines": code_lines["manual_proof_lines"],
                "generated_code_lines": code_lines["total_added_lines"],
            }
        )

    attempted = len([row for row in task_rows if row["status"] != "missing"])
    correct = sum(int(row["correct"]) for row in task_rows)
    timeout = sum(1 for row in task_rows if row["status"] == "timeout")
    wrong = sum(1 for row in task_rows if row["status"] == "wrong")
    wall_values = [float(row["wall_seconds"]) for row in task_rows if row["wall_seconds"] is not None]
    total_values = [float(row["total_tokens"]) for row in task_rows if row["total_tokens"] is not None]
    input_values = [float(row["input_tokens"]) for row in task_rows if row["input_tokens"] is not None]
    output_values = [float(row["output_tokens"]) for row in task_rows if row["output_tokens"] is not None]
    tool_values = [float(row["tool_calls"]) for row in task_rows if row["tool_calls"] is not None]
    annotation_line_values = [
        float(row["annotation_added_lines"])
        for row in task_rows
        if row["annotation_added_lines"] is not None
    ]
    manual_proof_line_values = [
        float(row["manual_proof_lines"])
        for row in task_rows
        if row["manual_proof_lines"] is not None
    ]
    line_values = [
        float(row["generated_code_lines"])
        for row in task_rows
        if row["generated_code_lines"] is not None
    ]

    return {
        "model": series.model,
        "harness": series.harness,
        "color": series.color,
        "attempted": attempted,
        "correct": correct,
        "errors": attempted - correct,
        "wrong": wrong,
        "timeout": timeout,
        "accuracy": correct / attempted if attempted else 0.0,
        "avg_seconds": mean(wall_values),
        "avg_minutes": mean(wall_values) / 60.0 if wall_values else 0.0,
        "avg_tokens_m": mean(total_values) / 1_000_000.0 if total_values else 0.0,
        "avg_input_tokens": mean(input_values),
        "avg_output_tokens": mean(output_values),
        "avg_tool_calls": mean(tool_values),
        "avg_annotation_added_lines": mean(annotation_line_values),
        "avg_manual_proof_lines": mean(manual_proof_line_values),
        "avg_generated_code_lines": mean(line_values),
        "time_runs": len(wall_values),
        "token_runs": len(total_values),
        "input_token_runs": len(input_values),
        "output_token_runs": len(output_values),
        "trace_runs": len(tool_values),
        "annotation_line_runs": len(annotation_line_values),
        "manual_proof_line_runs": len(manual_proof_line_values),
        "code_line_runs": len(line_values),
        "task_rows": task_rows,
    }


def summarize_glm52_harness(series: HarnessSeries) -> dict[str, object]:
    return summarize_harness_subset(series, HARNESS_CLAUDE_SHARED_TASKS)


def add_radar_scores(rows: list[dict[str, object]]) -> list[dict[str, object]]:
    scored = [dict(row) for row in rows]
    raw_metrics = [
        ("errors", "score_errors"),
        ("avg_minutes", "score_time"),
        ("avg_input_tokens", "score_input_tokens"),
        ("avg_output_tokens", "score_output_tokens"),
        ("avg_tool_calls", "score_tool_calls"),
        ("avg_generated_code_lines", "score_generated_code_lines"),
    ]
    for raw_key, score_key in raw_metrics:
        values = [float(row[raw_key]) for row in scored]
        high = max(values)
        for row in scored:
            value = float(row[raw_key])
            row[score_key] = value / high if high > 0 else 0.0
    return scored


def write_harness_radar_csv(rows: list[dict[str, object]]) -> None:
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    rows = add_radar_scores(rows)
    summary_path = FIGURES_DIR / "harness_outcomes_models.csv"
    with summary_path.open("w", encoding="utf-8", newline="") as handle:
        fieldnames = [
            "model",
            "harness",
            "attempted",
            "correct",
            "errors",
            "avg_minutes",
            "time_runs",
            "avg_input_tokens",
            "input_token_runs",
            "avg_output_tokens",
            "output_token_runs",
            "avg_tool_calls",
            "trace_runs",
            "avg_annotation_added_lines",
            "annotation_line_runs",
            "avg_manual_proof_lines",
            "manual_proof_line_runs",
            "avg_generated_code_lines",
            "code_line_runs",
            "score_errors",
            "score_time",
            "score_input_tokens",
            "score_output_tokens",
            "score_tool_calls",
            "score_generated_code_lines",
        ]
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow(
                {
                    "model": row["model"],
                    "harness": row["harness"],
                    "attempted": row["attempted"],
                    "correct": row["correct"],
                    "errors": row["errors"],
                    "avg_minutes": f"{float(row['avg_minutes']):.2f}",
                    "time_runs": row["time_runs"],
                    "avg_input_tokens": f"{float(row['avg_input_tokens']):.0f}",
                    "input_token_runs": row["input_token_runs"],
                    "avg_output_tokens": f"{float(row['avg_output_tokens']):.0f}",
                    "output_token_runs": row["output_token_runs"],
                    "avg_tool_calls": f"{float(row['avg_tool_calls']):.2f}",
                    "trace_runs": row["trace_runs"],
                    "avg_annotation_added_lines": f"{float(row['avg_annotation_added_lines']):.2f}",
                    "annotation_line_runs": row["annotation_line_runs"],
                    "avg_manual_proof_lines": f"{float(row['avg_manual_proof_lines']):.2f}",
                    "manual_proof_line_runs": row["manual_proof_line_runs"],
                    "avg_generated_code_lines": f"{float(row['avg_generated_code_lines']):.2f}",
                    "code_line_runs": row["code_line_runs"],
                    "score_errors": f"{float(row['score_errors']):.4f}",
                    "score_time": f"{float(row['score_time']):.4f}",
                    "score_input_tokens": f"{float(row['score_input_tokens']):.4f}",
                    "score_output_tokens": f"{float(row['score_output_tokens']):.4f}",
                    "score_tool_calls": f"{float(row['score_tool_calls']):.4f}",
                    "score_generated_code_lines": f"{float(row['score_generated_code_lines']):.4f}",
                }
            )

    detail_path = FIGURES_DIR / "harness_outcomes_models_detail.csv"
    with detail_path.open("w", encoding="utf-8", newline="") as handle:
        fieldnames = [
            "harness",
            "task",
            "workspace",
            "status",
            "correct",
            "wall_seconds",
            "input_tokens",
            "output_tokens",
            "tool_calls",
            "annotation_added_lines",
            "manual_proof_lines",
            "generated_code_lines",
        ]
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            for task_row in row["task_rows"]:
                writer.writerow(
                    {
                        "harness": row["harness"],
                        "task": task_row["task"],
                        "workspace": task_row["workspace"],
                        "status": task_row["status"],
                        "correct": task_row["correct"],
                        "wall_seconds": task_row["wall_seconds"] or "",
                        "input_tokens": task_row["input_tokens"] or "",
                        "output_tokens": task_row["output_tokens"] or "",
                        "tool_calls": task_row["tool_calls"] if task_row["tool_calls"] is not None else "",
                        "annotation_added_lines": task_row["annotation_added_lines"]
                        if task_row["annotation_added_lines"] is not None
                        else "",
                        "manual_proof_lines": task_row["manual_proof_lines"]
                        if task_row["manual_proof_lines"] is not None
                        else "",
                        "generated_code_lines": task_row["generated_code_lines"]
                        if task_row["generated_code_lines"] is not None
                        else "",
                    }
                )


def summarize(series: Series | HarnessSeries) -> dict[str, object]:
    counts = {"correct": 0, "wrong": 0, "timeout": 0}
    latest = latest_workspaces(series.result_dir)
    walls: list[float] = []
    tokens: list[float] = []
    input_tokens: list[float] = []
    output_tokens: list[float] = []
    tool_calls: list[float] = []
    harness = getattr(series, "harness", "")
    label = getattr(series, "label", "")
    if not harness:
        if label.startswith("Codex "):
            harness = "Codex CLI"
        elif label.startswith("Claude Code "):
            harness = "Claude Code"
        elif label.startswith("Kimi Code"):
            harness = "Kimi Code"
    for workspace in latest.values():
        metrics = workspace / "logs" / "metrics.md"
        if not metrics.exists():
            continue
        text = metrics.read_text(encoding="utf-8", errors="replace")
        counts[classify(text)] += 1
        wall = metric_value(text, "Wall-clock time (seconds)")
        if wall:
            try:
                walls.append(float(wall))
            except ValueError:
                pass
        total_tokens = metric_value(text, "Agent CLI total_tokens")
        if total_tokens:
            try:
                tokens.append(float(total_tokens))
            except ValueError:
                pass
        input_value = metric_value(text, "Agent CLI input_tokens")
        if input_value:
            try:
                input_tokens.append(float(input_value))
            except ValueError:
                pass
        output_value = metric_value(text, "Agent CLI output_tokens")
        if output_value:
            try:
                output_tokens.append(float(output_value))
            except ValueError:
                pass
        if harness:
            counted = trace_counts(workspace, harness)
            if counted is not None:
                tool_calls.append(float(counted))
    attempted = sum(counts.values())
    return {
        "label": getattr(series, "label", getattr(series, "harness", "")),
        "short_label": getattr(series, "short_label", getattr(series, "harness", "")),
        "model": getattr(series, "model", ""),
        "harness": getattr(series, "harness", ""),
        "icon": getattr(series, "icon", ""),
        "color": series.color,
        "attempted": attempted,
        "correct": counts["correct"],
        "wrong": counts["wrong"],
        "timeout": counts["timeout"],
        "accuracy": counts["correct"] / attempted if attempted else 0.0,
        "avg_minutes": (sum(walls) / len(walls) / 60.0) if walls else 0.0,
        "avg_tokens_m": (sum(tokens) / len(tokens) / 1_000_000.0) if tokens else 0.0,
        "avg_input_tokens_m": (sum(input_tokens) / len(input_tokens) / 1_000_000.0) if input_tokens else 0.0,
        "avg_output_tokens_k": (sum(output_tokens) / len(output_tokens) / 1_000.0) if output_tokens else 0.0,
        "avg_tool_calls": (sum(tool_calls) / len(tool_calls)) if tool_calls else 0.0,
        "token_runs": len(tokens),
        "input_token_runs": len(input_tokens),
        "output_token_runs": len(output_tokens),
        "tool_call_runs": len(tool_calls),
    }


def tint(hex_color: str, amount: float) -> tuple[float, float, float]:
    color = hex_color.lstrip("#")
    rgb = np.array([int(color[i : i + 2], 16) for i in (0, 2, 4)], dtype=float) / 255.0
    return tuple(rgb + (1.0 - rgb) * amount)


def hex_rgb(hex_color: str) -> tuple[int, int, int]:
    color = hex_color.lstrip("#")
    return tuple(int(color[i : i + 2], 16) for i in (0, 2, 4))


def ensure_source_icon(icon: str) -> Path:
    ICONS_DIR.mkdir(parents=True, exist_ok=True)
    url = ICON_URLS[icon]
    suffix = Path(url.split("?", 1)[0]).suffix or ".svg"
    source_path = ICONS_DIR / f"{icon}{suffix}"
    url_path = ICONS_DIR / f"{icon}.url"
    previous_url = url_path.read_text(encoding="utf-8").strip() if url_path.exists() else ""
    if previous_url != url or not source_path.exists():
        response = requests.get(ICON_URLS[icon], timeout=20)
        response.raise_for_status()
        source_path.write_bytes(response.content)
        url_path.write_text(url + "\n", encoding="utf-8")
    return source_path


def render_svg_icon(source_path: Path, color: str) -> Image.Image:
    svg = source_path.read_text(encoding="utf-8", errors="replace")
    svg = svg.replace("currentColor", color)
    svg = re.sub(r'fill="(?!none)[^"]*"', f'fill="{color}"', svg)
    svg = re.sub(r'stroke="(?!none)[^"]*"', f'stroke="{color}"', svg)
    if re.search(r"<svg[^>]*\sfill=", svg) is None:
        svg = svg.replace("<svg ", f'<svg fill="{color}" ', 1)
    if re.search(r"<svg[^>]*\scolor=", svg) is None:
        svg = svg.replace("<svg ", f'<svg color="{color}" ', 1)
    png_path = ICONS_DIR / "_tmp_icon_render.png"
    svg2png(bytestring=svg.encode("utf-8"), write_to=str(png_path), output_width=192, output_height=192)
    image = Image.open(png_path).convert("RGBA")
    png_path.unlink(missing_ok=True)
    return image


def render_original_svg(source_path: Path) -> Image.Image:
    png_path = ICONS_DIR / "_tmp_icon_render.png"
    svg2png(url=str(source_path), write_to=str(png_path), output_width=192, output_height=192)
    image = Image.open(png_path).convert("RGBA")
    png_path.unlink(missing_ok=True)
    return image


def fit_visible_content(image: Image.Image, target_size: int) -> Image.Image:
    image = image.convert("RGBA")
    alpha = image.getchannel("A")
    bbox = alpha.getbbox()
    if bbox is None:
        return Image.new("RGBA", (target_size, target_size), (0, 0, 0, 0))
    content = image.crop(bbox)
    scale = target_size / max(content.size)
    new_size = (
        max(1, round(content.width * scale)),
        max(1, round(content.height * scale)),
    )
    content = content.resize(new_size, Image.Resampling.LANCZOS)
    fitted = Image.new("RGBA", (target_size, target_size), (0, 0, 0, 0))
    fitted.alpha_composite(content, ((target_size - new_size[0]) // 2, (target_size - new_size[1]) // 2))
    return fitted


def circular_badge(glyph: Image.Image, background: tuple[int, int, int, int]) -> Image.Image:
    badge = Image.new("RGBA", (192, 192), (0, 0, 0, 0))
    mask = Image.new("L", (192, 192), 0)
    yy, xx = np.ogrid[:192, :192]
    circle = (xx - 96) ** 2 + (yy - 96) ** 2 <= 94**2
    mask_arr = np.zeros((192, 192), dtype=np.uint8)
    mask_arr[circle] = 255
    mask = Image.fromarray(mask_arr, mode="L")
    badge.paste(Image.new("RGBA", (192, 192), background), (0, 0), mask)

    border_arr = np.zeros((192, 192), dtype=np.uint8)
    outer = (xx - 96) ** 2 + (yy - 96) ** 2 <= 94**2
    inner = (xx - 96) ** 2 + (yy - 96) ** 2 <= 90**2
    border_arr[outer & ~inner] = 255
    border = Image.fromarray(border_arr, mode="L")
    badge.paste(Image.new("RGBA", (192, 192), (229, 231, 235, 255)), (0, 0), border)

    glyph = fit_visible_content(glyph, 160)
    badge.alpha_composite(glyph, (16, 16))
    return badge


def render_codex_color_icon(source_path: Path) -> Image.Image:
    """Render the official gradient Codex mark, dropping its white backplate."""
    svg = source_path.read_text(encoding="utf-8", errors="replace")
    svg = re.sub(r'<path[^>]*fill="#fff"[^>]*>\s*</path>', "", svg, count=1, flags=re.IGNORECASE)
    png_path = ICONS_DIR / "_tmp_icon_render.png"
    svg2png(bytestring=svg.encode("utf-8"), write_to=str(png_path), output_width=192, output_height=192)
    image = Image.open(png_path).convert("RGBA")
    png_path.unlink(missing_ok=True)
    return image


# Claude Code's terminal banner mark, one string per row of block characters.
CLAUDE_CODE_ART = (
    " ▐▛███▜▌ ",
    "▝▜█████▛▘",
    "  ▘▘ ▝▝  ",
)

# Block character -> filled quadrants (upper-left, upper-right, lower-left, lower-right).
BLOCK_QUADRANTS = {
    " ": (0, 0, 0, 0),
    "▘": (1, 0, 0, 0),
    "▝": (0, 1, 0, 0),
    "▖": (0, 0, 1, 0),
    "▗": (0, 0, 0, 1),
    "▀": (1, 1, 0, 0),
    "▄": (0, 0, 1, 1),
    "▌": (1, 0, 1, 0),
    "▐": (0, 1, 0, 1),
    "▛": (1, 1, 1, 0),
    "▜": (1, 1, 0, 1),
    "▙": (1, 0, 1, 1),
    "▟": (0, 1, 1, 1),
    "█": (1, 1, 1, 1),
}


def render_claude_code_glyph(color: str) -> Image.Image:
    """Draw the Claude Code block-art banner; quadrants are 1:2 like terminal cells."""
    quad_w, quad_h = 20, 40
    columns = max(len(row) for row in CLAUDE_CODE_ART)
    image = Image.new("RGBA", (columns * 2 * quad_w, len(CLAUDE_CODE_ART) * 2 * quad_h), (0, 0, 0, 0))
    draw = ImageDraw.Draw(image)
    fill = hex_rgb(color) + (255,)
    for row_index, row in enumerate(CLAUDE_CODE_ART):
        for col_index, char in enumerate(row):
            quads = BLOCK_QUADRANTS[char]
            for quad, (dx, dy) in zip(quads, ((0, 0), (1, 0), (0, 1), (1, 1))):
                if quad:
                    x0 = (col_index * 2 + dx) * quad_w
                    y0 = (row_index * 2 + dy) * quad_h
                    draw.rectangle([x0, y0, x0 + quad_w, y0 + quad_h], fill=fill)
    return image


def recolor_zhipu_icon(source_path: Path, color: str) -> Image.Image:
    rendered = render_original_svg(source_path)
    arr = np.array(rendered)
    alpha = arr[:, :, 3]
    visible = alpha > 0
    dark = visible & (arr[:, :, :3].mean(axis=2) < 120)
    colored = np.array(hex_rgb(color), dtype=np.uint8)
    arr[dark, :3] = colored
    return Image.fromarray(arr, mode="RGBA")


def ensure_icon_badge(icon: str, color: str) -> Path:
    safe_color = color.lstrip("#").lower()
    if icon == "claude_code":
        badge_path = ICONS_DIR / f"claude_code_badge_{safe_color}.png"
        badge = circular_badge(render_claude_code_glyph(color), (255, 255, 255, 255))
        badge.save(badge_path)
        return badge_path

    source_path = ensure_source_icon(icon)
    if icon == "codex":
        badge_name = "codex_badge_color.png"
    elif icon == "zhipu":
        badge_name = f"{icon}_badge_{safe_color}.png"
    else:
        badge_name = f"{icon}_badge_{safe_color}.png"
    badge_path = ICONS_DIR / badge_name
    # OpenAI and Zhipu badges encode the caller-supplied model color.  Rebuild
    # these inexpensive assets so older black-only cache entries cannot leak
    # into a newly generated figure.
    if (
        icon not in {"openai", "zhipu"}
        and badge_path.exists()
        and badge_path.stat().st_mtime >= source_path.stat().st_mtime
    ):
        return badge_path

    if icon == "codex":
        glyph = render_codex_color_icon(source_path)
        badge = circular_badge(glyph, (255, 255, 255, 255))
    elif icon == "openai":
        glyph = render_svg_icon(source_path, color)
        badge = circular_badge(glyph, (255, 255, 255, 255))
    elif icon == "claude":
        glyph = render_svg_icon(source_path, color)
        badge = circular_badge(glyph, (255, 255, 255, 255))
    elif icon == "deepseek":
        glyph = render_svg_icon(source_path, color)
        badge = circular_badge(glyph, (255, 255, 255, 255))
    elif icon == "zhipu":
        badge = recolor_zhipu_icon(source_path, color)
    elif icon == "opencode":
        # Preserve the official black/gray application mark; recoloring every
        # SVG fill would collapse its nested shapes into a solid square.
        badge = render_original_svg(source_path)
    elif icon == "kimi":
        badge = Image.open(source_path).convert("RGBA").resize((192, 192), Image.Resampling.LANCZOS)
    else:
        glyph = render_svg_icon(source_path, color)
        badge = circular_badge(glyph, (255, 255, 255, 255))

    badge.save(badge_path)
    return badge_path


def load_icon(icon: str, color: str) -> np.ndarray:
    path = ensure_icon_badge(icon, color)
    return np.asarray(Image.open(path).convert("RGBA"))


def write_csv(rows: Iterable[dict[str, object]]) -> None:
    path = FIGURES_DIR / "primary_outcomes_models.csv"
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "label",
                "attempted",
                "correct",
                "wrong",
                "timeout",
                "accuracy",
                "avg_minutes",
                "avg_tokens_m",
                "avg_input_tokens_m",
                "avg_output_tokens_k",
                "avg_tool_calls",
                "token_runs",
                "input_token_runs",
                "output_token_runs",
                "tool_call_runs",
            ],
        )
        writer.writeheader()
        for row in rows:
            writer.writerow(
                {
                    "label": row["label"],
                    "attempted": row["attempted"],
                    "correct": row["correct"],
                    "wrong": row["wrong"],
                    "timeout": row["timeout"],
                    "accuracy": f"{row['accuracy']:.4f}",
                    "avg_minutes": f"{row['avg_minutes']:.2f}",
                    "avg_tokens_m": f"{row['avg_tokens_m']:.2f}",
                    "avg_input_tokens_m": f"{row['avg_input_tokens_m']:.2f}",
                    "avg_output_tokens_k": f"{row['avg_output_tokens_k']:.2f}",
                    "avg_tool_calls": f"{row['avg_tool_calls']:.2f}",
                    "token_runs": row["token_runs"],
                    "input_token_runs": row["input_token_runs"],
                    "output_token_runs": row["output_token_runs"],
                    "tool_call_runs": row["tool_call_runs"],
                }
            )


def average_minutes_from_metrics(base_dir: Path, pattern: str, fallback_minutes: float) -> tuple[int, float]:
    values: list[float] = []
    for workspace in sorted(base_dir.glob(pattern)):
        metrics_path = workspace / "logs" / "metrics.md"
        if not metrics_path.exists():
            continue
        text = metrics_path.read_text(encoding="utf-8", errors="replace")
        seconds = metric_float(text, "Wall-clock time (seconds)")
        if seconds is not None:
            values.append(seconds / 60.0)
    if not values:
        return 0, fallback_minutes
    return len(values), mean(values)


def timeline_minutes(workspace: Path) -> float | None:
    epochs: list[float] = []
    for timeline_path in sorted((workspace / "logs").glob("*.timeline.tsv")):
        with timeline_path.open(encoding="utf-8", errors="replace") as handle:
            next(handle, None)
            for line in handle:
                if not line.strip():
                    continue
                try:
                    epochs.append(float(line.split("\t", 1)[0]))
                except ValueError:
                    continue
    if len(epochs) < 2:
        return None
    minutes = (max(epochs) - min(epochs)) / 60.0
    return minutes if minutes > 0 else None


def metric_minutes(workspace: Path) -> float | None:
    metrics_path = workspace / "logs" / "metrics.md"
    if not metrics_path.exists():
        return None
    text = metrics_path.read_text(encoding="utf-8", errors="replace")
    seconds = metric_float(text, "Wall-clock time (seconds)")
    return seconds / 60.0 if seconds is not None else None


def average_minutes_from_run_logs(base_dir: Path, pattern: str, fallback_minutes: float) -> tuple[int, float]:
    values: list[float] = []
    for workspace in sorted(base_dir.glob(pattern)):
        minutes = timeline_minutes(workspace)
        if minutes is None:
            minutes = metric_minutes(workspace)
        if minutes is not None:
            values.append(minutes)
    if not values:
        return 0, fallback_minutes
    return len(values), mean(values)


def write_harness_csv(rows: Iterable[dict[str, object]]) -> None:
    path = FIGURES_DIR / "harness_outcomes_models.csv"
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=[
                "model",
                "harness",
                "attempted",
                "correct",
                "wrong",
                "timeout",
                "accuracy",
                "avg_minutes",
                "avg_tokens_m",
                "token_runs",
            ],
        )
        writer.writeheader()
        for row in rows:
            writer.writerow(
                {
                    "model": row["model"],
                    "harness": row["harness"],
                    "attempted": row["attempted"],
                    "correct": row["correct"],
                    "wrong": row["wrong"],
                    "timeout": row["timeout"],
                    "accuracy": f"{row['accuracy']:.4f}",
                    "avg_minutes": f"{row['avg_minutes']:.2f}",
                    "avg_tokens_m": f"{row['avg_tokens_m']:.2f}",
                    "token_runs": row["token_runs"],
                }
            )


def display_model_label(label: str) -> str:
    if label == "Claude Code DeepSeek-V4-Pro":
        return "Claude Code\nDeepSeek-V4-Pro"
    return label


def display_primary_label(label: str) -> str:
    labels = {
        "Codex GPT-5.5 xhigh": "Codex GPT-5.5\nxhigh",
        "Codex GPT-5.5 medium": "Codex GPT-5.5\nmedium",
        "Codex GPT-5.4 medium": "Codex GPT-5.4\nmedium",
        "Claude Code GLM-5.2": "Claude Code\nGLM-5.2",
        "Claude Code DeepSeek-V4-Pro": "Claude Code\nDeepSeek-V4-Pro",
    }
    return labels.get(label, label)


def _draw_task_design_legacy() -> None:
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)

    # Cross-functional flowchart.  Shape, rather than color alone, carries the
    # semantics: people/agents are actors, waved sheets are artifacts, gears
    # are tools, diamonds are gates, and pills are terminal outcomes.
    # Figure-specific palette follows SL-VC Fig. 1: cyan LLM actors, lavender
    # verifier/tool nodes, dark violet feedback, and black-gray structure.
    slvc_ink = "#29252D"
    slvc_line = "#4D4851"
    slvc_actor = "#C7E5F1"
    slvc_actor_edge = "#4B8EAA"
    slvc_tool = "#DCC9E3"
    slvc_tool_edge = "#765489"
    slvc_feedback = "#65407A"
    contract_fill, contract_edge = "#E8F0F4", TASK_SCOPE_END_TO_END
    annotation_fill, annotation_edge = "#EDF5F8", TASK_SCOPE_PRIMARY
    proof_fill, proof_edge = "#F2F8FA", TASK_SCOPE_PROOF_ONLY

    fig, ax = plt.subplots(figsize=(7.55, 2.90), dpi=FIG_DPI)
    fig.patch.set_facecolor("#FFFFFF")
    ax.set_facecolor("#FFFFFF")
    ax.set_xlim(0.0, 16.35)
    ax.set_ylim(0.0, 6.05)
    ax.axis("off")

    def rounded_box(x, y, w, h, *, face="#FFFFFF", edge=TASK_AUDIT,
                    lw=0.72, radius=0.07, z=2, linestyle="solid"):
        box = patches.FancyBboxPatch(
            (x, y), w, h,
            boxstyle=f"round,pad=0.025,rounding_size={radius}",
            facecolor=face, edgecolor=edge, linewidth=lw,
            linestyle=linestyle, zorder=z,
        )
        ax.add_patch(box)
        return box

    def arrow(x0, y0, x1, y1, *, color=TEXT_MUTED, lw=0.76,
              style="-|>", z=4, connection="arc3"):
        ax.add_patch(patches.FancyArrowPatch(
            (x0, y0), (x1, y1), arrowstyle=style, mutation_scale=7.8,
            linewidth=lw, color=color, shrinkA=0, shrinkB=0,
            connectionstyle=connection, zorder=z,
        ))

    def elbow(points, *, color=TEXT_MUTED, lw=0.72, linestyle="solid", z=3):
        xs, ys = zip(*points)
        ax.plot(xs[:-1], ys[:-1], color=color, lw=lw,
                linestyle=linestyle, zorder=z)
        arrow(xs[-2], ys[-2], xs[-1], ys[-1], color=color, lw=lw, z=z + 1)

    def human_icon(cx, cy, scale=1.0, *, color=SLATE):
        ax.add_patch(patches.Circle((cx, cy + 0.13 * scale), 0.12 * scale,
                                    facecolor="#FFFFFF", edgecolor=color,
                                    linewidth=0.85, zorder=6))
        ax.add_patch(patches.Arc((cx, cy - 0.09 * scale), 0.44 * scale,
                                 0.34 * scale, theta1=10, theta2=170,
                                 edgecolor=color, linewidth=1.35, zorder=6))

    def agent_icon(cx, cy, scale=1.0, *, color=TASK_ANNOTATION):
        ax.add_patch(patches.FancyBboxPatch(
            (cx - 0.14 * scale, cy - 0.10 * scale), 0.28 * scale, 0.21 * scale,
            boxstyle=f"round,pad=0.008,rounding_size={0.035 * scale}",
            facecolor="#FFFFFF", edgecolor=color, linewidth=0.78, zorder=7,
        ))
        ax.plot([cx, cx], [cy + 0.12 * scale, cy + 0.19 * scale],
                color=color, lw=0.75, zorder=7)
        ax.add_patch(patches.Circle((cx, cy + 0.20 * scale), 0.018 * scale,
                                    facecolor=color, edgecolor="none", zorder=7))
        for dx in (-0.06, 0.06):
            ax.add_patch(patches.Circle((cx + dx * scale, cy + 0.02 * scale),
                                        0.017 * scale, facecolor=color,
                                        edgecolor="none", zorder=8))
        ax.plot([cx - 0.05 * scale, cx + 0.05 * scale],
                [cy - 0.055 * scale, cy - 0.055 * scale],
                color=color, lw=0.72, zorder=8)

    def agent_node(x, y, w, h, action, *, color):
        rounded_box(x, y, w, h, face=slvc_actor, edge=slvc_actor_edge,
                    lw=0.82, radius=0.10, z=5)
        agent_icon(x + 0.27, y + h / 2 + 0.02, 0.82, color=slvc_actor_edge)
        ax.text(x + 0.50, y + h / 2 + 0.12, "Agent", ha="left", va="center",
                fontsize=6.15, fontweight="bold", color=TEXT_DARK, zorder=8)
        ax.text(x + 0.50, y + h / 2 - 0.14, action, ha="left", va="center",
                fontsize=4.85, color=TEXT_MUTED, zorder=8)

    def document(x, y, w, h, title, subtitle="", *, color=SLATE,
                 face="#FFFFFF", z=5):
        verts = [
            (x, y + h), (x + w, y + h), (x + w, y + 0.13),
            (x + 0.76 * w, y - 0.01), (x + 0.50 * w, y + 0.13),
            (x + 0.24 * w, y + 0.27), (x, y + 0.13),
            (x, y + h), (x, y + h),
        ]
        codes = [MplPath.MOVETO, MplPath.LINETO, MplPath.LINETO,
                 MplPath.CURVE3, MplPath.CURVE3, MplPath.CURVE3,
                 MplPath.CURVE3, MplPath.LINETO, MplPath.CLOSEPOLY]
        ax.add_patch(patches.PathPatch(MplPath(verts, codes), facecolor=face,
                                       edgecolor=color, linewidth=0.78, zorder=z))
        ax.text(x + w / 2, y + h * 0.62, title, ha="center", va="center",
                fontsize=5.75, fontweight="semibold", color=TEXT_DARK,
                linespacing=0.90, zorder=z + 1)
        if subtitle:
            ax.text(x + w / 2, y + h * 0.31, subtitle, ha="center", va="center",
                    fontsize=4.55, color=TEXT_MUTED, linespacing=0.90, zorder=z + 1)

    def document_stack(x, y, w, h, title, subtitle, *, color):
        for dx, dy in ((0.12, 0.12), (0.06, 0.06)):
            document(x + dx, y + dy, w, h, "", color=color,
                     face="#F8FAFC", z=3)
        document(x, y, w, h, title, subtitle, color=color, z=5)

    def gear(cx, cy, radius, title, subtitle, *, color):
        points = []
        teeth = 12
        for i in range(teeth * 2):
            angle = np.pi / 2 + i * np.pi / teeth
            r = radius if i % 2 == 0 else radius * 0.82
            points.append((cx + r * np.cos(angle), cy + r * np.sin(angle)))
        ax.add_patch(patches.Polygon(points, closed=True, facecolor=slvc_tool,
                                     edgecolor=slvc_tool_edge, linewidth=0.86, zorder=5))
        ax.add_patch(patches.Circle((cx, cy), radius * 0.57,
                                    facecolor="#FFFFFF", edgecolor=slvc_tool_edge,
                                    linewidth=0.60, zorder=6))
        ax.text(cx, cy + 0.04, title, ha="center", va="center", fontsize=6.1,
                fontweight="bold", color=TEXT_DARK, zorder=7)
        ax.text(cx, cy - radius - 0.18, subtitle, ha="center", va="top",
                fontsize=4.65, color=TEXT_MUTED, linespacing=0.90, zorder=7)

    def diamond(cx, cy, rx, ry, title, subtitle="", *, color):
        ax.add_patch(patches.Polygon(
            [(cx, cy + ry), (cx + rx, cy), (cx, cy - ry), (cx - rx, cy)],
            closed=True, facecolor="#FFFFFF", edgecolor=color,
            linewidth=0.90, zorder=5,
        ))
        ax.text(cx, cy + (0.07 if subtitle else 0), title, ha="center", va="center",
                fontsize=5.45, fontweight="semibold", color=TEXT_DARK,
                linespacing=0.88, zorder=7)
        if subtitle:
            ax.text(cx, cy - 0.30, subtitle, ha="center", va="center",
                    fontsize=4.25, color=TEXT_MUTED, linespacing=0.88, zorder=7)

    def terminal(x, y, w, h, title, subtitle="", *, color, face="#FFFFFF",
                 double=False):
        rounded_box(x, y, w, h, face=face, edge=color, lw=0.90,
                    radius=h / 2, z=5)
        if double:
            rounded_box(x + 0.055, y + 0.055, w - 0.11, h - 0.11,
                        face="none", edge=color, lw=0.52,
                        radius=(h - 0.11) / 2, z=6)
        ax.text(x + w / 2, y + h / 2 + (0.10 if subtitle else 0), title,
                ha="center", va="center", fontsize=5.65, fontweight="bold",
                color=color, linespacing=0.90, zorder=7)
        if subtitle:
            ax.text(x + w / 2, y + h / 2 - 0.18, subtitle,
                    ha="center", va="center", fontsize=4.25,
                    color=TEXT_MUTED, linespacing=0.88, zorder=7)

    # Three stage containers intersect three subtle swimlanes.
    stages = [
        (2.42, 3.70, contract_fill, contract_edge, "1  CONTRACT"),
        (6.28, 3.92, annotation_fill, annotation_edge, "2  ANNOTATION"),
        (10.36, 3.52, proof_fill, proof_edge, "3  PROOF"),
    ]
    for x, w, fill, edge, label in stages:
        rounded_box(x, 0.38, w, 5.02, face=fill, edge=edge,
                    lw=0.88, radius=0.13, z=0)
        ax.text(x + 0.17, 5.10, label, ha="left", va="center",
                fontsize=6.25, fontweight="bold", color=edge, zorder=2)
        ax.plot([x + 0.16, x + w - 0.16], [4.88, 4.88],
                color=edge, lw=0.52, alpha=0.70, zorder=1)

    for y in (2.20, 3.78):
        ax.plot([0.72, 13.83], [y, y], color="#CBD5E1", lw=0.48,
                linestyle=(0, (2, 2.5)), zorder=1)
    for y, label in ((4.40, "ACTORS"), (3.00, "ARTIFACTS"), (1.30, "TOOLS / CHECKS")):
        ax.text(0.76, y, label, ha="right", va="center", fontsize=4.55,
                fontweight="bold", color=TEXT_MUTED, zorder=2)

    # Human-authored inputs.
    human_icon(1.52, 4.42, 1.08, color=SLATE)
    ax.text(1.52, 4.05, "Human", ha="center", va="center", fontsize=5.8,
            fontweight="bold", color=TEXT_DARK)
    document(0.88, 2.64, 0.72, 0.78, "NL", "specification", color=SLATE)
    document(1.67, 2.64, 0.72, 0.78, "C code", "immutable", color=SLATE)

    # Contract generation and semantic gate.
    agent_node(2.73, 4.02, 1.16, 0.72, "formalize", color=contract_edge)
    document(4.14, 2.62, 1.20, 0.86, "Contract", "QCP + Rocq defs", color=contract_edge)
    diamond(5.48, 1.30, 0.53, 0.65, "Semantic\nadequacy?", "faithful + complete",
            color=slvc_line)
    elbow([(2.39, 3.03), (2.56, 3.03), (2.56, 4.38), (2.73, 4.38)])
    arrow(3.89, 4.22, 4.28, 3.48, color=slvc_line)
    elbow([(4.74, 2.62), (4.74, 2.20), (5.48, 1.95)], color=slvc_line)
    arrow(5.03, 1.68, 3.43, 4.02, color=slvc_feedback, lw=0.68,
          connection="arc3,rad=-0.18")
    ax.text(4.10, 1.82, "revise contract", ha="center", va="center",
            fontsize=4.45, color=slvc_feedback,
            bbox={"facecolor": contract_fill, "edgecolor": "none", "pad": 0.25})

    # Annotation generation and QCP VC generation.
    agent_node(6.60, 4.02, 1.18, 0.72, "add annotations", color=annotation_edge)
    document(7.90, 2.62, 1.28, 0.86, "Annotated C", "invariants + assertions",
             color=annotation_edge)
    gear(8.96, 1.42, 0.45, "QCP", "symbolic execution\n+ VC generation",
         color=slvc_tool_edge)
    document_stack(9.22, 2.59, 0.72, 0.88, "VCs", "generated goals",
                   color=annotation_edge)
    elbow([(6.01, 1.30), (6.18, 1.30), (6.18, 4.38), (6.60, 4.38)],
          color=slvc_line)
    ax.text(6.10, 1.52, "pass", ha="center", va="bottom", fontsize=4.35,
            color=slvc_line)
    arrow(7.78, 4.22, 8.08, 3.48, color=slvc_line)
    elbow([(8.55, 2.62), (8.55, 2.18), (8.83, 1.80)], color=slvc_line)
    elbow([(9.09, 1.80), (9.09, 2.20), (9.50, 2.59)], color=slvc_line)
    arrow(8.60, 1.66, 7.20, 4.02, color=slvc_feedback, lw=0.68,
          connection="arc3,rad=-0.20")
    ax.text(7.75, 1.82, "strengthen annotations", ha="center", va="center",
            fontsize=4.35, color=slvc_feedback,
            bbox={"facecolor": annotation_fill, "edgecolor": "none", "pad": 0.25})

    # Proof generation and Rocq checking.
    agent_node(10.68, 4.02, 1.18, 0.72, "prove VCs", color=proof_edge)
    document(12.01, 2.62, 1.12, 0.86, "Rocq proof", "manual script",
             color=proof_edge)
    gear(13.10, 1.42, 0.45, "Rocq", "compile chain\n+ goal check", color=slvc_tool_edge)
    arrow(9.94, 3.03, 10.82, 4.02, color=slvc_line)
    arrow(11.86, 4.22, 12.14, 3.48, color=slvc_line)
    elbow([(12.57, 2.62), (12.57, 2.18), (12.97, 1.80)], color=slvc_line)
    arrow(12.74, 1.66, 11.28, 4.02, color=slvc_feedback, lw=0.68,
          connection="arc3,rad=-0.20")
    ax.text(11.90, 1.82, "repair proofs", ha="center", va="center",
            fontsize=4.35, color=slvc_feedback,
            bbox={"facecolor": proof_fill, "edgecolor": "none", "pad": 0.25})

    # Deterministic audit and explicit terminal outcomes.
    diamond(14.30, 3.02, 0.55, 0.68, "Audit\npass?", color=slvc_line)
    elbow([(13.55, 1.42), (13.82, 1.42), (13.82, 3.02), (13.75, 3.02)],
          color=slvc_line)
    ax.text(14.30, 2.16, "replay · integrity\nno proof bypass", ha="center",
            va="center", fontsize=4.25, color=TEXT_MUTED, linespacing=0.92)
    terminal(15.02, 2.59, 1.20, 0.86, "VERIFIED", "complete artifact",
             color=proof_edge, face="#FFFFFF", double=True)
    arrow(14.85, 3.02, 15.02, 3.02, color=proof_edge)
    ax.text(14.91, 3.20, "yes", ha="center", va="bottom", fontsize=4.25,
            color=proof_edge)
    terminal(13.78, 0.48, 1.04, 0.48, "REJECTED", color="#A06461",
             face="#F8EEEE")
    arrow(14.30, 2.34, 14.30, 0.96, color="#A06461")
    ax.text(14.43, 1.62, "no", ha="left", va="center", fontsize=4.25,
            color="#A06461")

    # Three benchmark tasks are dashed entry points, not pipeline components.
    task_entries = [
        (1.52, "END-TO-END", "starts from inputs", contract_edge,
         [(1.52, 5.56), (1.52, 4.76)]),
        (7.19, "PRIMARY", "given verified contract", annotation_edge,
         [(7.19, 5.56), (7.19, 5.46), (6.43, 5.46), (6.43, 4.38), (6.60, 4.38)]),
        (11.27, "PROOF-ONLY", "given annotations + VCs", proof_edge,
         [(11.27, 5.56), (11.27, 5.46), (10.51, 5.46), (10.51, 4.38), (10.68, 4.38)]),
    ]
    for x, title, subtitle, color, route in task_entries:
        rounded_box(x - 0.69, 5.57, 1.38, 0.34, face="#FFFFFF", edge=color,
                    lw=0.78, radius=0.16, z=8)
        ax.text(x, 5.74, title, ha="center", va="center", fontsize=5.15,
                fontweight="bold", color=color, zorder=9)
        ax.text(x, 5.45, subtitle, ha="center", va="center", fontsize=4.35,
                color=TEXT_MUTED, zorder=9,
                bbox={"facecolor": "white", "edgecolor": "none", "pad": 0.25})
        xs, ys = zip(*route)
        ax.plot(xs, ys, color=color, lw=0.68,
                linestyle=(0, (2.2, 1.8)), zorder=4)

    ax.text(8.15, 0.14,
            "solid arrows: artifact flow   ·   curved arrows: repair feedback   ·   dashed arrows: supplied task inputs",
            ha="center", va="center", fontsize=4.55, color=TEXT_MUTED)

    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"task_design_agentic.{ext}", bbox_inches="tight", pad_inches=0.025)
    plt.close(fig)


def draw_task_design() -> None:
    """Verification flow with stage colors aligned to the nested task scopes."""
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    fig, ax = plt.subplots(figsize=(7.45, 2.88), dpi=FIG_DPI)
    fig.patch.set_facecolor("#FFFFFF")
    ax.set_facecolor("#FFFFFF")
    ax.set_xlim(-0.10, 14.55)
    ax.set_ylim(0.0, 6.05)
    ax.axis("off")

    ink = "#222222"
    muted = "#666666"
    task_blue_dark = "#2F6F8A"
    task_blue = "#5B9BB5"
    task_blue_light = "#82B6CA"

    def task_frame(x, y, w, h, label, color):
        ax.add_patch(patches.FancyBboxPatch(
            (x, y), w, h,
            boxstyle="round,pad=0.02,rounding_size=0.10",
            facecolor="none", edgecolor=color, linewidth=1.05, zorder=0,
        ))
        ax.text(x + 0.20, y + h, label, ha="left", va="center",
                fontsize=6.0, fontweight="bold", color=color, zorder=8,
                bbox={"facecolor": "white", "edgecolor": "none", "pad": 0.8})

    def stage_box(x, y, w, h, label, color, fill):
        ax.add_patch(patches.FancyBboxPatch(
            (x, y), w, h,
            boxstyle="round,pad=0.01,rounding_size=0.04",
            facecolor=fill, edgecolor=color, linewidth=0.82,
            linestyle=(0, (3, 2)), zorder=1,
        ))
        ax.text(x + 0.14, y + h, label, ha="left", va="center",
                fontsize=5.15, fontweight="semibold", color=color, zorder=7,
                bbox={"facecolor": "white", "edgecolor": "none", "pad": 0.55})

    def arrow(x0, y0, x1, y1, *, color=ink, lw=0.78, rad=0.0, z=5,
              linestyle="solid"):
        ax.add_patch(patches.FancyArrowPatch(
            (x0, y0), (x1, y1), arrowstyle="-|>", mutation_scale=7.5,
            linewidth=lw, color=color, shrinkA=0, shrinkB=0,
            connectionstyle=f"arc3,rad={rad}", linestyle=linestyle, zorder=z,
        ))

    def process(x, y, w, h, title, subtitle=""):
        ax.add_patch(patches.Rectangle(
            (x, y), w, h, facecolor="#FFFFFF", edgecolor=ink,
            linewidth=0.78, zorder=4,
        ))
        ax.text(x + w / 2, y + h / 2 + (0.09 if subtitle else 0), title,
                ha="center", va="center", fontsize=5.65,
                fontweight="semibold", color=ink, linespacing=0.90, zorder=6)
        if subtitle:
            ax.text(x + w / 2, y + h / 2 - 0.18, subtitle,
                    ha="center", va="center", fontsize=4.45,
                    color=muted, linespacing=0.90, zorder=6)

    def human_role(x, y, w, h, title, subtitle=""):
        ax.add_patch(patches.FancyBboxPatch(
            (x, y), w, h,
            boxstyle="round,pad=0.02,rounding_size=0.12",
            facecolor="#FFFFFF", edgecolor=ink, linewidth=0.82, zorder=4,
        ))
        ax.text(x + w / 2, y + h / 2 + 0.09, title,
                ha="center", va="center", fontsize=5.65,
                fontweight="semibold", color=ink, zorder=6)
        if subtitle:
            ax.text(x + w / 2, y + h / 2 - 0.18, subtitle,
                    ha="center", va="center", fontsize=4.45,
                    color=muted, zorder=6)

    def tool(x, y, w, h, title, subtitle=""):
        # Standard predefined-process shape: rectangle with double side rules.
        process(x, y, w, h, title, subtitle)
        ax.plot([x + 0.09, x + 0.09], [y, y + h], color=ink, lw=0.55, zorder=6)
        ax.plot([x + w - 0.09, x + w - 0.09], [y, y + h], color=ink, lw=0.55, zorder=6)

    def document(x, y, w, h, title, subtitle="", *, color=ink):
        verts = [
            (x, y + h), (x + w, y + h), (x + w, y + 0.12),
            (x + 0.76 * w, y - 0.02), (x + 0.50 * w, y + 0.12),
            (x + 0.24 * w, y + 0.25), (x, y + 0.12),
            (x, y + h), (x, y + h),
        ]
        codes = [MplPath.MOVETO, MplPath.LINETO, MplPath.LINETO,
                 MplPath.CURVE3, MplPath.CURVE3, MplPath.CURVE3,
                 MplPath.CURVE3, MplPath.LINETO, MplPath.CLOSEPOLY]
        ax.add_patch(patches.PathPatch(
            MplPath(verts, codes), facecolor="#FFFFFF", edgecolor=color,
            linewidth=0.78, zorder=4,
        ))
        ax.text(x + w / 2, y + h * 0.62, title, ha="center", va="center",
                fontsize=5.55, fontweight="semibold", color=color, zorder=6)
        if subtitle:
            ax.text(x + w / 2, y + h * 0.31, subtitle, ha="center", va="center",
                    fontsize=4.35, color=muted, linespacing=0.88, zorder=6)

    def document_stack(x, y, w, h, title, subtitle=""):
        # Multiple overlapping waved sheets denote a set of generated VCs.
        for dx, dy in ((0.12, 0.12), (0.06, 0.06)):
            document(x + dx, y + dy, w, h, "")
        document(x, y, w, h, title, subtitle)

    def diamond(cx, cy, rx, ry, title, subtitle=""):
        ax.add_patch(patches.Polygon(
            [(cx, cy + ry), (cx + rx, cy), (cx, cy - ry), (cx - rx, cy)],
            closed=True, facecolor="#FFFFFF", edgecolor=ink,
            linewidth=0.80, zorder=4,
        ))
        ax.text(cx, cy + (0.08 if subtitle else 0), title,
                ha="center", va="center", fontsize=5.15,
                fontweight="semibold", color=ink, linespacing=0.88, zorder=6)
        if subtitle:
            ax.text(cx, cy - 0.24, subtitle, ha="center", va="center",
                    fontsize=4.05, color=muted, zorder=6)

    def terminal(x, y, w, h, title, subtitle="", *, double=False):
        ax.add_patch(patches.FancyBboxPatch(
            (x, y), w, h,
            boxstyle=f"round,pad=0.02,rounding_size={h / 2}",
            facecolor="#FFFFFF", edgecolor=ink, linewidth=0.82, zorder=4,
        ))
        if double:
            ax.add_patch(patches.FancyBboxPatch(
                (x + 0.05, y + 0.05), w - 0.10, h - 0.10,
                boxstyle=f"round,pad=0.01,rounding_size={(h - 0.10) / 2}",
                facecolor="none", edgecolor=ink, linewidth=0.48, zorder=5,
            ))
        ax.text(x + w / 2, y + h / 2 + (0.08 if subtitle else 0), title,
                ha="center", va="center", fontsize=5.5, fontweight="bold",
                color=ink, zorder=6)
        if subtitle:
            ax.text(x + w / 2, y + h / 2 - 0.17, subtitle,
                    ha="center", va="center", fontsize=4.15, color=muted, zorder=6)

    # The three task scopes and verification stages share one exact color map.
    task_frame(1.34, 0.25, 9.82, 4.15, "END-TO-END", task_blue_dark)
    task_frame(4.05, 0.47, 7.00, 3.65, "PRIMARY", task_blue)
    task_frame(8.16, 0.69, 2.78, 3.15, "PROOF-ONLY", task_blue_light)

    stage_box(1.42, 1.25, 2.58, 1.70, "STAGE I  CONTRACT",
              task_blue_dark, "#E8F0F4")
    stage_box(4.14, 1.25, 4.02, 1.70, "STAGE II  ANNOTATION",
              task_blue, "#EDF5F8")
    stage_box(8.28, 1.25, 2.72, 1.70, "STAGE III  PROOF",
              task_blue_light, "#F2F8FA")

    # Human oversight guides one shared agent, which generates and refines
    # artifacts across all stages.
    human_role(5.90, 5.40, 1.62, 0.52, "Human", "review and guide")
    process(6.02, 4.55, 1.38, 0.52, "Agent", "generate / refine")
    arrow(6.71, 5.40, 6.71, 5.07, lw=0.68)

    y = 2.03
    document(0.18, y - 0.42, 1.05, 0.86, "Input", "NL task + C code")
    document(1.55, y - 0.42, 1.26, 0.86, "Contract", "formal contract",
             color=task_blue_dark)
    diamond(3.48, y, 0.53, 0.58, "LLM Judge", "pass?")
    document(4.30, y - 0.42, 1.34, 0.86, "Annotated C",
             "invariants +\nassertions", color=task_blue)
    tool(5.97, y - 0.36, 1.06, 0.72, "VCG", "symbolic\nexecution")
    document_stack(7.34, y - 0.42, 0.72, 0.82, "VCs", "goals")
    document(8.48, y - 0.42, 1.18, 0.86, "Proof", "Rocq script",
             color=task_blue_light)
    tool(9.94, y - 0.36, 1.02, 0.72, "Rocq", "goal check")
    diamond(11.76, y, 0.53, 0.58, "Audit", "pass?")
    terminal(12.62, y - 0.40, 1.53, 0.80, "VERIFIED", "complete artifact", double=True)
    terminal(11.23, 0.12, 1.06, 0.45, "REJECTED")

    # Main artifact flow.
    for x0, x1 in ((1.23, 1.55), (2.81, 2.95), (4.01, 4.30),
                   (5.64, 5.97), (7.03, 7.34), (8.16, 8.48),
                   (9.66, 9.94), (10.96, 11.23), (12.29, 12.62)):
        arrow(x0, y, x1, y)

    # Dashed generation links make the single Agent's role explicit.
    arrow(6.35, 4.55, 2.18, 2.46, lw=0.58, rad=0.18, z=2,
          linestyle=(0, (3, 2)))
    arrow(6.66, 4.55, 4.97, 2.46, lw=0.58, rad=0.10, z=2,
          linestyle=(0, (3, 2)))
    arrow(7.08, 4.55, 9.07, 2.46, lw=0.58, rad=-0.10, z=2,
          linestyle=(0, (3, 2)))

    # VCG failures trigger local annotation refinement. Failed proof checks can
    # refine the proof locally or expose a missing source annotation.
    arrow(6.50, 1.67, 4.97, 1.67, lw=0.66, rad=-0.25)
    ax.text(5.73, 1.16, "VCG failure  →  refine annotations",
            ha="center", va="center", fontsize=4.05, color=muted)
    arrow(10.45, 2.39, 9.07, 2.45, lw=0.66, rad=-0.28)
    ax.text(9.77, 2.69, "proof failure  →  refine proof",
            ha="center", va="center", fontsize=4.05, color=muted)
    arrow(10.45, 1.67, 4.97, 1.61, lw=0.72, rad=-0.18)
    ax.text(7.72, 0.82, "proof failure  →  refine annotations",
            ha="center", va="center", fontsize=4.25, color=muted)

    # Audit branches.
    ax.text(12.43, y + 0.18, "yes", ha="center", va="bottom",
            fontsize=4.1, color=muted)
    arrow(11.76, 1.45, 11.76, 0.57, lw=0.70)
    ax.text(11.90, 1.02, "no", ha="left", va="center",
            fontsize=4.1, color=muted)

    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"task_design_agentic.{ext}",
                    bbox_inches="tight", pad_inches=0.025)
    plt.close(fig)


def draw_primary_outcomes_table(rows: list[dict[str, object]]) -> None:
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    rows = sorted(rows, key=lambda row: MODEL_ORDER.get(str(row["label"]), 999))
    max_total = max(int(row["attempted"]) for row in rows) if rows else 102
    row_gap = 1.18
    y_positions = np.arange(len(rows))[::-1] * row_gap

    bar_left = 0.0
    bar_h = 0.30
    x_end = max_total + 12.0

    fig, ax = plt.subplots(figsize=(6.60, 2.90), dpi=FIG_DPI)
    fig.patch.set_facecolor("#FFFFFF")
    ax.set_facecolor("#FFFFFF")
    ax.set_xlim(CONFIG_HARNESS_X - 1.0, x_end)
    header_y = y_positions[0] + 0.72
    ax.set_ylim(-0.70, header_y + 0.32)
    ax.axis("off")

    ax.add_patch(
        patches.Rectangle(
            (CONFIG_HARNESS_X - 0.5, header_y - 0.29),
            x_end - CONFIG_HARNESS_X,
            0.44,
            facecolor="#F1F4F8",
            edgecolor="none",
            zorder=0,
        )
    )
    ax.plot(
        [CONFIG_HARNESS_X - 0.5, x_end - 0.2],
        [header_y - 0.31, header_y - 0.31],
        color="#CBD5E1",
        lw=0.55,
    )
    draw_config_header(ax, header_y - 0.05)
    ax.text(
        bar_left + 2.0,
        header_y - 0.05,
        "Correct / Wrong / Timeout",
        ha="left",
        va="center",
        fontsize=7.5,
        color=TEXT_MID,
    )

    for row_index, (y, row) in enumerate(zip(y_positions, rows)):
        if row_index % 2 == 1:
            ax.add_patch(
                patches.Rectangle(
                    (CONFIG_HARNESS_X - 0.5, y - 0.39),
                    x_end - CONFIG_HARNESS_X,
                    0.84,
                    facecolor="#FAFBFC",
                    edgecolor="none",
                    zorder=0,
                )
            )
        correct = int(row["correct"])
        wrong = int(row["wrong"])
        timeout = int(row["timeout"])
        attempted = int(row["attempted"])
        acc = float(row["accuracy"]) * 100.0

        draw_config_cells(ax, y, str(row["label"]))

        segment_lw = 0.55
        ax.barh(y, correct, left=bar_left, height=bar_h, color=OUTCOME_CORRECT, edgecolor="white", linewidth=segment_lw)
        ax.barh(y, wrong, left=correct, height=bar_h, color=OUTCOME_WRONG, edgecolor="white", linewidth=segment_lw)
        ax.barh(
            y,
            timeout,
            left=correct + wrong,
            height=bar_h,
            color=OUTCOME_TIMEOUT,
            edgecolor="white",
            linewidth=segment_lw,
        )
        ax.barh(
            y,
            timeout,
            left=correct + wrong,
            height=bar_h,
            facecolor="none",
            edgecolor=PAPER_GRAY_DARK,
            linewidth=0.0,
            hatch="////",
        )
        if correct >= 8:
            ax.text(correct * 0.5, y, f"{correct}", ha="center", va="center", fontsize=7.2, color="#FFFFFF")
        if wrong >= 8:
            ax.text(correct + wrong * 0.5, y, f"{wrong}", ha="center", va="center", fontsize=7.0, color="#FFFFFF")
        if timeout >= 8:
            ax.text(
                correct + wrong + timeout * 0.5,
                y,
                f"{timeout}",
                ha="center",
                va="center",
                fontsize=7.0,
                color=TEXT_MID,
            )
        ax.text(attempted + 1.6, y, f"{acc:.1f}%", ha="left", va="center", fontsize=6.9, color=TEXT_MUTED)

    axis_y = -0.43
    ax.plot([bar_left, max_total], [axis_y, axis_y], color="#CBD5E1", lw=0.55)
    for tick in [0, 50, 100]:
        if tick <= max_total:
            ax.plot([tick, tick], [axis_y - 0.05, axis_y + 0.05], color="#CBD5E1", lw=0.55)
            ax.text(tick, axis_y - 0.18, str(tick), ha="center", va="center", fontsize=6.8, color=TEXT_MUTED)

    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"primary_outcomes_models.{ext}", bbox_inches="tight", pad_inches=0.025)
    plt.close(fig)


def draw_primary_cost_table(rows: list[dict[str, object]]) -> None:
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    rows = sorted(rows, key=lambda row: MODEL_ORDER.get(str(row["label"]), 999))
    max_minutes = max(float(row["avg_minutes"]) for row in rows) if rows else 80.0
    max_input = max(float(row["avg_input_tokens_m"]) for row in rows) if rows else 35.0
    max_output = max(float(row["avg_output_tokens_k"]) for row in rows) if rows else 250.0
    max_tools = max(float(row["avg_tool_calls"]) for row in rows) if rows else 300.0
    max_minutes = max(60.0, np.ceil(max_minutes / 10.0) * 10.0)
    max_input = max(10.0, np.ceil(max_input / 5.0) * 5.0)
    max_output = max(50.0, np.ceil(max_output / 50.0) * 50.0)
    max_tools = max(50.0, np.ceil(max_tools / 50.0) * 50.0)

    col_specs = [
        ("Min.", 0.0, max_minutes, lambda row: float(row["avg_minutes"]), "{:.1f}"),
        ("Input tok. (M)", 32.5, max_input, lambda row: float(row["avg_input_tokens_m"]), "{:.1f}"),
        ("Output tok. (K)", 65.0, max_output, lambda row: float(row["avg_output_tokens_k"]), "{:.0f}"),
        ("Tool calls", 97.5, max_tools, lambda row: float(row["avg_tool_calls"]), "{:.1f}"),
    ]
    col_width = 20.0
    x_end = 127.0
    row_gap = 1.18
    y_positions = np.arange(len(rows))[::-1] * row_gap

    fig, ax = plt.subplots(figsize=(7.05, 2.92), dpi=FIG_DPI)
    fig.patch.set_facecolor("#FFFFFF")
    ax.set_facecolor("#FFFFFF")
    ax.set_xlim(CONFIG_HARNESS_X - 1.0, x_end)
    header_y = y_positions[0] + 0.72
    ax.set_ylim(-0.70, header_y + 0.32)
    ax.axis("off")

    ax.add_patch(
        patches.Rectangle(
            (CONFIG_HARNESS_X - 0.5, header_y - 0.29),
            x_end - CONFIG_HARNESS_X,
            0.44,
            facecolor="#F1F4F8",
            edgecolor="none",
            zorder=0,
        )
    )
    ax.plot(
        [CONFIG_HARNESS_X - 0.5, x_end - 0.2],
        [header_y - 0.31, header_y - 0.31],
        color="#CBD5E1",
        lw=0.55,
    )
    draw_config_header(ax, header_y - 0.05)
    for label, left, _max_value, _getter, _fmt in col_specs:
        ax.text(left, header_y - 0.05, label, ha="left", va="center", fontsize=7.5, color=TEXT_MID)

    for row_index, (y, row) in enumerate(zip(y_positions, rows)):
        if row_index % 2 == 1:
            ax.add_patch(
                patches.Rectangle(
                    (CONFIG_HARNESS_X - 0.5, y - 0.38),
                    x_end - CONFIG_HARNESS_X,
                    0.84,
                    facecolor="#FAFBFC",
                    edgecolor="none",
                    zorder=0,
                )
            )
        draw_config_cells(ax, y, str(row["label"]))
        for metric_index, (_label, left, max_value, getter, fmt) in enumerate(col_specs):
            value = getter(row)
            width = col_width * value / max_value if max_value else 0.0
            color = COST_COLUMN_RAMP[metric_index]
            ax.barh(y, width, left=left, height=0.24, color=color, edgecolor="white", linewidth=0.45)
            ax.text(left + width + 0.8, y, fmt.format(value), ha="left", va="center", fontsize=7.0, color=TEXT_DARK)

    axis_y = -0.40
    for _label, left, max_value, _getter, _fmt in col_specs:
        ax.plot([left, left + col_width], [axis_y, axis_y], color="#CBD5E1", lw=0.55)
        ax.text(left, axis_y - 0.17, "0", ha="center", va="center", fontsize=6.8, color=TEXT_MUTED)
        ax.text(left + col_width, axis_y - 0.17, f"{max_value:.0f}", ha="center", va="center", fontsize=6.8, color=TEXT_MUTED)

    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"primary_cost_models.{ext}", bbox_inches="tight", pad_inches=0.025)
    plt.close(fig)


def draw_harness_metric_table(rows: list[dict[str, object]]) -> None:
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    rows = list(rows)
    harness_order = ["Codex CLI", "OpenCode", "Claude Code"]
    rows.sort(key=lambda row: harness_order.index(str(row["harness"])) if str(row["harness"]) in harness_order else 99)

    metrics = [
        ("Err.", lambda row: float(row["errors"]), lambda row: f"{int(row['errors'])}/8"),
        ("Min.", lambda row: float(row["avg_minutes"]), lambda row: f"{float(row['avg_minutes']):.1f}"),
        ("In M", lambda row: float(row["avg_input_tokens"]) / 1_000_000.0, lambda row: f"{float(row['avg_input_tokens']) / 1_000_000:.1f}"),
        ("Out K", lambda row: float(row["avg_output_tokens"]) / 1_000.0, lambda row: f"{float(row['avg_output_tokens']) / 1_000:.0f}"),
        ("Tools", lambda row: float(row["avg_tool_calls"]), lambda row: f"{float(row['avg_tool_calls']):.0f}"),
        ("Code+", lambda row: float(row["avg_generated_code_lines"]), lambda row: f"{float(row['avg_generated_code_lines']):.0f}"),
    ]
    maxima = [max(getter(row) for row in rows) if rows else 1.0 for _label, getter, _fmt in metrics]

    fig, ax = plt.subplots(figsize=(5.65, 1.72), dpi=FIG_DPI)
    fig.patch.set_facecolor("#FFFFFF")
    ax.set_facecolor("#FFFFFF")
    ax.set_xlim(0.0, 1.0)
    ax.set_ylim(0.0, 4.0)
    ax.axis("off")

    ax.add_patch(patches.Rectangle((0.02, 3.34), 0.96, 0.42, facecolor="#F1F4F8", edgecolor="none"))
    ax.plot([0.02, 0.98], [3.33, 3.33], color="#CBD5E1", lw=0.55)
    ax.text(0.04, 3.55, "Harness", ha="left", va="center", fontsize=7.2, color=TEXT_MID)
    col_x = [0.24, 0.36, 0.49, 0.62, 0.75, 0.88]
    track_w = 0.060
    for x, (label, _getter, _fmt) in zip(col_x, metrics):
        ax.text(x, 3.55, label, ha="left", va="center", fontsize=6.8, color=TEXT_MID)

    for i, row in enumerate(rows):
        y = 2.70 - i * 0.78
        if i % 2 == 1:
            ax.add_patch(patches.Rectangle((0.02, y - 0.30), 0.96, 0.58, facecolor="#FAFBFC", edgecolor="none"))
        color = str(row["color"])
        ax.add_patch(patches.Rectangle((0.04, y - 0.045), 0.018, 0.09, facecolor=color, edgecolor="none"))
        ax.text(0.065, y, str(row["harness"]), ha="left", va="center", fontsize=7.1, color=TEXT_DARK)
        for x, (metric, maximum) in zip(col_x, zip(metrics, maxima)):
            _label, getter, formatter = metric
            value = getter(row)
            scale = value / maximum if maximum else 0.0
            ax.add_patch(
                patches.Rectangle((x, y - 0.055), track_w, 0.11, facecolor="#E5E7EB", edgecolor="none")
            )
            ax.add_patch(
                patches.Rectangle((x, y - 0.055), track_w * scale, 0.11, facecolor=color, edgecolor="none")
            )
            ax.text(x + track_w + 0.010, y, formatter(row), ha="left", va="center", fontsize=6.6, color=TEXT_DARK)

    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"harness_outcomes_models.{ext}", bbox_inches="tight", pad_inches=0.025)
    plt.close(fig)


def draw_primary_outcomes(rows: list[dict[str, object]]) -> None:
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    rows = sorted(rows, key=lambda row: MODEL_ORDER.get(str(row["label"]), 999))
    max_total = max(int(row["attempted"]) for row in rows) if rows else 102

    fig, ax = plt.subplots(figsize=FIGSIZE_OUTCOMES, dpi=FIG_DPI)
    fig.patch.set_facecolor("#FFFFFF")
    ax.set_facecolor("#FFFFFF")
    fig.subplots_adjust(left=0.42, right=0.93, top=0.88, bottom=0.17)

    y_positions = np.arange(len(rows))[::-1]
    bar_h = 0.52

    for y, row in zip(y_positions, rows):
        correct = int(row["correct"])
        wrong = int(row["wrong"])
        timeout = int(row["timeout"])
        attempted = int(row["attempted"])
        acc = float(row["accuracy"])

        ax.barh(y, correct, height=bar_h, color=color, edgecolor="white", linewidth=0.9)
        ax.barh(
            y,
            wrong,
            left=correct,
            height=bar_h,
            color=tint(color, 0.50),
            edgecolor="white",
            linewidth=0.9,
        )
        ax.barh(
            y,
            timeout,
            left=correct + wrong,
            height=bar_h,
            color="#E5E7EB",
            edgecolor="white",
            linewidth=0.9,
            hatch="////",
        )
        if correct > 0:
            ax.text(
                max(1.0, correct * 0.50),
                y,
                f"{correct}",
                va="center",
                ha="center",
                fontsize=9.0,
                color="white" if correct >= 9 else TEXT_DARK,
                fontweight="bold",
            )
        ax.text(
            attempted + 1.5,
            y,
            f"{correct}/{attempted} ({acc * 100:.1f}%)",
            va="center",
            ha="left",
            fontsize=9.0,
            color=TEXT_DARK,
        )

    labels = [display_model_label(str(row["label"])) for row in rows]
    ax.set_yticks(y_positions)
    ax.set_yticklabels(labels, fontsize=9.0, color=TEXT_DARK)
    ax.tick_params(axis="y", length=0, pad=2)
    for tick in ax.get_yticklabels():
        tick.set_fontweight("semibold")

    ax.set_xlim(0, max_total + 26)
    ax.set_ylim(-0.7, len(rows) - 0.3)
    ax.set_xlabel("attempted primary-task runs", fontsize=9.0, color=TEXT_MID, labelpad=5)
    ax.set_xticks([0, 40, 80, 120])
    ax.tick_params(axis="x", labelsize=9.0, colors=TEXT_MUTED, length=0)
    ax.xaxis.grid(True, color=GRID, linewidth=0.65)
    ax.set_axisbelow(True)
    for spine in ax.spines.values():
        spine.set_visible(False)

    legend_y = len(rows) - 0.03
    legend_x = 40
    legend_items = [
        ("Correct", TEXT_DARK, None),
        ("Wrong", "#9CA3AF", None),
        ("Timeout", TIMEOUT_FILL, "////"),
    ]
    for i, (label, color, hatch) in enumerate(legend_items):
        x = legend_x + i * 24
        ax.barh(legend_y, 6.0, left=x, height=0.18, color=color, hatch=hatch, edgecolor="#9CA3AF", clip_on=False)
        ax.text(x + 7.2, legend_y, label, va="center", ha="left", fontsize=9.0, color=TEXT_MID)

    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"primary_outcomes_models.{ext}", bbox_inches="tight", pad_inches=0.03)
    plt.close(fig)


def draw_primary_results_summary(rows: list[dict[str, object]]) -> None:
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    rows = sorted(rows, key=lambda row: MODEL_ORDER.get(str(row["label"]), 999))
    max_total = max(int(row["attempted"]) for row in rows) if rows else 102
    max_minutes = max(float(row["avg_minutes"]) for row in rows) if rows else 80.0
    max_input = max(float(row["avg_input_tokens_m"]) for row in rows) if rows else 35.0
    max_output = max(float(row["avg_output_tokens_k"]) for row in rows) if rows else 250.0
    max_tools = max(float(row["avg_tool_calls"]) for row in rows) if rows else 120.0
    max_minutes = max(60.0, np.ceil(max_minutes / 10.0) * 10.0)
    max_input = max(10.0, np.ceil(max_input / 5.0) * 5.0)
    max_output = max(50.0, np.ceil(max_output / 50.0) * 50.0)
    max_tools = max(50.0, np.ceil(max_tools / 25.0) * 25.0)

    label_x = -56.0
    outcome_left = 0.0
    outcome_width = 56.0
    result_x = outcome_left + outcome_width + 2.0
    min_left = 78.0
    input_left = 122.0
    output_left = 166.0
    tool_left = 210.0
    cost_width = 29.0
    y_positions = np.arange(len(rows))[::-1]

    fig, ax = plt.subplots(figsize=(6.25, 3.55), dpi=FIG_DPI)
    fig.patch.set_facecolor("#FFFFFF")
    ax.set_facecolor("#FFFFFF")
    fig.subplots_adjust(left=0.015, right=0.995, top=0.88, bottom=0.18)

    bar_h = 0.32
    for y, row in zip(y_positions, rows):
        color = str(row["color"])
        correct = int(row["correct"])
        wrong = int(row["wrong"])
        timeout = int(row["timeout"])
        attempted = int(row["attempted"])
        acc = float(row["accuracy"]) * 100.0
        minutes = float(row["avg_minutes"])
        input_tokens_m = float(row["avg_input_tokens_m"])
        output_tokens_k = float(row["avg_output_tokens_k"])
        tools = float(row["avg_tool_calls"])

        correct_w = outcome_width * correct / max_total
        wrong_w = outcome_width * wrong / max_total
        timeout_w = outcome_width * timeout / max_total
        ax.barh(
            y,
            correct_w,
            left=outcome_left,
            height=bar_h,
            color=OUTCOME_CORRECT,
            edgecolor="white",
            linewidth=0.55,
        )
        ax.barh(
            y,
            wrong_w,
            left=outcome_left + correct_w,
            height=bar_h,
            color=OUTCOME_WRONG,
            edgecolor="white",
            linewidth=0.55,
        )
        ax.barh(
            y,
            timeout_w,
            left=outcome_left + correct_w + wrong_w,
            height=bar_h,
            color=OUTCOME_TIMEOUT,
            edgecolor="white",
            linewidth=0.55,
        )
        if correct_w > 4.0:
            ax.text(
                outcome_left + correct_w * 0.50,
                y,
                str(correct),
                ha="center",
                va="center",
                fontsize=7.8,
                color="#FFFFFF",
                fontweight="bold",
            )

        ax.barh(y + 0.25, 2.0, left=label_x, height=0.13, color=color, edgecolor="none")
        ax.text(
            label_x + 2.8,
            y + 0.15,
            display_primary_label(str(row["label"])),
            ha="left",
            va="center",
            fontsize=7.6,
            color=TEXT_DARK,
            fontweight="semibold",
            linespacing=0.92,
        )
        ax.text(
            label_x + 2.8,
            y - 0.24,
            f"{correct}/{wrong}/{timeout}   {acc:.1f}%",
            ha="left",
            va="center",
            fontsize=7.2,
            color=TEXT_MUTED,
        )
        ax.text(result_x, y, f"{correct}/{attempted}", ha="left", va="center", fontsize=7.8, color=TEXT_DARK)

        min_w = cost_width * minutes / max_minutes if max_minutes else 0.0
        input_w = cost_width * input_tokens_m / max_input if max_input else 0.0
        output_w = cost_width * output_tokens_k / max_output if max_output else 0.0
        tool_w = cost_width * tools / max_tools if max_tools else 0.0
        ax.barh(y, min_w, left=min_left, height=0.24, color=COST_COLUMN_RAMP[0], edgecolor="white", linewidth=0.45)
        ax.barh(y, input_w, left=input_left, height=0.24, color=COST_COLUMN_RAMP[1], edgecolor="white", linewidth=0.45)
        ax.barh(
            y,
            output_w,
            left=output_left,
            height=0.24,
            color=COST_COLUMN_RAMP[2],
            edgecolor="white",
            linewidth=0.45,
        )
        ax.barh(y, tool_w, left=tool_left, height=0.24, color=COST_COLUMN_RAMP[3], edgecolor="white", linewidth=0.45)
        ax.text(min_left + min_w + 0.7, y, f"{minutes:.1f}", ha="left", va="center", fontsize=7.6, color=TEXT_DARK)
        ax.text(input_left + input_w + 0.7, y, f"{input_tokens_m:.1f}", ha="left", va="center", fontsize=7.6, color=TEXT_DARK)
        ax.text(output_left + output_w + 0.7, y, f"{output_tokens_k:.0f}", ha="left", va="center", fontsize=7.6, color=TEXT_DARK)
        ax.text(tool_left + tool_w + 0.7, y, f"{tools:.1f}", ha="left", va="center", fontsize=7.6, color=TEXT_DARK)

    header_y = len(rows) - 0.05
    ax.text(label_x, header_y, "Model", ha="left", va="center", fontsize=8.0, color=TEXT_MID, fontweight="bold")
    ax.text(outcome_left, header_y, "C/W/T\noutcomes", ha="left", va="center", fontsize=8.0, color=TEXT_MID, fontweight="bold", linespacing=0.9)
    ax.text(min_left, header_y, "Min.", ha="left", va="center", fontsize=8.0, color=TEXT_MID, fontweight="bold")
    ax.text(input_left, header_y, "Input tok.\n(M)", ha="left", va="center", fontsize=8.0, color=TEXT_MID, fontweight="bold", linespacing=0.9)
    ax.text(output_left, header_y, "Output tok.\n(K)", ha="left", va="center", fontsize=8.0, color=TEXT_MID, fontweight="bold", linespacing=0.9)
    ax.text(tool_left, header_y, "Tool\ncalls", ha="left", va="center", fontsize=8.0, color=TEXT_MID, fontweight="bold", linespacing=0.9)

    axis_specs = [
        (outcome_left, outcome_width, str(max_total)),
        (min_left, cost_width, f"{max_minutes:.0f}"),
        (input_left, cost_width, f"{max_input:.0f}"),
        (output_left, cost_width, f"{max_output:.0f}"),
        (tool_left, cost_width, f"{max_tools:.0f}"),
    ]
    for x, xmax, label in axis_specs:
        ax.plot([x, x + xmax], [-0.62, -0.62], color=GRID, linewidth=0.55, clip_on=False)
        ax.text(x, -0.87, "0", ha="center", va="center", fontsize=7.6, color=TEXT_MUTED)
        ax.text(x + xmax, -0.87, label, ha="center", va="center", fontsize=7.6, color=TEXT_MUTED)

    legend_y = -1.15
    legend_items = [
        ("Correct", OUTCOME_CORRECT, None),
        ("Wrong", OUTCOME_WRONG, None),
        ("Timeout", OUTCOME_TIMEOUT, None),
    ]
    for i, (label, color, hatch) in enumerate(legend_items):
        x = outcome_left + i * 29.0
        ax.barh(legend_y, 4.0, left=x, height=0.16, color=color, edgecolor="#9CA3AF", hatch=hatch, clip_on=False)
        ax.text(x + 4.7, legend_y, label, ha="left", va="center", fontsize=7.6, color=TEXT_MUTED)

    ax.set_xlim(label_x - 1.5, tool_left + cost_width + 12.0)
    ax.set_ylim(-1.32, len(rows) - 0.50)
    ax.set_xticks([])
    ax.set_yticks([])
    for spine in ax.spines.values():
        spine.set_visible(False)

    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"primary_results_summary.{ext}", bbox_inches="tight", pad_inches=0.025)
    plt.close(fig)


def draw_harness_outcomes(rows: list[dict[str, object]]) -> None:
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    model_order = ["GLM-5.2", "DeepSeek-V4-Pro"]
    harness_order = ["Codex CLI", "OpenCode", "Claude Code"]
    by_key = {(str(row["model"]), str(row["harness"])): row for row in rows}
    max_total = max(int(row["attempted"]) for row in rows) if rows else 102

    fig, ax = plt.subplots(figsize=(7.2, 3.65), dpi=220)
    fig.patch.set_facecolor("#FFFFFF")
    ax.set_facecolor("#FFFFFF")

    y_positions: dict[tuple[str, str], float] = {}
    y = 5.0
    for model in model_order:
        for harness in harness_order:
            y_positions[(model, harness)] = y
            y -= 0.70
        y -= 0.55

    bar_h = 0.42
    group_header_x = -42
    label_x = -27
    for model in model_order:
        group_y = y_positions[(model, harness_order[0])] + 0.43
        ax.text(
            group_header_x,
            group_y,
            model,
            va="center",
            ha="left",
            fontsize=9.0,
            color="#111827",
            fontweight="bold",
        )
        for harness in harness_order:
            row = by_key[(model, harness)]
            row_y = y_positions[(model, harness)]
            color = str(row["color"])
            correct = int(row["correct"])
            wrong = int(row["wrong"])
            timeout = int(row["timeout"])
            attempted = int(row["attempted"])
            acc = float(row["accuracy"])

            ax.text(label_x, row_y, harness, va="center", ha="left", fontsize=9.0, color="#374151")
            ax.barh(row_y, correct, height=bar_h, color=color, edgecolor="white", linewidth=0.8)
            ax.barh(
                row_y,
                wrong,
                left=correct,
                height=bar_h,
                color=tint(color, 0.55),
                edgecolor="white",
                linewidth=0.8,
            )
            ax.barh(
                row_y,
                timeout,
                left=correct + wrong,
                height=bar_h,
                color="#E5E7EB",
                edgecolor="white",
                linewidth=0.8,
                hatch="////",
            )
            if correct > 0:
                ax.text(
                    min(correct * 0.50, correct - 0.2),
                    row_y,
                    f"{correct}",
                    va="center",
                    ha="center",
                    fontsize=9.0,
                    color="white" if correct >= 5 else "#111827",
                    fontweight="bold",
                )
            ax.text(
                attempted + 1.3,
                row_y,
                f"{correct}/{attempted} ({acc * 100:.1f}%)",
                va="center",
                ha="left",
                fontsize=9.0,
                color="#111827",
            )

    legend_y = 5.92
    legend_items = [
        ("Codex CLI", HARNESS_CODEX_GRAY),
        ("OpenCode", HARNESS_OPENCODE_BLUE),
        ("Claude Code", HARNESS_CLAUDE_ORANGE),
    ]
    for i, (label, color) in enumerate(legend_items):
        x = -27 + i * 31
        ax.barh(legend_y, 5.0, left=x, height=0.18, color=color, edgecolor="white", clip_on=False)
        ax.text(x + 6.2, legend_y, label, va="center", ha="left", fontsize=9.0, color="#374151")
    ax.text(
        75,
        legend_y,
        "solid=Correct, pale=Wrong, hatched=Timeout",
        va="center",
        ha="left",
        fontsize=9.0,
        color="#6B7280",
    )

    ax.set_xlim(-45, max_total + 35)
    ax.set_ylim(0.25, 6.25)
    ax.set_yticks([])
    ax.set_xlabel("attempted primary-task runs", fontsize=9.0, color="#374151", labelpad=7)
    ax.set_xticks([0, 20, 40, 60, 80, 100])
    ax.tick_params(axis="x", labelsize=9.0, colors="#4B5563", length=0)
    ax.xaxis.grid(True, color="#E5E7EB", linewidth=0.7)
    ax.set_axisbelow(True)
    for spine in ax.spines.values():
        spine.set_visible(False)

    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"harness_outcomes_models.{ext}", bbox_inches="tight", pad_inches=0.03)
    plt.close(fig)


def draw_harness_radar(rows: list[dict[str, object]]) -> None:
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    rows = add_radar_scores(rows)
    axes = [
        ("score_errors", "Errors", lambda row: f"{int(row['errors'])}/8"),
        ("score_time", "Time", lambda row: f"{float(row['avg_minutes']):.1f}m"),
        ("score_input_tokens", "Input\ntokens", lambda row: f"{float(row['avg_input_tokens']) / 1_000_000:.1f}M"),
        ("score_output_tokens", "Output\ntokens", lambda row: f"{float(row['avg_output_tokens']) / 1_000:.0f}k"),
        ("score_tool_calls", "Tool\ncalls", lambda row: f"{float(row['avg_tool_calls']):.0f}"),
        ("score_generated_code_lines", "Code+", lambda row: f"{float(row['avg_generated_code_lines']):.0f}"),
    ]
    angles = np.linspace(0, 2 * np.pi, len(axes), endpoint=False)
    closed_angles = np.concatenate([angles, [angles[0]]])

    # Larger native canvas so the radar prints with good presence while its text
    # still renders at the same on-page size as the other figures.
    fig, ax = plt.subplots(figsize=(4.15, 3.55), dpi=FIG_DPI, subplot_kw={"projection": "polar"})
    fig.patch.set_facecolor("#FFFFFF")
    ax.set_facecolor("#FFFFFF")
    fig.subplots_adjust(left=0.11, right=0.89, top=0.88, bottom=0.20)
    ax.set_theta_offset(np.pi / 2)
    ax.set_theta_direction(-1)
    ax.set_ylim(0, 1.30)

    ax.set_xticks(angles)
    ax.set_xticklabels([label for _, label, _ in axes], fontsize=7.6, color=TEXT_DARK)
    ax.tick_params(axis="x", pad=4)
    ax.set_yticks([0.25, 0.50, 0.75, 1.00])
    # Node labels already carry the raw values; the numeric radial ticks only
    # collide with them near the crowded centre, so keep the rings but hide the
    # numbers.
    ax.set_yticklabels([])
    ax.set_rlabel_position(90)
    ax.yaxis.grid(True, color=GRID, linewidth=0.55, linestyle="--", dashes=(2, 2))
    ax.xaxis.grid(True, color=GRID, linewidth=0.55, linestyle="--", dashes=(2, 2))
    ax.spines["polar"].set_color(FRAME)
    ax.spines["polar"].set_linewidth(0.75)

    series_values: list[np.ndarray] = []
    for row in rows:
        color = str(row["color"])
        values = np.array([float(row[key]) for key, _, _ in axes])
        series_values.append(values)
        closed_values = np.concatenate([values, [values[0]]])
        ax.plot(
            closed_angles,
            closed_values,
            color=color,
            linewidth=1.6,
            marker="o",
            markersize=4.0,
            markerfacecolor="#FFFFFF",
            markeredgewidth=1.1,
            label=str(row["harness"]),
            zorder=4,
        )
        ax.fill(closed_angles, closed_values, color=color, alpha=0.11, zorder=2)

    # Value labels: on each axis the series' labels are stacked along the spoke
    # in value order with a collision-free minimum gap. The gap accounts for the
    # spoke's on-screen orientation: side-facing spokes separate labels
    # horizontally (box width matters), vertical spokes separate them vertically
    # (box height matters). Labels use dark ink for legibility; the box border
    # carries the series color.
    label_h = 0.15
    r_min, r_max = 0.16, 1.18
    for axis_index, (angle, (_key, _axis_label, formatter)) in enumerate(zip(angles, axes)):
        horiz = abs(np.sin(angle))  # screen-x component of the spoke
        vert = abs(np.cos(angle))   # screen-y component of the spoke
        entries = sorted(
            ((float(series_values[row_index][axis_index]), row_index) for row_index in range(len(rows))),
            reverse=True,
        )
        placed: list[tuple[float, int, str]] = []
        previous_r: float | None = None
        previous_w = 0.0
        for value, row_index in entries:
            text = formatter(rows[row_index])
            width = 0.055 * len(text) + 0.07
            r = min(max(value, 0.10) + 0.12, r_max)
            if previous_r is not None:
                gap_h = (previous_w + width) / 2.0 / max(horiz, 1e-6)
                gap_v = label_h / max(vert, 1e-6)
                r = min(r, previous_r - min(gap_h, gap_v))
            placed.append((r, row_index, text))
            previous_r = r
            previous_w = width
        # If the stack ran below the readable band, shift it outward as a whole.
        lift = max(0.0, r_min - min(r for r, _, _ in placed))
        for r, row_index, text in placed:
            ax.text(
                angle,
                min(r + lift, 1.24),
                text,
                ha="center",
                va="center",
                fontsize=6.4,
                color=TEXT_DARK,
                bbox={
                    "boxstyle": "round,pad=0.12",
                    "facecolor": "white",
                    "edgecolor": str(rows[row_index]["color"]),
                    "linewidth": 0.6,
                    "alpha": 0.95,
                },
                zorder=8,
            )

    ax.legend(
        loc="upper center",
        bbox_to_anchor=(0.5, -0.22),
        ncol=3,
        frameon=False,
        fontsize=7.2,
        handlelength=1.5,
        columnspacing=0.50,
        handletextpad=0.35,
    )

    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"harness_outcomes_models.{ext}", bbox_inches="tight", pad_inches=0.03)
    plt.close(fig)


def draw_branch_difficulty(
    stage_minutes: tuple[float, float, float] | None = None,
    branch_rows: list[tuple[str, int, int, str]] | None = None,
) -> None:
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    if branch_rows is None:
        branch_rows = [
            ("End-to-end", 16, 95, TASK_SCOPE_END_TO_END),
            ("Primary", 31, 102, TASK_SCOPE_PRIMARY),
            ("Proof-only", 69, 104, TASK_SCOPE_PROOF_ONLY),
        ]
    if stage_minutes is None:
        _, contract_min = average_minutes_from_run_logs(
            CAV_BENCH_ROOT / "pipeline_results/codex/gpt-5.4/medium",
            "contract_*",
            8.4,
        )
        _, annotation_min = average_minutes_from_run_logs(
            RESULTS_ROOT / "codex/gpt-5.4/medium",
            "verify_*",
            26.3,
        )
        _, verify_min = average_minutes_from_run_logs(
            CAV_BENCH_ROOT / "proof_results/codex/gpt-5.4/medium",
            "proof_*",
            20.6,
        )
    else:
        contract_min, annotation_min, verify_min = stage_minutes
    stage_specs = [
        ("Contract", contract_min, TASK_CONTRACT),
        ("Annotation", annotation_min, TASK_ANNOTATION),
        ("Proof", verify_min, TASK_PROOF),
    ]
    task_time_rows = [
        ("End-to-end", [contract_min, annotation_min, verify_min], TASK_SCOPE_END_TO_END),
        ("Primary", [0.0, annotation_min, verify_min], TASK_SCOPE_PRIMARY),
        ("Proof-only", [0.0, 0.0, verify_min], TASK_SCOPE_PROOF_ONLY),
    ]

    max_branch_total = max(total for _, _correct, total, _color in branch_rows)
    max_task_minutes = max(sum(values) for _, values, _color in task_time_rows)
    max_task_minutes = max(50.0, np.ceil(max_task_minutes / 10.0) * 10.0)

    row_gap = 1.18
    y_positions = np.arange(len(branch_rows))[::-1] * row_gap

    left_label_x = 0.0
    left_bar_x = 17.0
    left_bar_w = 50.0
    right_bar_x = 84.0
    right_bar_w = 52.0
    right_value_x = right_bar_x + right_bar_w + 2.6
    x_end = right_value_x + 13.0

    fig, ax = plt.subplots(figsize=(5.2, 2.28), dpi=FIG_DPI)
    fig.patch.set_facecolor("#FFFFFF")
    ax.set_facecolor("#FFFFFF")
    ax.set_xlim(left_label_x - 1.0, x_end)
    header_y = y_positions[0] + 0.72
    ax.set_ylim(-0.70, header_y + 0.32)
    ax.axis("off")

    ax.add_patch(
        patches.Rectangle(
            (left_label_x - 0.5, header_y - 0.29),
            x_end - left_label_x,
            0.44,
            facecolor="#F1F4F8",
            edgecolor="none",
            zorder=0,
        )
    )
    ax.plot([left_label_x - 0.5, x_end - 0.2], [header_y - 0.31, header_y - 0.31], color="#CBD5E1", lw=0.55)
    ax.text(left_label_x, header_y - 0.05, "Branch", ha="left", va="center", fontsize=7.5, color=TEXT_MID)
    ax.text(left_bar_x, header_y - 0.05, "(a) Solved / Other", ha="left", va="center", fontsize=7.5, color=TEXT_MID)
    ax.text(right_bar_x, header_y - 0.05, "(b) Stage time (C/A/P)", ha="left", va="center", fontsize=7.5, color=TEXT_MID)
    ax.text(right_value_x, header_y - 0.05, "Min.", ha="left", va="center", fontsize=7.5, color=TEXT_MID)

    bar_h = 0.30
    segment_lw = 0.55
    for row_index, y in enumerate(y_positions):
        if row_index % 2 == 1:
            ax.add_patch(
                patches.Rectangle(
                    (left_label_x - 0.5, y - 0.38),
                    x_end - left_label_x,
                    0.84,
                    facecolor="#FAFBFC",
                    edgecolor="none",
                    zorder=0,
                )
            )

    for y, (label, correct, total, color) in zip(y_positions, branch_rows):
        other = total - correct
        correct_w = left_bar_w * correct / max_branch_total
        other_w = left_bar_w * other / max_branch_total
        ax.text(left_label_x, y, label, ha="left", va="center", fontsize=6.9, color=TEXT_DARK)
        ax.barh(y, correct_w, left=left_bar_x, height=bar_h, color=color, edgecolor="white", linewidth=segment_lw)
        ax.barh(
            y,
            other_w,
            left=left_bar_x + correct_w,
            height=bar_h,
            color=OUTCOME_TIMEOUT,
            edgecolor="white",
            linewidth=segment_lw,
        )
        ax.text(
            left_bar_x + correct_w + other_w + 1.5,
            y,
            f"{correct}/{total}",
            ha="left",
            va="center",
            fontsize=6.9,
            color=TEXT_MUTED,
        )

    for y, (task_label, values, task_color) in zip(y_positions, task_time_rows):
        left = 0.0
        for value, (_stage_label, _stage_minutes, _stage_color) in zip(values, stage_specs):
            if value <= 0:
                continue
            width = right_bar_w * value / max_task_minutes
            ax.barh(
                y,
                width,
                left=right_bar_x + left,
                height=bar_h,
                color=task_color,
                edgecolor="white",
                linewidth=segment_lw,
            )
            left += width
        total_minutes = sum(values)
        ax.text(
            right_value_x,
            y,
            f"{total_minutes:.1f}",
            ha="left",
            va="center",
            fontsize=7.0,
            color=TEXT_DARK,
        )

    axis_y = -0.40
    ax.plot([left_bar_x, left_bar_x + left_bar_w], [axis_y, axis_y], color="#CBD5E1", lw=0.55)
    for tick in [0, 50, 100]:
        x = left_bar_x + left_bar_w * tick / max_branch_total
        ax.plot([x, x], [axis_y - 0.05, axis_y + 0.05], color="#CBD5E1", lw=0.55)
        ax.text(x, axis_y - 0.17, str(tick), ha="center", va="center", fontsize=6.8, color=TEXT_MUTED)
    ax.text(left_bar_x + left_bar_w * 0.5, axis_y - 0.38, "runs", ha="center", va="center", fontsize=6.8, color=TEXT_MID)

    ax.plot([right_bar_x, right_bar_x + right_bar_w], [axis_y, axis_y], color="#CBD5E1", lw=0.55)
    for tick in [0, 25, 50]:
        x = right_bar_x + right_bar_w * tick / max_task_minutes
        ax.plot([x, x], [axis_y - 0.05, axis_y + 0.05], color="#CBD5E1", lw=0.55)
        ax.text(x, axis_y - 0.17, str(tick), ha="center", va="center", fontsize=6.8, color=TEXT_MUTED)
    ax.text(
        right_bar_x + right_bar_w * 0.5,
        axis_y - 0.38,
        "average wall-clock minutes",
        ha="center",
        va="center",
        fontsize=6.8,
        color=TEXT_MID,
    )

    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"branch_difficulty.{ext}", bbox_inches="tight", pad_inches=0.025)
    plt.close(fig)


def harness_tasks_by_model() -> dict[str, list[str]]:
    tasks_by_model: dict[str, list[str]] = {}
    models = sorted({series.model for series in HARNESS_SERIES})
    for model in models:
        model_series = [series for series in HARNESS_SERIES if series.model == model]
        task_sets = [set(latest_workspaces(series.result_dir)) for series in model_series]
        common_tasks = set.intersection(*task_sets) if task_sets else set()
        preferred = [task for task in HARNESS_CLAUDE_SHARED_TASKS if task in common_tasks]
        tasks_by_model[model] = preferred or sorted(common_tasks)
    return tasks_by_model


def draw_harness_comparison(rows: list[dict[str, object]]) -> None:
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    model_order = ["GLM-5.2", "DeepSeek-V4-Pro"]
    harness_order = ["Codex CLI", "OpenCode", "Claude Code"]
    by_key = {(str(row["model"]), str(row["harness"])): row for row in rows}
    max_total = max(int(row["attempted"]) for row in rows) if rows else 8

    fig_height = FIGSIZE_HARNESS[1] if len({str(row["model"]) for row in rows}) == 1 else FIGSIZE_OUTCOMES[1]
    fig, ax = plt.subplots(figsize=(FIGSIZE_HARNESS[0], fig_height), dpi=FIG_DPI)
    fig.patch.set_facecolor("#FFFFFF")
    ax.set_facecolor("#FFFFFF")

    y_positions: dict[tuple[str, str], float] = {}
    y = 2.75 if fig_height < 3.0 else 5.0
    top_y = y
    for model in model_order:
        for harness in harness_order:
            if (model, harness) in by_key:
                y_positions[(model, harness)] = y
                y -= 0.72
        y -= 0.58

    for model in model_order:
        rows_for_model = [by_key[(model, harness)] for harness in harness_order if (model, harness) in by_key]
        if not rows_for_model:
            continue
        first_y = y_positions[(model, harness_order[0])]
        task_count = int(rows_for_model[0].get("task_count", rows_for_model[0]["attempted"]))
        ax.text(
            -2.25,
            first_y + 0.48,
            f"{model}  |  common {task_count}-task subset",
            va="center",
            ha="left",
            fontsize=9.0,
            color=TEXT_DARK,
            fontweight="bold",
        )
        for harness in harness_order:
            row = by_key.get((model, harness))
            if row is None:
                continue
            row_y = y_positions[(model, harness)]
            color = str(row["color"])
            correct = int(row["correct"])
            wrong = int(row["wrong"])
            timeout = int(row["timeout"])
            attempted = int(row["attempted"])
            acc = float(row["accuracy"])

            ax.text(-1.95, row_y, harness, va="center", ha="left", fontsize=9.0, color=TEXT_MID)
            ax.barh(row_y, correct, height=0.42, color=color, edgecolor="white", linewidth=0.8)
            ax.barh(
                row_y,
                wrong,
                left=correct,
                height=0.42,
                color=tint(color, 0.55),
                edgecolor="white",
                linewidth=0.8,
            )
            ax.barh(
                row_y,
                timeout,
                left=correct + wrong,
                height=0.42,
                color=TIMEOUT_FILL,
                edgecolor="white",
                linewidth=0.8,
                hatch="////",
            )
            if correct > 0:
                ax.text(
                    max(0.18, correct * 0.50),
                    row_y,
                    f"{correct}",
                    va="center",
                    ha="center",
                    fontsize=9.0,
                    color="white" if correct >= 2 else TEXT_DARK,
                    fontweight="bold",
                )
            token_text = f"{float(row['avg_tokens_m']):.1f}M" if int(row["token_runs"]) else "n/a"
            ax.text(
                max_total + 0.38,
                row_y,
                f"{correct}/{attempted} ({acc * 100:.0f}%)  {float(row['avg_minutes']):.1f}m  {token_text}",
                va="center",
                ha="left",
                fontsize=9.0,
                color=TEXT_DARK,
            )

    legend_y = top_y + 0.76
    legend_items = [
        ("Correct", TEXT_DARK, None),
        ("Wrong", "#9CA3AF", None),
        ("Timeout", TIMEOUT_FILL, "////"),
    ]
    for i, (label, color, hatch) in enumerate(legend_items):
        x = 1.0 + i * 1.45
        ax.barh(legend_y, 0.56, left=x, height=0.16, color=color, hatch=hatch, edgecolor="#9CA3AF", clip_on=False)
        ax.text(x + 0.65, legend_y, label, va="center", ha="left", fontsize=9.0, color=TEXT_MID)
    ax.text(
        max_total + 0.38,
        legend_y,
        "C/All   avg min   avg tokens",
        va="center",
        ha="left",
        fontsize=9.0,
        color=TEXT_MUTED,
    )

    ax.set_xlim(-2.35, max_total + 5.1)
    ax.set_ylim(max(0.12, y + 0.34), legend_y + 0.34)
    ax.set_yticks([])
    ax.set_xlabel("attempted runs in the model-specific common subset", fontsize=9.0, color=TEXT_MID, labelpad=7)
    ax.set_xticks(list(range(0, max_total + 1, 2)))
    ax.tick_params(axis="x", labelsize=9.0, colors=TEXT_MUTED, length=0)
    ax.xaxis.grid(True, color=GRID, linewidth=0.7)
    ax.set_axisbelow(True)
    for spine in ax.spines.values():
        spine.set_visible(False)

    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"harness_outcomes_models.{ext}", bbox_inches="tight", pad_inches=0.035)
    plt.close(fig)


def draw_cost_profile(rows: list[dict[str, object]]) -> None:
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    rows = sorted(rows, key=lambda row: MODEL_ORDER.get(str(row["label"]), 999))
    max_minutes = max(float(row["avg_minutes"]) for row in rows) if rows else 90.0
    max_tokens = max(float(row["avg_tokens_m"]) for row in rows) if rows else 35.0
    max_minutes = max(60.0, np.ceil(max_minutes / 10.0) * 10.0)
    max_tokens = max(10.0, np.ceil(max_tokens / 5.0) * 5.0)

    fig, ax = plt.subplots(figsize=(7.2, 4.15), dpi=220)
    fig.patch.set_facecolor("#FFFFFF")
    ax.set_facecolor("#FFFFFF")

    y_positions = np.arange(len(rows))[::-1]
    minutes_left = 0.0
    tokens_left = 63.0
    col_width = 40.0
    bar_h = 0.28

    for y, row in zip(y_positions, rows):
        color = str(row["color"])
        minutes = float(row["avg_minutes"])
        tokens_m = float(row["avg_tokens_m"])
        token_runs = int(row["token_runs"])
        minutes_w = minutes / max_minutes * col_width if max_minutes else 0.0
        tokens_w = tokens_m / max_tokens * col_width if max_tokens else 0.0

        image = OffsetImage(load_icon(str(row["icon"]), color), zoom=0.088)
        ab = AnnotationBbox(image, (-74.0, y), frameon=False, box_alignment=(0.5, 0.5), zorder=6)
        ax.add_artist(ab)
        label_text = str(row["label"])
        label_y = y + 0.12
        stats_y = y - 0.20
        if label_text == "Claude Code DeepSeek-V4-Pro":
            label_text = "Claude Code\nDeepSeek-V4-Pro"
            label_y = y + 0.20
            stats_y = y - 0.30

        ax.text(
            -69.0,
            label_y,
            label_text,
            va="center",
            ha="left",
            fontsize=9.0,
            linespacing=0.88,
            color="#111827",
            fontweight="semibold",
        )
        ax.text(
            -69.0,
            stats_y,
            f"{int(row['correct'])}/{int(row['attempted'])} correct",
            va="center",
            ha="left",
            fontsize=9.0,
            color="#6B7280",
        )

        ax.barh(y + 0.16, minutes_w, left=minutes_left, height=bar_h, color=color, edgecolor="white", linewidth=0.9)
        ax.text(
            minutes_left + minutes_w + 1.0,
            y + 0.16,
            f"{minutes:.1f}",
            va="center",
            ha="left",
            fontsize=9.0,
            color="#111827",
        )
        ax.barh(
            y - 0.16,
            tokens_w,
            left=tokens_left,
            height=bar_h,
            color=tint(color, 0.35),
            edgecolor="white",
            linewidth=0.9,
        )
        token_label = f"{tokens_m:.1f}" if token_runs else "n/a"
        ax.text(
            tokens_left + tokens_w + 1.0,
            y - 0.16,
            token_label,
            va="center",
            ha="left",
            fontsize=9.0,
            color="#111827",
        )

    for x in [minutes_left, minutes_left + col_width, tokens_left, tokens_left + col_width]:
        ax.axvline(x, color="#E5E7EB", linewidth=0.7, zorder=0)

    ax.text(
        -77.0,
        len(rows) - 0.04,
        "Current cost snapshot",
        va="center",
        ha="left",
        fontsize=9.0,
        color="#111827",
        fontweight="bold",
    )
    ax.text(minutes_left, len(rows) - 0.45, "avg minutes", fontsize=9.0, color="#374151", fontweight="semibold")
    ax.text(tokens_left, len(rows) - 0.45, "avg total tokens (M)", fontsize=9.0, color="#374151", fontweight="semibold")
    ax.text(minutes_left + col_width, -0.72, f"{max_minutes:.0f}", fontsize=9.0, color="#6B7280", ha="center")
    ax.text(tokens_left + col_width, -0.72, f"{max_tokens:.0f}", fontsize=9.0, color="#6B7280", ha="center")
    ax.text(minutes_left, -0.72, "0", fontsize=9.0, color="#6B7280", ha="center")
    ax.text(tokens_left, -0.72, "0", fontsize=9.0, color="#6B7280", ha="center")

    ax.set_xlim(-78, tokens_left + col_width + 15)
    ax.set_ylim(-0.7, len(rows) - 0.3)
    ax.set_xticks([])
    ax.set_yticks([])
    for spine in ax.spines.values():
        spine.set_visible(False)

    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"primary_cost_models.{ext}", bbox_inches="tight", pad_inches=0.03)
    plt.close(fig)


def load_primary_rows() -> list[dict[str, object]]:
    """Reconstruct primary-task rows from the committed CSV.

    Restyling reads the frozen snapshot rather than re-summarizing the live
    results tree, so the numbers reported in the paper can never drift while we
    only change appearance. Colors and icons come from ``SERIES``.
    """
    path = FIGURES_DIR / "primary_outcomes_models.csv"
    lookup = {series.label: series for series in SERIES}
    rows: list[dict[str, object]] = []
    with path.open(encoding="utf-8", newline="") as handle:
        for record in csv.DictReader(handle):
            series = lookup.get(record["label"])
            rows.append(
                {
                    "label": record["label"],
                    "short_label": series.short_label if series else record["label"],
                    "color": series.color if series else STEEL_700,
                    "icon": series.icon if series else "",
                    "attempted": int(record["attempted"]),
                    "correct": int(record["correct"]),
                    "wrong": int(record["wrong"]),
                    "timeout": int(record["timeout"]),
                    "accuracy": float(record["accuracy"]),
                    "avg_minutes": float(record["avg_minutes"]),
                    "avg_tokens_m": float(record["avg_tokens_m"]),
                    "avg_input_tokens_m": float(record["avg_input_tokens_m"]),
                    "avg_output_tokens_k": float(record["avg_output_tokens_k"]),
                    "avg_tool_calls": float(record["avg_tool_calls"]),
                    "token_runs": int(record["token_runs"]),
                    "input_token_runs": int(record["input_token_runs"]),
                    "output_token_runs": int(record["output_token_runs"]),
                    "tool_call_runs": int(record["tool_call_runs"]),
                }
            )
    return rows


def load_harness_rows() -> list[dict[str, object]]:
    """Reconstruct harness-comparison rows from the committed CSV (colors from
    ``GLM52_HARNESS_SERIES``)."""
    path = FIGURES_DIR / "harness_outcomes_models.csv"
    color_by_harness = {series.harness: series.color for series in GLM52_HARNESS_SERIES}
    rows: list[dict[str, object]] = []
    with path.open(encoding="utf-8", newline="") as handle:
        for record in csv.DictReader(handle):
            rows.append(
                {
                    "model": record["model"],
                    "harness": record["harness"],
                    "color": color_by_harness.get(record["harness"], STEEL_700),
                    "attempted": int(record["attempted"]),
                    "correct": int(record["correct"]),
                    "errors": int(record["errors"]),
                    "avg_minutes": float(record["avg_minutes"]),
                    "avg_input_tokens": float(record["avg_input_tokens"]),
                    "avg_output_tokens": float(record["avg_output_tokens"]),
                    "avg_tool_calls": float(record["avg_tool_calls"]),
                    "avg_generated_code_lines": float(record["avg_generated_code_lines"]),
                }
            )
    return rows


def main() -> None:
    """Restyle every figure from the frozen CSV snapshot.

    Deterministic and offline-friendly: no live re-summarize, no CSV overwrite,
    so the reported numbers are preserved exactly. Run ``build_from_live()`` to
    refresh the underlying data from the results tree.
    """
    draw_task_design()
    rows = load_primary_rows()
    draw_primary_outcomes_table(rows)
    draw_primary_cost_table(rows)
    draw_primary_results_summary(rows)
    # Fig. 4 is owned by make_paper_figures.py, whose frozen snapshot retains
    # the directly observed coupled annotation--proof timing blocks.

    harness_rows = load_harness_rows()
    draw_harness_radar(harness_rows)


def build_from_live() -> None:
    """Refresh the CSV snapshot and figures from the live results tree."""
    rows = [summarize(series) for series in SERIES]
    write_csv(rows)
    draw_task_design()
    draw_primary_outcomes_table(rows)
    draw_primary_cost_table(rows)
    # Fig. 4 is owned by make_paper_figures.py; do not overwrite its strict
    # timing decomposition with the legacy additive approximation here.

    harness_rows = [summarize_glm52_harness(series) for series in GLM52_HARNESS_SERIES]
    write_harness_radar_csv(harness_rows)
    draw_harness_radar(harness_rows)


if __name__ == "__main__":
    import sys

    if "--from-live" in sys.argv:
        build_from_live()
    else:
        main()
