#!/usr/bin/env python3
"""Build the figures currently used by the main paper.

Outputs:
  figures/effort_scaling.{pdf,png}
  figures/branch_difficulty.{pdf,png}
  figures/task_design_agentic.{pdf,png}
"""

from __future__ import annotations

import csv
import json
import re
from pathlib import Path

import matplotlib.pyplot as plt
import matplotlib.patches as patches
import numpy as np

from make_experiment_figures import (  # noqa: E402
    FIGURES_DIR,
    FIG_DPI,
    GOLD,
    GRID,
    HARNESS_STYLES,
    MODEL_STYLES,
    OUTCOME_CORRECT,
    OUTCOME_TIMEOUT,
    OUTCOME_WRONG,
    SLATE,
    STEEL_100,
    STEEL_300,
    STEEL_500,
    STEEL_700,
    STEEL_900,
    TASK_ANNOTATION,
    TASK_CONTRACT,
    TASK_PROOF,
    TEAL,
    TEXT_DARK,
    TEXT_MID,
    TEXT_MUTED,
    draw_harness_metric_table,
    draw_task_design,
)

PROJECT_ROOT = Path(__file__).resolve().parents[1]
TABLES_DIR = PROJECT_ROOT / "tables"
SNAPSHOT = json.loads((FIGURES_DIR / "stats_snapshot.json").read_text(encoding="utf-8"))
MAIN_140 = json.loads(
    (FIGURES_DIR / "main_table_140_audit.json").read_text(encoding="utf-8")
)
BRANCH_140_PATH = FIGURES_DIR / "branch_140_audit.json"
BRANCH_140 = (
    json.loads(BRANCH_140_PATH.read_text(encoding="utf-8"))
    if BRANCH_140_PATH.exists()
    else {}
)

CORE_N = SNAPSHOT["core_task_count"]
EXT_N = SNAPSHOT["extension_task_count"]
BENCHMARK_N = 140
SOURCE_N = 164
MAIN_140_ROWS = {
    (str(row["group"]), str(row["model"]), str(row["effort"])): row
    for row in MAIN_140["rows"]
}

# Figure palette aligned with the restrained blue/gray visual language used by
# SL-VC: blue carries the comparison signal; gray supplies context and chrome.
FIG_BLUE_DARK = "#2F6F8A"
FIG_BLUE = "#5B9BB5"
FIG_BLUE_MID = "#82B6CA"
FIG_BLUE_LIGHT = "#BDE3F1"
FIG_GRAY_DARK = "#4A545A"
FIG_GRAY = "#8C979D"
FIG_GRAY_LIGHT = "#E3E8EB"
FIG_BG = "#FAFBFC"
FIG_GRID = "#DCE2E5"

# Display order for the results tables: strongest harness family first, then
# effort within family from most to least reasoning.
CONFIG_ORDER = [
    ("Codex", "GPT-5.5", "xhigh"),
    ("Codex", "GPT-5.5", "medium"),
    ("Codex", "GPT-5.4", "xhigh"),
    ("Codex", "GPT-5.4", "high"),
    ("Codex", "GPT-5.4", "medium"),
    ("Codex", "GPT-5.4", "low"),
    ("Codex", "GPT-5.4-mini", "medium"),
    ("Claude Code", "GLM-5.2", "default"),
    ("Claude Code", "DeepSeek-V4-Pro", "default"),
    ("Kimi Code", "Kimi for Coding", "thinking"),
]


def cfg(split: str, harness: str, model: str, effort: str) -> dict | None:
    return SNAPSHOT[split].get(f"{harness}|{model}|{effort}")


def display_effort(harness: str, model: str, effort: str) -> str:
    """Paper-facing effort label; snapshot keys retain their original names."""
    if harness == "Claude Code" and model in {"GLM-5.2", "DeepSeek-V4-Pro"}:
        return "thinking"
    return "--" if effort == "default" else effort


def display_model(model: str) -> str:
    """Paper-facing model name; snapshot keys retain their original names."""
    return {"Kimi for Coding": "kimi-2.7-code"}.get(model, model)


def _weighted(core: dict | None, ext: dict | None, value_key: str, weight_key: str) -> float:
    total = 0.0
    weight = 0.0
    for part in (core, ext):
        if part and part.get(weight_key):
            total += part[value_key] * part[weight_key]
            weight += part[weight_key]
    return total / weight if weight else 0.0


def _weighted_profile(
    core: dict | None,
    ext: dict | None,
    value_key: str,
    weight_key: str,
    profile_key: str,
) -> float:
    total = 0.0
    weight = 0.0
    for part in (core, ext):
        if part and part.get(weight_key):
            total += part.get(value_key, {}).get(profile_key, 0.0) * part[weight_key]
            weight += part[weight_key]
    return total / weight if weight else 0.0


def combined(harness: str, model: str, effort: str) -> dict | None:
    """Return the audited three-branch row for one model configuration."""
    lookup_model = "kimi-2.7-code" if model == "Kimi for Coding" else model
    lookup_effort = (
        "thinking"
        if harness == "Claude Code" and effort == "default"
        else effort
    )
    row_140 = MAIN_140_ROWS.get((harness, lookup_model, lookup_effort))
    if row_140 is not None:
        audited = dict(row_140)
        audited["benchmark_task_count"] = BENCHMARK_N
        audited["task_universe"] = BENCHMARK_N
        audited["accuracy"] = audited["correct"] / BENCHMARK_N
        audited["avg_minutes"] = audited["avg_minutes_solved"]
        audited["avg_input_tokens_m"] = audited["avg_input_tokens_m_solved"]
        audited["avg_output_tokens_k"] = audited["avg_output_tokens_k_solved"]
        audited["avg_tool_calls"] = audited["avg_tool_calls_solved"]
        audited["avg_tool_profile"] = audited["avg_tool_profile_solved"]
        return audited

    key = f"{harness}|{model}|{effort}"
    audited = SNAPSHOT.get("primary_combined", {}).get(key)
    if audited is not None:
        audited = dict(audited)
        audited["benchmark_task_count"] = BENCHMARK_N
        audited["task_universe"] = audited["attempted"]
        audited["accuracy"] = audited["correct"] / audited["attempted"]
        audited["avg_minutes"] = audited["avg_minutes_solved"]
        audited["avg_input_tokens_m"] = audited["avg_input_tokens_m_solved"]
        audited["avg_output_tokens_k"] = audited["avg_output_tokens_k_solved"]
        audited["avg_tool_calls"] = audited["avg_tool_calls_solved"]
        audited["avg_tool_profile"] = audited["avg_tool_profile_solved"]
        return audited
    core = cfg("primary_core", harness, model, effort)
    ext = cfg("primary_extension", harness, model, effort)
    if core is None and ext is None:
        return None
    parts = [p for p in (core, ext) if p]
    attempted = sum(p["attempted"] for p in parts)
    correct = sum(p["correct"] for p in parts)
    return {
        "harness": harness,
        "model": model,
        "effort": effort,
        "attempted": attempted,
        "benchmark_task_count": BENCHMARK_N,
        "task_universe": attempted,
        "correct": correct,
        "wrong": sum(p["wrong"] for p in parts),
        "timeout": sum(p["timeout"] for p in parts),
        "accuracy": correct / attempted,
        # cost averages are SOLVED-ONLY (失败的不统计): failed runs thrash on
        # verifier retries and would otherwise dominate the token/time means
        "avg_minutes": _weighted(core, ext, "avg_minutes_solved", "solved_time_runs"),
        "avg_input_tokens_m": _weighted(core, ext, "avg_input_tokens_m_solved", "solved_token_runs"),
        "avg_output_tokens_k": _weighted(core, ext, "avg_output_tokens_k_solved", "solved_token_runs"),
        "avg_tool_calls": _weighted(core, ext, "avg_tool_calls_solved", "solved_trace_runs"),
        "avg_tool_profile": {
            key: _weighted_profile(
                core, ext, "avg_tool_profile_solved", "solved_trace_runs", key
            )
            for key in ("total", "read", "write", "coqc", "vcg", "rounds")
        },
    }


# ---------------------------------------------------------------------------
# Generated LaTeX tables
# ---------------------------------------------------------------------------

def latex_main_results() -> str:
    rows = [
        (harness, model, effort, combined(harness, model, effort))
        for harness, model, effort in CONFIG_ORDER
    ]
    rows = [r for r in rows if r[3] is not None]
    best_acc = max(r[3]["accuracy"] for r in rows)
    lines: list[str] = []
    prev_harness = None
    for harness, model, effort, row in rows:
        if prev_harness is not None and harness != prev_harness:
            lines.append(r"\addlinespace[2.2pt]")
        if harness != prev_harness:
            lines.append(r"\textit{" + harness + r"} & & & & & & & & & \\")
        prev_harness = harness
        attempted = row["attempted"]
        effort_text = display_effort(harness, model, effort)
        acc = row["accuracy"] * 100
        acc_text = f"\\textbf{{{acc:.1f}}}" if row["accuracy"] == best_acc else f"{acc:.1f}"
        profile = row["avg_tool_profile"]
        lines.append(
            f"\\quad {display_model(model)} ({effort_text}) & "
            f"{row['correct']}/{attempted} & {row['wrong']}/{row['timeout']} & "
            f"{acc_text} & {row['avg_minutes']:.1f} & "
            f"{row['avg_input_tokens_m']:.1f}/{row['avg_output_tokens_k']:.0f} & "
            f"{profile['read']:.1f}/{profile['write']:.1f} & "
            f"{profile['total']:.1f} & "
            f"{profile['coqc']:.1f}/{profile['vcg']:.1f} & "
            f"{profile['rounds']:.1f} \\\\"
        )
    return "\n".join(lines) + "\n\\bottomrule\n"


def latex_tool_use_results() -> str:
    lines: list[str] = []
    prev_harness = None
    for harness, model, effort in CONFIG_ORDER:
        row = combined(harness, model, effort)
        if row is None or not row.get("avg_tool_profile"):
            continue
        if prev_harness is not None and harness != prev_harness:
            lines.append(r"\addlinespace[2.2pt]")
        if harness != prev_harness:
            lines.append(f"\\textit{{{harness}}} & & & & \\\\")
        prev_harness = harness
        profile = row["avg_tool_profile"]
        configuration = (
            f"{display_model(model)} "
            f"({display_effort(harness, model, effort)})"
        )
        lines.append(
            f"\\quad {configuration} & "
            f"{profile['read']:.1f}/{profile['write']:.1f} & "
            f"{profile['total']:.1f} & "
            f"{profile['coqc']:.1f}/{profile['vcg']:.1f} & "
            f"{profile['rounds']:.1f} \\\\"
        )
    return "\n".join(lines) + "\n\\bottomrule\n"


def latex_harness_results() -> str:
    lines: list[str] = []
    for model in ("GLM-5.2", "DeepSeek-V4-Pro"):
        lines.append(f"\\textit{{{model}}} & & & & & & \\\\ ")
        for harness in ("Codex CLI", "OpenCode", "Claude Code"):
            r = SNAPSHOT.get("harness_sensitivity", {}).get(f"{model}|{harness}")
            if not r:
                continue
            lines.append(
                f"\\quad {harness} & {r['correct']}/{r['attempted']} & "
                f"{r['avg_minutes_solved']:.1f} & {r['avg_input_tokens_m_solved']:.1f} & "
                f"{r['avg_output_tokens_k_solved']:.0f} & {r['avg_tool_calls_solved']:.0f} & "
                f"{r['avg_generated_code_lines_solved']:.0f} \\\\"
            )
    return "\n".join(lines) + "\n\\bottomrule\n"


def latex_harness_taskwise() -> str:
    task_labels = {
        "p052_below_threshold": "p052 below threshold",
        "p082_prime_length": "p082 prime length",
        "p138_is_equal_to_sum_even": "p138 sum of two evens",
        "p139_special_factorial": "p139 special factorial",
    }
    harnesses = ("Codex CLI", "OpenCode", "Claude Code")
    outcome_label = {"correct": "C", "wrong": "W", "timeout": "T"}
    tasks = SNAPSHOT["harness_sensitivity_design"]["cohort_tasks"]
    lines: list[str] = []
    for model in ("GLM-5.2", "DeepSeek-V4-Pro"):
        summaries = {
            harness: SNAPSHOT["harness_sensitivity"][f"{model}|{harness}"]
            for harness in harnesses
        }
        lines.append(f"\\multicolumn{{4}}{{l}}{{\\textit{{{model}}}}} \\\\ ")
        for index, task in enumerate(tasks):
            prefix = "\\rowcolor{papergraytwo} " if index % 2 == 0 else ""
            outcomes = [
                outcome_label.get(summaries[h]["per_task"].get(task, ""), "--")
                for h in harnesses
            ]
            lines.append(
                f"{prefix}{task_labels.get(task, task)} & "
                + " & ".join(outcomes)
                + " \\\\"
            )
        lines.append(r"\cmidrule(lr){2-4}")
        lines.append(
            r"\textbf{Accepted} & "
            + " & ".join(
                f"\\textbf{{{summaries[h]['correct']}/{len(tasks)}}}"
                for h in harnesses
            )
            + r" \\"
        )
        if model == "GLM-5.2":
            lines.append(r"\midrule")
    return "\n".join(lines) + "\n\\bottomrule\n"


def latex_extension_results() -> str:
    lines: list[str] = []
    prev_harness = None
    for harness, model, effort in CONFIG_ORDER:
        core = cfg("primary_core", harness, model, effort)
        ext = cfg("primary_extension", harness, model, effort)
        if core is None or ext is None:
            continue
        if prev_harness is not None and harness != prev_harness:
            lines.append(r"\addlinespace[2.2pt]")
        prev_harness = harness
        effort_text = display_effort(harness, model, effort)
        core_partial = r"$^{\dagger}$" if core["attempted"] < CORE_N else ""
        ext_partial = r"$^{\dagger}$" if ext["attempted"] < EXT_N else ""
        delta = ext["accuracy"] * 100 - core["accuracy"] * 100
        lines.append(
            f"{display_model(model)} & {effort_text} & "
            f"{core['correct']}/{core['attempted']}{core_partial} & {core['accuracy']*100:.1f} & "
            f"{ext['correct']}/{ext['attempted']}{ext_partial} & {ext['accuracy']*100:.1f} & "
            f"{delta:+.1f} \\\\"
        )
    return "\n".join(lines) + "\n\\bottomrule\n"


# ---------------------------------------------------------------------------
# Accepted-run tool activity
# ---------------------------------------------------------------------------

def draw_tool_activity() -> None:
    """Small-multiple dot plot replacing the dense tool-use table."""
    rows: list[tuple[str, dict[str, float]]] = []
    for harness, model, effort in CONFIG_ORDER:
        row = combined(harness, model, effort)
        if row is None or not row.get("avg_tool_profile"):
            continue
        effort_text = display_effort(harness, model, effort)
        model_text = display_model(model)
        harness_text = {
            "Claude Code": "Claude Code",
            "Kimi Code": "Kimi Code",
        }.get(harness, harness)
        label = f"{model_text} {effort_text} / {harness_text}"
        rows.append((label, row["avg_tool_profile"]))

    fig, axes = plt.subplots(
        1,
        3,
        figsize=(7.15, 3.18),
        sharey=True,
        gridspec_kw={"width_ratios": [1.5, 1.0, 0.78], "wspace": 0.10},
    )
    fig.patch.set_facecolor("white")
    y = np.arange(len(rows))

    panels = [
        (
            "(a) Repository operations",
            (("total", "All tools", FIG_BLUE_DARK, "o"),
             ("read", "Reads", FIG_BLUE, "s"),
             ("write", "Writes", FIG_BLUE_MID, "D")),
            (0, 205),
            [0, 50, 100, 150, 200],
        ),
        (
            "(b) Formal checks",
            (("coqc", "Rocq", FIG_BLUE_DARK, "o"),
             ("vcg", "VCG", FIG_BLUE_MID, "s")),
            (0, 62),
            [0, 20, 40, 60],
        ),
        (
            "(c) Interaction",
            (("rounds", "Rounds", FIG_BLUE_DARK, "o"),),
            (0, 162),
            [0, 50, 100, 150],
        ),
    ]

    for panel_i, (ax, (title, series, xlim, xticks)) in enumerate(zip(axes, panels)):
        ax.set_facecolor("white")
        for key, legend_label, color, marker in series:
            values = [float(profile[key]) for _label, profile in rows]
            ax.scatter(
                values,
                y,
                s=20,
                marker=marker,
                facecolor=color,
                edgecolor="white",
                linewidth=0.45,
                label=legend_label,
                zorder=3,
            )
        ax.set_title(title, loc="left", fontsize=7.1, color=FIG_GRAY_DARK,
                     fontweight="semibold", pad=15)
        ax.set_xlim(*xlim)
        ax.set_xticks(xticks)
        ax.tick_params(axis="x", labelsize=5.8, colors=FIG_GRAY, length=0, pad=2)
        ax.tick_params(axis="y", length=0, pad=4)
        ax.grid(axis="x", color=FIG_GRID, linewidth=0.5)
        ax.set_axisbelow(True)
        ax.set_xlabel("mean count per accepted run", fontsize=6.0,
                      color=FIG_GRAY_DARK, labelpad=4)
        for boundary in (6.5, 8.5):
            ax.axhline(boundary, color=FIG_GRAY_LIGHT, linewidth=0.75, zorder=1)
        for spine in ax.spines.values():
            spine.set_visible(False)
        ax.legend(
            loc="lower left",
            bbox_to_anchor=(0.0, 1.005),
            frameon=False,
            ncol=len(series),
            fontsize=5.65,
            handletextpad=0.25,
            columnspacing=0.65,
            borderaxespad=0,
        )
        if panel_i == 0:
            ax.set_yticks(y)
            ax.set_yticklabels([label for label, _profile in rows],
                               fontsize=5.85, color=FIG_GRAY_DARK)

    axes[0].invert_yaxis()
    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"tool_activity.{ext}",
                    bbox_inches="tight", pad_inches=0.025, dpi=FIG_DPI)
    plt.close(fig)


# ---------------------------------------------------------------------------
# Effort-scaling / cost--accuracy frontier
# ---------------------------------------------------------------------------

def _configuration_label(harness: str, model: str) -> str:
    """Compact text label; color always denotes the model."""
    if harness == "Kimi Code" and model == "Kimi for Coding":
        return display_model(model)
    return f"{display_model(model)} ({harness})"

def _draw_frontier(
    x_key: str,
    xlabel: str,
    xlim: tuple[float, float],
    xticks: list[float],
    filename: str,
    family_meta: list[tuple[str, str, tuple[int, int], list[tuple[str, tuple[int, int]]]]],
    context_meta: list[tuple[str, str, str, tuple[int, int]]],
    panel_title: str = "",
) -> None:
    """One cost--accuracy frontier panel; the x metric and every label offset
    are supplied by the caller so the time and token panels tune separately."""
    fig, ax = plt.subplots(figsize=(3.35, 2.28), dpi=FIG_DPI)
    fig.patch.set_facecolor("#FFFFFF")
    ax.set_facecolor("#FFFFFF")

    # Model identity is stable across both frontier panels.  Where a model has
    # an established brand blue (DeepSeek/Kimi), use it directly; OpenAI model
    # generations and GLM retain the paper's existing distinct identities.
    frontier_colors = {
        model: MODEL_STYLES[model]["color"]
        for model in (
            "GPT-5.5", "GPT-5.4", "GPT-5.4-mini", "GLM-5.2",
            "DeepSeek-V4-Pro", "Kimi for Coding",
        )
    }
    # Keep marker geometry constant across models; identity is encoded only by
    # the stable per-model color.
    context_markers = {
        model: "o"
        for model in ("GLM-5.2", "DeepSeek-V4-Pro", "Kimi for Coding", "GPT-5.4-mini")
    }
    context_labels = {
        "GLM-5.2": "GLM-5.2",
        "DeepSeek-V4-Pro": "DeepSeek-V4-Pro",
        "Kimi for Coding": "kimi-2.7-code",
        "GPT-5.4-mini": "GPT-5.4-mini",
    }

    families = [
        (harness, model, frontier_colors[model], family_offset, [
            (effort, offset, combined(harness, model, effort))
            for effort, offset in efforts
        ])
        for harness, model, family_offset, efforts in family_meta
    ]
    context_points = [
        (harness, model, frontier_colors[model], combined(harness, model, effort), offset)
        for harness, model, effort, offset in context_meta
    ]

    for harness, model, color, family_offset, points in families:
        xs = [p[x_key] for _e, _o, p in points if p]
        ys = [p["accuracy"] * 100 for _e, _o, p in points if p]
        ax.plot(xs, ys, color=color, lw=1.65, marker="o", ms=4.7,
                mfc="#FFFFFF", mec=color, mew=1.25, zorder=4,
                clip_on=False)
        if xs:
            # Direct labeling removes the need to match a detached legend to
            # the two frontiers.  Anchor at the line centroid and tune only a
            # small panel-specific offset.
            ax.annotate(
                f"{model} (Codex)",
                (float(np.mean(xs)), float(np.mean(ys))),
                textcoords="offset points", xytext=family_offset,
                ha="right" if family_offset[0] < 0 else "left",
                va="center", fontsize=5.8, color=color,
                fontweight="semibold", zorder=7,
            )
        for effort, (dx, dy), p in points:
            if not p:
                continue
            x, y = p[x_key], p["accuracy"] * 100
            label = effort
            ax.annotate(
                label, (x, y), textcoords="offset points", xytext=(dx, dy),
                fontsize=5.75, color=FIG_GRAY_DARK, zorder=6,
            )

    for harness, model, color, p, (dx, dy) in context_points:
        if not p:
            continue
        x, y = p[x_key], p["accuracy"] * 100
        ax.scatter([x], [y], s=24, marker=context_markers[model],
                   facecolor="white", edgecolor=color, linewidth=1.15, zorder=5)
        label = context_labels[model]
        ax.annotate(
            label,
            (x, y),
            textcoords="offset points",
            xytext=(dx, dy),
            ha="right" if dx < 0 else "left",
            va="center",
            fontsize=5.75,
            color=color,
            fontweight="semibold",
            zorder=6,
        )

    if panel_title:
        ax.set_title(panel_title, fontsize=7.3, color=FIG_GRAY_DARK,
                     fontweight="semibold", loc="left", pad=5)
    ax.set_xlabel(xlabel, fontsize=6.8, color=FIG_GRAY_DARK, labelpad=3)
    ax.set_ylabel("accepted among evaluated tasks (%)", fontsize=6.8,
                  color=FIG_GRAY_DARK, labelpad=4)
    ax.set_xlim(*xlim)
    ax.set_ylim(0, 64)
    ax.set_xticks(xticks)
    ax.set_yticks([0, 15, 30, 45, 60])
    ax.tick_params(labelsize=6.25, colors=FIG_GRAY, length=0)
    ax.grid(True, color=FIG_GRID, linewidth=0.52)
    ax.set_axisbelow(True)
    for spine in ax.spines.values():
        spine.set_visible(False)
    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"{filename}.{ext}", bbox_inches="tight", pad_inches=0.02)
    plt.close(fig)


def draw_effort_scaling() -> None:
    """(a) accuracy vs wall-clock minutes."""
    _draw_frontier(
        x_key="avg_minutes",
        xlabel="minutes per verified task",
        xlim=(15, 78),
        xticks=[20, 40, 60],
        filename="effort_scaling",
        panel_title="(a) Yield vs wall-clock time",
        family_meta=[
            ("Codex", "GPT-5.5", (-5, 9), [
                ("medium", (-30, 8)),
                ("xhigh", (5, -3)),
            ]),
            ("Codex", "GPT-5.4", (-5, 18), [
                ("low", (-6, 7)),
                ("medium", (3, -10)),
                ("high", (5, -4)),
                ("xhigh", (5, 7)),
            ]),
        ],
        context_meta=[
            ("Claude Code", "GLM-5.2", "default", (-4, -10)),
            ("Kimi Code", "Kimi for Coding", "thinking", (-4, 7)),
            ("Claude Code", "DeepSeek-V4-Pro", "default", (4, -4)),
            ("Codex", "GPT-5.4-mini", "medium", (4, 7)),
        ],
    )


def draw_effort_scaling_tokens() -> None:
    """(b) accuracy vs input tokens: the same frontier over token cost.  The
    GPT-5.5 sweep is nearly vertical (accuracy without extra context reads);
    GPT-5.4 pays ~2.2x the input tokens of low effort to reach xhigh."""
    _draw_frontier(
        x_key="avg_input_tokens_m",
        xlabel="CLI input tokens per verified task (millions)",
        xlim=(6, 34),
        xticks=[10, 20, 30],
        filename="effort_scaling_tokens",
        panel_title="(b) Yield vs input tokens",
        family_meta=[
            ("Codex", "GPT-5.5", (10, 0), [
                ("medium", (6, -6)),
                ("xhigh", (7, -3)),
            ]),
            ("Codex", "GPT-5.4", (-5, 10), [
                ("low", (-4, -12)),
                ("medium", (3, -10)),
                ("high", (5, -8)),
                ("xhigh", (5, -2)),
            ]),
        ],
        context_meta=[
            ("Claude Code", "GLM-5.2", "default", (4, 5)),
            ("Kimi Code", "Kimi for Coding", "thinking", (-4, 7)),
            ("Claude Code", "DeepSeek-V4-Pro", "default", (-4, 5)),
            ("Codex", "GPT-5.4-mini", "medium", (-4, -10)),
        ],
    )


# ---------------------------------------------------------------------------
# Agent--expert construction work loop (replaces the raster illustration)
# ---------------------------------------------------------------------------

def _round_box(ax, x, y, w, h, fill, edge, text, text_color, fontsize=6.6, lw=0.8):
    ax.add_patch(patches.FancyBboxPatch(
        (x, y), w, h, boxstyle="round,pad=0.012,rounding_size=0.025",
        facecolor=fill, edgecolor=edge, linewidth=lw, zorder=3, clip_on=False))
    ax.text(x + w / 2, y + h / 2, text, ha="center", va="center",
            fontsize=fontsize, color=text_color, zorder=4, linespacing=1.25, clip_on=False)


def draw_work_loop() -> None:
    """Vertical construction loop: expert (top) <-> agent, agent <-> the two
    parallel checkers (QCP VCG | coqc), checkers -> accepted artifact."""
    # taller-than-wide so the diagram, set at 0.28\textwidth in Figure 2,
    # matches the height of the right-hand artifact stack
    fig, ax = plt.subplots(figsize=(2.0, 2.31), dpi=FIG_DPI)
    fig.patch.set_facecolor("#FFFFFF")
    ax.set_xlim(-0.02, 1.02)
    ax.set_ylim(-0.02, 1.097)
    ax.axis("off")

    # Boxes, top to bottom.
    _round_box(ax, 0.03, 0.95, 0.94, 0.14, "#F7F9FB", "#CBD5E1",
               "Human expert  (guide & review)", TEXT_MID, fontsize=7.2)
    _round_box(ax, 0.03, 0.59, 0.94, 0.22, STEEL_100, STEEL_700,
               "Code agent\nedit contract / annotation / proof", STEEL_900, fontsize=7.2)
    _round_box(ax, 0.03, 0.22, 0.44, 0.19, "#EFF4F1", TEAL,
               "VCG\nsymexec", "#2C6360", fontsize=7.2)
    _round_box(ax, 0.53, 0.22, 0.44, 0.19, "#EFF4F1", TEAL,
               "coqc\nproof check", "#2C6360", fontsize=7.2)
    _round_box(ax, 0.03, 0.0, 0.94, 0.13, "#FBF4E7", GOLD,
               "Accepted verification artifact", "#8A5A1E", fontsize=7.2)

    # Expert <-> agent: dashed guidance on demand.
    ax.annotate("", xy=(0.42, 0.95), xytext=(0.42, 0.81),
                arrowprops=dict(arrowstyle="<|-|>", mutation_scale=7, lw=0.8,
                                color="#94A3B8", linestyle=(0, (2.5, 2)), shrinkA=1, shrinkB=1))
    ax.text(0.455, 0.878, "ask / guide", ha="left", va="center", fontsize=6.4, color=TEXT_MUTED)

    # Agent <-> each checker: run / feedback loops (one double arrow each).
    loop_arrow = dict(arrowstyle="<|-|>", mutation_scale=7, lw=0.9,
                      color=TEAL, shrinkA=1, shrinkB=1)
    ax.annotate("", xy=(0.25, 0.41), xytext=(0.25, 0.59), arrowprops=loop_arrow)
    ax.annotate("", xy=(0.75, 0.41), xytext=(0.75, 0.59), arrowprops=loop_arrow)
    ax.text(0.5, 0.50, "run / feedback", ha="center", va="center",
            fontsize=6.4, color="#2C6360")

    # Checkers -> artifact: accept.
    accept_arrow = dict(arrowstyle="-|>", mutation_scale=7, lw=0.9,
                        color=GOLD, shrinkA=1, shrinkB=1)
    ax.annotate("", xy=(0.25, 0.13), xytext=(0.25, 0.22), arrowprops=accept_arrow)
    ax.annotate("", xy=(0.75, 0.13), xytext=(0.75, 0.22), arrowprops=accept_arrow)
    ax.text(0.5, 0.172, "accept", ha="center", va="center", fontsize=6.4, color="#8A5A1E")

    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"work_loop.{ext}", bbox_inches="tight", pad_inches=0.02)
    plt.close(fig)


# ---------------------------------------------------------------------------
# Branch overview: directly observed stage-time shares + outcomes
# ---------------------------------------------------------------------------

def draw_branch_overview() -> None:
    """Trace-derived stage shares plus branch outcomes for the fixed system."""
    profile = SNAPSHOT["branch_time_profile_gpt54_medium"]
    interaction = SNAPSHOT["branch_interaction_gpt54_medium"]
    outcomes = SNAPSHOT["branch_outcomes_gpt54_medium"]
    task_colors = {
        "End-to-end": FIG_BLUE_DARK,
        "Primary": FIG_BLUE,
        "Proof-only": FIG_BLUE_MID,
    }

    time_rows = [
        ("End-to-end", profile["end_to_end"], "full chain"),
        ("Primary", profile["primary"], "contract given"),
        ("Proof-only", profile["proof_only"], "contract + annotations given"),
    ]

    fig, (ax, ix, bx) = plt.subplots(
        3, 1, figsize=(3.35, 4.72), dpi=FIG_DPI,
        gridspec_kw={"height_ratios": [1.05, 0.82, 0.86], "hspace": 0.58},
    )
    fig.patch.set_facecolor("#FFFFFF")

    # (a) Successful-run timing split at recorded VCG/coqc boundaries.
    ax.set_facecolor("#FFFFFF")
    y_positions = np.arange(len(time_rows))[::-1]
    ax.set_title("(a) Successful-run wall-clock composition",
                 fontsize=7.25, color=FIG_GRAY_DARK, fontweight="semibold",
                 loc="left", pad=4)
    ax.set_xlim(0, 41.5)
    ax.set_ylim(-0.58, len(time_rows) - 0.25)
    bar_h = 0.55
    for y, (label, row, supplied) in zip(y_positions, time_rows):
        left = 0.0
        total = float(row["total"])
        task_color = task_colors[label]
        stages = [
            ("Contract", "C", float(row.get("contract", 0.0))),
            ("Annotation", "A", float(row.get("annotation", 0.0))),
            ("Proof", "P", float(row.get("proof", 0.0))),
        ]
        for stage, short, minutes in stages:
            if not minutes:
                continue
            ax.barh(y, minutes, left=left, height=bar_h, color=task_color,
                    edgecolor="white", linewidth=0.65, zorder=3)
            share = 100.0 * minutes / total
            if minutes < 4.2:
                stage_label = f"{short}\n{minutes:.1f}\n{share:.0f}%"
                fontsize = 5.1
            elif stage == "Annotation" and minutes < 6.0:
                stage_label = f"Annot.\n{minutes:.1f} ({share:.0f}%)"
                fontsize = 5.5
            else:
                stage_label = f"{stage}\n{minutes:.1f} ({share:.0f}%)"
                fontsize = 5.7
            text_color = FIG_GRAY_DARK if label == "Proof-only" else "white"
            ax.text(left + minutes / 2, y, stage_label,
                    ha="center", va="center", fontsize=fontsize, color=text_color,
                    linespacing=0.90, zorder=5)
            left += minutes

        ax.text(total + 0.65, y + 0.10, f"{total:.1f} min",
                ha="left", va="center", fontsize=6.2, color=FIG_GRAY_DARK,
                fontweight="semibold")
        ax.text(total + 0.65, y - 0.14, f"n={row['runs']}",
                ha="left", va="center", fontsize=5.4, color=FIG_GRAY)
        ax.text(-0.02, y - 0.34, supplied, transform=ax.get_yaxis_transform(),
                ha="right", va="center", fontsize=5.15, color=FIG_GRAY)

    ax.set_yticks(y_positions)
    ax.set_yticklabels([label for label, _row, _supplied in time_rows], fontsize=6.5)
    for tick, (label, _row, _supplied) in zip(ax.get_yticklabels(), time_rows):
        tick.set_color(task_colors[label])
        tick.set_fontweight("semibold")
    ax.set_xticks([0, 10, 20, 30, 40])
    ax.set_xlabel("mean wall-clock minutes", fontsize=6.6, color=FIG_GRAY_DARK, labelpad=2)
    ax.tick_params(axis="x", labelsize=6.1, colors=FIG_GRAY, length=0)
    ax.tick_params(axis="y", colors=FIG_GRAY_DARK, length=0, pad=4)
    ax.grid(True, axis="x", color=FIG_GRID, linewidth=0.5)
    ax.set_axisbelow(True)
    for spine in ax.spines.values():
        spine.set_visible(False)

    # (b) Accepted-run tool calls and assistant interaction rounds.
    ix.set_facecolor("#FFFFFF")
    ix.set_title("(b) Accepted-run agentic interaction",
                 fontsize=7.25, color=FIG_GRAY_DARK, fontweight="semibold",
                 loc="left", pad=4)
    interaction_rows = [
        ("End-to-end", interaction["end_to_end"]),
        ("Primary", interaction["primary"]),
        ("Proof-only", interaction["proof_only"]),
    ]
    y_positions = np.arange(len(interaction_rows))[::-1]
    offset = 0.13
    for y, (label, row) in zip(y_positions, interaction_rows):
        color = task_colors[label]
        tools = float(row["profile"]["total"])
        rounds = float(row["profile"]["rounds"])
        ix.barh(y + offset, tools, height=0.20, color=color,
                edgecolor="none", zorder=3)
        ix.barh(y - offset, rounds, height=0.20, color=color, alpha=0.42,
                edgecolor="none", zorder=3)
        ix.text(tools + 3.0, y + offset, f"{tools:.1f}", ha="left", va="center",
                fontsize=5.8, color=FIG_GRAY_DARK)
        ix.text(rounds + 3.0, y - offset, f"{rounds:.1f}", ha="left", va="center",
                fontsize=5.8, color=FIG_GRAY_DARK)
        ix.text(205, y, f"n={row['runs']}", ha="right", va="center",
                fontsize=5.3, color=FIG_GRAY)
    contract_profile = interaction["end_to_end"].get("stage_profiles", {}).get("contract", {})
    if contract_profile:
        ix.text(
            0.995, -0.29,
            f"Contract stage: {contract_profile['total']:.1f} tools / "
            f"{contract_profile['rounds']:.1f} rounds",
            transform=ix.transAxes, ha="right", va="top",
            fontsize=5.25, color=FIG_GRAY,
        )
    ix.set_yticks(y_positions)
    ix.set_yticklabels([label for label, _row in interaction_rows], fontsize=6.5)
    for tick, (label, _row) in zip(ix.get_yticklabels(), interaction_rows):
        tick.set_color(task_colors[label])
        tick.set_fontweight("semibold")
    ix.set_ylim(-0.52, len(interaction_rows) - 0.25)
    ix.set_xlim(0, 210)
    ix.set_xticks([0, 50, 100, 150, 200])
    ix.set_xlabel("mean count", fontsize=6.6, color=FIG_GRAY_DARK, labelpad=2)
    ix.tick_params(labelsize=6.1, colors=FIG_GRAY, length=0)
    ix.tick_params(axis="y", colors=FIG_GRAY_DARK, length=0)
    ix.grid(True, axis="x", color=FIG_GRID, linewidth=0.5)
    ix.set_axisbelow(True)
    for spine in ix.spines.values():
        spine.set_visible(False)
    ix.legend(
        handles=[
            patches.Patch(facecolor=FIG_BLUE, edgecolor="none", label="Tool calls"),
            patches.Patch(facecolor=FIG_BLUE, alpha=0.42, edgecolor="none", label="Rounds"),
        ],
        loc="upper right", bbox_to_anchor=(1.0, 1.14),
        frameon=False, fontsize=5.3, ncol=2,
        handlelength=1.0, columnspacing=0.7, handletextpad=0.3,
    )

    # (c) Outcomes among the tasks evaluated for each branch.
    bx.set_facecolor("#FFFFFF")
    bx.set_title("(c) Outcomes among evaluated tasks",
                 fontsize=7.25, color=FIG_GRAY_DARK, fontweight="semibold",
                 loc="left", pad=4)
    outcome_rows = [
        ("End-to-end", outcomes["end_to_end"]),
        ("Primary", outcomes["primary"]),
        ("Proof-only", outcomes["proof_only"]),
    ]
    y_positions = np.arange(len(outcome_rows))[::-1]
    contract_error_color = "#B7C5CB"
    for y, (label, row) in zip(y_positions, outcome_rows):
        left = 0.0
        task_color = task_colors[label]
        segments = [
            (row["correct"], task_color),
            (row["downstream_fail"], "#D8E0E4"),
            (row["contract_error"], contract_error_color),
        ]
        for value, color in segments:
            if not value:
                continue
            bx.barh(y, value, left=left, height=0.49, color=color,
                    edgecolor="white", linewidth=0.55, zorder=3)
            text_color = "white" if color in {FIG_BLUE_DARK, FIG_BLUE, FIG_GRAY} else FIG_GRAY_DARK
            if value >= 8:
                bx.text(left + value / 2, y, str(value), ha="center", va="center",
                        fontsize=5.9, color=text_color, zorder=5)
            left += value
        bx.text(row["attempted"] + 2.2, y, f"{row['correct']}/{row['attempted']}",
                ha="left", va="center",
                fontsize=6.3, color=FIG_GRAY)
    bx.set_yticks(y_positions)
    bx.set_yticklabels([label for label, *_rest in outcome_rows], fontsize=6.5)
    for tick, (label, _row) in zip(bx.get_yticklabels(), outcome_rows):
        tick.set_color(task_colors[label])
        tick.set_fontweight("semibold")
    bx.set_ylim(-0.52, len(outcome_rows) - 0.23)
    bx.set_xlim(0, 145)
    bx.set_xticks([0, 40, 80, 120])
    bx.set_xlabel("evaluated tasks", fontsize=6.6, color=FIG_GRAY_DARK, labelpad=2)
    bx.tick_params(labelsize=6.1, colors=FIG_GRAY, length=0)
    bx.tick_params(axis="y", colors=FIG_GRAY_DARK, length=0)
    bx.grid(True, axis="x", color=FIG_GRID, linewidth=0.5)
    bx.set_axisbelow(True)
    for spine in bx.spines.values():
        spine.set_visible(False)

    legend_handles = [
        patches.Patch(facecolor=FIG_BLUE, edgecolor="none", label="Verified (task color)"),
        patches.Patch(facecolor="#D8E0E4", edgecolor="none", label="Downstream fail"),
        patches.Patch(facecolor=contract_error_color, edgecolor="none", label="Contract error"),
    ]
    bx.legend(handles=legend_handles, loc="upper center", bbox_to_anchor=(0.50, -0.38),
              ncol=3, frameon=False, fontsize=5.25, handlelength=1.1,
              columnspacing=0.7, handletextpad=0.35)

    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"branch_difficulty.{ext}",
                    bbox_inches="tight", pad_inches=0.025)
    plt.close(fig)


def draw_branch_outcomes() -> None:
    """Branch outcomes without the former successful-run timing panel."""
    outcomes = SNAPSHOT["branch_outcomes_gpt54_medium"]
    task_colors = {
        "End-to-end": FIG_BLUE_DARK,
        "Primary": FIG_BLUE,
        "Proof-only": FIG_BLUE_MID,
    }
    rows = [
        ("End-to-end", outcomes["end_to_end"]),
        ("Primary", outcomes["primary"]),
        ("Proof-only", outcomes["proof_only"]),
    ]
    fig, ax = plt.subplots(figsize=(3.35, 1.45), dpi=FIG_DPI)
    fig.patch.set_facecolor("#FFFFFF")
    ax.set_facecolor("#FFFFFF")
    y_positions = np.arange(len(rows))[::-1]
    contract_error_color = "#B7C5CB"
    for y, (label, row) in zip(y_positions, rows):
        left = 0.0
        segments = [
            (row["correct"], task_colors[label]),
            (row["downstream_fail"], "#D8E0E4"),
            (row["contract_error"], contract_error_color),
        ]
        for value, color in segments:
            if not value:
                continue
            ax.barh(y, value, left=left, height=0.49, color=color,
                    edgecolor="white", linewidth=0.55, zorder=3)
            text_color = "white" if color in {FIG_BLUE_DARK, FIG_BLUE} else FIG_GRAY_DARK
            if value >= 8:
                ax.text(left + value / 2, y, str(value), ha="center", va="center",
                        fontsize=5.9, color=text_color, zorder=5)
            left += value
        ax.text(row["attempted"] + 2.2, y, f"{row['correct']}/{row['attempted']}",
                ha="left", va="center", fontsize=6.3, color=FIG_GRAY)

    ax.set_yticks(y_positions)
    ax.set_yticklabels([label for label, _row in rows], fontsize=6.5)
    for tick, (label, _row) in zip(ax.get_yticklabels(), rows):
        tick.set_color(task_colors[label])
        tick.set_fontweight("semibold")
    ax.set_ylim(-0.52, len(rows) - 0.23)
    ax.set_xlim(0, 145)
    ax.set_xticks([0, 40, 80, 120])
    ax.set_xlabel("evaluated tasks", fontsize=6.6, color=FIG_GRAY_DARK, labelpad=2)
    ax.tick_params(labelsize=6.1, colors=FIG_GRAY, length=0)
    ax.tick_params(axis="y", colors=FIG_GRAY_DARK, length=0)
    ax.grid(True, axis="x", color=FIG_GRID, linewidth=0.5)
    ax.set_axisbelow(True)
    for spine in ax.spines.values():
        spine.set_visible(False)

    legend_handles = [
        patches.Patch(facecolor=FIG_BLUE, edgecolor="none", label="Verified (task color)"),
        patches.Patch(facecolor="#D8E0E4", edgecolor="none", label="Downstream fail"),
        patches.Patch(facecolor=contract_error_color, edgecolor="none", label="Contract error"),
    ]
    ax.legend(handles=legend_handles, loc="upper center", bbox_to_anchor=(0.50, -0.38),
              ncol=3, frameon=False, fontsize=5.25, handlelength=1.1,
              columnspacing=0.7, handletextpad=0.35)
    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"branch_difficulty.{ext}",
                    bbox_inches="tight", pad_inches=0.025)
    plt.close(fig)


# ---------------------------------------------------------------------------
# Harness metric table from the snapshot
# ---------------------------------------------------------------------------

HARNESS_COLORS = {
    harness: HARNESS_STYLES[harness]["color"]
    for harness in ("Codex CLI", "OpenCode", "Claude Code")
}


def harness_rows() -> list[dict[str, object]]:
    rows = []
    for model in ("GLM-5.2", "DeepSeek-V4-Pro"):
        for harness in ("Codex CLI", "OpenCode", "Claude Code"):
            r = SNAPSHOT.get("harness_sensitivity", {}).get(f"{model}|{harness}")
            if not r:
                continue
            rows.append({
                "model": model,
                "harness": harness,
                "color": HARNESS_COLORS[harness],
                "attempted": r["attempted"],
                "correct": r["correct"],
                "errors": r["attempted"] - r["correct"],
                "avg_minutes": r["avg_minutes"],
                "avg_input_tokens": r["avg_input_tokens_m"] * 1e6,
                "avg_output_tokens": r["avg_output_tokens_k"] * 1e3,
                "avg_tool_calls": r["avg_tool_calls"],
                "avg_generated_code_lines": r["avg_generated_code_lines"],
            })
    return rows



# ---------------------------------------------------------------------------
# Harness radar pair: GLM-5.2 and DeepSeek-V4-Pro
# ---------------------------------------------------------------------------

def _harness_radar_data() -> dict[str, list[dict[str, object]]]:
    """Fully audited outcomes on the Claude-selected shared-task cohort."""
    data: dict[str, list[dict[str, object]]] = {}
    for model in ("GLM-5.2", "DeepSeek-V4-Pro"):
        rows = []
        for harness in ("Codex CLI", "OpenCode", "Claude Code"):
            row = SNAPSHOT.get("harness_sensitivity", {}).get(f"{model}|{harness}")
            if not row:
                continue
            rows.append({
                "harness": harness,
                "correct": row["correct"],
                "attempted": row["attempted"],
                "minutes": row["avg_minutes_solved"],
                "in_m": row["avg_input_tokens_m_solved"],
                "tools": row["avg_tool_calls_solved"],
            })
        data[model] = rows
    return data


def draw_harness_radar_pair() -> None:
    """Two real radar charts, one per model, comparing three harnesses."""
    data = _harness_radar_data()
    axis_defs = [
        ("Accuracy", "accuracy"),
        ("Time eff.", "minutes"),
        ("Input-token eff.", "in_m"),
        ("Tool eff.", "tools"),
    ]
    angles = np.linspace(0, 2 * np.pi, len(axis_defs), endpoint=False).tolist()
    closed_angles = angles + angles[:1]
    harness_style = {
        "Codex CLI": (FIG_BLUE_DARK, "o"),
        "OpenCode": (FIG_GRAY, "s"),
        "Claude Code": (FIG_BLUE_MID, "^"),
    }
    fig, axes_pair = plt.subplots(
        1, 2, figsize=(3.55, 2.48), dpi=FIG_DPI,
        subplot_kw={"polar": True},
    )
    fig.patch.set_facecolor("#FFFFFF")
    fig.subplots_adjust(left=0.07, right=0.93, top=0.82, bottom=0.23, wspace=0.72)

    for panel_i, (ax, (model, rows)) in enumerate(zip(axes_pair, data.items())):
        accuracies = [float(r["correct"]) / float(r["attempted"]) for r in rows]
        minima = {
            key: min(float(r[key]) for r in rows if float(r[key]) > 0)
            for _label, key in axis_defs if key != "accuracy"
        }
        for r, accuracy in zip(rows, accuracies):
            harness = str(r["harness"])
            color, marker = harness_style[harness]
            values = [accuracy]
            values.extend(minima[key] / float(r[key]) for _label, key in axis_defs[1:])
            closed_values = values + values[:1]
            ax.plot(closed_angles, closed_values, color=color, linewidth=1.15,
                    marker=marker, markersize=2.8, label=harness, zorder=3)
            ax.fill(closed_angles, closed_values, color=color, alpha=0.07, zorder=2)

        ax.set_theta_offset(np.pi / 2)
        ax.set_theta_direction(-1)
        ax.set_xticks(angles)
        ax.set_xticklabels([label for label, _key in axis_defs],
                           fontsize=4.9, color=FIG_GRAY_DARK, linespacing=0.92)
        ax.set_ylim(0, 1.0)
        ax.set_yticks([0.25, 0.5, 0.75, 1.0])
        ax.set_yticklabels([])
        ax.grid(color=FIG_GRID, linewidth=0.48)
        ax.spines["polar"].set_color(FIG_GRID)
        ax.spines["polar"].set_linewidth(0.55)
        ax.set_title(f"({chr(97 + panel_i)}) {model}", y=1.16,
                     fontsize=7.0, color=FIG_GRAY_DARK, fontweight="semibold")
        accepted = "   ".join(
            f"{str(r['harness']).replace(' Code', '')}: {r['correct']}/{r['attempted']}"
            for r in rows
        )
        ax.text(0.5, -0.25, f"Accepted  {accepted}", transform=ax.transAxes,
                ha="center", va="center", fontsize=4.6, color=FIG_GRAY_DARK)

    handles, labels = axes_pair[0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="lower center", bbox_to_anchor=(0.5, 0.005),
               ncol=3, frameon=False, fontsize=5.8, handlelength=1.6,
               columnspacing=0.9, handletextpad=0.35)

    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"harness_radar.{ext}", bbox_inches="tight", pad_inches=0.03)
    plt.close(fig)


def draw_harness_task_radars() -> None:
    """Cost comparison on successes shared by both models and all harnesses."""
    from matplotlib.lines import Line2D

    axis_defs = [("Wall time", "wall_seconds"),
                 ("Input tokens", "input_tokens"),
                 ("Output tokens", "output_tokens"),
                 ("Tool calls", "tool_calls"),
                 ("Turns", "turns")]
    models = ("GLM-5.2", "DeepSeek-V4-Pro")
    harnesses = ("Codex CLI", "OpenCode", "Claude Code")
    shared_tasks = SNAPSHOT.get("harness_sensitivity_design", {}).get(
        "shared_success_tasks", []
    )
    if not shared_tasks:
        raise RuntimeError(
            "no audited success is shared by both models and all three harnesses"
        )

    rows: list[dict[str, object]] = []
    for model in models:
        for harness in harnesses:
            summary = SNAPSHOT["harness_sensitivity"][f"{model}|{harness}"]
            task_metrics = summary.get("per_task_metrics", {})
            row: dict[str, object] = {
                "model": model,
                "harness": harness,
                "shared_tasks": ";".join(shared_tasks),
            }
            for _label, key in axis_defs:
                values = [
                    float(task_metrics[task][key])
                    for task in shared_tasks
                    if key in task_metrics.get(task, {})
                ]
                row[key] = float(np.mean(values)) if values else float("nan")
            rows.append(row)

    with (FIGURES_DIR / "harness_task_metrics.csv").open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=["model", "harness", "shared_tasks"]
            + [key for _label, key in axis_defs],
        )
        writer.writeheader()
        writer.writerows(rows)

    maxima = {
        key: max(float(row[key]) for row in rows if np.isfinite(float(row[key])))
        for _label, key in axis_defs
    }
    angles = np.linspace(0, 2 * np.pi, len(axis_defs), endpoint=False).tolist()
    closed_angles = angles + angles[:1]
    harness_styles = {
        "Codex CLI": (FIG_BLUE_DARK, "o"),
        "OpenCode": (FIG_GRAY, "s"),
        "Claude Code": (FIG_BLUE_MID, "^"),
    }
    fig, axes = plt.subplots(
        1, 2, figsize=(7.05, 2.65), dpi=FIG_DPI,
        subplot_kw={"polar": True},
    )
    fig.patch.set_facecolor("#FFFFFF")
    fig.subplots_adjust(left=0.08, right=0.92, top=0.76, bottom=0.24,
                        wspace=0.62)

    for panel_i, (ax, model) in enumerate(zip(np.atleast_1d(axes).flat, models)):
        model_rows = [row for row in rows if row["model"] == model]
        for row in model_rows:
            harness = str(row["harness"])
            color, marker = harness_styles[harness]
            values = [float(row[key]) / maxima[key] for _label, key in axis_defs]
            closed_values = values + values[:1]
            ax.plot(closed_angles, closed_values, color=color,
                    linewidth=1.45,
                    marker=marker,
                    markersize=2.8,
                    zorder=3, alpha=0.95)
            ax.fill(closed_angles, closed_values, color=color, alpha=0.055)

        ax.set_theta_offset(np.pi / 2)
        ax.set_theta_direction(-1)
        ax.set_xticks(angles)
        ax.set_xticklabels([label for label, _key in axis_defs],
                           fontsize=5.0, color=FIG_GRAY_DARK)
        radial_max = 1.0
        radial_ticks = np.arange(0.25, radial_max + 0.01, 0.25)
        ax.set_ylim(0, radial_max)
        ax.set_yticks(radial_ticks)
        ax.set_yticklabels([f"{tick:g}" for tick in radial_ticks],
                           fontsize=4.4, color=FIG_GRAY)
        ax.grid(color=FIG_GRID, linewidth=0.48)
        ax.spines["polar"].set_visible(False)
        ax.set_title(f"({chr(97 + panel_i)}) {model}", y=1.16,
                     fontsize=6.8, color=FIG_GRAY_DARK,
                     fontweight="semibold")

    fig.suptitle(
        f"Mean cost on {len(shared_tasks)} six-way shared success"
        f"{'es' if len(shared_tasks) != 1 else ''} (global per-axis maximum = 1)",
        y=0.99, fontsize=7.0, color=FIG_GRAY_DARK,
    )

    legend = [Line2D([0], [0], color=color, marker=marker, linewidth=1.2,
                     markersize=3.2, label=harness)
              for harness, (color, marker) in harness_styles.items()]
    fig.legend(handles=legend, loc="lower center", bbox_to_anchor=(0.5, 0.035),
               ncol=3, frameon=False, fontsize=6.4, handlelength=1.8,
               columnspacing=1.0, handletextpad=0.35)

    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"harness_task_radars.{ext}",
                    bbox_inches="tight", pad_inches=0.035)
    plt.close(fig)


def draw_capability_effort_compact() -> None:
    """Publication-sized, shared-axis capability/effort comparison."""
    from matplotlib.lines import Line2D

    previous_family = plt.rcParams["font.family"]
    plt.rcParams["font.family"] = ["sans-serif"]
    plt.rcParams["font.sans-serif"] = ["TeX Gyre Heros", "Nimbus Sans", "Liberation Sans"]
    fig, axes = plt.subplots(1, 3, figsize=(7.05, 2.38), dpi=FIG_DPI, sharey=True)
    fig.patch.set_facecolor("#FFFFFF")
    fig.subplots_adjust(left=0.068, right=0.995, bottom=0.205, top=0.79, wspace=0.16)

    # Encode every model with both a stable color and a distinct marker so the
    # figure remains readable in grayscale and for color-impaired readers.
    model_markers = {
        "GPT-5.5": "o",
        "GPT-5.4": "s",
        "GPT-5.4-mini": "^",
        "GLM-5.2": "D",
        "DeepSeek-V4-Pro": "p",
        "Kimi for Coding": "X",
    }
    families = [
        ("GPT-5.5", FIG_BLUE_DARK, ["medium", "xhigh"]),
        ("GPT-5.4", FIG_BLUE, ["low", "medium", "high", "xhigh"]),
    ]
    contexts = [
        ("GLM-5.2", "Claude Code", "GLM-5.2", "default"),
        ("Kimi-2.7", "Kimi Code", "Kimi for Coding", "thinking"),
        ("DeepSeek-V4", "Claude Code", "DeepSeek-V4-Pro", "default"),
        ("GPT-5.4-mini", "Codex", "GPT-5.4-mini", "medium"),
    ]
    panels = [
        {
            "key": "avg_minutes", "title": "(a) Wall-clock time",
            "xlabel": "Minutes per accepted task", "xlim": (15, 76),
            "xticks": [20, 40, 60],
            "context_offsets": [(6, 7), (5, 8), (-8, -7), (6, 8)],
        },
        {
            "key": "avg_input_tokens_m", "title": "(b) Input tokens",
            "xlabel": "Input tokens per accepted task (M)", "xlim": (6, 34),
            "xticks": [10, 20, 30],
            "context_offsets": [(6, 7), (5, 8), (-8, -7), (6, 7)],
        },
    ]
    effort_offsets = [{
        "GPT-5.5": {"medium": (5, -11), "xhigh": (6, -3)},
        "GPT-5.4": {"low": (-7, 7), "medium": (5, -12),
                    "high": (6, -4), "xhigh": (6, 7)},
    }, {
        "GPT-5.5": {"medium": (5, -11), "xhigh": (6, -3)},
        "GPT-5.4": {"low": (-20, -3), "medium": (5, 6),
                    "high": (6, -4), "xhigh": (6, 7)},
    }]

    for panel_i, (ax, panel) in enumerate(zip(axes[:2], panels)):
        ax.set_facecolor("#FFFFFF")
        key = panel["key"]
        for model, color, efforts in families:
            points = [combined("Codex", model, effort) for effort in efforts]
            points = [(effort, point) for effort, point in zip(efforts, points) if point]
            xs = [point[key] for _effort, point in points]
            ys = [100.0 * point["accuracy"] for _effort, point in points]
            ax.plot(xs, ys, color=color, linewidth=1.65,
                    marker=model_markers[model], markersize=4.7,
                    markerfacecolor="#FFFFFF", markeredgecolor=color,
                    markeredgewidth=1.25, solid_capstyle="round", zorder=4)
            for effort, point in points:
                dx, dy = effort_offsets[panel_i][model][effort]
                ax.annotate(effort, (point[key], 100.0 * point["accuracy"]),
                            xytext=(dx, dy), textcoords="offset points",
                            fontsize=5.45, color=FIG_GRAY_DARK, zorder=6)

        for (label, harness, model, effort), (dx, dy) in zip(
                contexts, panel["context_offsets"]):
            point = combined(harness, model, effort)
            if not point:
                continue
            context_color = MODEL_STYLES[model]["color"]
            ax.scatter(point[key], 100.0 * point["accuracy"], s=25,
                       marker=model_markers[model],
                       facecolor="#FFFFFF", edgecolor=context_color,
                       linewidth=1.15, zorder=5)

        ax.set_title(panel["title"], loc="left", fontsize=7.05,
                     color="#3E4C59", fontweight="normal", pad=5)
        ax.set_xlabel(panel["xlabel"], fontsize=6.5, color=FIG_GRAY_DARK, labelpad=3)
        ax.set_xlim(*panel["xlim"])
        ax.set_xticks(panel["xticks"])
        ax.set_ylim(0, 64)
        ax.set_yticks([0, 20, 40, 60])
        ax.tick_params(axis="both", labelsize=5.9, colors="#59636B",
                       length=2.0, width=0.5)
        ax.grid(axis="y", color="#E5EAEF", linewidth=0.52, zorder=0)
        ax.grid(axis="x", visible=False)
        ax.spines["top"].set_visible(False)
        ax.spines["right"].set_visible(False)
        ax.spines["left"].set_color("#AEB7BD")
        ax.spines["bottom"].set_color("#AEB7BD")
        ax.spines["left"].set_linewidth(0.55)
        ax.spines["bottom"].set_linewidth(0.55)
        if panel_i == 0:
            ax.set_ylabel("Audited success (%)", fontsize=6.5,
                          color=FIG_GRAY_DARK, labelpad=4)

    # (c) converts elapsed time into cumulative yield.  To keep the narrow
    # panel legible, use the strongest reported effort for each GPT family and
    # the fixed configuration reported for every other model.
    ax = axes[2]
    ax.set_facecolor("#FFFFFF")
    budgets = np.array([30, 60, 90])
    budget_series = [
        ("GPT-5.5", "Codex", "GPT-5.5", "xhigh", MODEL_STYLES["GPT-5.5"]["color"], model_markers["GPT-5.5"]),
        ("GPT-5.4", "Codex", "GPT-5.4", "xhigh", MODEL_STYLES["GPT-5.4"]["color"], model_markers["GPT-5.4"]),
        ("GPT-5.4-mini", "Codex", "GPT-5.4-mini", "medium", MODEL_STYLES["GPT-5.4-mini"]["color"], model_markers["GPT-5.4-mini"]),
        ("GLM-5.2", "Claude Code", "GLM-5.2", "default", MODEL_STYLES["GLM-5.2"]["color"], model_markers["GLM-5.2"]),
        ("DeepSeek-V4-Pro", "Claude Code", "DeepSeek-V4-Pro", "default", MODEL_STYLES["DeepSeek-V4-Pro"]["color"], model_markers["DeepSeek-V4-Pro"]),
        ("kimi-2.7-code", "Kimi Code", "Kimi for Coding", "thinking", MODEL_STYLES["Kimi for Coding"]["color"], model_markers["Kimi for Coding"]),
    ]
    for _label, harness, model, effort, color, marker in budget_series:
        values, _attempted, _correct = _budget_yield(harness, model, effort)
        ax.plot(budgets, values, color=color, linewidth=1.65, marker=marker,
                markersize=4.7, markerfacecolor="#FFFFFF", markeredgecolor=color,
                markeredgewidth=1.25, solid_capstyle="round", zorder=3)
    ax.set_title("(c) Yield by time budget", loc="left", fontsize=7.05,
                 color="#3E4C59", fontweight="normal", pad=5)
    ax.set_xlabel("Wall-clock checkpoint (min)", fontsize=6.15,
                  color=FIG_GRAY_DARK, labelpad=3)
    ax.set_xlim(27, 93)
    ax.set_xticks(budgets)
    ax.set_ylim(0, 64)
    ax.set_yticks([0, 20, 40, 60])
    ax.tick_params(axis="both", labelsize=5.9, colors="#59636B",
                   length=2.0, width=0.5)
    ax.grid(axis="y", color="#E5EAEF", linewidth=0.52, zorder=0)
    ax.grid(axis="x", visible=False)
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.spines["left"].set_color("#AEB7BD")
    ax.spines["bottom"].set_color("#AEB7BD")
    ax.spines["left"].set_linewidth(0.55)
    ax.spines["bottom"].set_linewidth(0.55)

    legend = [
        Line2D([0], [0], color=FIG_BLUE_DARK, marker=model_markers["GPT-5.5"], markerfacecolor="white",
               linewidth=1.6, label="GPT-5.5"),
        Line2D([0], [0], color=FIG_BLUE, marker=model_markers["GPT-5.4"], markerfacecolor="white",
               linewidth=1.6, label="GPT-5.4"),
        Line2D([0], [0], color=MODEL_STYLES["GPT-5.4-mini"]["color"], marker=model_markers["GPT-5.4-mini"],
               markerfacecolor="white", linewidth=1.3, label="GPT-5.4-mini"),
        Line2D([0], [0], color=MODEL_STYLES["GLM-5.2"]["color"], marker=model_markers["GLM-5.2"],
               markerfacecolor="white", linewidth=1.3, label="GLM-5.2"),
        Line2D([0], [0], color=MODEL_STYLES["DeepSeek-V4-Pro"]["color"], marker=model_markers["DeepSeek-V4-Pro"],
               markerfacecolor="white", linewidth=1.3, label="DeepSeek-V4-Pro"),
        Line2D([0], [0], color=MODEL_STYLES["Kimi for Coding"]["color"], marker=model_markers["Kimi for Coding"],
               markerfacecolor="white", linewidth=1.3, label="kimi-2.7-code"),
    ]
    fig.legend(handles=legend, loc="upper center", bbox_to_anchor=(0.5, 0.995),
               ncol=6, frameon=False, fontsize=5.35, handlelength=1.45,
               columnspacing=0.72, handletextpad=0.30)
    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"effort_scaling.{ext}",
                    bbox_inches="tight", pad_inches=0.025)
    plt.close(fig)
    plt.rcParams["font.family"] = previous_family


def _budget_yield(harness: str, model: str, effort: str) -> tuple[list[float], int, int]:
    """Cumulative audited yield at fixed elapsed-time checkpoints.

    The selected workspaces and audited outcomes come directly from the frozen
    statistics snapshot.  A success enters the curve only when its recorded
    end-to-end wall time is no greater than the checkpoint.
    """
    lookup_model = "kimi-2.7-code" if model == "Kimi for Coding" else model
    lookup_effort = (
        "thinking"
        if harness == "Claude Code" and effort == "default"
        else effort
    )
    row = MAIN_140_ROWS.get((harness, lookup_model, lookup_effort))
    if row is None:
        return [0.0, 0.0, 0.0], 0, 0
    thresholds = (30 * 60, 60 * 60, 90 * 60)
    completed = [0, 0, 0]
    for task, outcome in row.get("per_task", {}).items():
        if outcome != "correct":
            continue
        workspace = Path(row["selected_workspaces"][task])
        metrics_path = workspace / "logs" / "metrics.md"
        if not metrics_path.exists():
            continue
        text = metrics_path.read_text(encoding="utf-8", errors="replace")
        matches = re.findall(
            r"^- Wall-clock time \(seconds\): `([^`]*)`", text, re.MULTILINE
        )
        if not matches:
            continue
        try:
            wall_seconds = float(matches[-1])
        except ValueError:
            continue
        for index, threshold in enumerate(thresholds):
            if wall_seconds <= threshold:
                completed[index] += 1
    attempted = int(row["attempted"])
    return [100.0 * count / BENCHMARK_N for count in completed], attempted, int(row["correct"])


def draw_budget_yield() -> None:
    """Audited success accumulated by 30, 60, and 90 minutes."""
    previous_family = plt.rcParams["font.family"]
    plt.rcParams["font.family"] = ["sans-serif"]
    plt.rcParams["font.sans-serif"] = ["TeX Gyre Heros", "Nimbus Sans", "Liberation Sans"]

    fig, axes = plt.subplots(1, 2, figsize=(7.05, 2.30), dpi=FIG_DPI, sharey=True)
    fig.patch.set_facecolor("#FFFFFF")
    fig.subplots_adjust(left=0.075, right=0.992, bottom=0.20, top=0.66, wspace=0.14)
    budgets = np.array([30, 60, 90])

    codex_series = [
        ("GPT-5.5 xhigh", "Codex", "GPT-5.5", "xhigh", FIG_BLUE_DARK, "-", "o"),
        ("GPT-5.5 medium", "Codex", "GPT-5.5", "medium", FIG_BLUE_DARK, "--", "s"),
        ("GPT-5.4 xhigh", "Codex", "GPT-5.4", "xhigh", FIG_BLUE, "-", "o"),
        ("GPT-5.4 high", "Codex", "GPT-5.4", "high", FIG_BLUE, "--", "s"),
        ("GPT-5.4 medium", "Codex", "GPT-5.4", "medium", FIG_BLUE, ":", "D"),
        ("GPT-5.4 low", "Codex", "GPT-5.4", "low", FIG_BLUE, "-.", "^"),
        ("GPT-5.4-mini medium", "Codex", "GPT-5.4-mini", "medium", "#7A8FA0", "-", "v"),
    ]
    other_series = [
        ("GLM-5.2 / Claude", "Claude Code", "GLM-5.2", "default", SLATE, "-", "o"),
        ("DeepSeek-V4-Pro / Claude", "Claude Code", "DeepSeek-V4-Pro", "default", MODEL_STYLES["DeepSeek-V4-Pro"]["color"], "-", "s"),
        ("kimi-2.7-code / Kimi", "Kimi Code", "Kimi for Coding", "thinking", MODEL_STYLES["Kimi for Coding"]["color"], "-", "D"),
    ]

    for panel_index, (ax, title, series) in enumerate(zip(
        axes,
        ("(a) Codex models and effort", "(b) Other model--harness pairs"),
        (codex_series, other_series),
    )):
        ax.set_facecolor("#FAFBFC")
        for label, harness, model, effort, color, linestyle, marker in series:
            values, _attempted, _correct = _budget_yield(harness, model, effort)
            ax.plot(
                budgets, values, label=label, color=color, linestyle=linestyle,
                linewidth=1.55, marker=marker, markersize=4.0,
                markerfacecolor="#FFFFFF", markeredgecolor=color,
                markeredgewidth=1.05, zorder=3,
            )
        ax.set_title(title, loc="left", fontsize=7.2, color="#303A42",
                     fontweight="bold", pad=5)
        ax.set_xlim(27, 93)
        ax.set_xticks(budgets)
        ax.set_xticklabels(["30", "60", "90"])
        ax.set_ylim(0, 65)
        ax.set_yticks([0, 20, 40, 60])
        ax.set_xlabel("Wall-clock checkpoint (min)", fontsize=6.5,
                      color=FIG_GRAY_DARK, labelpad=3)
        ax.tick_params(axis="both", labelsize=6.0, colors="#59636B",
                       length=2.0, width=0.5)
        ax.grid(axis="y", color="#DCE2E6", linewidth=0.52, zorder=0)
        ax.grid(axis="x", color="#E8ECEF", linewidth=0.42, zorder=0)
        ax.spines["top"].set_visible(False)
        ax.spines["right"].set_visible(False)
        ax.spines["left"].set_color("#AEB7BD")
        ax.spines["bottom"].set_color("#AEB7BD")
        ax.spines["left"].set_linewidth(0.55)
        ax.spines["bottom"].set_linewidth(0.55)
        ax.legend(
            loc="lower left", bbox_to_anchor=(0.0, 1.14), frameon=False,
            ncol=3 if panel_index == 0 else 2, fontsize=5.15,
            handlelength=2.25, columnspacing=0.75, handletextpad=0.38,
            borderaxespad=0,
        )
    axes[0].set_ylabel("Cumulative audited success (%)", fontsize=6.5,
                       color=FIG_GRAY_DARK, labelpad=4)

    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"budget_yield.{ext}",
                    bbox_inches="tight", pad_inches=0.025)
    plt.close(fig)
    plt.rcParams["font.family"] = previous_family


def draw_branch_overview_compact() -> None:
    """Three aligned, conference-sized views of branch difficulty."""
    previous_family = plt.rcParams["font.family"]
    plt.rcParams["font.family"] = ["sans-serif"]
    plt.rcParams["font.sans-serif"] = ["TeX Gyre Heros", "Nimbus Sans", "Liberation Sans"]
    profile = BRANCH_140.get("time_profile", SNAPSHOT["branch_time_profile_gpt54_medium"])
    paired_tokens = BRANCH_140.get("paired_work", SNAPSHOT["branch_paired_tokens_gpt54_medium"])
    outcomes = BRANCH_140.get("outcomes", SNAPSHOT["branch_outcomes_gpt54_medium"])
    labels = ["End-to-end", "Primary", "Proof-only"]
    keys = ["end_to_end", "primary", "proof_only"]
    y = np.arange(3)[::-1]

    fig, axes = plt.subplots(
        1, 3, figsize=(7.05, 2.12), dpi=FIG_DPI, sharey=False,
        gridspec_kw={"width_ratios": [1.08, 1.06, 1.08], "wspace": 0.56},
    )
    fig.patch.set_facecolor("#FFFFFF")
    fig.subplots_adjust(left=0.105, right=0.992, bottom=0.20, top=0.78)
    stage_defs = [
        ("Contract", "contract", FIG_BLUE_LIGHT),
        ("Aux. Annotation", "annotation", FIG_BLUE_MID),
        ("Proof", "proof", FIG_BLUE_DARK),
    ]

    # (a) Wall-clock composition uses stage identity, not task identity.
    ax = axes[0]
    for yi, key in zip(y, keys):
        row = profile[key]
        left = 0.0
        for stage, field, color in stage_defs:
            value = float(row.get(field, 0.0))
            if value <= 0:
                continue
            ax.barh(yi, value, left=left, height=0.47, color=color,
                    edgecolor="white", linewidth=0.6, zorder=3)
            if value >= 4.5:
                ax.text(left + value / 2, yi, f"{value:.1f}", ha="center", va="center",
                        fontsize=5.8, color="white" if field == "proof" else FIG_GRAY_DARK)
            left += value
        ax.text(left + 0.6, yi, f"{float(row['total']):.1f}", ha="left", va="center",
                fontsize=5.9, color=FIG_GRAY_DARK, fontweight="semibold")
    ax.set_title("(a) Stage time", loc="left", fontsize=7.3,
                 color=FIG_GRAY_DARK, fontweight="normal", y=1.22, pad=0)
    ax.set_xlim(0, 37)
    ax.set_xticks([0, 10, 20, 30])
    ax.set_xlabel("Mean minutes", fontsize=6.6, color=FIG_GRAY_DARK, labelpad=3)
    ax.set_yticks(y)
    ax.set_yticklabels(labels, fontsize=6.3, color=FIG_GRAY_DARK)
    ax.legend([patches.Patch(facecolor=c) for _s, _f, c in stage_defs],
              [s for s, _f, _c in stage_defs], loc="lower left",
              bbox_to_anchor=(0.0, 1.01), ncol=3, frameon=False, fontsize=5.4,
              borderaxespad=0, handlelength=0.9, columnspacing=0.65,
              handletextpad=0.3)

    # (b) Paired aggregate work: include only tasks accepted in both branches.
    ax = axes[1]
    summary = paired_tokens["summary"]
    metric_defs = [
        ("Time", "minutes", "{:.1f}m"),
        ("Input tokens", "input_m", "{:.1f}M"),
        ("Output tokens", "output_k", "{:.1f}k"),
        ("Tool calls", "tool_calls", "{:.0f}"),
    ]
    metric_y = np.arange(len(metric_defs))[::-1]
    for yi, (label, key, value_format) in zip(metric_y, metric_defs):
        primary_value = float(summary["primary"][key])
        proof_value = float(summary["proof_only"][key])
        proof_relative = 100.0 * proof_value / primary_value if primary_value else 0.0
        ax.barh(yi + 0.13, 100.0, height=0.22, color=FIG_BLUE_DARK, zorder=3)
        ax.barh(yi - 0.13, proof_relative, height=0.22, color=FIG_BLUE_MID, zorder=3)
        ax.text(102.0, yi + 0.13, value_format.format(primary_value), va="center",
                fontsize=5.45, color=FIG_GRAY_DARK)
        ax.text(proof_relative + 2.0, yi - 0.13, value_format.format(proof_value),
                va="center", fontsize=5.45, color=FIG_GRAY_DARK)
    ax.set_title(f"(b) Paired work ($n={int(paired_tokens['runs'])}$)", loc="left", fontsize=7.3,
                 color=FIG_GRAY_DARK, fontweight="normal", y=1.22, pad=0)
    ax.set_xlim(0, 125)
    ax.set_xticks([0, 50, 100])
    ax.set_xlabel("Relative to Primary (%)", fontsize=6.3,
                  color=FIG_GRAY_DARK, labelpad=3)
    ax.set_yticks(metric_y)
    ax.set_yticklabels([label for label, _key, _fmt in metric_defs],
                       fontsize=5.8, color=FIG_GRAY_DARK)
    # The long metric labels extend into the inter-panel gutter.  Keep this
    # axes above its neighbours and remove its opaque patch so Matplotlib does
    # not mask the leading characters when the panels are composed.
    ax.tick_params(axis="y", pad=1.5)
    ax.set_zorder(5)
    ax.patch.set_visible(False)
    ax.legend([patches.Patch(facecolor=FIG_BLUE_DARK),
               patches.Patch(facecolor=FIG_BLUE_MID)],
              ["Primary", "Proof-only"], loc="lower left",
              bbox_to_anchor=(0.0, 1.005), ncol=2, frameon=False,
              fontsize=5.25, borderaxespad=0, handlelength=0.85,
              columnspacing=0.75, handletextpad=0.28)

    # (c) Absolute outcomes preserve the different evaluated-set sizes.
    ax = axes[2]
    outcome_defs = [
        ("Verified", "correct", FIG_BLUE),
        ("Downstream fail", "downstream_fail", "#D8E0E4"),
        ("Contract error", "contract_error", "#AEBFC7"),
    ]
    for yi, key in zip(y, keys):
        row = outcomes[key]
        left = 0.0
        for label, field, color in outcome_defs:
            value = int(row[field])
            if value <= 0:
                continue
            ax.barh(yi, value, left=left, height=0.47, color=color,
                    edgecolor="white", linewidth=0.6, zorder=3)
            if value >= 10:
                ax.text(left + value / 2, yi, str(value), ha="center", va="center",
                        fontsize=5.8, color="white" if field == "correct" else FIG_GRAY_DARK)
            left += value
        ax.text(left + 2.0, yi, f"{row['correct']}/{row['attempted']}",
                ha="left", va="center", fontsize=5.8, color=FIG_GRAY_DARK)
    ax.set_title("(c) Audited outcomes", loc="left", fontsize=7.3,
                 color=FIG_GRAY_DARK, fontweight="normal", y=1.22, pad=0)
    ax.set_xlim(0, 147)
    ax.set_xticks([0, 60, 120])
    ax.set_xlabel("Evaluated tasks", fontsize=6.6, color=FIG_GRAY_DARK, labelpad=3)
    ax.set_yticks(y)
    ax.set_yticklabels(labels, fontsize=6.0, color=FIG_GRAY_DARK)
    ax.tick_params(axis="y", pad=3)
    ax.legend([patches.Patch(facecolor=c) for _l, _f, c in outcome_defs],
              [l for l, _f, _c in outcome_defs], loc="lower left",
              bbox_to_anchor=(0.0, 1.01), ncol=3, frameon=False, fontsize=5.1,
              borderaxespad=0, handlelength=0.85, columnspacing=0.52,
              handletextpad=0.25)

    for panel_i, ax in enumerate(axes):
        ax.set_facecolor("#FFFFFF")
        ax.grid(True, axis="y" if panel_i == 1 else "x",
                color=FIG_GRID, linewidth=0.5, zorder=0)
        ax.tick_params(axis="x", labelsize=6.0, colors=FIG_GRAY_DARK,
                       length=2.0, width=0.5)
        ax.tick_params(axis="y", length=0)
        ax.spines["top"].set_visible(False)
        ax.spines["right"].set_visible(False)
        ax.spines["left"].set_color(FIG_GRAY)
        ax.spines["bottom"].set_color(FIG_GRAY)
        ax.spines["left"].set_linewidth(0.6)
        ax.spines["bottom"].set_linewidth(0.6)

    for ext in ("pdf", "png"):
        fig.savefig(FIGURES_DIR / f"branch_difficulty.{ext}",
                    bbox_inches="tight", pad_inches=0.025)
    plt.close(fig)
    plt.rcParams["font.family"] = previous_family


def main() -> None:
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)

    draw_capability_effort_compact()
    print("wrote figures/effort_scaling.*")

    draw_branch_overview_compact()
    print("wrote figures/branch_difficulty.*")

    draw_task_design()
    print("wrote figures/task_design_agentic.*")


if __name__ == "__main__":
    main()
