#!/usr/bin/env python3
"""Audit and summarize GLM-5.2 under three code-agent harnesses."""

from __future__ import annotations

import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from statistics import mean

import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
import numpy as np

plt.rcParams["font.family"] = ["sans-serif"]
plt.rcParams["font.sans-serif"] = ["TeX Gyre Heros", "Nimbus Sans", "Liberation Sans"]


ROOT = Path(__file__).resolve().parents[1]
SCRIPT_DIR = ROOT / "scripts"
sys.path.insert(0, str(SCRIPT_DIR))

import collect_stats as audit  # noqa: E402


FIGURES = ROOT / "figures"
SPLITS = (
    ("main", Path("/home/yangfp/CAV/main/CAV-bench")),
    ("2.0.3", Path("/home/yangfp/CAV/2.0.3/CAV-bench")),
    ("2.0.4", Path("/home/yangfp/CAV/2.0.4/CAV-bench")),
)
HARNESSES = (
    ("Claude Code", "Claude Code", "claude"),
    ("OpenCode", "OpenCode", "opencode"),
    ("Codex CLI", "Codex CLI", "codex"),
)
COLORS = {
    "Accepted": "#2F6F8A",
    "Wrong": "#AEBFC7",
    "Timeout": "#D9E0E4",
}
HARNESS_STYLES = {
    "Claude Code": ("#82B6CA", "^"),
    "OpenCode": ("#8C979D", "s"),
    "Codex CLI": ("#2F6F8A", "o"),
}
RADAR_METRICS = (
    ("Time", "wall_seconds"),
    ("Input", "input_tokens"),
    ("Output", "output_tokens"),
    ("Tools", "tool_calls"),
)


def collect() -> dict[str, object]:
    parts: dict[str, list[dict[str, object]]] = {name: [] for name, _key, _dir in HARNESSES}
    task_metrics: dict[str, dict[str, dict[str, object]]] = {
        name: {} for name, _key, _dir in HARNESSES
    }
    cohorts: dict[str, list[str]] = {}

    for split_name, split_root in SPLITS:
        all_tasks = audit.ground_truth_tasks(split_root)
        claude_dir = split_root / "results" / "claude" / "glm-5.2" / "api"
        claude_all = audit.summarize_config(
            "Claude Code", claude_dir, all_tasks, False
        )
        if claude_all is None:
            raise RuntimeError(f"missing Claude Code results for {split_name}")
        # Fix the cohort before inspecting either alternative harness: every
        # GLM-5.2 task accepted under the main-paper Claude Code setup.
        cohort = {
            task for task, outcome in claude_all["per_task"].items()
            if outcome == "correct"
        }
        cohorts[split_name] = sorted(cohort)
        if not cohort:
            continue
        for name, harness_key, result_dir in HARNESSES:
            row = audit.summarize_config(
                harness_key,
                split_root / "results" / result_dir / "glm-5.2" / "api",
                cohort,
                True,
            )
            if row is None:
                raise RuntimeError(f"missing {name} results for {split_name}")
            if int(row["attempted"]) != len(cohort):
                raise RuntimeError(
                    f"incomplete {name} cohort for {split_name}: "
                    f"{row['attempted']}/{len(cohort)}"
                )
            parts[name].append(row)
            for task, metrics in row["per_task_metrics"].items():
                task_metrics[name][f"{split_name}/{task}"] = metrics

    combined = {
        name: audit.combine_primary_rows(rows) for name, rows in parts.items()
    }
    shared_successes = sorted(
        task
        for task in set.intersection(*(set(rows) for rows in task_metrics.values()))
        if all(task_metrics[name][task].get("outcome") == "correct" for name in task_metrics)
    )

    metric_keys = ("wall_seconds", "input_tokens", "output_tokens", "tool_calls", "turns")
    paired: dict[str, dict[str, float | int]] = {}
    for name in task_metrics:
        row: dict[str, float | int] = {"tasks": len(shared_successes)}
        for key in metric_keys:
            values = [
                float(task_metrics[name][task][key])
                for task in shared_successes
                if key in task_metrics[name][task]
            ]
            row[key] = mean(values) if values else 0.0
            row[f"{key}_runs"] = len(values)
        paired[name] = row

    return {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "model": "GLM-5.2",
        "selection": "all tasks accepted under Claude Code before inspecting OpenCode or Codex CLI",
        "cohorts": cohorts,
        "cohort_size": sum(len(tasks) for tasks in cohorts.values()),
        "rows": combined,
        "shared_success_tasks": shared_successes,
        "shared_task_metrics": {
            task: {name: task_metrics[name][task] for name in task_metrics}
            for task in shared_successes
        },
        "paired_success_cost": paired,
    }


def draw_outcomes(data: dict[str, object]) -> None:
    rows = data["rows"]
    names = [name for name, _key, _dir in HARNESSES]
    labels = ["Claude Code", "OpenCode", "Codex CLI"]
    x = np.arange(len(names))
    fig, ax = plt.subplots(figsize=(3.45, 2.2), dpi=300)
    fig.patch.set_facecolor("white")
    bottom = np.zeros(len(names))
    for category, key in (("Accepted", "correct"), ("Wrong", "wrong"), ("Timeout", "timeout")):
        values = np.array([100.0 * rows[name][key] / rows[name]["attempted"] for name in names])
        bars = ax.bar(x, values, width=0.58, bottom=bottom, color=COLORS[category],
                      edgecolor="white", linewidth=0.45, label=category)
        for bar, value, base in zip(bars, values, bottom):
            if value >= 8:
                ax.text(bar.get_x() + bar.get_width() / 2, base + value / 2,
                        f"{value:.1f}", ha="center", va="center", fontsize=6.1,
                        color="white" if category == "Accepted" else "#44515A")
        bottom += values
    ax.set_xticks(x, labels, fontsize=6.7)
    ax.set_ylabel("Audited outcomes (%)", fontsize=7.0, color="#4A545A")
    ax.set_ylim(0, 100)
    ax.set_yticks([0, 25, 50, 75, 100])
    ax.tick_params(axis="y", labelsize=6.4, colors="#6B7479", length=0)
    ax.tick_params(axis="x", colors="#4A545A", length=0)
    ax.grid(axis="y", color="#DCE2E5", linewidth=0.55)
    ax.set_axisbelow(True)
    for spine in ax.spines.values():
        spine.set_visible(False)
    ax.legend(loc="upper center", bbox_to_anchor=(0.5, 1.15), ncol=3,
              frameon=False, fontsize=6.1, columnspacing=0.8, handletextpad=0.3)
    fig.tight_layout(pad=0.55)
    for ext in ("pdf", "png"):
        fig.savefig(FIGURES / f"harness_glm52_pass_rate.{ext}",
                    bbox_inches="tight", pad_inches=0.025)
    plt.close(fig)


def representative_tasks(data: dict[str, object]) -> list[str]:
    """Select low-, median-, and high-sensitivity shared successes."""
    scored = []
    for task, metrics in data["shared_task_metrics"].items():
        ratios = []
        for _label, key in RADAR_METRICS:
            values = [float(metrics[name][key]) for name, _hkey, _dir in HARNESSES]
            ratios.append(max(values) / min(values))
        scored.append((mean(ratios), task))
    scored.sort()
    return [scored[0][1], scored[len(scored) // 2][1], scored[-1][1]]


def draw_representative_radars(data: dict[str, object]) -> None:
    tasks = data["representative_tasks"]
    angles = np.linspace(0, 2 * np.pi, len(RADAR_METRICS), endpoint=False).tolist()
    closed_angles = angles + angles[:1]
    fig, axes = plt.subplots(
        1, len(tasks), figsize=(7.05, 2.32), dpi=300,
        subplot_kw={"polar": True}, squeeze=False,
    )
    fig.patch.set_facecolor("white")
    fig.subplots_adjust(left=0.045, right=0.955, top=0.77, bottom=0.22, wspace=0.55)

    for panel, (ax, task) in enumerate(zip(axes.flat, tasks)):
        metrics = data["shared_task_metrics"][task]
        maxima = {
            key: max(float(metrics[name][key]) for name, _hkey, _dir in HARNESSES)
            for _label, key in RADAR_METRICS
        }
        for name, _hkey, _dir in HARNESSES:
            color, marker = HARNESS_STYLES[name]
            values = [float(metrics[name][key]) / maxima[key] for _label, key in RADAR_METRICS]
            closed = values + values[:1]
            ax.plot(closed_angles, closed, color=color, linewidth=1.35,
                    marker=marker, markersize=3.0, zorder=3)
            ax.fill(closed_angles, closed, color=color, alpha=0.055)
        ax.set_theta_offset(np.pi / 2)
        ax.set_theta_direction(-1)
        ax.set_xticks(angles)
        ax.set_xticklabels([label for label, _key in RADAR_METRICS],
                           fontsize=5.4, color="#4A545A")
        ax.set_ylim(0, 1.0)
        ax.set_yticks([0.25, 0.5, 0.75, 1.0])
        ax.set_yticklabels([".25", ".50", ".75", "1.0"],
                           fontsize=4.5, color="#8C979D")
        ax.grid(color="#DCE2E5", linewidth=0.48)
        ax.spines["polar"].set_visible(False)
        task_label = task.split("/", 1)[-1].replace("_", " ")
        sensitivity = ("low", "median", "high")[panel]
        ax.set_title(f"({chr(97 + panel)}) {task_label}\n{sensitivity} difference",
                     y=1.18, fontsize=6.6, color="#4A545A", fontweight="normal")

    legend = [
        Line2D([0], [0], color=HARNESS_STYLES[name][0],
               marker=HARNESS_STYLES[name][1], linewidth=1.25,
               markersize=3.4, label=name)
        for name, _hkey, _dir in HARNESSES
    ]
    fig.legend(handles=legend, loc="lower center", bbox_to_anchor=(0.5, 0.025),
               ncol=3, frameon=False, fontsize=6.3, handlelength=1.8,
               columnspacing=1.0, handletextpad=0.35)
    for ext in ("pdf", "png"):
        fig.savefig(FIGURES / f"harness_task_radars.{ext}",
                    bbox_inches="tight", pad_inches=0.035)
    plt.close(fig)


def main() -> None:
    FIGURES.mkdir(parents=True, exist_ok=True)
    data = collect()
    data["representative_tasks"] = representative_tasks(data)
    (FIGURES / "harness_glm52_30_audit.json").write_text(
        json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    draw_outcomes(data)
    draw_representative_radars(data)
    print(
        f"wrote GLM-5.2 harness results for {data['cohort_size']} tasks; "
        f"shared audited successes={len(data['shared_success_tasks'])}"
    )


if __name__ == "__main__":
    main()
