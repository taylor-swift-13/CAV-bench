#!/usr/bin/env python3
"""Draw the multi-label GPT-5.4-medium non-timeout error distribution.

The five slices count error-label incidences rather than disjoint tasks.  The
underlying cohort contains 112 audited rejections after excluding the four
raw timeout runs.  A task can contribute to more than one audit category.
"""

from __future__ import annotations

import csv
from pathlib import Path

import matplotlib.pyplot as plt


ROOT = Path(__file__).resolve().parents[1]
FIGURES = ROOT / "figures"

# Final-stage classification of the frozen GPT-5.4-medium primary runs.
# The 96 raw non-timeout failures split into 88 proof-stage and 8
# annotation/VCG-stage failures.  The remaining labels come from the external
# transcript and artifact audits and may overlap those failures or each other.
ERROR_COUNTS = {
    "Proof error": 88,
    "Prohibited read": 27,
    "Input modification": 13,
    "Proof bypass": 9,
    "Annotation / VCG error": 8,
}

COLORS = ["#4C78A8", "#E45756", "#F2CF5B", "#B279A2", "#72B7B2"]


def main() -> None:
    FIGURES.mkdir(parents=True, exist_ok=True)
    labels = list(ERROR_COUNTS)
    values = list(ERROR_COUNTS.values())
    total = sum(values)

    fig, ax = plt.subplots(figsize=(3.35, 2.55), dpi=220)
    wedges, _, autotexts = ax.pie(
        values,
        colors=COLORS,
        startangle=105,
        counterclock=False,
        autopct=lambda pct: f"{pct:.1f}%",
        pctdistance=0.76,
        wedgeprops={"width": 0.48, "edgecolor": "white", "linewidth": 0.9},
        textprops={"fontsize": 7.2, "color": "#263238"},
    )
    for text in autotexts:
        text.set_fontweight("semibold")

    legend_labels = [f"{label}  ({value})" for label, value in zip(labels, values)]
    ax.legend(
        wedges,
        legend_labels,
        loc="center left",
        bbox_to_anchor=(0.96, 0.5),
        frameon=False,
        fontsize=7.2,
        handlelength=1.0,
        handletextpad=0.5,
        labelspacing=0.55,
    )
    ax.text(0, 0.08, str(total), ha="center", va="center", fontsize=14,
            fontweight="bold", color="#263238")
    ax.text(0, -0.13, "error labels", ha="center", va="center", fontsize=7.2,
            color="#667085")
    ax.set(aspect="equal")
    fig.subplots_adjust(left=0.0, right=0.70, top=0.98, bottom=0.02)

    for suffix in ("pdf", "png"):
        fig.savefig(FIGURES / f"gpt54_medium_error_pie.{suffix}",
                    bbox_inches="tight", pad_inches=0.02)
    plt.close(fig)

    with (FIGURES / "gpt54_medium_error_pie.csv").open("w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["error_category", "count", "share_of_error_labels_percent"])
        for label, value in zip(labels, values):
            writer.writerow([label, value, f"{100 * value / total:.1f}"])


if __name__ == "__main__":
    main()
