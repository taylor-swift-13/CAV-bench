#!/usr/bin/env python3
"""Audit the three benchmark splits and generate the 140-task main table."""

from __future__ import annotations

import json
import sys
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
ROOT = SCRIPT_DIR.parent
sys.path.insert(0, str(SCRIPT_DIR))

import collect_stats as audit  # noqa: E402


SPLITS = (
    ("main", Path("/home/yangfp/CAV/main/CAV-bench")),
    ("2.0.3", Path("/home/yangfp/CAV/2.0.3/CAV-bench")),
    ("2.0.4", Path("/home/yangfp/CAV/2.0.4/CAV-bench")),
)
CONFIGS = (
    ("Codex", "Codex CLI", "GPT-5.5", "xhigh", "codex/gpt-5.5/xhigh"),
    ("Codex", "Codex CLI", "GPT-5.5", "medium", "codex/gpt-5.5/medium"),
    ("Codex", "Codex CLI", "GPT-5.4", "xhigh", "codex/gpt-5.4/xhigh"),
    ("Codex", "Codex CLI", "GPT-5.4", "high", "codex/gpt-5.4/high"),
    ("Codex", "Codex CLI", "GPT-5.4", "medium", "codex/gpt-5.4/medium"),
    ("Codex", "Codex CLI", "GPT-5.4", "low", "codex/gpt-5.4/low"),
    ("Codex", "Codex CLI", "GPT-5.4-mini", "medium", "codex/gpt-5.4-mini/medium"),
    ("Claude Code", "Claude Code", "GLM-5.2", "thinking", "claude/glm-5.2/api"),
    ("Claude Code", "Claude Code", "DeepSeek-V4-Pro", "thinking", "claude/deepseek-v4-pro/api"),
    ("Kimi Code", "Kimi Code", "kimi-2.7-code", "thinking", "kimicode/kimi-code__kimi-for-coding/thinking"),
)
DENOMINATOR = 140


def main() -> None:
    if (ROOT / "figures" / "publication_results.json").exists():
        from make_publication_tables import main as render_publication
        render_publication()
        return
    split_tasks = {name: audit.ground_truth_tasks(root) for name, root in SPLITS}
    split_sizes = {name: len(tasks) for name, tasks in split_tasks.items()}
    if split_sizes != {"main": 102, "2.0.3": 30, "2.0.4": 8}:
        raise RuntimeError(f"unexpected split sizes: {split_sizes}")

    rows = []
    for group, harness_key, model, effort, relative in CONFIGS:
        parts = []
        for split_name, split_root in SPLITS:
            row = audit.summarize_config(
                harness_key,
                split_root / "results" / relative,
                split_tasks[split_name],
                True,
            )
            if row:
                parts.append(row)
        combined = audit.combine_primary_rows(parts)
        combined.update({"group": group, "model": model, "effort": effort})
        combined["missing"] = DENOMINATOR - int(combined["attempted"])
        combined["success_rate_140"] = float(combined["correct"]) / DENOMINATOR
        rows.append(combined)
        print(
            f"{model} {effort}: {combined['correct']}/{DENOMINATOR}, "
            f"F/T={combined['wrong']}/{combined['timeout'] + combined['missing']} "
            "(missing counted as timeout)"
        )

    best = max(float(row["success_rate_140"]) for row in rows)
    lines = []
    previous_group = None
    for row in rows:
        group = str(row["group"])
        if previous_group is not None and group != previous_group:
            lines.append(r"\addlinespace[2.2pt]")
        if group != previous_group:
            lines.append(r"\textit{" + group + r"} & & & & & & & & & \\")
        previous_group = group
        rate = 100.0 * float(row["success_rate_140"])
        rate_text = f"\\textbf{{{rate:.1f}}}" if float(row["success_rate_140"]) == best else f"{rate:.1f}"
        profile = row["avg_tool_profile_solved"]
        lines.append(
            f"\\quad {row['model']} ({row['effort']}) & "
            f"{row['correct']}/{DENOMINATOR} & "
            f"{row['wrong']}/{row['timeout'] + row['missing']} & {rate_text} & "
            f"{row['avg_minutes_solved']:.1f} & "
            f"{row['avg_input_tokens_m_solved']:.1f}/{row['avg_output_tokens_k_solved']:.0f} & "
            f"{profile['read']:.1f}/{profile['write']:.1f} & "
            f"{profile['total']:.1f} & {profile['coqc']:.1f}/{profile['vcg']:.1f} & "
            f"{profile['rounds']:.1f} \\\\"
        )
    lines.append(r"\bottomrule")
    (ROOT / "tables" / "main_results.tex").write_text(
        "\n".join(lines) + "\n", encoding="utf-8"
    )

    payload = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "denominator": DENOMINATOR,
        "splits": split_sizes,
        "selection_and_audit_policy": audit.__doc__,
        "rows": rows,
    }
    (ROOT / "figures" / "main_table_140_audit.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()
