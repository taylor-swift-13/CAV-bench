#!/usr/bin/env python3
"""Generate the supplementary primary-task cost table over non-timeout runs."""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
COLLECTOR = ROOT / "scripts" / "collect_stats.py"
OUTPUT = ROOT / "tables" / "non_timeout_cost.tex"


def load_collector():
    spec = importlib.util.spec_from_file_location("cav_collect_stats", COLLECTOR)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {COLLECTOR}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def fmt(value: float, digits: int = 1) -> str:
    return f"{value:.{digits}f}"


def main() -> None:
    cs = load_collector()
    core_tasks = cs.ground_truth_tasks(cs.C_ROOT)
    extension_tasks = cs.ground_truth_tasks(cs.DLC_ROOT)
    grouped: dict[str, list[dict[str, object]]] = {}

    for configs, tasks in (
        (cs.CONFIGS_C, core_tasks),
        (cs.CONFIGS_DLC, extension_tasks),
    ):
        for harness_key, harness, model, effort, result_dir in configs:
            row = cs.summarize_config(harness_key, result_dir, tasks, with_traces=True)
            if row is None:
                continue
            row.update(harness=harness, model=model, effort=effort)
            grouped.setdefault(cs.config_key(harness, model, effort), []).append(row)

    combined = {key: cs.combine_primary_rows(rows) for key, rows in grouped.items()}
    order = [
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
    display_model = {"Kimi for Coding": "kimi-2.7-code"}
    display_effort = {"default": "thinking"}

    lines: list[str] = []
    last_harness = ""
    for harness, model, effort in order:
        row = combined[cs.config_key(harness, model, effort)]
        if harness != last_harness:
            if lines:
                lines.append(r"\addlinespace[2.2pt]")
            lines.append(rf"\textit{{{harness}}} & & & & & & & \\")
            last_harness = harness
        profile = row["avg_tool_profile_non_timeout"]
        label = f"{display_model.get(model, model)} ({display_effort.get(effort, effort)})"
        lines.append(
            rf"\quad {label} & {int(row['non_timeout_runs'])}"
            rf" & {fmt(float(row['avg_minutes_non_timeout']))}"
            rf" & {fmt(float(row['avg_input_tokens_m_non_timeout']))}/{fmt(float(row['avg_output_tokens_k_non_timeout']), 0)}"
            rf" & {fmt(float(profile['read']))}/{fmt(float(profile['write']))}"
            rf" & {fmt(float(row['avg_tool_calls_non_timeout']))}"
            rf" & {fmt(float(profile['coqc']))}/{fmt(float(profile['vcg']))}"
            rf" & {fmt(float(profile['rounds']))} \\")

    lines.append(r"\bottomrule")
    OUTPUT.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"wrote {OUTPUT}")


if __name__ == "__main__":
    main()
