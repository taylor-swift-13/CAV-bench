#!/usr/bin/env python3
"""Build Figure 4 statistics from all three CAV-Bench branches."""

from __future__ import annotations

import json
import sys
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
ROOT = SCRIPT_DIR.parent
sys.path.insert(0, str(SCRIPT_DIR))

import collect_stats as stats  # noqa: E402


BRANCHES = (
    Path("/home/yangfp/CAV/main/CAV-bench"),
    Path("/home/yangfp/CAV/2.0.3/CAV-bench"),
    Path("/home/yangfp/CAV/2.0.4/CAV-bench"),
)


def merge(parts: list[dict]) -> dict:
    merged = {}
    for part in parts:
        overlap = set(merged) & set(part)
        if overlap:
            raise RuntimeError(f"task overlap across branches: {sorted(overlap)}")
        merged.update(part)
    return merged


def main() -> None:
    tasks = {root: stats.ground_truth_tasks(root) for root in BRANCHES}
    if [len(tasks[root]) for root in BRANCHES] != [102, 30, 8]:
        raise RuntimeError("unexpected three-branch task counts")

    e2e_rows = [
        stats.summarize_pipeline(
            root / "pipeline_results/codex/gpt-5.4/medium", tasks[root]
        )
        for root in BRANCHES
    ]
    main_snapshot = json.loads(
        (ROOT / "figures" / "main_table_140_audit.json").read_text(encoding="utf-8")
    )
    primary_row = next(
        row for row in main_snapshot["rows"]
        if row["model"] == "GPT-5.4" and row["effort"] == "medium"
    )

    e2e_attempted = sum(int(row["attempted"]) for row in e2e_rows)
    e2e_correct = sum(int(row["correct"]) for row in e2e_rows)
    e2e_downstream = sum(
        int(row["status_counts"].get("audit_check_failed", 0))
        + int(row["status_counts"].get("protocol_downstream_rejected", 0))
        for row in e2e_rows
    )
    proof_attempted = 0
    proof_correct = 0
    for root in BRANCHES:
        selected, report = stats.selected_workspaces(
            root / "proof_results/codex/gpt-5.4/medium", "proof"
        )
        rejected = set(report["tasks"])
        for task, workspace in selected.items():
            if task not in tasks[root]:
                continue
            proof_attempted += 1
            metrics = (workspace / "logs" / "metrics.md").read_text(
                encoding="utf-8", errors="replace"
            )
            if task not in rejected and stats.classify(metrics) == "correct":
                proof_correct += 1
    outcomes = {
        "end_to_end": {
            "attempted": e2e_attempted,
            "correct": e2e_correct,
            "downstream_fail": e2e_downstream,
            "contract_error": e2e_attempted - e2e_correct - e2e_downstream,
        },
        "primary": {
            "attempted": int(primary_row["attempted"]),
            "correct": int(primary_row["correct"]),
            "downstream_fail": int(primary_row["attempted"]) - int(primary_row["correct"]),
            "contract_error": 0,
        },
        "proof_only": {
            "attempted": proof_attempted,
            "correct": proof_correct,
            "downstream_fail": proof_attempted - proof_correct,
            "contract_error": 0,
        },
    }

    e2e_stage_parts = []
    e2e_phase_parts = []
    primary_phase_parts = []
    proof_phase_parts = []
    primary_token_parts = []
    proof_token_parts = []
    primary_tool_parts = []
    proof_tool_parts = []
    for root in BRANCHES:
        branch_tasks = tasks[root]
        stage_rows, phase_rows = stats.runner_success_pipeline_timings(
            root / "pipeline_results/codex/gpt-5.4/medium", branch_tasks
        )
        _selected_pipeline, pipeline_report = stats.selected_pipeline_workspaces(
            root / "pipeline_results/codex/gpt-5.4/medium"
        )
        rejected_pipeline = set(pipeline_report["tasks"])
        stage_rows = {
            name: row for name, row in stage_rows.items()
            if name not in rejected_pipeline
        }
        phase_rows = {
            name: row for name, row in phase_rows.items()
            if name not in rejected_pipeline
        }
        e2e_stage_parts.append(stage_rows)
        e2e_phase_parts.append(phase_rows)
        primary_phase_parts.append(stats.stage_task_phase_minutes(
            root / "results/codex/gpt-5.4/medium", branch_tasks, "verify",
        ))
        proof_phase_parts.append(stats.stage_task_phase_minutes(
            root / "proof_results/codex/gpt-5.4/medium", branch_tasks, "proof",
            proof_only=True,
        ))
        primary_token_parts.append(stats.successful_tokens_by_task(
            root / "results/codex/gpt-5.4/medium", branch_tasks, "verify"
        ))
        proof_token_parts.append(stats.successful_tokens_by_task(
            root / "proof_results/codex/gpt-5.4/medium", branch_tasks, "proof"
        ))
        primary_tool_parts.append(stats.successful_tool_profiles_by_task(
            root / "results/codex/gpt-5.4/medium", branch_tasks, "verify"
        ))
        proof_tool_parts.append(stats.successful_tool_profiles_by_task(
            root / "proof_results/codex/gpt-5.4/medium", branch_tasks, "proof"
        ))

    e2e_stage = merge(e2e_stage_parts)
    e2e_phase = merge(e2e_phase_parts)
    primary_phase = merge(primary_phase_parts)
    proof_phase = merge(proof_phase_parts)
    primary_token = merge(primary_token_parts)
    proof_token = merge(proof_token_parts)
    primary_tool = merge(primary_tool_parts)
    proof_tool = merge(proof_tool_parts)

    e2e_names = sorted(set(e2e_stage) & set(e2e_phase))
    time_profile = {
        "end_to_end": {
            "runs": len(e2e_names),
            "contract": stats.mean([
                float(e2e_stage[name].get("contract", 0.0)) for name in e2e_names
            ]),
            "annotation": stats.mean([
                float(e2e_stage[name].get("eval", 0.0))
                + float(e2e_phase[name]["annotation"]) for name in e2e_names
            ]),
            "proof": stats.mean([
                float(e2e_phase[name]["proof"]) for name in e2e_names
            ]),
        },
        "primary": {
            "runs": len(primary_phase),
            "contract": 0.0,
            "annotation": stats.mean([
                float(row["annotation"]) for row in primary_phase.values()
            ]),
            "proof": stats.mean([float(row["proof"]) for row in primary_phase.values()]),
        },
        "proof_only": {
            "runs": len(proof_phase),
            "contract": 0.0,
            "annotation": 0.0,
            "proof": stats.mean([float(row["proof"]) for row in proof_phase.values()]),
        },
    }
    for row in time_profile.values():
        row["total"] = row["contract"] + row["annotation"] + row["proof"]

    paired = sorted(
        set(primary_phase) & set(proof_phase)
        & set(primary_token) & set(proof_token)
        & set(primary_tool) & set(proof_tool)
    )
    paired_work = {
        "runs": len(paired),
        "tasks": paired,
        "summary": {
            "primary": {
                "minutes": stats.mean([
                    float(primary_phase[name]["annotation"])
                    + float(primary_phase[name]["proof"]) for name in paired
                ]),
                "input_m": stats.mean([float(primary_token[name]["input_m"]) for name in paired]),
                "output_k": stats.mean([float(primary_token[name]["output_k"]) for name in paired]),
                "tool_calls": stats.mean([float(primary_tool[name]["total"]) for name in paired]),
            },
            "proof_only": {
                "minutes": stats.mean([float(proof_phase[name]["proof"]) for name in paired]),
                "input_m": stats.mean([float(proof_token[name]["input_m"]) for name in paired]),
                "output_k": stats.mean([float(proof_token[name]["output_k"]) for name in paired]),
                "tool_calls": stats.mean([float(proof_tool[name]["total"]) for name in paired]),
            },
        },
    }

    payload = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "branch_sizes": {str(root): len(tasks[root]) for root in BRANCHES},
        "outcomes": outcomes,
        "time_profile": time_profile,
        "paired_work": paired_work,
    }
    (ROOT / "figures" / "branch_140_audit.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()
