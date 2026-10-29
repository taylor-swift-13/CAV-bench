#!/usr/bin/env python3
"""Generate the primary-task failure table from the audited 140-task snapshot."""

from __future__ import annotations

import json
import sys
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
ROOT = SCRIPT_DIR.parent
sys.path.insert(0, str(SCRIPT_DIR))

import collect_stats as audit  # noqa: E402


def has_proof_goals(workspace: Path) -> bool:
    """Whether VCG produced a nonempty goal artifact for the submitted program."""
    for path in workspace.rglob("*_goal.v"):
        if path.is_file() and path.read_text(encoding="utf-8", errors="replace").strip():
            return True
    return False


def artifact_groups(workspace: Path) -> set[str]:
    result = audit.artifact_audit_module(workspace).scan_workspace(workspace)
    return {
        str(finding.get("group"))
        for finding in result.get("findings", [])
        if finding.get("severity") == "error"
    }


def main() -> None:
    if (ROOT / "figures" / "publication_results.json").exists():
        from make_publication_tables import main as render_publication
        render_publication()
        return
    snapshot_path = ROOT / "figures" / "main_table_140_audit.json"
    snapshot = json.loads(snapshot_path.read_text(encoding="utf-8"))
    output_rows: list[dict[str, object]] = []

    for row in snapshot["rows"]:
        proof = 0
        vcg = 0
        invalid_proof = 0
        input_modification = 0
        prohibited_read = 0

        for task, outcome in row["per_task"].items():
            workspace = Path(row["selected_workspaces"][task])
            if outcome == "wrong":
                if has_proof_goals(workspace):
                    proof += 1
                else:
                    vcg += 1

            metrics_path = workspace / "logs" / "metrics.md"
            metrics = metrics_path.read_text(encoding="utf-8", errors="replace")
            groups = artifact_groups(workspace)
            # Proof shortcuts are counted only when the agent claimed success;
            # incomplete failed proofs naturally contain unfinished material.
            if audit.final_result(metrics) == "Success" and groups & {
                "proof_bypass",
                "import_review",
            }:
                invalid_proof += 1
            if "source_integrity" in groups:
                input_modification += 1

            protocol = row["protocol_rejections"]["tasks"].get(task, {})
            if "transcript_leakage" in protocol.get("reasons", []):
                prohibited_read += 1

        output_rows.append(
            {
                "group": row["group"],
                "model": row["model"],
                "effort": row["effort"],
                "failure": int(row["wrong"]),
                "timeout": int(row["timeout"]) + int(row["missing"]),
                "proof": proof,
                "vcg": vcg,
                "invalid_proof": invalid_proof,
                "input_modification": input_modification,
                "prohibited_read": prohibited_read,
            }
        )

    lines: list[str] = []
    previous_group: str | None = None
    totals: Counter[str] = Counter()
    numeric_keys = (
        "failure",
        "timeout",
        "proof",
        "vcg",
        "invalid_proof",
        "input_modification",
        "prohibited_read",
    )
    for row in output_rows:
        group = str(row["group"])
        if previous_group is not None and group != previous_group:
            lines.append(r"\addlinespace[2.2pt]")
        if group != previous_group:
            lines.append(r"\textit{" + group + r"} & & & \\")
        previous_group = group
        for key in numeric_keys:
            totals[key] += int(row[key])
        lines.append(
            f"\\quad {row['model']} ({row['effort']}) & "
            f"{row['failure']}/{row['timeout']} & "
            f"{row['proof']}/{row['vcg']} & "
            f"{row['invalid_proof']}/{row['input_modification']}/{row['prohibited_read']}"
            + " " + "\\\\"
        )
    lines.extend(
        [
            r"\midrule",
            "\\textbf{Total} & "
            f"\\textbf{{{totals['failure']}/{totals['timeout']}}} & "
            f"\\textbf{{{totals['proof']}/{totals['vcg']}}} & "
            f"\\textbf{{{totals['invalid_proof']}/{totals['input_modification']}/{totals['prohibited_read']}}}"
            + " " + "\\\\",
            r"\bottomrule",
        ]
    )
    (ROOT / "tables" / "error_analysis_models.tex").write_text(
        "\n".join(lines) + "\n", encoding="utf-8"
    )
    payload = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "source_snapshot": str(snapshot_path),
        "stage_rule": "proof iff the selected failed run contains a nonempty *_goal.v; otherwise VCG",
        "audit_rule": {
            "P": "claimed-success artifact rejected for proof bypass or forbidden import",
            "I": "contract or executable implementation differs from the fixed input",
            "R": "transcript audit detects access to disallowed material",
        },
        "rows": output_rows,
        "totals": dict(totals),
    }
    (ROOT / "figures" / "error_table_140_audit.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()
