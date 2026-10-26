#!/usr/bin/env python3
"""Generate supplementary non-timeout cost rows from the 140-task audit."""

from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    snapshot = json.loads(
        (ROOT / "figures" / "main_table_140_audit.json").read_text(encoding="utf-8")
    )
    lines = []
    previous_group = None
    for row in snapshot["rows"]:
        group = str(row["group"])
        if previous_group is not None and group != previous_group:
            lines.append(r"\addlinespace[2.2pt]")
        if group != previous_group:
            lines.append(r"\textit{" + group + "} & & & & & & & " + "\\\\")
        previous_group = group
        profile = row["avg_tool_profile_non_timeout"]
        lines.append(
            f"\\quad {row['model']} ({row['effort']}) & "
            f"{row['non_timeout_runs']} & {row['avg_minutes_non_timeout']:.1f} & "
            f"{row['avg_input_tokens_m_non_timeout']:.1f}/{row['avg_output_tokens_k_non_timeout']:.0f} & "
            f"{profile['read']:.1f}/{profile['write']:.1f} & {profile['total']:.1f} & "
            f"{profile['coqc']:.1f}/{profile['vcg']:.1f} & {profile['rounds']:.1f}"
            + " " + "\\\\"
        )
    lines.append(r"\bottomrule")
    (ROOT / "tables" / "non_timeout_cost.tex").write_text(
        "\n".join(lines) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()
