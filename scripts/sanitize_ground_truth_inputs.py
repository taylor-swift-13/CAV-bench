#!/usr/bin/env python3
"""Derive non-leaking public inputs from DLC ground-truth artifacts."""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
GROUND_TRUTH = REPO / "ground_truth"
INPUT = REPO / "input" / "humaneval"
ANNOTATED = REPO / "annotated_input" / "humaneval"

QCP_BLOCK_RE = re.compile(r"/\*@(.*?)\*/", re.DOTALL)
CONTRACT_RE = re.compile(r"/\*@(.*?)\*/", re.DOTALL)
PROOF_START_RE = re.compile(
    r"^\s*(?:(?:Local|Global|Polymorphic|Program)\s+)*"
    r"(?:Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example)\b"
)
PROOF_END_RE = re.compile(r"\b(?:Qed|Defined|Admitted|Abort)\.\s*(?:\(\*.*\*\))?\s*$")
LTAC_START_RE = re.compile(r"^\s*Ltac\b")


def normalized_executable(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    text = re.sub(r"//.*", "", text)
    return re.sub(r"\s+", "", text)


def contracts(text: str) -> list[str]:
    return [
        re.sub(r"\s+", " ", body).strip()
        for body in CONTRACT_RE.findall(text)
        if re.search(r"\b(?:Require|Ensure)\b", body)
    ]


def public_c(full_text: str) -> str:
    def keep_or_remove(match: re.Match[str]) -> str:
        body = match.group(1)
        if re.search(r"\b(?:Extern|Import)\s+Coq\b", body):
            return match.group(0)
        if re.search(r"\b(?:Require|Ensure)\b", body):
            return match.group(0)
        return ""

    text = QCP_BLOCK_RE.sub(keep_or_remove, full_text)
    text = re.sub(r"[ \t]+\n", "\n", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.rstrip() + "\n"


def public_v(full_text: str) -> str:
    output: list[str] = []
    state = "copy"
    for line in full_text.splitlines():
        if state == "proof":
            if PROOF_END_RE.search(line):
                state = "copy"
            continue
        if state == "ltac":
            if line.strip().endswith("."):
                state = "copy"
            continue
        if PROOF_START_RE.match(line):
            state = "proof"
            if PROOF_END_RE.search(line):
                state = "copy"
            continue
        if LTAC_START_RE.match(line):
            state = "ltac"
            if line.strip().endswith("."):
                state = "copy"
            continue
        output.append(line)
    if state != "copy":
        raise RuntimeError(f"unterminated Coq {state} block")
    text = "\n".join(output)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.rstrip() + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--problem", action="append", help="Problem stem; repeatable")
    parser.add_argument("--all", action="store_true", help="Process every ground-truth case")
    parser.add_argument("--write", action="store_true", help="Apply changes (default: dry run)")
    args = parser.parse_args()

    if not args.problem and not args.all:
        parser.error("select at least one --problem, or pass --all explicitly")
    if args.problem and args.all:
        parser.error("--problem and --all are mutually exclusive")

    selected = set(args.problem or [])
    cases = sorted(path for path in GROUND_TRUTH.glob("p*") if path.is_dir())
    if selected:
        available = {path.name for path in cases}
        unknown = sorted(selected - available)
        if unknown:
            parser.error("unknown problem(s): " + ", ".join(unknown))
        cases = [path for path in cases if path.name in selected]

    report: list[dict[str, object]] = []
    for case in cases:
        stem = case.name
        full_c = (case / f"{stem}.c").read_text(encoding="utf-8", errors="replace")
        full_v = (case / f"{stem}.v").read_text(encoding="utf-8", errors="replace")
        stripped_c = public_c(full_c)
        stripped_v = public_v(full_v)
        if normalized_executable(stripped_c) != normalized_executable(full_c):
            raise RuntimeError(f"{stem}: sanitizing changes executable C")
        if contracts(stripped_c) != contracts(full_c):
            raise RuntimeError(f"{stem}: sanitizing changes contracts")
        if re.search(r"/\*@\s*(?:Inv|Assert)\b|\bwhich\s+implies\b|/\*@[^*]*\bwhere\b", stripped_c):
            raise RuntimeError(f"{stem}: answer-bearing C annotation survived")
        if re.search(
            r"^\s*(?:(?:Local|Global|Polymorphic|Program)\s+)*"
            r"(?:Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example|Ltac)\b|"
            r"\b(?:Qed|Admitted|Abort)\.",
            stripped_v,
            re.MULTILINE,
        ):
            raise RuntimeError(f"{stem}: proof command survived public V sanitization")

        desired = {
            INPUT / f"{stem}.c": stripped_c,
            INPUT / f"{stem}.v": stripped_v,
            ANNOTATED / f"{stem}.c": full_c.rstrip() + "\n",
            ANNOTATED / f"{stem}.v": stripped_v,
        }
        changed = [
            str(path.relative_to(REPO)) for path, text in desired.items()
            if not path.exists() or path.read_text(encoding="utf-8", errors="replace") != text
        ]
        if args.write:
            for path, text in desired.items():
                path.parent.mkdir(parents=True, exist_ok=True)
                if not path.exists() or path.read_text(encoding="utf-8", errors="replace") != text:
                    path.write_text(text, encoding="utf-8")
        report.append({"stem": stem, "changed": changed})
        print(f"[{ 'write' if args.write else 'dry-run' }] {stem}: {len(changed)} files")

    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
