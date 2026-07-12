#!/usr/bin/env python3
"""Move task-local Coq proofs from companion specs into proof_manual files.

For every ground-truth HumanEval case, the canonical companion ``<name>.v``
must be definition-only.  This script extracts top-level theorem/proof and Ltac
commands, inserts them near the top of ``<name>_proof_manual.v``, and then makes
the ground-truth, primary-input, and annotated-input companion ``.v`` files
byte-identical.

The default is a dry run.  Pass ``--write`` to apply the migration.
"""
from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
GROUND_TRUTH = REPO / "ground_truth"
INPUT = REPO / "input" / "humaneval"
ANNOTATED_INPUT = REPO / "annotated_input" / "humaneval"

BEGIN_MARKER = "(* BEGIN migrated companion-spec proofs *)"
END_MARKER = "(* END migrated companion-spec proofs *)"

ATTRIBUTE_PREFIX = r"(?:#\[[^\]]*\]\s*)*"
QUALIFIER_PREFIX = r"(?:(?:Local|Global|Polymorphic|Program)\s+)*"
THEOREM_RE = re.compile(
    rf"^\s*{ATTRIBUTE_PREFIX}{QUALIFIER_PREFIX}"
    r"(Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example|Goal)\b"
)
THEOREM_NAME_RE = re.compile(
    rf"^\s*{ATTRIBUTE_PREFIX}{QUALIFIER_PREFIX}"
    r"(?:Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example)\s+([A-Za-z0-9_']+)\b"
)
LTAC_RE = re.compile(
    rf"^\s*{ATTRIBUTE_PREFIX}(?:Local\s+|Global\s+)?"
    r"(?:Ltac|Tactic\s+Notation)\b"
)
PROOF_ENV_RE = re.compile(
    r"^\s*(?:Import|Export)\b|"
    r"^\s*(?:(?:Local|Global)\s+)?(?:Open|Close)\s+Scope\b|"
    r"^\s*(?:Set|Unset)\b"
)
PROOF_END_RE = re.compile(r"^\s*(?:Qed|Defined|Admitted|Abort|Save\b[^.]*)\s*\.\s*$")
FORBIDDEN_RE = re.compile(
    rf"^\s*{ATTRIBUTE_PREFIX}{QUALIFIER_PREFIX}"
    r"(?:Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example|Goal|Ltac|Tactic\s+Notation|"
    r"Proof|Qed|Defined|Admitted|Abort)\b",
    re.MULTILINE,
)
ASSUMPTION_RE = re.compile(
    rf"^\s*{ATTRIBUTE_PREFIX}{QUALIFIER_PREFIX}"
    r"(?:Axiom|Axioms|Hypothesis|Hypotheses|Parameter|Parameters|Conjecture|"
    r"Variable|Variables|Declare)\b",
    re.MULTILINE,
)


@dataclass(frozen=True)
class SplitResult:
    definitions: str
    proofs: str
    theorem_names: tuple[str, ...]
    proof_commands: int


def mask_comments(text: str) -> str:
    """Replace nested Coq comments with spaces while preserving newlines."""
    output: list[str] = []
    depth = 0
    in_string = False
    i = 0
    while i < len(text):
        if depth:
            if text.startswith("(*", i):
                depth += 1
                output.extend("  ")
                i += 2
                continue
            if text.startswith("*)", i):
                depth -= 1
                output.extend("  ")
                i += 2
                continue
            output.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue
        if not in_string and text.startswith("(*", i):
            depth = 1
            output.extend("  ")
            i += 2
            continue
        char = text[i]
        if char == '"':
            if in_string and i + 1 < len(text) and text[i + 1] == '"':
                output.extend('""')
                i += 2
                continue
            in_string = not in_string
        output.append(char)
        i += 1
    if depth:
        raise RuntimeError("unterminated Coq comment")
    if in_string:
        raise RuntimeError("unterminated Coq string")
    return "".join(output)


def command_segments(text: str) -> list[str]:
    """Split Coq text at vernacular/tactic terminators, retaining formatting."""
    segments: list[str] = []
    start = 0
    depth = 0
    in_string = False
    i = 0
    while i < len(text):
        if depth:
            if text.startswith("(*", i):
                depth += 1
                i += 2
                continue
            if text.startswith("*)", i):
                depth -= 1
                i += 2
                continue
            i += 1
            continue
        if not in_string and text.startswith("(*", i):
            depth = 1
            i += 2
            continue
        char = text[i]
        if char == '"':
            if in_string and i + 1 < len(text) and text[i + 1] == '"':
                i += 2
                continue
            in_string = not in_string
            i += 1
            continue
        if char == "." and not in_string:
            next_char = text[i + 1] if i + 1 < len(text) else ""
            if not next_char or next_char.isspace() or text.startswith("(*", i + 1):
                segments.append(text[start : i + 1])
                start = i + 1
        i += 1
    if depth:
        raise RuntimeError("unterminated Coq comment")
    if in_string:
        raise RuntimeError("unterminated Coq string")
    if start < len(text):
        segments.append(text[start:])
    return segments


def command_code(segment: str) -> str:
    return mask_comments(segment).strip()


def split_proofs(text: str) -> SplitResult:
    definitions: list[str] = []
    proofs: list[str] = []
    proof_environment: list[str] = []
    theorem_names: list[str] = []
    in_proof = False
    proofs_started = False
    proof_commands = 0

    def start_proof_output() -> None:
        nonlocal proofs_started
        if proofs_started:
            return
        proofs_started = True
        if proof_environment:
            proofs.append("\n".join(proof_environment).rstrip() + "\n\n")

    for segment in command_segments(text):
        code = command_code(segment)
        if in_proof:
            proofs.append(segment)
            proof_commands += 1
            if PROOF_END_RE.match(code):
                in_proof = False
            continue

        theorem = THEOREM_RE.match(code)
        if theorem:
            start_proof_output()
            proofs.append(segment)
            proof_commands += 1
            name_match = THEOREM_NAME_RE.match(code)
            if name_match:
                theorem_names.append(name_match.group(1))
            # Companion specs use ordinary theorem blocks.  A ``:=`` can occur
            # inside the proposition itself (for example in a ``let``), so it
            # is not a sound signal for an inline proof term.
            in_proof = True
            continue

        if LTAC_RE.match(code):
            start_proof_output()
            proofs.append(segment)
            proof_commands += 1
            continue

        definitions.append(segment)
        if PROOF_ENV_RE.match(code):
            # Scope/import commands are retained in the definition file and
            # replayed in proof_manual.  Keeping their original position among
            # proof blocks avoids notation drift (notably list-vs-set, nat-vs-Z,
            # and bool scopes) after moving proofs to another compilation unit.
            if proofs_started:
                proofs.append("\n" + code + "\n")
            else:
                proof_environment.append(code)

    if in_proof:
        raise RuntimeError("unterminated theorem proof")

    definition_text = "".join(definitions).rstrip() + "\n"
    proof_text = "".join(proofs).strip()
    if proof_text:
        proof_text += "\n"
    return SplitResult(
        definitions=definition_text,
        proofs=proof_text,
        theorem_names=tuple(theorem_names),
        proof_commands=proof_commands,
    )


def insert_into_manual(manual: str, proofs: str) -> str:
    if not proofs:
        return manual.rstrip() + "\n"
    if BEGIN_MARKER in manual or END_MARKER in manual:
        raise RuntimeError("manual file already contains migration markers")
    anchor = "Local Open Scope sac."
    index = manual.find(anchor)
    if index < 0:
        raise RuntimeError(f"manual insertion anchor not found: {anchor}")
    index += len(anchor)
    block = (
        f"\n\n{BEGIN_MARKER}\n"
        "Module MigratedCompanionProofs.\n"
        "Local Open Scope bool_scope.\n"
        f"{proofs.rstrip()}\n"
        "End MigratedCompanionProofs.\n"
        "Export MigratedCompanionProofs.\n"
        f"{END_MARKER}"
    )
    return (manual[:index] + block + manual[index:]).rstrip() + "\n"


def referenced_before_manual(case: Path, names: tuple[str, ...]) -> list[str]:
    references: list[str] = []
    for suffix in ("goal", "proof_auto"):
        path = case / f"{case.name}_{suffix}.v"
        text = mask_comments(path.read_text(encoding="utf-8", errors="replace"))
        for name in names:
            if re.search(rf"\b{re.escape(name)}\b", text):
                references.append(f"{path.name}:{name}")
    return references


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--problem", action="append", help="Problem stem; repeatable")
    parser.add_argument("--all", action="store_true", help="Process all ground-truth cases")
    parser.add_argument("--write", action="store_true", help="Apply changes")
    args = parser.parse_args()
    if not args.problem and not args.all:
        parser.error("select at least one --problem, or use --all")
    if args.problem and args.all:
        parser.error("--problem and --all are mutually exclusive")

    cases = sorted(path for path in GROUND_TRUTH.iterdir() if path.is_dir())
    if args.problem:
        selected = set(args.problem)
        available = {path.name for path in cases}
        unknown = sorted(selected - available)
        if unknown:
            parser.error("unknown problem(s): " + ", ".join(unknown))
        cases = [path for path in cases if path.name in selected]

    report: list[dict[str, object]] = []
    for case in cases:
        stem = case.name
        spec_path = case / f"{stem}.v"
        manual_path = case / f"{stem}_proof_manual.v"
        spec = spec_path.read_text(encoding="utf-8", errors="replace")
        manual = manual_path.read_text(encoding="utf-8", errors="replace")
        split = split_proofs(spec)
        if FORBIDDEN_RE.search(mask_comments(split.definitions)):
            raise RuntimeError(f"{stem}: proof command remains in definition-only .v")
        masked_definitions = mask_comments(split.definitions)
        assumptions = ASSUMPTION_RE.findall(masked_definitions)
        if assumptions:
            # QCP's generated global-string model names the linker-provided
            # literal-address map as this one declaration.  It is not a proof
            # or task-specific semantic assumption; reject every other stub.
            commands = [
                command_code(segment)
                for segment in command_segments(split.definitions)
                if ASSUMPTION_RE.match(command_code(segment))
            ]
            if commands != ["Parameter LitMap : string -> addr."]:
                raise RuntimeError(
                    f"{stem}: unsupported assumption command(s) remain: {commands}"
                )
        early_refs = referenced_before_manual(case, split.theorem_names)
        if early_refs:
            raise RuntimeError(
                f"{stem}: generated files reference proofs before proof_manual: "
                + ", ".join(early_refs)
            )
        migrated_manual = insert_into_manual(manual, split.proofs)
        desired = {
            spec_path: split.definitions,
            INPUT / f"{stem}.v": split.definitions,
            ANNOTATED_INPUT / f"{stem}.v": split.definitions,
            manual_path: migrated_manual,
        }
        changed = [
            str(path.relative_to(REPO))
            for path, content in desired.items()
            if not path.exists()
            or path.read_text(encoding="utf-8", errors="replace") != content
        ]
        if args.write:
            for path, content in desired.items():
                path.parent.mkdir(parents=True, exist_ok=True)
                if not path.exists() or path.read_text(
                    encoding="utf-8", errors="replace"
                ) != content:
                    path.write_text(content, encoding="utf-8")
        entry = {
            "stem": stem,
            "proof_commands": split.proof_commands,
            "theorems": len(split.theorem_names),
            "changed": changed,
        }
        report.append(entry)
        print(
            f"[{'write' if args.write else 'dry-run'}] {stem}: "
            f"proof_commands={split.proof_commands} theorems={len(split.theorem_names)} "
            f"changed={len(changed)}"
        )

    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
