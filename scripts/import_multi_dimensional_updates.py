#!/usr/bin/env python3
"""Safely refresh proved multi-dimensional HumanEval bundles in DLC.

Only the annotated C, case-local support module, and manual proof are imported
into ground truth. Public inputs are derived separately after fresh replay.
Generated goal/auto/goal-check files must be recreated by the validator before
a case is admitted. The script never deletes ground truth.
"""
from __future__ import annotations

import argparse
import json
import os
import re
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
SOURCE = Path(os.environ.get(
    "QCP_MULTI_SOURCE",
    "/home/yangfp/QualifiedCProgramming/QCP_examples/humaneval/multi_dimensional_arrays",
))
INPUT = REPO / "input" / "humaneval"
GROUND_TRUTH = REPO / "ground_truth"

# Candidates accepted by a fresh DLC symexec + five-stage Coq replay on
# 2026-07-12. Other source bundles remain opt-in until they pass the same gate.
DEFAULT_IDS = (1, 7, 14, 28, 29, 74, 101, 105, 112, 113, 117, 147, 149, 153, 158, 160)
STEM_OVERRIDES = {
    117: "p117_select_words",
    147: "p147_get_matrix_triples",
    149: "p149_sorted_list_sum",
    153: "p153_Strongest_Extension",
    160: "p160_do_algebra",
}

CONTRACT_RE = re.compile(r"/\*@(.*?)\*/", re.DOTALL)
FORBIDDEN_MANUAL_RE = re.compile(
    r"(?<![A-Za-z_])(Admitted|Abort|admit|give_up)(?![A-Za-z_])|"
    r"^\s*(Axiom|Hypothesis|Parameter|Conjecture)\b",
    re.MULTILINE,
)
FORBIDDEN_SUPPORT_RE = re.compile(
    r"(?<![A-Za-z_])(Admitted|Abort|admit|give_up)(?![A-Za-z_])|"
    r"^\s*Axiom\b",
    re.MULTILINE,
)


def normalized_executable(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    text = re.sub(r"//.*", "", text)
    return re.sub(r"\s+", "", text)


def contracts(text: str) -> list[str]:
    return [
        re.sub(r"\s+", " ", body).strip()
        for body in CONTRACT_RE.findall(text)
        if re.search(r"\bEnsure\b", body)
    ]


def clean_text(text: str) -> str:
    return "\n".join(line.rstrip() for line in text.splitlines()).rstrip() + "\n"


def remove_manual_lemmas(text: str, names: tuple[str, ...]) -> str:
    for name in names:
        pattern = re.compile(
            rf"^Lemma\s+{re.escape(name)}\b.*?^Qed\.\s*\n?",
            re.MULTILINE | re.DOTALL,
        )
        text, count = pattern.subn("", text, count=1)
        if count != 1:
            raise RuntimeError(f"expected exactly one manual lemma {name}")
    return text


def stem_for(number: int) -> str:
    if number in STEM_OVERRIDES:
        return STEM_OVERRIDES[number]
    matches = sorted(INPUT.glob(f"p{number:03d}_*.c"))
    if len(matches) != 1:
        raise RuntimeError(f"problem {number}: expected one DLC input, found {len(matches)}")
    return matches[0].stem


def rewrite_module_names(text: str, number: int, stem: str) -> str:
    text = re.sub(rf"\bcoins_{number}\b", stem, text)
    for suffix in ("goal", "proof_auto", "proof_manual", "goal_check"):
        text = re.sub(rf"\bC_{number}_{suffix}\b", f"{stem}_{suffix}", text)
    text = re.sub(rf"\bC_{number}\b", stem, text)

    generated = rf"{re.escape(stem)}_(?:goal|proof_auto|proof_manual)"
    pattern = re.compile(
        rf"^From\s+SimpleC\.EE\s+Require\s+Import\s+"
        rf"((?:{generated})(?:\s+{generated})*)\s*\.\s*$",
        re.MULTILINE,
    )
    text = pattern.sub(
        lambda match: (
            f"From SimpleC.EE.CAV.ground_truth_{stem} Require Import "
            f"{match.group(1)}."
        ),
        text,
    )
    text = re.sub(
        r"^Require Import (string_strategy_(?:goal|proof))\s*\.\s*$",
        r"From SimpleC.StdLib Require Import \1.",
        text,
        flags=re.MULTILINE,
    )
    return text


def support_text(number: int, stem: str) -> str:
    coins_path = SOURCE / f"coins_{number}.v"
    spec_path = SOURCE.parent / "spec" / f"{number}.v"
    coins = coins_path.read_text(encoding="utf-8", errors="replace")
    spec = spec_path.read_text(encoding="utf-8", errors="replace").rstrip()
    load = re.compile(rf'^\s*Load\s+"\.\./spec/{number}"\s*\.\s*$', re.MULTILINE)
    if not load.search(coins):
        raise RuntimeError(f"problem {number}: coins file does not load ../spec/{number}")
    text = rewrite_module_names(load.sub(spec, coins), number, stem)
    if number == 7 and "Definition substring_at" not in text:
        marker = "Local Open Scope Z_scope.\n"
        compatibility = """

(* Case-local compatibility with the source proof; DLC intentionally keeps the
   benchmark's pinned string library unchanged. *)
Definition substring_at (str sub : list Z) (i : Z) : Prop :=
  0 <= i <= string_length str /\\
  i + string_length sub <= string_length str /\\
  forall k, 0 <= k < string_length sub ->
    Znth (i + k) str 0 = Znth k sub 0.

Definition strstr_result (str sub : list Z) (ret s : Z) : Prop :=
  (exists i,
      substring_at str sub i /\\
      (forall k, 0 <= k < i -> ~ substring_at str sub k) /\\
      ret = s + i /\\
      ret <> 0) \/
  ((forall k, 0 <= k <= string_length str -> ~ substring_at str sub k) /\\
   ret = 0).
"""
        if marker not in text:
            raise RuntimeError(f"{stem}: cannot place string compatibility definitions")
        text = text.replace(marker, marker + compatibility, 1)
    if number == 112 and "Definition strchr_result" not in text:
        marker = "Local Open Scope Z_scope.\n"
        compatibility = """

(* Case-local compatibility with the source proof; DLC intentionally keeps the
   benchmark's pinned string library unchanged. *)
Definition strchr_result (str : list Z) (c ret s : Z) : Prop :=
  (exists i,
      0 <= i < string_length str /\\
      Znth i str 0 = c /\\
      (forall k, 0 <= k < i -> Znth k str 0 <> c) /\\
      ret = s + i /\\
      ret <> 0) \/
  ((forall k, 0 <= k < string_length str -> Znth k str 0 <> c) /\\
   ((c = 0 /\\ ret = s + string_length str) \/
    (c <> 0 /\\ ret = 0))).
"""
        if marker not in text:
            raise RuntimeError(f"{stem}: cannot place string compatibility definition")
        text = text.replace(marker, marker + compatibility, 1)
    return clean_text(text)


def desired_files(number: int) -> tuple[str, dict[Path, str]]:
    stem = stem_for(number)
    source_c = (SOURCE / f"C_{number}.c").read_text(encoding="utf-8", errors="replace")
    input_path = INPUT / f"{stem}.c"
    input_c = input_path.read_text(encoding="utf-8", errors="replace") if input_path.exists() else source_c
    manual = (SOURCE / f"C_{number}_proof_manual.v").read_text(
        encoding="utf-8", errors="replace"
    )
    support = support_text(number, stem)

    if input_path.exists() and normalized_executable(source_c) != normalized_executable(input_c):
        raise RuntimeError(f"{stem}: source changes executable C")
    if input_path.exists() and contracts(source_c) != contracts(input_c):
        raise RuntimeError(f"{stem}: source changes fixed function contracts")
    for label, text, pattern in (
        ("support", support, FORBIDDEN_SUPPORT_RE),
        ("manual", manual, FORBIDDEN_MANUAL_RE),
    ):
        match = pattern.search(text)
        if match:
            raise RuntimeError(f"{stem}: forbidden {match.group(0)!r} in source {label}")

    source_c = clean_text(rewrite_module_names(source_c, number, stem))
    manual = rewrite_module_names(manual, number, stem)
    if number == 112:
        manual = remove_manual_lemmas(
            manual,
            (
                "proof_of_reverse_delete_entail_wit_11",
                "proof_of_reverse_delete_entail_wit_12",
            ),
        )
    manual = clean_text(manual)
    case_dir = GROUND_TRUTH / stem
    return stem, {
        case_dir / f"{stem}.c": source_c,
        case_dir / f"{stem}.v": support,
        case_dir / f"{stem}_proof_manual.v": manual,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--problem", action="append", type=int, help="HumanEval number; repeatable")
    parser.add_argument("--write", action="store_true", help="Apply changes (default: dry run)")
    args = parser.parse_args()

    numbers = tuple(args.problem) if args.problem else DEFAULT_IDS
    report: list[dict[str, object]] = []
    errors = 0
    for number in numbers:
        try:
            stem, files = desired_files(number)
        except Exception as exc:
            errors += 1
            report.append({"number": number, "error": str(exc)})
            print(f"[skip] {number}: {exc}")
            continue
        changed = [str(path.relative_to(REPO)) for path, text in files.items()
                   if not path.exists() or path.read_text(encoding="utf-8", errors="replace") != text]
        if args.write:
            for path, text in files.items():
                path.parent.mkdir(parents=True, exist_ok=True)
                if not path.exists() or path.read_text(encoding="utf-8", errors="replace") != text:
                    path.write_text(text, encoding="utf-8")
        report.append({"number": number, "stem": stem, "changed": changed})
        print(f"[{ 'write' if args.write else 'dry-run' }] {stem}: {len(changed)} files")

    print(json.dumps(report, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
