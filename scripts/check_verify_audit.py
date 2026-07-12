#!/usr/bin/env python3
"""Unified verify artifact audit for source integrity and proof bypasses.

This checker is intended to run outside the agent-visible prompt. It is the
single automatic runner-side artifact audit used by ``run_verify.py`` and
``run_proof.py``.

It accepts one or more verify workspace/result directories and returns findings
grouped by audit class. A nonzero exit code means at least one error finding was
found, unless ``--no-fail`` is used.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
from typing import Any, Iterable


WORKSPACE_RE = re.compile(r"^verify_\d{8}_\d+_(?P<name>[A-Za-z0-9_]+)$")
STANDARD_GENERATED_RE = re.compile(r".*_(goal|proof_auto|proof_manual|goal_check)\.v$")
TARGET_GENERATED_SUFFIXES = ("goal", "proof_auto", "proof_manual", "goal_check")
SYEXEC_OWNED_SUFFIXES = ("goal", "proof_auto", "goal_check")

# Logical-path prefixes that legitimately appear in QCP manual proofs.
ALLOWED_IMPORT_PREFIXES: tuple[str, ...] = (
    "Coq.",
    "AUXLib",
    "SimpleC.",
    "compcert.lib",
    "SetsClass",
    "Logic",
    "FP",
    "MonadLib",
    "ListLib",
    "MaxMinLib",
    "GraphLib",
    "Permutation",
)

_BLOCK_RE = re.compile(r"/\*@(.*?)\*/", re.DOTALL)
_WS_RE = re.compile(r"\s+")
_IMPORT_RE = re.compile(r"^\s*(?:From\s+(\S+)\s+)?Require\s+(?:Import|Export)\s+(.+?)\.", re.MULTILINE)
_PROOF_STUB_RE = re.compile(r"(?<![A-Za-z_])(Admitted|Abort|admit|give_up)(?![A-Za-z_])")
_AXIOM_RE = re.compile(
    r"^\s*(Axiom|Hypothesis|Parameter|Parameters|Conjecture|Variable|Variables|Declare)\b",
    re.MULTILINE,
)


def _normalize(text: str) -> str:
    return _WS_RE.sub(" ", text).strip()


def extract_contract_specs(c_text: str) -> list[str]:
    """Normalized ``/*@ ... */`` contract blocks from a C source file."""
    specs: list[str] = []
    for body in _BLOCK_RE.findall(c_text):
        if re.search(r"\bEnsure\b", body):
            specs.append(_normalize(body))
    return specs


def scan_contract_weakening(original_c: str, verified_c: str) -> list[dict[str, Any]]:
    """Flag changes to the function contract between original and annotated C."""
    orig = extract_contract_specs(original_c)
    ver = extract_contract_specs(verified_c)
    if orig == ver:
        return []
    return [{
        "category": "contract_weakening",
        "severity": "error",
        "file": "verified",
        "line": 0,
        "snippet": (ver[0] if ver else "<no contract block in verified>")[:400],
        "message": (
            "Verified file's contract (With/Require/Ensure) differs from the "
            "original. Annotations may add Inv/Assert/which-implies but must not "
            "alter the contract. original_specs={} verified_specs={}".format(
                len(orig), len(ver))
        ),
    }]


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _scan_lines(
    text: str,
    file_label: str,
    pattern: re.Pattern[str],
    category: str,
    severity: str,
    message: str,
) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    for i, line in enumerate(text.splitlines(), start=1):
        if pattern.search(line):
            findings.append({
                "category": category,
                "severity": severity,
                "file": file_label,
                "line": i,
                "snippet": line.strip()[:400],
                "message": message,
            })
    return findings


def scan_proof_file(
    text: str,
    file_label: str,
    *,
    flag_stubs: bool = True,
    allowed_local_modules: set[str] | None = None,
) -> list[dict[str, Any]]:
    """Scan a manual proof file for stubs, axioms, and unusual imports."""
    findings: list[dict[str, Any]] = []
    if flag_stubs:
        findings += _scan_lines(
            text, file_label, _PROOF_STUB_RE, "proof_stub", "error",
            "proof_manual.v contains an admit/Admitted/Abort stub; a manual "
            "obligation was not actually discharged.",
        )
    for i, line in enumerate(text.splitlines(), start=1):
        if _AXIOM_RE.match(line):
            findings.append({
                "category": "manual_axiom",
                "severity": "error",
                "file": file_label,
                "line": i,
                "snippet": line.strip()[:400],
                "message": "Hand-written proof assumption assumes the goal instead of proving it.",
            })
    for match in _IMPORT_RE.finditer(text):
        origin = match.group(1)
        names = match.group(2)
        targets = [origin] if origin else names.split()
        for target in targets:
            if target in (allowed_local_modules or set()):
                continue
            if not any(target.startswith(prefix) or target == prefix.rstrip(".")
                       for prefix in ALLOWED_IMPORT_PREFIXES):
                line = text[: match.start()].count("\n") + 1
                findings.append({
                    "category": "forbidden_import",
                    "severity": "error",
                    "file": file_label,
                    "line": line,
                    "snippet": match.group(0).strip()[:400],
                    "message": f"Import `{target}` is outside the known QCP/Coq "
                               "library set; confirm it is not used to smuggle in "
                               "an assumption.",
                })
                break
    return findings


_C_MULTI_CHAR_TOKENS = tuple(sorted({
    "<<=", ">>=", "...", "->", "++", "--", "<<", ">>", "<=", ">=",
    "==", "!=", "&&", "||", "+=", "-=", "*=", "/=", "%=", "&=", "|=",
    "^=", "##", "::",
}, key=len, reverse=True))


def _c_tokens_without_comments(text: str) -> list[str]:
    """Lex C conservatively while dropping comments and layout.

    Unlike a comment-stripping regex, this keeps comment-looking text inside
    string and character literals and preserves token boundaries.  The audit
    therefore cannot hide an executable edit by merging identifiers across
    whitespace or by placing ``//``/``/*`` inside a literal.
    """
    tokens: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if ch.isspace():
            i += 1
            continue
        if text.startswith("//", i):
            newline = text.find("\n", i + 2)
            i = n if newline < 0 else newline + 1
            continue
        if text.startswith("/*", i):
            end = text.find("*/", i + 2)
            if end < 0:
                tokens.append("<unterminated-comment>")
                break
            i = end + 2
            continue
        if ch in {'"', "'"}:
            quote = ch
            start = i
            i += 1
            while i < n:
                if text[i] == "\\":
                    i += 2
                    continue
                if text[i] == quote:
                    i += 1
                    break
                i += 1
            else:
                tokens.append("<unterminated-literal>")
            tokens.append(text[start:i])
            continue
        if ch.isalpha() or ch == "_":
            start = i
            i += 1
            while i < n and (text[i].isalnum() or text[i] == "_"):
                i += 1
            tokens.append(text[start:i])
            continue
        if ch.isdigit() or (ch == "." and i + 1 < n and text[i + 1].isdigit()):
            start = i
            i += 1
            while i < n:
                cur = text[i]
                if cur.isalnum() or cur in "._":
                    i += 1
                    continue
                if cur in "+-" and i > start and text[i - 1] in "eEpP":
                    i += 1
                    continue
                break
            tokens.append(text[start:i])
            continue
        matched = next((op for op in _C_MULTI_CHAR_TOKENS if text.startswith(op, i)), None)
        if matched is not None:
            tokens.append(matched)
            i += len(matched)
            continue
        tokens.append(ch)
        i += 1
    return tokens


def normalize_c_without_annotations(text: str) -> str:
    return "\x1f".join(_c_tokens_without_comments(text))


def infer_case_name(workspace: Path) -> str:
    match = WORKSPACE_RE.match(workspace.name)
    if match:
        return match.group("name")
    return workspace.name


def finding(
    *,
    case: str,
    group: str,
    category: str,
    severity: str,
    file: str,
    line: int = 0,
    snippet: str = "",
    message: str,
) -> dict[str, Any]:
    return {
        "case": case,
        "group": group,
        "category": category,
        "severity": severity,
        "file": file,
        "line": line,
        "snippet": re.sub(r"\s+", " ", snippet).strip()[:700],
        "message": message,
    }


def one_or_none(paths: Iterable[Path]) -> Path | None:
    paths = sorted(paths)
    if len(paths) == 1:
        return paths[0]
    return None


def original_c_path(workspace: Path, case: str) -> Path | None:
    preferred = workspace / "original" / f"{case}.c"
    if preferred.exists():
        return preferred
    return one_or_none((workspace / "original").glob("*.c"))


def verified_c_path(workspace: Path) -> Path | None:
    annotated_dir = workspace / "annotated"
    preferred = annotated_dir / f"{workspace.name}.c"
    if preferred.exists():
        return preferred
    return one_or_none(annotated_dir.glob("*.c"))


def generated_dir(workspace: Path) -> Path:
    return workspace / "coq" / "generated"


def infer_generated_stem(gendir: Path, case: str) -> str:
    preferred = gendir / f"{case}_proof_manual.v"
    if preferred.exists():
        return case
    manuals = sorted(gendir.glob("*_proof_manual.v"))
    if len(manuals) == 1:
        return manuals[0].name[:-len("_proof_manual.v")]
    return case


def normalized_generated_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace").replace("\r\n", "\n")


def agent_writable_proof_files(workspace: Path) -> list[Path]:
    """Return manual proofs and non-standard helper files written in the case.

    Symexec-owned goal/auto/check files legitimately declare obligation axioms
    and are protected by the freshness check, so they are excluded.  Every
    other collected Coq file can influence a manual proof and must be scanned.
    """
    gendir = generated_dir(workspace)
    if not gendir.exists():
        return []
    files: list[Path] = []
    for path in sorted(gendir.glob("*.v")):
        if path.name.endswith(("_goal.v", "_proof_auto.v", "_goal_check.v")):
            continue
        files.append(path)
    return files


def normalize_qcp_finding(raw: dict[str, Any], *, case: str) -> dict[str, Any]:
    category = str(raw.get("category", "proof_artifact"))
    if category in {"proof_stub", "manual_axiom"}:
        group = "proof_bypass"
    elif category == "contract_weakening":
        group = "source_integrity"
    elif category == "forbidden_import":
        group = "import_review"
    else:
        group = "proof_artifact"
    return finding(
        case=case,
        group=group,
        category=category,
        severity=str(raw.get("severity", "error")),
        file=str(raw.get("file", "")),
        line=int(raw.get("line", 0) or 0),
        snippet=str(raw.get("snippet", "")),
        message=str(raw.get("message", "")),
    )


def scan_runner_inputs(
    workspace: Path,
    case: str,
    *,
    input_path: Path | None = None,
    input_v_path: Path | None = None,
) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    if input_path is not None:
        original = workspace / "original" / input_path.name
        if not original.exists():
            findings.append(finding(
                case=case,
                group="artifact_shape",
                category="missing_bootstrap_original_c",
                severity="error",
                file=str(original),
                message="Runner input C was not preserved in workspace/original.",
            ))
        elif input_path.exists() and file_sha256(original) != file_sha256(input_path):
            findings.append(finding(
                case=case,
                group="source_integrity",
                category="input_c_changed_after_bootstrap",
                severity="error",
                file=str(input_path),
                message="Runner input C differs from the workspace bootstrap copy.",
            ))
    if input_v_path is not None:
        original_v = workspace / "original" / input_v_path.name
        if not original_v.exists():
            findings.append(finding(
                case=case,
                group="artifact_shape",
                category="missing_bootstrap_original_v",
                severity="error",
                file=str(original_v),
                message="Runner input V was not preserved in workspace/original.",
            ))
        elif input_v_path.exists() and file_sha256(original_v) != file_sha256(input_v_path):
            findings.append(finding(
                case=case,
                group="source_integrity",
                category="input_v_changed_after_bootstrap",
                severity="error",
                file=str(input_v_path),
                message="Runner input V differs from the workspace bootstrap copy.",
            ))
    return findings


def scan_source_artifacts(
    workspace: Path,
    case: str,
    *,
    annotated_c_path: Path | None = None,
) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    original = original_c_path(workspace, case)
    verified = annotated_c_path if annotated_c_path is not None else verified_c_path(workspace)

    if original is None:
        findings.append(finding(
            case=case,
            group="artifact_shape",
            category="missing_original_c",
            severity="error",
            file=str(workspace / "original"),
            message="Missing unique original C artifact.",
        ))
    if verified is None or not verified.exists():
        findings.append(finding(
            case=case,
            group="artifact_shape",
            category="missing_verified_c",
            severity="error",
            file=str(verified if verified is not None else workspace / "annotated"),
            message="Missing unique verified/annotated C artifact.",
        ))

    if original is None or verified is None or not verified.exists():
        return findings

    original_text = original.read_text(encoding="utf-8", errors="replace")
    verified_text = verified.read_text(encoding="utf-8", errors="replace")
    for raw in scan_contract_weakening(original_text, verified_text):
        findings.append(normalize_qcp_finding(raw, case=case))

    if normalize_c_without_annotations(original_text) != normalize_c_without_annotations(verified_text):
        findings.append(finding(
            case=case,
            group="source_integrity",
            category="executable_c_changed",
            severity="error",
            file=str(verified),
            message="Verified C changes executable code after removing comments/QCP annotations.",
        ))

    return findings


def scan_proof_artifacts(workspace: Path, case: str) -> list[dict[str, Any]]:
    findings: list[dict[str, Any]] = []
    gendir = generated_dir(workspace)
    if not gendir.exists():
        return [finding(
            case=case,
            group="artifact_shape",
            category="missing_generated_dir",
            severity="error",
            file=str(gendir),
            message="Missing generated Coq artifact directory.",
        )]

    stem = infer_generated_stem(gendir, case)
    for suffix in TARGET_GENERATED_SUFFIXES:
        if (gendir / f"{stem}_{suffix}.v").exists():
            continue
        findings.append(finding(
            case=case,
            group="artifact_shape",
            category="missing_target_generated_artifact",
            severity="error",
            file=str(gendir / f"{stem}_{suffix}.v"),
            message=f"Missing unique target generated artifact for suffix {suffix}.",
        ))

    allowed_local_modules = {
        path.stem for path in (workspace / "original").glob("*.v")
    } | {
        path.stem for path in gendir.glob("*.v")
    }
    for path in agent_writable_proof_files(workspace):
        text = path.read_text(encoding="utf-8", errors="replace")
        for raw in scan_proof_file(
            text,
            path.name,
            flag_stubs=True,
            allowed_local_modules=allowed_local_modules,
        ):
            normalized = normalize_qcp_finding(raw, case=case)
            normalized["file"] = str(path)
            findings.append(normalized)

    return findings


def scan_generated_freshness(
    submitted_dir: Path,
    fresh_dir: Path,
    *,
    case: str,
    function_name: str | None = None,
) -> list[dict[str, Any]]:
    """Compare symexec-owned target artifacts against a fresh symexec run.

    ``proof_manual.v`` is deliberately excluded because it is the manual proof
    file. The other target files must be the runner-generated output for the
    final annotated C, not hand-edited artifacts.
    """
    findings: list[dict[str, Any]] = []
    stem = function_name or case
    for suffix in SYEXEC_OWNED_SUFFIXES:
        submitted = submitted_dir / f"{stem}_{suffix}.v"
        fresh = fresh_dir / f"{stem}_{suffix}.v"
        if not submitted.exists():
            findings.append(finding(
                case=case,
                group="generated_freshness",
                category="missing_submitted_generated_artifact",
                severity="error",
                file=str(submitted),
                message=f"Missing submitted symexec-owned artifact {submitted.name}.",
            ))
            continue
        if not fresh.exists():
            findings.append(finding(
                case=case,
                group="generated_freshness",
                category="missing_fresh_generated_artifact",
                severity="error",
                file=str(fresh),
                message=f"Fresh symexec did not produce expected artifact {fresh.name}.",
            ))
            continue
        if normalized_generated_text(submitted) != normalized_generated_text(fresh):
            findings.append(finding(
                case=case,
                group="generated_freshness",
                category="modified_symexec_owned_artifact",
                severity="error",
                file=str(submitted),
                message=(
                    f"{submitted.name} differs from fresh symexec output for the final "
                    "annotated C. Only the manual proof artifact may contain manual edits."
                ),
            ))
    return findings


def audit_inputs(
    *,
    input_path: Path | None = None,
    input_v_path: Path | None = None,
    annotated_c_path: Path | None = None,
) -> dict[str, str | None]:
    return {
        "input_c": str(input_path.resolve()) if input_path is not None else None,
        "input_v": str(input_v_path.resolve()) if input_v_path is not None else None,
        "annotated_c": str(annotated_c_path.resolve()) if annotated_c_path is not None else None,
    }


def scan_workspace(
    workspace: Path,
    *,
    input_path: Path | None = None,
    input_v_path: Path | None = None,
    annotated_c_path: Path | None = None,
) -> dict[str, Any]:
    workspace = workspace.resolve()
    case = infer_case_name(workspace)
    findings: list[dict[str, Any]] = []
    findings.extend(scan_runner_inputs(
        workspace,
        case,
        input_path=input_path,
        input_v_path=input_v_path,
    ))
    findings.extend(scan_source_artifacts(workspace, case, annotated_c_path=annotated_c_path))
    findings.extend(scan_proof_artifacts(workspace, case))
    summary = summarize(findings)
    return {
        "ok": summary["errors"] == 0,
        "workspace": str(workspace),
        "case": case,
        "inputs": audit_inputs(
            input_path=input_path,
            input_v_path=input_v_path,
            annotated_c_path=annotated_c_path,
        ),
        "summary": summary,
        "findings": findings,
    }


def discover_workspaces(paths: Iterable[Path]) -> list[Path]:
    workspaces: set[Path] = set()
    for path in paths:
        if path.is_file():
            continue
        if not path.is_dir():
            continue
        if WORKSPACE_RE.match(path.name) and ((path / "logs").exists() or (path / "coq").exists()):
            workspaces.add(path)
            continue
        for candidate in path.glob("verify_*"):
            if candidate.is_dir() and WORKSPACE_RE.match(candidate.name):
                workspaces.add(candidate)
    return sorted(workspaces)


def summarize(findings: list[dict[str, Any]]) -> dict[str, Any]:
    errors = [f for f in findings if f.get("severity") == "error"]
    warnings = [f for f in findings if f.get("severity") == "warning"]
    by_group: dict[str, int] = {}
    by_category: dict[str, int] = {}
    for item in findings:
        by_group[str(item.get("group", "?"))] = by_group.get(str(item.get("group", "?")), 0) + 1
        by_category[str(item.get("category", "?"))] = by_category.get(str(item.get("category", "?")), 0) + 1
    return {
        "findings": len(findings),
        "errors": len(errors),
        "warnings": len(warnings),
        "groups": dict(sorted(by_group.items())),
        "categories": dict(sorted(by_category.items())),
        "ok": len(errors) == 0,
    }


def aggregate(results: list[dict[str, Any]]) -> dict[str, Any]:
    findings = [finding for result in results for finding in result["findings"]]
    summary = summarize(findings)
    summary["workspaces"] = len(results)
    summary["ok_workspaces"] = sum(1 for result in results if result["summary"]["ok"])
    return summary


def print_text(results: list[dict[str, Any]]) -> None:
    summary = aggregate(results)
    print(
        "Unified verify audit: "
        f"workspaces={summary['workspaces']} findings={summary['findings']} "
        f"errors={summary['errors']} warnings={summary['warnings']} "
        f"clean={summary['errors'] == 0}"
    )
    if summary["groups"]:
        print("Groups:")
        for group, count in summary["groups"].items():
            print(f"- {group}: {count}")
    for result in results:
        if not result["findings"]:
            continue
        print(f"\n## {result['case']}")
        for item in result["findings"]:
            print(
                f"- {item['severity']} {item['group']}/{item['category']} "
                f"{item['file']}:{item['line']}\n"
                f"  {item['message']}\n"
                f"  {item['snippet']}"
            )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Unified verify artifact anti-cheating audit.")
    parser.add_argument("paths", nargs="+", help="Verify workspace/result directories.")
    parser.add_argument(
        "--fresh-generated",
        help="Optional fresh symexec generated directory to compare against one workspace's submitted artifacts.",
    )
    parser.add_argument("--function-name", help="Target function stem for --fresh-generated comparison.")
    parser.add_argument("--json", action="store_true", help="Emit JSON.")
    parser.add_argument("--no-fail", action="store_true", help="Always exit 0.")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    workspaces = discover_workspaces([Path(p) for p in args.paths])
    if args.fresh_generated and len(workspaces) != 1:
        raise SystemExit("--fresh-generated requires exactly one discovered workspace")
    results = [scan_workspace(path) for path in workspaces]
    if args.fresh_generated:
        result = results[0]
        case = result["case"]
        fresh_findings = scan_generated_freshness(
            generated_dir(Path(result["workspace"])),
            Path(args.fresh_generated),
            case=case,
            function_name=args.function_name or case,
        )
        result["findings"].extend(fresh_findings)
        result["summary"] = summarize(result["findings"])
        result["ok"] = result["summary"]["ok"]
    summary = aggregate(results)
    if args.json:
        json.dump({"summary": summary, "results": results}, sys.stdout, indent=2, ensure_ascii=False)
        sys.stdout.write("\n")
    else:
        print_text(results)
    if args.no_fail:
        return 0
    return 1 if summary["errors"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
