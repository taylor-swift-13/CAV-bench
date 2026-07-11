#!/usr/bin/env python3
"""Verify ground_truth humaneval cases by rerunning symexec and coqc.

For each ground_truth/<problem>, this stages the aligned C into the local QCP
mirror, reruns symexec to regenerate goal/proof_auto/goal_check, replaces
proof_manual with the migrated proof, then compiles case-local support, goal,
proof_auto, proof_manual, and goal_check. Ground-truth cases do not use deps
directories; required support must be inlined into case-local .v files.
"""
from __future__ import annotations

from pathlib import Path
import argparse
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import time


REPO = Path(__file__).resolve().parents[2]
GROUND_TRUTH = REPO / "ground_truth"
INPUT = REPO / "input" / "humaneval"
QCP_ROOT = Path(os.environ.get("QCP_ROOT", str(REPO / "QualifiedCProgramming")))
QCP_INPUT_ROOT = QCP_ROOT / "QCP_examples" / "CAV"
QCP_COQ_ROOT = QCP_ROOT / "SeparationLogic" / "examples" / "CAV"
STRATEGY_SOURCE_PATH = os.environ.get("QCP_STRATEGY_SOURCE_PATH", "QCP_examples/QCP_demos_LLM/")
STRATEGY_COQ_PATH = os.environ.get("QCP_STRATEGY_COQ_PATH", "SimpleC.EE.QCP_demos_LLM")
STDLIB_SOURCE_PATH = os.environ.get("QCP_STDLIB_SOURCE_PATH", "QCP_examples/stdlib/")
STDLIB_COQ_PATH = os.environ.get("QCP_STDLIB_COQ_PATH", "SimpleC.StdLib")
COQC_COMMAND = shlex.split(os.environ.get("COQC", "coqc"))
SYMEXEC_COMMAND = shlex.split(os.environ.get(
    "SYMEXEC", str(QCP_ROOT / "linux-binary" / "symexec")
))

LOCAL_REQ_RE = re.compile(r"^\s*Require\s+(?:Import|Export)\s+([A-Za-z0-9_ ]+)\s*\.", re.M)
LOCAL_FROM_REQ_RE = re.compile(r"^\s*From\s+[A-Za-z0-9_.]+\s+Require\s+(?:Import|Export)\s+([A-Za-z0-9_ ]+)\s*\.", re.M)
STRATEGY_REQ_RE = re.compile(
    rf"^\s*From\s+{re.escape(STRATEGY_COQ_PATH)}\s+Require\s+(?:Import|Export)\s+([A-Za-z0-9_ ]+)\s*\.",
    re.M,
)
OBLIGATION_RE = re.compile(r"\b(Admitted|admit|Abort|Axiom)\b")


def coq_common_args(workspace: str, deps_flag: list[str] | None = None) -> list[str]:
    args: list[str] = []
    if deps_flag:
        args.extend(deps_flag)
    args.extend(
        [
            "-R",
            str(QCP_ROOT / "SeparationLogic" / "SeparationLogic"),
            "SimpleC.SL",
            "-R",
            str(QCP_ROOT / "SeparationLogic" / "unifysl"),
            "Logic",
            "-R",
            str(QCP_ROOT / "SeparationLogic" / "sets"),
            "SetsClass",
            "-R",
            str(QCP_ROOT / "SeparationLogic" / "compcert_lib"),
            "compcert.lib",
            "-R",
            str(QCP_ROOT / "SeparationLogic" / "auxlibs"),
            "AUXLib",
            "-R",
            str(QCP_ROOT / "SeparationLogic" / "examples"),
            "SimpleC.EE",
            "-R",
            str(QCP_ROOT / "SeparationLogic" / "stdlib"),
            "SimpleC.StdLib",
            "-R",
            str(QCP_ROOT / "SeparationLogic" / "StrategyLib"),
            "SimpleC.StrategyLib",
            "-R",
            str(QCP_ROOT / "SeparationLogic" / "Common"),
            "SimpleC.Common",
            "-R",
            str(QCP_ROOT / "SeparationLogic" / "fixedpoints"),
            "FP",
            "-R",
            str(QCP_ROOT / "SeparationLogic" / "MonadLib"),
            "MonadLib",
            "-R",
            str(QCP_ROOT / "SeparationLogic" / "listlib"),
            "ListLib",
            "-R",
            str(QCP_COQ_ROOT / workspace),
            f"SimpleC.EE.CAV.{workspace}",
        ]
    )
    return args


def run(cmd: list[str], *, cwd: Path, timeout: int, log: list[str]) -> int:
    start = time.time()
    log.append("$ " + " ".join(cmd))
    try:
        proc = subprocess.run(
            cmd,
            cwd=cwd,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        log.append(f"TIMEOUT after {timeout}s")
        if exc.stdout:
            log.append(exc.stdout if isinstance(exc.stdout, str) else exc.stdout.decode(errors="replace"))
        return 124
    log.append(f"rc={proc.returncode} elapsed={time.time() - start:.2f}s")
    if proc.stdout:
        log.append(proc.stdout)
    return proc.returncode


def copy_headers(target: Path) -> None:
    target.mkdir(parents=True, exist_ok=True)
    for source in sorted(INPUT.glob("*.h")):
        shutil.copy2(source, target / source.name)


def stage_case(case_dir: Path, workspace: str) -> tuple[Path, Path]:
    stem = case_dir.name
    qcp_input = QCP_INPUT_ROOT / workspace
    qcp_coq = QCP_COQ_ROOT / workspace
    spec_dir = qcp_coq / "spec"
    for path in (qcp_input, qcp_coq):
        if path.exists():
            shutil.rmtree(path)
    qcp_input.mkdir(parents=True)
    spec_dir.mkdir(parents=True)

    shutil.copy2(case_dir / f"{stem}.c", qcp_input / f"{stem}.c")
    copy_headers(qcp_input)

    for source in sorted(INPUT.glob("*.v")):
        shutil.copy2(source, qcp_coq / source.name)

    for source in sorted(case_dir.glob("*.v")):
        if source.name not in {
            f"{stem}_goal.v",
            f"{stem}_proof_auto.v",
            f"{stem}_proof_manual.v",
            f"{stem}_goal_check.v",
        }:
            shutil.copy2(source, qcp_coq / source.name)

    return qcp_input, qcp_coq


def local_dep_order(deps_dir: Path) -> list[Path]:
    order: list[Path] = []
    seen: set[Path] = set()

    def visit(path: Path) -> None:
        resolved = path.resolve()
        if resolved in seen or not path.exists():
            return
        seen.add(resolved)
        text = path.read_text(encoding="utf-8", errors="replace")
        for group in LOCAL_REQ_RE.findall(text) + LOCAL_FROM_REQ_RE.findall(text):
            for module in group.split():
                local = deps_dir / f"{module}.v"
                if local.exists():
                    visit(local)
        order.append(path)

    for path in sorted(deps_dir.glob("*.v")):
        visit(path)
    return order


def support_dep_order(root: Path, generated_stem: str) -> list[Path]:
    generated = {
        f"{generated_stem}_goal.v",
        f"{generated_stem}_proof_auto.v",
        f"{generated_stem}_proof_manual.v",
        f"{generated_stem}_goal_check.v",
    }
    order: list[Path] = []
    seen: set[Path] = set()

    def visit(path: Path) -> None:
        resolved = path.resolve()
        if resolved in seen or not path.exists():
            return
        seen.add(resolved)
        text = path.read_text(encoding="utf-8", errors="replace")
        for group in LOCAL_REQ_RE.findall(text) + LOCAL_FROM_REQ_RE.findall(text):
            for module in group.split():
                local = root / f"{module}.v"
                if local.exists() and local.name not in generated:
                    visit(local)
        order.append(path)

    root_files = [root / name for name in generated if (root / name).exists()]
    for source in root_files:
        text = source.read_text(encoding="utf-8", errors="replace")
        for group in LOCAL_REQ_RE.findall(text) + LOCAL_FROM_REQ_RE.findall(text):
            for module in group.split():
                local = root / f"{module}.v"
                if local.exists() and local.name not in generated:
                    visit(local)
    return order


def strategy_dep_order(sources: list[Path]) -> list[Path]:
    strategy_dir = QCP_ROOT / "SeparationLogic" / "examples" / STRATEGY_COQ_PATH.split(".")[-1]
    order: list[Path] = []
    seen: set[Path] = set()

    def visit(path: Path) -> None:
        resolved = path.resolve()
        if resolved in seen or not path.exists():
            return
        seen.add(resolved)
        text = path.read_text(encoding="utf-8", errors="replace")
        for group in LOCAL_REQ_RE.findall(text) + LOCAL_FROM_REQ_RE.findall(text):
            for module in group.split():
                local = strategy_dir / f"{module}.v"
                if local.exists():
                    visit(local)
        order.append(path)

    for source in sources:
        visit(source)
    return order


def strategy_roots_from_generated(qcp_coq: Path) -> list[Path]:
    strategy_dir = QCP_ROOT / "SeparationLogic" / "examples" / STRATEGY_COQ_PATH.split(".")[-1]
    roots: list[Path] = []
    seen: set[Path] = set()
    for generated in sorted(qcp_coq.glob("*.v")):
        text = generated.read_text(encoding="utf-8", errors="replace")
        for group in STRATEGY_REQ_RE.findall(text):
            for module in group.split():
                path = strategy_dir / f"{module}.v"
                if path.exists() and path.resolve() not in seen:
                    seen.add(path.resolve())
                    roots.append(path)
    return roots


def clean_coq_artifacts(path: Path) -> None:
    if not path.exists():
        return
    for pattern in ("*.vo", "*.glob", "*.vok", "*.vos", ".*.aux"):
        for artifact in path.rglob(pattern):
            if artifact.is_file():
                artifact.unlink()


def remove_deps_dirs(path: Path) -> None:
    if not path.exists():
        return
    for deps_dir in sorted(path.glob("*/deps")):
        if deps_dir.is_symlink():
            continue
        if deps_dir.is_dir():
            shutil.rmtree(deps_dir)


def verify_case(case_dir: Path, *, timeout: int, keep: bool) -> dict:
    stem = case_dir.name
    workspace = f"ground_truth_{stem}"
    log: list[str] = []
    result = {
        "name": stem,
        "workspace": workspace,
        "status": "Fail",
        "stage": "",
        "log": str(case_dir / "verify_ground_truth.log"),
    }

    qcp_input, qcp_coq = stage_case(case_dir, workspace)
    clean_coq_artifacts(qcp_coq)

    symexec = [
        *SYMEXEC_COMMAND,
        f"--goal-file=SeparationLogic/examples/CAV/{workspace}/{stem}_goal.v",
        f"--proof-auto-file=SeparationLogic/examples/CAV/{workspace}/{stem}_proof_auto.v",
        f"--proof-manual-file=SeparationLogic/examples/CAV/{workspace}/{stem}_proof_manual.v",
        f"--coq-logic-path=SimpleC.EE.CAV.{workspace}",
        f"-I{STDLIB_SOURCE_PATH}",
        "-slp",
        STDLIB_SOURCE_PATH,
        STDLIB_COQ_PATH,
        f"-I{STRATEGY_SOURCE_PATH}",
        "-slp",
        STRATEGY_SOURCE_PATH,
        STRATEGY_COQ_PATH,
        f"--input-file=QCP_examples/CAV/{workspace}/{stem}.c",
        "--no-exec-info",
    ]
    rc = run(symexec, cwd=QCP_ROOT, timeout=timeout, log=log)
    if rc != 0:
        result["stage"] = "symexec"
        log.append("[FAIL] symexec")
        (case_dir / "verify_ground_truth.log").write_text("\n".join(log) + "\n", encoding="utf-8")
        return result
    log.append("symexec replay succeeded")

    migrated_manual = case_dir / f"{stem}_proof_manual.v"
    shutil.copy2(migrated_manual, qcp_coq / migrated_manual.name)

    case_args = coq_common_args(workspace)
    for support in support_dep_order(qcp_coq, stem):
        rc = run([*COQC_COMMAND, *case_args, support.name], cwd=qcp_coq, timeout=timeout, log=log)
        if rc != 0:
            result["stage"] = f"support:{support.name}"
            log.append(f"[FAIL] support:{support.name}")
            (case_dir / "verify_ground_truth.log").write_text("\n".join(log) + "\n", encoding="utf-8")
            return result
    log.append("[OK] support")

    for suffix in ("goal", "proof_auto", "proof_manual", "goal_check"):
        name = f"{stem}_{suffix}.v"
        rc = run([*COQC_COMMAND, *case_args, name], cwd=qcp_coq, timeout=timeout, log=log)
        if rc != 0:
            result["stage"] = suffix
            log.append(f"[FAIL] {suffix}")
            (case_dir / "verify_ground_truth.log").write_text("\n".join(log) + "\n", encoding="utf-8")
            return result
        log.append(f"[OK] {suffix}")

    manual_text = (qcp_coq / f"{stem}_proof_manual.v").read_text(encoding="utf-8", errors="replace")
    if OBLIGATION_RE.search(manual_text):
        result["stage"] = "proof_manual_obligation_marker"
        log.append("[FAIL] proof_manual_obligation_marker")
        (case_dir / "verify_ground_truth.log").write_text("\n".join(log) + "\n", encoding="utf-8")
        return result

    for suffix in ("goal", "proof_auto", "proof_manual", "goal_check"):
        shutil.copy2(qcp_coq / f"{stem}_{suffix}.v", case_dir / f"{stem}_{suffix}.v")

    result["status"] = "Success"
    result["stage"] = "verified"
    (case_dir / "verify_ground_truth.log").write_text("\n".join(log) + "\n", encoding="utf-8")
    if not keep:
        clean_coq_artifacts(qcp_coq)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--problem", action="append", help="Problem stem, e.g. p003_below_zero. Repeatable.")
    parser.add_argument("--limit", type=int, help="Verify only the first N selected cases.")
    parser.add_argument("--timeout", type=int, default=120, help="Per-command timeout in seconds.")
    parser.add_argument("--keep-workspace", action="store_true", help="Keep staged QCP workspaces and compile artifacts.")
    args = parser.parse_args()

    selected = set(args.problem or [])
    case_dirs = sorted(path for path in GROUND_TRUTH.iterdir() if path.is_dir())
    if selected:
        case_dirs = [path for path in case_dirs if path.name in selected]
    if args.limit is not None:
        case_dirs = case_dirs[: args.limit]

    results: list[dict] = []
    for case_dir in case_dirs:
        print(f"[verify-ground-truth] {case_dir.name}", flush=True)
        result = verify_case(case_dir, timeout=args.timeout, keep=args.keep_workspace)
        results.append(result)
        print(f"[verify-ground-truth] {case_dir.name} {result['status']} stage={result['stage']}", flush=True)

    summary = {
        "selected": len(results),
        "success": sum(1 for r in results if r["status"] == "Success"),
        "fail": sum(1 for r in results if r["status"] != "Success"),
    }
    print(json.dumps(summary, sort_keys=True))
    return 0 if all(r["status"] == "Success" for r in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
