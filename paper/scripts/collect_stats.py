#!/usr/bin/env python3
"""Collect a definitive statistics snapshot from the CAV-Bench result trees.

Writes figures/stats_snapshot.json, the single data source consumed by both the
experiment figures and the numbers quoted in the paper text.

Usage:
    python3 scripts/collect_stats.py            # full sweep (includes tool-call trace parsing)
    python3 scripts/collect_stats.py --fast     # skip tool-call trace parsing
"""

from __future__ import annotations

import difflib
import importlib.util
import json
import re
import shlex
import sys
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path
from types import ModuleType
from typing import Any

PROJECT_ROOT = Path(__file__).resolve().parents[1]
FIGURES_DIR = PROJECT_ROOT / "figures"
C_ROOT = Path("/home/yangfp/CAV/main/CAV-bench")
DLC_ROOT = Path("/home/yangfp/CAV/2.0.3/CAV-bench")
RTE_ROOT = Path("/home/yangfp/CAV/2.0.4/CAV-bench")
CODEX_SESSIONS_ROOT = Path.home() / ".codex" / "sessions"

_FALSE_COMMAND_PREFIX_RE = re.compile(
    r"""\b(?:rg|grep|find|ps|pgrep|pkill)\b|\bcommand\s+-v\b"""
)
_COQ_TOOL_RE = re.compile(r"""(?<![\w.-])(coqc|coqtop)\b""")
_VCG_TOOL_RE = re.compile(
    r"""(?<![\w.-])(?:[\w./-]*/)?symexec\s+--goal-file(?:=|\s)"""
)
_READ_SHELL_RE = re.compile(
    r"""(?:^|&&|;|\||\n)\s*(?:[A-Za-z_][A-Za-z0-9_]*=\S+\s+)*"""
    r"""(?:cat|sed|head|tail|less|more|rg|grep|find|ls|tree|stat|wc|"""
    r"""diff|cmp|file|readlink|realpath)\b"""
)
_READ_TOOL_NAMES = {
    "read",
    "readfile",
    "read_file",
    "glob",
    "grep",
    "search",
    "listfiles",
    "list_files",
}
_WRITE_TOOL_NAMES = {
    "write",
    "writefile",
    "write_file",
    "edit",
    "multiedit",
    "multi_edit",
    "strreplacefile",
    "str_replace_file",
    "file_change",
    "apply_patch",
}
_WRITE_SHELL_RE = re.compile(
    r"""(?:^|&&|;|\||\n)\s*(?:[A-Za-z_][A-Za-z0-9_]*=\S+\s+)*"""
    r"""(?:tee|touch|cp|mv|install|truncate|apply_patch)\b|"""
    r"""(?<![-=>])>{1,2}(?!=)(?!\s*(?:/dev/null|&))"""
)
_SESSION_PATH_CACHE: dict[str, Path | None] = {}
_LEAKAGE_MODULE_CACHE: dict[Path, ModuleType] = {}
_ARTIFACT_MODULE_CACHE: dict[Path, ModuleType] = {}
_WORKSPACE_AUDIT_CACHE: dict[tuple[Path, bool, tuple[str, ...]], dict[str, object]] = {}
_SELECTION_CACHE: dict[tuple[Path, str], tuple[dict[str, Path], dict[str, object]]] = {}

# These are the answer-bearing/cross-run read categories enforced by the
# repository's standalone transcript scanner.  ``repo_annotated_access`` is
# intentionally absent: the active annotated file is the agent's designated
# output, not a prior answer.  The scanner already distinguishes the current
# output workspace from a different ``output/verify_*`` workspace.
LEAKAGE_EXCLUSION_CATEGORIES = {
    "ground_truth_access",
    "results_access",
    "output_workspace_access",
    "annotated_input_access",
    "other_cav_workspace_access",
    "cav_workspace_glob",
    "cav_parent_scan",
}

# Canonical task lists come from the ground-truth corpora.
def ground_truth_tasks(root: Path) -> set[str]:
    return {p.name for p in (root / "ground_truth").iterdir() if p.is_dir()}


# (harness key for trace parsing, display harness, display model, display effort, result dir)
CONFIGS_C = [
    ("Codex CLI", "Codex", "GPT-5.5", "xhigh", C_ROOT / "results/codex/gpt-5.5/xhigh"),
    ("Codex CLI", "Codex", "GPT-5.5", "medium", C_ROOT / "results/codex/gpt-5.5/medium"),
    ("Codex CLI", "Codex", "GPT-5.4", "xhigh", C_ROOT / "results/codex/gpt-5.4/xhigh"),
    ("Codex CLI", "Codex", "GPT-5.4", "high", C_ROOT / "results/codex/gpt-5.4/high"),
    ("Codex CLI", "Codex", "GPT-5.4", "medium", C_ROOT / "results/codex/gpt-5.4/medium"),
    ("Codex CLI", "Codex", "GPT-5.4", "low", C_ROOT / "results/codex/gpt-5.4/low"),
    ("Codex CLI", "Codex", "GPT-5.4-mini", "medium", C_ROOT / "results/codex/gpt-5.4-mini/medium"),
    ("Claude Code", "Claude Code", "GLM-5.2", "default", C_ROOT / "results/claude/glm-5.2/api"),
    ("Claude Code", "Claude Code", "DeepSeek-V4-Pro", "default", C_ROOT / "results/claude/deepseek-v4-pro/api"),
    ("Kimi Code", "Kimi Code", "Kimi for Coding", "thinking", C_ROOT / "results/kimicode/kimi-code__kimi-for-coding/thinking"),
]

CONFIGS_DLC = [
    ("Codex CLI", "Codex", "GPT-5.5", "xhigh", DLC_ROOT / "results/codex/gpt-5.5/xhigh"),
    ("Codex CLI", "Codex", "GPT-5.5", "medium", DLC_ROOT / "results/codex/gpt-5.5/medium"),
    ("Codex CLI", "Codex", "GPT-5.4", "xhigh", DLC_ROOT / "results/codex/gpt-5.4/xhigh"),
    ("Codex CLI", "Codex", "GPT-5.4", "high", DLC_ROOT / "results/codex/gpt-5.4/high"),
    ("Codex CLI", "Codex", "GPT-5.4", "medium", DLC_ROOT / "results/codex/gpt-5.4/medium"),
    ("Codex CLI", "Codex", "GPT-5.4", "low", DLC_ROOT / "results/codex/gpt-5.4/low"),
    ("Codex CLI", "Codex", "GPT-5.4-mini", "medium", DLC_ROOT / "results/codex/gpt-5.4-mini/medium"),
    ("Claude Code", "Claude Code", "GLM-5.2", "default", DLC_ROOT / "results/claude/glm-5.2/api"),
    ("Claude Code", "Claude Code", "DeepSeek-V4-Pro", "default", DLC_ROOT / "results/claude/deepseek-v4-pro/api"),
    ("Kimi Code", "Kimi Code", "Kimi for Coding", "thinking", DLC_ROOT / "results/kimicode/kimi-code__kimi-for-coding/thinking"),
]

HARNESS_CLAUDE_SHARED_TASKS = [
    "p052_below_threshold",
    "p082_prime_length",
    "p138_is_equal_to_sum_even",
    "p139_special_factorial",
]

# Fig. 4 is a fixed timing analysis registered on the original 127 runnable
# programs.  The five later DLC additions are part of all effectiveness
# denominators (132/164), but were not part of this trace cohort.
BRANCH_TIMING_EXTENSION_EXCLUDED = {
    "p117_select_words",
    "p147_get_matrix_triples",
    "p149_sorted_list_sum",
    "p153_Strongest_Extension",
    "p160_do_algebra",
}

HARNESS_CONFIGS = [
    ("GLM-5.2|Codex CLI", "Codex CLI", "GLM-5.2", C_ROOT / "results/codex/glm-5.2/api"),
    ("GLM-5.2|OpenCode", "OpenCode", "GLM-5.2", C_ROOT / "results/opencode/glm-5.2/api"),
    ("GLM-5.2|Claude Code", "Claude Code", "GLM-5.2", C_ROOT / "results/claude/glm-5.2/api"),
    ("DeepSeek-V4-Pro|Codex CLI", "Codex CLI", "DeepSeek-V4-Pro", C_ROOT / "results/codex/deepseek-v4-pro/api"),
    ("DeepSeek-V4-Pro|OpenCode", "OpenCode", "DeepSeek-V4-Pro", C_ROOT / "results/opencode/deepseek-v4-pro/api"),
    ("DeepSeek-V4-Pro|Claude Code", "Claude Code", "DeepSeek-V4-Pro", C_ROOT / "results/claude/deepseek-v4-pro/api"),
]


def metric_value(text: str, key: str) -> str:
    prefix = f"- {key}: `"
    values = [line[len(prefix):-1] for line in text.splitlines() if line.startswith(prefix) and line.endswith("`")]
    return values[-1] if values else ""


def metric_float(text: str, key: str) -> float | None:
    value = metric_value(text, key)
    try:
        return float(value)
    except ValueError:
        return None


def final_result(text: str) -> str:
    for line in reversed(text.splitlines()):
        if line.startswith("Final Result:"):
            return line.split(":", 1)[1].strip()
    return ""


def classify(text: str) -> str:
    if final_result(text) == "Success":
        return "correct"
    if metric_value(text, "Last agent exit code") == "124":
        return "timeout"
    if metric_value(text, "Status") == "Timeout":
        return "timeout"
    return "wrong"


def problem_name(workspace: Path, prefix: str = "verify") -> str:
    return re.sub(rf"^{prefix}_[0-9]{{8}}_[0-9]{{6}}[0-9a-z]*_", "", workspace.name)


def benchmark_root(workspace: Path) -> Path:
    for root in (C_ROOT, DLC_ROOT, RTE_ROOT):
        if workspace.is_relative_to(root):
            return root
    raise ValueError(f"workspace is outside the three benchmark branches: {workspace}")


def leakage_module(workspace: Path) -> ModuleType:
    """Load the corpus-owned scanner so the statistics audit cannot drift."""
    root = benchmark_root(workspace)
    script = root / "scripts" / "check_leakage.py"
    if script not in _LEAKAGE_MODULE_CACHE:
        spec = importlib.util.spec_from_file_location(
            f"cav_bench_check_leakage_{len(_LEAKAGE_MODULE_CACHE)}", script
        )
        if spec is None or spec.loader is None:
            raise RuntimeError(f"cannot load leakage scanner: {script}")
        module = importlib.util.module_from_spec(spec)
        # dataclasses resolves the defining module through sys.modules.
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        _LEAKAGE_MODULE_CACHE[script] = module
    return _LEAKAGE_MODULE_CACHE[script]


def artifact_audit_module(workspace: Path) -> ModuleType:
    root = benchmark_root(workspace)
    script = root / "scripts" / "check_verify_audit.py"
    if script not in _ARTIFACT_MODULE_CACHE:
        spec = importlib.util.spec_from_file_location(
            f"cav_bench_check_verify_audit_{len(_ARTIFACT_MODULE_CACHE)}", script
        )
        if spec is None or spec.loader is None:
            raise RuntimeError(f"cannot load artifact audit: {script}")
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        _ARTIFACT_MODULE_CACHE[script] = module
    return _ARTIFACT_MODULE_CACHE[script]


def agent_transcripts(workspace: Path) -> list[Path]:
    logs = workspace / "logs"
    return sorted(
        path
        for path in logs.glob("agent_stdout_*.jsonl")
        if not path.name.endswith(".timeline.tsv")
    )


def compact_leakage_findings(findings: list[Any]) -> dict[str, object]:
    categories = Counter(str(item.category) for item in findings)
    examples = []
    for item in findings[:3]:
        examples.append(
            {
                "category": str(item.category),
                "transcript": str(item.transcript),
                "line": int(item.line),
                "tool": str(item.tool),
                "snippet": str(item.snippet)[:300],
            }
        )
    return {
        "finding_count": len(findings),
        "categories": dict(sorted(categories.items())),
        "examples": examples,
    }


def audit_workspace(
    workspace: Path,
    *,
    require_transcript: bool = True,
    check_artifacts: bool = True,
    allowed_workspace_names: set[str] | None = None,
) -> dict[str, object]:
    """Audit one agent workspace without mutating any experiment artifact."""
    allowed_names = tuple(sorted(allowed_workspace_names or set()))
    cache_key = (workspace, check_artifacts, allowed_names)
    if cache_key in _WORKSPACE_AUDIT_CACHE:
        cached = dict(_WORKSPACE_AUDIT_CACHE[cache_key])
        reasons = list(cached.get("reasons", []))
        if require_transcript and not cached.get("transcript_count", 0):
            reasons.append("missing_transcript")
        cached["reasons"] = sorted(set(reasons))
        return cached

    transcripts = agent_transcripts(workspace)
    reasons: list[str] = []
    if len(transcripts) > 1:
        # The final metrics aggregate multiple launches and cannot identify the
        # first launch's independently audited outcome.  The attempt remains
        # in A but external admission overrides its outcome to Wrong.
        reasons.append("legacy_multiple_invocations")

    relevant: list[Any] = []
    if transcripts:
        module = leakage_module(workspace)
        for finding in module.scan_paths([workspace]):
            category = str(finding.category)
            if category not in LEAKAGE_EXCLUSION_CATEGORIES:
                continue
            # End-to-end stages are allowed to read artifacts produced by the
            # other stages of the *same* pipeline attempt.  The standalone
            # scanner cannot infer that relationship from an archived path.
            if category in {
                "output_workspace_access",
                "other_cav_workspace_access",
                "cav_workspace_glob",
            }:
                named = re.findall(r"`((?:verify|contract|eval)_[^`]+)`", str(finding.message))
                if named and all(name in allowed_names for name in named):
                    continue
                mentioned = set(
                    re.findall(
                        r"(?:verify|contract|eval)_\d{8}_\d+[a-z]?_[A-Za-z0-9_]+",
                        str(finding.snippet),
                    )
                )
                if mentioned and mentioned <= set(allowed_names):
                    continue
            relevant.append(finding)
        if relevant:
            reasons.append("transcript_leakage")

    artifact_result: dict[str, object] = {
        "checked": False,
        "error_count": 0,
        "groups": {},
        "categories": {},
        "examples": [],
    }
    metrics_path = workspace / "logs" / "metrics.md"
    claimed_success = False
    if metrics_path.exists():
        metrics_text = metrics_path.read_text(encoding="utf-8", errors="replace")
        claimed_success = final_result(metrics_text) == "Success"
    # Shape/proof admission is meaningful for artifacts claimed as successful;
    # an ordinary failed/timeout run is already a model failure and naturally
    # lacks a complete proof bundle.
    if check_artifacts and claimed_success:
        module = artifact_audit_module(workspace)
        result = module.scan_workspace(workspace)
        error_findings = [
            finding
            for finding in result.get("findings", [])
            if finding.get("severity") == "error"
        ]
        summary = result.get("summary", {})
        artifact_result = {
            "checked": True,
            "error_count": len(error_findings),
            "groups": summary.get("groups", {}),
            "categories": summary.get("categories", {}),
            "examples": [
                {
                    "group": finding.get("group"),
                    "category": finding.get("category"),
                    "file": finding.get("file"),
                    "line": finding.get("line"),
                    "snippet": str(finding.get("snippet", ""))[:300],
                }
                for finding in error_findings[:3]
            ],
        }
        if error_findings:
            reasons.append("artifact_audit_failure")

    audit: dict[str, object] = {
        "workspace": str(workspace),
        "transcript_count": len(transcripts),
        "reasons": sorted(set(reasons)),
        "leakage": compact_leakage_findings(relevant),
        "artifact_audit": artifact_result,
    }
    _WORKSPACE_AUDIT_CACHE[cache_key] = audit
    if require_transcript and not transcripts:
        audit = dict(audit)
        audit["reasons"] = sorted(set([*audit["reasons"], "missing_transcript"]))
    return audit


def complete_metrics_workspace(workspace: Path) -> bool:
    path = workspace / "logs" / "metrics.md"
    if not path.exists():
        return False
    text = path.read_text(encoding="utf-8", errors="replace")
    return bool(metric_value(text, "End time")) and bool(
        final_result(text) or metric_value(text, "Status")
    )


def attempt_order(workspace: Path) -> tuple[float, str]:
    metrics = workspace / "logs" / "metrics.md"
    if metrics.exists():
        text = metrics.read_text(encoding="utf-8", errors="replace")
        start = timestamp_epoch(metric_value(text, "Start time"))
        if start is not None:
            return start, workspace.name
    return workspace.stat().st_mtime, workspace.name


def selection_report(
    rejections: dict[str, dict[str, object]],
    extra_complete: dict[str, list[str]],
    incomplete: dict[str, list[str]],
) -> dict[str, object]:
    by_reason: Counter[str] = Counter()
    leakage_categories: Counter[str] = Counter()
    artifact_categories: Counter[str] = Counter()
    artifact_groups: Counter[str] = Counter()
    for audit in rejections.values():
        by_reason.update(str(reason) for reason in audit.get("reasons", []))
        leakage_categories.update(
            {
                str(key): int(value)
                for key, value in (audit.get("leakage", {}).get("categories", {})).items()
            }
        )
        artifact_categories.update(
            {
                str(key): int(value)
                for key, value in audit.get("artifact_audit", {}).get("categories", {}).items()
            }
        )
        artifact_groups.update(
            {
                str(key): int(value)
                for key, value in audit.get("artifact_audit", {}).get("groups", {}).items()
            }
        )
    return {
        "count": len(rejections),
        "by_reason": dict(sorted(by_reason.items())),
        "leakage_categories": dict(sorted(leakage_categories.items())),
        "artifact_categories": dict(sorted(artifact_categories.items())),
        "artifact_groups": dict(sorted(artifact_groups.items())),
        "tasks": dict(sorted(rejections.items())),
        "additional_complete_attempts_ignored": dict(sorted(extra_complete.items())),
        "incomplete_attempts_ignored": dict(sorted(incomplete.items())),
    }


def selected_workspaces(
    result_dir: Path,
    prefix: str = "verify",
) -> tuple[dict[str, Path], dict[str, object]]:
    """Select at most one completed attempt per task.

    Selection is chronological, never outcome based: the earliest complete
    workspace is the counted attempt.  An external-audit rejection overrides
    its outcome to Wrong; a later workspace can never replace it.
    """
    cache_key = (result_dir, prefix)
    if cache_key in _SELECTION_CACHE:
        return _SELECTION_CACHE[cache_key]

    grouped: dict[str, list[Path]] = defaultdict(list)
    incomplete: dict[str, list[str]] = defaultdict(list)
    for workspace in result_dir.glob(f"{prefix}_*"):
        if not workspace.is_dir():
            continue
        name = problem_name(workspace, prefix)
        if complete_metrics_workspace(workspace):
            grouped[name].append(workspace)
        else:
            incomplete[name].append(str(workspace))

    selected: dict[str, Path] = {}
    rejections: dict[str, dict[str, object]] = {}
    extra_complete: dict[str, list[str]] = {}
    for name, candidates in sorted(grouped.items()):
        candidates.sort(key=attempt_order)
        first = candidates[0]
        audit = audit_workspace(first, check_artifacts=prefix in {"verify", "proof"})
        selected[name] = first
        if audit["reasons"]:
            rejections[name] = audit
        if len(candidates) > 1:
            extra_complete[name] = [str(path) for path in candidates[1:]]

    report = selection_report(rejections, extra_complete, incomplete)
    _SELECTION_CACHE[cache_key] = (selected, report)
    return selected, report


def pipeline_payload(workspace: Path) -> dict[str, object] | None:
    path = workspace / "pipeline_summary.json"
    if not path.exists():
        return None
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    return payload if payload.get("status") else None


def audit_pipeline_workspace(workspace: Path, result_dir: Path) -> dict[str, object]:
    payload = pipeline_payload(workspace) or {}
    component_names = {
        Path(str(raw_path)).name for raw_path in payload.get("workspaces", [])
    }
    component_audits: list[dict[str, object]] = []
    reasons: list[str] = []
    finding_count = 0
    categories: Counter[str] = Counter()
    examples: list[dict[str, object]] = []
    artifact_errors = 0
    artifact_categories: Counter[str] = Counter()
    artifact_groups: Counter[str] = Counter()
    artifact_examples: list[dict[str, object]] = []
    for raw_path in payload.get("workspaces", []):
        component = result_dir / Path(str(raw_path)).name
        if not component.exists():
            reasons.append("missing_pipeline_component")
            component_audits.append(
                {"workspace": str(component), "reasons": ["missing_pipeline_component"]}
            )
            continue
        audit = audit_workspace(
            component,
            require_transcript=False,
            check_artifacts=component.name.startswith("verify_"),
            allowed_workspace_names=component_names,
        )
        component_audits.append(audit)
        reasons.extend(str(reason) for reason in audit.get("reasons", []))
        leak = audit.get("leakage", {})
        finding_count += int(leak.get("finding_count", 0))
        categories.update(
            {str(key): int(value) for key, value in leak.get("categories", {}).items()}
        )
        examples.extend(leak.get("examples", []))
        artifact = audit.get("artifact_audit", {})
        artifact_errors += int(artifact.get("error_count", 0))
        artifact_categories.update(
            {str(key): int(value) for key, value in artifact.get("categories", {}).items()}
        )
        artifact_groups.update(
            {str(key): int(value) for key, value in artifact.get("groups", {}).items()}
        )
        artifact_examples.extend(artifact.get("examples", []))
    return {
        "workspace": str(workspace),
        "reasons": sorted(set(reasons)),
        "components": component_audits,
        "leakage": {
            "finding_count": finding_count,
            "categories": dict(sorted(categories.items())),
            "examples": examples[:3],
        },
        "artifact_audit": {
            "checked": any(
                component.get("artifact_audit", {}).get("checked", False)
                for component in component_audits
            ),
            "error_count": artifact_errors,
            "groups": dict(sorted(artifact_groups.items())),
            "categories": dict(sorted(artifact_categories.items())),
            "examples": artifact_examples[:3],
        },
    }


def selected_pipeline_workspaces(
    result_dir: Path,
) -> tuple[dict[str, Path], dict[str, object]]:
    cache_key = (result_dir, "pipeline")
    if cache_key in _SELECTION_CACHE:
        return _SELECTION_CACHE[cache_key]

    grouped: dict[str, list[Path]] = defaultdict(list)
    incomplete: dict[str, list[str]] = defaultdict(list)
    for workspace in result_dir.glob("pipeline_*"):
        if not workspace.is_dir() or workspace.name.startswith("pipeline_batch_"):
            continue
        name = problem_name(workspace, "pipeline")
        if pipeline_payload(workspace) is None:
            incomplete[name].append(str(workspace))
        else:
            grouped[name].append(workspace)

    selected: dict[str, Path] = {}
    rejections: dict[str, dict[str, object]] = {}
    extra_complete: dict[str, list[str]] = {}
    for name, candidates in sorted(grouped.items()):
        candidates.sort(key=lambda path: (path.name, path.stat().st_mtime))
        first = candidates[0]
        audit = audit_pipeline_workspace(first, result_dir)
        selected[name] = first
        if audit["reasons"]:
            rejections[name] = audit
        if len(candidates) > 1:
            extra_complete[name] = [str(path) for path in candidates[1:]]

    report = selection_report(rejections, extra_complete, incomplete)
    _SELECTION_CACHE[cache_key] = (selected, report)
    return selected, report


def timestamp_epoch(value: str) -> float | None:
    value = value.strip()
    if not value:
        return None
    if value.endswith("Z"):
        value = value[:-1] + "+00:00"
    for parser in (
        lambda text: datetime.fromisoformat(text),
        lambda text: datetime.strptime(text, "%Y-%m-%d %H:%M:%S %z"),
    ):
        try:
            return parser(value).timestamp()
        except ValueError:
            continue
    return None


def real_shell_occurrence(command: str, match: re.Match[str], tool: str) -> bool:
    """Reject commands that only search for a checker executable's name."""
    # Split only real shell sequencing delimiters: a vertical bar frequently
    # occurs inside quoted ripgrep patterns and is not reliable here.
    segment = re.split(r"&&|;|\n", command[:match.start()])[-1]
    if _FALSE_COMMAND_PREFIX_RE.search(segment):
        return False
    tail = command[match.end():].lstrip(" \t\"'")
    if tail.startswith("$"):
        return True
    if tool == "coqtop" and (tail.startswith("<<") or tail.startswith("<")):
        return True
    if tail.startswith(("-", "/")):
        return True
    return bool(
        re.match(r"""(?:\.\.?/)?[A-Za-z0-9_][\w./-]*\.v(?:\s|[\"']|$)""", tail)
    )


def command_phase_markers(command: str) -> tuple[bool, bool]:
    """Return (is_coqc, is_vcg) for an executed shell command.

    The boundary follows the runner's annotation/proof timing convention:
    VCG is either a direct symexec invocation or the older
    symexec_keep_proofs.py wrapper.  Regex boundaries avoid counting commands
    that merely read documentation or grep for these names.
    """
    is_coqc = bool(re.search(r"""=\s*compile_generated\s*\(""", command))
    if not is_coqc:
        is_coqc = any(
            real_shell_occurrence(command, match, match.group(1))
            for match in _COQ_TOOL_RE.finditer(command)
        )

    is_vcg = bool(re.search(r"""=\s*run_symexec\s*\(""", command))
    is_vcg = is_vcg or bool(
        re.search(r"""\bpython3\s+\S*symexec_keep_proofs\.py\s+--name\b""", command)
    )
    if not is_vcg:
        for match in _VCG_TOOL_RE.finditer(command):
            segment = re.split(r"&&|;|\n", command[:match.start()])[-1]
            if not _FALSE_COMMAND_PREFIX_RE.search(segment):
                is_vcg = True
                break
    return is_coqc, is_vcg


def dedupe_timestamps(values: list[float], tolerance: float) -> list[float]:
    out: list[float] = []
    for value in sorted(values):
        if not out or value - out[-1] > tolerance:
            out.append(value)
        else:
            out[-1] = min(out[-1], value)
    return out


def timeline_phase_markers(path: Path) -> tuple[list[float], list[float]]:
    """Extract VCG starts and coqc completions from a runner timeline."""
    vcg_starts: list[float] = []
    coqc_completions: list[float] = []
    if not path.exists():
        return vcg_starts, coqc_completions
    for line_number, line in enumerate(path.read_text(encoding="utf-8", errors="replace").splitlines()):
        if line_number == 0:
            continue
        fields = line.split("\t", 7)
        if len(fields) < 8:
            continue
        try:
            epoch = float(fields[0])
        except ValueError:
            continue
        event_type, item_type, command = fields[3], fields[4], fields[7]
        if item_type != "command_execution":
            continue
        is_coqc, is_vcg = command_phase_markers(command)
        if event_type == "item.started" and is_vcg:
            vcg_starts.append(epoch)
        # Failed coqc invocations still delimit proof work before an annotation
        # revision, so use every completed command event, not only exit code 0.
        if event_type == "item.completed" and is_coqc:
            coqc_completions.append(epoch)
    return vcg_starts, coqc_completions


def stdout_thread_id(path: Path) -> str:
    if not path.exists():
        return ""
    with path.open(encoding="utf-8", errors="replace") as handle:
        for line in handle:
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(event, dict) and event.get("thread_id"):
                return str(event["thread_id"])
    return ""


def codex_session_path(thread_id: str) -> Path | None:
    if not thread_id:
        return None
    if thread_id not in _SESSION_PATH_CACHE:
        matches = list(CODEX_SESSIONS_ROOT.glob(f"**/*{thread_id}.jsonl"))
        _SESSION_PATH_CACHE[thread_id] = matches[0] if matches else None
    return _SESSION_PATH_CACHE[thread_id]


def rollout_phase_markers(path: Path) -> tuple[list[float], list[float]]:
    """Recover timestamps for early runs that predate runner timeline TSVs."""
    vcg_starts: list[float] = []
    coqc_completions: list[float] = []
    coqc_calls: set[str] = set()
    if not path.exists():
        return vcg_starts, coqc_completions
    with path.open(encoding="utf-8", errors="replace") as handle:
        for line in handle:
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                continue
            if event.get("type") != "response_item":
                continue
            payload = event.get("payload") or {}
            if not isinstance(payload, dict):
                continue
            epoch = timestamp_epoch(str(event.get("timestamp", "")))
            if epoch is None:
                continue
            event_type = payload.get("type")
            if event_type == "function_call":
                raw_args = payload.get("arguments") or ""
                try:
                    args = json.loads(raw_args) if isinstance(raw_args, str) else raw_args
                except json.JSONDecodeError:
                    args = {}
                command = str((args or {}).get("cmd", "")) if isinstance(args, dict) else ""
                is_coqc, is_vcg = command_phase_markers(command)
                if is_vcg:
                    vcg_starts.append(epoch)
                if is_coqc:
                    coqc_calls.add(str(payload.get("call_id", "")))
            elif (
                event_type == "function_call_output"
                and str(payload.get("call_id", "")) in coqc_calls
            ):
                coqc_completions.append(epoch)
    return vcg_starts, coqc_completions


def workspace_phase_markers(workspace: Path) -> tuple[list[float], list[float], int]:
    """Collect command markers, falling back to Codex rollouts when needed."""
    vcg_starts: list[float] = []
    coqc_completions: list[float] = []
    missing_rollouts = 0
    logs = workspace / "logs"
    for stdout_path in sorted(logs.glob("agent_stdout_*.jsonl")):
        if stdout_path.name.endswith(".timeline.tsv"):
            continue
        timeline_path = Path(str(stdout_path) + ".timeline.tsv")
        if timeline_path.exists():
            vcg, coqc = timeline_phase_markers(timeline_path)
        else:
            thread_id = stdout_thread_id(stdout_path)
            session_path = codex_session_path(thread_id)
            if session_path is None:
                missing_rollouts += 1
                continue
            vcg, coqc = rollout_phase_markers(session_path)
        vcg_starts.extend(vcg)
        coqc_completions.extend(coqc)

    # Runner-owned initial/rerun VCG markers complement the agent timeline and
    # are especially important for runs whose first VCG precedes agent launch.
    phase_path = logs / "phase_timeline.tsv"
    if phase_path.exists():
        for line in phase_path.read_text(encoding="utf-8", errors="replace").splitlines():
            fields = line.split("\t")
            if len(fields) < 3 or fields[2] not in {"symexec_init_start", "symexec_rerun_start"}:
                continue
            try:
                vcg_starts.append(float(fields[0]))
            except ValueError:
                continue

    return (
        dedupe_timestamps(vcg_starts, tolerance=2.0),
        dedupe_timestamps(coqc_completions, tolerance=0.2),
        missing_rollouts,
    )


def phase_task_minutes(workspace: Path, *, proof_only: bool = False) -> dict[str, float | int]:
    """Split a run by VCG/coqc boundaries.

    Within VCG_i -> VCG_{i+1}, proof lasts through the final coqc completion;
    the remaining final-coqc -> next-VCG interval is annotation.  Before the
    first VCG the same rule is applied from run start; after the final VCG all
    remaining time is proof.  Proof-only fixes annotations, so its full run is
    assigned to proof.
    """
    metrics_path = workspace / "logs" / "metrics.md"
    if not metrics_path.exists():
        return {}
    text = metrics_path.read_text(encoding="utf-8", errors="replace")
    start = timestamp_epoch(metric_value(text, "Start time"))
    total_seconds = metric_float(text, "Wall-clock time (seconds)")
    if start is None or total_seconds is None:
        return {}
    if proof_only:
        return {
            "annotation": 0.0,
            "proof": total_seconds / 60.0,
            "total": total_seconds / 60.0,
            "vcg_events": 0,
            "coqc_events": 0,
            "missing_rollouts": 0,
        }

    end = start + total_seconds
    vcg_starts, coqc_completions, missing_rollouts = workspace_phase_markers(workspace)
    vcg_starts = [value for value in vcg_starts if start <= value <= end]
    coqc_completions = [value for value in coqc_completions if start <= value <= end]

    annotation_seconds = 0.0
    previous_vcg = start
    for vcg_start in vcg_starts:
        coqc_in_cycle = [
            value for value in coqc_completions
            if previous_vcg <= value <= vcg_start
        ]
        annotation_start = max(coqc_in_cycle) if coqc_in_cycle else previous_vcg
        annotation_seconds += max(0.0, vcg_start - annotation_start)
        previous_vcg = vcg_start
    proof_seconds = max(0.0, total_seconds - annotation_seconds)
    return {
        "annotation": annotation_seconds / 60.0,
        "proof": proof_seconds / 60.0,
        "total": total_seconds / 60.0,
        "vcg_events": len(vcg_starts),
        "coqc_events": len(coqc_completions),
        "missing_rollouts": missing_rollouts,
    }


def command_tool_profile(command: str) -> dict[str, int]:
    is_coqc, is_vcg = command_phase_markers(command)
    read_candidates = [command]
    try:
        argv = shlex.split(command)
    except ValueError:
        argv = []
    for index, token in enumerate(argv[:-2]):
        if Path(token).name in {"sh", "bash", "zsh"} and argv[index + 1] == "-lc":
            read_candidates.append(argv[index + 2])
    return {
        "read": int(any(_READ_SHELL_RE.search(value) for value in read_candidates)),
        "write": int(any(_WRITE_SHELL_RE.search(value) for value in read_candidates)),
        "coqc": int(is_coqc),
        "vcg": int(is_vcg),
    }


def tool_call_profile(name: str, arguments: object) -> dict[str, int]:
    normalized = name.casefold().replace("-", "_")
    profile = {
        "read": int(normalized in _READ_TOOL_NAMES),
        "write": int(normalized in _WRITE_TOOL_NAMES),
        "coqc": 0,
        "vcg": 0,
    }
    if normalized not in {"bash", "shell", "execute", "exec", "command"}:
        return profile
    if isinstance(arguments, str):
        try:
            decoded = json.loads(arguments)
        except json.JSONDecodeError:
            decoded = arguments
    else:
        decoded = arguments
    if isinstance(decoded, dict):
        command = str(decoded.get("command") or decoded.get("cmd") or "")
    else:
        command = str(decoded or "")
    shell_profile = command_tool_profile(command)
    return {key: max(profile[key], shell_profile[key]) for key in profile}


def trace_tool_profile(workspace: Path, harness: str) -> dict[str, int] | None:
    logs_dir = workspace / "logs"
    paths = sorted(
        p for p in logs_dir.glob("agent_stdout_*.jsonl") if not p.name.endswith(".timeline.tsv")
    )
    if not paths:
        return None
    profile = {
        "total": 0,
        "read": 0,
        "write": 0,
        "coqc": 0,
        "vcg": 0,
        "rounds": 0,
    }
    saw_json = False
    round_ids: set[str] = set()

    def add_call(name: str, arguments: object) -> None:
        profile["total"] += 1
        categories = tool_call_profile(name, arguments)
        for key, value in categories.items():
            profile[key] += value

    for path in paths:
        with path.open(encoding="utf-8", errors="replace") as handle:
            for line in handle:
                try:
                    event = json.loads(line)
                except json.JSONDecodeError:
                    continue
                saw_json = True
                event_type = event.get("type")
                if harness == "Codex CLI":
                    item = event.get("item") or {}
                    item_type = str(item.get("type", ""))
                    if event_type == "item.completed" and item_type == "agent_message":
                        profile["rounds"] += 1
                    if event_type == "item.completed" and item_type == "command_execution":
                        add_call("command", {"command": item.get("command", "")})
                    elif event_type == "item.completed" and item_type in {
                        "file_change",
                        "collab_tool_call",
                        "todo_list",
                        "web_search",
                    }:
                        add_call(item_type, item)
                elif harness == "OpenCode":
                    if event_type == "assistant":
                        profile["rounds"] += 1
                    if event_type == "tool_use":
                        add_call(
                            str(event.get("name") or event.get("tool") or ""),
                            event.get("input") or event.get("arguments") or {},
                        )
                elif harness == "Claude Code":
                    if event_type == "assistant":
                        message = event.get("message") or {}
                        message_id = str(message.get("id") or event.get("uuid") or "")
                        if message_id:
                            round_ids.add(message_id)
                        for block in message.get("content") or []:
                            if isinstance(block, dict) and block.get("type") == "tool_use":
                                add_call(
                                    str(block.get("name", "")),
                                    block.get("input") or {},
                                )
                elif harness == "Kimi Code":
                    if event.get("role") == "assistant":
                        profile["rounds"] += 1
                    calls = event.get("tool_calls") or []
                    if isinstance(calls, list):
                        for call in calls:
                            function = (
                                (call.get("function") or {})
                                if isinstance(call, dict)
                                else {}
                            )
                            add_call(
                                str(function.get("name", "")),
                                function.get("arguments") or {},
                            )
    if harness == "Claude Code":
        profile["rounds"] = len(round_ids)
    return profile if saw_json else None


def mean(values: list[float]) -> float:
    return sum(values) / len(values) if values else 0.0


def added_nonblank_lines(before_path: Path, after_path: Path) -> int:
    if not before_path.exists() or not after_path.exists():
        return 0
    before = [l.strip() for l in before_path.read_text(encoding="utf-8", errors="replace").splitlines()]
    after = [l.strip() for l in after_path.read_text(encoding="utf-8", errors="replace").splitlines()]
    added = 0
    matcher = difflib.SequenceMatcher(a=before, b=after, autojunk=False)
    for tag, _i1, _i2, j1, j2 in matcher.get_opcodes():
        if tag in {"insert", "replace"}:
            added += sum(1 for l in after[j1:j2] if l)
    return added


def manual_proof_body_lines(path: Path) -> int:
    if not path.exists():
        return 0
    count = 0
    in_proof = False
    for raw in path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = raw.strip()
        if not line:
            continue
        if not in_proof:
            if re.match(r"^(Proof|Next Obligation)\b", line):
                in_proof = True
                line = re.sub(r"^(Proof|Next Obligation)\.?", "", line, count=1).strip()
                if not line:
                    continue
            else:
                continue
        terminator = re.search(r"\b(Qed|Admitted|Abort|Defined)\.", line)
        if terminator:
            before_term = line[: terminator.start()].strip()
            if before_term and not before_term.startswith("(*"):
                count += 1
            in_proof = False
            continue
        if line.startswith("(*") and line.endswith("*)"):
            continue
        count += 1
    return count


def generated_code_lines(workspace: Path) -> int:
    original = sorted((workspace / "original").glob("*.c"))
    annotated = sorted((workspace / "annotated").glob("*.c"))
    annotation_lines = added_nonblank_lines(original[0], annotated[0]) if original and annotated else 0
    proof_lines = sum(
        manual_proof_body_lines(p) for p in (workspace / "coq" / "generated").glob("*_proof_manual.v")
    )
    return annotation_lines + proof_lines


def summarize_config(
    harness_key: str,
    result_dir: Path,
    tasks: set[str],
    with_traces: bool,
    with_code_lines: bool = False,
    trace_solved_only: bool = False,
) -> dict[str, object] | None:
    if not result_dir.exists():
        return None
    selected, protocol_report = selected_workspaces(result_dir)
    selected = {name: ws for name, ws in selected.items() if name in tasks}
    rejected_tasks = {
        name: detail
        for name, detail in protocol_report["tasks"].items()
        if name in tasks
    }
    filtered_report = selection_report(
        rejected_tasks,
        {
            name: paths
            for name, paths in protocol_report["additional_complete_attempts_ignored"].items()
            if name in tasks
        },
        {
            name: paths
            for name, paths in protocol_report["incomplete_attempts_ignored"].items()
            if name in tasks
        },
    )
    if not selected:
        return None
    counts = {"correct": 0, "wrong": 0, "timeout": 0}
    walls: list[float] = []
    input_tokens: list[float] = []
    output_tokens: list[float] = []
    total_tokens: list[float] = []
    tool_profiles: list[dict[str, int]] = []
    code_lines: list[float] = []
    per_task: dict[str, str] = {}
    per_task_metrics: dict[str, dict[str, object]] = {}
    # solved-only buckets: cost averages over audited successes exclude the
    # thrashing of failed runs (失败的不统计)
    solved = {"walls": [], "input": [], "output": [], "tools": [], "code": []}
    # Cost over completed non-timeout trajectories, including rejected runs.
    non_timeout = {"walls": [], "input": [], "output": [], "tools": []}
    selected_paths: dict[str, str] = {}
    for name, ws in sorted(selected.items()):
        metrics_path = ws / "logs" / "metrics.md"
        if not metrics_path.exists():
            continue
        text = metrics_path.read_text(encoding="utf-8", errors="replace")
        outcome = "wrong" if name in rejected_tasks else classify(text)
        # Primary-task success uses the recorded end-to-end 90-minute cutoff.
        recorded_wall = metric_float(text, "Wall-clock time (seconds)")
        if outcome == "correct" and (recorded_wall is None or recorded_wall > 5400):
            outcome = "timeout"
        counts[outcome] += 1
        per_task[name] = outcome
        selected_paths[name] = str(ws)
        task_row: dict[str, object] = {"outcome": outcome}
        wall = metric_float(text, "Wall-clock time (seconds)")
        if wall:
            walls.append(wall)
            task_row["wall_seconds"] = wall
            if outcome == "correct":
                solved["walls"].append(wall)
            if outcome != "timeout":
                non_timeout["walls"].append(wall)
        for key, bucket, skey in (
            ("Agent CLI input_tokens", input_tokens, "input"),
            ("Agent CLI output_tokens", output_tokens, "output"),
            ("Agent CLI total_tokens", total_tokens, None),
        ):
            value = metric_float(text, key)
            if value:
                bucket.append(value)
                task_row[
                    {
                        "Agent CLI input_tokens": "input_tokens",
                        "Agent CLI output_tokens": "output_tokens",
                        "Agent CLI total_tokens": "total_tokens",
                    }[key]
                ] = value
                if skey and outcome == "correct":
                    solved[skey].append(value)
                if skey and outcome != "timeout":
                    non_timeout[skey].append(value)
        if with_traces and not (trace_solved_only and outcome != "correct"):
            profile = trace_tool_profile(ws, harness_key)
            if profile is not None:
                tool_profiles.append(profile)
                task_row["tool_calls"] = profile["total"]
                task_row["turns"] = profile["rounds"]
                if outcome == "correct":
                    solved["tools"].append(profile)
                if outcome != "timeout":
                    non_timeout["tools"].append(profile)
        if with_code_lines:
            lines = float(generated_code_lines(ws))
            code_lines.append(lines)
            if outcome == "correct":
                solved["code"].append(lines)
        per_task_metrics[name] = task_row
    attempted = sum(counts.values())
    if not attempted:
        return None
    return {
        "attempted": attempted,
        "task_universe": len(tasks),
        "source_universe": 164,
        "runnable_universe": 132,
        "correct": counts["correct"],
        "wrong": counts["wrong"],
        "timeout": counts["timeout"],
        "coverage": attempted / len(tasks),
        "attempted_accuracy": counts["correct"] / attempted if attempted else 0.0,
        "source_yield": counts["correct"] / 164,
        "runnable_yield": counts["correct"] / 132,
        "corpus_yield": counts["correct"] / len(tasks),
        # Backward-compatible aliases consumed by the existing figure code.
        "accuracy": counts["correct"] / attempted if attempted else 0.0,
        "accuracy_full": counts["correct"] / len(tasks),
        "avg_minutes": mean(walls) / 60.0,
        "avg_input_tokens_m": mean(input_tokens) / 1e6,
        "avg_output_tokens_k": mean(output_tokens) / 1e3,
        "avg_total_tokens_m": mean(total_tokens) / 1e6,
        "avg_tool_calls": mean([float(row["total"]) for row in tool_profiles]),
        "avg_tool_profile": {
            key: mean([float(row[key]) for row in tool_profiles])
            for key in ("total", "read", "write", "coqc", "vcg", "rounds")
        },
        "avg_generated_code_lines": mean(code_lines),
        "time_runs": len(walls),
        "token_runs": len(total_tokens),
        "trace_runs": len(tool_profiles),
        "code_line_runs": len(code_lines),
        "avg_minutes_solved": mean(solved["walls"]) / 60.0,
        "avg_input_tokens_m_solved": mean(solved["input"]) / 1e6,
        "avg_output_tokens_k_solved": mean(solved["output"]) / 1e3,
        "avg_tool_calls_solved": mean(
            [float(row["total"]) for row in solved["tools"]]
        ),
        "avg_tool_profile_solved": {
            key: mean([float(row[key]) for row in solved["tools"]])
            for key in ("total", "read", "write", "coqc", "vcg", "rounds")
        },
        "avg_generated_code_lines_solved": mean(solved["code"]),
        "avg_minutes_non_timeout": mean(non_timeout["walls"]) / 60.0,
        "avg_input_tokens_m_non_timeout": mean(non_timeout["input"]) / 1e6,
        "avg_output_tokens_k_non_timeout": mean(non_timeout["output"]) / 1e3,
        "avg_tool_calls_non_timeout": mean(
            [float(row["total"]) for row in non_timeout["tools"]]
        ),
        "avg_tool_profile_non_timeout": {
            key: mean([float(row[key]) for row in non_timeout["tools"]])
            for key in ("total", "read", "write", "coqc", "vcg", "rounds")
        },
        "solved_time_runs": len(solved["walls"]),
        "solved_token_runs": len(solved["input"]),
        "solved_trace_runs": len(solved["tools"]),
        "solved_code_line_runs": len(solved["code"]),
        "non_timeout_runs": counts["correct"] + counts["wrong"],
        "non_timeout_time_runs": len(non_timeout["walls"]),
        "non_timeout_token_runs": len(non_timeout["input"]),
        "non_timeout_trace_runs": len(non_timeout["tools"]),
        "per_task": per_task,
        "per_task_metrics": per_task_metrics,
        "selected_workspaces": selected_paths,
        "protocol_rejections": filtered_report,
    }


def summarize_pipeline(result_dir: Path, tasks: set[str]) -> dict[str, object]:
    """End-to-end branch: one pipeline_summary.json per pipeline_* workspace."""
    selected, protocol_report = selected_pipeline_workspaces(result_dir)
    rejected_tasks = {
        name: detail
        for name, detail in protocol_report["tasks"].items()
        if name in tasks
    }
    statuses: dict[str, str] = {}
    walls: list[float] = []
    solved_walls: list[float] = []
    solved_stage_walls: dict[str, list[float]] = {
        "contract": [],
        "eval": [],
        "verify": [],
    }
    solved_stage_task_minutes: dict[str, dict[str, float]] = {}
    verify_phase_task_minutes_solved: dict[str, dict[str, float | int]] = {}
    eval_verdicts: dict[str, str] = {}
    selected_paths: dict[str, str] = {}
    for name, ws in selected.items():
        if name not in tasks:
            continue
        selected_paths[name] = str(ws)
        summary_path = ws / "pipeline_summary.json"
        if not summary_path.exists():
            statuses[name] = "missing"
            continue
        try:
            payload = json.loads(summary_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            statuses[name] = "invalid"
            continue
        raw_status = str(payload.get("status", "unknown"))
        statuses[name] = raw_status
        if name in rejected_tasks:
            rejected_components = [
                component
                for component in rejected_tasks[name].get("components", [])
                if component.get("reasons")
            ]
            verify_rejected = any(
                Path(str(component.get("workspace", ""))).name.startswith("verify_")
                for component in rejected_components
            )
            statuses[name] = (
                "protocol_downstream_rejected"
                if verify_rejected
                else "protocol_contract_rejected"
            )
        if raw_status == "eval_gate_failed":
            # Older pipeline runs sometimes wrote the evaluator result under a
            # nested evaluation/ directory.  Inspect both layouts so a
            # plumbing failure is not mislabeled as a bad contract.
            verdict = "missing"
            for raw_workspace in payload.get("workspaces", []):
                workspace_name = Path(str(raw_workspace)).name
                if not workspace_name.startswith("eval_"):
                    continue
                eval_workspace = result_dir / workspace_name
                for verdict_path in sorted(eval_workspace.glob("**/final_result.md")):
                    verdict_text = verdict_path.read_text(encoding="utf-8", errors="replace")
                    match = re.search(r"^Spec verdict:\s*(\S+)", verdict_text, re.MULTILINE)
                    if match:
                        verdict = match.group(1)
                        if verdict == "Buggy":
                            break
                break
            eval_verdicts[name] = verdict
        if statuses[name] == "success":
            for raw_workspace in payload.get("workspaces", []):
                workspace_name = Path(str(raw_workspace)).name
                if not workspace_name.startswith("verify_"):
                    continue
                phases = phase_task_minutes(result_dir / workspace_name)
                if phases:
                    verify_phase_task_minutes_solved[name] = phases
                break
        cost_path = ws / "cost_summary.md"
        if cost_path.exists():
            cost_text = cost_path.read_text(encoding="utf-8", errors="replace")
            match = re.search(
                r"Total wall-clock \(sum of serial stages, seconds\): `([0-9.]+)`",
                cost_text,
            )
            if match:
                walls.append(float(match.group(1)))
                if statuses[name] == "success":
                    solved_walls.append(float(match.group(1)))
            if statuses[name] == "success":
                per_task: dict[str, float] = {}
                for line in cost_text.splitlines():
                    if not line.startswith("| ") or "**total**" in line:
                        continue
                    fields = [field.strip() for field in line.strip("|").split("|")]
                    if len(fields) < 6 or fields[0] not in solved_stage_walls:
                        continue
                    try:
                        seconds = float(fields[5])
                    except ValueError:
                        continue
                    solved_stage_walls[fields[0]].append(seconds)
                    per_task[fields[0]] = seconds / 60.0
                if per_task:
                    solved_stage_task_minutes[name] = per_task
    attempted = len(statuses)
    correct = sum(1 for s in statuses.values() if s == "success")
    status_counts = {
        status: sum(1 for value in statuses.values() if value == status)
        for status in sorted(set(statuses.values()))
    }
    return {
        "attempted": attempted,
        "correct": correct,
        "wrong": attempted - correct,
        "timeout": 0,
        "task_universe": len(tasks),
        "coverage": attempted / len(tasks),
        "attempted_accuracy": correct / attempted if attempted else 0.0,
        "source_yield": correct / 164,
        "avg_minutes": mean(walls) / 60.0,
        "avg_minutes_solved": mean(solved_walls) / 60.0,
        "solved_time_runs": len(solved_walls),
        "stage_avg_minutes_solved": {
            stage: mean(values) / 60.0
            for stage, values in solved_stage_walls.items()
        },
        "stage_task_minutes_solved": solved_stage_task_minutes,
        "verify_phase_task_minutes_solved": verify_phase_task_minutes_solved,
        "status_counts": status_counts,
        "eval_verdicts": eval_verdicts,
        "contract_quality_rejected": sum(1 for value in eval_verdicts.values() if value == "Buggy"),
        "eval_artifact_failures": sum(1 for value in eval_verdicts.values() if value != "Buggy"),
        "reached_verify": (
            status_counts.get("success", 0)
            + status_counts.get("audit_check_failed", 0)
            + status_counts.get("protocol_downstream_rejected", 0)
        ),
        "statuses": statuses,
        "selected_workspaces": selected_paths,
        "protocol_rejections": selection_report(
            rejected_tasks,
            {
                name: paths
                for name, paths in protocol_report["additional_complete_attempts_ignored"].items()
                if name in tasks
            },
            {
                name: paths
                for name, paths in protocol_report["incomplete_attempts_ignored"].items()
                if name in tasks
            },
        ),
    }


def summarize_proof_only(result_dir: Path, tasks: set[str]) -> dict[str, object]:
    selected, protocol_report = selected_workspaces(result_dir, "proof")
    selected = {
        n: ws
        for n, ws in selected.items()
        if n in tasks
    }


def successful_tool_profile(
    result_dir: Path,
    tasks: set[str],
    prefix: str,
    harness: str = "Codex CLI",
) -> dict[str, object]:
    """Mean trace activity over audited successful single-stage runs."""
    selected, report = selected_workspaces(result_dir, prefix)
    profiles: list[dict[str, int]] = []
    for name, workspace in selected.items():
        if name not in tasks or name in report["tasks"]:
            continue
        metrics_path = workspace / "logs" / "metrics.md"
        if not metrics_path.exists():
            continue
        text = metrics_path.read_text(encoding="utf-8", errors="replace")
        if classify(text) != "correct":
            continue
        profile = trace_tool_profile(workspace, harness)
        if profile is not None:
            profiles.append(profile)
    return {
        "runs": len(profiles),
        "profile": {
            key: mean([float(row[key]) for row in profiles])
            for key in ("total", "read", "write", "coqc", "vcg", "rounds")
        },
    }


def successful_tool_profiles_by_task(
    result_dir: Path,
    tasks: set[str],
    prefix: str,
    harness: str = "Codex CLI",
) -> dict[str, dict[str, int]]:
    """Per-task trace profiles for audited successful single-stage runs."""
    selected, report = selected_workspaces(result_dir, prefix)
    profiles: dict[str, dict[str, int]] = {}
    for name, workspace in selected.items():
        if name not in tasks or name in report["tasks"]:
            continue
        metrics_path = workspace / "logs" / "metrics.md"
        if not metrics_path.exists():
            continue
        text = metrics_path.read_text(encoding="utf-8", errors="replace")
        if classify(text) != "correct":
            continue
        profile = trace_tool_profile(workspace, harness)
        if profile is not None:
            profiles[name] = profile
    return profiles


def successful_token_profile(
    result_dir: Path,
    tasks: set[str],
    prefix: str,
) -> dict[str, object]:
    """Mean CLI token usage over audited successful single-stage runs."""
    selected, report = selected_workspaces(result_dir, prefix)
    rows: list[tuple[float, float]] = []
    for name, workspace in selected.items():
        if name not in tasks or name in report["tasks"]:
            continue
        metrics_path = workspace / "logs" / "metrics.md"
        if not metrics_path.exists():
            continue
        text = metrics_path.read_text(encoding="utf-8", errors="replace")
        if classify(text) != "correct":
            continue
        input_tokens = metric_float(text, "Agent CLI input_tokens")
        output_tokens = metric_float(text, "Agent CLI output_tokens")
        if input_tokens is not None or output_tokens is not None:
            rows.append((input_tokens or 0.0, output_tokens or 0.0))
    return {
        "runs": len(rows),
        "input_m": mean([row[0] for row in rows]) / 1_000_000.0 if rows else 0.0,
        "output_k": mean([row[1] for row in rows]) / 1_000.0 if rows else 0.0,
    }


def successful_tokens_by_task(
    result_dir: Path,
    tasks: set[str],
    prefix: str,
) -> dict[str, dict[str, float]]:
    """Per-task CLI tokens for audited successful single-stage runs."""
    selected, report = selected_workspaces(result_dir, prefix)
    rows: dict[str, dict[str, float]] = {}
    for name, workspace in selected.items():
        if name not in tasks or name in report["tasks"]:
            continue
        metrics_path = workspace / "logs" / "metrics.md"
        if not metrics_path.exists():
            continue
        text = metrics_path.read_text(encoding="utf-8", errors="replace")
        if classify(text) != "correct":
            continue
        input_tokens = metric_float(text, "Agent CLI input_tokens")
        output_tokens = metric_float(text, "Agent CLI output_tokens")
        if input_tokens is not None:
            rows[name] = {
                "input_m": input_tokens / 1_000_000.0,
                "output_k": (output_tokens or 0.0) / 1_000.0,
            }
    return rows


def successful_pipeline_token_profile(
    result_dir: Path,
    tasks: set[str],
) -> dict[str, object]:
    """Mean summed CLI tokens over audited successful end-to-end pipelines."""
    selected, report = selected_pipeline_workspaces(result_dir)
    rows: list[tuple[float, float]] = []
    for name, workspace in selected.items():
        if name not in tasks or name in report["tasks"]:
            continue
        payload = pipeline_payload(workspace) or {}
        if payload.get("status") != "success":
            continue
        input_tokens = 0.0
        output_tokens = 0.0
        found = False
        for raw_workspace in payload.get("workspaces", []):
            component = result_dir / Path(str(raw_workspace)).name
            metrics_path = component / "logs" / "metrics.md"
            if not metrics_path.exists():
                continue
            text = metrics_path.read_text(encoding="utf-8", errors="replace")
            component_input = metric_float(text, "Agent CLI input_tokens")
            component_output = metric_float(text, "Agent CLI output_tokens")
            if component_input is not None or component_output is not None:
                found = True
                input_tokens += component_input or 0.0
                output_tokens += component_output or 0.0
        if found:
            rows.append((input_tokens, output_tokens))
    return {
        "runs": len(rows),
        "input_m": mean([row[0] for row in rows]) / 1_000_000.0 if rows else 0.0,
        "output_k": mean([row[1] for row in rows]) / 1_000.0 if rows else 0.0,
    }


def combine_token_summaries(rows: list[dict[str, object]]) -> dict[str, object]:
    """Run-weighted combination of branch token summaries."""
    runs = sum(int(row.get("runs", 0)) for row in rows)
    return {
        "runs": runs,
        "input_m": (
            sum(float(row.get("input_m", 0.0)) * int(row.get("runs", 0)) for row in rows)
            / runs if runs else 0.0
        ),
        "output_k": (
            sum(float(row.get("output_k", 0.0)) * int(row.get("runs", 0)) for row in rows)
            / runs if runs else 0.0
        ),
    }


def successful_pipeline_tool_profile(
    result_dir: Path,
    tasks: set[str],
    harness: str = "Codex CLI",
) -> dict[str, object]:
    """Mean summed trace activity over successful end-to-end pipelines."""
    selected, report = selected_pipeline_workspaces(result_dir)
    profiles: list[dict[str, int]] = []
    keys = ("total", "read", "write", "coqc", "vcg", "rounds")
    stage_profiles: dict[str, list[dict[str, int]]] = defaultdict(list)
    for name, workspace in selected.items():
        if name not in tasks or name in report["tasks"]:
            continue
        payload = pipeline_payload(workspace) or {}
        if payload.get("status") != "success":
            continue
        combined = {key: 0 for key in keys}
        found = False
        for raw_workspace in payload.get("workspaces", []):
            component = result_dir / Path(str(raw_workspace)).name
            profile = trace_tool_profile(component, harness)
            if profile is None:
                continue
            found = True
            stage_profiles[component.name.split("_", 1)[0]].append(profile)
            for key in keys:
                combined[key] += int(profile[key])
        if found:
            profiles.append(combined)
    return {
        "runs": len(profiles),
        "profile": {
            key: mean([float(row[key]) for row in profiles])
            for key in keys
        },
        "stage_profiles": {
            stage: {
                key: mean([float(row[key]) for row in rows])
                for key in keys
            }
            for stage, rows in stage_profiles.items()
        },
        "stage_profile_runs": {
            stage: len(rows) for stage, rows in stage_profiles.items()
        },
    }


def combine_trace_summaries(rows: list[dict[str, object]]) -> dict[str, object]:
    """Run-weighted combination of branch trace summaries."""
    keys = ("total", "read", "write", "coqc", "vcg", "rounds")
    runs = sum(int(row.get("runs", 0)) for row in rows)
    profile = {
        key: (
            sum(
                float(row.get("profile", {}).get(key, 0.0))
                * int(row.get("runs", 0))
                for row in rows
            )
            / runs
            if runs else 0.0
        )
        for key in keys
    }
    stages = sorted({stage for row in rows for stage in row.get("stage_profiles", {})})
    stage_profiles = {}
    for stage in stages:
        stage_rows = [row for row in rows if stage in row.get("stage_profiles", {})]
        stage_runs = sum(
            int(row.get("stage_profile_runs", {}).get(stage, 0))
            for row in stage_rows
        )
        stage_profiles[stage] = {
            key: (
                sum(
                    float(row["stage_profiles"][stage].get(key, 0.0))
                    * int(row.get("stage_profile_runs", {}).get(stage, 0))
                    for row in stage_rows
                )
                / stage_runs
                if stage_runs else 0.0
            )
            for key in keys
        }
    return {"runs": runs, "profile": profile, "stage_profiles": stage_profiles}
    counts = {"correct": 0, "wrong": 0, "timeout": 0}
    walls: list[float] = []
    solved_walls: list[float] = []
    per_task: dict[str, str] = {}
    for name, ws in selected.items():
        metrics_path = ws / "logs" / "metrics.md"
        if not metrics_path.exists():
            continue
        text = metrics_path.read_text(encoding="utf-8", errors="replace")
        outcome = "wrong" if name in protocol_report["tasks"] else classify(text)
        counts[outcome] += 1
        per_task[name] = outcome
        wall = metric_float(text, "Wall-clock time (seconds)")
        if wall:
            walls.append(wall)
            if outcome == "correct":
                solved_walls.append(wall)
    attempted = sum(counts.values())
    rejected_tasks = {
        name: detail
        for name, detail in protocol_report["tasks"].items()
        if name in tasks
    }
    return {
        "attempted": attempted,
        "correct": counts["correct"],
        "wrong": counts["wrong"],
        "timeout": counts["timeout"],
        "task_universe": len(tasks),
        "coverage": attempted / len(tasks),
        "attempted_accuracy": counts["correct"] / attempted if attempted else 0.0,
        "source_yield": counts["correct"] / 164,
        "avg_minutes": mean(walls) / 60.0,
        "avg_minutes_solved": mean(solved_walls) / 60.0,
        "solved_time_runs": len(solved_walls),
        "per_task": per_task,
        "protocol_rejections": selection_report(
            rejected_tasks,
            {
                name: paths
                for name, paths in protocol_report["additional_complete_attempts_ignored"].items()
                if name in tasks
            },
            {
                name: paths
                for name, paths in protocol_report["incomplete_attempts_ignored"].items()
                if name in tasks
            },
        ),
    }


def stage_minutes_contract(result_dir: Path, tasks: set[str]) -> tuple[int, float]:
    walls: list[float] = []
    selected, _report = selected_workspaces(result_dir, "contract")
    for name, ws in selected.items():
        if name not in tasks:
            continue
        metrics_path = ws / "logs" / "metrics.md"
        if not metrics_path.exists():
            continue
        text = metrics_path.read_text(encoding="utf-8", errors="replace")
        wall = metric_float(text, "Wall-clock time (seconds)")
        if wall:
            walls.append(wall)
    return len(walls), mean(walls) / 60.0


def stage_task_minutes(result_dir: Path, tasks: set[str], prefix: str,
                       solved_only: bool = False) -> dict[str, float]:
    """Per-task wall-clock minutes (metrics.md, latest run per task) for one
    stage's result tree.  Same run selection as the aggregate stage averages,
    so the distribution figure and the quoted means can never disagree."""
    out: dict[str, float] = {}
    selected, report = selected_workspaces(result_dir, prefix)
    for name, ws in selected.items():
        if name not in tasks:
            continue
        metrics_path = ws / "logs" / "metrics.md"
        if not metrics_path.exists():
            continue
        text = metrics_path.read_text(encoding="utf-8", errors="replace")
        if solved_only:
            ok = name not in report["tasks"] and (
                metric_value(text, "Status") == "Success"
                if prefix == "contract"
                else classify(text) == "correct"
            )
            if not ok:
                continue
        wall = metric_float(text, "Wall-clock time (seconds)")
        if wall:
            out[name] = wall / 60.0
    return out


def stage_task_phase_minutes(
    result_dir: Path,
    tasks: set[str],
    prefix: str,
    *,
    proof_only: bool = False,
    admitted_only: bool = True,
) -> dict[str, dict[str, float | int]]:
    """Trace-derived annotation/proof split for audited successful runs."""
    out: dict[str, dict[str, float | int]] = {}
    selected, report = selected_workspaces(result_dir, prefix)
    for name, workspace in selected.items():
        if name not in tasks:
            continue
        metrics_path = workspace / "logs" / "metrics.md"
        if not metrics_path.exists():
            continue
        text = metrics_path.read_text(encoding="utf-8", errors="replace")
        if (admitted_only and name in report["tasks"]) or classify(text) != "correct":
            continue
        phases = phase_task_minutes(workspace, proof_only=proof_only)
        if phases:
            out[name] = phases
    return out


def runner_success_pipeline_timings(
    result_dir: Path,
    tasks: set[str],
) -> tuple[dict[str, dict[str, float]], dict[str, dict[str, float | int]]]:
    """Raw successful timing traces for the fixed descriptive cohort.

    External audit rejections still override effectiveness outcomes.  Timing
    retains runner-success traces because Fig. 4 describes where elapsed time
    was spent in the historically fixed 127-program cohort.
    """
    selected, _report = selected_pipeline_workspaces(result_dir)
    stage_rows: dict[str, dict[str, float]] = {}
    phases: dict[str, dict[str, float | int]] = {}
    for name, workspace in selected.items():
        if name not in tasks:
            continue
        payload = pipeline_payload(workspace) or {}
        if payload.get("status") != "success":
            continue
        cost_path = workspace / "cost_summary.md"
        row: dict[str, float] = {}
        if cost_path.exists():
            for line in cost_path.read_text(encoding="utf-8", errors="replace").splitlines():
                if not line.startswith("| ") or "**total**" in line:
                    continue
                fields = [field.strip() for field in line.strip("|").split("|")]
                if len(fields) < 6 or fields[0] not in {"contract", "eval", "verify"}:
                    continue
                try:
                    row[fields[0]] = float(fields[5]) / 60.0
                except ValueError:
                    continue
        for raw_workspace in payload.get("workspaces", []):
            component = result_dir / Path(str(raw_workspace)).name
            if not component.name.startswith("verify_"):
                continue
            phase_row = phase_task_minutes(component)
            if phase_row:
                phases[name] = phase_row
            break
        if row and name in phases:
            stage_rows[name] = row
    return stage_rows, phases


def config_key(harness: str, model: str, effort: str) -> str:
    return f"{harness}|{model}|{effort}"


def weighted_rows(rows: list[dict[str, object]], value: str, weight: str) -> float:
    denominator = sum(int(row.get(weight, 0)) for row in rows)
    if not denominator:
        return 0.0
    return sum(
        float(row.get(value, 0.0)) * int(row.get(weight, 0))
        for row in rows
    ) / denominator


def weighted_tool_profile(
    rows: list[dict[str, object]], value: str, weight: str
) -> dict[str, float]:
    denominator = sum(int(row.get(weight, 0)) for row in rows)
    if not denominator:
        return {
            key: 0.0
            for key in ("total", "read", "write", "coqc", "vcg", "rounds")
        }
    return {
        key: sum(
            float(row.get(value, {}).get(key, 0.0)) * int(row.get(weight, 0))
            for row in rows
        ) / denominator
        for key in ("total", "read", "write", "coqc", "vcg", "rounds")
    }


def combine_primary_rows(rows: list[dict[str, object]]) -> dict[str, object]:
    attempted = sum(int(row["attempted"]) for row in rows)
    correct = sum(int(row["correct"]) for row in rows)
    wrong = sum(int(row["wrong"]) for row in rows)
    timeout = sum(int(row["timeout"]) for row in rows)
    rejections: dict[str, dict[str, object]] = {}
    extra_complete: dict[str, list[str]] = {}
    incomplete: dict[str, list[str]] = {}
    per_task: dict[str, str] = {}
    selected_paths: dict[str, str] = {}
    for row in rows:
        per_task.update(row.get("per_task", {}))
        selected_paths.update(row.get("selected_workspaces", {}))
        report = row.get("protocol_rejections", {})
        rejections.update(report.get("tasks", {}))
        extra_complete.update(report.get("additional_complete_attempts_ignored", {}))
        incomplete.update(report.get("incomplete_attempts_ignored", {}))
    return {
        "attempted": attempted,
        # Backward-compatible table fields: the visible denominator is the
        # complete 164-program source universe; coverage uses runnable=132.
        "task_universe": 164,
        "benchmark_task_count": 132,
        "runnable_universe": 132,
        "source_universe": 164,
        "construction_excluded": 32,
        "correct": correct,
        "wrong": wrong,
        "timeout": timeout,
        "coverage": attempted / 132,
        "attempted_accuracy": correct / attempted if attempted else 0.0,
        "source_yield": correct / 164,
        "runnable_yield": correct / 132,
        # The aggregate figure/table accuracy is deliberately source yield.
        "accuracy": correct / 164,
        "avg_minutes": weighted_rows(rows, "avg_minutes", "time_runs"),
        "avg_input_tokens_m": weighted_rows(rows, "avg_input_tokens_m", "token_runs"),
        "avg_output_tokens_k": weighted_rows(rows, "avg_output_tokens_k", "token_runs"),
        "avg_total_tokens_m": weighted_rows(rows, "avg_total_tokens_m", "token_runs"),
        "avg_tool_calls": weighted_rows(rows, "avg_tool_calls", "trace_runs"),
        "avg_tool_profile": weighted_tool_profile(
            rows, "avg_tool_profile", "trace_runs"
        ),
        "avg_minutes_solved": weighted_rows(rows, "avg_minutes_solved", "solved_time_runs"),
        "avg_input_tokens_m_solved": weighted_rows(
            rows, "avg_input_tokens_m_solved", "solved_token_runs"
        ),
        "avg_output_tokens_k_solved": weighted_rows(
            rows, "avg_output_tokens_k_solved", "solved_token_runs"
        ),
        "avg_tool_calls_solved": weighted_rows(
            rows, "avg_tool_calls_solved", "solved_trace_runs"
        ),
        "avg_tool_profile_solved": weighted_tool_profile(
            rows, "avg_tool_profile_solved", "solved_trace_runs"
        ),
        "avg_minutes_non_timeout": weighted_rows(
            rows, "avg_minutes_non_timeout", "non_timeout_time_runs"
        ),
        "avg_input_tokens_m_non_timeout": weighted_rows(
            rows, "avg_input_tokens_m_non_timeout", "non_timeout_token_runs"
        ),
        "avg_output_tokens_k_non_timeout": weighted_rows(
            rows, "avg_output_tokens_k_non_timeout", "non_timeout_token_runs"
        ),
        "avg_tool_calls_non_timeout": weighted_rows(
            rows, "avg_tool_calls_non_timeout", "non_timeout_trace_runs"
        ),
        "avg_tool_profile_non_timeout": weighted_tool_profile(
            rows, "avg_tool_profile_non_timeout", "non_timeout_trace_runs"
        ),
        "time_runs": sum(int(row.get("time_runs", 0)) for row in rows),
        "token_runs": sum(int(row.get("token_runs", 0)) for row in rows),
        "trace_runs": sum(int(row.get("trace_runs", 0)) for row in rows),
        "solved_time_runs": sum(int(row.get("solved_time_runs", 0)) for row in rows),
        "solved_token_runs": sum(int(row.get("solved_token_runs", 0)) for row in rows),
        "solved_trace_runs": sum(int(row.get("solved_trace_runs", 0)) for row in rows),
        "non_timeout_runs": sum(int(row.get("non_timeout_runs", 0)) for row in rows),
        "non_timeout_time_runs": sum(int(row.get("non_timeout_time_runs", 0)) for row in rows),
        "non_timeout_token_runs": sum(int(row.get("non_timeout_token_runs", 0)) for row in rows),
        "non_timeout_trace_runs": sum(int(row.get("non_timeout_trace_runs", 0)) for row in rows),
        "per_task": dict(sorted(per_task.items())),
        "selected_workspaces": dict(sorted(selected_paths.items())),
        "protocol_rejections": selection_report(rejections, extra_complete, incomplete),
    }


def main() -> None:
    with_traces = "--fast" not in sys.argv
    c_tasks = ground_truth_tasks(C_ROOT)
    dlc_tasks = ground_truth_tasks(DLC_ROOT)
    if (len(c_tasks), len(dlc_tasks)) != (102, 30):
        raise RuntimeError(
            "unexpected runnable corpus: "
            f"core={len(c_tasks)}, extension={len(dlc_tasks)}; expected 102+30"
        )

    snapshot: dict[str, object] = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "source_task_count": 164,
        "benchmark_task_count": len(c_tasks) + len(dlc_tasks),
        "core_task_count": len(c_tasks),
        "extension_task_count": len(dlc_tasks),
        "construction_exclusion_count": 32,
        "admission_policy": {
            "attempt": "earliest complete metrics workspace per configuration and task",
            "later_complete_workspaces": "reported and ignored",
            "protocol_rejection_outcome": "wrong (overrides success and timeout)",
            "protocol_rejection_reasons": [
                "transcript_leakage",
                "legacy_multiple_invocations",
                "missing_transcript",
                "artifact_audit_failure",
            ],
            "transcript_audit": "corpus scripts/check_leakage.py",
            "artifact_audit": "corpus scripts/check_verify_audit.py::scan_workspace",
        },
        "primary_core": {},
        "primary_extension": {},
        "primary_combined": {},
        "harness_sensitivity": {},
        "harness_sensitivity_design": {
            "selection_harness": "Claude Code",
            "selection_rule": "audited-success intersection of both models",
            "cohort_tasks": HARNESS_CLAUDE_SHARED_TASKS,
            "cost_rule": "intersection of audited successes across all six model-harness configurations",
            "shared_success_tasks": [],
        },
    }

    for harness_key, harness, model, effort, result_dir in CONFIGS_C:
        row = summarize_config(harness_key, result_dir, c_tasks, with_traces)
        if row:
            row.update({"harness": harness, "model": model, "effort": effort})
            snapshot["primary_core"][config_key(harness, model, effort)] = row
            print(f"C   {harness} {model} {effort}: {row['correct']}/{row['attempted']} "
                  f"({row['accuracy']*100:.1f}%) avg {row['avg_minutes']:.1f} min")

    for harness_key, harness, model, effort, result_dir in CONFIGS_DLC:
        row = summarize_config(harness_key, result_dir, dlc_tasks, with_traces)
        if row:
            row.update({"harness": harness, "model": model, "effort": effort})
            snapshot["primary_extension"][config_key(harness, model, effort)] = row
            print(f"DLC {harness} {model} {effort}: {row['correct']}/{row['attempted']} "
                  f"({row['accuracy']*100:.1f}%) avg {row['avg_minutes']:.1f} min")

    for key in sorted(set(snapshot["primary_core"]) | set(snapshot["primary_extension"])):
        parts = [
            split[key]
            for split in (snapshot["primary_core"], snapshot["primary_extension"])
            if key in split
        ]
        combined = combine_primary_rows(parts)
        harness, model, effort = key.split("|", 2)
        combined.update({"harness": harness, "model": model, "effort": effort})
        snapshot["primary_combined"][key] = combined
        print(
            f"ALL {harness} {model} {effort}: attempted={combined['attempted']}/132 "
            f"correct={combined['correct']} attempted-accuracy="
            f"{combined['attempted_accuracy']*100:.1f}% source-yield="
            f"{combined['source_yield']*100:.1f}% protocol-rejections="
            f"{combined['protocol_rejections']['count']}"
        )

    # Branch tasks under Codex GPT-5.4 medium across the 132 runnable tasks.
    snapshot["endtoend_core_gpt54_medium"] = summarize_pipeline(
        C_ROOT / "pipeline_results/codex/gpt-5.4/medium", c_tasks
    )
    snapshot["endtoend_extension_gpt54_medium"] = summarize_pipeline(
        DLC_ROOT / "pipeline_results/codex/gpt-5.4/medium", dlc_tasks
    )
    snapshot["proofonly_core_gpt54_medium"] = summarize_proof_only(
        C_ROOT / "proof_results/codex/gpt-5.4/medium", c_tasks
    )
    snapshot["proofonly_extension_gpt54_medium"] = summarize_proof_only(
        DLC_ROOT / "proof_results/codex/gpt-5.4/medium", dlc_tasks
    )
    e2e_trace = combine_trace_summaries([
        successful_pipeline_tool_profile(
            C_ROOT / "pipeline_results/codex/gpt-5.4/medium", c_tasks
        ),
        successful_pipeline_tool_profile(
            DLC_ROOT / "pipeline_results/codex/gpt-5.4/medium", dlc_tasks
        ),
    ])
    proof_trace = combine_trace_summaries([
        successful_tool_profile(
            C_ROOT / "proof_results/codex/gpt-5.4/medium", c_tasks, "proof"
        ),
        successful_tool_profile(
            DLC_ROOT / "proof_results/codex/gpt-5.4/medium", dlc_tasks, "proof"
        ),
    ])
    primary_trace_row = snapshot["primary_combined"].get(
        config_key("Codex", "GPT-5.4", "medium"), {}
    )
    snapshot["branch_interaction_gpt54_medium"] = {
        "end_to_end": e2e_trace,
        "primary": {
            "runs": int(primary_trace_row.get("solved_trace_runs", 0)),
            "profile": primary_trace_row.get("avg_tool_profile_solved", {}),
        },
        "proof_only": proof_trace,
    }
    e2e_tokens = combine_token_summaries([
        successful_pipeline_token_profile(
            C_ROOT / "pipeline_results/codex/gpt-5.4/medium", c_tasks
        ),
        successful_pipeline_token_profile(
            DLC_ROOT / "pipeline_results/codex/gpt-5.4/medium", dlc_tasks
        ),
    ])
    proof_tokens = combine_token_summaries([
        successful_token_profile(
            C_ROOT / "proof_results/codex/gpt-5.4/medium", c_tasks, "proof"
        ),
        successful_token_profile(
            DLC_ROOT / "proof_results/codex/gpt-5.4/medium", dlc_tasks, "proof"
        ),
    ])
    snapshot["branch_tokens_gpt54_medium"] = {
        "end_to_end": e2e_tokens,
        "primary": {
            "runs": int(primary_trace_row.get("solved_token_runs", 0)),
            "input_m": float(primary_trace_row.get("avg_input_tokens_m_solved", 0.0)),
            "output_k": float(primary_trace_row.get("avg_output_tokens_k_solved", 0.0)),
        },
        "proof_only": proof_tokens,
    }
    primary_tokens_by_task = {}
    proof_tokens_by_task = {}
    for root, tasks in ((C_ROOT, c_tasks), (DLC_ROOT, dlc_tasks)):
        primary_tokens_by_task.update(successful_tokens_by_task(
            root / "results/codex/gpt-5.4/medium", tasks, "verify"
        ))
        proof_tokens_by_task.update(successful_tokens_by_task(
            root / "proof_results/codex/gpt-5.4/medium", tasks, "proof"
        ))
    paired_token_tasks = sorted(set(primary_tokens_by_task) & set(proof_tokens_by_task))
    snapshot["branch_paired_tokens_gpt54_medium"] = {
        "runs": len(paired_token_tasks),
        "tasks": {
            name: {
                "primary": primary_tokens_by_task[name],
                "proof_only": proof_tokens_by_task[name],
            }
            for name in paired_token_tasks
        },
    }
    primary_tools_by_task = {}
    proof_tools_by_task = {}
    for root, tasks in ((C_ROOT, c_tasks), (DLC_ROOT, dlc_tasks)):
        primary_tools_by_task.update(successful_tool_profiles_by_task(
            root / "results/codex/gpt-5.4/medium", tasks, "verify"
        ))
        proof_tools_by_task.update(successful_tool_profiles_by_task(
            root / "proof_results/codex/gpt-5.4/medium", tasks, "proof"
        ))
    paired_trace_tasks = [
        name for name in paired_token_tasks
        if name in primary_tools_by_task and name in proof_tools_by_task
    ]
    snapshot["branch_paired_tokens_gpt54_medium"]["summary"] = {
        "primary": {
            "input_m": mean([primary_tokens_by_task[name]["input_m"] for name in paired_token_tasks]),
            "output_k": mean([primary_tokens_by_task[name]["output_k"] for name in paired_token_tasks]),
            "tool_calls": mean([primary_tools_by_task[name]["total"] for name in paired_trace_tasks]),
        },
        "proof_only": {
            "input_m": mean([proof_tokens_by_task[name]["input_m"] for name in paired_token_tasks]),
            "output_k": mean([proof_tokens_by_task[name]["output_k"] for name in paired_token_tasks]),
            "tool_calls": mean([proof_tools_by_task[name]["total"] for name in paired_trace_tasks]),
        },
    }
    contract_runs, contract_min = stage_minutes_contract(
        C_ROOT / "pipeline_results/codex/gpt-5.4/medium", c_tasks
    )
    primary_row = snapshot["primary_core"].get(config_key("Codex", "GPT-5.4", "medium")) or {}
    snapshot["stage_minutes_gpt54_medium"] = {
        "contract_runs": contract_runs,
        "contract": contract_min,
        "annotation_plus_proof": primary_row.get("avg_minutes", 0.0),
        "proof_only": snapshot["proofonly_core_gpt54_medium"]["avg_minutes"],
    }
    snapshot["stage_task_minutes_gpt54_medium"] = {
        "contract": stage_task_minutes(
            C_ROOT / "pipeline_results/codex/gpt-5.4/medium", c_tasks, "contract"),
        "primary": stage_task_minutes(
            C_ROOT / "results/codex/gpt-5.4/medium", c_tasks, "verify"),
        "proof": stage_task_minutes(
            C_ROOT / "proof_results/codex/gpt-5.4/medium", c_tasks, "proof"),
    }
    snapshot["stage_task_minutes_solved_gpt54_medium"] = {
        "contract": stage_task_minutes(
            C_ROOT / "pipeline_results/codex/gpt-5.4/medium", c_tasks, "contract", solved_only=True),
        "primary": stage_task_minutes(
            C_ROOT / "results/codex/gpt-5.4/medium", c_tasks, "verify", solved_only=True),
        "proof": stage_task_minutes(
            C_ROOT / "proof_results/codex/gpt-5.4/medium", c_tasks, "proof", solved_only=True),
    }

    e2e_core = snapshot["endtoend_core_gpt54_medium"]
    e2e_extension = snapshot["endtoend_extension_gpt54_medium"]
    timing_dlc_tasks = dlc_tasks - BRANCH_TIMING_EXTENSION_EXCLUDED
    if len(timing_dlc_tasks) != 25:
        raise RuntimeError(
            "Fig. 4 timing cohort drifted: expected 25 original DLC tasks, "
            f"found {len(timing_dlc_tasks)}"
        )
    e2e_stage_core_timing, e2e_phase_core_timing = runner_success_pipeline_timings(
        C_ROOT / "pipeline_results/codex/gpt-5.4/medium", c_tasks
    )
    e2e_stage_extension_timing, e2e_phase_extension_timing = (
        runner_success_pipeline_timings(
            DLC_ROOT / "pipeline_results/codex/gpt-5.4/medium", timing_dlc_tasks
        )
    )
    primary_phase_core = stage_task_phase_minutes(
        C_ROOT / "results/codex/gpt-5.4/medium",
        c_tasks,
        "verify",
        admitted_only=False,
    )
    primary_phase_extension = stage_task_phase_minutes(
        DLC_ROOT / "results/codex/gpt-5.4/medium",
        timing_dlc_tasks,
        "verify",
        admitted_only=False,
    )
    proof_phase_core = stage_task_phase_minutes(
        C_ROOT / "proof_results/codex/gpt-5.4/medium",
        c_tasks,
        "proof",
        proof_only=True,
        admitted_only=False,
    )
    proof_phase_extension = stage_task_phase_minutes(
        DLC_ROOT / "proof_results/codex/gpt-5.4/medium",
        timing_dlc_tasks,
        "proof",
        proof_only=True,
        admitted_only=False,
    )
    snapshot["stage_phase_task_minutes_solved_gpt54_medium"] = {
        "end_to_end": {
            **e2e_phase_core_timing,
            **e2e_phase_extension_timing,
        },
        "primary": {**primary_phase_core, **primary_phase_extension},
        "proof_only": {**proof_phase_core, **proof_phase_extension},
    }

    # Directly observed, additive successful-run timing blocks for Fig. 4.
    # Annotation/proof boundaries follow the recorded VCG/coqc cycles.
    phase_tasks = snapshot["stage_phase_task_minutes_solved_gpt54_medium"]
    e2e_phases = phase_tasks["end_to_end"]
    primary_phases = phase_tasks["primary"]
    proof_phases = phase_tasks["proof_only"]
    e2e_stage_tasks = {
        **e2e_stage_core_timing,
        **e2e_stage_extension_timing,
    }
    e2e_stage_rows = [e2e_stage_tasks[name] for name in e2e_phases]
    e2e_contract_generation = mean(
        [float(row.get("contract", 0.0)) for row in e2e_stage_rows]
    )
    e2e_annotation_acceptance = mean(
        [float(row.get("eval", 0.0)) for row in e2e_stage_rows]
    )
    e2e_annotation = e2e_annotation_acceptance + mean(
        [float(row["annotation"]) for row in e2e_phases.values()]
    )
    e2e_proof = mean([float(row["proof"]) for row in e2e_phases.values()])
    primary_annotation = mean([float(row["annotation"]) for row in primary_phases.values()])
    primary_proof = mean([float(row["proof"]) for row in primary_phases.values()])
    proof_only_proof = mean([float(row["proof"]) for row in proof_phases.values()])
    paired_tasks = sorted(
        set(primary_phases) & set(proof_phases)
    )
    paired_primary_annotation = mean(
        [float(primary_phases[name]["annotation"]) for name in paired_tasks]
    )
    paired_primary_proof = mean(
        [float(primary_phases[name]["proof"]) for name in paired_tasks]
    )
    paired_proof_only = mean(
        [float(proof_phases[name]["proof"]) for name in paired_tasks]
    )
    paired_primary_total = paired_primary_annotation + paired_primary_proof
    snapshot["branch_time_profile_gpt54_medium"] = {
        "cohort": {
            "runnable_tasks": 127,
            "policy": "earliest-complete runner-success traces in the fixed original cohort",
            "later_dlc_tasks_excluded": sorted(BRANCH_TIMING_EXTENSION_EXCLUDED),
        },
        "end_to_end": {
            "runs": len(e2e_phases),
            # The evaluator/acceptance interval is part of annotation work:
            # it checks whether the generated contract supports the annotated
            # program.  Contract itself is only the generation interval.
            "contract": e2e_contract_generation,
            "annotation": e2e_annotation,
            "proof": e2e_proof,
            "total": e2e_contract_generation + e2e_annotation + e2e_proof,
        },
        "primary": {
            "runs": len(primary_phases),
            "contract": 0.0,
            "annotation": primary_annotation,
            "proof": primary_proof,
            "total": primary_annotation + primary_proof,
        },
        "proof_only": {
            "runs": len(proof_phases),
            "contract": 0.0,
            "annotation": 0.0,
            "proof": proof_only_proof,
            "total": proof_only_proof,
        },
        "paired_primary_proof": {
            "runs": len(paired_tasks),
            "primary_annotation": paired_primary_annotation,
            "primary_proof": paired_primary_proof,
            "primary": paired_primary_total,
            "proof_only": paired_proof_only,
            "difference": paired_primary_total - paired_proof_only,
            "relative_increase": (
                (paired_primary_total - paired_proof_only) / paired_proof_only
                if paired_proof_only else 0.0
            ),
        },
        "missing_rollout_timestamps": {
            branch: sum(int(row["missing_rollouts"]) for row in rows.values())
            for branch, rows in phase_tasks.items()
        },
    }
    snapshot["branch_paired_tokens_gpt54_medium"]["summary"]["primary"]["minutes"] = paired_primary_total
    snapshot["branch_paired_tokens_gpt54_medium"]["summary"]["proof_only"]["minutes"] = paired_proof_only

    # Fig. 4 uses the full 164-program HumanEval universe.  Construction
    # exclusions and branch runs not yet attempted remain separate from agent
    # failures so verifier scope is never attributed to the model.
    source_total = int(snapshot["source_task_count"])
    benchmark_total = int(snapshot["benchmark_task_count"])
    construction_excluded = source_total - benchmark_total
    primary_extension_row = (
        snapshot["primary_extension"].get(config_key("Codex", "GPT-5.4", "medium"))
        or {}
    )
    proof_core = snapshot["proofonly_core_gpt54_medium"]
    proof_extension = snapshot["proofonly_extension_gpt54_medium"]

    e2e_attempted = int(e2e_core["attempted"]) + int(e2e_extension["attempted"])
    e2e_correct = int(e2e_core["correct"]) + int(e2e_extension["correct"])
    e2e_downstream = sum(
        int(row["status_counts"].get("audit_check_failed", 0))
        + int(row["status_counts"].get("protocol_downstream_rejected", 0))
        for row in (e2e_core, e2e_extension)
    )
    e2e_contract_error = e2e_attempted - e2e_correct - e2e_downstream

    primary_attempted = int(primary_row.get("attempted", 0)) + int(
        primary_extension_row.get("attempted", 0)
    )
    primary_correct = int(primary_row.get("correct", 0)) + int(
        primary_extension_row.get("correct", 0)
    )
    proof_attempted = int(proof_core["attempted"]) + int(proof_extension["attempted"])
    proof_correct = int(proof_core["correct"]) + int(proof_extension["correct"])
    snapshot["branch_outcomes_gpt54_medium"] = {
        "end_to_end": {
            "total": source_total,
            "attempted": e2e_attempted,
            "correct": e2e_correct,
            "downstream_fail": e2e_downstream,
            "contract_error": e2e_contract_error,
            "not_run": benchmark_total - e2e_attempted,
            "construction_excluded": construction_excluded,
        },
        "primary": {
            "total": source_total,
            "attempted": primary_attempted,
            "correct": primary_correct,
            "downstream_fail": primary_attempted - primary_correct,
            "contract_error": 0,
            "not_run": benchmark_total - primary_attempted,
            "construction_excluded": construction_excluded,
        },
        "proof_only": {
            "total": source_total,
            "attempted": proof_attempted,
            "correct": proof_correct,
            "downstream_fail": proof_attempted - proof_correct,
            "contract_error": 0,
            "not_run": benchmark_total - proof_attempted,
            "construction_excluded": construction_excluded,
        },
    }

    # Harness/model comparison on tasks accepted by both models under Claude
    # Code.  The cohort is fixed before inspecting Codex/OpenCode outcomes.
    for snapshot_key, harness_key, model, result_dir in HARNESS_CONFIGS:
        row = summarize_config(
            harness_key,
            result_dir,
            set(HARNESS_CLAUDE_SHARED_TASKS),
            with_traces,
            with_code_lines=True,
        )
        if row:
            row.update({"harness": harness_key, "model": model})
            snapshot["harness_sensitivity"][snapshot_key] = row
            print(f"HARNESS {snapshot_key}: {row['correct']}/{row['attempted']}")

    harness_rows = list(snapshot["harness_sensitivity"].values())
    if len(harness_rows) == len(HARNESS_CONFIGS):
        shared_successes = set(HARNESS_CLAUDE_SHARED_TASKS)
        for row in harness_rows:
            shared_successes &= {
                task
                for task, outcome in row.get("per_task", {}).items()
                if outcome == "correct"
            }
        snapshot["harness_sensitivity_design"]["shared_success_tasks"] = sorted(
            shared_successes
        )
        print(
            "HARNESS six-way shared successes: "
            + ", ".join(sorted(shared_successes))
        )

    e2e = snapshot["endtoend_core_gpt54_medium"]
    po = snapshot["proofonly_core_gpt54_medium"]
    print(f"End-to-end GPT-5.4 medium: {e2e['correct']}/{e2e['attempted']}")
    print(f"Proof-only GPT-5.4 medium: {po['correct']}/{po['attempted']} avg {po['avg_minutes']:.1f} min")
    sm = snapshot["stage_minutes_gpt54_medium"]
    print(f"Stage minutes: contract {sm['contract']:.1f} ({sm['contract_runs']} runs), "
          f"annotation+proof {sm['annotation_plus_proof']:.1f}, proof {sm['proof_only']:.1f}")

    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    out_path = FIGURES_DIR / "stats_snapshot.json"
    out_path.write_text(json.dumps(snapshot, indent=1, sort_keys=True), encoding="utf-8")
    print(f"wrote {out_path}")


if __name__ == "__main__":
    main()
