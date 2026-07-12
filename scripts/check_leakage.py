#!/usr/bin/env python3
"""Standalone transcript audit for answer/workspace leakage.

This is the single leakage scanner. It checks ``agent_stdout_*.jsonl`` for
tool calls that read answer-bearing or cross-run paths. It is intentionally
separate from ``check_verify_audit.py`` and is not called by ``run_verify.py``
or ``run_proof.py`` because leakage is a process-compliance issue; it does not
by itself prove that the final Coq artifact is invalid.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import json
from pathlib import Path
import re
import sys
from typing import Any, Iterable


WORKSPACE_RE = re.compile(r"verify_\d{8}_\d+_[A-Za-z0-9_]+")

READ_TOOLS = {"read", "readfile", "grep", "glob", "search", "searchfiles", "list", "ls"}
WRITE_TOOLS = {"edit", "write", "multiedit", "strreplacefile", "writefile"}
READISH_BASH_RE = re.compile(
    r"\b(cat|head|tail|sed|less|more|nl|awk|grep|rg|find|ls|stat|wc|"
    r"diff|cmp|python3?|perl|sort|cp)\b"
)

GROUND_TRUTH_PATH_RE = re.compile(
    r"(?:^|[/\s\"'`])ground_truth(?:[_/A-Za-z0-9.-]|$)|"
    r"(?:QCP_examples|SeparationLogic/examples)/CAV/ground_truth"
)
RESULTS_PATH_RE = re.compile(r"(?:^|[\s\"'`])(?:\./)?results/|/results/")
OUTPUT_VERIFY_RE = re.compile(
    r"(?:^|[\s\"'`])(?:\./)?output/(verify_\d{8}_\d+_[A-Za-z0-9_]+)|"
    r"/output/(verify_\d{8}_\d+_[A-Za-z0-9_]+)"
)
ANNOTATED_INPUT_RE = re.compile(r"(?:^|[\s\"'`])(?:\./)?annotated_input/|/annotated_input/")
REPO_ANNOTATED_RE = re.compile(r"(?:^|[\s\"'`])(?:\./)?annotated/verify_|/annotated/verify_")

CAV_WORKSPACE_RE = re.compile(
    r"(?:QCP_examples|SeparationLogic/examples)/CAV/"
    r"(verify_\d{8}_\d+_[A-Za-z0-9_]+|ground_truth[A-Za-z0-9_]*)"
)
CAV_GLOB_RE = re.compile(
    r"(?:QCP_examples|SeparationLogic/examples)/CAV/"
    r"([^/\s\"'`]+)(?:/[^ \t\r\n\"'`]*)?[*?]"
)
CAV_PARENT_SCAN_RE = re.compile(
    r"\b(?:find|ls|rg|grep)\s+[^;\n|&]*"
    r"(?:QCP_examples|SeparationLogic/examples)/CAV/?(?:\s|$)"
)


@dataclass
class Finding:
    case: str
    transcript: str
    line: int
    tool: str
    category: str
    severity: str
    snippet: str
    message: str


def current_workspace_from_path(path: Path) -> str | None:
    match = WORKSPACE_RE.search(str(path))
    return match.group(0) if match else None


def discover_transcripts(paths: Iterable[Path]) -> list[Path]:
    found: list[Path] = []
    for path in paths:
        if path.is_file():
            if path.name.startswith("agent_stdout_") and path.suffix == ".jsonl":
                found.append(path)
            continue
        if path.is_dir():
            found.extend(path.glob("**/logs/agent_stdout_*.jsonl"))
    return sorted(set(found))


def iter_tool_uses(transcript: Path):
    for line_no, raw in enumerate(transcript.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
        if not raw.lstrip().startswith("{"):
            continue
        try:
            obj = json.loads(raw)
        except json.JSONDecodeError:
            continue
        # Claude stream-json.
        if obj.get("type") == "assistant":
            message = obj.get("message") or {}
            for item in message.get("content") or []:
                if not isinstance(item, dict) or item.get("type") != "tool_use":
                    continue
                yield line_no, item.get("name") or "<unknown>", item.get("input") or {}

        # Codex JSONL.  Scan completed commands to avoid counting each command
        # twice (item.started + item.completed).
        if obj.get("type") == "item.completed":
            item = obj.get("item") or {}
            if item.get("type") == "command_execution":
                yield line_no, "Bash", {"command": item.get("command") or ""}

        # Kimi Code stream-json/OpenAI-style function calls.
        if obj.get("role") == "assistant":
            for call in obj.get("tool_calls") or []:
                function = call.get("function") if isinstance(call, dict) else None
                if not isinstance(function, dict):
                    continue
                raw_args = function.get("arguments") or {}
                if isinstance(raw_args, str):
                    try:
                        raw_args = json.loads(raw_args)
                    except json.JSONDecodeError:
                        raw_args = {"arguments": raw_args}
                yield line_no, function.get("name") or "<unknown>", raw_args

        # OpenCode JSON events.
        if obj.get("type") == "tool":
            state = obj.get("state") or {}
            yield line_no, obj.get("tool") or "<unknown>", state.get("input") or {}


def tool_input_text(tool: str, tool_input: Any) -> str:
    if not isinstance(tool_input, dict):
        return str(tool_input)
    if tool == "Bash":
        return str(tool_input.get("command") or "")
    pieces: list[str] = []
    for key, value in tool_input.items():
        if isinstance(value, str):
            pieces.append(f"{key}={value}")
        else:
            pieces.append(f"{key}={value!r}")
    return " ".join(pieces)


def write_target_text(tool_input: Any) -> str:
    """Return only path-like fields for non-shell write tools.

    Scanning replacement/content payloads would flag a clean agent merely for
    documenting a forbidden path in ``issues.md``.  The destination path is
    what matters for a write-boundary violation.
    """
    if not isinstance(tool_input, dict):
        return str(tool_input)
    path_keys = {"path", "file_path", "filepath", "filePath", "target", "destination"}
    return " ".join(
        f"{key}={value}"
        for key, value in tool_input.items()
        if key in path_keys and isinstance(value, str)
    )


def is_read_like(tool: str, text: str) -> bool:
    normalized = tool.lower()
    if normalized in READ_TOOLS:
        return True
    if normalized in {"bash", "shell"} and is_compile_artifact_cleanup(text):
        return False
    if normalized in {"bash", "shell"} and READISH_BASH_RE.search(text):
        return True
    return False


def is_compile_artifact_cleanup(text: str) -> bool:
    """Ignore cross-workspace deletion of Coq build products only.

    Concurrent Coq jobs can leave duplicate ``.vo/.glob/.aux`` files on a
    shared load path.  Removing those products reads no answer-bearing source
    and should not be classified as leakage.
    """
    lowered = text.lower()
    if ".unlink()" not in lowered:
        return False
    explicit_ext = any(ext in lowered for ext in (".vo", ".glob", ".vok", ".vos", ".aux"))
    generated_ext_loop = all(f"'{ext}'" in lowered for ext in ("vo", "glob", "vok", "vos", "aux"))
    if not (explicit_ext or generated_ext_loop):
        return False
    forbidden = ("read_text", "read_bytes", "open(", " cat ", " head ", " tail ", " sed ", " grep ", " rg ", " cp ")
    return not any(marker in lowered for marker in forbidden)


def is_write_like(tool: str) -> bool:
    return tool.lower() in WRITE_TOOLS


def short(text: str, limit: int = 700) -> str:
    text = re.sub(r"\s+", " ", text).strip()
    return text[:limit]


def add_finding(
    findings: list[Finding],
    *,
    case: str,
    transcript: Path,
    line: int,
    tool: str,
    category: str,
    snippet: str,
    message: str,
    severity: str = "error",
) -> None:
    findings.append(
        Finding(
            case=case,
            transcript=str(transcript),
            line=line,
            tool=tool,
            category=category,
            severity=severity,
            snippet=short(snippet),
            message=message,
        )
    )


def scan_transcript(transcript: Path, *, strict_current_output: bool = False) -> list[Finding]:
    current = current_workspace_from_path(transcript)
    case = current or transcript.parent.parent.name
    findings: list[Finding] = []

    for line_no, tool, tool_input in iter_tool_uses(transcript):
        text = tool_input_text(tool, tool_input)
        read_like = is_read_like(tool, text)
        write_like = is_write_like(tool)
        if not (read_like or write_like):
            continue
        if write_like and not read_like:
            text = write_target_text(tool_input)

        if GROUND_TRUTH_PATH_RE.search(text):
            add_finding(
                findings,
                case=case,
                transcript=transcript,
                line=line_no,
                tool=tool,
                category="ground_truth_access",
                snippet=text,
                message="Agent accessed a ground_truth mirror/path.",
            )

        if RESULTS_PATH_RE.search(text):
            add_finding(
                findings,
                case=case,
                transcript=transcript,
                line=line_no,
                tool=tool,
                category="results_access",
                snippet=text,
                message="Agent accessed archived results; these may contain prior answers.",
            )

        for match in OUTPUT_VERIFY_RE.finditer(text):
            workspace = match.group(1) or match.group(2)
            if not strict_current_output and current and workspace == current:
                continue
            add_finding(
                findings,
                case=case,
                transcript=transcript,
                line=line_no,
                tool=tool,
                category="output_workspace_access",
                snippet=text,
                message=f"Agent accessed output workspace `{workspace}`.",
            )

        if ANNOTATED_INPUT_RE.search(text):
            add_finding(
                findings,
                case=case,
                transcript=transcript,
                line=line_no,
                tool=tool,
                category="annotated_input_access",
                snippet=text,
                message="Agent accessed annotated_input, which can contain solved annotations.",
            )

        if REPO_ANNOTATED_RE.search(text):
            add_finding(
                findings,
                case=case,
                transcript=transcript,
                line=line_no,
                tool=tool,
                category="repo_annotated_access",
                snippet=text,
                message="Agent accessed repo-level annotated verify artifacts.",
            )

        other_workspaces = sorted({
            match.group(1)
            for match in CAV_WORKSPACE_RE.finditer(text)
            if not (current and match.group(1) == current)
        })
        for workspace in other_workspaces:
            category = "ground_truth_access" if workspace.startswith("ground_truth") else "other_cav_workspace_access"
            add_finding(
                findings,
                case=case,
                transcript=transcript,
                line=line_no,
                tool=tool,
                category=category,
                snippet=text,
                message=f"Agent accessed QCP CAV workspace `{workspace}` outside the current case.",
            )

        for match in CAV_GLOB_RE.finditer(text):
            workspace_segment = match.group(1)
            if current and workspace_segment == current:
                continue
            add_finding(
                findings,
                case=case,
                transcript=transcript,
                line=line_no,
                tool=tool,
                category="cav_workspace_glob",
                snippet=text,
                message=(
                    "Agent used a glob under QCP CAV workspaces outside the "
                    "current workspace, which can read other runs."
                ),
            )

        if CAV_PARENT_SCAN_RE.search(text):
            add_finding(
                findings,
                case=case,
                transcript=transcript,
                line=line_no,
                tool=tool,
                category="cav_parent_scan",
                snippet=text,
                message="Agent scanned the QCP CAV parent directory instead of the current workspace.",
            )

    deduped: list[Finding] = []
    seen: set[tuple[str, int, str, str]] = set()
    for item in findings:
        key = (item.transcript, item.line, item.category, item.message)
        if key in seen:
            continue
        seen.add(key)
        deduped.append(item)
    return deduped


def scan_paths(paths: Iterable[Path], *, strict_current_output: bool = False) -> list[Finding]:
    findings: list[Finding] = []
    for transcript in discover_transcripts(paths):
        findings.extend(scan_transcript(transcript, strict_current_output=strict_current_output))
    return findings


def summarize(findings: list[Finding], transcript_count: int) -> dict[str, Any]:
    errors = [finding for finding in findings if finding.severity == "error"]
    return {
        "transcripts": transcript_count,
        "findings": len(findings),
        "errors": len(errors),
        "categories": sorted({finding.category for finding in findings}),
        "clean": len(errors) == 0,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Scan agent_stdout JSONL transcripts for answer/workspace leakage."
    )
    parser.add_argument(
        "paths",
        nargs="*",
        default=["results/claude/deepseek-v4-pro/api"],
        help="Result/workspace/log paths to scan. Default: results/claude/deepseek-v4-pro/api",
    )
    parser.add_argument(
        "--strict-current-output",
        action="store_true",
        help="Also flag reads of the current output/verify_* workspace.",
    )
    parser.add_argument("--json", action="store_true", help="Emit machine-readable JSON.")
    parser.add_argument(
        "--no-fail",
        action="store_true",
        help="Always exit 0 even when findings are present.",
    )
    return parser


def print_text(findings: list[Finding], transcript_count: int) -> None:
    summary = summarize(findings, transcript_count)
    print(
        "Transcript leakage scan: "
        f"transcripts={summary['transcripts']} findings={summary['findings']} "
        f"errors={summary['errors']} clean={summary['clean']}"
    )
    if not findings:
        return
    by_case: dict[str, list[Finding]] = {}
    for finding in findings:
        by_case.setdefault(finding.case, []).append(finding)
    for case in sorted(by_case):
        print(f"\n## {case}")
        for finding in by_case[case]:
            print(
                f"- {finding.category} {finding.transcript}:{finding.line} "
                f"tool={finding.tool}\n"
                f"  {finding.message}\n"
                f"  {finding.snippet}"
            )


def main() -> int:
    args = build_parser().parse_args()
    paths = [Path(path) for path in args.paths]
    transcripts = discover_transcripts(paths)
    findings = scan_paths(paths, strict_current_output=args.strict_current_output)
    summary = summarize(findings, len(transcripts))
    if args.json:
        json.dump(
            {
                "summary": summary,
                "findings": [asdict(finding) for finding in findings],
            },
            sys.stdout,
            ensure_ascii=False,
            indent=2,
        )
        sys.stdout.write("\n")
    else:
        print_text(findings, len(transcripts))
    return 0 if args.no_fail or summary["clean"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
