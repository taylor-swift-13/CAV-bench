#!/usr/bin/env python3
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import threading
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import agent_config
import agent_metrics
import check_leakage
import check_verify_audit


REPO_ROOT = Path(__file__).resolve().parents[1]
import coq_runner

QCP_ROOT = REPO_ROOT / "QualifiedCProgramming"
QCP_SL_DIR = QCP_ROOT / "SeparationLogic"
QCP_CAV_INPUT_ROOT = QCP_ROOT / "QCP_examples" / "CAV"
QCP_CAV_EXAMPLES_ROOT = QCP_SL_DIR / "examples" / "CAV"
QCP_CAV_LOCK_ROOT = QCP_SL_DIR / "_cav_locks"

DEFAULT_SKILL = REPO_ROOT / "skills" / "verify" / "SKILL.md"
PROOF_ONLY_SKILL = REPO_ROOT / "skills" / "verify" / "MODE_PROOF_ONLY.md"
OUTPUT_ROOT = REPO_ROOT / "output"
DEFAULT_MODEL = "gpt-5.4"
DEFAULT_CLAUDE_MODEL = "sonnet"
DEFAULT_REASONING_EFFORT = "medium"
QCP_SKILL_PATHS = (
    "QualifiedCProgramming/.agents/skills/verification-orchestrator/SKILL.md",
    "QualifiedCProgramming/.agents/skills/annotation-filling/SKILL.md",
    "QualifiedCProgramming/.agents/skills/annotation-checking/SKILL.md",
    "QualifiedCProgramming/.agents/skills/vc-checking/SKILL.md",
    "QualifiedCProgramming/.agents/skills/group-worker-proving/SKILL.md",
    "QualifiedCProgramming/.agents/skills/final-check/SKILL.md",
)

# Agent-facing rules live in skills/verify/SKILL.md (see §4.0 read/write
# boundaries, §4.3/§4.4 proof-manual-only completion, §4.5a-§4.5e workflow).
# This script's prompts pass paths + per-run context and refer to the skill.

NOISE_PATTERNS = [
    "WARNING: proceeding, even though we could not update PATH: Read-only file system",
    "failed to renew cache TTL: Read-only file system",
    "failed to record rollout items: failed to queue rollout items: channel closed",
    "failed to connect to websocket: IO error: Connection reset by peer",
]


def timestamp_now() -> str:
    return dt.datetime.now().strftime("%Y%m%d_%H%M%S")


def iso_now() -> str:
    return dt.datetime.now().astimezone().strftime("%Y-%m-%d %H:%M:%S %z")


def stem_from_input(input_path: Path) -> str:
    return input_path.stem


def ensure_parent(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def emit_log(message: str) -> None:
    print(f"[verify] {message}", flush=True)


def iso_from_epoch(epoch: float) -> str:
    return dt.datetime.fromtimestamp(epoch).astimezone().strftime("%Y-%m-%d %H:%M:%S.%f %z")


def _tsv_cell(value: object) -> str:
    return str(value if value is not None else "").replace("\t", " ").replace("\n", " ").replace("\r", " ")


def _timeline_row(epoch: float, line_no: int, raw_line: str) -> str:
    event_type = ""
    item_type = ""
    item_status = ""
    item_id = ""
    command = ""
    try:
        obj = json.loads(raw_line)
    except json.JSONDecodeError:
        obj = {}
    if isinstance(obj, dict):
        event_type = obj.get("type") or ""
        item = obj.get("item")
        if isinstance(item, dict):
            item_type = item.get("type") or ""
            item_status = item.get("status") or ""
            item_id = item.get("id") or ""
            command = item.get("command") or ""
    return "\t".join(
        _tsv_cell(v)
        for v in (
            f"{epoch:.6f}",
            iso_from_epoch(epoch),
            line_no,
            event_type,
            item_type,
            item_status,
            item_id,
            command,
        )
    )


def run_agent_with_timeline(
    cmd: list[str],
    *,
    prompt: str | None,
    stdout_jsonl: Path,
    stdout_timeline: Path,
    stderr_log: Path,
    cwd: Path,
    timeout: int,
    env: dict[str, str],
) -> int:
    ensure_parent(stdout_jsonl)
    stdout_timeline.parent.mkdir(parents=True, exist_ok=True)
    with stdout_jsonl.open("w", encoding="utf-8") as out_f, \
            stdout_timeline.open("w", encoding="utf-8") as timeline_f, \
            stderr_log.open("w", encoding="utf-8") as err_f:
        timeline_f.write("epoch\tiso_time\tline_no\tevent_type\titem_type\titem_status\titem_id\tcommand\n")
        proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=err_f,
            text=True,
            cwd=cwd,
            env=env,
            bufsize=1,
        )
        writer_error: list[BaseException] = []

        def write_prompt() -> None:
            try:
                if prompt is None:
                    if proc.stdin is not None:
                        proc.stdin.close()
                    return
                assert proc.stdin is not None
                proc.stdin.write(prompt)
                proc.stdin.close()
            except BaseException as exc:
                writer_error.append(exc)

        def read_stdout() -> None:
            assert proc.stdout is not None
            line_no = 0
            for line in proc.stdout:
                line_no += 1
                epoch = time.time()
                out_f.write(line)
                out_f.flush()
                timeline_f.write(_timeline_row(epoch, line_no, line) + "\n")
                timeline_f.flush()

        writer = threading.Thread(target=write_prompt, daemon=True)
        reader = threading.Thread(target=read_stdout, daemon=True)
        writer.start()
        reader.start()
        try:
            returncode = proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait()
            reader.join(timeout=5)
            writer.join(timeout=5)
            raise
        reader.join(timeout=5)
        writer.join(timeout=5)
        return returncode


def build_agent_env(logs_dir: Path) -> dict[str, str]:
    env = os.environ.copy()
    cache_dir = logs_dir / ".agent_cache"
    state_dir = logs_dir / ".state"
    data_dir = logs_dir / ".data"
    config_dir = logs_dir / ".config"
    tmp_dir = logs_dir / ".tmp"
    cache_dir.mkdir(parents=True, exist_ok=True)
    state_dir.mkdir(parents=True, exist_ok=True)
    data_dir.mkdir(parents=True, exist_ok=True)
    config_dir.mkdir(parents=True, exist_ok=True)
    tmp_dir.mkdir(parents=True, exist_ok=True)
    env["XDG_CACHE_HOME"] = str(cache_dir)
    env["XDG_STATE_HOME"] = str(state_dir)
    env["XDG_DATA_HOME"] = str(data_dir)
    env["XDG_CONFIG_HOME"] = str(config_dir)
    env["TMPDIR"] = str(tmp_dir)
    env["TMP"] = str(tmp_dir)
    env["TEMP"] = str(tmp_dir)
    return env


def codex_supports_reasoning_effort(codex_bin: str, cwd: Path, env: dict[str, str]) -> bool:
    try:
        proc = subprocess.run(
            [codex_bin, "exec", "--help"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            cwd=cwd,
            env=env,
            timeout=10,
        )
    except (subprocess.SubprocessError, OSError):
        return False
    return "--reasoning-effort" in proc.stdout


def filter_stderr_in_place(stderr_log: Path) -> None:
    if not stderr_log.exists():
        return
    clean_lines = []
    for raw_line in stderr_log.read_text(encoding="utf-8", errors="replace").splitlines():
        if any(pattern in raw_line for pattern in NOISE_PATTERNS):
            continue
        clean_lines.append(raw_line)
    stderr_log.write_text("\n".join(clean_lines) + ("\n" if clean_lines else ""), encoding="utf-8")


def paired_input_v(input_path: Path) -> Path | None:
    candidate = input_path.with_suffix(".v")
    if candidate.exists():
        return candidate
    return None


def imported_coq_dependency_paths(input_path: Path) -> list[Path]:
    text = input_path.read_text(encoding="utf-8", errors="replace")
    import_groups = re.findall(r"Import\s+Coq\s+Require\s+Import\s+([A-Za-z0-9_ ]+)", text)
    modules = sorted({module for group in import_groups for module in group.split()})
    deps: list[Path] = []
    for module in modules:
        candidate = input_path.parent / f"{module}.v"
        if candidate.exists():
            deps.append(candidate)
    return deps


def qcp_agent_c_path(workspace_path: Path, annotated_c_path: Path) -> Path:
    return QCP_CAV_INPUT_ROOT / workspace_path.name / annotated_c_path.name


def qcp_case_coq_dir(workspace_path: Path) -> Path:
    return QCP_CAV_EXAMPLES_ROOT / workspace_path.name


def qcp_case_deps_dir(workspace_path: Path) -> Path:
    return qcp_case_coq_dir(workspace_path) / "deps"


def qcp_rel(path: Path) -> str:
    return str(Path(path).resolve().relative_to(QCP_ROOT))


def _qcp_skill_list() -> str:
    lines = [
        "Read every QCP official skill below before editing this case:",
        *[f"- `{path}`" for path in QCP_SKILL_PATHS],
        "",
        "Also read the relevant QCP docs:",
        "- `QualifiedCProgramming/.agents/skills/annotation-checking/docs/spec-quality-checklist.md` — spec-quality criteria and external predicate definition requirements.",
        "- `QualifiedCProgramming/.agents/skills/annotation-filling/docs/annotation-guide.md` — annotation syntax and placement rules.",
        "- `QualifiedCProgramming/.agents/skills/annotation-filling/docs/pure-proposition-predicates.md` — mathematical predicates instead of algorithm mirrors.",
        "- `QualifiedCProgramming/.agents/skills/annotation-filling/docs/array-string-guide.md` — built-in array/string predicate support and required side conditions.",
        "- `QualifiedCProgramming/.agents/skills/group-worker-proving/docs/` — proof tactics and separation-logic proof patterns.",
        "- `QualifiedCProgramming/.agents/skills/final-check/` — final compile/check workflow.",
        "Use `verification-orchestrator` as the orchestration entry point. Use `annotation-filling` and `annotation-checking` for annotation/symexec. Use `vc-checking` and `group-worker-proving` for manual VC diagnosis/proofs. Use `final-check` to validate the current case before completion.",
    ]
    return "\n".join(lines)


def _repo_skill_list(skill_path: Path, *, proof_only: bool = False) -> str:
    paths = [Path("../skills/verify/SKILL.md")]
    if proof_only:
        paths.append(Path("../skills/verify/MODE_PROOF_ONLY.md"))
    lines = [
        "Read this repo-level CAV verify skill before editing this case:",
        *[f"- `{path}`" for path in paths],
        "These are the only repo-level files you may read; all other repo-level directories remain out of scope.",
    ]
    return "\n".join(lines)


def _input_lines(input_path: Path, input_v_path: Path | None, function_name: str, workspace_path: Path, annotated_c_path: Path) -> str:
    input_v = f"`{input_v_path.name}`" if input_v_path else "`<not provided>`"
    qcp_c = qcp_agent_c_path(workspace_path, annotated_c_path)
    qcp_coq = qcp_case_coq_dir(workspace_path)
    qcp_deps = qcp_case_deps_dir(workspace_path)
    qcp_logs = qcp_coq / "logs"
    return (
        f"- Input C name: `{input_path.name}` (already staged by runner; do not open original input path)\n"
        f"- Optional input V name: {input_v} (already staged by runner when present)\n"
        f"- Target function: `{function_name}`\n"
        "- Output workspace: runner-owned artifact collection outside agent scope; do not access it.\n"
        f"- Active QCP annotated C to edit: `{qcp_rel(qcp_c)}`\n"
        f"- Active QCP Coq directory to edit/compile: `{qcp_rel(qcp_coq)}`\n"
        f"- Active QCP deps directory: `{qcp_rel(qcp_deps)}` (read-only staged bare `.v` specs for Require Import)\n"
        f"- Active QCP logs directory: `{qcp_rel(qcp_logs)}`\n"
    )


def _qcp_final_check_commands(
    function_name: str,
    workspace_path: Path,
    annotated_c_path: Path,
    input_path: Path,
    input_v_path: Path | None,
) -> str:
    workspace = workspace_path.name
    qcp_c_rel = f"QCP_examples/CAV/{workspace}/{annotated_c_path.name}"
    coq_dir_rel = f"SeparationLogic/examples/CAV/{workspace}"
    deps_rel = f"examples/CAV/{workspace}/deps"
    sl_coq_args = (
        f"-Q {deps_rel} '' "
        "-R flocq/src Flocq "
        "-R SeparationLogic SimpleC.SL "
        "-R unifysl Logic "
        "-R sets SetsClass "
        "-R compcert_lib compcert.lib "
        "-R auxlibs AUXLib "
        "-R examples SimpleC.EE "
        "-R stdlib SimpleC.StdLib "
        "-R StrategyLib SimpleC.StrategyLib "
        "-R Common SimpleC.Common "
        "-R fixedpoints FP "
        "-R MonadLib MonadLib "
        "-R listlib ListLib "
        "-R MaxMinLib MaxMinLib "
        "-R GraphLib GraphLib "
        "-R SumLib SumLib "
        "-R tracelib TraceLib "
        "-R coq-record-update/src RecordUpdate "
        "-Q algorithms Algorithms"
    )
    commands = [
        f"linux-binary/symexec --goal-file={coq_dir_rel}/{function_name}_goal.v --proof-auto-file={coq_dir_rel}/{function_name}_proof_auto.v --proof-manual-file={coq_dir_rel}/{function_name}_proof_manual.v --coq-logic-path=SimpleC.EE.CAV.{workspace} -IQCP_examples/stdlib/ -slp QCP_examples/stdlib/ SimpleC.StdLib -IQCP_examples/QCP_demos_LLM/ -slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM --input-file={qcp_c_rel} --no-exec-info",
    ]
    for source in original_v_dependency_closure(input_path, input_v_path):
        commands.append(f"cd SeparationLogic && coqc {sl_coq_args} examples/CAV/{workspace}/deps/{source.name}")
    for source in local_strategy_v_sources(input_path.parent):
        commands.append(f"cd SeparationLogic && coqc {sl_coq_args} examples/CAV/{workspace}/{source.name}")
    commands.extend(
        [
            f"cd SeparationLogic && coqc {sl_coq_args} examples/CAV/{workspace}/{function_name}_goal.v",
            f"cd SeparationLogic && coqc {sl_coq_args} examples/CAV/{workspace}/{function_name}_proof_auto.v",
            f"cd SeparationLogic && coqc {sl_coq_args} examples/CAV/{workspace}/{function_name}_proof_manual.v",
            f"cd SeparationLogic && coqc {sl_coq_args} examples/CAV/{workspace}/{function_name}_goal_check.v",
        ]
    )
    return "\n".join(
        [
            "Exact QCP commands for this case (run from QualifiedCProgramming):",
            "```bash",
            *commands,
            "```",
            "Do not search for symexec, Makefiles, dune files, QCP docs, scripts, or external parser directories. Use only the commands above.",
            "Runner-side final acceptance will re-check the same QCP mirror after you exit. If any annotation, symexec, proof, or final-check step fails while you are working, do not exit; keep editing annotation/proof and rerun the relevant QCP check. Only write Final Result: Success when the mirror is ready for runner acceptance. Only write Final Result: Fail when you have confirmed a contract_program_mismatch_blocker: the Contract and original program semantics conflict and the case must return to Contract/user decision.",
            "Runner acceptance expects the original executable program and contract to be preserved, and every manual proof obligation to be justified by real proof work from the available case facts. Separately, you must keep all work inside the active case workspace and must not use prior answers or unrelated runs.",
            "Do not prove or edit proof_auto.v. It is normal QCP-generated output; the real manual burden is proof_manual.v. Completion is judged by all manual proof obligations being genuinely discharged and goal_check.v compiling.",
            "Do not add anything whose purpose is to make the files accepted without proving the stated obligations, and do not use external answer artifacts. If proof_manual.v is empty or has no manual obligations and the QCP final-check sequence succeeds, immediately write QCP logs/issues.md, QCP logs/metrics.md, and finish with Final Result: Success.",
        ]
    )


def build_prompt(
    skill_path: Path,
    input_path: Path,
    input_v_path: Path | None,
    function_name: str,
    workspace_path: Path,
    annotated_c_path: Path,
    attempt: int,
    restart_context: str | None = None,
) -> str:
    lines = [
        "Use the repo-level CAV verify skill plus QCP official workflow rules. First read the repo-level CAV skill files and the full read-only QCP `QualifiedCProgramming/.agents/skills/` list below; then use this prompt and the current QCP mirror for case-specific paths and audit requirements.",
        "",
        _repo_skill_list(skill_path),
        "",
        _qcp_skill_list(),
        "",
        "Persistence requirement: default the contract to correct. If annotation, symexec, proof, or final-check fails while you are working, do not exit; keep editing annotation/proof and rerun the relevant QCP check. Writing issues.md or metrics.md is not permission to stop. The only exception is a confirmed contract_program_mismatch_blocker: the Contract and original program semantics conflict and the case must return to Contract/user decision.",
        "",
        "Compile boundary: use the QCP final-check sequence summarized here and cross-check it against read-only QCP `QualifiedCProgramming/.agents/skills/` docs: symexec, then dependency-ordered coqc for original deps, goal, proof_auto, proof_manual, and goal_check. The current case is already staged in the current workspace's QCP mirror under QualifiedCProgramming. Do all annotation, symexec, proof, and coqc work there. Do not compile under output/coq/generated, do not parallelize a dependency-ordered QCP final-check sequence, and never copy .vo/.glob/.aux files back to output.",
        "Runner artifact boundary: do not write output/, annotated/, repo-level logs, or staged bare spec deps yourself. Write only issues.md and metrics.md under the active QCP logs directory; do not put probe files, proof backups, or temporary Coq files under logs. Use a `.tmp/` directory inside the active QCP Coq directory for temporary probes/backups. The runner collects the current QCP annotated C, QCP logs, and final target .v artifacts from the QCP mirror after the agent exits.",
        "",
        "Repository read/write boundary: after reading this prompt, the repo-level CAV skill files listed above, and the read-only QCP `QualifiedCProgramming/.agents/skills/` docs, write only the active QCP annotated C, active QCP Coq directory, and issues.md/metrics.md in active QCP logs. The active QCP deps directory is read-only. Do not read or write output/, annotated/, scripts/, input/, QCP source files outside `QualifiedCProgramming/.agents/skills/`, unrelated QCP mirror workspaces, git history, or agent stdout logs. The only repo-level files you may read are the listed `../skills/...` files.",
        "",
        "Read boundary: the current QCP mirror directories listed in Inputs are in scope, along with the listed repo-level CAV skill files, `QualifiedCProgramming/.agents/skills/`, `QualifiedCProgramming/tutorial/`, `QualifiedCProgramming/QCP_examples/{Applications_human,LLM_bench,QCP_demos_human,QCP_demos_LLM,stdlib}/`, `QualifiedCProgramming/SeparationLogic/stdlib/`, and `QualifiedCProgramming/SeparationLogic/examples/{Applications_human,LLM_bench,QCP_demos_human,QCP_demos_LLM}/` for required related examples. The output workspace is runner-owned and must not be read by the agent.",
        "",
        "Symexec rerun rule: work in the QCP mirror. If you rerun symexec after annotation changes, preserve the previous target .v files inside the current QCP mirror for reference before regenerating, then manually reuse old proof structure where witness statements still match.",
        "",
        "Inputs:",
        _input_lines(input_path, input_v_path, function_name, workspace_path, annotated_c_path).rstrip(),
        "",
        _qcp_final_check_commands(function_name, workspace_path, annotated_c_path, input_path, input_v_path),
    ]
    if restart_context:
        lines += ["", "Restart feedback:", restart_context.rstrip()]
    return "\n".join(lines) + "\n"


def build_proof_only_prompt(
    skill_path: Path,
    input_path: Path,
    input_v_path: Path | None,
    function_name: str,
    workspace_path: Path,
    annotated_c_path: Path,
    attempt: int,
    restart_context: str | None = None,
) -> str:
    lines = [
        "Use the repo-level CAV verify skill plus QCP official workflow rules. First read the repo-level CAV skill files and the full read-only QCP `QualifiedCProgramming/.agents/skills/` list below, even in proof-only mode; then use this prompt and the current QCP mirror for case-specific paths and audit requirements.",
        "",
        _repo_skill_list(skill_path, proof_only=True),
        "",
        _qcp_skill_list(),
        "",
        "Persistence requirement: proof-only mode must keep proving while proof_manual.v can still be edited. If proof or final-check fails while you are working, do not exit; keep editing proof_manual.v and rerun the relevant QCP check. Writing issues.md or metrics.md is not permission to stop. The only exception is a confirmed contract_program_mismatch_blocker: the Contract and original program semantics conflict and the case must return to Contract/user decision.",
        "",
        "Compile boundary: use the QCP final-check sequence summarized here and cross-check it against read-only QCP `QualifiedCProgramming/.agents/skills/` docs: dependency-ordered coqc for original deps, goal, proof_auto, proof_manual, and goal_check. The current case is already staged in the current workspace's QCP mirror under QualifiedCProgramming. Do all proof and coqc work there. Do not compile under output/coq/generated, do not parallelize a dependency-ordered QCP final-check sequence, and never copy .vo/.glob/.aux files back to output.",
        "Runner artifact boundary: do not write output/, annotated/, repo-level logs, or staged bare spec deps yourself. Write only issues.md and metrics.md under the active QCP logs directory; do not put probe files, proof backups, or temporary Coq files under logs. Use a `.tmp/` directory inside the active QCP Coq directory for temporary probes/backups. The runner collects the current QCP annotated C, QCP logs, and final target .v artifacts from the QCP mirror after the agent exits.",
        "",
        "Repository read/write boundary: after reading this prompt, the repo-level CAV skill files listed above, and the read-only QCP `QualifiedCProgramming/.agents/skills/` docs, write only the active QCP annotated C, active QCP Coq directory, and issues.md/metrics.md in active QCP logs. The active QCP deps directory is read-only. Do not read or write output/, annotated/, scripts/, input/, QCP source files outside `QualifiedCProgramming/.agents/skills/`, unrelated QCP mirror workspaces, git history, or agent stdout logs. The only repo-level files you may read are the listed `../skills/...` files.",
        "",
        "Read boundary: the current QCP mirror directories listed in Inputs are in scope, along with the listed repo-level CAV skill files, `QualifiedCProgramming/.agents/skills/`, `QualifiedCProgramming/tutorial/`, `QualifiedCProgramming/QCP_examples/{Applications_human,LLM_bench,QCP_demos_human,QCP_demos_LLM,stdlib}/`, `QualifiedCProgramming/SeparationLogic/stdlib/`, and `QualifiedCProgramming/SeparationLogic/examples/{Applications_human,LLM_bench,QCP_demos_human,QCP_demos_LLM}/` for required related examples. The output workspace is runner-owned and must not be read by the agent.",
        "",
        "Do not rerun symexec in proof-only mode. If a prior generated snapshot exists under coq/last, it is read-only reference material for proof structure.",
        "",
        "Mode: proof-only (also follow MODE_PROOF_ONLY.md per SKILL.md §4.5c).",
        "",
        "Inputs:",
        _input_lines(input_path, input_v_path, function_name, workspace_path, annotated_c_path).rstrip(),
        "",
        _qcp_final_check_commands(function_name, workspace_path, annotated_c_path, input_path, input_v_path),
    ]
    if restart_context:
        lines += ["", "Restart feedback (must be addressed before finishing this verify run):", restart_context.rstrip()]
    return "\n".join(lines) + "\n"


def _phase_log(workspace_path: Path, event: str, detail: str = "") -> None:
    """Append a timestamped phase event to <ws>/logs/phase_timeline.tsv (best-effort).
    Initial symexec and agent-triggered reruns share this timeline."""
    try:
        import time as _t
        p = workspace_path / "logs" / "phase_timeline.tsv"
        p.parent.mkdir(parents=True, exist_ok=True)
        with open(p, "a", encoding="utf-8") as f:
            f.write(f"{_t.time():.3f}\t{_t.strftime('%Y-%m-%d %H:%M:%S')}\t{event}\t{detail}\n")
    except Exception:
        pass


def phase_timing_lines(metrics_md_path: Path, start_iso: str, end_iso: str, stdout_timeline: Path | None = None) -> list[str]:
    """Aggregate phase_timeline.tsv into per annotation↔proof cycle durations.
    Each symexec run bounds a cycle; the gap to the next symexec (or run end) is the
    time spent proving/editing against that annotation version."""
    import datetime
    tl = metrics_md_path.parent / "phase_timeline.tsv"
    if not tl.exists():
        return []
    def _ep(iso: str):
        for parser in (
            lambda s: datetime.datetime.strptime(s, "%Y-%m-%d %H:%M:%S %z"),
            datetime.datetime.fromisoformat,
        ):
            try:
                return parser(iso).timestamp()
            except Exception:
                continue
        return None
    starts: list[float] = []
    dones: list[float] = []
    last_ep = None
    for ln in tl.read_text(encoding="utf-8", errors="replace").splitlines():
        p = ln.split("\t")
        if len(p) < 3:
            continue
        try:
            ep = float(p[0])
        except ValueError:
            continue
        last_ep = ep
        if p[2] in ("symexec_init_start", "symexec_rerun_start"):
            starts.append(ep)
        elif p[2] in ("symexec_init_done", "symexec_rerun_done"):
            dones.append(ep)
    if not starts:
        return []
    coqc_done: list[float] = []
    if stdout_timeline and stdout_timeline.exists():
        for ln in stdout_timeline.read_text(encoding="utf-8", errors="replace").splitlines()[1:]:
            p = ln.split("\t")
            if len(p) < 8:
                continue
            try:
                ep = float(p[0])
            except ValueError:
                continue
            event_type, item_type, item_status, command = p[3], p[4], p[5], p[7]
            if event_type == "item.completed" and item_type == "command_execution" and item_status == "completed":
                if re.search(r"(^|[/\s'\"])(coqc|coqtop)(\s|$)", command):
                    coqc_done.append(ep)
    run_start, run_end = _ep(start_iso), (_ep(end_iso) or last_ep)
    out = [f"- Annotation↔proof cycles (symexec runs): `{len(starts)}`"]
    if run_start and run_end:
        annotation_seconds = 0.0
        prev_symexec = run_start
        for s in starts:
            coqc_since_prev_symexec = [c for c in coqc_done if prev_symexec <= c <= s]
            if coqc_since_prev_symexec:
                annotation_seconds += max(0.0, s - max(coqc_since_prev_symexec))
            else:
                annotation_seconds += max(0.0, s - prev_symexec)
            prev_symexec = s
        total_seconds = max(0.0, run_end - run_start)
        proof_seconds = max(0.0, total_seconds - annotation_seconds)
        out.append(f"- Annotation phase time (estimated seconds): `{annotation_seconds:.1f}`")
        out.append(f"- Proof phase time (estimated seconds): `{proof_seconds:.1f}`")
    if run_start:
        out.append(f"  - initial annotation (run start → 1st symexec): `{starts[0]-run_start:.1f}s`")
    for i, s in enumerate(starts):
        nxt = starts[i + 1] if i + 1 < len(starts) else (run_end or s)
        out.append(f"  - cycle {i+1}: symexec, then `{max(0.0, nxt - s):.1f}s` proving/edit before next")
    return out


def write_metrics(
    metrics_md_path: Path,
    *,
    status: str,
    attempts: int,
    last_agent_exit: int,
    start_iso: str,
    end_iso: str,
    wall_clock_seconds: float,
    agent: str,
    model: str,
    reasoning_effort: str,
    usage: dict[str, int] | None,
    prompt_path: Path,
    stdout_jsonl: Path,
    stdout_timeline: Path | None = None,
    stderr_log: Path,
    last_message_path: Path,
    input_c: Path,
    input_v: Path | None,
    annotated_snapshot: Path | None = None,
    annotated_cleanup: str = "not attempted",
) -> None:
    lines = [
        "# Verify Metrics",
        "",
        "- Stage: `verify`",
        f"- Status: `{status}`",
        f"- Attempts: `{attempts}`",
        f"- Last agent exit code: `{last_agent_exit}`",
        f"- Start time: `{start_iso}`",
        f"- End time: `{end_iso}`",
        f"- Wall-clock time (seconds): `{wall_clock_seconds:.2f}`",
        f"- Agent: `{agent}`",
        f"- Model: `{model or 'n/a'}`",
        f"- Reasoning effort: `{reasoning_effort or 'n/a'}`",
        f"- Input C: `{input_c}`",
        f"- Input V: `{input_v if input_v else '<not provided>'}`",
        f"- Annotated C snapshot: `{annotated_snapshot if annotated_snapshot else '<not saved>'}`",
        f"- Annotated C global cleanup: `{annotated_cleanup}`",
        f"- Prompt file: `{prompt_path}`",
        f"- Agent stdout: `{stdout_jsonl}`",
        f"- Agent stdout timeline: `{stdout_timeline if stdout_timeline else '<not recorded>'}`",
        f"- Agent stderr: `{stderr_log}`",
        f"- Agent last message: `{last_message_path}`",
    ]
    lines.extend(agent_metrics.usage_lines(
        usage, prompt_path=prompt_path, last_message_path=last_message_path))
    lines.extend(phase_timing_lines(metrics_md_path, start_iso, end_iso, stdout_timeline))
    lines.extend(["- Experience updates: none", f"Final Result: {status}"])
    metrics_md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def save_annotated_snapshot(workspace_path: Path, annotated_c_path: Path) -> Path | None:
    if not annotated_c_path.exists():
        return None
    snapshot = workspace_path / "annotated" / annotated_c_path.name
    snapshot.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(annotated_c_path, snapshot)
    return snapshot


def cleanup_global_annotated_after_snapshot(annotated_c_path: Path, annotated_snapshot: Path | None) -> str:
    """Remove the repo-level annotated file after preserving it in the workspace."""
    if annotated_snapshot is None or not annotated_snapshot.exists():
        return "skipped: snapshot missing"
    if not annotated_c_path.exists():
        return "already absent"
    try:
        annotated_c_path.unlink()
    except OSError as exc:
        return f"failed: {exc}"
    return f"deleted {annotated_c_path}"


def stage_qcp_mirror_for_agent(
    workspace_path: Path,
    input_path: Path,
    input_v_path: Path | None,
    annotated_c_path: Path,
    function_name: str,
) -> dict[str, Path]:
    """Prepare the current QCP mirror as the agent's only read/write workspace."""
    workspace_name = workspace_path.name
    qcp_input_dir = QCP_CAV_INPUT_ROOT / workspace_name
    qcp_examples_dir = qcp_case_coq_dir(workspace_path)
    qcp_deps_dir = qcp_case_deps_dir(workspace_path)
    for directory in (qcp_input_dir, qcp_examples_dir):
        if directory.exists():
            shutil.rmtree(directory)
        directory.mkdir(parents=True, exist_ok=True)
    (qcp_examples_dir / "logs").mkdir(parents=True, exist_ok=True)

    qcp_annotated = qcp_input_dir / annotated_c_path.name
    shutil.copy2(annotated_c_path, qcp_annotated)
    _copy_header_deps(input_path.parent, qcp_input_dir)
    stage_original_v_deps(input_path, input_v_path, qcp_deps_dir)
    _copy_strategy_v_deps(
        input_path.parent,
        qcp_examples_dir,
        workspace_logic_path=f"SimpleC.EE.CAV.{workspace_name}",
        case_module=input_path.stem,
    )
    write_qcp_agent_audit_script(
        workspace_path=workspace_path,
        input_path=input_path,
        input_v_path=input_v_path,
        annotated_c_path=annotated_c_path,
        function_name=function_name,
    )
    return {
        "qcp_input_dir": qcp_input_dir,
        "qcp_examples_dir": qcp_examples_dir,
        "qcp_deps_dir": qcp_deps_dir,
        "qcp_annotated": qcp_annotated,
    }


def _shell_join(argv: list[str]) -> str:
    return " ".join(shlex.quote(arg) for arg in argv)


def write_qcp_agent_audit_script(
    *,
    workspace_path: Path,
    input_path: Path,
    input_v_path: Path | None,
    annotated_c_path: Path,
    function_name: str,
) -> Path:
    """Write the per-case QCP mirror final-check helper script."""
    workspace = workspace_path.name

    qcp_c_rel = f"QCP_examples/CAV/{workspace}/{annotated_c_path.name}"
    coq_dir_rel = f"SeparationLogic/examples/CAV/{workspace}"
    deps_rel = f"examples/CAV/{workspace}/deps"
    log_rel = f"{coq_dir_rel}/logs/agent_audit.log"
    audit_rel = f"{coq_dir_rel}/run_audit.sh"

    original_c = workspace_path / "original" / input_path.name
    original_text = original_c.read_text(encoding="utf-8", errors="replace") if original_c.exists() else input_path.read_text(encoding="utf-8", errors="replace")
    expected_executable = normalize_c_without_annotations(original_text)
    expected_contracts = check_verify_audit.extract_contract_specs(original_text)

    coq_args = [
        "-Q", deps_rel, "",
        "-R", "flocq/src", "Flocq",
        "-R", "SeparationLogic", "SimpleC.SL",
        "-R", "unifysl", "Logic",
        "-R", "sets", "SetsClass",
        "-R", "compcert_lib", "compcert.lib",
        "-R", "auxlibs", "AUXLib",
        "-R", "examples", "SimpleC.EE",
        "-R", "stdlib", "SimpleC.StdLib",
        "-R", "StrategyLib", "SimpleC.StrategyLib",
        "-R", "Common", "SimpleC.Common",
        "-R", "fixedpoints", "FP",
        "-R", "MonadLib", "MonadLib",
        "-R", "listlib", "ListLib",
        "-R", "MaxMinLib", "MaxMinLib",
        "-R", "GraphLib", "GraphLib",
        "-R", "SumLib", "SumLib",
        "-R", "tracelib", "TraceLib",
        "-R", "coq-record-update/src", "RecordUpdate",
        "-Q", "algorithms", "Algorithms",
    ]
    commands: list[list[str]] = [[
        "linux-binary/symexec",
        f"--goal-file={coq_dir_rel}/{function_name}_goal.v",
        f"--proof-auto-file={coq_dir_rel}/{function_name}_proof_auto.v",
        f"--proof-manual-file={coq_dir_rel}/{function_name}_proof_manual.v",
        f"--coq-logic-path=SimpleC.EE.CAV.{workspace}",
        "-IQCP_examples/stdlib/",
        "-slp", "QCP_examples/stdlib/", "SimpleC.StdLib",
        "-IQCP_examples/QCP_demos_LLM/",
        "-slp", "QCP_examples/QCP_demos_LLM/", "SimpleC.EE.QCP_demos_LLM",
        f"--input-file={qcp_c_rel}",
        "--no-exec-info",
    ]]
    for source in original_v_dependency_closure(input_path, input_v_path):
        commands.append(["bash", "-lc", _shell_join(["cd", "SeparationLogic"]) + " && " + _shell_join(["coqc", *coq_args, f"examples/CAV/{workspace}/deps/{source.name}"])])
    for source in local_strategy_v_sources(input_path.parent):
        commands.append(["bash", "-lc", _shell_join(["cd", "SeparationLogic"]) + " && " + _shell_join(["coqc", *coq_args, f"examples/CAV/{workspace}/{source.name}"])])
    for suffix in ("goal", "proof_auto", "proof_manual", "goal_check"):
        commands.append(["bash", "-lc", _shell_join(["cd", "SeparationLogic"]) + " && " + _shell_join(["coqc", *coq_args, f"examples/CAV/{workspace}/{function_name}_{suffix}.v"])])

    script = f"""#!/usr/bin/env bash
set -u
cd "$(dirname "$0")/../../../.."
LOG={shlex.quote(log_rel)}
mkdir -p "$(dirname "$LOG")"
: > "$LOG"
fail() {{
  echo "[audit] FAIL: $*" | tee -a "$LOG"
  exit 1
}}
run() {{
  echo "[audit] $*" | tee -a "$LOG"
  "$@" >>"$LOG" 2>&1 || fail "command failed: $*"
}}

python3 - <<'PY' >>"$LOG" 2>&1
import json, re, sys
from pathlib import Path

qcp_c = Path({qcp_c_rel!r})
expected_executable = {expected_executable!r}
expected_contracts = json.loads({json.dumps(expected_contracts)!r})

def normalize_c_without_annotations(text):
    multi = ("<<=", ">>=", "...", "->", "++", "--", "<<", ">>", "<=", ">=", "==", "!=", "&&", "||", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "##", "::")
    tokens = []
    i = 0
    while i < len(text):
        ch = text[i]
        if ch.isspace():
            i += 1
        elif text.startswith("//", i):
            end = text.find("\\n", i + 2)
            i = len(text) if end < 0 else end + 1
        elif text.startswith("/*", i):
            end = text.find("*/", i + 2)
            if end < 0:
                tokens.append("<unterminated-comment>")
                break
            i = end + 2
        elif ch == '"' or ch == "'":
            quote, start = ch, i
            i += 1
            while i < len(text):
                if text[i] == "\\\\":
                    i += 2
                elif text[i] == quote:
                    i += 1
                    break
                else:
                    i += 1
            tokens.append(text[start:i])
        elif ch.isalpha() or ch == "_":
            start = i
            i += 1
            while i < len(text) and (text[i].isalnum() or text[i] == "_"):
                i += 1
            tokens.append(text[start:i])
        elif ch.isdigit() or (ch == "." and i + 1 < len(text) and text[i + 1].isdigit()):
            start = i
            i += 1
            while i < len(text):
                cur = text[i]
                if cur.isalnum() or cur in "._":
                    i += 1
                elif cur in "+-" and i > start and text[i - 1] in "eEpP":
                    i += 1
                else:
                    break
            tokens.append(text[start:i])
        else:
            op = next((candidate for candidate in multi if text.startswith(candidate, i)), None)
            if op is None:
                tokens.append(ch)
                i += 1
            else:
                tokens.append(op)
                i += len(op)
    return "\\x1f".join(tokens)

def normalize(text):
    return re.sub(r"\\s+", " ", text).strip()

def extract_contract_specs(c_text):
    specs = []
    for body in re.findall(r"/\\*@(.*?)\\*/", c_text, flags=re.DOTALL):
        if re.search(r"\\bEnsure\\b", body):
            specs.append(normalize(body))
    return specs

text = qcp_c.read_text(encoding="utf-8", errors="replace")
if extract_contract_specs(text) != expected_contracts:
    print("[audit] contract changed")
    sys.exit(2)
if normalize_c_without_annotations(text) != expected_executable:
    print("[audit] executable C changed after stripping comments/QCP annotations")
    sys.exit(3)
print("[audit] source integrity passed")
PY
py_rc=$?
case "$py_rc" in
  0) ;;
  2) fail "contract changed" ;;
  3) fail "executable C changed" ;;
  *) fail "source integrity check failed: rc=$py_rc" ;;
esac
"""
    for command in commands:
        script += f"run {_shell_join(command)}\n"
    script += 'echo "[audit] SUCCESS" | tee -a "$LOG"\n'

    audit_path = qcp_case_coq_dir(workspace_path) / "run_audit.sh"
    audit_path.write_text(script, encoding="utf-8")
    audit_path.chmod(0o555)
    return audit_path


def collect_qcp_annotated_c(workspace_path: Path, annotated_c_path: Path) -> str:
    qcp_annotated = qcp_agent_c_path(workspace_path, annotated_c_path)
    if not qcp_annotated.exists():
        return f"missing QCP annotated C: {qcp_annotated}"
    shutil.copy2(qcp_annotated, annotated_c_path)
    return f"collected QCP annotated C: {annotated_c_path} <- {qcp_annotated}"


def collect_qcp_mirror_logs(workspace_path: Path) -> list[str]:
    qcp_logs_dir = QCP_CAV_EXAMPLES_ROOT / workspace_path.name / "logs"
    output_logs_dir = workspace_path / "logs"
    copied: list[str] = []
    if not qcp_logs_dir.exists():
        copied.append(f"missing QCP logs directory: {qcp_logs_dir}")
        return copied
    output_logs_dir.mkdir(parents=True, exist_ok=True)
    for name in ("issues.md", "metrics.md"):
        source = qcp_logs_dir / name
        if not source.exists():
            copied.append(f"missing QCP log: {source}")
            continue
        target = output_logs_dir / name
        shutil.copy2(source, target)
        copied.append(f"collected QCP log: {target} <- {source}")
    return copied


def update_issues_on_failure(issues_path: Path, stage: str, exit_code: int, stderr_log: Path) -> None:
    issues_path.parent.mkdir(parents=True, exist_ok=True)
    if issues_path.exists():
        existing = issues_path.read_text(encoding="utf-8").rstrip() + "\n\n"
    else:
        existing = "# Execution Issues\n\n"
    block = (
        "## External Agent Failure\n\n"
        f"- Stage: `{stage}`\n"
        f"- Exit code: `{exit_code}`\n"
        f"- Stderr log: `{stderr_log}`\n"
    )
    issues_path.write_text(existing + block, encoding="utf-8")


def update_issues_on_protocol_violation(
    issues_path: Path,
    reason: str,
    audit_detail: str,
    final_result_detail: str,
    last_message_path: Path,
) -> None:
    issues_path.parent.mkdir(parents=True, exist_ok=True)
    if issues_path.exists():
        existing = issues_path.read_text(encoding="utf-8").rstrip() + "\n\n"
    else:
        existing = "# Execution Issues\n\n"
    block = (
        "## Agent Protocol Violation\n\n"
        f"- Reason: `{reason}`\n"
        f"- Audit detail: `{audit_detail}`\n"
        f"- Final result detail: `{final_result_detail}`\n"
        f"- Last message: `{last_message_path}`\n"
        "- Expected behavior: keep proving/editing until QCP final-check succeeds, "
        "external timeout stops the run, or a contract-program mismatch blocker "
        "requires Contract/user decision.\n"
    )
    issues_path.write_text(existing + block, encoding="utf-8")


def verify_workspace_completed(workspace_path: Path) -> tuple[bool, str]:
    metrics_md = metrics_path(workspace_path)
    if not metrics_md.exists():
        return False, f"missing_metrics:{metrics_md}"

    lines = metrics_md.read_text(encoding="utf-8", errors="replace").splitlines()
    saw_success = False
    saw_fail = False
    for raw_line in lines:
        # Tolerate markdown decoration the agent sometimes adds, e.g.
        # `**Final Result: Success (confirmed in round 7)**` — strip `*`/backticks
        # and match the marker as a substring rather than the whole line.
        cleaned = raw_line.replace("*", "").replace("`", "").strip()
        if "Final Result: Success" in cleaned:
            saw_success = True
        elif "Final Result: Fail" in cleaned:
            saw_fail = True

    if saw_success:
        return True, "metrics_contains_final_result_success"
    if saw_fail:
        return False, "metrics_contains_final_result_fail"
    return False, "metrics_missing_final_result"


def verify_workspace_final_result(workspace_path: Path) -> str:
    """Return the agent-declared final result state from metrics.md."""
    _, detail = verify_workspace_completed(workspace_path)
    return detail


def verify_proof_artifact_check(
    workspace_path: Path,
    function_name: str,
    input_v_path: Path | None,
    annotated_c_path: Path,
    input_path: Path,
) -> tuple[bool, str]:
    generated_dir = workspace_path / "coq" / "generated"
    manual_path = generated_dir / f"{function_name}_proof_manual.v"
    if not manual_path.exists():
        missing = [str(manual_path)]
    else:
        missing = []
    if missing:
        return False, "missing_generated_files:" + ",".join(missing)

    if proof_manual_has_obligations(generated_dir, function_name):
        return False, f"proof_manual_has_obligations:{manual_path}"

    ok, compile_logs = compile_generated_via_qcp_mirror(
        workspace_path,
        function_name,
        input_path,
        input_v_path,
        annotated_c_path,
    )
    log_path = workspace_path / "logs" / "audit_check_coqc.log"
    log_path.write_text("\n\n".join(compile_logs) + "\n", encoding="utf-8")
    if not ok:
        return False, f"audit_check_coqc_failed:{log_path}"

    return True, f"audit_check_success:{log_path}"


def verify_unified_cheating_audit_check(
    workspace_path: Path,
    *,
    input_path: Path | None = None,
    input_v_path: Path | None = None,
    annotated_c_path: Path | None = None,
) -> tuple[bool, str]:
    """Run the single runner-side artifact audit."""
    result = check_verify_audit.scan_workspace(
        workspace_path,
        input_path=input_path,
        input_v_path=input_v_path,
        annotated_c_path=annotated_c_path,
    )
    log_path = workspace_path / "logs" / "verify_audit.json"
    log_path.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    summary = result["summary"]
    if not result["ok"]:
        categories = ",".join(summary["categories"].keys())
        return False, f"verify_audit_failed:{log_path}:categories={categories}"
    return True, f"verify_audit_success:{log_path}"


def verify_transcript_leakage_check(workspace_path: Path) -> tuple[bool, str]:
    """Reject answer-bearing or cross-run reads recorded in agent transcripts."""
    transcripts = check_leakage.discover_transcripts([workspace_path])
    findings = check_leakage.scan_paths([workspace_path])
    summary = check_leakage.summarize(findings, len(transcripts))
    log_path = workspace_path / "logs" / "leakage_audit.json"
    log_path.write_text(json.dumps({
        "summary": summary,
        "findings": [check_leakage.asdict(item) for item in findings],
    }, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    if not summary["clean"]:
        categories = ",".join(summary["categories"])
        return False, f"leakage_audit_failed:{log_path}:categories={categories}"
    return True, f"leakage_audit_success:{log_path}"


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalize_c_without_annotations(text: str) -> str:
    """Token-aware executable C normalization shared with the final audit."""
    return check_verify_audit.normalize_c_without_annotations(text)


def verify_audit_check(
    *,
    workspace_path: Path,
    function_name: str,
    input_path: Path,
    input_v_path: Path | None,
    annotated_c_path: Path,
) -> tuple[bool, str]:
    checks: list[tuple[bool, str]] = []

    checks.append(verify_transcript_leakage_check(workspace_path))
    if not checks[-1][0]:
        return False, ";".join(detail for _, detail in checks)

    checks.append(verify_unified_cheating_audit_check(
        workspace_path=workspace_path,
        input_path=input_path,
        input_v_path=input_v_path,
        annotated_c_path=annotated_c_path,
    ))
    if not checks[-1][0]:
        return False, ";".join(detail for _, detail in checks)

    checks.append(verify_proof_artifact_check(workspace_path, function_name, input_v_path, annotated_c_path, input_path))
    if not checks[-1][0]:
        return False, ";".join(detail for _, detail in checks)

    return True, ";".join(detail for _, detail in checks)


def strip_c_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    return re.sub(r"//.*", "", text)


def is_loop_free_candidate(input_path: Path) -> tuple[bool, str]:
    """Conservative gate for deterministic verify without an external agent."""
    text = strip_c_comments(input_path.read_text(encoding="utf-8", errors="replace"))
    forbidden = (r"\bfor\b", r"\bwhile\b", r"\bdo\b", r"\bswitch\b", r"\bgoto\b")
    for pattern in forbidden:
        if re.search(pattern, text):
            return False, f"has_control_flow:{pattern}"
    if not re.search(r"\b\w+(?:\s*\*)?\s+\w+\s*\([^)]*\)\s*\{", text):
        return False, "not_simple_function"
    return True, "loop_free"


def snapshot_generated_for_reference(workspace_path: Path, function_name: str) -> Path | None:
    generated_dir = workspace_path / "coq" / "generated"
    if not generated_dir.exists() or not any(generated_dir.glob(f"{function_name}_*.v")):
        return None
    last_dir = workspace_path / "coq" / "last"
    if last_dir.exists():
        shutil.rmtree(last_dir)
    shutil.copytree(generated_dir, last_dir)
    return last_dir


def run_symexec(
    workspace_path: Path,
    annotated_c_path: Path,
    function_name: str,
    timeout_seconds: int = 120,
    *,
    preserve_manual: bool = False,
) -> tuple[int, str, str]:
    generated_dir = workspace_path / "coq" / "generated"
    generated_dir.mkdir(parents=True, exist_ok=True)
    _phase_log(workspace_path, "symexec_init_start")
    last_dir = snapshot_generated_for_reference(workspace_path, function_name)
    if last_dir is not None:
        _phase_log(workspace_path, "symexec_previous_generated_snapshot", str(last_dir))
    suffixes_to_refresh = ("goal", "proof_auto", "goal_check") if preserve_manual else ("goal", "proof_auto", "proof_manual", "goal_check")
    for suffix in suffixes_to_refresh:
        old = generated_dir / f"{function_name}_{suffix}.v"
        if old.exists():
            old.unlink()
    logic_path = f"SimpleC.EE.CAV.{workspace_path.name}"
    cmd = [
        str(REPO_ROOT / "QualifiedCProgramming" / "linux-binary" / "symexec"),
        f"--goal-file={generated_dir / f'{function_name}_goal.v'}",
        f"--proof-auto-file={generated_dir / f'{function_name}_proof_auto.v'}",
        f"--proof-manual-file={generated_dir / f'{function_name}_proof_manual.v'}",
        f"--coq-logic-path={logic_path}",
        f"-I{REPO_ROOT / 'QualifiedCProgramming' / 'QCP_examples' / 'stdlib'}/",
        "-slp", str(REPO_ROOT / "QualifiedCProgramming" / "QCP_examples" / "stdlib") + "/", "SimpleC.StdLib",
        # Strategy lib path = canonical QCP_demos_LLM strategies, qualified to
        # SimpleC.EE.QCP_demos_LLM so generated goal.v emits prefixed requires
        # (`From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal`),
        # which resolve uniquely even with duplicate demo dirs on the load-path.
        # humaneval cases reuse the generic, pre-built int/char-array strategies.
        f"-I{REPO_ROOT / 'QualifiedCProgramming' / 'QCP_examples' / 'QCP_demos_LLM'}/",
        "-slp", str(REPO_ROOT / "QualifiedCProgramming" / "QCP_examples" / "QCP_demos_LLM") + "/", "SimpleC.EE.QCP_demos_LLM",
        f"--input-file={annotated_c_path}",
        "--no-exec-info",
    ]
    try:
        proc = subprocess.run(
            cmd,
            cwd=REPO_ROOT / "QualifiedCProgramming",
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout_seconds,
        )
    except subprocess.TimeoutExpired:
        return 124, "", f"symexec timed out after {timeout_seconds}s"
    except OSError as exc:
        return 127, "", f"symexec not runnable: {exc}"
    return proc.returncode, proc.stdout, proc.stderr


PROOF_BYPASS_RE = re.compile(
    r"(?<![A-Za-z_])(Admitted|Abort|admit|give_up)(?![A-Za-z_])"
    r"|^\s*(Axiom|Hypothesis|Parameter|Parameters|Conjecture|Variable|Variables|Declare)\b",
    re.MULTILINE,
)


def proof_file_has_obligations(proof_file: Path) -> bool:
    if not proof_file.exists():
        return True
    text = proof_file.read_text(encoding="utf-8", errors="replace")
    return bool(PROOF_BYPASS_RE.search(text))


def proof_manual_has_obligations(generated_dir: Path, function_name: str) -> bool:
    """Verify completion judge: unfinished manual proof work lives in this file.

    QCP's generated auto-proof file has its own generated shape and is accepted
    through the final goal-check. The manual file must contain completed proof
    work, while the final goal-check confirms the combined artifacts.
    """
    return proof_file_has_obligations(generated_dir / f"{function_name}_proof_manual.v")


def collect_qcp_mirror_artifacts(workspace_path: Path, function_name: str) -> list[str]:
    """Collect current target .v artifacts from the workspace's QCP mirror.

    This is an artifact fallback only. Compilation still happens in QCP, and the
    output workspace receives only the target generated .v files, never .vo,
    .glob, .aux, strategy files, or other compile products.
    """
    qcp_examples_dir = QCP_CAV_EXAMPLES_ROOT / workspace_path.name
    generated_dir = workspace_path / "coq" / "generated"
    logs: list[str] = []
    if not qcp_examples_dir.exists():
        logs.append(f"missing QCP mirror: {qcp_examples_dir}")
    else:
        generated_dir.mkdir(parents=True, exist_ok=True)
        standard_names = standard_generated_v_names(function_name)
        for suffix in ("goal", "proof_auto", "proof_manual", "goal_check"):
            source = qcp_examples_dir / f"{function_name}_{suffix}.v"
            if not source.exists():
                logs.append(f"missing QCP artifact: {source}")
                continue
            target = generated_dir / source.name
            shutil.copy2(source, target)
            logs.append(f"collected QCP artifact: {target} <- {source}")
        for source in sorted(qcp_examples_dir.glob("*.v")):
            if source.name in standard_names:
                continue
            target = generated_dir / source.name
            shutil.copy2(source, target)
            logs.append(f"collected QCP extra artifact: {target} <- {source}")
    log_path = workspace_path / "logs" / "artifact_collection.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text("\n".join(logs) + "\n", encoding="utf-8")
    return logs


BARE_REQUIRE_IMPORT_RE = re.compile(r"^\s*Require\s+Import\s+([A-Za-z0-9_ ]+)\s*\.", re.M)
FROM_REQUIRE_IMPORT_RE = re.compile(r"^\s*From\s+([A-Za-z0-9_.]+)\s+Require\s+Import\s+([A-Za-z0-9_ ]+)\s*\.", re.M)


def standard_generated_v_names(function_name: str) -> set[str]:
    return {f"{function_name}_{suffix}.v" for suffix in ("goal", "proof_auto", "proof_manual", "goal_check")}


def original_v_roots(input_path: Path, input_v_path: Path | None) -> list[Path]:
    roots: list[Path] = []
    seen: set[Path] = set()
    for source in ([input_v_path] if input_v_path is not None else []) + imported_coq_dependency_paths(input_path):
        if source is None:
            continue
        resolved = source.resolve()
        if resolved in seen:
            continue
        seen.add(resolved)
        roots.append(source)
    return roots


def _local_v_imports(source: Path) -> list[Path]:
    text = source.read_text(encoding="utf-8", errors="replace")
    deps: list[Path] = []
    for imports in BARE_REQUIRE_IMPORT_RE.findall(text):
        for dep in imports.split():
            candidate = source.parent / f"{dep}.v"
            if candidate.exists():
                deps.append(candidate)
    for prefix, imports in FROM_REQUIRE_IMPORT_RE.findall(text):
        if prefix == "Coq" or prefix.startswith("Coq."):
            continue
        for dep in imports.split():
            candidates = [source.parent / f"{dep}.v"]
            if "." not in prefix:
                candidates.append(source.parent / f"{prefix}_{dep}.v")
            for candidate in candidates:
                if candidate.exists():
                    deps.append(candidate)
                    break
    return deps


def original_v_dependency_closure(input_path: Path, input_v_path: Path | None) -> list[Path]:
    order: list[Path] = []
    seen: set[Path] = set()

    def copy_closure(source: Path) -> None:
        resolved = source.resolve()
        if resolved in seen:
            return
        seen.add(resolved)
        for dep in _local_v_imports(source):
            copy_closure(dep)
        order.append(source)

    for root in original_v_roots(input_path, input_v_path):
        copy_closure(root)
    return order


def stage_original_v_deps(input_path: Path, input_v_path: Path | None, target_dir: Path) -> list[str]:
    target_dir.mkdir(parents=True, exist_ok=True)
    logs: list[str] = []
    for source in original_v_dependency_closure(input_path, input_v_path):
        target = target_dir / source.name
        shutil.copy2(source, target)
        logs.append(f"staged read-only bare spec dep: {target} <- {source}")
    return logs


def check_qcp_deps_specs_unchanged(workspace_path: Path, input_path: Path, input_v_path: Path | None) -> list[str]:
    qcp_deps_dir = qcp_case_deps_dir(workspace_path)
    issues: list[str] = []
    for source in original_v_dependency_closure(input_path, input_v_path):
        staged = qcp_deps_dir / source.name
        if not staged.exists():
            issues.append(f"missing staged bare spec dep: {staged}")
        elif file_sha256(staged) != file_sha256(source):
            issues.append(f"staged bare spec dep modified: {staged} differs from {source}")
    return issues


def _copy_header_deps(source_dir: Path, target_dir: Path) -> list[str]:
    target_dir.mkdir(parents=True, exist_ok=True)
    copied: list[str] = []
    for header in ("verification_stdlib.h", "verification_list.h", "int_array_def.h", "long_array_def.h", "char_array_def.h"):
        source = REPO_ROOT / header
        if source.exists():
            shutil.copy2(source, target_dir / header)
            copied.append(f"staged root header: {target_dir / header} <- {source}")
    for source in sorted(source_dir.glob("*.h")):
        target = target_dir / source.name
        shutil.copy2(source, target)
        copied.append(f"staged input header: {target} <- {source}")
    for source in sorted(source_dir.glob("*.strategies")):
        target = target_dir / source.name
        shutil.copy2(source, target)
        copied.append(f"staged input strategies: {target} <- {source}")
    return copied


def local_strategy_v_sources(*source_dirs: Path, include_checks: bool = False) -> list[Path]:
    seen: set[str] = set()
    sources: list[Path] = []
    suffixes = ("_strategy_goal.v", "_strategy_proof.v")
    if include_checks:
        suffixes = suffixes + ("_strategy_goal_check.v",)
    for source_dir in source_dirs:
        for suffix in suffixes:
            for source in sorted(source_dir.glob(f"*{suffix}")):
                if source.name in seen:
                    continue
                seen.add(source.name)
                sources.append(source)
    return sources


def _rewrite_local_strategy_v(text: str, workspace_logic_path: str, case_module: str) -> str:
    text = re.sub(
        r"Require\s+Import\s+(?:SimpleC\.EE\.)?coins_[0-9]+\s*\.",
        f"Require Import {case_module}.",
        text,
    )
    text = re.sub(
        r"From\s+SimpleC\.EE(?:\.[A-Za-z0-9_]+)*\s+Require\s+Import\s+([A-Za-z0-9_ ]*strategy[A-Za-z0-9_ ]*)\s*\.",
        f"From {workspace_logic_path} Require Import \\1.",
        text,
    )
    return text


def _copy_strategy_v_deps(source_dir: Path, target_dir: Path, *, workspace_logic_path: str, case_module: str) -> list[str]:
    target_dir.mkdir(parents=True, exist_ok=True)
    copied: list[str] = []
    for source in local_strategy_v_sources(source_dir, include_checks=True):
        target = target_dir / source.name
        text = source.read_text(encoding="utf-8", errors="replace")
        target.write_text(_rewrite_local_strategy_v(text, workspace_logic_path, case_module), encoding="utf-8")
        shutil.copystat(source, target)
        copied.append(f"staged local strategy Coq: {target} <- {source}")
    return copied


def local_coq_dependency_order(root_v: Path, staged_dir: Path) -> list[Path]:
    """Return local staged Coq files needed for root_v, deps before users."""
    order: list[Path] = []
    visiting: set[str] = set()
    done: set[str] = set()

    def visit(module: str) -> None:
        if module in done or module in visiting:
            return
        path = staged_dir / f"{module}.v"
        if not path.exists():
            return
        visiting.add(module)
        text = path.read_text(encoding="utf-8", errors="replace")
        for imports in BARE_REQUIRE_IMPORT_RE.findall(text):
            for dep in imports.split():
                if (staged_dir / f"{dep}.v").exists():
                    visit(dep)
        for prefix, imports in FROM_REQUIRE_IMPORT_RE.findall(text):
            if prefix == "Coq" or prefix.startswith("Coq."):
                continue
            for dep in imports.split():
                if (staged_dir / f"{dep}.v").exists():
                    visit(dep)
                    continue
                if "." not in prefix:
                    candidate = f"{prefix}_{dep}"
                    if (staged_dir / f"{candidate}.v").exists():
                        visit(candidate)
        visiting.remove(module)
        done.add(module)
        order.append(path)

    visit(root_v.stem)
    return order


def canonicalize_manual_goal_import(manual_path: Path, function_name: str, logic_path: str) -> None:
    text = manual_path.read_text(encoding="utf-8", errors="replace")
    pattern = re.compile(
        rf"^\s*From\s+SimpleC\.EE(?:\.[A-Za-z0-9_]+)*\s+Require\s+Import\s+{re.escape(function_name)}_goal\s*\.",
        re.M,
    )
    replacement = f"From {logic_path} Require Import {function_name}_goal."
    new_text, count = pattern.subn(replacement, text)
    if count == 0:
        bare_pattern = re.compile(rf"^\s*Require\s+Import\s+{re.escape(function_name)}_goal\s*\.", re.M)
        new_text = bare_pattern.sub(replacement, text)
    if new_text != text:
        manual_path.write_text(new_text, encoding="utf-8")


def acquire_qcp_mirror_lock(workspace_name: str, timeout_seconds: int) -> Path:
    QCP_CAV_LOCK_ROOT.mkdir(parents=True, exist_ok=True)
    lock_dir = QCP_CAV_LOCK_ROOT / workspace_name
    deadline = time.time() + max(1, timeout_seconds)
    while True:
        try:
            lock_dir.mkdir()
            (lock_dir / "pid").write_text(str(os.getpid()) + "\n", encoding="utf-8")
            return lock_dir
        except FileExistsError:
            if time.time() >= deadline:
                raise TimeoutError(f"timed out waiting for QCP mirror lock: {lock_dir}")
            time.sleep(0.2)


def compile_generated_via_qcp_mirror(
    workspace_path: Path,
    function_name: str,
    input_path: Path,
    input_v_path: Path | None,
    annotated_c_path: Path,
    timeout_seconds: int = 120,
) -> tuple[bool, list[str]]:
    """Run the official Coq chain from a QCP examples mirror.

    The generated Coq files are placed under
    ``SeparationLogic/examples/CAV/<workspace>`` and compiled with QCP's normal
    ``-R examples SimpleC.EE`` load-path. Bare input spec imports are staged
    inside the same case mirror under ``deps/`` and exposed with
    ``-Q examples/CAV/<workspace>/deps ""``.
    """
    workspace_name = workspace_path.name
    qcp_input_dir = QCP_CAV_INPUT_ROOT / workspace_name
    qcp_examples_dir = qcp_case_coq_dir(workspace_path)
    qcp_deps_dir = qcp_case_deps_dir(workspace_path)
    generated_dir = workspace_path / "coq" / "generated"
    manual_path = generated_dir / f"{function_name}_proof_manual.v"
    logs: list[str] = []
    lock_dir: Path | None = None

    try:
        try:
            lock_dir = acquire_qcp_mirror_lock(workspace_name, timeout_seconds)
            logs.append(f"acquired QCP mirror lock: {lock_dir}")
        except TimeoutError as exc:
            logs.append(str(exc))
            return False, logs

        for directory in (qcp_input_dir, qcp_examples_dir):
            if directory.exists():
                shutil.rmtree(directory)
            directory.mkdir(parents=True, exist_ok=True)

        qcp_annotated = qcp_input_dir / annotated_c_path.name
        shutil.copy2(annotated_c_path, qcp_annotated)
        logs.append(f"staged annotated C: {qcp_annotated} <- {annotated_c_path}")
        logs.extend(_copy_header_deps(input_path.parent, qcp_input_dir))
        logs.extend(stage_original_v_deps(input_path, input_v_path, qcp_deps_dir))
        logs.extend(
            _copy_strategy_v_deps(
                input_path.parent,
                qcp_examples_dir,
                workspace_logic_path=f"SimpleC.EE.CAV.{workspace_name}",
                case_module=input_path.stem,
            )
        )
        logic_path = f"SimpleC.EE.CAV.{workspace_name}"
        qcp_manual_path = qcp_examples_dir / manual_path.name
        standard_names = standard_generated_v_names(function_name)
        for source in sorted(generated_dir.glob("*.v")):
            if source.name in standard_names:
                continue
            target = qcp_examples_dir / source.name
            shutil.copy2(source, target)
            logs.append(f"staged local generated dep: {target} <- {source}")
        shutil.copy2(manual_path, qcp_manual_path)
        canonicalize_manual_goal_import(qcp_manual_path, function_name, logic_path)
        logs.append(f"staged proof_manual: {qcp_manual_path} <- {manual_path}")

        sym_cmd = [
            str(QCP_ROOT / "linux-binary" / "symexec"),
            f"--goal-file=SeparationLogic/examples/CAV/{workspace_name}/{function_name}_goal.v",
            f"--proof-auto-file=SeparationLogic/examples/CAV/{workspace_name}/{function_name}_proof_auto.v",
            f"--proof-manual-file=SeparationLogic/examples/CAV/{workspace_name}/{function_name}_proof_manual.v",
            f"--coq-logic-path={logic_path}",
            "-IQCP_examples/stdlib/",
            "-slp", "QCP_examples/stdlib/", "SimpleC.StdLib",
            "-IQCP_examples/QCP_demos_LLM/",
            "-slp", "QCP_examples/QCP_demos_LLM/", "SimpleC.EE.QCP_demos_LLM",
            f"--input-file=QCP_examples/CAV/{workspace_name}/{qcp_annotated.name}",
            "--no-exec-info",
        ]
        try:
            proc = subprocess.run(
                sym_cmd,
                cwd=QCP_ROOT,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=timeout_seconds,
            )
            logs.append("$ " + " ".join(sym_cmd) + f"\nrc={proc.returncode}\n{proc.stdout}{proc.stderr}")
        except subprocess.TimeoutExpired:
            logs.append("$ " + " ".join(sym_cmd) + f"\nrc=124\nsymexec timed out after {timeout_seconds}s")
            return False, logs
        except OSError as exc:
            logs.append("$ " + " ".join(sym_cmd) + f"\nrc=127\nsymexec not runnable: {exc}")
            return False, logs
        if proc.returncode != 0:
            return False, logs

        freshness_findings = check_verify_audit.scan_generated_freshness(
            generated_dir,
            qcp_examples_dir,
            case=function_name,
            function_name=function_name,
        )
        if freshness_findings:
            logs.append(
                "[artifact_audit] generated_freshness_failed\n"
                + json.dumps({"findings": freshness_findings}, indent=2, ensure_ascii=False)
            )
            return False, logs
        logs.append("[artifact_audit] generated_freshness_passed")

        extra_q = [(str(qcp_deps_dir), "")]
        coq_files: list[Path] = []
        for source in original_v_dependency_closure(input_path, input_v_path):
            coq_files.append(qcp_deps_dir / source.name)
        for path in local_coq_dependency_order(qcp_examples_dir / f"{function_name}_goal.v", qcp_examples_dir):
            if path.name != f"{function_name}_goal.v":
                coq_files.append(path)
        coq_files.append(qcp_examples_dir / f"{function_name}_goal.v")
        coq_files.append(qcp_examples_dir / f"{function_name}_proof_auto.v")
        for path in local_coq_dependency_order(qcp_manual_path, qcp_examples_dir):
            if path.name not in {f"{function_name}_goal.v", f"{function_name}_proof_auto.v"}:
                coq_files.append(path)
        coq_files.append(qcp_examples_dir / f"{function_name}_goal_check.v")
        deduped_coq_files: list[Path] = []
        seen_coq_files: set[Path] = set()
        for path in coq_files:
            resolved = path.resolve()
            if resolved in seen_coq_files:
                continue
            seen_coq_files.add(resolved)
            deduped_coq_files.append(path)
        coq_files = deduped_coq_files
        for path in coq_files:
            rc, out, err = coq_runner.run_coqc(path, extra_q=extra_q, timeout_seconds=timeout_seconds)
            logs.append(f"$ coqc {path}\nrc={rc}\n{out}{err}")
            if rc != 0:
                return False, logs

        generated_dir.mkdir(parents=True, exist_ok=True)
        for source in sorted(qcp_examples_dir.glob("*.v")):
            if source.name in standard_names:
                continue
            target = generated_dir / source.name
            shutil.copy2(source, target)
            logs.append(f"collected final local generated dep: {target} <- {source}")
        for suffix in ("goal", "proof_auto", "proof_manual", "goal_check"):
            source = qcp_examples_dir / f"{function_name}_{suffix}.v"
            target = generated_dir / source.name
            shutil.copy2(source, target)
            logs.append(f"collected final QCP artifact: {target} <- {source}")
        return True, logs
    finally:
        coq_runner.clean_compile_artifacts(qcp_examples_dir, recursive=False)
        coq_runner.clean_compile_artifacts(qcp_deps_dir, recursive=False)
        if qcp_input_dir.exists():
            shutil.rmtree(qcp_input_dir)
        if qcp_examples_dir.exists():
            shutil.rmtree(qcp_examples_dir)
        if lock_dir is not None and lock_dir.exists():
            shutil.rmtree(lock_dir)


def try_trivial_fast_path(
    *,
    workspace_path: Path,
    annotated_c_path: Path,
    input_path: Path,
    input_v_path: Path | None,
    function_name: str,
    model: str,
    reasoning_effort: str,
    start_iso: str,
    start_wall: float,
) -> tuple[bool, int]:
    if input_v_path is not None:
        return False, 0
    candidate, detail = is_loop_free_candidate(input_path)
    if not candidate:
        emit_log(f"trivial_fast_path_skipped detail={detail}")
        return False, 0

    logs_dir = workspace_path / "logs"
    stdout_log = logs_dir / "deterministic_fast_path_stdout.log"
    stderr_log = logs_dir / "deterministic_fast_path_stderr.log"
    prompt_log = logs_dir / "deterministic_fast_path_prompt.txt"
    last_message = logs_dir / "deterministic_fast_path_last_message.txt"
    prompt_log.write_text("deterministic loop-free fast path; no external agent invoked\n", encoding="utf-8")
    emit_log(f"trivial_fast_path_start detail={detail}")

    rc, symout, symerr = run_symexec(workspace_path, annotated_c_path, function_name)
    stdout_parts = ["# symexec\n", symout]
    stderr_parts = [symerr]
    generated_dir = workspace_path / "coq" / "generated"
    expected = [generated_dir / f"{function_name}_{suffix}.v" for suffix in ("goal", "proof_auto", "proof_manual", "goal_check")]
    if rc != 0 or not all(path.exists() for path in expected):
        stdout_log.write_text("".join(stdout_parts), encoding="utf-8")
        stderr_log.write_text("".join(stderr_parts), encoding="utf-8")
        emit_log(f"trivial_fast_path_failed stage=symexec rc={rc}")
        return False, 0

    if proof_manual_has_obligations(generated_dir, function_name):
        stdout_log.write_text("".join(stdout_parts), encoding="utf-8")
        stderr_log.write_text("".join(stderr_parts), encoding="utf-8")
        emit_log("trivial_fast_path_failed stage=proof_manual_obligations")
        return False, 0

    stdout_parts.append(
        "\n# audit\n"
        "Skipping pre-audit coqc replay; verify_audit_check owns the single "
        "authoritative compile pass for this deterministic fast path.\n"
    )
    stdout_log.write_text("".join(stdout_parts), encoding="utf-8")
    stderr_log.write_text("".join(stderr_parts), encoding="utf-8")

    gates_ok, gates_detail = verify_audit_check(
        workspace_path=workspace_path,
        function_name=function_name,
        input_path=input_path,
        input_v_path=input_v_path,
        annotated_c_path=annotated_c_path,
    )
    if not gates_ok:
        emit_log(f"trivial_fast_path_failed stage=audit_check detail={gates_detail}")
        return False, 0

    coq_runner.clean_compile_artifacts(workspace_path / "coq")
    issues = workspace_path / "logs" / "issues.md"
    issues.write_text(
        "# Issues Log\n\n"
        "No issues encountered. Deterministic loop-free fast path completed "
        "symexec and all generated Coq compilation without invoking an external agent.\n",
        encoding="utf-8",
    )
    last_message.write_text(
        "Deterministic loop-free fast path completed successfully.\n",
        encoding="utf-8",
    )
    annotated_snapshot = save_annotated_snapshot(workspace_path, annotated_c_path)
    annotated_cleanup = cleanup_global_annotated_after_snapshot(annotated_c_path, annotated_snapshot)
    write_metrics(
        metrics_path(workspace_path),
        status="Success",
        attempts=0,
        last_agent_exit=0,
        start_iso=start_iso,
        end_iso=iso_now(),
        wall_clock_seconds=time.time() - start_wall,
        agent="deterministic-fast-path",
        model=model,
        reasoning_effort=reasoning_effort,
        usage=None,
        prompt_path=prompt_log,
        stdout_jsonl=stdout_log,
        stdout_timeline=None,
        stderr_log=stderr_log,
        last_message_path=last_message,
        input_c=input_path,
        input_v=input_v_path,
        annotated_snapshot=annotated_snapshot,
        annotated_cleanup=annotated_cleanup,
    )
    emit_log("trivial_fast_path_success")
    return True, 0


def bootstrap_workspace(workspace_path: Path, input_path: Path, input_v_path: Path | None, function_name: str) -> Path:
    (workspace_path / "logs").mkdir(parents=True, exist_ok=True)
    (workspace_path / "original").mkdir(parents=True, exist_ok=True)
    (workspace_path / "coq").mkdir(parents=True, exist_ok=True)
    (REPO_ROOT / "annotated").mkdir(parents=True, exist_ok=True)

    original_c = workspace_path / "original" / input_path.name
    annotated_c = REPO_ROOT / "annotated" / f"{workspace_path.name}.c"
    shutil.copy2(input_path, original_c)
    shutil.copy2(input_path, annotated_c)

    # Provision bare-include headers next to the annotated C so symexec resolves
    # both common verification headers and task-local headers such as sll_def.h.
    include_names = {
        "verification_stdlib.h",
        "verification_list.h",
        "int_array_def.h",
        "char_array_def.h",
    }
    include_names.update(re.findall(r'#\s*include\s+"([^"]+)"', input_path.read_text(encoding="utf-8", errors="replace")))
    for _h in sorted(include_names):
        if "/" in _h or "\\" in _h:
            continue
        _src = input_path.parent / _h
        if _src.exists():
            shutil.copy2(_src, REPO_ROOT / "annotated" / _h)

    if input_v_path is not None:
        dst_v = workspace_path / "original" / input_v_path.name
        shutil.copy2(input_v_path, dst_v)
    for dep_v in imported_coq_dependency_paths(input_path):
        dst_v = workspace_path / "original" / dep_v.name
        if input_v_path is not None and dep_v.resolve() == input_v_path.resolve():
            continue
        shutil.copy2(dep_v, dst_v)

    return annotated_c


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run an agent to execute the full verify workflow.")
    parser.add_argument("input_c", help="Path to input C file, relative to repo root or absolute.")
    parser.add_argument("function_name_positional", nargs="?", help="Optional function name to verify. Kept for CLI compatibility.")
    parser.add_argument("--function-name", help="Function name to verify. Preferred form.")
    parser.add_argument("--skill", default=str(DEFAULT_SKILL), help="Path to verification skill markdown.")
    parser.add_argument("--workspace-name", help="Explicit workspace stem; defaults to input file stem.")
    parser.add_argument("--timestamp", help="Explicit verify timestamp; defaults to current local time.")
    parser.add_argument("--model", default=None, help="Agent model. Defaults to config, else built-in per agent.")
    parser.add_argument(
        "--reasoning-effort",
        default=None,
        help="Agent reasoning effort. Defaults to config, else medium.",
    )
    parser.add_argument("--dry-run", action="store_true", help="Prepare workspace and prompt, but do not invoke the agent.")
    parser.add_argument("--config", default=None, help="Path to agents.json config.")
    parser.add_argument("--agent", choices=["codex", "claude", "kimicode", "opencode"], default=None)
    parser.add_argument("--codex-bin", default=None, help="Codex CLI binary.")
    parser.add_argument("--claude-bin", default=None, help="Claude CLI binary.")
    parser.add_argument("--kimicode-bin", default=None, help="Kimi Code CLI binary.")
    parser.add_argument("--opencode-bin", default=None, help="OpenCode CLI binary.")
    parser.add_argument("--timeout-seconds", type=int, default=5400, help="Kill the external agent run if it exceeds this wall-clock timeout.")
    parser.add_argument("--restart-context-file", default=None, help="File whose content (e.g. audit check feedback) is injected into the round-1 prompt on a re-run.")
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()

    cfg = agent_config.load(args.config)
    agent = args.agent or cfg.agent("codex")
    builtin_model = DEFAULT_CLAUDE_MODEL if agent == "claude" else ("kimi-code/kimi-for-coding" if agent == "kimicode" else DEFAULT_MODEL)
    model = args.model or cfg.default_model(agent, builtin_model)
    metrics_model = cfg.model_display(agent, model)
    reasoning_effort = (
        agent_config.kimicode_reasoning_effort(args.reasoning_effort, cfg.kimicode_thinking(True))
        if agent == "kimicode"
        else (args.reasoning_effort or cfg.reasoning_effort(DEFAULT_REASONING_EFFORT))
    )
    codex_bin = args.codex_bin or cfg.bin("codex", "codex")
    claude_bin = args.claude_bin or cfg.bin("claude", "claude")
    kimicode_bin = args.kimicode_bin or cfg.bin("kimicode", "kimi")
    opencode_bin = args.opencode_bin or cfg.bin("opencode", "opencode")

    input_path = Path(args.input_c)
    if not input_path.is_absolute():
        input_path = (REPO_ROOT / input_path).resolve()
    skill_path = Path(args.skill)
    if not skill_path.is_absolute():
        skill_path = (REPO_ROOT / skill_path).resolve()

    if not input_path.exists():
        print(f"input file not found: {input_path}", file=sys.stderr)
        return 2
    if input_path.suffix != ".c":
        print(f"input file must be a .c file: {input_path}", file=sys.stderr)
        return 2
    if not skill_path.exists():
        print(f"skill file not found: {skill_path}", file=sys.stderr)
        return 2

    function_name = args.function_name or args.function_name_positional
    if not function_name:
        print("function name is required: pass --function-name NAME or a positional NAME", file=sys.stderr)
        return 2

    input_v_path = paired_input_v(input_path)

    workspace_stem = args.workspace_name or stem_from_input(input_path)
    workspace_timestamp = args.timestamp or timestamp_now()
    workspace_path = OUTPUT_ROOT / f"verify_{workspace_timestamp}_{workspace_stem}"
    annotated_c_path = bootstrap_workspace(workspace_path, input_path, input_v_path, function_name)
    qcp_stage = stage_qcp_mirror_for_agent(workspace_path, input_path, input_v_path, annotated_c_path, function_name)
    emit_log(f"workspace={workspace_path}")
    emit_log(f"input_c={input_path}")
    emit_log(f"function_name={function_name}")
    emit_log(f"input_v={input_v_path if input_v_path else '<not provided>'}")
    emit_log(f"annotated_c={annotated_c_path}")
    emit_log(f"qcp_agent_c={qcp_stage['qcp_annotated']}")
    emit_log(f"agent={agent}")
    emit_log(f"model={model}")
    logs_dir = workspace_path / "logs"
    qcp_agent_logs_dir = QCP_CAV_EXAMPLES_ROOT / workspace_path.name / "logs"
    agent_env = build_agent_env(logs_dir if agent == "opencode" else qcp_agent_logs_dir)
    reasoning_effort_supported = (
        codex_supports_reasoning_effort(codex_bin, QCP_ROOT, agent_env)
        if agent == "codex"
        else False
    )
    claude_effort_supported = (
        agent_config.claude_supports_flag(claude_bin, QCP_ROOT, agent_env, "--effort")
        if agent == "claude"
        else False
    )
    emit_log(f"reasoning_effort={reasoning_effort}")
    emit_log(f"reasoning_effort_supported={reasoning_effort_supported}")
    emit_log(f"claude_effort_supported={claude_effort_supported}")
    run_label = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
    prompt_path = logs_dir / f"agent_prompt_{run_label}.txt"
    stdout_jsonl = logs_dir / f"agent_stdout_{run_label}.jsonl"
    stdout_timeline: Path | None = None
    stderr_log = logs_dir / f"agent_stderr_{run_label}.log"
    last_message_path = logs_dir / f"agent_last_message_{run_label}.txt"

    if args.dry_run:
        prompt = build_prompt(skill_path, input_path, input_v_path, function_name, workspace_path, annotated_c_path, 1)
        ensure_parent(prompt_path)
        prompt_path.write_text(prompt, encoding="utf-8")
        annotated_snapshot = save_annotated_snapshot(workspace_path, annotated_c_path)
        annotated_cleanup = cleanup_global_annotated_after_snapshot(annotated_c_path, annotated_snapshot)
        write_metrics(
            metrics_path(workspace_path),
            status="Success",
            attempts=0,
            last_agent_exit=0,
            start_iso=iso_now(),
            end_iso=iso_now(),
            wall_clock_seconds=0.0,
            agent=agent,
            model=metrics_model,
            reasoning_effort=reasoning_effort,
            usage=None,
            prompt_path=prompt_path,
            stdout_jsonl=stdout_jsonl,
            stdout_timeline=None,
            stderr_log=stderr_log,
            last_message_path=last_message_path,
            input_c=input_path,
            input_v=input_v_path,
            annotated_snapshot=annotated_snapshot,
            annotated_cleanup=annotated_cleanup,
        )
        emit_log("dry_run=true")
        print(str(workspace_path))
        return 0

    overall_start_wall = time.time()
    overall_start_iso = iso_now()
    fast_completed, fast_rc = try_trivial_fast_path(
        workspace_path=workspace_path,
        annotated_c_path=annotated_c_path,
        input_path=input_path,
        input_v_path=input_v_path,
        function_name=function_name,
        model=metrics_model,
        reasoning_effort=reasoning_effort,
        start_iso=overall_start_iso,
        start_wall=overall_start_wall,
    )
    if fast_completed:
        print(str(workspace_path))
        return fast_rc

    proof_only_mode = (
        input_v_path is None
        and is_loop_free_candidate(input_path)[0]
        and (workspace_path / "coq" / "generated" / f"{function_name}_goal.v").exists()
    )
    if proof_only_mode:
        emit_log("agent_mode=proof_only_loop_free")

    total_budget_seconds = args.timeout_seconds
    attempt = 0
    proc_returncode = 1
    completed = False
    usage_total: dict[str, int] | None = None

    verify_restart_context = None
    if args.restart_context_file:
        rc_path = Path(args.restart_context_file)
        if rc_path.exists():
            verify_restart_context = rc_path.read_text(encoding="utf-8", errors="replace")

    while attempt < 1:
        attempt += 1
        elapsed_before = time.time() - overall_start_wall
        remaining_budget = total_budget_seconds - elapsed_before
        if remaining_budget <= 0:
            emit_log("agent_exec_budget_exhausted")
            proc_returncode = 124
            break

        run_label = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
        prompt_path = logs_dir / f"agent_prompt_{run_label}.txt"
        stdout_jsonl = logs_dir / f"agent_stdout_{run_label}.jsonl"
        stdout_timeline = logs_dir / f"agent_stdout_{run_label}.jsonl.timeline.tsv"
        stderr_log = logs_dir / f"agent_stderr_{run_label}.log"
        last_message_path = logs_dir / f"agent_last_message_{run_label}.txt"
        qcp_last_message_path = qcp_agent_logs_dir / f"agent_last_message_{run_label}.txt"
        qcp_last_message_arg = qcp_rel(qcp_last_message_path)
        if proof_only_mode:
            prompt = build_proof_only_prompt(
                skill_path,
                input_path,
                input_v_path,
                function_name,
                workspace_path,
                annotated_c_path,
                attempt,
                verify_restart_context,
            )
        else:
            prompt = build_prompt(
                skill_path,
                input_path,
                input_v_path,
                function_name,
                workspace_path,
                annotated_c_path,
                attempt,
                verify_restart_context,
            )
        ensure_parent(prompt_path)
        prompt_path.write_text(prompt, encoding="utf-8")

        round_timeout = max(1, int(remaining_budget))
        cmd = [
            codex_bin,
            "exec",
            "--json",
            "--skip-git-repo-check",
            "--sandbox",
            "workspace-write",
            "--ephemeral",
            "-C",
            str(QCP_ROOT),
            "-o",
            qcp_last_message_arg,
        ]
        emit_log(
            f"agent_exec_start attempt={attempt} round_timeout_seconds={round_timeout} total_budget_seconds={total_budget_seconds}"
        )

        start_wall = time.time()
        start_iso = iso_now()
        failure_detail = None
        try:
            if agent == "claude":
                cmd = [
                    claude_bin,
                    "--print",
                    # not --bare: bare mode refuses OAuth/keychain auth, so subscription
                    # logins fail; empty --setting-sources keeps hooks/plugins/settings out.
                    "--setting-sources",
                    "",
                    "--no-session-persistence",
                    "--permission-mode",
                    "bypassPermissions",
                    "--add-dir",
                    str(REPO_ROOT),
                    str(QCP_ROOT),
                    "--output-format",
                    "stream-json",
                    "--verbose",
                ]
                if model:
                    cmd.extend(["--model", model])
                if reasoning_effort and reasoning_effort not in {"api", "none", "default"} and claude_effort_supported:
                    cmd.extend(["--effort", reasoning_effort])
                proc_returncode = run_agent_with_timeline(
                    cmd,
                    prompt=prompt,
                    stdout_jsonl=stdout_jsonl,
                    stdout_timeline=stdout_timeline,
                    stderr_log=stderr_log,
                    cwd=QCP_ROOT,
                    timeout=round_timeout,
                    env=agent_env,
                )
                last_message = agent_metrics.extract_claude_last_message(stdout_jsonl)
                if last_message is not None:
                    ensure_parent(qcp_last_message_path)
                    qcp_last_message_path.write_text(last_message, encoding="utf-8")
                elif stdout_jsonl.exists():
                    ensure_parent(qcp_last_message_path)
                    qcp_last_message_path.write_text(stdout_jsonl.read_text(encoding="utf-8", errors="replace"), encoding="utf-8")
            elif agent == "kimicode":
                cmd = [
                    kimicode_bin,
                    "--print",
                    "--work-dir",
                    str(QCP_ROOT),
                    "--input-format",
                    "text",
                    "--output-format",
                    "stream-json",
                ]
                if model:
                    cmd.extend(["--model", model])
                cmd.append("--no-thinking" if reasoning_effort == "no-thinking" else "--thinking")
                proc_returncode = run_agent_with_timeline(
                    cmd,
                    prompt=prompt,
                    stdout_jsonl=stdout_jsonl,
                    stdout_timeline=stdout_timeline,
                    stderr_log=stderr_log,
                    cwd=QCP_ROOT,
                    timeout=round_timeout,
                    env=agent_env,
                )
                if stdout_jsonl.exists():
                    ensure_parent(qcp_last_message_path)
                    qcp_last_message_path.write_text(stdout_jsonl.read_text(encoding="utf-8", errors="replace"), encoding="utf-8")
            elif agent == "opencode":
                opencode_model = model
                opencode_provider = os.environ.get("OPENCODE_PROVIDER")
                if opencode_model and "/" not in opencode_model and opencode_provider:
                    opencode_model = f"{opencode_provider}/{opencode_model}"
                cmd = [
                    opencode_bin,
                    "run",
                    "--format",
                    "json",
                    "--agent",
                    "build",
                ]
                if opencode_model:
                    cmd.extend(["--model", opencode_model])
                if reasoning_effort and reasoning_effort not in {"api", "none", "default"}:
                    cmd.extend(["--variant", reasoning_effort])
                cmd.append(prompt)
                proc_returncode = run_agent_with_timeline(
                    cmd,
                    prompt=None,
                    stdout_jsonl=stdout_jsonl,
                    stdout_timeline=stdout_timeline,
                    stderr_log=stderr_log,
                    cwd=QCP_ROOT,
                    timeout=round_timeout,
                    env=agent_env,
                )
                last_message = agent_metrics.extract_opencode_last_message(stdout_jsonl)
                ensure_parent(qcp_last_message_path)
                if last_message is not None:
                    qcp_last_message_path.write_text(last_message, encoding="utf-8")
                elif stdout_jsonl.exists():
                    qcp_last_message_path.write_text(stdout_jsonl.read_text(encoding="utf-8", errors="replace"), encoding="utf-8")
            else:
                cmd = [
                    codex_bin,
                    "exec",
                    "--json",
                    "--skip-git-repo-check",
                    "--sandbox",
                    "workspace-write",
                    "--ephemeral",
                    "-C",
                    str(QCP_ROOT),
                    "-o",
                    qcp_last_message_arg,
                ]
                if model:
                    cmd.extend(["--model", model])
                if reasoning_effort and reasoning_effort_supported:
                    cmd.extend(["--reasoning-effort", reasoning_effort])
                    emit_log(f"codex_reasoning_effort_mode=flag value={reasoning_effort}")
                elif reasoning_effort:
                    cmd.extend(["-c", f"model_reasoning_effort={reasoning_effort}"])
                    emit_log(f"codex_reasoning_effort_mode=config value={reasoning_effort}")
                cmd.append("-")
                proc_returncode = run_agent_with_timeline(
                    cmd,
                    prompt=prompt,
                    stdout_jsonl=stdout_jsonl,
                    stdout_timeline=stdout_timeline,
                    stderr_log=stderr_log,
                    cwd=QCP_ROOT,
                    timeout=round_timeout,
                    env=agent_env,
                )
        except subprocess.TimeoutExpired:
            proc_returncode = 124
            failure_detail = f"external agent run exceeded remaining timeout budget of {round_timeout} seconds"
            emit_log(f"agent_exec_timeout attempt={attempt} detail={failure_detail}")
        end_wall = time.time()
        filter_stderr_in_place(stderr_log)
        if agent == "kimicode":
            try:
                agent_metrics.capture_kimicode_context_usage(
                    logs_dir=workspace_path / "logs",
                    started_at=start_wall,
                    ended_at=end_wall,
                    needles=[str(workspace_path), workspace_stem],
                )
            except Exception as exc:
                emit_log(f"kimicode_usage_capture_error={exc}")
        if agent == "opencode":
            try:
                removed_opencode = agent_metrics.cleanup_opencode_heavy_artifacts(
                    logs_dir=workspace_path / "logs",
                    data_home=agent_env.get("XDG_DATA_HOME"),
                    config_home=agent_env.get("XDG_CONFIG_HOME"),
                    state_home=agent_env.get("XDG_STATE_HOME"),
                    cache_home=agent_env.get("XDG_CACHE_HOME"),
                )
                emit_log(f"opencode_runtime_artifacts_removed={len(removed_opencode)}")
            except Exception as exc:
                emit_log(f"opencode_runtime_cleanup_error={exc}")

        usage_total = agent_metrics.add_usage(usage_total, agent_metrics.parse_usage(agent, stdout_jsonl))
        if qcp_last_message_path.exists():
            ensure_parent(last_message_path)
            shutil.copy2(qcp_last_message_path, last_message_path)
        if not last_message_path.exists():
            last_message = None
            if agent == "claude":
                last_message = agent_metrics.extract_claude_last_message(stdout_jsonl)
            elif agent == "opencode":
                last_message = agent_metrics.extract_opencode_last_message(stdout_jsonl)
            if last_message is None and stdout_jsonl.exists():
                last_message = stdout_jsonl.read_text(encoding="utf-8", errors="replace")
            if last_message is not None:
                ensure_parent(last_message_path)
                last_message_path.write_text(last_message, encoding="utf-8")

        deps_spec_issues = check_qcp_deps_specs_unchanged(workspace_path, input_path, input_v_path)
        if deps_spec_issues:
            update_issues_on_protocol_violation(
                workspace_path / "logs" / "issues.md",
                "agent_modified_staged_deps_specs",
                "; ".join(deps_spec_issues),
                "staged_deps_specs_changed",
                last_message_path,
            )
            emit_log(f"deps_spec_integrity=failed count={len(deps_spec_issues)}")
        else:
            emit_log("deps_spec_integrity=passed")

        if proc_returncode != 0:
            update_issues_on_failure(
                workspace_path / "logs" / "issues.md",
                "external-agent-run",
                proc_returncode,
                stderr_log,
            )
            if failure_detail is not None:
                issues_path = workspace_path / "logs" / "issues.md"
                existing = issues_path.read_text(encoding="utf-8").rstrip() + "\n"
                issues_path.write_text(existing + f"- Detail: `{failure_detail}`\n", encoding="utf-8")
            emit_log(f"agent_exec_failed attempt={attempt} exit_code={proc_returncode}")
        else:
            emit_log(f"agent_exec_completed attempt={attempt} exit_code=0")

        annotated_collection = collect_qcp_annotated_c(workspace_path, annotated_c_path)
        emit_log(f"annotated_collection={annotated_collection}")
        log_collection = collect_qcp_mirror_logs(workspace_path)
        emit_log(f"log_collection count={sum(1 for line in log_collection if line.startswith('collected QCP log:'))}")
        collected = collect_qcp_mirror_artifacts(workspace_path, function_name)
        emit_log(f"artifact_collection count={sum(1 for line in collected if line.startswith('collected QCP artifact:'))}")

        completed, detail = verify_audit_check(
            workspace_path=workspace_path,
            function_name=function_name,
            input_path=input_path,
            input_v_path=input_v_path,
            annotated_c_path=annotated_c_path,
        )
        final_result_detail = verify_workspace_final_result(workspace_path)
        if completed:
            emit_log(f"verify_completed={detail}")
            proc_returncode = 0
            break

        if final_result_detail == "metrics_contains_final_result_fail":
            emit_log(f"verify_agent_declared_fail detail={detail}")
            issues_text = ""
            issues_path = workspace_path / "logs" / "issues.md"
            if issues_path.exists():
                issues_text = issues_path.read_text(encoding="utf-8", errors="replace")
            if (
                "contract_program_mismatch_blocker" not in issues_text
                and "contract_or_original_spec_blocker" not in issues_text
            ):
                update_issues_on_protocol_violation(
                    issues_path,
                    "agent_declared_fail_without_contract_program_mismatch_blocker",
                    detail,
                    final_result_detail,
                    last_message_path,
                )
            if proc_returncode == 0:
                proc_returncode = 1
            break

        elapsed_total = time.time() - overall_start_wall
        if elapsed_total >= total_budget_seconds:
            emit_log("agent_exec_budget_exhausted_after_attempt")
            if proc_returncode == 0:
                proc_returncode = 124
            break

        if final_result_detail != "metrics_contains_final_result_success":
            emit_log(
                f"verify_incomplete attempt={attempt} final_result={final_result_detail} detail={detail}"
            )
            update_issues_on_protocol_violation(
                workspace_path / "logs" / "issues.md",
                "agent_exited_before_success_or_legal_fail",
                detail,
                final_result_detail,
                last_message_path,
            )
            if proc_returncode == 0:
                proc_returncode = 1
            break

        emit_log(f"verify_success_claim_rejected attempt={attempt} detail={detail}")
        if proc_returncode == 0:
            proc_returncode = 1
        break

    # Drop coqc intermediates (.vo/.glob/.aux).
    # from workspace dirs, keeping .v/.c sources. Never touches the shared QCP tree.
    removed = coq_runner.clean_compile_artifacts(workspace_path / "coq")
    removed += coq_runner.clean_compile_artifacts(workspace_path / "original", recursive=False)
    # The input .v (input/<ds>/<name>.v) compiles in place when goal.v Requires it;
    # drop only THIS problem's intermediates (race-safe under parallel verify_batch).
    for _suf in (".vo", ".glob", ".vok", ".vos"):
        _f = input_path.with_suffix(_suf)
        if _f.exists():
            _f.unlink(); removed.append(str(_f))
    _aux = input_path.parent / f".{input_path.stem}.aux"
    if _aux.exists():
        _aux.unlink(); removed.append(str(_aux))
    emit_log(f"cleaned_compile_artifacts count={len(removed)}")

    overall_end_iso = iso_now()
    annotated_snapshot = save_annotated_snapshot(workspace_path, annotated_c_path)
    annotated_cleanup = cleanup_global_annotated_after_snapshot(annotated_c_path, annotated_snapshot)
    write_metrics(
        metrics_path(workspace_path),
        status="Success" if proc_returncode == 0 else "Fail",
        attempts=attempt,
        last_agent_exit=proc_returncode,
        start_iso=overall_start_iso,
        end_iso=overall_end_iso,
        wall_clock_seconds=time.time() - overall_start_wall,
        agent=agent,
        model=model,
        reasoning_effort=reasoning_effort,
        usage=usage_total,
        prompt_path=prompt_path,
        stdout_jsonl=stdout_jsonl,
        stdout_timeline=stdout_timeline,
        stderr_log=stderr_log,
        last_message_path=last_message_path,
        input_c=input_path,
        input_v=input_v_path,
        annotated_snapshot=annotated_snapshot,
        annotated_cleanup=annotated_cleanup,
    )

    emit_log(f"stdout_jsonl={stdout_jsonl}")
    emit_log(f"stdout_timeline={stdout_timeline if stdout_timeline else '<not recorded>'}")
    emit_log(f"stderr_log={stderr_log}")
    emit_log(f"last_message={last_message_path}")

    print(str(workspace_path))
    return proc_returncode


def metrics_path(workspace_path: Path) -> Path:
    return workspace_path / "logs" / "metrics.md"


if __name__ == "__main__":
    sys.exit(main())
