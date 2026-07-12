#!/usr/bin/env python3
"""Run proof-only work from a pre-annotated C input.

This is intentionally separate from ``run_verify.py``. ``run_verify`` owns the
normal verify workflow and its internal fast-path proof-only routing. This
entry point consumes ``annotated_input/<dataset>/<name>.c`` as a complete
annotation, asks the agent to run symexec, then prove ``proof_manual.v``.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import agent_config
import agent_metrics
import run_verify as rv


def emit_log(message: str) -> None:
    print(f"[proof] {message}", flush=True)


def timestamp_now() -> str:
    return dt.datetime.now().strftime("%Y%m%d_%H%M%S")


def iso_now() -> str:
    return dt.datetime.now().astimezone().strftime("%Y-%m-%d %H:%M:%S %z")


def ensure_parent(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def bootstrap_proof_workspace(
    workspace_path: Path,
    input_path: Path,
    input_v_path: Path | None,
    annotated_input_path: Path,
) -> Path:
    (workspace_path / "logs").mkdir(parents=True, exist_ok=True)
    (workspace_path / "original").mkdir(parents=True, exist_ok=True)
    (workspace_path / "coq").mkdir(parents=True, exist_ok=True)
    (rv.REPO_ROOT / "annotated").mkdir(parents=True, exist_ok=True)

    shutil.copy2(input_path, workspace_path / "original" / input_path.name)
    if input_v_path is not None:
        shutil.copy2(input_v_path, workspace_path / "original" / input_v_path.name)
    for dep_v in rv.imported_coq_dependency_paths(input_path):
        if input_v_path is not None and dep_v.resolve() == input_v_path.resolve():
            continue
        shutil.copy2(dep_v, workspace_path / "original" / dep_v.name)

    annotated_c = rv.REPO_ROOT / "annotated" / f"{workspace_path.name}.c"
    shutil.copy2(annotated_input_path, annotated_c)

    include_names = {
        "verification_stdlib.h",
        "verification_list.h",
        "int_array_def.h",
        "char_array_def.h",
    }
    include_text = input_path.read_text(encoding="utf-8", errors="replace")
    include_text += "\n" + annotated_input_path.read_text(encoding="utf-8", errors="replace")
    include_names.update(re.findall(r'#\s*include\s+"([^"]+)"', include_text))
    for header in sorted(include_names):
        if "/" in header or "\\" in header:
            continue
        for directory in (input_path.parent, annotated_input_path.parent):
            source = directory / header
            if source.exists():
                shutil.copy2(source, rv.REPO_ROOT / "annotated" / header)
                break

    return annotated_c


def stage_qcp_mirror_for_proof(
    workspace_path: Path,
    input_path: Path,
    input_v_path: Path | None,
    annotated_input_path: Path,
    annotated_c_path: Path,
    function_name: str,
) -> dict[str, Path]:
    qcp_input_dir = rv.QCP_CAV_INPUT_ROOT / workspace_path.name
    qcp_examples_dir = rv.qcp_case_coq_dir(workspace_path)
    qcp_deps_dir = rv.qcp_case_deps_dir(workspace_path)
    for directory in (qcp_input_dir, qcp_examples_dir):
        if directory.exists():
            shutil.rmtree(directory)
        directory.mkdir(parents=True, exist_ok=True)
    (qcp_examples_dir / "logs").mkdir(parents=True, exist_ok=True)

    qcp_annotated = qcp_input_dir / annotated_c_path.name
    shutil.copy2(annotated_c_path, qcp_annotated)
    rv._copy_header_deps(input_path.parent, qcp_input_dir)
    if annotated_input_path.parent != input_path.parent:
        rv._copy_header_deps(annotated_input_path.parent, qcp_input_dir)
    rv.stage_original_v_deps(input_path, input_v_path, qcp_deps_dir)
    rv._copy_strategy_v_deps(
        input_path.parent,
        qcp_examples_dir,
        workspace_logic_path=f"SimpleC.EE.CAV.{workspace_path.name}",
        case_module=input_path.stem,
    )
    if annotated_input_path.parent != input_path.parent:
        rv._copy_strategy_v_deps(
            annotated_input_path.parent,
            qcp_examples_dir,
            workspace_logic_path=f"SimpleC.EE.CAV.{workspace_path.name}",
            case_module=input_path.stem,
        )
    write_qcp_proof_audit_script(
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


def write_qcp_proof_audit_script(
    *,
    workspace_path: Path,
    input_path: Path,
    input_v_path: Path | None,
    annotated_c_path: Path,
    function_name: str,
) -> Path:
    workspace = workspace_path.name
    qcp_c_rel = f"QCP_examples/CAV/{workspace}/{annotated_c_path.name}"
    coq_dir_rel = f"SeparationLogic/examples/CAV/{workspace}"
    deps_rel = f"examples/CAV/{workspace}/deps"
    log_rel = f"{coq_dir_rel}/logs/agent_audit.log"

    original_c = workspace_path / "original" / input_path.name
    original_text = original_c.read_text(encoding="utf-8", errors="replace")
    expected_executable = rv.normalize_c_without_annotations(original_text)
    expected_contracts = rv.check_verify_audit.extract_contract_specs(original_text)

    coq_args = [
        "-Q", deps_rel, "",
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
    ]

    commands: list[list[str]] = []
    for source in rv.original_v_dependency_closure(input_path, input_v_path):
        commands.append(["bash", "-lc", _shell_join(["cd", "SeparationLogic"]) + " && " + _shell_join(["coqc", *coq_args, f"examples/CAV/{workspace}/deps/{source.name}"])])
    for source in rv.local_strategy_v_sources(input_path.parent, annotated_input_path.parent):
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
    audit_path = rv.qcp_case_coq_dir(workspace_path) / "run_audit.sh"
    audit_path.write_text(script, encoding="utf-8")
    audit_path.chmod(0o555)
    return audit_path


def build_run_proof_prompt(
    skill_path: Path,
    input_path: Path,
    input_v_path: Path | None,
    function_name: str,
    workspace_path: Path,
    annotated_c_path: Path,
    restart_context: str | None = None,
) -> str:
    workspace = workspace_path.name
    qcp_c_rel = f"QCP_examples/CAV/{workspace}/{annotated_c_path.name}"
    coq_dir_rel = f"SeparationLogic/examples/CAV/{workspace}"
    deps_rel = f"examples/CAV/{workspace}/deps"
    symexec_cmd = (
        f"linux-binary/symexec --goal-file={coq_dir_rel}/{function_name}_goal.v "
        f"--proof-auto-file={coq_dir_rel}/{function_name}_proof_auto.v "
        f"--proof-manual-file={coq_dir_rel}/{function_name}_proof_manual.v "
        f"--coq-logic-path=SimpleC.EE.CAV.{workspace} "
        f"-IQCP_examples/stdlib/ "
        f"-slp QCP_examples/stdlib/ SimpleC.StdLib "
        f"-IQCP_examples/QCP_demos_LLM/ "
        f"-slp QCP_examples/QCP_demos_LLM/ SimpleC.EE.QCP_demos_LLM "
        f"--input-file={qcp_c_rel} --no-exec-info"
    )
    coq_args = (
        f"-Q {deps_rel} '' "
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
        "-R listlib ListLib"
    )
    deps_commands = [
        f"cd SeparationLogic && coqc {coq_args} examples/CAV/{workspace}/deps/{source.name}"
        for source in rv.original_v_dependency_closure(input_path, input_v_path)
    ]
    strategy_commands = [
        f"cd SeparationLogic && coqc {coq_args} examples/CAV/{workspace}/{source.name}"
        for source in rv.local_strategy_v_sources(input_path.parent, annotated_input_path.parent)
    ]
    lines = [
        "Run proof stage only. The C file is already fully annotated; do not edit function contracts, executable C, loop invariants, assertions, or any annotation in the staged C.",
        "",
        "Read this repo-level CAV verify skill before working:",
        f"- `{Path('../skills/verify/SKILL.md')}`",
        "",
        rv._qcp_skill_list(),
        "",
        "Mode: run-proof.",
        "First run symexec exactly once from QualifiedCProgramming, then prove the generated proof_manual.v. After proof edits, run the QCP final-check sequence; do not rerun symexec unless the annotation changed.",
        "",
        "Inputs:",
        f"- Input C name: `{input_path.name}` (original/source-integrity baseline)",
        f"- Optional input V name: `{input_v_path.name if input_v_path else '<not provided>'}`",
        f"- Target function: `{function_name}`",
        f"- Active QCP annotated C: `{qcp_c_rel}`",
        f"- Active QCP Coq directory: `{coq_dir_rel}`",
        f"- Active QCP deps directory: `{coq_dir_rel}/deps`",
        "",
        "Run from QualifiedCProgramming:",
        "```bash",
        symexec_cmd,
        *deps_commands,
        *strategy_commands,
        f"cd SeparationLogic && coqc {coq_args} examples/CAV/{workspace}/{function_name}_goal.v",
        f"cd SeparationLogic && coqc {coq_args} examples/CAV/{workspace}/{function_name}_proof_auto.v",
        f"cd SeparationLogic && coqc {coq_args} examples/CAV/{workspace}/{function_name}_proof_manual.v",
        f"cd SeparationLogic && coqc {coq_args} examples/CAV/{workspace}/{function_name}_goal_check.v",
        "```",
        "",
        "Write only `<function>_proof_manual.v` and `logs/issues.md` / `logs/metrics.md` after symexec generates files. Do not edit proof_auto.v, goal.v, goal_check.v, deps, or the annotated C.",
        "Runner acceptance expects the annotated program and contract to stay unchanged, and every manual proof obligation to be justified by real proof work from the available case facts. Separately, you must keep all work inside the active case workspace and must not use prior answers or unrelated runs.",
        "Only finish with Final Result: Success after the QCP final-check sequence succeeds and the mirror is ready for runner acceptance. If symexec fails or the annotation is insufficient, record the blocker in logs/issues.md and finish with Final Result: Fail only for a confirmed contract_program_mismatch_blocker.",
    ]
    if restart_context:
        lines += ["", "Restart feedback:", restart_context.rstrip()]
    return "\n".join(lines) + "\n"


def proof_audit_check(workspace_path: Path, function_name: str, input_path: Path, input_v_path: Path | None, annotated_c_path: Path) -> tuple[bool, str]:
    leakage_ok, leakage_detail = rv.verify_transcript_leakage_check(workspace_path)
    if not leakage_ok:
        return False, leakage_detail
    unified_ok, unified_detail = rv.verify_unified_cheating_audit_check(
        workspace_path=workspace_path,
        input_path=input_path,
        input_v_path=input_v_path,
        annotated_c_path=annotated_c_path,
    )
    if not unified_ok:
        return False, unified_detail
    audit = rv.qcp_case_coq_dir(workspace_path) / "run_audit.sh"
    if not audit.exists():
        return False, f"missing_audit_script:{audit}"
    proc = subprocess.run(
        ["bash", str(audit.relative_to(rv.QCP_ROOT))],
        cwd=rv.QCP_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=300,
    )
    audit_log = rv.qcp_case_coq_dir(workspace_path) / "logs" / "agent_audit.log"
    out_log = workspace_path / "logs" / "audit_check_coqc.log"
    if audit_log.exists():
        shutil.copy2(audit_log, out_log)
    else:
        out_log.write_text(proc.stdout + proc.stderr, encoding="utf-8")
    if proc.returncode != 0:
        return False, f"proof_audit_failed:{out_log}"
    rv.collect_qcp_mirror_artifacts(workspace_path, function_name)
    unified_ok, unified_detail = rv.verify_unified_cheating_audit_check(
        workspace_path,
        input_path=input_path,
        input_v_path=input_v_path,
        annotated_c_path=annotated_c_path,
    )
    if not unified_ok:
        return False, f"proof_audit_failed:{out_log};{unified_detail}"
    artifact_ok, artifact_detail = rv.verify_proof_artifact_check(
        workspace_path,
        function_name,
        input_v_path,
        annotated_c_path,
        input_path,
    )
    if not artifact_ok:
        return False, f"proof_audit_failed:{out_log};{unified_detail};{artifact_detail}"
    return True, f"proof_audit_success:{out_log};{unified_detail};{artifact_detail}"


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run proof-only from a pre-annotated C file.")
    parser.add_argument("input_c", help="Original input C file, relative to repo root or absolute.")
    parser.add_argument("function_name_positional", nargs="?", help="Optional function name.")
    parser.add_argument("--function-name", help="Function name. Preferred form.")
    parser.add_argument("--annotated-input-c", required=True, help="Pre-annotated C file to stage for proof.")
    parser.add_argument("--skill", default=str(rv.DEFAULT_SKILL), help="Path to verification skill markdown.")
    parser.add_argument("--workspace-name", help="Explicit workspace stem; defaults to input file stem.")
    parser.add_argument("--timestamp", help="Explicit timestamp; defaults to current local time.")
    parser.add_argument("--model", default=None)
    parser.add_argument("--reasoning-effort", default=None)
    parser.add_argument("--config", default=None)
    parser.add_argument("--agent", choices=["codex", "claude", "kimicode", "opencode"], default=None)
    parser.add_argument("--codex-bin", default=None)
    parser.add_argument("--claude-bin", default=None)
    parser.add_argument("--kimicode-bin", default=None)
    parser.add_argument("--opencode-bin", default=None)
    parser.add_argument("--timeout-seconds", type=int, default=5400)
    parser.add_argument("--restart-context-file", default=None)
    parser.add_argument("--dry-run", action="store_true")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    cfg = agent_config.load(args.config)
    agent = args.agent or cfg.agent("codex")
    builtin_model = rv.DEFAULT_CLAUDE_MODEL if agent == "claude" else ("kimi-code/kimi-for-coding" if agent == "kimicode" else rv.DEFAULT_MODEL)
    model = args.model or cfg.default_model(agent, builtin_model)
    metrics_model = cfg.model_display(agent, model)
    reasoning_effort = (
        agent_config.kimicode_reasoning_effort(args.reasoning_effort, cfg.kimicode_thinking(True))
        if agent == "kimicode"
        else (args.reasoning_effort or cfg.reasoning_effort(rv.DEFAULT_REASONING_EFFORT))
    )
    codex_bin = args.codex_bin or cfg.bin("codex", "codex")
    claude_bin = args.claude_bin or cfg.bin("claude", "claude")
    kimicode_bin = args.kimicode_bin or cfg.bin("kimicode", "kimi")
    opencode_bin = args.opencode_bin or cfg.bin("opencode", "opencode")

    input_path = Path(args.input_c)
    if not input_path.is_absolute():
        input_path = (rv.REPO_ROOT / input_path).resolve()
    annotated_input_path = Path(args.annotated_input_c)
    if not annotated_input_path.is_absolute():
        annotated_input_path = (rv.REPO_ROOT / annotated_input_path).resolve()
    skill_path = Path(args.skill)
    if not skill_path.is_absolute():
        skill_path = (rv.REPO_ROOT / skill_path).resolve()

    for path, label in ((input_path, "input C"), (annotated_input_path, "annotated input C"), (skill_path, "skill")):
        if not path.exists():
            print(f"{label} not found: {path}", file=sys.stderr)
            return 2
    if input_path.suffix != ".c" or annotated_input_path.suffix != ".c":
        print("input and annotated input must both be .c files", file=sys.stderr)
        return 2
    if args.timeout_seconds < 1:
        print("--timeout-seconds must be positive", file=sys.stderr)
        return 2

    function_name = args.function_name or args.function_name_positional
    if not function_name:
        print("function name is required: pass --function-name NAME or positional NAME", file=sys.stderr)
        return 2
    input_v_path = rv.paired_input_v(input_path)

    workspace_stem = args.workspace_name or rv.stem_from_input(input_path)
    workspace_timestamp = args.timestamp or timestamp_now()
    workspace_path = rv.OUTPUT_ROOT / f"proof_{workspace_timestamp}_{workspace_stem}"
    annotated_c_path = bootstrap_proof_workspace(workspace_path, input_path, input_v_path, annotated_input_path)
    qcp_stage = stage_qcp_mirror_for_proof(workspace_path, input_path, input_v_path, annotated_input_path, annotated_c_path, function_name)
    logs_dir = workspace_path / "logs"
    qcp_agent_logs_dir = rv.QCP_CAV_EXAMPLES_ROOT / workspace_path.name / "logs"
    agent_env = rv.build_agent_env(logs_dir if agent == "opencode" else qcp_agent_logs_dir)
    reasoning_effort_supported = rv.codex_supports_reasoning_effort(codex_bin, rv.QCP_ROOT, agent_env) if agent == "codex" else False
    claude_effort_supported = agent_config.claude_supports_flag(claude_bin, rv.QCP_ROOT, agent_env, "--effort") if agent == "claude" else False

    emit_log(f"workspace={workspace_path}")
    emit_log(f"input_c={input_path}")
    emit_log(f"annotated_input_c={annotated_input_path}")
    emit_log(f"function_name={function_name}")
    emit_log(f"qcp_agent_c={qcp_stage['qcp_annotated']}")
    emit_log(f"agent={agent}")
    emit_log(f"model={model}")
    emit_log(f"reasoning_effort={reasoning_effort}")

    start_wall = time.time()
    start_iso = iso_now()
    run_label = dt.datetime.now().strftime("%Y%m%d_%H%M%S")
    prompt_path = logs_dir / f"agent_prompt_{run_label}.txt"
    stdout_jsonl = logs_dir / f"agent_stdout_{run_label}.jsonl"
    stdout_timeline = logs_dir / f"agent_stdout_{run_label}.jsonl.timeline.tsv"
    stderr_log = logs_dir / f"agent_stderr_{run_label}.log"
    last_message_path = logs_dir / f"agent_last_message_{run_label}.txt"
    qcp_last_message_path = qcp_agent_logs_dir / f"agent_last_message_{run_label}.txt"

    restart_context = None
    if args.restart_context_file:
        rc_path = Path(args.restart_context_file)
        if rc_path.exists():
            restart_context = rc_path.read_text(encoding="utf-8", errors="replace")
    prompt = build_run_proof_prompt(skill_path, input_path, input_v_path, function_name, workspace_path, annotated_c_path, restart_context)
    ensure_parent(prompt_path)
    prompt_path.write_text(prompt, encoding="utf-8")
    if args.dry_run:
        print(str(workspace_path))
        return 0

    proc_returncode = 1
    usage_total: dict[str, int] | None = None
    round_timeout = args.timeout_seconds
    failure_detail = None
    try:
        if agent == "claude":
            cmd = [
                # not --bare: bare mode refuses OAuth/keychain auth, so subscription
                # logins fail; empty --setting-sources keeps hooks/plugins/settings out.
                claude_bin, "--print", "--setting-sources", "", "--no-session-persistence",
                "--permission-mode", "bypassPermissions", "--add-dir", str(rv.REPO_ROOT),
                str(rv.QCP_ROOT), "--output-format", "stream-json", "--verbose",
            ]
            if model:
                cmd.extend(["--model", model])
            if reasoning_effort and reasoning_effort not in {"api", "none", "default"} and claude_effort_supported:
                cmd.extend(["--effort", reasoning_effort])
            proc_returncode = rv.run_agent_with_timeline(cmd, prompt=prompt, stdout_jsonl=stdout_jsonl, stdout_timeline=stdout_timeline, stderr_log=stderr_log, cwd=rv.QCP_ROOT, timeout=round_timeout, env=agent_env)
            last_message = agent_metrics.extract_claude_last_message(stdout_jsonl)
            if last_message is not None:
                ensure_parent(qcp_last_message_path)
                qcp_last_message_path.write_text(last_message, encoding="utf-8")
        elif agent == "kimicode":
            cmd = [kimicode_bin, "--print", "--work-dir", str(rv.QCP_ROOT), "--input-format", "text", "--output-format", "stream-json"]
            if model:
                cmd.extend(["--model", model])
            cmd.append("--no-thinking" if reasoning_effort == "no-thinking" else "--thinking")
            proc_returncode = rv.run_agent_with_timeline(cmd, prompt=prompt, stdout_jsonl=stdout_jsonl, stdout_timeline=stdout_timeline, stderr_log=stderr_log, cwd=rv.QCP_ROOT, timeout=round_timeout, env=agent_env)
            if stdout_jsonl.exists():
                ensure_parent(qcp_last_message_path)
                qcp_last_message_path.write_text(stdout_jsonl.read_text(encoding="utf-8", errors="replace"), encoding="utf-8")
        elif agent == "opencode":
            opencode_model = model
            opencode_provider = os.environ.get("OPENCODE_PROVIDER")
            if opencode_model and "/" not in opencode_model and opencode_provider:
                opencode_model = f"{opencode_provider}/{opencode_model}"
            cmd = [opencode_bin, "run", "--format", "json", "--agent", "build"]
            if opencode_model:
                cmd.extend(["--model", opencode_model])
            if reasoning_effort and reasoning_effort not in {"api", "none", "default"}:
                cmd.extend(["--variant", reasoning_effort])
            cmd.append(prompt)
            proc_returncode = rv.run_agent_with_timeline(cmd, prompt=None, stdout_jsonl=stdout_jsonl, stdout_timeline=stdout_timeline, stderr_log=stderr_log, cwd=rv.QCP_ROOT, timeout=round_timeout, env=agent_env)
            last_message = agent_metrics.extract_opencode_last_message(stdout_jsonl)
            ensure_parent(qcp_last_message_path)
            if last_message is not None:
                qcp_last_message_path.write_text(last_message, encoding="utf-8")
            elif stdout_jsonl.exists():
                qcp_last_message_path.write_text(stdout_jsonl.read_text(encoding="utf-8", errors="replace"), encoding="utf-8")
        else:
            cmd = [codex_bin, "exec", "--json", "--skip-git-repo-check", "--sandbox", "workspace-write", "--ephemeral", "-C", str(rv.QCP_ROOT), "-o", rv.qcp_rel(qcp_last_message_path)]
            if model:
                cmd.extend(["--model", model])
            if reasoning_effort and reasoning_effort_supported:
                cmd.extend(["--reasoning-effort", reasoning_effort])
            elif reasoning_effort:
                cmd.extend(["-c", f"model_reasoning_effort={reasoning_effort}"])
            cmd.append("-")
            proc_returncode = rv.run_agent_with_timeline(cmd, prompt=prompt, stdout_jsonl=stdout_jsonl, stdout_timeline=stdout_timeline, stderr_log=stderr_log, cwd=rv.QCP_ROOT, timeout=round_timeout, env=agent_env)
    except subprocess.TimeoutExpired:
        proc_returncode = 124
        failure_detail = f"external agent run exceeded timeout budget of {round_timeout} seconds"
        emit_log(f"agent_exec_timeout detail={failure_detail}")

    rv.filter_stderr_in_place(stderr_log)
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
    if proc_returncode != 0:
        rv.update_issues_on_failure(workspace_path / "logs" / "issues.md", "external-agent-run", proc_returncode, stderr_log)
        if failure_detail:
            issues_path = workspace_path / "logs" / "issues.md"
            existing = issues_path.read_text(encoding="utf-8").rstrip() + "\n"
            issues_path.write_text(existing + f"- Detail: `{failure_detail}`\n", encoding="utf-8")
        emit_log(f"agent_exec_failed exit_code={proc_returncode}")
    else:
        emit_log("agent_exec_completed exit_code=0")

    annotated_collection = rv.collect_qcp_annotated_c(workspace_path, annotated_c_path)
    emit_log(f"annotated_collection={annotated_collection}")
    log_collection = rv.collect_qcp_mirror_logs(workspace_path)
    emit_log(f"log_collection count={sum(1 for line in log_collection if line.startswith('collected QCP log:'))}")
    collected = rv.collect_qcp_mirror_artifacts(workspace_path, function_name)
    emit_log(f"artifact_collection count={sum(1 for line in collected if line.startswith('collected QCP artifact:'))}")

    completed, detail = proof_audit_check(workspace_path, function_name, input_path, input_v_path, annotated_c_path)
    if completed:
        proc_returncode = 0
        emit_log(f"proof_completed={detail}")
    elif proc_returncode == 0:
        proc_returncode = 1
        rv.update_issues_on_protocol_violation(workspace_path / "logs" / "issues.md", "proof_audit_failed", detail, rv.verify_workspace_final_result(workspace_path), last_message_path)
        emit_log(f"proof_incomplete detail={detail}")

    removed = rv.coq_runner.clean_compile_artifacts(workspace_path / "coq")
    removed += rv.coq_runner.clean_compile_artifacts(workspace_path / "original", recursive=False)
    emit_log(f"cleaned_compile_artifacts count={len(removed)}")

    annotated_snapshot = rv.save_annotated_snapshot(workspace_path, annotated_c_path)
    annotated_cleanup = rv.cleanup_global_annotated_after_snapshot(annotated_c_path, annotated_snapshot)
    rv.write_metrics(
        rv.metrics_path(workspace_path),
        status="Success" if proc_returncode == 0 else "Fail",
        attempts=1,
        last_agent_exit=proc_returncode,
        start_iso=start_iso,
        end_iso=iso_now(),
        wall_clock_seconds=time.time() - start_wall,
        agent=agent,
        model=metrics_model,
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
    print(str(workspace_path))
    return proc_returncode


if __name__ == "__main__":
    sys.exit(main())
