#!/usr/bin/env bash
# Run raw -> contract -> eval -> verify pipelines and archive all stage
# workspaces into pipeline_results/<harness>/<model>/<effort>/, one problem at
# a time with conservative quota-failure retry behavior.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

PIPELINE_RESULTS_ROOT="${PIPELINE_RESULTS_ROOT:-$ROOT/pipeline_results}"
DATASET="${DATASET:-humaneval}"
JOBS="${JOBS:-1}"
CONTRACT_TIMEOUT="${CONTRACT_TIMEOUT:-}"
EVAL_TIMEOUT="${EVAL_TIMEOUT:-}"
VERIFY_TIMEOUT="${VERIFY_TIMEOUT:-}"
CONFIG="${CONFIG:-}"
SKIP_EVAL=0
DRY_RUN=0
FORCE=0
FAST_FAIL_SECONDS="${FAST_FAIL_SECONDS:-120}"
QUOTA_SLEEP_SECONDS="${QUOTA_SLEEP_SECONDS:-18000}"
MAX_FAST_RETRIES="${MAX_FAST_RETRIES:-1}"
MAX_PROBLEMS="${MAX_PROBLEMS:-10}"
MODEL_OVERRIDE="${MODEL_OVERRIDE:-${ARK_MODEL:-${MODEL:-}}}"
ARK_PROFILE_CONFIG="${ARK_PROFILE_CONFIG:-$ROOT/config/ark_api/profiles.json}"
ARK_PROFILE_SELECTED="${ARK_PROFILE:-}"

usage() {
  cat <<'EOF'
usage: scripts/batch_safe_pipeline.sh [options] [config|all] [problem_name ...]

Runs scripts/run_pipeline.py for raw/<dataset>/<problem_name>.md and moves the
pipeline workspace plus its contract/eval/verify workspaces into:
  pipeline_results/<harness>/<model>/<effort>/

If the first positional argument is not a known config label, it is treated as a
problem name and the default config is codex-54-medium.

Configs:
  codex-54-medium
  codex-54-mini-medium
  codex-54-high
  codex-54-low
  codex-55-medium
  codex-55-xhigh
  codex-ark-1-deepseek
  codex-ark-1-glm
  codex-ark-2-deepseek
  codex-ark-2-glm
  codex-ark-3-deepseek
  codex-ark-3-glm
  codex-ark-4-deepseek
  codex-ark-4-glm
  codex-ark-5-deepseek
  codex-ark-5-glm
  opencode-ark-1-deepseek
  opencode-ark-1-glm
  opencode-ark-2-deepseek
  opencode-ark-2-glm
  opencode-ark-3-deepseek
  opencode-ark-3-glm
  opencode-ark-4-deepseek
  opencode-ark-4-glm
  claude-sonnet-medium
  kimi-thinking
  all

Options:
  --dataset NAME         Read raw/<dataset>/*.md. Default: humaneval.
  --jobs N, -j N         Accepted for compatibility; batch-safe runs use jobs=1.
  --results-root DIR     Archive root. Default: pipeline_results.
  --contract-timeout N   Passed to run_pipeline.py.
  --eval-timeout N       Passed to run_pipeline.py.
  --verify-timeout N     Passed to run_pipeline.py.
  --skip-eval            Passed to run_pipeline.py.
  --config PATH          Passed to run_pipeline.py.
  --dry-run              Passed to run_pipeline.py.
  --force                Do not skip problems that already have a successful pipeline result.
  -h, --help             Show this help.

Examples:
  scripts/batch_safe_pipeline.sh codex-54-medium p053_add
  scripts/batch_safe_pipeline.sh --dataset mbpp codex-54-mini-medium mbpp_511_find_Min_Sum
  scripts/batch_safe_pipeline.sh --dataset humaneval codex-54-medium
EOF
}

is_known_config() {
  case "$1" in
    all|codex-54-medium|codex-54-mini-medium|mini|codex-54-high|codex-54-low|codex-55-medium|codex-55-xhigh|claude-sonnet-medium|kimi-thinking|codex-ark|codex-ark-api|opencode-ark|opencode-ark-api|codex-ark-*|opencode-ark-*)
      return 0
      ;;
    *)
      return 1
      ;;
  esac
}

POSITIONAL=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --dataset)
      [[ $# -ge 2 ]] || { echo "missing value for --dataset" >&2; exit 2; }
      DATASET="$2"
      shift 2
      ;;
    --jobs|-j)
      [[ $# -ge 2 ]] || { echo "missing value for $1" >&2; exit 2; }
      JOBS="$2"
      shift 2
      ;;
    --results-root)
      [[ $# -ge 2 ]] || { echo "missing value for --results-root" >&2; exit 2; }
      PIPELINE_RESULTS_ROOT="$2"
      shift 2
      ;;
    --contract-timeout)
      [[ $# -ge 2 ]] || { echo "missing value for --contract-timeout" >&2; exit 2; }
      CONTRACT_TIMEOUT="$2"
      shift 2
      ;;
    --eval-timeout)
      [[ $# -ge 2 ]] || { echo "missing value for --eval-timeout" >&2; exit 2; }
      EVAL_TIMEOUT="$2"
      shift 2
      ;;
    --verify-timeout)
      [[ $# -ge 2 ]] || { echo "missing value for --verify-timeout" >&2; exit 2; }
      VERIFY_TIMEOUT="$2"
      shift 2
      ;;
    --config)
      [[ $# -ge 2 ]] || { echo "missing value for --config" >&2; exit 2; }
      CONFIG="$2"
      shift 2
      ;;
    --skip-eval)
      SKIP_EVAL=1
      shift
      ;;
    --dry-run)
      DRY_RUN=1
      shift
      ;;
    --force)
      FORCE=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    --)
      shift
      while [[ $# -gt 0 ]]; do
        POSITIONAL+=("$1")
        shift
      done
      ;;
    -*)
      echo "unknown option: $1" >&2
      usage >&2
      exit 2
      ;;
    *)
      POSITIONAL+=("$1")
      shift
      ;;
  esac
done

if ! [[ "$JOBS" =~ ^[0-9]+$ ]] || [[ "$JOBS" -lt 1 ]]; then
  echo "--jobs must be a positive integer: $JOBS" >&2
  exit 2
fi

for timeout_name in CONTRACT_TIMEOUT EVAL_TIMEOUT VERIFY_TIMEOUT; do
  timeout_value="${!timeout_name}"
  if [[ -n "$timeout_value" ]] && { ! [[ "$timeout_value" =~ ^[0-9]+$ ]] || [[ "$timeout_value" -lt 1 ]]; }; then
    echo "${timeout_name} must be a positive integer: $timeout_value" >&2
    exit 2
  fi
done

REQUESTED="codex-54-medium"
NAMES=()
if [[ ${#POSITIONAL[@]} -gt 0 ]]; then
  first="${POSITIONAL[0]}"
  if is_known_config "$first"; then
    REQUESTED="$first"
    if [[ ${#POSITIONAL[@]} -gt 1 ]]; then
      NAMES=("${POSITIONAL[@]:1}")
    fi
  else
    NAMES=("${POSITIONAL[@]}")
  fi
fi

CODEX_JOBS="${CODEX_JOBS:-$JOBS}"
CLAUDE_JOBS="${CLAUDE_JOBS:-$JOBS}"
KIMI_JOBS="${KIMI_JOBS:-$JOBS}"
OPENCODE_JOBS="${OPENCODE_JOBS:-$JOBS}"

case "$REQUESTED" in
  codex-ark|codex-ark-api) REQUESTED="codex-ark-2-deepseek" ;;
  opencode-ark|opencode-ark-api) REQUESTED="opencode-ark-2-deepseek" ;;
esac

ark_requested="$REQUESTED"
case "$REQUESTED" in
  codex-ark-*|opencode-ark-*)
    ark_requested="${ark_requested#codex-}"
    ark_requested="${ark_requested#opencode-}"
    ;;
esac
if python3 "$ROOT/scripts/ark_profile_env.py" --config "$ARK_PROFILE_CONFIG" --field model "$ark_requested" >/dev/null 2>&1; then
  ARK_PROFILE_SELECTED="$ark_requested"
fi

safe_path_component() {
  printf '%s\n' "$1" | sed 's#[/[:space:]]#__#g'
}

result_dir_for() {
  local root="$1"
  local harness="$2"
  local model="$3"
  local effort="$4"
  printf '%s/%s/%s/%s\n' "$root" "$(safe_path_component "$harness")" "$(safe_path_component "$model")" "$(safe_path_component "$effort")"
}

# label|agent|model|effort|result_dir|jobs
ark_model="${MODEL_OVERRIDE:-}"
ark_label="${ARK_PROFILE_SELECTED:-ark-profile}"
if [[ -n "$ARK_PROFILE_SELECTED" && -z "$ark_model" ]]; then
  ark_model="$(python3 "$ROOT/scripts/ark_profile_env.py" --config "$ARK_PROFILE_CONFIG" --field model "$ARK_PROFILE_SELECTED")"
fi
RUN_CONFIGS=(
  "codex-54-medium|codex|gpt-5.4|medium|$(result_dir_for "$PIPELINE_RESULTS_ROOT" codex gpt-5.4 medium)|$CODEX_JOBS"
  "codex-54-mini-medium|codex|gpt-5.4-mini|medium|$(result_dir_for "$PIPELINE_RESULTS_ROOT" codex gpt-5.4-mini medium)|$CODEX_JOBS"
  "codex-54-high|codex|gpt-5.4|high|$(result_dir_for "$PIPELINE_RESULTS_ROOT" codex gpt-5.4 high)|$CODEX_JOBS"
  "codex-54-low|codex|gpt-5.4|low|$(result_dir_for "$PIPELINE_RESULTS_ROOT" codex gpt-5.4 low)|$CODEX_JOBS"
  "codex-55-medium|codex|gpt-5.5|medium|$(result_dir_for "$PIPELINE_RESULTS_ROOT" codex gpt-5.5 medium)|$CODEX_JOBS"
  "codex-55-xhigh|codex|gpt-5.5|xhigh|$(result_dir_for "$PIPELINE_RESULTS_ROOT" codex gpt-5.5 xhigh)|$CODEX_JOBS"
  "codex-$ark_label|codex|$ark_model|api|$(result_dir_for "$PIPELINE_RESULTS_ROOT" codex "$ark_model" api)|$CODEX_JOBS"
  "opencode-$ark_label|opencode|$ark_model|api|$(result_dir_for "$PIPELINE_RESULTS_ROOT" opencode "$ark_model" api)|$OPENCODE_JOBS"
  "claude-sonnet-medium|claude|sonnet|medium|$(result_dir_for "$PIPELINE_RESULTS_ROOT" claude sonnet medium)|$CLAUDE_JOBS"
  "kimi-thinking|kimicode|kimi-code/kimi-for-coding|thinking|$(result_dir_for "$PIPELINE_RESULTS_ROOT" kimicode kimi-code/kimi-for-coding thinking)|$KIMI_JOBS"
)

canonical_config() {
  case "$1" in
    mini) printf '%s\n' "codex-54-mini-medium" ;;
    codex-ark|codex-ark-api) printf '%s\n' "codex-ark-2-deepseek" ;;
    opencode-ark|opencode-ark-api) printf '%s\n' "opencode-ark-2-deepseek" ;;
    *) printf '%s\n' "$1" ;;
  esac
}

config_for() {
  local requested_label
  requested_label="$(canonical_config "$1")"
  local config
  for config in "${RUN_CONFIGS[@]}"; do
    if [[ "${config%%|*}" == "$requested_label" ]]; then
      printf '%s\n' "$config"
      return 0
    fi
  done
  return 1
}

raw_names() {
  local raw_dir="raw/$DATASET"
  [[ -d "$raw_dir" ]] || { echo "missing raw dataset directory: $raw_dir" >&2; return 2; }
  find "$raw_dir" -maxdepth 1 -type f -name '*.md' -printf '%f\n' \
    | sed 's/\.md$//' \
    | sort
}

existing_success_names() {
  local result_dir="$1"
  [[ -d "$result_dir" ]] || return 0
  python3 - "$result_dir" <<'PY'
from pathlib import Path
import json
import sys

root = Path(sys.argv[1])
names = set()
for summary in root.glob("pipeline_*/pipeline_summary.json"):
    try:
        data = json.loads(summary.read_text(encoding="utf-8"))
    except Exception:
        continue
    if data.get("status") == "success" and data.get("name"):
        names.add(str(data["name"]))
for name in sorted(names):
    print(name)
PY
}

filter_existing_success() {
  local existing_file="$1"
  shift
  local name
  for name in "$@"; do
    if [[ "$FORCE" -eq 1 ]] || ! grep -qxF "$name" "$existing_file"; then
      printf '%s\n' "$name"
    fi
  done
}

archive_pipeline() {
  local pipeline_dir="$1"
  local result_dir="$2"
  python3 - "$ROOT" "$pipeline_dir" "$result_dir" <<'PY'
from pathlib import Path
import json
import shutil
import sys

root = Path(sys.argv[1]).resolve()
pipeline_dir = Path(sys.argv[2]).resolve()
result_dir = Path(sys.argv[3]).resolve()
output_root = (root / "output").resolve()

def under(path: Path, parent: Path) -> bool:
    try:
        path.relative_to(parent)
        return True
    except ValueError:
        return False

if not pipeline_dir.exists() or not pipeline_dir.is_dir():
    raise SystemExit(f"missing pipeline directory: {pipeline_dir}")
if not under(pipeline_dir, output_root):
    raise SystemExit(f"refusing to archive non-output pipeline dir: {pipeline_dir}")

summary = pipeline_dir / "pipeline_summary.json"
dirs: list[Path] = [pipeline_dir]
if summary.exists():
    try:
        data = json.loads(summary.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise SystemExit(f"bad pipeline summary JSON: {summary}: {exc}") from exc
    for raw in data.get("workspaces", []):
        path = Path(raw).resolve()
        if path.exists() and path.is_dir():
            dirs.append(path)

unique: list[Path] = []
seen: set[Path] = set()
for path in dirs:
    if path in seen:
        continue
    seen.add(path)
    if not under(path, output_root):
        raise SystemExit(f"refusing to archive non-output workspace: {path}")
    if not path.name.startswith(("pipeline_", "contract_", "eval_", "verify_")):
        raise SystemExit(f"refusing to archive unexpected workspace name: {path}")
    unique.append(path)

result_dir.mkdir(parents=True, exist_ok=True)
mappings: dict[str, str] = {}
for source in unique:
    target = (result_dir / source.name).resolve()
    if target.exists():
        raise SystemExit(f"archive target already exists: {target}")
    shutil.move(str(source), str(target))
    mappings[str(source)] = str(target)

text_suffixes = {".json", ".md", ".log", ".txt", ".tsv", ".c", ".v"}
for target_raw in mappings.values():
    target_root = Path(target_raw)
    for path in target_root.rglob("*"):
        if not path.is_file():
            continue
        if path.suffix not in text_suffixes:
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        new_text = text
        for old, new in mappings.items():
            new_text = new_text.replace(old, new)
        if new_text != text:
            path.write_text(new_text, encoding="utf-8")

for target_raw in mappings.values():
    base = Path(target_raw).name
    shutil.rmtree(root / "QualifiedCProgramming" / "QCP_examples" / "CAV" / base, ignore_errors=True)
    shutil.rmtree(root / "QualifiedCProgramming" / ".tmp" / "QCP_examples" / "CAV" / base, ignore_errors=True)
    shutil.rmtree(root / "QualifiedCProgramming" / "SeparationLogic" / "examples" / "CAV" / base, ignore_errors=True)
    shutil.rmtree(root / "QualifiedCProgramming" / ".tmp" / "SeparationLogic" / "examples" / "CAV" / base, ignore_errors=True)
    shutil.rmtree(root / "QualifiedCProgramming" / "SeparationLogic" / "_cav_locks" / base, ignore_errors=True)
    shutil.rmtree(root / "QualifiedCProgramming" / ".tmp" / "SeparationLogic" / "_cav_locks" / base, ignore_errors=True)
    annotated = root / "annotated" / f"{base}.c"
    if annotated.exists():
        annotated.unlink()

for old, new in mappings.items():
    print(f"archived {old} -> {new}")
PY
}

newest_pipeline_for_name_since() {
  local name="$1"
  local marker="$2"
  find "$ROOT/output" -maxdepth 1 -type d -name "pipeline_*_${name}" -newer "$marker" -printf '%T@ %p\n' \
    | sort -nr \
    | awk 'NR == 1 { $1=""; sub(/^ /, ""); print; exit }'
}

run_one() {
  local label="$1"
  local agent="$2"
  local model="$3"
  local effort="$4"
  local result_dir="$5"
  local name="$6"
  local raw_path="raw/$DATASET/$name.md"

  if [[ ! -f "$raw_path" ]]; then
    echo "[$label] MISS $name (no $raw_path)" >&2
    return 10
  fi

  local cmd=(python3 scripts/run_pipeline.py "$raw_path" --function-name "$name" --dataset "$DATASET")
  [[ -n "$CONTRACT_TIMEOUT" ]] && cmd+=(--contract-timeout "$CONTRACT_TIMEOUT")
  [[ -n "$EVAL_TIMEOUT" ]] && cmd+=(--eval-timeout "$EVAL_TIMEOUT")
  [[ -n "$VERIFY_TIMEOUT" ]] && cmd+=(--verify-timeout "$VERIFY_TIMEOUT")
  [[ "$SKIP_EVAL" -eq 1 ]] && cmd+=(--skip-eval)
  [[ "$DRY_RUN" -eq 1 ]] && cmd+=(--dry-run)
  [[ -n "$CONFIG" ]] && cmd+=(--config "$CONFIG")
  if [[ -n "${ARK_PROFILE_SELECTED:-}" ]]; then
    export ARK_PROFILE="$ARK_PROFILE_SELECTED"
    export ARK_PROFILE_CONFIG="$ARK_PROFILE_CONFIG"
    export ARK_MODEL="$model"
    export OPENCODE_PROVIDER="${OPENCODE_PROVIDER:-ark}"
    case "$agent" in
      claude) cmd+=(--claude-bin "$ROOT/scripts/claude_ark_wrapper.sh") ;;
      codex) cmd+=(--codex-bin "$ROOT/scripts/codex_ark_wrapper.sh") ;;
      opencode) cmd+=(--opencode-bin "$ROOT/scripts/opencode_ark_wrapper.sh") ;;
    esac
  fi
  cmd+=(--agent "$agent" --model "$model" --reasoning-effort "$effort")

  echo "[$label] START $name dataset=$DATASET"
  printf '[%s] $' "$label"
  printf ' %q' "${cmd[@]}"
  printf '\n'

  local marker
  marker="$(mktemp "$ROOT/output/.pipeline_marker.XXXXXX")"
  set +e
  "${cmd[@]}"
  local pipeline_rc=$?
  set -e

  local pipeline_dir
  pipeline_dir="$(newest_pipeline_for_name_since "$name" "$marker")"
  rm -f "$marker"
  if [[ -z "$pipeline_dir" || ! -d "$pipeline_dir" ]]; then
    echo "[$label] NO_PIPELINE_WORKSPACE $name rc=$pipeline_rc" >&2
    return 30
  fi

  if archive_pipeline "$pipeline_dir" "$result_dir"; then
    echo "[$label] ARCHIVED $name -> $result_dir"
  else
    echo "[$label] ARCHIVE_FAILED $name pipeline=$pipeline_dir" >&2
    return 31
  fi

  if [[ "$pipeline_rc" -ne 0 ]]; then
    echo "[$label] PIPELINE_FAILED $name rc=$pipeline_rc (artifacts archived)" >&2
    return "$pipeline_rc"
  fi
  echo "[$label] DONE $name"
}

status_label() {
  case "$1" in
    0) echo "success" ;;
    1) echo "pipeline_failed" ;;
    2) echo "usage" ;;
    10) echo "missing_raw" ;;
    30) echo "missing_pipeline_workspace" ;;
    31) echo "archive_failed" ;;
    *) echo "unknown_$1" ;;
  esac
}

latest_pipeline_for_problem() {
  local result_dir="$1"
  local name="$2"
  find "$result_dir" -maxdepth 1 -type d -name "pipeline_*_${name}" -printf '%T@ %p\n' 2>/dev/null \
    | sort -nr \
    | awk 'NR == 1 { $1=""; sub(/^ /, ""); print }'
}

pipeline_status() {
  local pipeline_dir="$1"
  if [[ -n "$pipeline_dir" && -f "$pipeline_dir/pipeline_summary.json" ]]; then
    python3 - "$pipeline_dir/pipeline_summary.json" <<'PY'
import json, sys
try:
    print(json.load(open(sys.argv[1], encoding="utf-8")).get("status", "unknown"))
except Exception:
    print("unknown")
PY
  else
    printf '%s\n' "unknown"
  fi
}

delete_pipeline_result() {
  local result_dir="$1"
  local pipeline_dir="$2"
  [[ -n "$pipeline_dir" && "$pipeline_dir" == "$result_dir"/pipeline_* ]] || {
    echo "refusing to delete unexpected pipeline path: $pipeline_dir" >&2
    return 1
  }
  python3 - "$pipeline_dir" "$result_dir" <<'PY'
from pathlib import Path
import json
import shutil
import sys

pipeline_dir = Path(sys.argv[1]).resolve()
result_dir = Path(sys.argv[2]).resolve()
to_delete = [pipeline_dir]
summary = pipeline_dir / "pipeline_summary.json"
if summary.exists():
    try:
        data = json.loads(summary.read_text(encoding="utf-8"))
    except Exception:
        data = {}
    for raw in data.get("workspaces", []):
        path = Path(raw).resolve()
        try:
            path.relative_to(result_dir)
        except ValueError:
            continue
        if path.name.startswith(("contract_", "eval_", "verify_")):
            to_delete.append(path)
for path in to_delete:
    if path.exists():
        shutil.rmtree(path)
        print(f"deleted {path}")
PY
}

single_job_config() {
  local config="$1"
  local label agent model effort result_dir jobs
  IFS='|' read -r label agent model effort result_dir jobs <<< "$config"
  printf '%s|%s|%s|%s|%s|1\n' "$label" "$agent" "$model" "$effort" "$result_dir"
}

run_one_problem_safe() {
  local config="$1"
  local label="$2"
  local result_dir="$3"
  local name="$4"
  local attempt="$5"
  local start end elapsed rc pipeline_dir status

  start="$(date +%s)"
  echo "[$(date '+%F %T %z')] START pipeline config=$label problem=$name attempt=$attempt"
  set +e
  run_one "$label" "$6" "$7" "$8" "$result_dir" "$name"
  rc=$?
  set -e
  end="$(date +%s)"
  elapsed=$((end - start))

  pipeline_dir="$(latest_pipeline_for_problem "$result_dir" "$name" || true)"
  status="$(pipeline_status "$pipeline_dir")"
  echo "[$(date '+%F %T %z')] DONE pipeline config=$label problem=$name attempt=$attempt rc=$rc status=$status elapsed=${elapsed}s"

  if [[ "$rc" -ne 0 && "$elapsed" -le "$FAST_FAIL_SECONDS" ]]; then
    [[ -n "$pipeline_dir" ]] && delete_pipeline_result "$result_dir" "$pipeline_dir"
    return 75
  fi
  return 0
}

run_batch_safe() {
  local config="$1"
  shift
  local label agent model effort result_dir jobs problem fast_retries rc started_count=0 existing_file
  IFS='|' read -r label agent model effort result_dir jobs <<< "$config"
  config="$(single_job_config "$config")"
  mkdir -p "$result_dir"

  existing_file="$(mktemp)"
  existing_success_names "$result_dir" > "$existing_file"
  for problem in "$@"; do
    if [[ "$started_count" -ge "$MAX_PROBLEMS" ]]; then
      echo "[$(date '+%F %T %z')] STOP pipeline config=$label reason=max_problems count=$started_count"
      rm -f "$existing_file"
      return 0
    fi
    if [[ -f "$ROOT/output/stop_pipeline_${label}.flag" || -f "$ROOT/output/stop_all_batch_safe.flag" ]]; then
      echo "[$(date '+%F %T %z')] STOP pipeline config=$label reason=stop_flag"
      rm -f "$existing_file"
      return 0
    fi
    if [[ "$FORCE" -eq 0 ]] && grep -qxF "$problem" "$existing_file"; then
      echo "[$(date '+%F %T %z')] SKIP pipeline config=$label problem=$problem reason=existing_success"
      continue
    fi
    fast_retries=0
    while true; do
      started_count=$((started_count + 1))
      set +e
      run_one_problem_safe "$config" "$label" "$result_dir" "$problem" "$((fast_retries + 1))" "$agent" "$model" "$effort"
      rc=$?
      set -e
      if [[ "$rc" -eq 0 ]]; then
        break
      fi
      if [[ "$rc" -ne 75 ]]; then
        rm -f "$existing_file"
        echo "[$(date '+%F %T %z')] STOP pipeline config=$label problem=$problem rc=$rc"
        return "$rc"
      fi
      if [[ "$fast_retries" -ge "$MAX_FAST_RETRIES" ]]; then
        rm -f "$existing_file"
        echo "[$(date '+%F %T %z')] STOP pipeline config=$label problem=$problem reason=second_fast_failure"
        return 75
      fi
      fast_retries=$((fast_retries + 1))
      started_count=$((started_count - 1))
      echo "[$(date '+%F %T %z')] FAST_FAIL pipeline config=$label problem=$problem; sleeping ${QUOTA_SLEEP_SECONDS}s before retry"
      sleep "$QUOTA_SLEEP_SECONDS"
    done
  done
  rm -f "$existing_file"

  echo "[$(date '+%F %T %z')] COMPLETE pipeline config=$label started=$started_count problems=$#"
}

start_config() {
  local config="$1"
  shift
  local label agent model effort result_dir jobs
  IFS='|' read -r label agent model effort result_dir jobs <<< "$config"
  local -a requested_names=("$@")
  local -a names=()
  local existing_file

  mkdir -p "$result_dir"
  if [[ ${#requested_names[@]} -eq 0 ]]; then
    mapfile -t requested_names < <(raw_names)
  fi

  existing_file="$(mktemp)"
  existing_success_names "$result_dir" > "$existing_file"
  mapfile -t names < <(filter_existing_success "$existing_file" "${requested_names[@]}")
  rm -f "$existing_file"

  if [[ ${#names[@]} -eq 0 ]]; then
    echo "[$label] nothing to run; all requested problems already have successful pipeline results in $result_dir"
    return 0
  fi

  local run_id run_dir
  run_id="$(date +%Y%m%d_%H%M%S)"
  run_dir="$ROOT/output/pipeline_batch_${run_id}_${label}"
  mkdir -p "$run_dir"
  echo "[$label] starting ${#names[@]} problems dataset=$DATASET agent=$agent model=$model effort=$effort jobs=$jobs -> $result_dir"

  local -a successes=()
  local -a failures=()

  if [[ "$jobs" -eq 1 ]]; then
    local name log rc label_status
    for name in "${names[@]}"; do
      log="$run_dir/$name.log"
      if run_one "$label" "$agent" "$model" "$effort" "$result_dir" "$name" 2>&1 | tee "$log"; then
        successes+=("$name")
      else
        rc=${PIPESTATUS[0]}
        label_status="$(status_label "$rc")"
        failures+=("$name:$label_status")
      fi
    done
  else
    local name log status_file status label_status
    echo "[$label] logs=$run_dir"
    for name in "${names[@]}"; do
      while [[ "$(jobs -rp | wc -l)" -ge "$jobs" ]]; do
        sleep 1
      done
      log="$run_dir/$name.log"
      status_file="$run_dir/$name.status"
      (
        set +e
        run_one "$label" "$agent" "$model" "$effort" "$result_dir" "$name" >"$log" 2>&1
        rc=$?
        printf '%s:%s\n' "$name" "$(status_label "$rc")" > "$status_file"
        exit 0
      ) &
      echo "[$label] launched name=$name pid=$! log=$log"
    done
    wait

    for name in "${names[@]}"; do
      status_file="$run_dir/$name.status"
      if [[ ! -f "$status_file" ]]; then
        failures+=("$name:missing_status")
        continue
      fi
      status="$(<"$status_file")"
      label_status="${status#*:}"
      if [[ "$label_status" == "success" ]]; then
        successes+=("$name")
      else
        failures+=("$name:$label_status")
      fi
    done
  fi

  {
    echo "# Pipeline Batch Summary"
    echo
    echo "- Label: \`$label\`"
    echo "- Dataset: \`$DATASET\`"
    echo "- Agent: \`$agent\`"
    echo "- Model: \`$model\`"
    echo "- Reasoning effort: \`$effort\`"
    echo "- Total requested after skip: \`${#names[@]}\`"
    echo "- Success: \`${#successes[@]}\`"
    echo "- Failure: \`${#failures[@]}\`"
    echo
    echo "## Successes"
    for name in "${successes[@]}"; do
      echo "- $name"
    done
    echo
    echo "## Failures"
    for failure in "${failures[@]}"; do
      echo "- $failure"
    done
  } > "$run_dir/summary.md"

  local archived_run_dir="$result_dir/$(basename "$run_dir")"
  if [[ -e "$archived_run_dir" ]]; then
    echo "[$label] batch log target already exists: $archived_run_dir" >&2
  else
    mv "$run_dir" "$archived_run_dir"
    echo "[$label] batch logs archived -> $archived_run_dir"
  fi

  echo "[$label] summary: total=${#names[@]} success=${#successes[@]} failure=${#failures[@]}"
  if [[ ${#failures[@]} -gt 0 ]]; then
    echo "[$label] failures:" >&2
    for failure in "${failures[@]}"; do
      echo "  $failure" >&2
    done
    return 1
  fi
}

configs_to_run=()
if [[ "$REQUESTED" == "all" ]]; then
  configs_to_run=("${RUN_CONFIGS[@]}")
else
  if ! config="$(config_for "$REQUESTED")"; then
    echo "unknown config: $REQUESTED" >&2
    usage >&2
    exit 2
  fi
  configs_to_run=("$config")
fi

if [[ ${#NAMES[@]} -eq 0 ]]; then
  mapfile -t NAMES < <(raw_names)
fi

overall_rc=0
for config in "${configs_to_run[@]}"; do
  if ! run_batch_safe "$config" "${NAMES[@]}"; then
    overall_rc=1
  fi
done

exit "$overall_rc"
