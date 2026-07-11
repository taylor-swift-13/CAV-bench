#!/usr/bin/env bash
# Run proof-only jobs one problem at a time, copy completed workspaces to
# proof_results, and stop/retry conservatively on likely quota exhaustion.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

RESULTS_ROOT="${RESULTS_ROOT:-$ROOT/proof_results}"
ANNOTATED_ROOT="${ANNOTATED_ROOT:-$ROOT/annotated_input}"
DATASET="${DATASET:-humaneval}"
TIMEOUT="${TIMEOUT:-5400}"
JOBS="${JOBS:-1}"
CODEX_JOBS="${CODEX_JOBS:-$JOBS}"
CLAUDE_JOBS="${CLAUDE_JOBS:-$JOBS}"
KIMI_JOBS="${KIMI_JOBS:-$JOBS}"
OPENCODE_JOBS="${OPENCODE_JOBS:-$JOBS}"
FOREGROUND="${FOREGROUND:-1}"
FORCE=0
MODEL_OVERRIDE="${MODEL_OVERRIDE:-${ARK_MODEL:-${MODEL:-}}}"
ARK_PROFILE_CONFIG="${ARK_PROFILE_CONFIG:-$ROOT/config/ark_api/profiles.json}"
ARK_PROFILE_SELECTED="${ARK_PROFILE:-}"
FAST_FAIL_SECONDS="${FAST_FAIL_SECONDS:-120}"
QUOTA_SLEEP_SECONDS="${QUOTA_SLEEP_SECONDS:-18000}"
MAX_FAST_RETRIES="${MAX_FAST_RETRIES:-1}"
MAX_PROBLEMS="${MAX_PROBLEMS:-10}"

usage() {
  cat <<'EOF'
usage: scripts/batch_safe_proof.sh [options] <config> [problem_name ...]

Runs proof-only for one agent/model configuration. For each problem:
  annotated_input/<dataset>/<name>.c       is the annotated C input
  annotated_input/<dataset>/<name>.v       is optional paired Coq spec/dependency

The agent receives a run-proof prompt: run symexec from the annotated C, then
prove proof_manual.v. This is intentionally separate from run_verify.

Results are saved under:
  proof_results/<agent>/<model>/<effort>/

Fast failing runs retry up to MAX_FAST_RETRIES after QUOTA_SLEEP_SECONDS. Each
invocation starts at most MAX_PROBLEMS new problems.

Supported configs:
  codex-54-high
  codex-54-medium
  codex-54-low
  codex-54-mini-medium
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
  opencode-ark-5-deepseek
  opencode-ark-5-glm
  claude-haiku-medium
  claude-opus-medium
  claude-sonnet-high
  claude-sonnet-low
  claude-sonnet-medium
  kimi-thinking

Aliases:
  high    -> codex-54-high
  medium  -> codex-54-medium
  low     -> codex-54-low
  mini    -> codex-54-mini-medium
  kimi    -> kimi-thinking

Options:
  --dataset NAME          Read input/<dataset> and annotated_input/<dataset>.
                          Default: humaneval.
  --annotated-root DIR    Root containing annotated inputs. Default: ./annotated_input.
  --jobs N, -j N          Accepted for compatibility; batch-safe runs use jobs=1.
  --timeout N             Per-problem total timeout in seconds. Default: 5400.
  --results-root DIR      Archive root. Default: ./proof_results.
  --background            Start the batch in background.
  --foreground            Run in foreground. Default.
  --force                 Run even if a matching result already exists.
  -h, --help              Show this help.

Examples:
  scripts/batch_safe_proof.sh low p003_below_zero
  scripts/batch_safe_proof.sh codex-54-medium
EOF
}

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

build_run_configs() {
  local ark_model="${MODEL_OVERRIDE:-}"
  local ark_label="${ARK_PROFILE_SELECTED:-ark-profile}"
  if [[ -n "$ARK_PROFILE_SELECTED" && -z "$ark_model" ]]; then
    ark_model="$(python3 "$ROOT/scripts/ark_profile_env.py" --config "$ARK_PROFILE_CONFIG" --field model "$ARK_PROFILE_SELECTED")"
  fi
  RUN_CONFIGS=(
    "claude-haiku-medium|claude|haiku|medium|$(result_dir_for "$RESULTS_ROOT" claude haiku medium)|output/proof_only_batch_claude_haiku_medium.out|$CLAUDE_JOBS|"
    "claude-opus-medium|claude|opus|medium|$(result_dir_for "$RESULTS_ROOT" claude opus medium)|output/proof_only_batch_claude_opus_medium.out|$CLAUDE_JOBS|"
    "claude-sonnet-high|claude|sonnet|high|$(result_dir_for "$RESULTS_ROOT" claude sonnet high)|output/proof_only_batch_claude_sonnet_high.out|$CLAUDE_JOBS|"
    "claude-sonnet-low|claude|sonnet|low|$(result_dir_for "$RESULTS_ROOT" claude sonnet low)|output/proof_only_batch_claude_sonnet_low.out|$CLAUDE_JOBS|"
    "claude-sonnet-medium|claude|sonnet|medium|$(result_dir_for "$RESULTS_ROOT" claude sonnet medium)|output/proof_only_batch_claude_sonnet_medium.out|$CLAUDE_JOBS|"
    "codex-54-mini-medium|codex|gpt-5.4-mini|medium|$(result_dir_for "$RESULTS_ROOT" codex gpt-5.4-mini medium)|output/proof_only_batch_codex_54_mini_medium.out|$CODEX_JOBS|"
    "codex-54-high|codex|gpt-5.4|high|$(result_dir_for "$RESULTS_ROOT" codex gpt-5.4 high)|output/proof_only_batch_codex_54_high.out|$CODEX_JOBS|"
    "codex-54-low|codex|gpt-5.4|low|$(result_dir_for "$RESULTS_ROOT" codex gpt-5.4 low)|output/proof_only_batch_codex_54_low.out|$CODEX_JOBS|"
    "codex-54-medium|codex|gpt-5.4|medium|$(result_dir_for "$RESULTS_ROOT" codex gpt-5.4 medium)|output/proof_only_batch_codex_54_medium.out|$CODEX_JOBS|"
    "codex-55-medium|codex|gpt-5.5|medium|$(result_dir_for "$RESULTS_ROOT" codex gpt-5.5 medium)|output/proof_only_batch_codex_55_medium.out|$CODEX_JOBS|"
    "codex-55-xhigh|codex|gpt-5.5|xhigh|$(result_dir_for "$RESULTS_ROOT" codex gpt-5.5 xhigh)|output/proof_only_batch_codex_55_xhigh.out|$CODEX_JOBS|"
    "codex-$ark_label|codex|$ark_model|api|$(result_dir_for "$RESULTS_ROOT" codex "$ark_model" api)|output/proof_only_batch_codex_${ark_label}.out|$CODEX_JOBS|"
    "opencode-$ark_label|opencode|$ark_model|api|$(result_dir_for "$RESULTS_ROOT" opencode "$ark_model" api)|output/proof_only_batch_opencode_${ark_label}.out|$OPENCODE_JOBS|"
    "kimi-thinking|kimicode|kimi-code/kimi-for-coding|thinking|$(result_dir_for "$RESULTS_ROOT" kimicode kimi-code/kimi-for-coding thinking)|output/proof_only_batch_kimi_thinking.out|$KIMI_JOBS|"
  )
}

canonical_config() {
  case "$1" in
    codex-ark-*|opencode-ark-*)
      printf '%s\n' "$1"
      return
      ;;
  esac
  case "$1" in
    codex-ark|codex-ark-api) printf '%s\n' "codex-ark-2-deepseek" ;;
    opencode-ark|opencode-ark-api) printf '%s\n' "opencode-ark-2-deepseek" ;;
    high) printf '%s\n' "codex-54-high" ;;
    medium|codex) printf '%s\n' "codex-54-medium" ;;
    low) printf '%s\n' "codex-54-low" ;;
    mini|codex-mini) printf '%s\n' "codex-54-mini-medium" ;;
    kimi|kimicode) printf '%s\n' "kimi-thinking" ;;
    *) printf '%s\n' "$1" ;;
  esac
}

config_for() {
  local label="$1"
  local config
  for config in "${RUN_CONFIGS[@]}"; do
    if [[ "${config%%|*}" == "$label" ]]; then
      printf '%s\n' "$config"
      return 0
    fi
  done
  return 1
}

metric_value() {
  local metrics="$1"
  local key="$2"
  sed -n "s/^- ${key}: \`\([^\`]*\)\`$/\1/p" "$metrics" | tail -n 1
}

workspace_problem_name() {
  basename "$1" | sed -E 's/^(verify|proof)_[0-9]{8}_[0-9]{6}[0-9]*_//'
}

cleanup_workspace_after_result_copy() {
  local workspace="$1"
  local base
  base="$(basename "$workspace")"
  if [[ -z "$base" || ( "$base" != verify_* && "$base" != proof_* ) ]]; then
    echo "refusing to clean unexpected workspace path: $workspace" >&2
    return 1
  fi
  rm -rf \
    "$ROOT/QualifiedCProgramming/QCP_examples/CAV/$base" \
    "$ROOT/QualifiedCProgramming/.tmp/QCP_examples/CAV/$base" \
    "$ROOT/QualifiedCProgramming/SeparationLogic/examples/CAV/$base" \
    "$ROOT/QualifiedCProgramming/.tmp/SeparationLogic/examples/CAV/$base" \
    "$ROOT/QualifiedCProgramming/SeparationLogic/_cav_locks/$base" \
    "$ROOT/annotated/$base.c" \
    "$workspace"
}

copy_workspace_to_result_dir() {
  local workspace="$1"
  local result_dir="$2"
  local label="$3"
  local name="$4"
  local dest
  dest="$result_dir/$(basename "$workspace")"
  if [[ -e "$dest" ]]; then
    echo "[$label] SKIP_COPY $name -> $dest (exists)"
    cleanup_workspace_after_result_copy "$workspace"
    return 0
  fi
  mkdir -p "$result_dir"
  if cp -a "$workspace" "$result_dir"/; then
    echo "[$label] COPIED $name -> $dest"
    cleanup_workspace_after_result_copy "$workspace"
    return 0
  fi
  echo "[$label] COPY_FAILED $name -> $dest"
  return 1
}

existing_names() {
  local result_dir="$1"
  local agent="$2"
  local model="$3"
  local effort="$4"
  local workspace metrics got_agent got_model got_effort
  shopt -s nullglob
  for workspace in "$result_dir"/proof_* "$result_dir"/verify_*; do
    metrics="$workspace/logs/metrics.md"
    [[ -f "$metrics" ]] || continue
    got_agent="$(metric_value "$metrics" "Agent")"
    got_model="$(metric_value "$metrics" "Model")"
    got_effort="$(metric_value "$metrics" "Reasoning effort")"
    if [[ "$got_model" == "$model" && "$got_effort" == "$effort" ]] &&
       [[ "$got_agent" == "$agent" || "$got_agent" == "proof-only-initial-symexec" ]]; then
      workspace_problem_name "$workspace"
    fi
  done | sort -u
  shopt -u nullglob
}

filter_existing() {
  local existing_file="$1"
  shift
  local name
  for name in "$@"; do
    if [[ "$FORCE" -eq 1 ]] || ! grep -qxF "$name" "$existing_file"; then
      printf '%s\n' "$name"
    fi
  done
}

annotated_names() {
  local annotated_dir="$ANNOTATED_ROOT/$DATASET"
  [[ -d "$annotated_dir" ]] || { echo "missing annotated input directory: $annotated_dir" >&2; return 2; }
  find "$annotated_dir" -maxdepth 1 -type f -name '*.c' -printf '%f\n' \
    | sed 's/\.c$//' \
    | sort
}

validate_positive_int() {
  local name="$1"
  local value="$2"
  if ! [[ "$value" =~ ^[0-9]+$ ]] || [[ "$value" -lt 1 ]]; then
    echo "$name must be a positive integer: $value" >&2
    exit 2
  fi
}

start_batch() {
  local config="$1"
  shift
  local label agent model effort result_dir log_file jobs agent_config
  IFS='|' read -r label agent model effort result_dir log_file jobs agent_config <<< "$config"
  if [[ -n "${BATCH_LOG_SUFFIX:-}" ]]; then
    log_file="${log_file%.out}_${BATCH_LOG_SUFFIX}.out"
  fi
  local -a all_names=("$@")
  local -a names=()
  local existing_file

  mkdir -p "$result_dir"
  existing_file="$(mktemp)"
  existing_names "$result_dir" "$agent" "$model" "$effort" > "$existing_file"
  mapfile -t names < <(filter_existing "$existing_file" "${all_names[@]}" | awk '!seen[$0]++')
  rm -f "$existing_file"

  if [[ ${#names[@]} -eq 0 ]]; then
    echo "[$label] nothing to run; requested proof-only results already exist in $result_dir"
    return 0
  fi

  echo "[$label] starting ${#names[@]} proof-only problems agent=$agent model=$model effort=$effort jobs=$jobs -> $result_dir"

  run_batch_jobs() {
    set -o pipefail
    set +e
    mkdir -p output
    lock_dir="output/.proof_only_${LOCK_LABEL:-$label}.lock"
    if ! mkdir "$lock_dir" 2>/dev/null; then
      lock_pid="$(cat "$lock_dir/pid" 2>/dev/null || true)"
      if [[ -n "$lock_pid" ]] && kill -0 "$lock_pid" 2>/dev/null; then
        echo "[$label] lock exists at $lock_dir; pid=$lock_pid is still running"
        return 1
      fi
      echo "[$label] removing stale lock at $lock_dir"
      rm -rf "$lock_dir"
      if ! mkdir "$lock_dir" 2>/dev/null; then
        echo "[$label] could not acquire lock at $lock_dir"
        return 1
      fi
    fi
    printf '%s\n' "$$" > "$lock_dir/pid"
    trap 'rm -rf "$lock_dir"' RETURN
    problem_lock_root="$lock_dir/problems"
    mkdir -p "$problem_lock_root"

    export ROOT DATASET TIMEOUT ANNOTATED_ROOT ARK_PROFILE_SELECTED ARK_PROFILE_CONFIG
    export agent model effort result_dir label problem_lock_root agent_config
    export -f cleanup_workspace_after_result_copy
    export -f copy_workspace_to_result_dir

    local batch_rc
    printf '%s\n' "${names[@]}" | xargs -P "$jobs" -I{} bash -c '
      set +e
      name="$1"
      problem_lock="$problem_lock_root/$name.lock"
      if ! mkdir "$problem_lock" 2>/dev/null; then
        lock_pid="$(cat "$problem_lock/pid" 2>/dev/null || true)"
        if [[ -n "$lock_pid" ]] && kill -0 "$lock_pid" 2>/dev/null; then
          echo "[$label] SKIP_RUNNING $name pid=$lock_pid"
          exit 0
        fi
        rm -rf "$problem_lock"
        if ! mkdir "$problem_lock" 2>/dev/null; then
          echo "[$label] SKIP_LOCKED $name"
          exit 0
        fi
      fi
      printf "%s\n" "$$" > "$problem_lock/pid"
      trap "rm -rf \"$problem_lock\"" EXIT

      c="$ANNOTATED_ROOT/$DATASET/$name.c"
      annotated_c="$c"
      if [[ ! -f "$c" ]]; then
        problem_log="output/missing_proof_only_${label}_${name}.log"
        echo "[$label] MISS $name (no $c)" | tee -a "$problem_log"
        exit 10
      fi

      ts="$(date +%Y%m%d_%H%M%S)$RANDOM"
      workspace="output/proof_${ts}_${name}"
      mkdir -p "$workspace/logs"
      problem_log="$workspace/logs/batch.log"
      echo "[$label] START_PROOF_ONLY $name ts=$ts annotated=$annotated_c" | tee "$problem_log"

      if [[ -n "${agent_config:-}" ]]; then
        export CAV_AGENT_CONFIG="$agent_config"
      fi
      extra_agent_args=()
      if [[ -n "${ARK_PROFILE_SELECTED:-}" ]]; then
        export ARK_PROFILE="$ARK_PROFILE_SELECTED"
        export ARK_PROFILE_CONFIG="$ARK_PROFILE_CONFIG"
        export ARK_MODEL="$model"
        export OPENCODE_PROVIDER="${OPENCODE_PROVIDER:-ark}"
        case "$agent" in
          claude) extra_agent_args+=(--claude-bin "$ROOT/scripts/claude_ark_wrapper.sh") ;;
          codex) extra_agent_args+=(--codex-bin "$ROOT/scripts/codex_ark_wrapper.sh") ;;
          opencode) extra_agent_args+=(--opencode-bin "$ROOT/scripts/opencode_ark_wrapper.sh") ;;
        esac
      fi
      python3 scripts/run_proof.py "$c" \
        --function-name "$name" --workspace-name "$name" \
        --timestamp "$ts" \
        --agent "$agent" --model "$model" --reasoning-effort "$effort" \
        --timeout-seconds "$TIMEOUT" \
        --annotated-input-c "$annotated_c" \
        "${extra_agent_args[@]}" \
        >> "$problem_log" 2>&1
      rc=$?

      if [[ -z "$workspace" || ! -d "$workspace" ]]; then
        workspace="$(ls -dt output/proof_*_"$name" 2>/dev/null | head -n 1)"
      fi
      if [[ -n "$workspace" && -d "$workspace" ]]; then
        echo "[$label] RUN_DONE $name rc=$rc workspace=$workspace" | tee -a "$problem_log"
        if ! copy_workspace_to_result_dir "$workspace" "$result_dir" "$label" "$name"; then
          rc=1
        fi
        echo "[$label] DONE $name rc=$rc workspace=$workspace"
      else
        echo "[$label] NO_WORKSPACE $name rc=$rc" | tee -a "$problem_log"
        rc=1
      fi
      exit "$rc"
    ' _ {}
    batch_rc=$?
    trap - RETURN
    rm -rf "$lock_dir"
    return "$batch_rc"
  }

  finalize_batch_log() {
    local batch_rc="$1"
    local final_log="$result_dir/$(basename "$log_file")"
    mkdir -p "$result_dir"
    if [[ -f "$log_file" ]]; then
      cp -a "$log_file" "$final_log"
      rm -f "$log_file"
    fi
    return "$batch_rc"
  }

  if [[ "$FOREGROUND" == "1" ]]; then
    mkdir -p "$(dirname "$log_file")"
    run_batch_jobs > "$log_file" 2>&1
    local batch_rc=$?
    finalize_batch_log "$batch_rc"
    echo "[$label] completed rc=$batch_rc log=$result_dir/$(basename "$log_file")"
    return "$batch_rc"
  fi

  mkdir -p "$(dirname "$log_file")"
  (
    trap "" HUP
    run_batch_jobs > "$log_file" 2>&1
    batch_rc=$?
    finalize_batch_log "$batch_rc"
    exit "$batch_rc"
  ) &
  disown "$!" 2>/dev/null || true
  echo "[$label] pid=$! log=$log_file final_log=$result_dir/$(basename "$log_file")"
}

latest_metrics_for_problem() {
  local result_dir="$1"
  local name="$2"
  local latest
  latest="$(find "$result_dir" -maxdepth 1 -type d \( -name "proof_*_${name}" -o -name "verify_*_${name}" \) -printf '%T@ %p\n' 2>/dev/null \
    | sort -nr \
    | awk 'NR == 1 { $1=""; sub(/^ /, ""); print }')"
  [[ -n "$latest" && -f "$latest/logs/metrics.md" ]] || return 1
  printf '%s\n' "$latest/logs/metrics.md"
}

delete_result_for_metrics() {
  local metrics="$1"
  local result_dir="$2"
  local workspace
  workspace="$(cd "$(dirname "$metrics")/.." && pwd)"
  case "$workspace" in
    "$result_dir"/proof_*|"$result_dir"/verify_*)
      echo "[$(date '+%F %T %z')] DELETE_FAST_FAIL_WORKSPACE $workspace"
      rm -rf "$workspace"
      ;;
    *)
      echo "refusing to delete unexpected proof path: $workspace" >&2
      return 1
      ;;
  esac
}

single_job_config() {
  local config="$1"
  local label agent model effort result_dir log_file jobs agent_config
  IFS='|' read -r label agent model effort result_dir log_file jobs agent_config <<< "$config"
  printf '%s|%s|%s|%s|%s|%s|1|%s\n' "$label" "$agent" "$model" "$effort" "$result_dir" "$log_file" "$agent_config"
}

run_one_problem_safe() {
  local config="$1"
  local result_dir="$2"
  local label="$3"
  local name="$4"
  local attempt="$5"
  local start end elapsed rc metrics status wall safe_label

  start="$(date +%s)"
  safe_label="${label//[^A-Za-z0-9_]/_}"
  echo "[$(date '+%F %T %z')] START proof config=$label problem=$name attempt=$attempt"
  set +e
  BATCH_LOG_SUFFIX="batch_safe_proof_${safe_label}_${name}_$(date +%Y%m%d_%H%M%S)" \
    start_batch "$config" "$name"
  rc=$?
  set -e
  end="$(date +%s)"
  elapsed=$((end - start))

  status="unknown"
  wall="$elapsed"
  metrics=""
  if metrics="$(latest_metrics_for_problem "$result_dir" "$name")"; then
    status="$(metric_value "$metrics" "Status")"
    wall="$(metric_value "$metrics" "Wall-clock time (seconds)")"
  fi
  echo "[$(date '+%F %T %z')] DONE proof config=$label problem=$name attempt=$attempt rc=$rc status=$status elapsed=${elapsed}s wall=${wall}s"

  if [[ "$status" == "Fail" && "$elapsed" -le "$FAST_FAIL_SECONDS" ]]; then
    [[ -n "$metrics" ]] && delete_result_for_metrics "$metrics" "$result_dir"
    return 75
  fi
  if [[ "$rc" -ne 0 && "$elapsed" -le "$FAST_FAIL_SECONDS" ]]; then
    [[ -n "$metrics" ]] && delete_result_for_metrics "$metrics" "$result_dir"
    return 75
  fi
  return 0
}

run_batch_safe() {
  local config="$1"
  shift
  local label agent model effort result_dir log_file jobs agent_config problem fast_retries rc started_count=0
  IFS='|' read -r label agent model effort result_dir log_file jobs agent_config <<< "$config"
  config="$(single_job_config "$config")"
  mkdir -p "$result_dir"

  for problem in "$@"; do
    if [[ "$started_count" -ge "$MAX_PROBLEMS" ]]; then
      echo "[$(date '+%F %T %z')] STOP proof config=$label reason=max_problems count=$started_count"
      return 0
    fi
    if [[ -f "$ROOT/output/stop_proof_${label}.flag" || -f "$ROOT/output/stop_all_batch_safe.flag" ]]; then
      echo "[$(date '+%F %T %z')] STOP proof config=$label reason=stop_flag"
      return 0
    fi
    if [[ "$FORCE" -eq 0 ]] && latest_metrics_for_problem "$result_dir" "$problem" >/dev/null; then
      echo "[$(date '+%F %T %z')] SKIP proof config=$label problem=$problem reason=existing_result"
      continue
    fi
    if [[ ! -f "$ANNOTATED_ROOT/$DATASET/$problem.c" ]]; then
      echo "[$(date '+%F %T %z')] SKIP proof config=$label problem=$problem reason=missing_annotated_c"
      continue
    fi

    fast_retries=0
    while true; do
      started_count=$((started_count + 1))
      set +e
      run_one_problem_safe "$config" "$result_dir" "$label" "$problem" "$((fast_retries + 1))"
      rc=$?
      set -e
      if [[ "$rc" -eq 0 ]]; then
        break
      fi
      if [[ "$rc" -ne 75 ]]; then
        echo "[$(date '+%F %T %z')] STOP proof config=$label problem=$problem rc=$rc"
        return "$rc"
      fi
      if [[ "$fast_retries" -ge "$MAX_FAST_RETRIES" ]]; then
        echo "[$(date '+%F %T %z')] STOP proof config=$label problem=$problem reason=second_fast_failure"
        return 75
      fi
      fast_retries=$((fast_retries + 1))
      started_count=$((started_count - 1))
      echo "[$(date '+%F %T %z')] FAST_FAIL proof config=$label problem=$problem; sleeping ${QUOTA_SLEEP_SECONDS}s before retry"
      sleep "$QUOTA_SLEEP_SECONDS"
    done
  done

  echo "[$(date '+%F %T %z')] COMPLETE proof config=$label started=$started_count problems=$#"
}

POSITIONAL=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --dataset)
      [[ $# -ge 2 ]] || { echo "missing value for --dataset" >&2; exit 2; }
      DATASET="$2"
      shift 2
      ;;
    --annotated-root)
      [[ $# -ge 2 ]] || { echo "missing value for --annotated-root" >&2; exit 2; }
      ANNOTATED_ROOT="$2"
      shift 2
      ;;
    --jobs|-j)
      [[ $# -ge 2 ]] || { echo "missing value for $1" >&2; exit 2; }
      JOBS="$2"
      CODEX_JOBS="$2"
      CLAUDE_JOBS="$2"
      KIMI_JOBS="$2"
      OPENCODE_JOBS="$2"
      shift 2
      ;;
    --timeout)
      [[ $# -ge 2 ]] || { echo "missing value for --timeout" >&2; exit 2; }
      TIMEOUT="$2"
      shift 2
      ;;
    --results-root)
      [[ $# -ge 2 ]] || { echo "missing value for --results-root" >&2; exit 2; }
      RESULTS_ROOT="$2"
      shift 2
      ;;
    --background)
      FOREGROUND=0
      shift
      ;;
    --foreground)
      FOREGROUND=1
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

validate_positive_int "JOBS" "$JOBS"
validate_positive_int "TIMEOUT" "$TIMEOUT"

if [[ ${#POSITIONAL[@]} -lt 1 ]]; then
  usage >&2
  exit 2
fi

requested="$(canonical_config "${POSITIONAL[0]}")"
REQUESTED_NAMES=("${POSITIONAL[@]:1}")

ark_requested="$requested"
case "$requested" in
  codex-ark-*|opencode-ark-*)
    ark_requested="${ark_requested#codex-}"
    ark_requested="${ark_requested#opencode-}"
    ;;
esac

if python3 "$ROOT/scripts/ark_profile_env.py" --config "$ARK_PROFILE_CONFIG" --field model "$ark_requested" >/dev/null 2>&1; then
  ARK_PROFILE_SELECTED="$ark_requested"
fi

case "$requested" in
  all)
    echo "this script runs exactly one config; pass a single config such as codex-54-low" >&2
    exit 2
    ;;
esac

build_run_configs
config="$(config_for "$requested" || true)"
if [[ -z "$config" ]]; then
  echo "unknown config: ${POSITIONAL[0]}" >&2
  usage >&2
  exit 2
fi

if [[ ${#REQUESTED_NAMES[@]} -gt 0 ]]; then
  names=("${REQUESTED_NAMES[@]}")
else
  mapfile -t names < <(annotated_names)
fi

run_batch_safe "$config" "${names[@]}"
