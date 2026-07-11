#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ARK_PROFILE_CONFIG="${ARK_PROFILE_CONFIG:-$ROOT/config/ark_api/profiles.json}"
OPENCODE_PROVIDER="${OPENCODE_PROVIDER:-ark}"

if [[ -n "${ARK_PROFILE:-}" ]]; then
  eval "$("$ROOT/scripts/ark_profile_env.py" --config "$ARK_PROFILE_CONFIG" "$ARK_PROFILE")"
fi

if [[ -z "${ARK_API_KEY:-}" || -z "${ARK_BASE_URL:-}" || -z "${ARK_MODEL:-}" ]]; then
  echo "opencode_ark_wrapper requires ARK_PROFILE or ARK_API_KEY, ARK_BASE_URL, and ARK_MODEL" >&2
  exit 2
fi

opencode_base_url="$ARK_BASE_URL"
case "$opencode_base_url" in
  */v3) ;;
  */) opencode_base_url="${opencode_base_url}v3" ;;
  *) opencode_base_url="${opencode_base_url}/v3" ;;
esac

config_home="${XDG_CONFIG_HOME:-$HOME/.config}"
data_home="${XDG_DATA_HOME:-$HOME/.local/share}"
config_dir="$config_home/opencode"
data_dir="$data_home/opencode"
auth_file="$data_dir/auth.json"
config_file="$config_dir/opencode.json"

mkdir -p "$config_dir" "$data_dir"
umask 077

python3 - "$config_file" "$auth_file" "$OPENCODE_PROVIDER" "$opencode_base_url" "$ARK_MODEL" <<'PY'
import json
import os
import sys
from pathlib import Path

config_path = Path(sys.argv[1])
auth_path = Path(sys.argv[2])
provider = sys.argv[3]
base_url = sys.argv[4]
model = sys.argv[5]

config = {
    "$schema": "https://opencode.ai/config.json",
    "provider": {
        provider: {
            "npm": "@ai-sdk/openai-compatible",
            "name": "Volcengine Ark",
            "options": {"baseURL": base_url},
            "models": {
                model: {
                    "name": model,
                    "tool_call": True,
                    "temperature": True,
                    "reasoning": True,
                }
            },
        }
    },
    "model": f"{provider}/{model}",
    "permission": "allow",
    "share": "disabled",
}
auth = {provider: {"type": "api", "key": os.environ["ARK_API_KEY"]}}

config_path.write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
auth_path.write_text(json.dumps(auth, indent=2) + "\n", encoding="utf-8")
PY

cleanup() {
  rm -f "$auth_file"
}
trap cleanup EXIT

opencode "$@"
