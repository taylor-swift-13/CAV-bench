#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ARK_PROFILE_CONFIG="${ARK_PROFILE_CONFIG:-$ROOT/config/ark_api/profiles.json}"
ARK_PROVIDER_ID="${ARK_PROVIDER_ID:-ark}"

if [[ -n "${ARK_PROFILE:-}" ]]; then
  eval "$("$ROOT/scripts/ark_profile_env.py" --config "$ARK_PROFILE_CONFIG" "$ARK_PROFILE")"
fi

if [[ -z "${ARK_API_KEY:-}" || -z "${ARK_BASE_URL:-}" ]]; then
  echo "codex_ark_wrapper requires ARK_PROFILE or ARK_API_KEY plus ARK_BASE_URL" >&2
  exit 2
fi

codex_base_url="$ARK_BASE_URL"
case "$codex_base_url" in
  */v3) ;;
  */) codex_base_url="${codex_base_url}v3" ;;
  *) codex_base_url="${codex_base_url}/v3" ;;
esac

provider_args=(
  -c "model_provider=$ARK_PROVIDER_ID"
  -c "model_providers.$ARK_PROVIDER_ID.name=Volcengine Ark"
  -c "model_providers.$ARK_PROVIDER_ID.base_url=$codex_base_url"
  -c "model_providers.$ARK_PROVIDER_ID.env_key=ARK_API_KEY"
)

if [[ "${1:-}" == "exec" ]]; then
  shift
  exec codex exec "${provider_args[@]}" "$@"
fi

exec codex "${provider_args[@]}" "$@"
