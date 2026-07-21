#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import shlex
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROFILE_CONFIG = ROOT / "config" / "ark_api" / "profiles.json"
FIELDS = ("agent", "api_key", "base_url", "model")


def load_profile(config_path: Path, profile_name: str) -> dict[str, str]:
    try:
        data = json.loads(config_path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise SystemExit(f"cannot read Ark profile config {config_path}: {exc}")
    except json.JSONDecodeError as exc:
        raise SystemExit(f"invalid Ark profile config {config_path}: {exc}")

    profile = data.get(profile_name)
    if not isinstance(profile, dict):
        known = ", ".join(sorted(data)) if isinstance(data, dict) else ""
        raise SystemExit(f"unknown Ark profile: {profile_name}" + (f" (known: {known})" if known else ""))

    missing = [field for field in FIELDS if not isinstance(profile.get(field), str) or not profile[field]]
    if missing:
        raise SystemExit(f"Ark profile {profile_name} missing fields: {', '.join(missing)}")
    return {field: profile[field] for field in FIELDS}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("profile")
    parser.add_argument("--config", default=str(DEFAULT_PROFILE_CONFIG))
    parser.add_argument("--field", choices=FIELDS)
    args = parser.parse_args()

    profile = load_profile(Path(args.config), args.profile)
    if args.field:
        print(profile[args.field])
        return 0

    env = {
        "ARK_PROFILE_AGENT": profile["agent"],
        "ARK_API_KEY": profile["api_key"],
        "ARK_BASE_URL": profile["base_url"],
        "ANTHROPIC_AUTH_TOKEN": profile["api_key"],
        "ANTHROPIC_API_KEY": profile["api_key"],
        "ANTHROPIC_BASE_URL": profile["base_url"],
        "ARK_MODEL": profile["model"],
        "ANTHROPIC_MODEL": profile["model"],
    }
    for key, value in env.items():
        print(f"export {key}={shlex.quote(value)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
