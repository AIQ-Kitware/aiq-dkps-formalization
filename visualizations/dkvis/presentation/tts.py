"""Load editable TTS profiles and private endpoint overrides without dependencies."""

from __future__ import annotations

import os
from pathlib import Path
import shlex
import tomllib

from dkvis.presentation.paths import ROOT
DEFAULT_CONFIG = ROOT / "tts.toml"
DEFAULTS = dict(
    timeout_seconds=600,
    max_chars=420,
    max_words=65,
    max_audio_seconds=60.0,
    chunk_pause_seconds=0.12,
)


def load_env(path=ROOT / ".env"):
    if not path.exists():
        return
    for number, line in enumerate(path.read_text().splitlines(), 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("export "):
            line = line[7:]
        key, separator, value = line.partition("=")
        if not separator or not key.strip().isidentifier():
            raise ValueError(f"Invalid environment assignment in {path}:{number}")
        tokens = shlex.split(value, comments=True)
        if len(tokens) > 1:
            raise ValueError(f"Quote values containing spaces in {path}:{number}")
        os.environ.setdefault(key.strip(), tokens[0] if tokens else "")


def load_profiles(path=DEFAULT_CONFIG):
    load_env()
    with Path(path).open("rb") as stream:
        return tomllib.load(stream)


def resolve_profile(document, selected=None, overrides=None):
    selected = (
        selected or os.environ.get("DKVIS_TTS_PROFILE")
        or os.environ.get("MATCHING_TTS_PROFILE") or document.get("profile", "crall")
    )
    profiles = document.get("profiles", {})
    if selected not in profiles:
        raise ValueError(f'Unknown TTS profile {selected!r}; available: {", ".join(profiles)}')
    result = {**DEFAULTS, **document.get("defaults", {}), **profiles[selected], "profile": selected}
    result.update(overrides or {})
    result['postprocess'] = {**document.get('postprocess', {}), **result.get('postprocess', {})}
    if result['postprocess']:
        from dkvis.presentation.audio_quality import settings as audio_settings
        result['postprocess'] = audio_settings(result['postprocess'])
    variable = result.pop("endpoint_env", None)
    if variable:
        if not (overrides or {}).get("endpoint"):
            result["endpoint"] = os.environ.get(variable) or result.get("endpoint")
        if not result["endpoint"]:
            raise ValueError(
                f'Set {variable} in {ROOT / ".env"} or your environment for profile {selected}.'
            )
    for key in ["endpoint", "model", "voice", "response_format"]:
        if not result.get(key):
            raise ValueError(f"Missing {key} in TTS profile {selected}.")
    if result["response_format"] not in {"wav", "mp3"}:
        raise ValueError("TTS response_format must be wav or mp3")
    if result.get("max_chars", 420) < 80 or result.get("max_words", 65) < 5:
        raise ValueError("TTS max_chars must be at least 80 and max_words at least 5")
    if (
        result.get("max_audio_seconds", 60) < 0
        or result.get("chunk_pause_seconds", 0.12) < 0
        or result.get("timeout_seconds", 600) <= 0
    ):
        raise ValueError(
            "TTS duration limits and pauses must be nonnegative; timeout must be positive"
        )
    request = result.get("request", {})
    if (
        not isinstance(request, dict)
        or {"input", "model", "voice", "response_format"} & request.keys()
    ):
        raise ValueError("request settings may not replace input, model, voice, or response_format")
    return result
