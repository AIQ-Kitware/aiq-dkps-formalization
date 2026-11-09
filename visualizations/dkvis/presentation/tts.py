"""Load editable TTS profiles and private endpoint overrides without dependencies."""

from __future__ import annotations

import os
import json
from datetime import datetime, timezone
import urllib.request
import urllib.error
from urllib.parse import urlsplit, urlunsplit
from pathlib import Path
import shlex
import tomllib
import wave

from dkvis.presentation.paths import ROOT
DEFAULT_CONFIG = ROOT / "tts.toml"
# Machine-local add-on config (gitignored): may add or override
# [profiles.*] and [pronunciation_lexicons] entries without touching any
# checked-in file. It is merged in only when the default config is loaded;
# an explicit config path is honored exactly as written.
LOCAL_CONFIG = ROOT / "tts.local.toml"
DEFAULTS = dict(
    timeout_seconds=600,
    max_chars=420,
    max_words=65,
    max_audio_seconds=60.0,
    max_speech_words_per_second=12.0,
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


def load_profiles(path=None):
    """Load the shared profiles plus local overrides, or an explicit TOML alone."""
    load_env()
    config_path = DEFAULT_CONFIG if path is None else Path(path)
    with config_path.open('rb') as stream:
        document = tomllib.load(stream)
    document['_config_dir'] = str(config_path.resolve().parent)
    if path is None:
        merge_local_overlay(document)
    return document


def _merge_tables(base, changes):
    """Merge TOML tables without dropping unspecified nested profile options."""
    merged = dict(base)
    for name, value in changes.items():
        old = merged.get(name)
        if isinstance(old, dict) and isinstance(value, dict):
            merged[name] = _merge_tables(old, value)
        else:
            merged[name] = value
    return merged


def merge_local_overlay(document):
    """Apply the gitignored machine-local settings over the shared profiles.

    A local profile may override only its endpoint, voice, request fields, or
    other selected settings. Unspecified settings come from tts.toml.
    Specifying an endpoint in the local file takes precedence over an inherited
    endpoint_env setting; an explicit local endpoint_env restores env lookup.
    """
    if not LOCAL_CONFIG.is_file():
        return document
    with LOCAL_CONFIG.open('rb') as stream:
        overlay = tomllib.load(stream)
    if 'profile' in overlay:
        document['profile'] = overlay['profile']
    for section in ('defaults', 'postprocess', 'pronunciations'):
        if section in overlay:
            document[section] = _merge_tables(document.get(section, {}), overlay[section])
    for model, lexicon in overlay.get('pronunciation_lexicons', {}).items():
        # Relative private paths are relative to tts.local.toml, not tts.toml.
        if isinstance(lexicon, str) and lexicon and not Path(lexicon).expanduser().is_absolute():
            lexicon = str((LOCAL_CONFIG.parent / lexicon).resolve())
        document.setdefault('pronunciation_lexicons', {})[model] = lexicon
    for name, patch in overlay.get('profiles', {}).items():
        if not isinstance(patch, dict):
            raise ValueError(f'Local TTS profile {name!r} must be a table')
        patch = dict(patch)
        if isinstance(patch.get('pronunciation_lexicon'), str):
            lexicon = Path(patch['pronunciation_lexicon']).expanduser()
            if not lexicon.is_absolute():
                patch['pronunciation_lexicon'] = str((LOCAL_CONFIG.parent / lexicon).resolve())
        current = document.setdefault('profiles', {}).get(name, {})
        merged = _merge_tables(current, patch)
        if 'endpoint' in patch and 'endpoint_env' not in patch:
            # Otherwise KOKORO_TTS_ENDPOINT or CRALL_TTS_ENDPOINT in .env
            # silently cancels the explicit local URL.
            merged.pop('endpoint_env', None)
        if 'voice' in patch and patch['voice'] != current.get('voice') and 'reference' not in patch:
            # A changed voice cannot inherit a different voice's reference.
            merged.pop('reference', None)
        document['profiles'][name] = merged
    return document


def resolve_profile(document, selected=None, overrides=None):
    selected = (
        selected or os.environ.get("DKVIS_TTS_PROFILE")
        or os.environ.get("MATCHING_TTS_PROFILE") or document.get("profile", "crall-math-dk-v2-breeze-tts2")
    )
    profiles = document.get("profiles", {})
    if selected not in profiles:
        raise ValueError(f'Unknown TTS profile {selected!r}; available: {", ".join(profiles)}')
    result = {**DEFAULTS, **document.get("defaults", {}), **profiles[selected], "profile": selected}
    if 'voice' in (overrides or {}):
        # An explicit API voice must also identify the output, including profiles
        # without a narrator label and overrides that repeat the default voice.
        result['narrator_voice'] = overrides['voice']
        if overrides['voice'] != result.get('voice'):
            result.pop('reference', None)
    inherited_request = result.get('request', {})
    inherited_postprocess = result.get('postprocess', {})
    result.update(overrides or {})
    if 'request' in (overrides or {}) and isinstance(inherited_request, dict) and isinstance(result['request'], dict):
        result['request'] = {**inherited_request, **result['request']}
    if 'postprocess' in (overrides or {}) and isinstance(inherited_postprocess, dict) and isinstance(result['postprocess'], dict):
        result['postprocess'] = {**inherited_postprocess, **result['postprocess']}
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
        or result.get('max_speech_words_per_second', 12) < 0
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
    if result.get('reference'):
        result['reference'] = reference_snapshot(result['reference'])
    from dkvis.presentation.pronunciation import validate_replacements, load_pls_aliases
    result.setdefault('pronunciation_lexicon', document.get('pronunciation_lexicons', {}).get(result['model']))
    if 'pronunciation_replacements' not in result:
        lexicon = result['pronunciation_lexicon']
        if lexicon:
            path = Path(lexicon).expanduser()
            if not path.is_absolute():
                path = Path(document.get('_config_dir', ROOT)) / path
            result['pronunciation_replacements'] = load_pls_aliases(path)
        else:
            result['pronunciation_replacements'] = document.get('pronunciations', {}).get(result['model'], {})
    validate_replacements(result['pronunciation_replacements'])
    return result


def narrator_id(settings):
    """Name public variants by reference speaker and model when configured.

    Raw speech retains the base profile's cache directory, with the API voice
    in each request hash. Encoded scene files use this narrator identity so
    two voices sharing defaults cannot overwrite one another's segments.
    """
    speaker = settings.get('narrator_voice')
    return f"{speaker}-{settings['model']}" if speaker else settings['profile']


def reference_snapshot(reference):
    """Keep portable reference names, with optional local file observations.

    These are client-side observations, not an attestation of remote file contents.
    No audio data, absolute host paths, or reference hashes are stored.
    """
    result={'source':reference.get('source'), 'basis':'configured filenames',
            'observed_at':datetime.now(timezone.utc).isoformat()}
    directory=os.environ.get('DKVIS_TTS_REFERENCE_DIR')
    for kind in ['audio','transcript']:
        name=reference[kind]
        if not isinstance(name,str) or Path(name).name!=name or name in {'.','..'}:
            raise ValueError('Reference audio/transcript must be plain basenames')
        info={'basename':name}
        if directory:
            path=Path(directory)/name
            try:
                stat=path.stat()
                info.update(bytes=stat.st_size,modified_at=datetime.fromtimestamp(stat.st_mtime,timezone.utc).isoformat())
                if kind=='transcript':
                    info['text']=path.read_text(encoding='utf-8')
                else:
                    try:
                        with wave.open(str(path),'rb') as stream:
                            info.update(sample_rate=stream.getframerate(),channels=stream.getnchannels(),
                                        sample_width_bytes=stream.getsampwidth(),
                                        seconds=stream.getnframes()/stream.getframerate())
                    except (wave.Error,EOFError):
                        pass
                info['observation']='local file snapshot'
            except (OSError,UnicodeError):
                info['observation']='local file unavailable'
        result[kind]=info
    return result


def server_runtime(endpoint):
    """Best-effort runtime metadata from local-ai; unsupported servers still work."""
    parsed=urlsplit(endpoint)
    path=parsed.path.rsplit('/audio/speech',1)[0]+'/runtime'
    url=urlunsplit((parsed.scheme,parsed.netloc,path,'',''))
    observed_at=datetime.now(timezone.utc).isoformat()
    fields=['backend','model_alias','model_revision','source_revision','device',
            'dtype_policy','effective_dtype','sample_rate','loaded_at_unix',
            'pipeline','breeze_fast','attention_implementation','torch_version',
            'cuda_version','cudnn_version','gpu_name','gpu_capability']
    try:
        with urllib.request.urlopen(url,timeout=3) as response:
            data=json.load(response)
        if not isinstance(data,dict):
            raise ValueError('Expected runtime object')
        return dict(status='reported',observed_at=observed_at,details={k:data[k] for k in fields if k in data})
    except (OSError,ValueError,urllib.error.URLError) as error:
        return dict(status='unavailable',observed_at=observed_at,reason=type(error).__name__)


def add_tts_arguments(parser, default_profile=None):
    """Common direct overrides for production videos and continuity experiments."""
    parser.add_argument('--tts-config',type=Path,default=None,help='TOML server defaults; explicit path disables automatic local overlay')
    parser.add_argument('--tts-profile',default=default_profile,help='profile to use as defaults')
    for name in ['endpoint','model','voice','instruction','language']:
        parser.add_argument('--'+name,help=f'override the profile {name}')
    parser.add_argument('--response-format',choices=['wav','mp3'])
    parser.add_argument('--timeout',type=float,help='request timeout in seconds')
    parser.add_argument('--request-json',type=json.loads,help='additional speech API fields')
    parser.add_argument('--tts-settings-json',type=json.loads,help='client profile overrides')


def tts_overrides(args):
    result=args.tts_settings_json if args.tts_settings_json is not None else {}
    if not isinstance(result,dict):raise ValueError('--tts-settings-json must be a JSON object')
    result=dict(result)
    for key in ['endpoint','model','voice','response_format']:
        if getattr(args,key) is not None:result[key]=getattr(args,key)
    if args.timeout is not None:result['timeout_seconds']=args.timeout
    request=result.get('request',{})
    if not isinstance(request,dict):raise ValueError('TTS request settings must be a JSON object')
    request=dict(request)
    if args.request_json is not None:
        if not isinstance(args.request_json,dict):raise ValueError('--request-json must be a JSON object')
        request.update(args.request_json)
    if args.instruction is not None:request['instruction']=args.instruction
    if args.language is not None:request['language']=args.language
    if request:result['request']=request
    return result
