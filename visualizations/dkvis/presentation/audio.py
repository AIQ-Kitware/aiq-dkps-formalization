"""Speech requests, complete-text chunking, caching, and lossless audio joins."""
from __future__ import annotations

import hashlib
from datetime import datetime, timezone
import json
import re
import shutil
import subprocess
import time
import urllib.error
import urllib.request
from pathlib import Path

from dkvis.presentation.media import duration
from dkvis.presentation.timing import timing


class AudioLimitError(RuntimeError):
    """The server returned audio at its generation limit, possibly mid-sentence."""


class AudioTooShortError(RuntimeError):
    """A response is implausibly short for a substantial passage."""


def check_audio_minimum(text, seconds, max_words_per_second=12.0):
    # A deliberately loose sanity check, not speech recognition. Short titles
    # and brief formula labels need no minimum-duration heuristic.
    words = len(text.split())
    if max_words_per_second and words >= 20 and seconds < words / max_words_per_second:
        raise AudioTooShortError(
            f'Suspiciously short TTS response: {words} words in {seconds:g}s '
            f'(more than {max_words_per_second:g} words/s).'
        )


def request_digest(endpoint, payload):
    return hashlib.sha256(
        json.dumps({"endpoint": endpoint, **payload}, sort_keys=True).encode()
    ).hexdigest()


def check_audio_limit(seconds, limit):
    if limit and seconds >= limit - min(0.1, limit * 0.005):
        raise AudioLimitError(
            f"Audio reached the configured {limit:g}s server limit ({seconds:g}s); split the text."
        )


def speech(
    text: str,
    stem: Path,
    *,
    endpoint: str,
    model: str,
    voice: str,
    language: str | None,
    timeout: float,
    response_format="wav",
    request_settings=None,
    max_audio_seconds=60.0,
    max_speech_words_per_second=12.0,
    profile="custom",
    force=False,
    reference=None,
    server_runtime=None,
) -> Path:
    payload = {
        **(request_settings or {}),
        "model": model,
        "input": text,
        "voice": voice,
        "response_format": response_format,
    }
    if language:
        payload["language"] = language
    digest = request_digest(endpoint, payload)
    # Preserve caches from different servers/voices instead of overwriting them.
    stem = stem.with_name(stem.name + "-" + digest[:16])
    stem.parent.mkdir(parents=True, exist_ok=True)
    audio, metadata = stem.with_suffix("." + response_format), stem.with_suffix(".json")
    log = timing()
    started = time.perf_counter()
    if not force and metadata.is_file():
        try:
            cached = json.loads(metadata.read_text())
            if cached["request_sha256"] == digest:
                if cached.get("status") == "duration_limit":
                    check_audio_limit(cached["seconds"], max_audio_seconds)
                if not audio.is_file():
                    raise FileNotFoundError(audio)
                seconds = duration(audio)
                check_audio_limit(seconds, max_audio_seconds)
                check_audio_minimum(text, seconds, max_speech_words_per_second)
                log.record(
                    "audio_cache",
                    time.perf_counter() - started,
                    profile=profile,
                    model=model,
                    voice=voice,
                    audio_seconds=seconds,
                    cache_hit=True,
                    file=str(audio),
                )
                return audio
        except AudioTooShortError:
            # Keep the failed response for diagnosis before a retry replaces it.
            rejected = audio.with_name(audio.stem + '.too-short.' + response_format)
            if audio.exists():
                shutil.copy2(audio, rejected)
                shutil.copy2(metadata, rejected.with_suffix('.json'))
            log.record('audio_cache_rejected', time.perf_counter() - started,
                       profile=profile, file=str(audio), reason='implausibly_short_audio')
            raise
        except AudioLimitError:
            log.record(
                "audio_cache_rejected",
                time.perf_counter() - started,
                profile=profile,
                file=str(audio),
                reason="server_duration_limit",
            )
            raise
        except (KeyError, ValueError, OSError, subprocess.CalledProcessError):
            pass
    request = urllib.request.Request(
        endpoint, data=json.dumps(payload).encode(), headers={"Content-Type": "application/json"}
    )
    temporary = audio.with_suffix(".part." + response_format)
    stem.with_suffix(".txt").write_text(text + "\n")
    fields = dict(
        profile=profile,
        model=model,
        voice=voice,
        response_format=response_format,
        endpoint_sha256=hashlib.sha256(endpoint.encode()).hexdigest(),
        request_settings=request_settings or {},
        request_sha256=digest,
        audio_file=str(audio),
        characters=len(text),
        words=len(text.split()),
        cache_hit=False,
    )
    try:
        with log.measure("tts_request", **fields) as event:
            request_start = time.perf_counter()
            with urllib.request.urlopen(request, timeout=timeout) as response:
                if "json" in response.headers.get("Content-Type", ""):
                    raise RuntimeError(
                        f"Speech endpoint returned JSON instead of audio: {response.read(2000)!r}"
                    )
                with temporary.open("wb") as output:
                    while data := response.read(1024 * 1024):
                        output.write(data)
            generation_seconds = time.perf_counter() - request_start
            seconds = duration(temporary)
            try:
                check_audio_minimum(text, seconds, max_speech_words_per_second)
            except AudioTooShortError:
                rejected = audio.with_name(audio.stem + f'.too-short-{time.time_ns()}.' + response_format)
                temporary.replace(rejected)
                event.update(rejected_file=str(rejected), reason='implausibly_short_audio', audio_seconds=seconds)
                rejected.with_suffix('.json').write_text(json.dumps(dict(
                    request_sha256=digest, status='too_short', seconds=seconds,
                    words=len(text.split()), request_settings=request_settings or {},
                    generation_seconds=generation_seconds,
                ), indent=2) + '\n')
                raise
            event.update(
                audio_seconds=seconds,
                request_seconds=generation_seconds,
                realtime_factor=generation_seconds / seconds,
                bytes=temporary.stat().st_size,
            )
            try:
                check_audio_limit(seconds, max_audio_seconds)
            except AudioLimitError:
                rejected = audio.with_suffix(".truncated." + response_format)
                temporary.replace(rejected)
                event.update(rejected_file=str(rejected), reason="server_duration_limit")
                metadata.write_text(
                    json.dumps(
                        dict(
                            request_sha256=digest,
                            status="duration_limit",
                            seconds=seconds,
                            rejected_file=str(rejected),
                        ),
                        indent=2,
                    )
                    + "\n"
                )
                raise
            temporary.replace(audio)
            metadata.write_text(
                json.dumps(
                    dict(
                        request_sha256=digest,
                        model=model,
                        voice=voice,
                        response_format=response_format,
                        seconds=seconds,
                        generation_seconds=generation_seconds,
                        realtime_factor=generation_seconds / seconds,
                        profile=profile,
                        generated_at=datetime.now(timezone.utc).isoformat(),
                        request_settings=request_settings or {},
                        reference=reference,
                        server_runtime=server_runtime,
                        endpoint_sha256=fields['endpoint_sha256'],
                    ),
                    indent=2,
                )
                + "\n"
            )
    except urllib.error.HTTPError as error:
        raise RuntimeError(
            f'Speech request failed ({error.code}): {error.read(2000).decode(errors="replace")}'
        ) from error
    except urllib.error.URLError as error:
        raise RuntimeError(f"Cannot reach speech endpoint: {error.reason}") from error
    finally:
        temporary.unlink(missing_ok=True)
    return audio


def text_chunks(text, max_chars=420, max_words=65):
    """Pack complete sentences; split an overlong sentence only at word boundaries."""
    text = " ".join(text.split())
    if not text:
        return []
    result = []
    current = ""
    for sentence in re.split(r"(?<=[.!?])\s+", text):
        candidate = (current + " " + sentence).strip()
        if len(candidate) <= max_chars and len(candidate.split()) <= max_words:
            current = candidate
            continue
        if current:
            result.append(current)
            current = ""
        words = sentence.split()
        for word in words:
            candidate = (current + " " + word).strip()
            if current and (len(candidate) > max_chars or len(candidate.split()) > max_words):
                result.append(current)
                current = word
            else:
                current = candidate
    if current:
        result.append(current)
    return result


def synthesize_beat(text, label, work, settings):
    """Complete every word, retrying capped responses with smaller requests."""
    profile = settings["profile"]
    cache = work / "audio" / re.sub(r"[^a-zA-Z0-9_-]", "_", profile)
    limit = settings.get("max_audio_seconds", 60.0)
    chunks = text_chunks(text, settings.get("max_chars", 420), settings.get("max_words", 65))
    if not chunks:
        raise ValueError("Cannot synthesize empty narration")
    parts = []

    def synthesize_piece(piece):
        try:
            def request_piece(force):
                return speech(
                    piece,
                    cache / label,
                    endpoint=settings["endpoint"],
                    model=settings["model"],
                    voice=settings["voice"],
                    language=None,
                    timeout=settings.get("timeout_seconds", 600),
                    response_format=settings["response_format"],
                    request_settings=settings.get("request", {}),
                    max_audio_seconds=limit,
                    max_speech_words_per_second=settings.get('max_speech_words_per_second', 12.0),
                    profile=profile,
                    force=force,
                    reference=settings.get("reference"),
                    server_runtime=settings.get("server_runtime"),
                )
            try:
                return [request_piece(settings.get('refresh_audio', False))]
            except AudioTooShortError:
                print('  Incomplete speech response: regenerating this request once.', flush=True)
                timing().record('audio_short_retry', 0, profile=profile, words=len(piece.split()))
                return [request_piece(True)]
        except AudioLimitError:
            words = len(piece.split())
            if words < 2:
                raise
            smaller = text_chunks(piece, settings.get("max_chars", 420), max(1, words // 2))
            if len(smaller) < 2:
                raise
            print(
                f"  Server duration limit: retrying {words} words as {len(smaller)} shorter requests.",
                flush=True,
            )
            timing().record(
                "audio_split_retry", 0, profile=profile, words=words, parts=len(smaller)
            )
            return [path for subpiece in smaller for path in synthesize_piece(subpiece)]

    for i, chunk in enumerate(chunks, 1):
        print(f"  speech chunk {i}/{len(chunks)} ({len(chunk.split())} words)", flush=True)
        parts.extend(synthesize_piece(chunk))
    # Keep raw synthesis caches unchanged. Processing has a separate content and
    # settings cache, so audio can be retuned without another server request.
    from dkvis.presentation.audio_quality import process_chunk, fingerprint
    processing = settings.get('postprocess', {})
    if processing.get('enabled', False):
        parts = [process_chunk(part, work/'processed'/profile, processing) for part in parts]
    if len(parts) == 1:
        return parts[0]
    pause = settings.get("chunk_pause_seconds", 0.12)
    key = hashlib.sha256(
        json.dumps(dict(parts=[dict(path=str(p), sha256=fingerprint(p)) for p in parts], pause=pause)).encode()
    ).hexdigest()[:16]
    joined = cache / f"{label}-joined-{key}.wav"
    # Persist exact request boundaries even when an existing join is reused.
    joined.with_suffix('.parts.json').write_text(json.dumps(
        dict(inputs=[str(p.resolve()) for p in parts], pause=pause), indent=2))
    if joined.exists() and not settings.get("refresh_audio", False):
        started = time.perf_counter()
        seconds = duration(joined)
        timing().record(
            "audio_join_cache",
            time.perf_counter() - started,
            profile=profile,
            audio_seconds=seconds,
            file=str(joined),
            cache_hit=True,
            input_files=[str(part) for part in parts],
        )
        return joined
    with timing().measure(
        "audio_join",
        profile=profile,
        parts=len(parts),
        chunk_pause_seconds=pause,
        input_files=[str(part) for part in parts],
    ) as event:
        inputs = [arg for part in parts for arg in ["-i", str(part)]]
        filters = []
        for i in range(len(parts)):
            pad = f",apad=pad_dur={pause}" if i < len(parts) - 1 and pause else ""
            filters.append(
                f"[{i}:a]aresample=48000,aformat=sample_fmts=s16:channel_layouts=mono,asetpts=PTS-STARTPTS{pad}[a{i}]"
            )
        filters.append(
            "".join(f"[a{i}]" for i in range(len(parts))) + f"concat=n={len(parts)}:v=0:a=1[out]"
        )
        temporary = joined.with_suffix(".part.wav")
        subprocess.run(
            [
                "ffmpeg",
                "-hide_banner",
                "-loglevel",
                "error",
                "-y",
                *inputs,
                "-filter_complex",
                ";".join(filters),
                "-map",
                "[out]",
                "-c:a",
                "pcm_s16le",
                str(temporary),
            ],
            check=True,
        )
        temporary.replace(joined)
        event.update(audio_seconds=duration(joined), file=str(joined))
    return joined
