"""Render the matching deck with configurable TTS profiles and measured timings.

Uses OpenAI-compatible speech endpoints. Sentence-aware requests avoid server
duration limits; completed chunks are cached by text and request settings.
Each narrated build plays when its own explanation starts, then holds until
that explanation ends. Chapters still correspond to complete slides.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
import time
from pathlib import Path
import subprocess
import sys
import urllib.error
import urllib.request

from dkvis.matching_narration import ROOT, export, read_narration
from dkvis.palette import OUTPUT_SUFFIX, THEME
from dkvis.render_timing import timing
from dkvis.tts_config import DEFAULT_CONFIG, load_profiles, resolve_profile


def duration(path: Path) -> float:
    result = subprocess.run(
        [
            "ffprobe",
            "-v",
            "error",
            "-show_entries",
            "format=duration",
            "-of",
            "default=noprint_wrappers=1:nokey=1",
            str(path),
        ],
        check=True,
        capture_output=True,
        text=True,
    )
    value = float(result.stdout.strip())
    if value <= 0:
        raise ValueError(f"media has no positive duration: {path}")
    return value


class AudioLimitError(RuntimeError):
    """The server returned audio at its generation limit, possibly mid-sentence."""


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
    profile="custom",
    force=False,
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
            return [
                speech(
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
                    profile=profile,
                    force=settings.get("refresh_audio", False),
                )
            ]
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
    if len(parts) == 1:
        return parts[0]
    pause = settings.get("chunk_pause_seconds", 0.12)
    key = hashlib.sha256(
        json.dumps(dict(parts=[str(p) for p in parts], pause=pause)).encode()
    ).hexdigest()[:16]
    joined = cache / f"{label}-joined-{key}.wav"
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


def concat_list(paths: list[Path], output: Path) -> Path:
    def escaped(path):
        return str(path.resolve()).replace("'", "'\\''")

    output.write_text("".join(f"file '{escaped(path)}'\n" for path in paths))
    return output


def narrated_builds(scene: str, folder: Path, script) -> list[tuple[Path, str]]:
    """Preflight clips and their exact note-to-speech alignment before requests."""
    path = folder / f"{scene}.json"
    if not path.is_file():
        raise FileNotFoundError(f"Missing {path}; rerun without --skip-render.")
    builds = json.loads(path.read_text())["slides"]
    if len(builds) != len(script.beats) or any(
        build.get("notes", "").strip() != text for build, text in zip(builds, script.beats)
    ):
        raise RuntimeError(f"Stale narration or builds for {scene}; rerun without --skip-render.")
    result = [(ROOT / build["file"], text) for build, text in zip(builds, script.beats)]
    if not all(clip.is_file() for clip, _ in result):
        raise FileNotFoundError(f"Missing clips for {scene}; rerun without --skip-render.")
    return result


def narrated_segment(
    visual: Path, audio: Path, output: Path, *, pause: float, fps: int, preset: str
) -> float:
    with timing().measure(
        "video_segment",
        fps=fps,
        preset=preset,
        crf=20,
        pause=pause,
        audio=str(audio),
        visual=str(visual),
        output=str(output),
    ) as event:
        visual_seconds, audio_seconds = duration(visual), duration(audio)
        # Round UP to a video frame so the final audio samples cannot be cropped.
        seconds = math.ceil((max(visual_seconds, audio_seconds) + pause) * fps) / fps
        freeze = max(0, seconds - visual_seconds)
        temporary = output.with_suffix(".part.mp4")
        subprocess.run(
            [
                "ffmpeg",
                "-hide_banner",
                "-loglevel",
                "error",
                "-y",
                "-i",
                str(visual),
                "-i",
                str(audio),
                "-map",
                "0:v:0",
                "-map",
                "1:a:0",
                "-vf",
                f"fps={fps},tpad=stop_mode=clone:stop_duration={freeze:.6f}",
                "-af",
                "aresample=48000,apad",
                "-ar",
                "48000",
                "-ac",
                "1",
                "-t",
                f"{seconds:.6f}",
                "-c:v",
                "libx264",
                "-preset",
                preset,
                "-crf",
                "20",
                "-pix_fmt",
                "yuv420p",
                "-c:a",
                "aac",
                "-b:a",
                "192k",
                "-movflags",
                "+faststart",
                str(temporary),
            ],
            check=True,
        )
        temporary.replace(output)
        actual = duration(output)
        event.update(
            input_audio_seconds=audio_seconds,
            input_video_seconds=visual_seconds,
            output_seconds=actual,
            bytes=output.stat().st_size,
        )
        return actual


def chapter_metadata(entries: list[dict], path: Path) -> Path:
    def escape(value):
        for char in ["\\", "=", ";", "#"]:
            value = value.replace(char, "\\" + char)
        return value.replace("\n", " ")

    lines = [";FFMETADATA1", "title=Theorem 5: the real matching proof"]
    for entry in entries:
        lines += [
            "[CHAPTER]",
            "TIMEBASE=1/1000",
            f"START={round(entry['start']*1000)}",
            f"END={round(entry['end']*1000)}",
            f"title={escape(str(entry['number'])+'. '+entry['title'])}",
        ]
    path.write_text("\n".join(lines) + "\n")
    return path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--tts-config", type=Path, default=DEFAULT_CONFIG, help="editable TOML server profiles"
    )
    parser.add_argument(
        "--tts-profile", help="profile name; defaults to MATCHING_TTS_PROFILE or tts.toml"
    )
    parser.add_argument("--list-tts-profiles", action="store_true")
    parser.add_argument("--endpoint", help="override the selected profile endpoint")
    parser.add_argument("--model", help="override the selected profile model")
    parser.add_argument("--voice", help="override the selected profile voice")
    parser.add_argument("--language", help="optional request field")
    parser.add_argument("--response-format", choices=["wav", "mp3"])
    parser.add_argument("--timeout", type=float, help="override request timeout in seconds")
    parser.add_argument("--quality", choices=list("lmhpk"), default="h")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--fps", type=int, default=30)
    parser.add_argument("--pause", type=float, default=1.5)
    parser.add_argument("--beat-pause", type=float, default=0.35)
    parser.add_argument(
        "--preset", default="veryfast", choices=["ultrafast", "veryfast", "fast", "medium"]
    )
    parser.add_argument("--skip-render", action="store_true")
    parser.add_argument(
        "--refresh-audio",
        action="store_true",
        help="measure fresh synthesis even when audio is cached",
    )
    parser.add_argument(
        "--scenes", nargs="+", help="render selected chapters only, for quick comparisons"
    )
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    document = load_profiles(args.tts_config)
    if args.list_tts_profiles:
        for name, profile in document["profiles"].items():
            print(f"{name:12s} {profile['model']:30s} {profile['voice']}")
        return
    overrides = {
        key: getattr(args, key)
        for key in ["endpoint", "model", "voice", "response_format"]
        if getattr(args, key) is not None
    }
    if args.timeout is not None:
        overrides["timeout_seconds"] = args.timeout
    settings = resolve_profile(document, args.tts_profile, overrides)
    settings["refresh_audio"] = args.refresh_audio
    if args.language is not None:
        settings["request"] = {**settings.get("request", {}), "language": args.language}
    if (
        min(args.pause, args.beat_pause) < 0
        or min(args.fps, args.jobs, settings["timeout_seconds"]) <= 0
    ):
        parser.error("Pauses must be nonnegative; fps, jobs, and timeout must be positive")
    scripts = read_narration()
    if args.scenes:
        unknown = set(args.scenes) - scripts.keys()
        if unknown:
            parser.error(f'Unknown scenes: {", ".join(sorted(unknown))}')
        scripts = {name: script for name, script in scripts.items() if name in args.scenes}
    name = "matching-proof" + OUTPUT_SUFFIX
    profile = re.sub(r"[^a-zA-Z0-9_-]", "_", settings["profile"])
    log = timing()
    safe_settings = {k: v for k, v in settings.items() if k != "endpoint"}
    safe_settings["endpoint_sha256"] = hashlib.sha256(settings["endpoint"].encode()).hexdigest()
    log.set_context(
        application="matching_video",
        tts_profile=profile,
        tts_settings=safe_settings,
        fps=args.fps,
        preset=args.preset,
        quality=args.quality,
        jobs=args.jobs,
        pause=args.pause,
        beat_pause=args.beat_pause,
        theme=THEME,
    )
    try:
        with log.measure("run_total", scenes=list(scripts)):
            if not args.skip_render:
                with log.measure("slide_build"):
                    subprocess.run(
                        [
                            sys.executable,
                            "-m",
                            "dkvis.build_slides",
                            "matching-proof",
                            "--quality",
                            args.quality,
                            "--fps",
                            str(args.fps),
                            "--jobs",
                            str(args.jobs),
                            "--one-file",
                            "--html",
                            str(ROOT / "renders" / f"{name}.standalone.html"),
                            "--handout",
                        ],
                        cwd=ROOT,
                        check=True,
                    )
            else:
                log.record("slides_reused", 0, cache_hit=True)
            with log.measure("narration_export"):
                export(ROOT / "renders" / f"{name}-narration", theme=THEME)
            work = ROOT / "renders" / f"{name}-narrated"
            work.mkdir(parents=True, exist_ok=True)
            with log.measure("media_preflight"):
                visuals = {
                    scene: narrated_builds(scene, ROOT / f"slides-{name}", script)
                    for scene, script in scripts.items()
                }
            segments = []
            entries = []
            start = 0.0
            for number, (scene, script) in enumerate(scripts.items(), 1):
                print(f"[{number}/{len(scripts)}] {scene}: {script.title} [{profile}]", flush=True)
                chapter_start = start
                builds = []
                for k, (visual, text) in enumerate(visuals[scene], 1):
                    label = f"{scene}-beat{k:02d}"
                    audio = synthesize_beat(text, label, work, settings)
                    segment_dir = work / profile
                    segment_dir.mkdir(exist_ok=True)
                    segment = segment_dir / f"{label}.mp4"
                    pause = args.pause if k == len(visuals[scene]) else args.beat_pause
                    seconds = narrated_segment(
                        visual, audio, segment, pause=pause, fps=args.fps, preset=args.preset
                    )
                    builds.append(
                        dict(
                            number=k,
                            start=start,
                            end=start + seconds,
                            audio=str(audio),
                            segment=str(segment),
                        )
                    )
                    start += seconds
                    segments.append(segment)
                entries.append(
                    dict(
                        number=number,
                        scene=scene,
                        title=script.title,
                        start=chapter_start,
                        end=start,
                        builds=builds,
                    )
                )
            listing = concat_list(segments, work / f"segments-{profile}.txt")
            chapters = chapter_metadata(entries, work / f"chapters-{profile}.ffmetadata")
            suffix = f".{profile}.preview" if args.scenes else ""
            output = (args.output or ROOT / "renders" / f"{name}{suffix}.narrated.mp4").resolve()
            output.parent.mkdir(parents=True, exist_ok=True)
            temporary = output.with_suffix(".part.mp4")
            with log.measure("video_concat", output=str(output), segments=len(segments)) as event:
                subprocess.run(
                    [
                        "ffmpeg",
                        "-hide_banner",
                        "-loglevel",
                        "error",
                        "-y",
                        "-f",
                        "concat",
                        "-safe",
                        "0",
                        "-i",
                        str(listing),
                        "-i",
                        str(chapters),
                        "-map",
                        "0:v:0",
                        "-map",
                        "0:a:0",
                        "-map_metadata",
                        "1",
                        "-map_chapters",
                        "1",
                        "-c",
                        "copy",
                        "-movflags",
                        "+faststart",
                        str(temporary),
                    ],
                    check=True,
                )
                temporary.replace(output)
                event.update(output_seconds=duration(output), bytes=output.stat().st_size)
            timeline = json.dumps(entries, indent=2) + "\n"
            (work / f'timeline-{profile}{".preview" if args.scenes else ""}.json').write_text(
                timeline
            )
            if not args.scenes:
                (work / "timeline.json").write_text(timeline)
            print(f"Wrote {output} ({start/60:.1f} minutes, {len(entries)} chapters)", flush=True)
    finally:
        log.report()


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError, FileNotFoundError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error)) from error
