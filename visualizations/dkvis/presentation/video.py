"""Render an authored presentation with configurable TTS and measured timings.

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
from pathlib import Path
import subprocess
import sys

from dkvis.presentation.narration import export, narrated_decks, read_deck_narration
from dkvis.decks import get_deck
from dkvis.presentation.paths import ROOT
from dkvis.presentation.audio import synthesize_beat
from dkvis.presentation.media import concat_list, duration
from dkvis.palette import OUTPUT_SUFFIX, THEME
from dkvis.presentation.timing import timing
from dkvis.presentation.tts import DEFAULT_CONFIG, load_profiles, resolve_profile


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


def chapter_metadata(entries: list[dict], path: Path, *, title: str) -> Path:
    def escape(value):
        for char in ["\\", "=", ";", "#"]:
            value = value.replace(char, "\\" + char)
        return value.replace("\n", " ")

    lines = [";FFMETADATA1", f"title={escape(title)}"]
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


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--deck', choices=narrated_decks(), help='a deck with an authored transcript')
    parser.add_argument(
        "--tts-config", type=Path, default=DEFAULT_CONFIG, help="editable TOML server profiles"
    )
    parser.add_argument(
        "--tts-profile", help="profile name; defaults to DKVIS_TTS_PROFILE or tts.toml"
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
    args = parser.parse_args(argv)
    if not args.list_tts_profiles and not args.deck:
        parser.error('--deck is required for video production')
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
    scripts = read_deck_narration(args.deck)
    if args.scenes:
        unknown = set(args.scenes) - scripts.keys()
        if unknown:
            parser.error(f'Unknown scenes: {", ".join(sorted(unknown))}')
        scripts = {name: script for name, script in scripts.items() if name in args.scenes}
    name = args.deck + OUTPUT_SUFFIX
    profile = re.sub(r"[^a-zA-Z0-9_-]", "_", settings["profile"])
    log = timing()
    safe_settings = {k: v for k, v in settings.items() if k != "endpoint"}
    safe_settings["endpoint_sha256"] = hashlib.sha256(settings["endpoint"].encode()).hexdigest()
    log.set_context(
        application="presentation_video",
        deck=args.deck,
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
                            "dkvis.presentation.build",
                            args.deck,
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
                export(ROOT / "renders" / f"{name}-narration", theme=THEME,
                       deck_name=args.deck)
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
            chapters = chapter_metadata(entries, work / f"chapters-{profile}.ffmetadata",
                                        title=get_deck(args.deck).description or args.deck)
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
