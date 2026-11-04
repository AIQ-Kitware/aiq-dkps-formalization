"""Render the matching deck, request local Breeze narration, and assemble a video.

Uses the user's OpenAI-compatible local speech endpoint. Each narrated build's
explanation is sent in one request. Audio is cached by text and request settings.
Each narrated build plays when its own explanation starts, then holds until
that explanation ends. Chapters still correspond to complete slides.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import urllib.error
import urllib.request

from dkvis.matching_narration import ROOT, export, read_narration
from dkvis.palette import OUTPUT_SUFFIX, THEME


def duration(path: Path) -> float:
    result = subprocess.run(
        ["ffprobe", "-v", "error", "-show_entries", "format=duration",
         "-of", "default=noprint_wrappers=1:nokey=1", str(path)],
        check=True, capture_output=True, text=True)
    value = float(result.stdout.strip())
    if value <= 0:
        raise ValueError(f"media has no positive duration: {path}")
    return value


def speech(text: str, stem: Path, *, endpoint: str, model: str, voice: str,
           language: str | None, timeout: float) -> Path:
    payload = {"model": model, "input": text, "voice": voice,
               "response_format": "wav"}
    if language:
        payload["language"] = language
    digest = hashlib.sha256(json.dumps({"endpoint": endpoint, **payload},
                                      sort_keys=True).encode()).hexdigest()
    audio, metadata = stem.with_suffix(".wav"), stem.with_suffix(".json")
    if audio.is_file() and metadata.is_file():
        try:
            if json.loads(metadata.read_text())["request_sha256"] == digest:
                duration(audio)
                print(f"  cached {audio.name}", flush=True)
                return audio
        except (KeyError, ValueError, OSError, subprocess.CalledProcessError):
            pass
    request = urllib.request.Request(endpoint, data=json.dumps(payload).encode(),
                                     headers={"Content-Type": "application/json"})
    temporary = audio.with_suffix(".part.wav")
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            if "json" in response.headers.get("Content-Type", ""):
                raise RuntimeError(f"speech endpoint returned JSON instead of WAV: {response.read(2000)!r}")
            with temporary.open("wb") as output:
                while data := response.read(1024*1024):
                    output.write(data)
        seconds = duration(temporary)
        temporary.replace(audio)
        metadata.write_text(json.dumps({"request_sha256": digest, "model": model,
            "voice": voice, "language": language, "response_format": "wav",
            "seconds": seconds}, indent=2)+"\n")
    except urllib.error.HTTPError as error:
        raise RuntimeError(f"speech request failed ({error.code}): {error.read(2000).decode(errors='replace')}") from error
    except urllib.error.URLError as error:
        raise RuntimeError(f"cannot reach speech endpoint {endpoint}: {error.reason}") from error
    finally:
        temporary.unlink(missing_ok=True)
    return audio


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
            build.get("notes", "").strip() != text
            for build, text in zip(builds, script.beats)):
        raise RuntimeError(f"Stale narration or builds for {scene}; rerun without --skip-render.")
    result = [(ROOT / build["file"], text) for build, text in zip(builds, script.beats)]
    if not all(clip.is_file() for clip, _ in result):
        raise FileNotFoundError(f"Missing clips for {scene}; rerun without --skip-render.")
    return result


def narrated_segment(visual: Path, audio: Path, output: Path, *, pause: float,
                     fps: int, preset: str) -> float:
    visual_seconds, audio_seconds = duration(visual), duration(audio)
    seconds = max(visual_seconds, audio_seconds) + pause
    freeze = max(0, seconds-visual_seconds)
    temporary = output.with_suffix(".part.mp4")
    subprocess.run([
        "ffmpeg", "-hide_banner", "-loglevel", "error", "-y",
        "-i", str(visual), "-i", str(audio),
        "-map", "0:v:0", "-map", "1:a:0",
        "-vf", f"fps={fps},tpad=stop_mode=clone:stop_duration={freeze:.6f}",
        "-af", "apad", "-t", f"{seconds:.6f}",
        "-c:v", "libx264", "-preset", preset, "-crf", "20", "-pix_fmt", "yuv420p",
        "-c:a", "aac", "-b:a", "192k", "-movflags", "+faststart", str(temporary),
    ], check=True)
    temporary.replace(output)
    return duration(output)


def chapter_metadata(entries: list[dict], path: Path) -> Path:
    def escape(value):
        for char in ["\\", "=", ";", "#"]:
            value = value.replace(char, "\\"+char)
        return value.replace("\n", " ")
    lines = [";FFMETADATA1", "title=Theorem 5: the real matching proof"]
    for entry in entries:
        lines += ["[CHAPTER]", "TIMEBASE=1/1000",
                  f"START={round(entry['start']*1000)}",
                  f"END={round(entry['end']*1000)}",
                  f"title={escape(str(entry['number'])+'. '+entry['title'])}"]
    path.write_text("\n".join(lines)+"\n")
    return path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", default="http://127.0.0.1:8812/v1/audio/speech")
    parser.add_argument("--model", default="breeze-tts2")
    parser.add_argument("--voice", default="ryan")
    parser.add_argument("--language", help="optional language field; omitted from Breeze requests by default")
    parser.add_argument("--timeout", type=float, default=600)
    parser.add_argument("--quality", choices=list("lmhpk"), default="h")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--fps", type=int, default=30)
    parser.add_argument("--pause", type=float, default=1.5, help="seconds to pause after each slide's speech")
    parser.add_argument("--beat-pause", type=float, default=.35, help="seconds between narrated builds within a slide")
    parser.add_argument("--preset", default="veryfast", choices=["ultrafast","veryfast","fast","medium"])
    parser.add_argument("--skip-render", action="store_true", help="reuse existing Manim slide renders")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if min(args.pause,args.beat_pause) < 0 or args.fps <= 0 or args.timeout <= 0 or args.jobs <= 0:
        parser.error("pauses must be nonnegative; fps, timeout, and jobs must be positive")
    name = "matching-proof"+OUTPUT_SUFFIX
    if not args.skip_render:
        subprocess.run([sys.executable, "-m", "dkvis.build_slides", "matching-proof",
            "--quality", args.quality, "--fps", str(args.fps), "--jobs", str(args.jobs),
            "--one-file", "--html", str(ROOT / "renders" / f"{name}.standalone.html"),
            "--handout"], cwd=ROOT, check=True)
    export(ROOT / "renders" / f"{name}-narration", theme=THEME)
    work = ROOT / "renders" / f"{name}-narrated"
    work.mkdir(parents=True, exist_ok=True)
    scripts = read_narration()
    # Resolve every clip before making any potentially slow speech requests.
    visuals = {scene: narrated_builds(scene, ROOT / f"slides-{name}", script)
               for scene, script in scripts.items()}
    segments, entries = [], []
    start = 0.
    for number, (scene, script) in enumerate(scripts.items(), 1):
        print(f"[{number}/{len(scripts)}] {scene}: {script.title}", flush=True)
        chapter_start, builds = start, []
        for k, (visual, text) in enumerate(visuals[scene], 1):
            print(f"  explanation {k}/{len(visuals[scene])}", flush=True)
            # Scene/build names keep caches useful when earlier slides are inserted.
            stem = work / f"{scene}-beat{k:02d}"
            audio = speech(text, stem, endpoint=args.endpoint, model=args.model,
                           voice=args.voice, language=args.language, timeout=args.timeout)
            segment = stem.with_suffix(".mp4")
            pause = args.pause if k == len(visuals[scene]) else args.beat_pause
            seconds = narrated_segment(visual, audio, segment, pause=pause,
                                        fps=args.fps, preset=args.preset)
            builds.append({"number": k, "start": start, "end": start+seconds,
                           "audio": str(audio), "segment": str(segment)})
            start += seconds
            segments.append(segment)
        entries.append({"number": number, "scene": scene, "title": script.title,
                        "start": chapter_start, "end": start, "builds": builds})
    listing = concat_list(segments, work / "segments.txt")
    chapters = chapter_metadata(entries, work / "chapters.ffmetadata")
    output = (args.output or ROOT / "renders" / f"{name}.narrated.mp4").resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_suffix(".part.mp4")
    subprocess.run(["ffmpeg", "-hide_banner", "-loglevel", "error", "-y",
        "-f", "concat", "-safe", "0", "-i", str(listing), "-i", str(chapters),
        "-map", "0:v:0", "-map", "0:a:0", "-map_metadata", "1", "-map_chapters", "1",
        "-c", "copy", "-movflags", "+faststart", str(temporary)], check=True)
    temporary.replace(output)
    (work / "timeline.json").write_text(json.dumps(entries, indent=2)+"\n")
    print(f"Wrote {output} ({start/60:.1f} minutes, {len(entries)} chapters)")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, FileNotFoundError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error)) from error
