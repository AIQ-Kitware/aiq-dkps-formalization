"""Small FFprobe and FFmpeg utilities shared by audio and video production."""
from pathlib import Path
import subprocess


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


def concat_list(paths: list[Path], output: Path) -> Path:
    def escaped(path):
        return str(path.resolve()).replace("'", "'\\''")

    output.write_text("".join(f"file '{escaped(path)}'\n" for path in paths))
    return output
