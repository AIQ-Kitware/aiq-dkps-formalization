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


def edge_fades(samples, rate, milliseconds=8.):
    """Return PCM samples with short zero-ended ramps, retaining every sample."""
    import numpy as np

    result = np.array(samples, copy=True)
    count = min(round(rate*milliseconds/1000), len(result)//2)
    if count > 0:
        ramp = np.linspace(0., 1., count)
        result[:count] = result[:count]*ramp
        result[-count:] = result[-count:]*ramp[::-1]
    return result


def assemble_narration(entries, output, *, fade_ms=8., total_seconds=None):
    """Assemble lossless speech at build timestamps; encode the final audio once.

    Source audio is decoded directly, avoiding the independent AAC encoders in
    the video segments. Tiny edge fades prevent a discontinuity into silence.
    """
    import numpy as np
    import wave
    from dkvis.presentation.timing import timing

    rate = 48000
    output = Path(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    cursor = 0
    def silence(stream, count):
        for i in range(0, count, rate):
            stream.writeframesraw(b'\0\0'*min(rate, count-i))
    with timing().measure('narration_assembly', output=str(output), edge_fade_ms=fade_ms):
        with wave.open(str(output), 'wb') as stream:
            stream.setparams((1, 2, rate, 0, 'NONE', 'not compressed'))
            for scene in entries:
                for build in scene['builds']:
                    start, end = round(build['start']*rate), round(build['end']*rate)
                    if start < cursor:
                        raise ValueError('Narration timeline overlaps')
                    silence(stream, start-cursor)
                    decoded = subprocess.run(
                        ['ffmpeg', '-v', 'error', '-i', str(build['audio']), '-map', '0:a:0',
                         '-ar', str(rate), '-ac', '1', '-f', 's16le', '-'],
                        check=True, capture_output=True).stdout
                    samples = edge_fades(np.frombuffer(decoded, dtype='<i2'), rate, fade_ms)
                    if start+len(samples) > end:
                        raise ValueError('Speech exceeds the build; refusing to truncate it')
                    stream.writeframesraw(samples.astype('<i2').tobytes())
                    silence(stream, end-start-len(samples))
                    cursor = end
            if total_seconds is not None:
                total = round(total_seconds*rate)
                if cursor > total:
                    raise ValueError('Timeline extends beyond the source media')
                silence(stream, total-cursor)
    return output
