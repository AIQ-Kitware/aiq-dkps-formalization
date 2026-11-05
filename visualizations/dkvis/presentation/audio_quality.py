"""Measure lecture audio and repair a saved render without TTS or Manim.

    python -m dkvis.presentation audio analyze renders/lecture.narrated.mp4 --timeline ...
    python -m dkvis.presentation audio repair renders/lecture.narrated.mp4 --timeline ...
"""
from __future__ import annotations

import argparse
from functools import lru_cache
import hashlib
import html
import json
import math
import os
import shutil
from pathlib import Path
import subprocess
import tempfile
import tomllib
import wave

import numpy as np

from dkvis.presentation.paths import ROOT
from dkvis.presentation.media import assemble_narration, duration
from dkvis.presentation.timing import timing

DEFAULTS = dict(enabled=True, target_lufs=-18., peak_db=-1.5, loudness_range=7.,
                max_gain_db=24., highpass_hz=60., compression=True,
                threshold_db=-20., ratio=2.5, attack_ms=5., release_ms=180., edge_fade_ms=8.)
VERSION = 3
CACHE = ROOT/'renders/audio-quality/cache'


def run(args):
    try:
        return subprocess.run(args, check=True, capture_output=True)
    except subprocess.CalledProcessError as error:
        raise RuntimeError(f'{args[0]} failed: {error.stderr.decode(errors="replace")[-3000:]}') from error


def settings(values=None):
    result = {**DEFAULTS, **(values or {})}
    for key in ['enabled', 'compression']:
        if not isinstance(result[key], bool):
            raise ValueError(f'{key} must be a boolean')
    for key, low, high in [('target_lufs', -36, -10), ('peak_db', -9, -.1),
                           ('loudness_range', 1, 30), ('max_gain_db', 0, 36),
                           ('highpass_hz', 0, 500), ('threshold_db', -60, 0),
                           ('edge_fade_ms', 0, 50), ('ratio', 1, 20), ('attack_ms', .1, 200), ('release_ms', 1, 2000)]:
        value = float(result[key])
        if not math.isfinite(value) or not low <= value <= high:
            raise ValueError(f'{key} must be between {low} and {high}')
        result[key] = value
    return result


@lru_cache
def ffmpeg_version():
    return run(['ffmpeg', '-version']).stdout.decode().splitlines()[0]


def fingerprint(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024*1024), b''):
            digest.update(block)
    return digest.hexdigest()


def loudness(path, config=None, prefix=''):
    cfg = settings(config)
    filt = (f'loudnorm=I={cfg["target_lufs"]}:TP={cfg["peak_db"]}:'
            f'LRA={cfg["loudness_range"]}:print_format=json')
    output = run(['ffmpeg', '-hide_banner', '-nostats', '-i', str(path), '-vn', '-af',
                  prefix+filt, '-f', 'null', '-']).stderr.decode()
    raw = json.loads(output[output.rfind('{'):output.rfind('}')+1])
    return {k: float(v) if k != 'normalization_type' and math.isfinite(float(v)) else
            (v if k == 'normalization_type' else None) for k, v in raw.items()}


def levels(samples, rate, window=.1):
    """Nonoverlapping RMS windows, including a correctly weighted final window."""
    samples = np.asarray(samples, dtype=np.float64)
    hop = max(1, round(rate*window))
    starts = np.arange(0, len(samples), hop)
    if not len(starts):
        return np.array([]), np.array([])
    lengths = np.minimum(hop, len(samples)-starts)
    power = np.add.reduceat(samples*samples, starts)/lengths
    return starts/rate, 10*np.log10(np.maximum(power, 1e-12))


def signal_summary(samples, rate, gate=-55.):
    times, rms = levels(samples, rate)
    active = rms > gate  # level gate, not a speech recognizer
    indices = np.flatnonzero(active)
    head = body = tail = np.array([])
    if len(indices):
        head = rms[active & (times < times[indices[0]]+2.)]
        body = rms[active & (times >= times[indices[0]]+2.)]
        tail = rms[active & (times >= times[indices[-1]]-2.)]
    median = lambda a: float(np.median(a)) if len(a) else None
    onset = (float(np.percentile(head, 90)-np.percentile(body, 90))
             if len(head) and len(body) else None)
    peak = float(np.max(np.abs(samples))) if len(samples) else 0.
    return dict(seconds=len(samples)/rate, sample_rate=rate,
                first_sample=float(samples[0]) if len(samples) else 0.,
                last_sample=float(samples[-1]) if len(samples) else 0.,
                sample_peak_dbfs=20*math.log10(max(peak, 1e-12)),
                rail_samples=int(np.count_nonzero(np.abs(samples) >= .999)),
                active_gate_dbfs=gate, active_rms_median_dbfs=median(rms[active]),
                opening_rms_dbfs=float(np.percentile(head, 90)) if len(head) else None,
                ending_rms_dbfs=float(np.percentile(tail, 90)) if len(tail) else None,
                opening_excess_db=onset, rms_time_seconds=times.tolist(), rms_dbfs=rms.tolist())


def measure(path):
    path = Path(path).resolve()
    key = hashlib.sha256(f'{fingerprint(path)}:{VERSION}:{ffmpeg_version()}'.encode()).hexdigest()
    target = CACHE/f'{key}.json'
    if target.exists():
        return {**json.loads(target.read_text()), 'file': str(path)}
    with timing().measure('audio_measure', input=str(path)):
        probe = json.loads(run(['ffprobe', '-v', 'error', '-show_streams', '-of', 'json', str(path)]).stdout)
        stream = next((s for s in probe['streams'] if s['codec_type'] == 'audio'), None)
        if stream is None:
            raise ValueError(f'No audio stream in {path}')
        rate = int(stream['sample_rate'])
        decoded = run(['ffmpeg', '-v', 'error', '-i', str(path), '-map', '0:a:0',
                       '-ac', '1', '-f', 'f32le', '-']).stdout
        summary = signal_summary(np.frombuffer(decoded, dtype='<f4'), rate)
        summary.update(file=str(path), source_channels=stream['channels'], loudness=loudness(path))
    CACHE.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(summary, indent=2, allow_nan=False))
    return summary


def process_chunk(source, directory, config=None):
    """Level a copy, compress gently, then perform measured two-pass loudnorm."""
    source, directory = Path(source).resolve(), Path(directory)
    cfg = settings(config)
    if not cfg['enabled']:
        return source
    key = hashlib.sha256(json.dumps(dict(source=fingerprint(source), config=cfg,
                                        version=VERSION, ffmpeg=ffmpeg_version()), sort_keys=True).encode()).hexdigest()[:20]
    target = directory/f'{source.stem}-{key}.wav'
    metadata = target.with_suffix('.json')
    if target.exists() and metadata.exists():
        timing().record('audio_process_cache', 0, source=str(source), output=str(target), cache_hit=True)
        return target
    directory.mkdir(parents=True, exist_ok=True)
    before = measure(source)
    input_i = before['loudness']['input_i']
    filters = []
    if cfg['highpass_hz']:
        filters.append(f'highpass=f={cfg["highpass_hz"]}')
    if input_i is not None and input_i > -60:
        gain = min(cfg['max_gain_db'], cfg['target_lufs']-input_i)
        filters.append(f'volume={gain}dB')
        if cfg['compression']:
            filters.append(f'acompressor=threshold={10**(cfg["threshold_db"]/20)}:'
                           f'ratio={cfg["ratio"]}:attack={cfg["attack_ms"]}:'
                           f'release={cfg["release_ms"]}:makeup=1:knee=2.8')
    with timing().measure('audio_process', source=str(source), output=str(target), settings=cfg):
        with tempfile.TemporaryDirectory(dir=directory) as temp:
            prepared = Path(temp)/'prepared.wav'
            run(['ffmpeg', '-v', 'error', '-i', str(source), '-vn', '-af', ','.join(filters) or 'anull',
                 '-ar', '48000', '-ac', '1', '-c:a', 'pcm_f32le', str(prepared)])
            measured = loudness(prepared, cfg)
            normalization = 'anull'
            if measured['input_i'] is not None and measured['input_i'] > -60:
                normalization = (f'loudnorm=I={cfg["target_lufs"]}:TP={cfg["peak_db"]}:LRA={cfg["loudness_range"]}:'
                                 f'measured_I={measured["input_i"]}:measured_TP={measured["input_tp"]}:'
                                 f'measured_LRA={measured["input_lra"]}:measured_thresh={measured["input_thresh"]}:'
                                 f'offset={measured["target_offset"]}:linear=true')
            fade = min(cfg['edge_fade_ms']/1000, before['seconds']/2)
            envelope = (f',afade=t=in:st=0:d={fade},afade=t=out:st={before["seconds"]-fade}:d={fade}'
                        if fade else '')
            temporary = Path(temp)/'result.wav'
            run(['ffmpeg', '-v', 'error', '-i', str(prepared), '-af', normalization+f',aresample=48000,asetpts=PTS-STARTPTS,apad,atrim=end_sample={round(before["seconds"]*48000)}'+envelope,
                 '-ar', '48000', '-ac', '1', '-c:a', 'pcm_s16le', str(temporary)])
            if abs(duration(temporary)-before['seconds']) > .002:
                raise ValueError(f'Processing changed audio duration: {duration(temporary)} versus {before["seconds"]}')
            temporary.replace(target)
        after = measure(target)
        metadata.write_text(json.dumps(dict(source=str(source), settings=cfg, before=before, after=after), indent=2))
    return target


def artifact(path):
    path = Path(path)
    if path.exists():
        return path
    if 'renders' in path.parts:
        relocated = ROOT/Path(*path.parts[path.parts.index('renders'):])
        if relocated.exists():
            return relocated
    raise FileNotFoundError(path)


@lru_cache
def historical_joins():
    result = {}
    log = ROOT/'renders/logs/render-timings.jsonl'
    if log.exists():
        for line in log.open():
            try:
                event = json.loads(line)
            except ValueError:
                continue
            if event.get('stage') in {'audio_join', 'audio_join_cache'} and event.get('input_files'):
                result[event['file']] = (event['input_files'], event.get('chunk_pause_seconds', .12))
    return result


def parts(audio):
    audio = artifact(audio)
    sidecar = audio.with_suffix('.parts.json')
    if sidecar.exists():
        info = json.loads(sidecar.read_text())
        return [artifact(p) for p in info['inputs']], info['pause']
    info = historical_joins().get(str(audio))
    if info:
        return [artifact(p) for p in info[0]], info[1]
    if '-joined-' in audio.stem:
        raise ValueError(f'No exact chunk provenance for {audio}; cannot infer request boundaries safely')
    return [audio], 0.


def audit(media, timeline=None):
    report = dict(media=str(Path(media).resolve()), overall=measure(media), chunks=[], boundaries=[])
    if timeline:
        for scene in json.loads(Path(timeline).read_text()):
            for build in scene['builds']:
                paths, pause = parts(build['audio'])
                offset = build['start']
                for i, path in enumerate(paths):
                    row = dict(scene=scene['scene'], beat=build['number'], chunk=i+1,
                               start=offset, metrics=measure(path))
                    report['chunks'].append(row)
                    offset += row['metrics']['seconds']+pause
    for previous, current in zip(report['chunks'], report['chunks'][1:]):
        end, start = previous['metrics']['ending_rms_dbfs'], current['metrics']['opening_rms_dbfs']
        delta = start-end if end is not None and start is not None else None
        report['boundaries'].append(dict(time=current['start'], delta_db=delta,
                                         scene=current['scene'], beat=current['beat'], chunk=current['chunk']))
    report['suspect_boundaries'] = [r for r in report['boundaries'] if r['delta_db'] is not None and abs(r['delta_db']) > 6]
    report['suspect_edges'] = [dict(time=r['start'], scene=r['scene'], beat=r['beat'], chunk=r['chunk'],
        step=max(abs(r['metrics']['first_sample']), abs(r['metrics']['last_sample'])))
        for r in report['chunks']
        if max(abs(r['metrics']['first_sample']), abs(r['metrics']['last_sample'])) > .00316]
    report['suspect_openings'] = [dict(time=r['start'], scene=r['scene'], beat=r['beat'], chunk=r['chunk'],
                                      excess_db=r['metrics']['opening_excess_db']) for r in report['chunks']
                                  if (r['metrics']['opening_excess_db'] or 0) > 6]
    return report


def repair(media, timeline, out, config, *, edges_only=False):
    """Reconstruct speech at original timestamps; copy video and encode audio once."""
    entries = json.loads(Path(timeline).read_text())
    directory = out/'processed'
    directory.mkdir(parents=True, exist_ok=True)
    repaired_entries = []
    master = out/'leveled.wav'
    rate = 48000
    with timing().measure('audio_repair', media=str(media), settings=config, edges_only=edges_only):
        for scene in entries:
            new_scene = {**scene, 'builds': []}
            repaired_entries.append(new_scene)
            for build in scene['builds']:
                sources, pause = parts(build['audio'])
                corrected = []
                for source in sources:
                    if edges_only:
                        target = directory/f'{source.stem}-{fingerprint(source)[:12]}-edges.wav'
                        assemble_narration([{'builds': [dict(audio=source, start=0., end=measure(source)['seconds'])]}],
                                           target, fade_ms=config['edge_fade_ms'])
                    else:
                        target = process_chunk(source, directory, config)
                    corrected.append(target)
                new_audio = out/f'{scene["scene"]}-beat{build["number"]:02d}.wav'
                with wave.open(str(new_audio), 'wb') as beat:
                    beat.setparams((1, 2, rate, 0, 'NONE', 'not compressed'))
                    for i, path in enumerate(corrected):
                        frames = run(['ffmpeg', '-v', 'error', '-i', str(path), '-ar', str(rate),
                                      '-ac', '1', '-f', 's16le', '-']).stdout
                        beat.writeframesraw(frames)
                        if i < len(corrected)-1:
                            beat.writeframesraw(b'\0\0'*round(pause*rate))
                new_audio.with_suffix('.parts.json').write_text(json.dumps(
                    dict(inputs=[str(p.resolve()) for p in corrected], pause=pause)))
                new_scene['builds'].append({**build, 'audio': str(new_audio.resolve())})
        assemble_narration(repaired_entries, master, fade_ms=config['edge_fade_ms'],
                           total_seconds=duration(media))
        target = out/'leveled.mp4'
        temporary = out/'leveled.part.mp4'
        run(['ffmpeg', '-v', 'error', '-i', str(media), '-i', str(master), '-map', '0:v:0', '-map', '1:a:0',
             '-map_metadata', '0', '-map_chapters', '0', '-c:v', 'copy', '-c:a', 'aac', '-b:a', '192k',
             '-movflags', '+faststart', str(temporary)])
        temporary.replace(target)
        timeline_out = out/'timeline.json'
        timeline_out.write_text(json.dumps(repaired_entries, indent=2))
    return target, timeline_out


def write_report(out, before, after=None):
    out.mkdir(parents=True, exist_ok=True)
    (out/'report.json').write_text(json.dumps(dict(before=before, after=after), indent=2, allow_nan=False))
    sections = []
    for label, report in [('Original', before), ('Corrected', after)]:
        if report is None:
            continue
        metric = report['overall']
        player = label.lower()
        source = html.escape(os.path.relpath(report['media'], out))
        width, height = 1000, 160
        time = metric['rms_time_seconds']; db = metric['rms_dbfs']
        stride = max(1, len(time)//3000)
        points = ' '.join(f'{t/metric["seconds"]*width:.1f},{height-(max(-65,min(0,d))+65)/65*height:.1f}' for t,d in zip(time[::stride],db[::stride]))
        events = sorted(report['suspect_boundaries'], key=lambda x: abs(x['delta_db']), reverse=True)[:30]
        rows = ''.join(f'<tr><td><button onclick="seek(\'{player}\',{e["time"]})">{e["time"]:.1f}s</button></td>'
                       f'<td>{html.escape(e["scene"])}, beat {e["beat"]}, chunk {e["chunk"]}</td><td>{e["delta_db"]:+.1f} dB</td></tr>' for e in events)
        openings = ''.join(f'<tr><td><button onclick="seek(\'{player}\',{e["time"]})">{e["time"]:.1f}s</button></td>'
                           f'<td>{html.escape(e["scene"])}, beat {e["beat"]}, chunk {e["chunk"]}</td><td>{e["excess_db"]:+.1f} dB</td></tr>'
                           for e in sorted(report['suspect_openings'], key=lambda x: -x['excess_db']))
        edge_rows = ''.join(f'<tr><td><button onclick="seek(\'{player}\',{e["time"]})">{e["time"]:.1f}s</button></td>'
                            f'<td>{html.escape(e["scene"])}, beat {e["beat"]}, chunk {e["chunk"]}</td>'
                            f'<td>{20*math.log10(e["step"]):.1f} dBFS</td></tr>' for e in report['suspect_edges'])
        sections.append(f'<h2>{label}</h2><video id="{player}" controls src="{source}" width="720"></video>'
                        f'<p>Integrated: {metric["loudness"]["input_i"]} LUFS; true peak: {metric["loudness"]["input_tp"]} dBTP; '
                        f'loudness range: {metric["loudness"]["input_lra"]} LU. '
                        f'{len(report["suspect_boundaries"])} candidate boundary jumps; {len(report["suspect_openings"])} candidate loud openings.</p>'
                        f'<svg viewBox="0 0 {width} {height}" onclick="seek(\'{player}\',event.offsetX/this.clientWidth*{metric["seconds"]})">'
                        f'<rect width="100%" height="100%" fill="#eef3f8"/><polyline points="{points}" fill="none" stroke="#176a93" stroke-width="1"/></svg>'
                        f'<p>100 ms RMS envelope, −65 to 0 dBFS; click to seek. Start/body and boundary flags are level heuristics, not speech recognition or proof of a defect.</p>'
                        f'<p>Boundary levels compare the 90th-percentile active RMS in the last/first two seconds; openings compare the first two seconds with the remaining body. Active windows exceed −55 dBFS.</p>'
                        f'<h3>Candidate boundary jumps</h3><table><tr><th>Time</th><th>Boundary</th><th>Level change</th></tr>{rows}</table>'
                        f'<h3>Nonzero source edges</h3><p>Request edges above −50 dBFS can click when joined to silence. This measures the source chunks, not an acoustic click classifier.</p><table>{edge_rows}</table>'
                        f'<h3>Candidate loud openings</h3><table><tr><th>Time</th><th>Chunk</th><th>Opening/body excess</th></tr>{openings}</table>')
    (out/'report.html').write_text('<!doctype html><meta charset="utf-8"><title>Lecture audio review</title>'
        '<style>body{font:17px system-ui;max-width:1100px;margin:30px auto}svg{width:100%}td,th{padding:8px;text-align:left}button{cursor:pointer}</style>'
        '<h1>Lecture audio review</h1>'+''.join(sections)+
        '<script>function seek(id,t){document.getElementById(id).currentTime=Math.max(0,t-1)}</script>')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=['analyze', 'repair'])
    parser.add_argument('media', type=Path)
    parser.add_argument('--timeline', type=Path)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--config', type=Path, default=ROOT/'tts.toml')
    parser.add_argument('--profile', default='crall')
    parser.add_argument('--edges-only', action='store_true', help='fade request edges and rebuild audio without changing loudness/compression')
    args = parser.parse_args(argv)
    if args.operation == 'repair' and args.timeline is None:
        parser.error('repair requires the render timeline to preserve synchronization')
    args.out.mkdir(parents=True, exist_ok=True)
    if any((args.out/name).exists() for name in ['leveled.mp4', 'leveled.wav', 'report.json']):
        parser.error('Choose a fresh --out directory to preserve the previous comparison')
    document = tomllib.loads(args.config.read_text())
    config = settings({**document.get('postprocess', {}),
                       **document.get('profiles', {}).get(args.profile, {}).get('postprocess', {})})
    # Renderers replace named outputs atomically. Keep the exact input for a
    # stable comparison even if another render publishes a newer video.
    snapshot = args.out / ('original'+args.media.suffix)
    shutil.copy2(args.media, snapshot)
    timeline_snapshot = None
    if args.timeline is not None:
        timeline_snapshot = args.out/'original-timeline.json'
        shutil.copy2(args.timeline, timeline_snapshot)
    try:
        before = audit(snapshot, timeline_snapshot)
        before['source_media'] = str(args.media.resolve())
        write_report(args.out, before)
        after = None
        if args.operation == 'repair':
            target, timeline = repair(snapshot, timeline_snapshot, args.out, config, edges_only=args.edges_only)
            after = audit(target, timeline)
            write_report(args.out, before, after)
        for name, report in [('Before', before), ('After', after)]:
            if report:
                m = report['overall']['loudness']
                print(name, f'{m["input_i"]} LUFS, {m["input_tp"]} dBTP, {len(report["suspect_boundaries"])} candidate jumps, {len(report["suspect_openings"])} candidate loud openings, {len(report["suspect_edges"])} nonzero source edges')
        print(f'Report: {args.out / "report.html"}')
    finally:
        timing().report()


if __name__ == '__main__':
    main()
