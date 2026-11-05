"""Recover the text actually synthesized, with approximate within-chunk captions.

No speech recognition or TTS request is needed. Existing audio-cache sidecars
preserve the request text; new timelines also keep their own text snapshot.
"""
from pathlib import Path
import json
import math


def read_json(path, default=None):
    try:
        return json.loads(Path(path).read_text())
    except (OSError, ValueError):
        return default


def local_path(root, value):
    """Only follow metadata references into the served tree, including symlinks."""
    root = Path(root).resolve()
    try:
        path = Path(value)
        path = (path if path.is_absolute() else root/path).resolve()
    except (TypeError,ValueError,OSError):
        return None
    try:
        path.relative_to(root)
    except ValueError:
        return None
    return path if not any(p.startswith('.') for p in path.relative_to(root).parts) else None


def speech_parts(root, audio, seen=None):
    """Return exact request text and duration for raw, processed or joined speech."""
    path = local_path(root, audio)
    if path is None or not path.is_file():
        return []
    seen = set(seen or ())
    if path in seen or len(seen)>20:
        return []
    seen.add(path)
    sidecar=local_path(root,path.with_suffix('.parts.json'))
    joined = read_json(sidecar) if sidecar else None
    if isinstance(joined,dict):
        result=[]
        inputs=joined.get('inputs', [])
        try:
            pause=float(joined.get('pause',0))
            if not isinstance(inputs,list) or not math.isfinite(pause) or pause<0:
                return []
        except (ValueError,TypeError):
            return []
        for i, source in enumerate(inputs):
            parts=speech_parts(root,source,seen)
            if not parts:
                return []  # Never present a silently incomplete transcript.
            result.extend(parts)
            if i<len(inputs)-1:
                result.append(dict(text='', seconds=pause))
        return result
    sidecar=local_path(root,path.with_suffix('.json'))
    metadata=read_json(sidecar,{}) if sidecar else {}
    if not isinstance(metadata,dict):
        return []
    if metadata.get('source'):
        return speech_parts(root,metadata['source'],seen)
    try:
        text_path=local_path(root,path.with_suffix('.txt'))
        if text_path is None:
            return []
        text=text_path.read_text().strip()
        seconds=float(metadata['seconds'])
        if not text or not math.isfinite(seconds) or seconds<=0:
            return []
        return [dict(text=text,seconds=seconds,generated=path.stat().st_mtime,
                     model=metadata.get('model'),voice=metadata.get('voice'))]
    except (OSError, KeyError, ValueError, TypeError):
        return []


def transcript_rows(root, entries):
    """Use render-time snapshots first, then exact historical speech requests."""
    result=[]
    for entry in entries:
        for build in entry.get('builds', []):
            try:
                start,end=float(build['start']),float(build['end'])
                if not all(math.isfinite(x) for x in [start,end]) or not 0<=start<end:
                    continue
                parts=build.get('speech_parts') or speech_parts(root,build.get('audio',''))
                text=build.get('text') or ' '.join(p['text'] for p in parts if p.get('text'))
                if not text:
                    continue
                seconds=float(build.get('speech_seconds',sum(p['seconds'] for p in parts) or end-start))
                if not math.isfinite(seconds) or seconds<=0:
                    continue
                if not parts:
                    parts=[dict(text=text,seconds=seconds)]
                result.append(dict(scene=entry.get('scene'),title=entry.get('title',''),
                                   start=start,end=end,speech_end=min(end,start+seconds),
                                   text=text,parts=parts))
            except (ValueError,TypeError,KeyError):
                continue
    return result


def cues(rows, words_per_cue=14):
    """Speech-chunk boundaries are known; word timing inside each is approximate."""
    result=[]
    for row in rows:
        cursor=row['start']
        for part in row['parts']:
            seconds=float(part['seconds'])
            words=part['text'].split()
            if words:
                groups=[' '.join(words[i:i+words_per_cue]) for i in range(0,len(words),words_per_cue)]
                total=sum(len(g) for g in groups)
                used=0.
                for group in groups:
                    length=seconds*len(group)/total
                    begin=cursor+used;end=min(row['speech_end'],begin+length)
                    if end>begin:
                        result.append(dict(start=begin,end=end,text=group))
                    used+=length
            cursor+=seconds
    return result


def vtt(rows):
    def stamp(value):
        ms=round(value*1000)
        return f'{ms//3600000:02}:{ms//60000%60:02}:{ms//1000%60:02}.{ms%1000:03}'
    # Escape WebVTT cue markup so arbitrary narration is displayed literally.
    def literal(text):
        return text.replace('&','&amp;').replace('<','&lt;').replace('>','&gt;')
    blocks=[f'{i}\n{stamp(c["start"])} --> {stamp(c["end"])}\n{literal(c["text"])}'
            for i,c in enumerate(cues(rows),1)]
    return 'WEBVTT\n\n'+'\n\n'.join(blocks)+'\n'
