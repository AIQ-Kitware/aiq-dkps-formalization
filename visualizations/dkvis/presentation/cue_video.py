"""Schedule existing Manim animation pieces against aligned spoken phrases."""
from __future__ import annotations
import hashlib
import json
import math
from pathlib import Path
import subprocess
import yaml
from dkvis.presentation.alignment import transcript_words
from dkvis.presentation.audio_quality import fingerprint, ffmpeg_version
from dkvis.presentation.media import duration, concat_list
from dkvis.presentation.narration import read_deck_narration
from dkvis.presentation.paths import ROOT
from dkvis.presentation.timing import timing
from dkvis.presentation.video import narrated_builds


def phrase_time(words, phrase):
    target=[w['normalized'] for w in transcript_words(phrase)]
    values=[w['normalized'] for w in words]
    starts=[i for i in range(len(values)-len(target)+1) if values[i:i+len(target)]==target]
    if len(starts)!=1:raise ValueError(f'Cue phrase must occur exactly once in its build: {phrase!r}')
    selected=words[starts[0]:starts[0]+len(target)]
    return selected[0]['start'],min(w['score'] for w in selected)


def event_plan(beat, end, visual_seconds, definitions, fps):
    events=definitions or [dict(visual_at=0)]
    if events[0].get('visual_at',0)!=0:
        raise ValueError('The first visual event must begin at source time zero')
    sources=[float(e.get('visual_at',0)) for e in events]+[visual_seconds]
    if any(a>=b for a,b in zip(sources,sources[1:])):
        raise ValueError('Visual event offsets must increase within the rendered clip')
    starts=[]; scores=[]
    for event in events:
        t,score=phrase_time(beat['words'],event['phrase']) if event.get('phrase') else (beat['start'],None)
        starts.append(t+event.get('offset_seconds',0)); scores.append(score)
    if any(a>=b for a,b in zip(starts,starts[1:])):
        raise ValueError('Spoken cue events must be in source order')
    quantize=lambda t:round(t*fps)/fps
    ends=starts[1:]+[end]
    result=[]
    for i,event in enumerate(events):
        begin=beat['start'] if i==0 else starts[i]
        finish=ends[i]
        if not beat['start']-.1<=starts[i]<end or finish<=begin:
            raise ValueError('Spoken cue lies outside its visual build')
        begin,finish=quantize(begin),quantize(finish)
        if finish<=begin:raise ValueError('Visual event has less than one video frame')
        lead=max(0,quantize(starts[i])-begin)
        available=finish-begin-lead
        if available<=0:raise ValueError('No time remains to show the cued animation')
        source=sources[i+1]-sources[i]
        result.append(dict(start=begin,end=finish,lead=lead,source_start=sources[i],
            source_seconds=source,play_seconds=min(source,available),frames=round((finish-begin)*fps),
            phrase=event.get('phrase'),cue_score=scores[i]))
    return result


def render_piece(visual, event, cache, fps):
    inputs=dict(version=1,visual=fingerprint(visual),event=event,fps=fps,ffmpeg=ffmpeg_version())
    key=hashlib.sha256(json.dumps(inputs,sort_keys=True).encode()).hexdigest()
    output=cache/f'{key}.mp4'; metadata=output.with_suffix('.json')
    if output.exists() and metadata.exists():
        saved=json.loads(metadata.read_text())
        if saved.get('output_sha256')==fingerprint(output):
            timing().record('cue_video_cache',0,cache_hit=True,file=str(output));return output
    cache.mkdir(parents=True,exist_ok=True)
    seconds=event['frames']/fps
    scale=event['play_seconds']/event['source_seconds']
    filters=(f'setpts={scale}*(PTS-STARTPTS),fps={fps},'
             f'tpad=start_mode=clone:start_duration={event["lead"]}:stop_mode=clone:stop_duration={seconds},'
             f'trim=duration={seconds},setpts=PTS-STARTPTS')
    temporary=output.with_suffix('.part.mp4')
    with timing().measure('cue_video_encode',output=str(output),seconds=seconds):
        subprocess.run(['ffmpeg','-v','error','-y','-ss',str(event['source_start']),'-t',str(event['source_seconds']),
            '-i',str(visual),'-an','-vf',filters,'-frames:v',str(event['frames']),
            '-c:v','libx264','-preset','veryfast','-crf','20','-threads','2','-pix_fmt','yuv420p',str(temporary)],check=True)
        temporary.replace(output)
    metadata.write_text(json.dumps(dict(inputs=inputs,output_sha256=fingerprint(output)),indent=2)+'\n')
    return output


def write_captions(words, path):
    def stamp(t):
        ms=round(t*1000); sec,ms=divmod(ms,1000); minute,sec=divmod(sec,60); hour,minute=divmod(minute,60)
        return f'{hour:02d}:{minute:02d}:{sec:02d}.{ms:03d}'
    rows=['WEBVTT','']
    for i in range(0,len(words),10):
        group=words[i:i+10]
        text=' '.join(w['text'] for w in group).replace('&','&amp;').replace('<','&lt;')
        rows.extend([f'{stamp(group[0]["start"])} --> {stamp(group[-1]["end"])}',text,''])
    path.write_text('\n'.join(rows))


def render_experiment_video(deck, result, folder, cue_path=None, fps=30):
    from dkvis.lectures import lecture_path, load_index
    scripts=read_deck_narration(deck)
    default=(ROOT/lecture_path(next(k for k,v in load_index().items() if v['deck']==deck))).with_name('animation_cues.yaml')
    definitions=yaml.safe_load(Path(cue_path or default).read_text())['scenes'] if Path(cue_path or default).exists() else {}
    visuals={name:narrated_builds(name,ROOT/f'slides-{deck}',script) for name,script in scripts.items()
             if any(c['scene']==name for c in result['cues'])}
    clips=[]; schedule=[]
    for i,beat in enumerate(result['cues']):
        end=result['cues'][i+1]['start'] if i+1<len(result['cues']) else math.ceil(result['seconds']*fps)/fps
        visual=visuals[beat['scene']][beat['beat']-1][0]
        events=event_plan(beat,end,duration(visual),definitions.get(beat['scene'],{}).get(beat['beat']),fps)
        for event in events:
            schedule.append(dict(scene=beat['scene'],beat=beat['beat'],**event))
            clips.append(render_piece(visual,event,folder.parent/'video-cache',fps))
    listing=concat_list(clips,folder/'visual-segments.txt')
    output=folder/'aligned.mp4'; temporary=folder/'aligned.part.mp4'
    with timing().measure('cue_video_assemble',mode=result['mode'],output=str(output)):
        subprocess.run(['ffmpeg','-v','error','-y','-f','concat','-safe','0','-i',str(listing),
            '-i',str(folder/'processed.wav'),'-map','0:v:0','-map','1:a:0','-c:v','copy',
            '-c:a','aac','-b:a','192k','-movflags','+faststart',str(temporary)],check=True)
        temporary.replace(output)
    if duration(output)+.01<result['seconds']:
        raise ValueError('Synchronized video truncated its narration')
    (folder/'animation-timing.json').write_text(json.dumps(schedule,indent=2)+'\n')
    write_captions(result['words'],folder/'captions.vtt')
    return output
