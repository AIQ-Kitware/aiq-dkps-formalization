"""Controlled long-passage TTS comparisons, isolated from normal lecture outputs.

Conditioning modes: original, previous, anchored (original + recent speech as
one composite reference). Staging uses an explicitly supplied shared voice
directory; the running server can read new references without a restart.
"""
from __future__ import annotations
import argparse
import hashlib
import html
import json
import os
from pathlib import Path
import shutil
import subprocess
import time
from dkvis.presentation.alignment import Aligner, phrase_crop, transcript_words
from dkvis.presentation.audio import speech, text_chunks
from dkvis.presentation.audio_quality import fingerprint, process_chunk
from dkvis.presentation.media import duration, assemble_narration
from dkvis.presentation.narration import read_deck_narration
from dkvis.presentation.paths import ROOT
from dkvis.presentation.provenance import snapshot
from dkvis.presentation.timing import timing
from dkvis.presentation.tts import load_profiles, resolve_profile, narrator_id, add_tts_arguments, tts_overrides

MODES=('original','previous','anchored')
VERSION=1


def passage_plan(scripts, max_words=90, max_chars=800):
    """Pack coherent sentences independently of visual build boundaries."""
    text=''; beats=[]
    for scene,script in scripts.items():
        for i,beat in enumerate(script.beats):
            clean=' '.join(beat.split())
            if text:text+=' '
            beats.append(dict(scene=scene,beat=i+1,char_start=len(text),char_end=len(text)+len(clean),text=clean))
            text+=clean
    passages=[]; cursor=0
    for chunk in text_chunks(text,max_words=max_words,max_chars=max_chars):
        start=text.find(chunk,cursor)
        if start<0 or text[cursor:start].strip():raise ValueError('Passage packing lost transcript text')
        passages.append(dict(text=chunk,char_start=start,char_end=start+len(chunk)))
        cursor=start+len(chunk)
    if text[cursor:].strip():raise ValueError('Passage packing omitted trailing text')
    return dict(text=text,beats=beats,passages=passages)


def crop_audio(source, crop, output):
    output=Path(output); output.parent.mkdir(parents=True,exist_ok=True)
    subprocess.run(['ffmpeg','-v','error','-y','-i',str(source),'-ss',str(crop['start']),
                    '-t',str(crop['end']-crop['start']),'-ar','24000','-ac','1',
                    '-c:a','pcm_s16le',str(output)],check=True)
    return output


def stage_reference(parts, voice_dir, cache):
    """Publish immutable, content-named references; never change a named voice."""
    voice_dir=Path(voice_dir); cache=Path(cache)
    if not voice_dir.is_dir():raise ValueError('Shared server voice directory does not exist')
    identity=[dict(sha256=fingerprint(p['audio']),text=p['text']) for p in parts]
    digest=hashlib.sha256(json.dumps(dict(parts=identity,pause=.15,version=VERSION),sort_keys=True).encode()).hexdigest()
    voice='dkvis-exp-'+digest[:24]
    target=voice_dir/f'{voice}.wav'; transcript=' '.join(p['text'] for p in parts)
    if not target.exists():
        temporary=cache/f'{voice}.wav'; temporary.parent.mkdir(parents=True,exist_ok=True)
        entries=[]; cursor=0
        for part in parts:
            seconds=duration(part['audio'])
            entries.append(dict(builds=[dict(audio=part['audio'],start=cursor,end=cursor+seconds)]))
            cursor+=seconds+.15
        assemble_narration(entries,temporary,fade_ms=0)
        # A file name identifies the exact conditioning inputs and join policy.
        published=target.with_suffix('.wav.part')
        shutil.copyfile(temporary,published)
        published.replace(target)
    text_path=target.with_suffix('.txt')
    if text_path.exists() and text_path.read_text().strip()!=transcript:
        raise ValueError('Conditioning reference name collision')
    text_path.write_text(transcript+'\n')
    return dict(voice=voice,sha256=fingerprint(target),text=transcript,
                components=identity,join_pause_seconds=.15)


def cue_times(plan, records):
    """Map each visual build to the first spoken word in its source range."""
    result=[]
    words=[]
    for row in records:
        for word in row['alignment']['words']:
            words.append({**word,'char_start':word['char_start']+row['char_start'],
                          'char_end':word['char_end']+row['char_start'],
                          'start':word['start']+row['start'],'end':word['end']+row['start']})
    for beat in plan['beats']:
        selected=[w for w in words if beat['char_start']<=w['char_start']<beat['char_end']]
        if not selected:raise ValueError('Visual cue has no aligned words')
        result.append({**beat,'start':selected[0]['start'],'words':selected})
    result[0]['start']=0
    return result, words


def run_mode(mode, plan, base, original, args, aligner, out):
    folder=out/mode; folder.mkdir(parents=True,exist_ok=True)
    records=[]; cursor=0; previous=None
    for i,passage in enumerate(plan['passages']):
        conditioning=[original]
        parent=None
        if mode!='original' and previous is not None:
            crop=phrase_crop(previous['alignment'],args.tail_seconds,tail=True)
            tail=crop_audio(previous['raw_audio'],crop,folder/f'context-{i:03d}.wav')
            recent=dict(audio=tail,text=crop['text'])
            conditioning=([original,recent] if mode=='anchored' else [recent])
            parent=dict(audio_sha256=fingerprint(previous['raw_audio']),crop=crop)
        reference=stage_reference(conditioning,args.voice_dir,out/'reference-staging')
        request={**base.get('request',{}),'seed':args.seed,'ref_text':reference['text']}
        print(f'{mode}: passage {i+1}/{len(plan["passages"])} ({len(passage["text"].split())} words)',flush=True)
        start=time.perf_counter()
        cache=(out/'speech-cache' if args.refresh_audio else ROOT/'renders/experiments/speech-cache'/narrator_id(base))
        raw=speech(passage['text'],cache/'speech',endpoint=base['endpoint'],
                   model=base['model'],voice=reference['voice'],language=base.get('language'),
                   timeout=base['timeout_seconds'],response_format=base['response_format'],request_settings=request,
                   max_audio_seconds=base.get('max_audio_seconds',60),profile=narrator_id(base),
                   max_speech_words_per_second=base.get('max_speech_words_per_second',12),
                   reference=dict(original_voice=base['voice'],conditioning=reference,parent=parent),
                   force=False)
        measured=time.perf_counter()-start
        generation=json.loads(raw.with_suffix('.json').read_text())
        alignment=aligner.align(raw,passage['text'],out.parent/'alignment-cache')
        processed=process_chunk(raw,out/'processed-cache',base['postprocess']) if base.get('postprocess',{}).get('enabled') else raw
        seconds=duration(raw)
        record={**passage,'number':i+1,'start':cursor,'end':cursor+seconds,
                'raw_audio':str(raw.resolve()),'audio':str(processed.resolve()),
                'conditioning':reference,'parent':parent,'alignment':alignment,
                'lookup_or_generation_seconds':measured,
                'source_generation_seconds':generation.get('generation_seconds'),
                'audio_processing':json.loads(processed.with_suffix('.json').read_text()) if processed!=raw else None}
        records.append(record); previous=record; cursor+=seconds+args.passage_pause
        (folder/'passages.json').write_text(json.dumps(records,indent=2)+'\n')
    for kind,key in [('raw','raw_audio'),('processed','audio')]:
        entries=[dict(builds=[dict(audio=r[key],start=r['start'],end=r['end'])]) for r in records]
        assemble_narration(entries,folder/f'{kind}.wav',fade_ms=8 if kind=='processed' else 0)
    cues, words=cue_times(plan,records)
    result=dict(mode=mode,passages=records,cues=cues,words=words,seconds=cursor-args.passage_pause)
    (folder/'timeline.json').write_text(json.dumps(result,indent=2)+'\n')
    return result


def write_report(out, results, metadata):
    """Local listening comparison; measurements are diagnostics, not rankings."""
    sections=[]
    esc=lambda value:html.escape(str(value),quote=True)
    for result in results:
        mode=result['mode']; folder=out/mode
        rows=[]; boundaries=[]
        for r in result['passages']:
            raw=os.path.relpath(r['raw_audio'],out)
            low=[w['text'] for w in r['alignment']['words'] if w['score']<.1]
            generated=r.get('source_generation_seconds')
            cost=f'{generated:.1f}s source generation' if generated is not None else 'source generation timing unavailable'
            processing=r.get('audio_processing') or {}
            levels=[]
            for kind in ['before','after']:
                info=processing.get(kind,{})
                lufs=info.get('loudness',{}).get('input_i')
                if lufs is not None:levels.append(f'{kind}: {lufs:.1f} LUFS')
            rows.append(f'<details><summary>Passage {r["number"]}: {r["end"]-r["start"]:.1f}s; {len(low)} low-score words</summary>'
                f'<p>{esc(r["text"])}</p><audio controls preload="none" src="{esc(raw)}"></audio>'
                f'<p>{cost}; current cache lookup/generation {r["lookup_or_generation_seconds"]:.2f}s. {esc("; ".join(levels))}</p>'
                f'<p>Words to review: {esc(", ".join(low) or "none flagged")}. Low scores can also reflect technical vocabulary or alignment errors.</p>'
                f'<p>Acoustic-model reading (diagnostic): {esc(r["alignment"]["recognized"])}</p></details>')
        for left,right in zip(result['passages'],result['passages'][1:]):
            point=right['start']; start=max(0,left['end']-3); end=min(result['seconds'],point+3)
            clips=[]
            boundary=dict(time=point,previous_passage=left['number'],next_passage=right['number'])
            for kind in ['raw','processed']:
                source=folder/f'{kind}.wav'
                # Stable master identity prevents reuse after refreshing synthesis.
                identity=fingerprint(source)
                clip=folder/f'join-{right["number"]:02d}-{kind}-{identity[:12]}.wav'
                if not clip.exists():crop_audio(source,dict(start=start,end=end),clip)
                clips.append(f'<label>{kind}<audio controls preload="none" src="{mode}/{clip.name}"></audio></label>')
                before=(left.get('audio_processing') or {}).get('before' if kind=='raw' else 'after',{})
                after=(right.get('audio_processing') or {}).get('before' if kind=='raw' else 'after',{})
                tail=before.get('ending_rms_dbfs'); head=after.get('opening_rms_dbfs')
                boundary[kind+'_onset_minus_previous_tail_db']=None if tail is None or head is None else head-tail
            boundaries.append(boundary)
            rows.append(f'<details><summary>Join before passage {right["number"]}, {point:.1f}s</summary>'
                +''.join(clips)+f'<pre>{esc(json.dumps(boundary,indent=2))}</pre></details>')
        (folder/'boundaries.json').write_text(json.dumps(boundaries,indent=2)+'\n')
        video=''
        if (folder/'aligned.mp4').exists():
            video=f'''<video controls preload="metadata"><source src="{mode}/aligned.mp4" type="video/mp4">
<track kind="captions" src="{mode}/captions.vtt" srclang="en" label="English"></video>
<button class="cc" aria-pressed="false">Captions off</button>
<label>Speed <select class="speed"><option>1</option><option>1.5</option><option>2</option><option>3</option><option>4</option></select>×</label>'''
        total=sum(r.get('source_generation_seconds') or 0 for r in result['passages'])
        sections.append(f'<section><h2>{mode}</h2><p>{result["seconds"]:.1f}s audio; {total:.1f}s source generation (shared cached passages counted in each variant).</p>'+video+
            f'<p>Raw speech</p><audio controls preload="none" src="{mode}/raw.wav"></audio>'
            f'<p>Processed speech</p><audio controls preload="none" src="{mode}/processed.wav"></audio>'
            f'<p><a href="{mode}/timeline.json">Transcript, timing and provenance</a> · <a href="{mode}/boundaries.json">Join measurements</a></p>'+''.join(rows)+'</section>')
    page='''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width"><title>TTS continuity experiment</title>
<style>body{font:17px system-ui;max-width:1150px;margin:2rem auto;padding:1rem;background:#10151e;color:#eee}section{border-top:1px solid #567;margin-top:2rem}audio,video{width:100%;margin:.5rem 0}a{color:#6cf}details{margin:1rem 0}p{line-height:1.5}button,select{font:inherit;margin:.5rem}pre{white-space:pre-wrap}</style>
<h1>TTS continuity experiment</h1><p>Same authored passages and generation settings. Original reference, previous-phrase conditioning, and original-plus-previous composite conditioning. The last mode combines two excerpts into one reference; it is not native two-context inference. Listen to intelligibility and boundaries; no automatic winner is assigned.</p>
<p>Captions and visual cues use forced alignment of the authored transcript. They do not certify that the model pronounced every word correctly. Join level differences compare active two-second edge windows; differing sounds naturally have differing levels.</p>'''+''.join(sections)+'''
<script>document.querySelectorAll('section').forEach(s=>{const v=s.querySelector('video');if(!v)return;
s.querySelector('.speed').onchange=e=>{v.playbackRate=Number(e.target.value)};
s.querySelector('.cc').onclick=e=>{const on=v.textTracks[0].mode!=='showing';v.textTracks[0].mode=on?'showing':'disabled';e.target.textContent=on?'Captions on':'Captions off';e.target.setAttribute('aria-pressed',String(on))};});</script></html>'''
    (out/'index.html').write_text(page)
    (out/'experiment.json').write_text(json.dumps(metadata,indent=2)+'\n')

def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--deck',required=True)
    parser.add_argument('--scenes',nargs='+',required=True)
    parser.add_argument('--modes',nargs='+',choices=MODES,default=list(MODES))
    parser.add_argument('--voice-dir',type=Path,required=True,help='Explicit shared directory mounted by the server')
    parser.add_argument('--reference-audio',type=Path,required=True)
    parser.add_argument('--reference-text',type=Path,required=True)
    add_tts_arguments(parser,default_profile='crall-math-dk-v2-breeze-tts2')
    parser.add_argument('--seed',type=int,default=42)
    parser.add_argument('--max-words',type=int,default=90)
    parser.add_argument('--max-chars',type=int,default=800)
    parser.add_argument('--reference-seconds',type=float,default=8)
    parser.add_argument('--tail-seconds',type=float,default=6)
    parser.add_argument('--passage-pause',type=float,default=.2)
    parser.add_argument('--refresh-audio',action='store_true')
    parser.add_argument('--output',type=Path)
    parser.add_argument('--fps',type=int,default=30)
    parser.add_argument('--skip-video',action='store_true')
    parser.add_argument('--cues',type=Path)
    args=parser.parse_args(argv)
    for name in ['max_words','max_chars','reference_seconds','tail_seconds','fps']:
        if getattr(args,name)<=0:parser.error(f'{name} must be positive')
    if args.passage_pause<0:parser.error('passage-pause must be nonnegative')
    if not args.voice_dir.is_dir():parser.error('voice-dir must be the existing shared server directory')
    for path in [args.reference_audio,args.reference_text]:
        if not path.is_file():parser.error(f'Reference file does not exist: {path}')
    doc=load_profiles(args.tts_config)
    try:
        overrides=tts_overrides(args)
    except ValueError as error:
        parser.error(str(error))
    base=resolve_profile(doc,args.tts_profile,overrides)
    scripts=read_deck_narration(args.deck)
    unknown=set(args.scenes)-scripts.keys()
    if unknown:parser.error(f'Unknown scenes: {unknown}')
    scripts={k:v for k,v in scripts.items() if k in args.scenes}
    plan=passage_plan(scripts,args.max_words,args.max_chars)
    run_key=hashlib.sha256(json.dumps(dict(plan=plan,voice=base['voice'],model=base['model'],
        request=base.get('request',{}),seed=args.seed,endpoint=base['endpoint'],postprocess=base['postprocess'],
        response_format=base['response_format'],language=base.get('language'),passage_pause=args.passage_pause,
        reference=fingerprint(args.reference_audio),reference_text=args.reference_text.read_text(),
        tail=args.tail_seconds,reference_seconds=args.reference_seconds,version=VERSION),sort_keys=True).encode()).hexdigest()[:16]
    out=(args.output or ROOT/'renders/experiments'/args.deck/run_key).resolve(); out.mkdir(parents=True,exist_ok=True)
    if args.refresh_audio:
        from datetime import datetime, timezone
        out=out/('refresh-'+datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
        out.mkdir(parents=True,exist_ok=True)
    aligner=Aligner()
    original_alignment=aligner.align(args.reference_audio,args.reference_text.read_text().strip(),out.parent/'alignment-cache')
    crop=phrase_crop(original_alignment,args.reference_seconds,tail=False)
    original=dict(audio=crop_audio(args.reference_audio,crop,out/'original-excerpt.wav'),text=crop['text'])
    metadata=dict(version=VERSION,deck=args.deck,scenes=list(scripts),voice=base['voice'],model=base['model'],
        request=base.get('request',{}),seed=args.seed,postprocess=base['postprocess'],reference_crop=crop,
        response_format=base['response_format'],language=base.get('language'),passage_pause=args.passage_pause,
        reference_basename=args.reference_audio.name,reference_sha256=fingerprint(args.reference_audio),
        endpoint_sha256=hashlib.sha256(base['endpoint'].encode()).hexdigest(),
        source=snapshot(args.deck,'video'),plan=plan,run_key=run_key,refresh_requested=args.refresh_audio)
    results=[]
    try:
        for mode in args.modes:
            result=run_mode(mode,plan,base,original,args,aligner,out)
            results.append(result)
            write_report(out,results,metadata)
            if not args.skip_video:
                from dkvis.presentation.cue_video import render_experiment_video
                render_experiment_video(args.deck,result,out/mode,args.cues,args.fps)
                write_report(out,results,metadata)
    finally:
        timing().report()
    print(f'Experiment: {out/"index.html"}',flush=True)


if __name__=='__main__':main()
