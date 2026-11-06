"""Speech-independent tests of alignment, passage packing, and conditioning identity."""
from pathlib import Path
import shutil
import subprocess
import wave
import numpy as np
import pytest
from dkvis.presentation.alignment import ctc_path, phrase_crop
from dkvis.presentation.continuity import passage_plan, cue_times, stage_reference
from dkvis.presentation.cue_video import phrase_time, event_plan, render_piece
from dkvis.presentation.narration import Narration
from dkvis.presentation.media import duration


def emissions(ids, classes=4):
    result=np.full((len(ids),classes),-10.)
    result[np.arange(len(ids)),ids]=0
    return result


def test_ctc_aligns_labels_and_requires_a_blank_between_repeated_letters():
    states,labels=ctc_path(emissions([0,1,1,0,2,0,3,3,0]),[1,2,3])
    assert list(labels[states])==[0,1,1,0,2,0,3,3,0]
    states,labels=ctc_path(emissions([1,0,1]),[1,1])
    assert list(labels[states])==[1,0,1]
    with pytest.raises(ValueError,match='too few frames'):
        ctc_path(emissions([1,1]),[1,1])


def test_passages_cross_visual_boundaries_without_losing_words():
    scripts={'One':Narration('','','',('Alpha beta gamma. Delta epsilon.','Zeta eta theta.')),
             'Two':Narration('','','',('Iota kappa lambda.',))}
    plan=passage_plan(scripts,max_words=7,max_chars=100)
    assert ' '.join(p['text'] for p in plan['passages'])==plan['text']
    assert len(plan['beats'])==3
    # The final word of each build still maps to that exact build after packing.
    records=[]
    for i,p in enumerate(plan['passages']):
        words=[]
        import re
        for j,m in enumerate(re.finditer(r'\w+',p['text'])):
            words.append(dict(text=m[0],normalized=m[0].upper(),char_start=m.start(),char_end=m.end(),
                              start=j*.5,end=j*.5+.4,score=.9))
        records.append({**p,'start':i*10,'alignment':dict(words=words)})
    cues,words=cue_times(plan,records)
    assert [c['words'][0]['text'] for c in cues]==['Alpha','Zeta','Iota']
    assert [c['words'][-1]['text'] for c in cues]==['epsilon','theta','lambda']
    assert all(a['start']<b['start'] for a,b in zip(cues,cues[1:]))


def test_phrase_cues_are_unique_and_control_animation_lead():
    words=[dict(normalized=x,text=x.lower(),start=5+i,end=5+i+.5,score=.9)
           for i,x in enumerate(['APPLY','THE','OPERATOR','THEN','DRAW','THE','RESIDUAL'])]
    assert phrase_time(words,'draw the residual')==(9,.9)
    with pytest.raises(ValueError,match='exactly once'):phrase_time(words,'the')
    beat=dict(start=5,words=words)
    plan=event_plan(beat,14,3,[dict(visual_at=0,phrase='Apply the operator'),
                           dict(visual_at=1.2,phrase='draw the residual')],10)
    assert plan[0]['end']==plan[1]['start']==9
    assert plan[0]['source_seconds']==1.2
    assert plan[1]['frames']==50
    assert event_plan(beat,14,3,[dict(visual_at=0,phrase='draw the residual')],10)[0]['lead']==4


def test_reference_crop_keeps_complete_words_and_their_exact_transcript():
    text='First sentence. Another complete phrase.'
    words=[]
    import re
    for i,m in enumerate(re.finditer(r'\w+',text)):
        words.append(dict(text=m[0],char_start=m.start(),char_end=m.end(),start=i,end=i+.7,score=.9))
    crop=phrase_crop(dict(text=text,words=words,seconds=5),target_seconds=2.5)
    assert crop['text']=='Another complete phrase'
    assert crop['start']<2 and crop['end']>4.7


def write_wave(path,value):
    with wave.open(str(path),'wb') as f:
        f.setparams((1,2,24000,0,'NONE','not compressed'))
        f.writeframes(np.full(2400,value,dtype='<i2').tobytes())


@pytest.mark.skipif(not shutil.which('ffmpeg'),reason='FFmpeg required')
def test_conditioning_content_changes_the_published_voice_identity(tmp_path):
    voice_dir=tmp_path/'voices';voice_dir.mkdir()
    source=tmp_path/'source.wav';write_wave(source,100)
    parts=[dict(audio=source,text='A complete phrase.')]
    first=stage_reference(parts,voice_dir,tmp_path/'cache')
    assert stage_reference(parts,voice_dir,tmp_path/'cache')['voice']==first['voice']
    write_wave(source,200)
    assert stage_reference(parts,voice_dir,tmp_path/'cache')['voice']!=first['voice']
    assert (voice_dir/f'{first["voice"]}.txt').read_text().strip()=='A complete phrase.'


@pytest.mark.skipif(not shutil.which('ffmpeg'),reason='FFmpeg required')
def test_animation_holds_before_the_spoken_cue_and_preserves_its_end(tmp_path):
    source=tmp_path/'visual.mp4'
    subprocess.run(['ffmpeg','-v','error','-y','-f','lavfi','-i','color=red:s=160x90:r=10:d=0.5',
                    '-f','lavfi','-i','color=blue:s=160x90:r=10:d=0.5',
                    '-filter_complex','[0:v][1:v]concat=n=2:v=1:a=0[v]',
                    '-map','[v]','-c:v','libx264','-pix_fmt','yuv420p',str(source)],check=True)
    event=dict(source_start=0,source_seconds=1,play_seconds=1,lead=1,frames=30)
    output=render_piece(source,event,tmp_path/'cache',10)
    assert duration(output)>=2.99
    def rgb(t):
        raw=subprocess.run(['ffmpeg','-v','error','-ss',str(t),'-i',str(output),'-frames:v','1',
                            '-f','rawvideo','-pix_fmt','rgb24','pipe:1'],check=True,capture_output=True).stdout
        return np.frombuffer(raw,dtype=np.uint8).reshape(-1,3).mean(axis=0)
    assert rgb(.8)[0]>200  # red is held before the cue
    assert rgb(1.8)[2]>200 and rgb(2.8)[2]>200  # motion finishes, then blue is held
    stamp=output.stat().st_mtime_ns
    assert render_piece(source,event,tmp_path/'cache',10)==output and output.stat().st_mtime_ns==stamp
