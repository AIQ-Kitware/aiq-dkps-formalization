"""Real small encodes verify content-based reuse and full single-scene updates."""
import importlib
import json
import shutil
import subprocess
import wave

import pytest

from dkvis.presentation import video
from dkvis.presentation.narration import Narration

pytestmark=pytest.mark.skipif(not shutil.which('ffmpeg'),reason='FFmpeg is needed')


def clip(path,color='navy'):
    subprocess.run(['ffmpeg','-v','error','-y','-f','lavfi','-i',f'color=c={color}:s=160x90:r=10:d=1',
                    '-c:v','libx264','-pix_fmt','yuv420p',str(path)],check=True)


def speech(path,sample=0):
    with wave.open(str(path),'wb') as stream:
        stream.setparams((1,2,48000,0,'NONE','not compressed'))
        stream.writeframes(sample.to_bytes(2,'little',signed=True)*24000)


@pytest.fixture
def isolated_timings(tmp_path,monkeypatch):
    monkeypatch.setenv('DKVIS_RENDER_TIMING_LOG',str(tmp_path/'timings.jsonl'))
    monkeypatch.setenv('DKVIS_RENDER_CONTEXT','{}')
    monkeypatch.setenv('DKVIS_RENDER_RUN_ID','incremental-test')
    module=importlib.import_module('dkvis.presentation.timing')
    monkeypatch.setattr(module,'_CURRENT',module.TimingLog())


def test_segment_reuse_depends_on_contents_and_encoding_settings(tmp_path,monkeypatch,isolated_timings):
    visual,audio,output=(tmp_path/name for name in ['visual.mp4','speech.wav','segment.mp4'])
    clip(visual);speech(audio)
    original=subprocess.run;encodes=[]
    def run(command,*args,**kwargs):
        if command[0]=='ffmpeg' and '-c:v' in command:
            encodes.append(command)
        return original(command,*args,**kwargs)
    monkeypatch.setattr(subprocess,'run',run)
    settings=dict(pause=.2,fps=10,preset='ultrafast')
    video.narrated_segment(visual,audio,output,**settings)
    first=output.stat().st_mtime_ns
    video.narrated_segment(visual,audio,output,**settings)
    assert len(encodes)==1 and output.stat().st_mtime_ns==first
    moved=tmp_path/'same-contents.mp4';shutil.copyfile(visual,moved)
    video.narrated_segment(moved,audio,output,**settings)
    assert len(encodes)==1
    speech(audio,100)
    video.narrated_segment(visual,audio,output,**settings)
    assert len(encodes)==2
    settings['pause']=.4
    video.narrated_segment(visual,audio,output,**settings)
    assert len(encodes)==3
    settings['fps']=12
    video.narrated_segment(visual,audio,output,**settings)
    assert len(encodes)==4
    clip(visual,'red');encodes.clear()
    video.narrated_segment(visual,audio,output,**settings)
    assert len(encodes)==1
    output.write_bytes(b'broken cached output')
    video.narrated_segment(visual,audio,output,**settings)
    assert len(encodes)==2


def test_update_one_scene_reassembles_every_chapter(tmp_path,monkeypatch,isolated_timings):
    first,second=tmp_path/'first.mp4',tmp_path/'second.mp4'
    clip(first);clip(second)
    audio=tmp_path/'speech.wav';speech(audio)
    scripts={'PrTitle':Narration('First','','',('First explanation.',)),
             'Pr00Question':Narration('Second','','',('Second explanation.',))}
    monkeypatch.setattr(video,'ROOT',tmp_path)
    monkeypatch.setattr(video,'load_profiles',lambda *a:{})
    monkeypatch.setattr(video,'resolve_profile',lambda *a:dict(profile='qa',endpoint='http://unreachable.invalid',
        model='test-tts',voice='test',narrator_voice='test-speaker',response_format='wav',postprocess={},timeout_seconds=60))
    monkeypatch.setattr(video,'read_deck_narration',lambda *a:scripts)
    monkeypatch.setattr(video,'narrated_builds',lambda scene,folder,script:[
        (first if scene=='PrTitle' else second,script.beats[0])])
    monkeypatch.setattr(video,'synthesize_beat',lambda *a:audio)
    monkeypatch.setattr(video,'export',lambda *a,**kw:None)
    output=tmp_path/'full.mp4'
    arguments=['--deck','prereq-projections','--fps','10','--preset','ultrafast','--output',str(output)]
    video.main([*arguments,'--skip-render'])
    segment=tmp_path/'renders/prereq-projections-narrated/test-speaker-test-tts/PrTitle-beat01.mp4'
    unchanged=segment.stat().st_mtime_ns
    original=subprocess.run;renders=[]
    def run(command,*args,**kwargs):
        if 'dkvis.presentation.build' in command:
            renders.append(command)
            assert command[command.index('--scenes')+1:]==['Pr00Question']
            clip(second,'red')
            return subprocess.CompletedProcess(command,0)
        return original(command,*args,**kwargs)
    monkeypatch.setattr(subprocess,'run',run)
    video.main([*arguments,'--update-scenes','Pr00Question'])
    assert len(renders)==1 and segment.stat().st_mtime_ns==unchanged
    timeline=json.loads((tmp_path/'renders/prereq-projections-narrated/timeline-test-speaker-test-tts.json').read_text())
    assert [entry['scene'] for entry in timeline]==list(scripts)
    assert timeline[1]['start']>0 and timeline[1]['end']>timeline[1]['start']
    metadata=json.loads(output.with_name(output.name+'.metadata.json').read_text())['settings']
    assert not metadata['preview']
    assert metadata['profile']=='test-speaker-test-tts'


def test_voice_overrides_keep_separate_outputs_and_reusable_segments(tmp_path, monkeypatch, isolated_timings):
    visual = tmp_path/'visual.mp4'
    clip(visual)
    sounds = {}
    for speaker, value in [('speaker-a', 0), ('speaker-b', 100)]:
        sounds[speaker] = tmp_path/f'{speaker}.wav'
        speech(sounds[speaker], value)
    # Deliberately omit narrator_voice: even a minimal private profile must
    # identify an explicit API voice in the output and segment directories.
    doc = dict(profiles=dict(breeze=dict(endpoint='http://unreachable.invalid',
        model='test-tts', voice='base', response_format='wav')))
    scripts = {'PrTitle': Narration('Title', '', '', ('Some narration.',))}
    monkeypatch.setattr(video, 'ROOT', tmp_path)
    monkeypatch.setattr(video, 'load_profiles', lambda *a: doc)
    monkeypatch.setattr(video, 'read_deck_narration', lambda *a: scripts)
    monkeypatch.setattr(video, 'narrated_builds', lambda *a: [(visual, 'Some narration.')])
    monkeypatch.setattr(video, 'synthesize_beat', lambda text, label, work, settings: sounds[settings['voice']])
    monkeypatch.setattr(video, 'export', lambda *a, **kw: None)
    arguments = ['--deck', 'prereq-projections', '--tts-profile', 'breeze',
                 '--skip-render', '--fps', '10', '--preset', 'ultrafast']
    work = tmp_path/'renders/prereq-projections-narrated'
    video.main([*arguments, '--voice', 'speaker-a'])
    first = work/'speaker-a-test-tts/PrTitle-beat01.mp4'
    stamp = first.stat().st_mtime_ns
    manifest = first.with_name(first.name+'.segment-cache.json').read_bytes()
    video.main([*arguments, '--voice', 'speaker-b'])
    second = work/'speaker-b-test-tts/PrTitle-beat01.mp4'
    assert first != second and second.is_file()
    assert first.stat().st_mtime_ns == stamp
    assert first.with_name(first.name+'.segment-cache.json').read_bytes() == manifest
    for speaker in sounds:
        output = tmp_path/'renders'/f'{video.lecture_output_name("prereq-projections")}.{speaker}-test-tts.narrated.mp4'
        metadata = json.loads(output.with_name(output.name+'.metadata.json').read_text())['settings']
        assert metadata['voice'] == speaker
        assert metadata['profile'] == f'{speaker}-test-tts'
    video.main([*arguments, '--voice', 'speaker-a'])
    assert first.stat().st_mtime_ns == stamp  # Returning to a voice reuses its segment.
