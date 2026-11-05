"""A small real encode verifies text/provenance snapshots without calling TTS."""
import json
import importlib
import shutil
import subprocess
import wave

import pytest

from dkvis.presentation import video
from dkvis.presentation.narration import Narration
from dkvis.presentation.captions import transcript_rows


@pytest.mark.skipif(not shutil.which('ffmpeg'),reason='FFmpeg is needed for video export')
def test_generated_video_retains_speech_and_model_provenance(tmp_path,monkeypatch):
    visual=tmp_path/'visual.mp4'
    subprocess.run(['ffmpeg','-v','error','-y','-f','lavfi','-i','color=c=navy:s=160x90:r=10:d=1',
                    '-c:v','libx264','-pix_fmt','yuv420p',str(visual)],check=True)
    audio=tmp_path/'speech.wav'
    with wave.open(str(audio),'wb') as stream:
        stream.setparams((1,2,48000,0,'NONE','not compressed'))
        stream.writeframes(b'\0\0'*24000)
    speech='An eigenvalue and an eigenspace are different objects.'
    settings=dict(profile='qa',endpoint='http://unreachable.invalid',model='test-tts',
                  voice='test-voice',response_format='wav',postprocess={},timeout_seconds=60)
    monkeypatch.setattr(video,'ROOT',tmp_path)
    monkeypatch.setattr(video,'load_profiles',lambda *a:{})
    monkeypatch.setattr(video,'resolve_profile',lambda *a:settings)
    monkeypatch.setattr(video,'read_deck_narration',lambda *a:{'PrTitle':Narration('Title','','',(speech,))})
    monkeypatch.setattr(video,'narrated_builds',lambda *a:[(visual,speech)])
    monkeypatch.setattr(video,'synthesize_beat',lambda *a:audio)
    monkeypatch.setattr(video,'export',lambda *a,**kw:None)
    monkeypatch.setenv('DKVIS_RENDER_TIMING_LOG',str(tmp_path/'timings.jsonl'))
    monkeypatch.setenv('DKVIS_RENDER_CONTEXT','{}')
    monkeypatch.setenv('DKVIS_RENDER_RUN_ID','library-test')
    timing_module=importlib.import_module('dkvis.presentation.timing')
    monkeypatch.setattr(timing_module,'_CURRENT',timing_module.TimingLog())
    output=tmp_path/'lecture.qa.narrated.mp4'
    video.main(['--deck','prereq-projections','--skip-render','--fps','10',
                '--preset','ultrafast','--output',str(output)])
    timeline=json.loads((tmp_path/'renders/prereq-projections-narrated/timeline-qa.json').read_text())
    assert timeline[0]['builds'][0]['text']==speech
    assert timeline[0]['builds'][0]['speech_seconds']==pytest.approx(.5)
    assert timeline[0]['builds'][0]['speech_parts'][0]['text']==speech
    metadata=json.loads(output.with_name(output.name+'.metadata.json').read_text())
    assert metadata['settings']['model']=='test-tts'
    assert metadata['settings']['voice']=='test-voice'
    assert metadata['generated_at'] and metadata['provenance']['transcript']
    assert 'endpoint' not in metadata['settings']
    audio.unlink()
    recovered=transcript_rows(tmp_path,timeline)
    assert recovered[0]['text']==speech
    assert recovered[0]['speech_end']==pytest.approx(.5)
