"""Reference identities and generation records survive cached speech reuse."""
import io
import json
import importlib
import urllib.error

from dkvis.presentation import audio
from dkvis.presentation.tts import resolve_profile,narrator_id,server_runtime


def test_reference_snapshot_and_voice_override(tmp_path,monkeypatch):
    reference=dict(source='local-ai/services/tts/voice-references',audio='crall-math-dk-v2.wav',transcript='crall-math-dk-v2.txt')
    (tmp_path/reference['audio']).write_bytes(b'sample recording')
    (tmp_path/reference['transcript']).write_text('The words spoken in the reference recording.')
    monkeypatch.setenv('DKVIS_TTS_REFERENCE_DIR',str(tmp_path))
    name='crall-math-dk-v2-breeze-tts2'
    doc=dict(profiles={name:dict(endpoint='http://localhost',model='breeze-tts2',
        voice='crall-math-dk-v2',narrator_voice='crall-math-dk-v2',response_format='wav',reference=reference)})
    settings=resolve_profile(doc,name)
    assert narrator_id(settings)==name
    captured=settings['reference']
    assert captured['audio']['basename']=='crall-math-dk-v2.wav'
    assert captured['audio']['bytes']==len(b'sample recording')
    assert captured['transcript']['text']=='The words spoken in the reference recording.'
    assert captured['audio']['modified_at']
    assert str(tmp_path) not in json.dumps(captured)
    assert 'reference' not in resolve_profile(doc,name,dict(voice='another-reference'))
    assert reference['audio']=='crall-math-dk-v2.wav'  # never mutate the profile document


def test_speech_cache_retains_its_original_generation_context(tmp_path,monkeypatch):
    monkeypatch.setenv('DKVIS_RENDER_TIMING_LOG',str(tmp_path/'timings.jsonl'))
    monkeypatch.setenv('DKVIS_RENDER_CONTEXT','{}')
    module=importlib.import_module('dkvis.presentation.timing')
    monkeypatch.setattr(module,'_CURRENT',module.TimingLog())
    monkeypatch.setattr(audio,'duration',lambda path:.5)
    requests=[]
    def request(req,**kwargs):
        requests.append(json.loads(req.data))
        response=io.BytesIO(b'synthesized audio')
        response.headers={'Content-Type':'audio/wav'}
        return response
    monkeypatch.setattr(audio.urllib.request,'urlopen',request)
    common=dict(endpoint='http://private-server.invalid/v1/audio/speech',model='breeze-tts2',
                voice='crall-math-dk-v2',language=None,timeout=2,profile='crall-math-dk-v2-breeze-tts2',
                request_settings=dict(instruction='Steady lecture delivery.',cfg_scale=2),
                server_runtime=dict(status='reported',details=dict(model_revision='revision-one')))
    first=dict(audio=dict(basename='crall-math-dk-v2.wav',bytes=100),transcript=dict(basename='crall-math-dk-v2.txt',text='Reference words.'))
    path=audio.speech('Some lecture words.',tmp_path/'clip',reference=first,**common)
    original=json.loads(path.with_suffix('.json').read_text())
    assert original['reference']==first and original['generated_at']
    assert original['request_settings']==common['request_settings']
    assert original['server_runtime']==common['server_runtime']
    assert 'private-server' not in json.dumps(original)
    changed={**first,'audio':dict(basename='crall-math-dk-v2.wav',bytes=200)}
    assert audio.speech('Some lecture words.',tmp_path/'clip',reference=changed,**common)==path
    assert len(requests)==1 and json.loads(path.with_suffix('.json').read_text())==original
    audio.speech('Some lecture words.',tmp_path/'clip',reference=changed,force=True,**common)
    assert len(requests)==2 and json.loads(path.with_suffix('.json').read_text())['reference']==changed
    other=audio.speech('Some lecture words.',tmp_path/'clip',reference=None,
                       **{**common,'voice':'crall-math-dk-v3'})
    assert other!=path and len(requests)==3
    assert requests[0]['voice']=='crall-math-dk-v2'
    assert 'reference' not in requests[0]  # metadata is not an unsupported API request field


def test_runtime_metadata_is_optional_and_filters_host_details(monkeypatch):
    import dkvis.presentation.tts as tts
    urls=[]
    def request(url,**kwargs):
        urls.append(url)
        return io.BytesIO(json.dumps(dict(backend='breeze-tts2',model_revision='revision',
            effective_dtype='bfloat16',reference_wav='/private/default-voice.wav',api_key='secret')).encode())
    monkeypatch.setattr(tts.urllib.request,'urlopen',request)
    snapshot=server_runtime('http://localhost/prefix/v1/audio/speech')
    assert urls==['http://localhost/prefix/v1/runtime']
    assert snapshot['details']==dict(backend='breeze-tts2',model_revision='revision',effective_dtype='bfloat16')
    def unavailable(*args,**kwargs):
        raise urllib.error.URLError('connection to a private address failed')
    monkeypatch.setattr(tts.urllib.request,'urlopen',unavailable)
    snapshot=server_runtime('http://localhost/v1/audio/speech')
    assert snapshot['status']=='unavailable' and snapshot['reason']=='URLError'
    assert snapshot['observed_at']
