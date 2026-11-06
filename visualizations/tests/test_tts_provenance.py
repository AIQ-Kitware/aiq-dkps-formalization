"""Reference identities and generation records survive cached speech reuse."""
import io
import json
import importlib
import shutil
import urllib.error
import pytest

from dkvis.presentation import audio
from dkvis.presentation.tts import resolve_profile,narrator_id,server_runtime


def test_runtime_overrides_merge_without_changing_the_base_profile():
    doc = dict(postprocess=dict(enabled=True), profiles=dict(breeze=dict(
        endpoint='http://localhost', model='breeze-tts2', voice='ryan',
        narrator_voice='ryan', response_format='wav',
        request=dict(instruction='Base delivery.', cfg_scale=2),
        postprocess=dict(target_lufs=-20, ratio=3))))
    settings = resolve_profile(doc, 'breeze', dict(voice='private-voice',
        request=dict(instruction='Steady delivery.', speed=1.1),
        postprocess=dict(ratio=2), max_words=100))
    assert settings['request'] == dict(instruction='Steady delivery.', cfg_scale=2, speed=1.1)
    assert settings['postprocess']['target_lufs'] == -20
    assert settings['postprocess']['ratio'] == 2
    assert settings['max_words'] == 100
    assert narrator_id(settings) == 'private-voice-breeze-tts2'
    assert doc['profiles']['breeze']['request']['instruction'] == 'Base delivery.'
    for key in ['input', 'model', 'voice', 'response_format']:
        with pytest.raises(ValueError, match='request settings may not replace'):
            resolve_profile(doc, 'breeze', dict(request={key: 'invalid'}))


def test_video_cli_overrides_reach_effective_settings_before_rendering(monkeypatch):
    from dkvis.presentation import video
    doc = dict(profiles=dict(breeze=dict(endpoint='http://localhost',
        model='breeze-tts2', voice='ryan', narrator_voice='ryan', response_format='wav',
        request=dict(instruction='Base delivery.', cfg_scale=2))))
    monkeypatch.setattr(video, 'load_profiles', lambda path: doc)
    captured = {}
    def resolve(*args):
        captured.update(resolve_profile(*args))
        return captured
    monkeypatch.setattr(video, 'resolve_profile', resolve)
    class BeforeRendering(Exception):
        pass
    def stop(deck):
        raise BeforeRendering()
    monkeypatch.setattr(video, 'read_deck_narration', stop)
    with pytest.raises(BeforeRendering):
        video.main(['--deck', 'operators-rayleigh-ritz', '--tts-profile', 'breeze',
            '--tts-settings-json', json.dumps(dict(voice='old-voice', max_words=100,
                request=dict(speed=1.1, cfg_scale=3))),
            '--voice', 'private-voice', '--endpoint', 'http://private.invalid/v1/audio/speech',
            '--request-json', json.dumps(dict(cfg_scale=2.5, instruction='JSON delivery.')),
            '--instruction', "Don't shout at the start.", '--language', 'English'])
    assert captured['voice'] == 'private-voice'
    assert captured['endpoint'] == 'http://private.invalid/v1/audio/speech'
    assert captured['max_words'] == 100
    assert captured['request'] == dict(speed=1.1, cfg_scale=2.5,
        instruction="Don't shout at the start.", language='English')
    assert narrator_id(captured) == 'private-voice-breeze-tts2'


@pytest.mark.parametrize('flag', ['--request-json', '--tts-settings-json'])
def test_video_cli_rejects_nonobject_json_before_rendering(flag, monkeypatch):
    from dkvis.presentation import video
    monkeypatch.setattr(video, 'load_profiles', lambda path: {})
    with pytest.raises(SystemExit) as error:
        video.main(['--deck', 'operators-rayleigh-ritz', flag, '[]'])
    assert error.value.code == 2


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


@pytest.mark.parametrize('voice', ['default', 'custom'])
def test_explicit_voice_names_outputs_even_without_a_profile_narrator_label(voice):
    doc = dict(profiles=dict(breeze=dict(endpoint='http://localhost',
        model='breeze-tts2', voice='default', response_format='wav')))
    settings = resolve_profile(doc, 'breeze', dict(voice=voice))
    assert settings['voice'] == voice
    assert narrator_id(settings) == f'{voice}-breeze-tts2'


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
    assert requests[-1]['voice']=='crall-math-dk-v3'
    assert audio.speech('Some lecture words.',tmp_path/'clip',reference=changed,**common)==path
    assert len(requests)==3  # Switching back reuses the original voice's cache.
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


def test_incomplete_cached_passage_is_retried_without_changing_its_request(tmp_path, monkeypatch):
    from dkvis.presentation.audio import synthesize_beat
    monkeypatch.setenv('DKVIS_RENDER_TIMING_LOG', str(tmp_path/'timings.jsonl'))
    module=importlib.import_module('dkvis.presentation.timing')
    monkeypatch.setattr(module, '_CURRENT', module.TimingLog())
    # Only duration is faked; exercise actual request/cache/archive/retry behavior.
    monkeypatch.setattr(audio, 'duration', lambda path: float(path.read_bytes()))
    replies=iter([b'0.96', b'24.0']); requests=[]
    def request(req, **kwargs):
        requests.append(json.loads(req.data))
        response=io.BytesIO(next(replies)); response.headers={'Content-Type':'audio/wav'}
        return response
    monkeypatch.setattr(audio.urllib.request, 'urlopen', request)
    text=' '.join(['trial']*60)
    settings=dict(profile='demo', endpoint='http://test.invalid/speech', model='demo',
                  voice='demo', response_format='wav', max_chars=1000, max_words=100)
    stem=tmp_path/'audio/demo/Lecture-beat01'
    path=audio.speech(text, stem, endpoint=settings['endpoint'], model='demo', voice='demo',
                      language=None, timeout=2, max_speech_words_per_second=0)
    repaired=synthesize_beat(text, 'Lecture-beat01', tmp_path, settings)
    assert repaired==path and repaired.read_bytes()==b'24.0'
    assert requests[0]==requests[1] and len(requests)==2
    assert path.with_name(path.stem+'.too-short.wav').read_bytes()==b'0.96'
    assert synthesize_beat(text, 'Lecture-beat01', tmp_path, settings)==path
    assert len(requests)==2  # The valid replacement is reused normally.


def test_repeated_short_responses_fail_without_publishing_an_accepted_clip(tmp_path, monkeypatch):
    from dkvis.presentation.audio import synthesize_beat, AudioTooShortError, check_audio_minimum
    monkeypatch.setenv('DKVIS_RENDER_TIMING_LOG', str(tmp_path/'timings.jsonl'))
    module=importlib.import_module('dkvis.presentation.timing')
    monkeypatch.setattr(module, '_CURRENT', module.TimingLog())
    monkeypatch.setattr(audio, 'duration', lambda path: .96)
    requests=[]
    def request(req, **kwargs):
        requests.append(req)
        response=io.BytesIO(b'incomplete response'); response.headers={'Content-Type':'audio/wav'}
        return response
    monkeypatch.setattr(audio.urllib.request, 'urlopen', request)
    with pytest.raises(AudioTooShortError, match='60 words'):
        synthesize_beat(' '.join(['trial']*60), 'Lecture-beat01', tmp_path,
                        dict(profile='demo', endpoint='http://test.invalid/speech', model='demo',
                             voice='demo', response_format='wav', max_chars=1000, max_words=100))
    assert len(requests)==2
    assert len(list((tmp_path/'audio/demo').glob('*.too-short-*.wav')))==2
    assert not [p for p in (tmp_path/'audio/demo').glob('*.wav') if '.too-short-' not in p.name]
    check_audio_minimum('Brief title.', .3)
    check_audio_minimum(' '.join(['trial']*60), 12)


@pytest.mark.skipif(not shutil.which('ffmpeg'), reason='FFmpeg required')
def test_join_is_invalidated_when_a_regenerated_part_changes_in_place(tmp_path, monkeypatch):
    import wave
    from dkvis.presentation.audio import synthesize_beat
    from dkvis.presentation.media import duration
    monkeypatch.setenv('DKVIS_RENDER_TIMING_LOG', str(tmp_path/'timings.jsonl'))
    module=importlib.import_module('dkvis.presentation.timing')
    monkeypatch.setattr(module, '_CURRENT', module.TimingLog())
    one=tmp_path/'one.wav'; two=tmp_path/'two.wav'
    def write(path, seconds):
        with wave.open(str(path), 'wb') as stream:
            stream.setparams((1, 2, 24000, 0, 'NONE', 'not compressed'))
            stream.writeframes(b'\0\0'*round(seconds*24000))
    write(one, .2);write(two, .2)
    (tmp_path/'audio/demo').mkdir(parents=True)
    monkeypatch.setattr(audio, 'speech', lambda text, *args, **kwargs: one if text.startswith('Alpha') else two)
    settings=dict(profile='demo', endpoint='http://test.invalid/speech', model='demo',
                  voice='demo', response_format='wav', max_chars=80, max_words=65)
    text=' '.join(['Alpha']*10)+'. '+' '.join(['Beta']*10)+'.'
    first=synthesize_beat(text, 'Lecture-beat01', tmp_path, settings)
    assert duration(first)==pytest.approx(.52, abs=.002)
    write(one, .4)
    second=synthesize_beat(text, 'Lecture-beat01', tmp_path, settings)
    assert first!=second and duration(second)==pytest.approx(.72, abs=.002)
    assert synthesize_beat(text, 'Lecture-beat01', tmp_path, settings)==second
