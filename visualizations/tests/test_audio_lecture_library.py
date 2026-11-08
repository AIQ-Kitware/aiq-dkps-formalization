"""The on-demand speech library uses repo transcripts and cached page audio."""
import json
from pathlib import Path
import shutil
import time

import pytest
from starlette.testclient import TestClient

from dkvis.presentation.audio_library import AudioLectureLibrary, split_pages
from dkvis.presentation.serve import create_app
from dkvis.presentation.paths import ROOT


def test_original_lecture_collection_is_directly_browsable():
    library = AudioLectureLibrary()
    try:
        items = library.catalog()
        assert len(items) == 150
        assert items[0]['id'] == '000000' and items[-1]['id'] == '149000'
        page = library.detail('021000')
        assert page['page_count'] > 5
        assert all(len(p) <= library.page_chars for p in page['pages'])
        assert 'compression' in page['transcript'].lower()
        assert '<!-- END SPOKEN LECTURE -->' not in page['transcript']
        assert 'LEAN CORRESPONDENCE' not in page['transcript'].upper()
    finally:
        library.close()


def test_paginate_preserves_all_words_and_has_no_empty_pages():
    sample = 'First paragraph. Second sentence.\n\n' + ('Long sentence with many words. ' * 45)
    pages = split_pages(sample, max_chars=160)
    assert len(pages) > 2
    assert all(1 <= len(p) <= 160 for p in pages)
    assert ' '.join(' '.join(pages).split()) == ' '.join(sample.split())
    assert split_pages('One small sentence.') == ['One small sentence.']


@pytest.fixture
def audio_site(tmp_path):
    source = tmp_path/'src'
    source.mkdir()
    original = ROOT/'draft-stages'/'tts-lectures'/'extract_narration.py'
    shutil.copyfile(original, source/'extract_narration.py')
    lecture = source/'123000-mock-lecture.md'
    lecture.write_text('# Some mathematical material\n\n<!-- BEGIN SPOKEN LECTURE -->\n\n'
                       + 'We study a linear operator. A second sentence gives more information.\n\n' * 8
                       + '\n<!-- END SPOKEN LECTURE -->\n\n## Display-only correspondence\nNever spoken.\n')
    renders = tmp_path/'renders'; renders.mkdir()
    calls = []

    def fake_speech(text, settings, target):
        calls.append(dict(text=text, settings=settings))
        time.sleep(0.025)
        target.write_bytes(b'ID3' + b'\0' * 4096)

    lib = AudioLectureLibrary(sources=source, cache=tmp_path/'audio-cache',
                              endpoint='http://127.0.0.1:8880/v1/audio/speech',
                              page_chars=250, sender=fake_speech)
    with TestClient(create_app(renders, audio_library=lib)) as client:
        yield client, lecture, lib, calls


def ready(client, page=0, voice='af_heart', speed=1.0):
    url = f'/api/audio-lectures/123000/pages/{page}'
    settings = {'voice': voice, 'speed': speed}
    response = client.post(url+'/render', json=settings)
    assert response.status_code in (200, 202), response.text
    for _ in range(100):
        row = client.get(url, params=settings).json()
        if row['state'] == 'ready':
            return row
        if row['state'] == 'error':
            pytest.fail(row['error'])
        time.sleep(.01)
    pytest.fail('Speech mock did not finish')


def test_catalog_transcript_and_audio_playback(audio_site):
    client, _lecture, _lib, calls = audio_site
    assert client.get('/audio').status_code == 200
    assert 'Cache whole lecture' in client.get('/audio').text
    data = client.get('/api/audio-lectures').json()
    assert [r['id'] for r in data['items']] == ['123000']
    detail = client.get('/api/audio-lectures/123000').json()
    assert detail['title'] == 'Some mathematical material'
    assert detail['page_count'] > 1
    assert 'Never spoken' not in detail['transcript']
    assert client.get('/api/audio-lectures/999999').status_code == 404
    assert client.get('/api/audio-lectures/123000/pages/1000').status_code == 404
    assert client.get('/api/audio-lectures/123000/pages/0/audio').status_code == 404
    row = ready(client)
    assert len(calls) == 1
    audio = client.get(row['url'])
    assert audio.content == b'ID3' + b'\0' * 4096
    assert audio.headers['content-type'].startswith('audio/mpeg')
    piece = client.get(row['url'], headers={'Range':'bytes=0-2'})
    assert piece.status_code == 206 and piece.content == b'ID3'
    ready(client)
    assert len(calls) == 1  # Same page/config is re-used.
    ready(client, voice='af_sky')
    assert len(calls) == 2
    assert len(list(_lib.cache.rglob('*.mp3'))) == 2


def test_audio_cache_is_invalidated_by_transcript_edit(audio_site):
    client, lecture, _lib, calls = audio_site
    original = ready(client)
    lecture.write_text(lecture.read_text().replace('A second sentence', 'Another sentence'))
    changed = ready(client)
    assert changed['key'] != original['key']
    assert len(calls) == 2


def test_render_inputs_are_bounded_and_same_origin(audio_site):
    client, _lecture, _lib, calls = audio_site
    url = '/api/audio-lectures/123000/pages/0/render'
    assert client.post(url, json={'voice':'a/../../etc'}).status_code == 400
    assert client.post(url, json={'speed':99}).status_code == 400
    assert client.post(url, json={'endpoint':'http://evil.test'}).status_code == 400
    assert client.post(url, json={}, headers={'Origin':'https://evil.test'}).status_code == 403
    assert client.post(url, content=b'{' + b' ' * 3000,
                       headers={'Content-Type':'application/json'}).status_code == 413
    assert client.post(url, content=b'{}', headers={'Content-Type':'text/plain'}).status_code == 415
    assert client.post('/api/audio-lectures/123000/pages/-1/render', json={}).status_code == 404
    assert not calls


def test_voice_discovery_always_has_a_default(audio_site, monkeypatch):
    client, _lecture, lib, _calls = audio_site
    monkeypatch.setattr(lib, 'voices', lambda: ['af_heart','am_adam'])
    assert client.get('/api/audio-voices').json()['voices'] == ['af_heart','am_adam']


def test_openai_compatible_kokoro_request(monkeypatch, tmp_path):
    import io
    import urllib.request
    from dkvis.presentation.audio_library import SpeechSettings
    seen = {}

    class FakeResponse(io.BytesIO):
        headers = {'Content-Type': 'audio/mpeg'}

    def fake_open(request, timeout):
        seen.update(json.loads(request.data))
        assert request.full_url == 'http://127.0.0.1:8880/v1/audio/speech'
        assert request.get_method() == 'POST'
        assert 1 <= timeout <= 180
        return FakeResponse(b'ID3' + b'\x00' * 2048)

    monkeypatch.setattr(urllib.request, 'urlopen', fake_open)
    lib = AudioLectureLibrary(cache=tmp_path/'cache', profile='kokoro',
                              endpoint='http://127.0.0.1:8880/v1/audio/speech',
                              response_format='mp3')
    try:
        target = tmp_path/'sample.mp3'
        lib._send_speech('Read this mathematical statement.', SpeechSettings('kokoro', 'af_heart', 1.1), target)
        assert target.read_bytes().startswith(b'ID3')
        assert seen == {'model':'kokoro', 'voice':'af_heart','speed':1.1,
                        'input':'Read this mathematical statement.', 'response_format':'mp3', 'stream':False}
    finally:
        lib.close()


def test_app_lifespan_closes_speech_workers_without_legacy_event_handler(tmp_path, monkeypatch):
    from starlette.applications import Starlette

    # Starlette 1.x removed add_event_handler; startup must not depend on it.
    monkeypatch.delattr(Starlette, 'add_event_handler', raising=False)
    renders = tmp_path / 'renders'
    renders.mkdir()
    library = AudioLectureLibrary(sources=tmp_path / 'empty-lectures', cache=tmp_path / 'cache')
    closed = []
    original_close = library.close

    def close_once():
        closed.append(True)
        original_close()

    monkeypatch.setattr(library, 'close', close_once)
    try:
        app = create_app(renders, audio_library=library)
        with TestClient(app) as client:
            assert client.get('/audio').status_code == 200
            assert closed == []
        assert closed == [True]
    finally:
        original_close()


def test_default_audio_reader_uses_crall_profile_and_ignores_kokoro_env(monkeypatch, tmp_path):
    monkeypatch.setenv('DKVIS_TTS_PROFILE', 'crall-math-dk-v2-breeze-tts2')
    monkeypatch.setenv('KOKORO_TTS_ENDPOINT', 'http://192.168.222.38:8880/v1/audio/speech')
    monkeypatch.setenv('CRALL_TTS_ENDPOINT', '')
    library = AudioLectureLibrary(cache=tmp_path/'cache')
    try:
        assert library.profile == 'crall-math-dk-v2-breeze-tts2'
        assert library.endpoint == 'http://127.0.0.1:8821/v1/audio/speech'
        assert library.model == 'breeze-tts2'
        assert library.default_voice == 'crall-math-dk-v2'
        assert library.response_format == 'wav'
        assert library.page_chars == 420
    finally:
        library.close()


def test_breeze_payload_converts_wav_to_mp3(tmp_path, monkeypatch):
    import io
    import urllib.request
    import wave
    from dkvis.presentation.audio_library import SpeechSettings

    audio = io.BytesIO()
    with wave.open(audio, 'wb') as output:
        output.setnchannels(1)
        output.setsampwidth(2)
        output.setframerate(24000)
        output.writeframes(b'\x00\x00' * 4800)
    observed = []

    class FakeResponse(io.BytesIO):
        headers = {'Content-Type': 'audio/wav'}

    def fake_open(request, timeout):
        observed.append(json.loads(request.data))
        return FakeResponse(audio.getvalue())

    monkeypatch.setattr(urllib.request, 'urlopen', fake_open)
    library = AudioLectureLibrary(cache=tmp_path/'cache')
    try:
        destination = tmp_path/'lecture.mp3'
        library._send_speech('A projection is self adjoint.',
                             SpeechSettings(library.model, library.default_voice, 1.25), destination)
        assert destination.read_bytes()[:3] == b'ID3'
        assert observed[0]['response_format'] == 'wav'
        assert observed[0]['model'] == 'breeze-tts2'
        assert observed[0]['voice'] == 'crall-math-dk-v2'
        assert observed[0]['cfg_scale'] == 2.0
        assert 'instruction' in observed[0]
        assert 'speed' not in observed[0]
        assert 'stream' not in observed[0]
        assert not list(tmp_path.glob('*.source.*'))
    finally:
        library.close()


def test_audio_health_endpoint_and_selected_profile(audio_site, monkeypatch):
    client, _lecture, library, _calls = audio_site
    monkeypatch.setattr(library, 'connection_status', lambda: dict(
        state='reachable', profile=library.profile, model=library.model,
        voice=library.default_voice, upstream='127.0.0.1:8821'))
    health = client.get('/api/audio-health').json()
    assert health['state'] == 'reachable'
    assert health['profile'] == 'crall-math-dk-v2-breeze-tts2'
    assert client.get('/api/audio-lectures').json()['profile'] == health['profile']


def test_server_defaults_bind_lan_and_nonconflicting_port(monkeypatch):
    from dkvis.presentation import serve
    seen = {}

    def fake_uvicorn_run(app, host, port):
        seen.update(host=host, port=port)

    import uvicorn
    monkeypatch.setattr(uvicorn, 'run', fake_uvicorn_run)
    serve.main([])
    assert seen == dict(host='0.0.0.0', port=8001)


def test_reader_defaults_to_kokoro_independent_of_production_profile(tmp_path, monkeypatch):
    from dkvis.presentation.audio_library import AudioLectureHub
    monkeypatch.setenv('DKVIS_TTS_PROFILE', 'crall-math-dk-v2-breeze-tts2')
    monkeypatch.setenv('MATCHING_TTS_PROFILE', 'crall-math-dk-v2-breeze-tts2')
    monkeypatch.delenv('DKVIS_AUDIO_TTS_PROFILE', raising=False)
    monkeypatch.setenv('KOKORO_TTS_ENDPOINT', 'http://192.168.222.38:8880/v1/audio/speech')
    hub = AudioLectureHub(cache=tmp_path/'cache')
    try:
        assert hub.profile == 'kokoro'
        assert hub.engine('kokoro').model == 'kokoro'
        assert hub.engine('kokoro').endpoint == 'http://192.168.222.38:8880/v1/audio/speech'
        assert hub.engine('kokoro').default_voice == 'af_heart'
        crall = hub.engine('crall-math-dk-v2-breeze-tts2')
        assert crall.model == 'breeze-tts2'
        assert crall.default_voice == 'crall-math-dk-v2'
        assert crall.endpoint.endswith(':8821/v1/audio/speech')
        assert hub.profiles()[0]['id'] == 'kokoro'
    finally:
        hub.close()


def test_profile_selection_voice_registration_and_cache_isolation(tmp_path, monkeypatch):
    from dkvis.presentation.audio_library import AudioLectureHub
    from dkvis.presentation.audio_library import AudioLectureLibrary
    monkeypatch.delenv('DKVIS_AUDIO_TTS_PROFILE', raising=False)
    monkeypatch.setenv('KOKORO_TTS_ENDPOINT', 'http://127.0.0.1:8880/v1/audio/speech')
    monkeypatch.setenv('CRALL_TTS_ENDPOINT', '')
    source = tmp_path/'lectures';source.mkdir()
    shutil.copyfile(ROOT/'draft-stages'/'tts-lectures'/'extract_narration.py',
                    source/'extract_narration.py')
    (source/'123000-test-lecture.md').write_text(
        '# Test lecture\n\n<!-- BEGIN SPOKEN LECTURE -->\n\n'
        + ('A short sentence. Another sentence about the operator.\n\n' * 8)
        + '<!-- END SPOKEN LECTURE -->\n', encoding='utf-8')
    renders=tmp_path/'renders';renders.mkdir()
    calls=[]

    def fake_send(text, settings, target):
        calls.append((settings.model, settings.voice, text))
        target.write_bytes(b'ID3'+b'\0'*4096)

    monkeypatch.setattr(AudioLectureLibrary, 'voices', lambda self: [self.default_voice])
    monkeypatch.setattr(AudioLectureLibrary, 'connection_status', lambda self: dict(
        state='reachable', profile=self.profile, upstream='mock:1234',
        voice=self.default_voice, model=self.model))
    hub = AudioLectureHub(sources=source, cache=tmp_path/'cache', sender=fake_send,
                          page_chars=250)
    with TestClient(create_app(renders, audio_library=hub)) as client:
        response=client.get('/api/audio-profiles')
        assert response.status_code == 200
        assert response.json()['default_profile']=='kokoro'
        profiles = {row['id'] for row in response.json()['profiles']}
        assert {'kokoro', 'crall-math-dk-v2-breeze-tts2'} <= profiles
        assert client.get('/api/audio-voices',params={'profile':'kokoro'}).json()['default_voice']=='af_heart'
        assert client.get('/api/audio-voices',params={'profile':'crall-math-dk-v2-breeze-tts2'}).json()['default_voice']=='crall-math-dk-v2'
        assert client.get('/api/audio-voices',params={'profile':'not-real'}).status_code==400
        assert client.get('/api/audio-health',params={'profile':'not-real'}).status_code==400
        assert client.post('/api/audio-voices/register',json={
            'profile':'kokoro','voice':'am_custom.1','label':'Math reader'}).status_code==201
        voice_payload=client.get('/api/audio-voices',params={'profile':'kokoro'}).json()
        assert 'am_custom.1' in voice_payload['voices']
        assert {'profile':'kokoro','voice':'am_custom.1','label':'Math reader'} in voice_payload['registered']
        assert 'am_custom.1' not in client.get('/api/audio-voices',params={
            'profile':'crall-math-dk-v2-breeze-tts2'}).json()['voices']
        assert client.post('/api/audio-voices/register',json={
            'profile':'bogus','voice':'valid'}).status_code==400
        assert client.post('/api/audio-voices/register',json={
            'profile':'kokoro','voice':'../oops'}).status_code==400
        assert client.post('/api/audio-voices/register',json={
            'profile':'kokoro','voice':'a','url':'http://malicious'}).status_code==400
        assert client.post('/api/audio-voices/register',json={
            'profile':'kokoro','voice':'x'},headers={'Origin':'https://other.example'}).status_code==403
        for profile, model, voice in [('kokoro','kokoro','am_custom.1'),
                                      ('crall-math-dk-v2-breeze-tts2','breeze-tts2','crall-math-dk-v2')]:
            url='/api/audio-lectures/123000/pages/0'
            config=dict(profile=profile,voice=voice,speed=1.0)
            response=client.post(url+'/render',json=config)
            assert response.status_code in (200,202),response.text
            for attempt in range(120):
                result=client.get(url,params=config).json()
                if result['state']=='ready':break
                if result['state']=='error':pytest.fail(result['error'])
                time.sleep(.01)
            else:pytest.fail('Page did not render')
            assert 'profile='+profile in result['url']
            assert client.get(result['url']).content.startswith(b'ID3')
            assert (model, voice) in [(item[0],item[1]) for item in calls]
        assert len(calls)==2
        assert len(list((tmp_path/'cache').rglob('*.mp3')))==2
    assert json.loads((tmp_path/'cache'/'registered-voices.json').read_text())['voices']==[
        {'profile':'kokoro','voice':'am_custom.1','label':'Math reader'}]


def test_audio_reader_includes_synchronized_text_controls():
    from dkvis.presentation.audio_library import AUDIO_PAGE
    html=AUDIO_PAGE.read_text(encoding='utf-8')
    for required in ['id="liveText"', 'id="readingPosition"', 'id="followText"',
                     'function speechSegments(', 'function updateTranscriptFocus(',
                     "audio.addEventListener('timeupdate',updateTranscriptFocus)",
                     'id="registerVoice"', 'id="profile"']:
        assert required in html
