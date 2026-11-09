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


@pytest.fixture(autouse=True)
def _local_tts_overlay_disabled(tmp_path, monkeypatch):
    """Keep these tests deterministic even when this machine has a personal
    tts.local.toml (which is gitignored and never present in a fresh clone)."""
    from dkvis.presentation import tts
    monkeypatch.setattr(tts, 'LOCAL_CONFIG', tmp_path / 'absent-local-tts.toml')
    for setting in ('DKVIS_AUDIO_SEGMENT_WORDS', 'DKVIS_AUDIO_SEGMENT_CHARS',
                    'DKVIS_AUDIO_SEGMENT_SECONDS'):
        monkeypatch.delenv(setting, raising=False)


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


def test_shorter_default_pages_and_environment_override(monkeypatch, tmp_path):
    monkeypatch.delenv('DKVIS_AUDIO_PAGE_CHARS', raising=False)
    library = AudioLectureLibrary(cache=tmp_path / 'default-cache')
    try:
        assert library.page_chars == 600
        doc = library.detail('000000')
        assert all(0 < len(page) <= 600 for page in doc['pages'])
        assert ' '.join(' '.join(doc['pages']).split()) == ' '.join(doc['transcript'].split())
        # The new default still makes fewer breaks than the original 420-character setting.
        assert len(doc['pages']) < len(split_pages(doc['transcript'], max_chars=420))
    finally:
        library.close()

    monkeypatch.setenv('DKVIS_AUDIO_PAGE_CHARS', '900')
    overridden = AudioLectureLibrary(cache=tmp_path / 'override-cache')
    try:
        assert overridden.page_chars == 900
        assert all(len(page) <= 900 for page in overridden.detail('000000')['pages'])
    finally:
        overridden.close()


def test_cache_identity_includes_page_size_and_page_address(audio_site):
    """Audio from an old pagination layout must not be treated as current."""
    _client, _lecture, lib, _calls = audio_site
    settings = lib.settings(voice='af_alloy')
    original_path, original_text, original_key = lib._target('123000', 0, settings)
    assert lib.detail('123000')['page_chars'] == 250
    assert lib.catalog()[0]['page_chars'] == 250
    lib.page_chars = 260
    changed_path, changed_text, changed_key = lib._target('123000', 0, settings)
    assert original_text == changed_text  # text hashes alone cannot detect this
    assert changed_key != original_key
    assert changed_path != original_path
    assert lib.detail('123000')['page_chars'] == 260
    second_path, second_text, second_key = lib._target('123000', 1, settings)
    assert second_text == changed_text  # repeated pages have distinct cache jobs
    assert second_key != changed_key
    assert second_path != changed_path
    lib.page_chars = 250
    _, restored_text, restored_key = lib._target('123000', 0, settings)
    assert restored_text == original_text
    assert restored_key == original_key


def test_versioned_browser_audio_urls_prevent_stale_cached_mp3(audio_site):
    client, _lecture, lib, calls = audio_site
    before = ready(client, voice='af_alloy')
    assert 'key=' + before['key'] in before['url']
    first = client.get(before['url'])
    assert first.status_code == 200
    assert 'immutable' in first.headers['cache-control']
    assert len(calls) == 1
    immediate = client.post('/api/audio-lectures/123000/pages/0/render',
                            json={'voice': 'af_alloy', 'speed': 1})
    assert immediate.status_code == 200
    assert immediate.json()['url'] == before['url']

    # Even if page zero has identical text, the public audio URL must change
    # because its page length is a distinct input to the cached artifact.
    lib.page_chars = 260
    after = ready(client, voice='af_alloy')
    assert before['key'] != after['key']
    assert before['url'] != after['url']
    assert 'key=' + after['key'] in after['url']
    assert client.get(before['url']).status_code == 404
    assert client.get(after['url']).status_code == 200
    assert len(calls) == 2

    # Older clients may still request unkeyed URLs. Keep them functional,
    # but never mark their responses immutable.
    unkeyed = after['url'].split('&key=')[0]
    legacy = client.get(unkeyed)
    assert legacy.status_code == 200
    assert 'no-store' in legacy.headers['cache-control']


def test_audio_health_exposes_effective_synthesis_limits(audio_site):
    client, _lecture, lib, _calls = audio_site
    result = client.get('/api/audio-health').json()
    assert result['page_chars'] == lib.page_chars == 250
    assert result['speech_max_chars'] == lib.speech_max_chars
    assert result['speech_max_words'] == lib.speech_max_words
    assert result['speech_max_seconds'] == lib.max_audio_seconds
    assert result['model'] == lib.model
    assert result['profile'] == lib.profile


def test_changing_page_size_does_not_serve_previous_cached_audio(audio_site):
    client, _lecture, lib, calls = audio_site
    before = ready(client, voice='af_alloy')
    original_text = lib.detail('123000')['pages'][0]
    assert len(calls) == 1
    lib.page_chars = 260
    assert lib.detail('123000')['pages'][0] == original_text
    status = client.get('/api/audio-lectures/123000/pages/0',
                        params={'voice': 'af_alloy', 'speed': 1}).json()
    assert status['state'] == 'missing'
    assert status['key'] != before['key']
    after = ready(client, voice='af_alloy')
    assert after['state'] == 'ready'
    assert after['key'] != before['key']
    assert len(calls) == 2


def test_paginate_preserves_all_words_and_has_no_empty_pages():
    sample = 'First paragraph. Second sentence.\n\n' + ('Long sentence with many words. ' * 45)
    pages = split_pages(sample, max_chars=160)
    assert len(pages) > 2
    assert all(1 <= len(p) <= 160 for p in pages)
    assert ' '.join(' '.join(pages).split()) == ' '.join(sample.split())
    assert split_pages('One small sentence.') == ['One small sentence.']


def test_sentence_aware_pagination_does_not_split_fitting_sentences():
    one = 'The spectrum has two separated clusters, each with a stable projection.'
    two = 'A perturbation changes the eigenvectors but can preserve a useful spectral gap.'
    three = 'This is the third sentence, whose entire argument belongs together.'
    text = f'{one} {two} {three}'
    # Combining the first two exceeds the limit. Each individual sentence fits,
    # and the paginator must move the whole sentence to the next page.
    pages = split_pages(text, max_chars=115)
    assert pages == [one, two, three]
    assert all(sum(sentence in page for page in pages) == 1
               for sentence in (one, two, three))
    assert ' '.join(' '.join(pages).split()) == text


def test_sentence_boundaries_with_quotes_lowercase_and_abbreviations():
    quoted = 'The proof says \"the projection is stable.\" next we inspect the residual.'
    # The next spoken phrase can begin in lowercase after a quoted sentence.
    pages = split_pages(quoted + ' A final observation is included.', max_chars=100)
    assert 'stable.\"' in pages[0]
    assert ' '.join(' '.join(pages).split()) == ' '.join((quoted+' A final observation is included.').split())
    abbrev = 'Dr. Smith refers to Fig. Three in the explanation. The concluding point is precise.'
    pages = split_pages(abbrev, max_chars=100)
    assert ' '.join(' '.join(pages).split()) == abbrev


def test_oversized_sentence_splits_only_when_necessary():
    first = 'This is a complete short sentence.'
    long = 'A genuinely long proof sentence ' + ('with several important hypotheses ' * 10).strip() + '.'
    pages = split_pages(first + ' ' + long, max_chars=110)
    assert pages[0] == first
    assert all(0 < len(page) <= 110 for page in pages)
    assert ' '.join(' '.join(pages).split()) == first + ' ' + long


def test_pagination_algorithm_change_invalidates_cached_audio(audio_site):
    import dkvis.presentation.audio_library as reader
    _client, _lecture, library, _calls = audio_site
    original = library._target('123000', 0, library.settings())[2]
    with pytest.MonkeyPatch.context() as patches:
        patches.setattr(reader, 'PAGINATION_VERSION', 'sentence-aware-v3')
        revised = library._target('123000', 0, library.settings())[2]
        assert revised != original
        assert library.detail('123000')['pagination_version'] == 'sentence-aware-v3'


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


def test_plain_text_transcript_returns_only_spoken_narration(audio_site):
    client, _lecture, _lib, _calls = audio_site
    result = client.get('/api/audio-lectures/123000/transcript.txt')
    assert result.status_code == 200
    assert result.headers['content-type'].startswith('text/plain')
    assert result.headers['x-content-type-options'] == 'nosniff'
    spoken = client.get('/api/audio-lectures/123000').json()['transcript']
    assert result.text == spoken
    assert 'Never spoken' not in result.text
    assert 'Speech page' not in result.text
    assert '<!-- BEGIN SPOKEN LECTURE -->' not in result.text
    assert client.get('/api/audio-lectures/999999/transcript.txt').status_code == 404
    assert client.get('/api/audio-lectures/123000/transcript.txt?track=g3').status_code == 400
    assert 'Plain text / copy all' in client.get('/audio').text


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
        assert library.page_chars == 600
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
        assert hub.engine('kokoro').default_voice == 'af_alloy'
        crall = hub.engine('crall-math-dk-v2-breeze-tts2')
        assert crall.model == 'breeze-tts2'
        assert crall.default_voice == 'crall-math-dk-v2'
        assert crall.endpoint.endswith(':8821/v1/audio/speech')
        assert hub.profiles()[0]['id'] == 'kokoro'
    finally:
        hub.close()


def test_local_tts_config_adds_reader_profile_without_replacing_defaults(tmp_path, monkeypatch):
    from dkvis.presentation import tts
    from dkvis.presentation.audio_library import AudioLectureHub
    monkeypatch.delenv('DKVIS_AUDIO_TTS_PROFILE', raising=False)
    monkeypatch.delenv('DKVIS_AUDIO_TTS_ENDPOINT', raising=False)
    overlay = tmp_path / 'tts.local.toml'
    overlay.write_text(
        'profile = "private-voice-breeze-tts2"\n'
        '\n'
        '[profiles.private-voice-breeze-tts2]\n'
        'narrator_voice = "private-voice"\n'
        'endpoint = "http://127.0.0.1:8821/v1/audio/speech"\n'
        'model = "breeze-tts2"\n'
        'voice = "private-voice"\n'
        'response_format = "wav"\n',
        encoding='utf-8')
    monkeypatch.setattr(tts, 'LOCAL_CONFIG', overlay)
    hub = AudioLectureHub(cache=tmp_path / 'cache')
    try:
        # The checked-in reader default stays Kokoro; the local profile is an
        # extra option, not a replacement for the checked-in profiles.
        assert hub.profile == 'kokoro'
        ids = [row['id'] for row in hub.profiles()]
        assert ids[0] == 'kokoro'
        assert 'private-voice-breeze-tts2' in ids
        engine = hub.engine('private-voice-breeze-tts2')
        assert engine.model == 'breeze-tts2'
        assert engine.default_voice == 'private-voice'
        assert engine.endpoint == 'http://127.0.0.1:8821/v1/audio/speech'
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
        assert client.get('/api/audio-voices',params={'profile':'kokoro'}).json()['default_voice']=='af_alloy'
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


def test_browser_timeline_math_and_complete_transcript_dom():
    """Run DOM-independent JavaScript checks against the actual reader source."""
    import subprocess
    node = shutil.which('node')
    if node is None:
        pytest.skip('Node.js is unavailable')
    script = Path(__file__).with_name('test_audio_reader_progress.js')
    result = subprocess.run([node, str(script)], check=True, text=True,
                            capture_output=True, timeout=15)
    assert 'Full transcript and lecture-wide timeline calculations passed' in result.stdout


def test_machine_local_endpoint_overlay_preserves_inherited_profile(tmp_path, monkeypatch):
    """A local endpoint should work without copying a full built-in profile."""
    from dkvis.presentation import tts
    from dkvis.presentation.audio_library import AudioLectureHub
    config = tmp_path / 'tts.local.toml'
    config.write_text('''
[profiles.kokoro]
endpoint = "http://127.0.0.1:8899/v1/audio/speech"
[profiles.crall-math-dk-v2-breeze-tts2.request]
instruction = "Local mathematical narration."
[profiles.local-voice]
model = "kokoro"
voice = "af_sky"
response_format = "mp3"
endpoint = "http://127.0.0.1:8877/v1/audio/speech"
''', encoding='utf-8')
    monkeypatch.setattr(tts, 'LOCAL_CONFIG', config)
    monkeypatch.setenv('KOKORO_TTS_ENDPOINT', 'http://192.168.0.1:8880/v1/audio/speech')
    monkeypatch.delenv('DKVIS_AUDIO_TTS_PROFILE', raising=False)
    doc = tts.load_profiles()
    assert doc['profiles']['kokoro']['model'] == 'kokoro'
    assert doc['profiles']['kokoro']['voice'] == 'af_alloy'
    assert doc['profiles']['kokoro']['narrator_voice'] == 'af_alloy'
    assert doc['profiles']['kokoro']['response_format'] == 'mp3'
    assert 'endpoint_env' not in doc['profiles']['kokoro']
    assert doc['profiles']['crall-math-dk-v2-breeze-tts2']['request']['cfg_scale'] == 2.0
    assert doc['profiles']['crall-math-dk-v2-breeze-tts2']['request']['instruction'] == 'Local mathematical narration.'
    hub = AudioLectureHub(cache=tmp_path / 'cache')
    try:
        assert hub.profile == 'kokoro'
        assert hub.engine('kokoro').endpoint == 'http://127.0.0.1:8899/v1/audio/speech'
        assert hub.engine('local-voice').endpoint == 'http://127.0.0.1:8877/v1/audio/speech'
        # All engines use the hub's one configuration snapshot.
        config.unlink()
        assert hub.engine('crall-math-dk-v2-breeze-tts2').request_settings['instruction'] == 'Local mathematical narration.'
    finally:
        hub.close()


def test_local_profile_override_can_replace_reference_and_relative_lexicons(tmp_path, monkeypatch):
    from dkvis.presentation import tts
    config = tmp_path / 'tts.local.toml'
    config.write_text('''
[profiles.crall]
voice = "new-voice"
pronunciation_lexicon = "custom.pls"
[pronunciation_lexicons]
"other-model" = "extra.pls"
''', encoding='utf-8')
    monkeypatch.setattr(tts, 'LOCAL_CONFIG', config)
    doc = tts.load_profiles()
    profile = doc['profiles']['crall']
    assert profile['voice'] == 'new-voice'
    assert 'reference' not in profile
    assert profile['pronunciation_lexicon'] == str(tmp_path/'custom.pls')
    assert doc['pronunciation_lexicons']['other-model'] == str(tmp_path/'extra.pls')
    # Explicit independent configs do not accidentally inherit local overrides.
    explicit = tmp_path / 'standalone.toml'
    explicit.write_text('''
[profiles.private]
endpoint = "http://localhost:8900/v1/audio/speech"
model = "kokoro"
voice = "af_heart"
response_format = "mp3"
''', encoding='utf-8')
    doc = tts.load_profiles(explicit)
    assert set(doc['profiles']) == {'private'}
    # Explicitly naming the normal file also opts out of machine-local overlays.
    plain = tts.load_profiles(tts.DEFAULT_CONFIG)
    assert plain['profiles']['crall']['voice'] == 'crall-math-dk'
    assert 'pronunciation_lexicon' not in plain['profiles']['crall']


def test_breeze_page_uses_verified_subrequests_and_real_chunk_timings(tmp_path, monkeypatch):
    """A syntactically valid WAV at the server cap must never end a page early."""
    import io
    import urllib.request
    import wave
    from dkvis.presentation.audio_library import SpeechSettings
    from dkvis.presentation.media import duration

    requests = []

    class FakeResponse(io.BytesIO):
        headers = {'Content-Type': 'audio/wav'}

    def fake_open(request, timeout):
        payload = json.loads(request.data)
        requests.append(payload)
        words = len(payload['input'].split())
        # Simulate the Breeze generation cutoff: the return is valid WAV but
        # the last words were not spoken for the oversized requests.
        seconds = 1.0 if words >= 20 else words * .055
        audio = io.BytesIO()
        with wave.open(audio, 'wb') as output:
            output.setnchannels(1)
            output.setsampwidth(2)
            output.setframerate(24000)
            output.writeframes(b'\x00\x00' * int(seconds * 24000))
        return FakeResponse(audio.getvalue())

    monkeypatch.setattr(urllib.request, 'urlopen', fake_open)
    library = AudioLectureLibrary(cache=tmp_path / 'cache',
                                  profile='crall-math-dk-v2-breeze-tts2')
    try:
        library.max_audio_seconds = 1.0
        library.max_speech_words_per_second = 0
        library.speech_max_words = 50
        library.speech_max_chars = 280
        text = ' '.join(f'concept{i}' for i in range(75)) + '.'
        destination = tmp_path / 'page.mp3'
        library._send_speech(text, SpeechSettings('breeze-tts2', 'user-custom', 1.25), destination)
        assert destination.is_file()
        timings = json.loads((tmp_path / 'page.mp3.timings.json').read_text())
        assert timings['version'] == 1
        assert sum(chunk['words'] for chunk in timings['chunks']) == 75
        assert len(requests) > len(timings['chunks']), 'duration-capped audio must be retried'
        assert len(timings['chunks']) >= 4
        assert all(row['voice'] == 'user-custom' for row in requests)
        assert all(row['response_format'] == 'wav' and 'speed' not in row for row in requests)
        assert timings['chunks'][0]['start'] == 0
        assert all(a['end'] <= b['start'] for a, b in zip(timings['chunks'], timings['chunks'][1:]))
        assert timings['chunks'][-1]['end'] <= timings['duration'] + .02
        assert abs(duration(destination) - timings['duration']) < .05
    finally:
        library.close()


def test_breeze_cache_identity_changes_for_bounded_synthesis(audio_site):
    """Reject any pre-fix cached, potentially incomplete Breeze page files."""
    _client, _lecture, lib, _calls = audio_site
    from dkvis.presentation.audio_library import SpeechSettings
    settings = SpeechSettings('breeze-tts2', 'user-custom', 1.0)
    path, _text, digest = lib._target('123000', 0, settings)
    assert path.suffix == '.mp3'
    assert digest and len(digest) == 64
    assert 'bounded-v4' in __import__('inspect').getsource(lib._target)


def test_reader_breeze_small_chunks_are_stricter_than_production(tmp_path):
    library = AudioLectureLibrary(cache=tmp_path/'cache',
                                  profile='crall-math-dk-v2-breeze-tts2')
    try:
        assert library.speech_max_words <= 12
        assert library.speech_max_chars <= 140
        assert 0 < library.max_speech_words_per_second <= 6
    finally:
        library.close()


def test_short_tts_segments_are_not_mistaken_for_complete_audio():
    from dkvis.presentation.audio import check_audio_minimum, AudioTooShortError
    with pytest.raises(AudioTooShortError):
        check_audio_minimum('word ' * 12, 1.0, 6.0, min_words=8)
    check_audio_minimum('word ' * 12, 4.0, 6.0, min_words=8)


def test_breeze_retries_non_cap_short_wav_in_smaller_passages(tmp_path, monkeypatch):
    """A TTS backend can omit speech without returning a 60-second capped file."""
    import io
    import urllib.request
    import wave
    from dkvis.presentation.audio_library import SpeechSettings

    calls = []

    class Response(io.BytesIO):
        headers = {'Content-Type': 'audio/wav'}

    def fake_open(request, timeout):
        payload = json.loads(request.data)
        words = len(payload['input'].split())
        calls.append(words)
        # Valid WAV, but too short for the requested text if >= 12 words.
        seconds = .7 if words >= 12 else words * .38
        audio = io.BytesIO()
        with wave.open(audio, 'wb') as output:
            output.setnchannels(1)
            output.setsampwidth(2)
            output.setframerate(24000)
            output.writeframes(b'\0\0' * round(seconds * 24000))
        return Response(audio.getvalue())

    monkeypatch.setattr(urllib.request, 'urlopen', fake_open)
    library = AudioLectureLibrary(cache=tmp_path/'cache',
                                  profile='crall-math-dk-v2-breeze-tts2')
    try:
        from dkvis.presentation.media import duration
        destination = tmp_path/'complete.mp3'
        library._send_speech(' '.join(f'theorem{i}' for i in range(48)),
                             SpeechSettings('breeze-tts2', 'my-voice', 1), destination)
        assert destination.exists()
        timings = json.loads((tmp_path/'complete.mp3.timings.json').read_text())
        assert sum(item['words'] for item in timings['chunks']) == 48
        assert duration(destination) > 12
        assert max(calls) >= 12 and min(calls) < 12, 'too-short chunks must be split'
    finally:
        library.close()


def test_breeze_assembly_duration_mismatch_is_not_cached(tmp_path, monkeypatch):
    """FFmpeg output shorter than the decoded inputs must fail before cache publication."""
    import io
    import urllib.request
    import wave
    from dkvis.presentation.audio_library import SpeechSettings, SpeechServiceError
    from dkvis.presentation import media

    class Response(io.BytesIO):
        headers = {'Content-Type': 'audio/wav'}

    def fake_open(request, timeout):
        wav = io.BytesIO()
        with wave.open(wav, 'wb') as out:
            out.setnchannels(1)
            out.setsampwidth(2)
            out.setframerate(24000)
            out.writeframes(b'\0\0' * 48000)
        return Response(wav.getvalue())

    real_duration = media.duration
    monkeypatch.setattr(urllib.request, 'urlopen', fake_open)
    monkeypatch.setattr(media, 'duration', lambda path: 0.5 if path.suffix == '.tmp' else real_duration(path))
    library = AudioLectureLibrary(cache=tmp_path/'cache',
                                  profile='crall-math-dk-v2-breeze-tts2')
    try:
        target = tmp_path/'cache'/'bad-output.mp3'
        with pytest.raises(SpeechServiceError, match='Audio assembly lost speech'):
            library._generate(target, 'Four words are enough.',
                              SpeechSettings('breeze-tts2', 'my-voice', 1))
        assert not target.exists()
    finally:
        library.close()


def test_breeze_detects_short_http_body(tmp_path, monkeypatch):
    """Reject a response whose actual bytes do not match Content-Length."""
    import io
    import urllib.request
    from dkvis.presentation.audio_library import SpeechSettings, SpeechServiceError

    class Response(io.BytesIO):
        headers = {'Content-Type': 'audio/wav', 'Content-Length': '5000'}

    monkeypatch.setattr(urllib.request, 'urlopen',
                        lambda request, timeout: Response(b'RIFF' + b'\0' * 2000))
    library = AudioLectureLibrary(cache=tmp_path/'cache',
                                  profile='crall-math-dk-v2-breeze-tts2')
    try:
        target = tmp_path/'cache'/'short-body.mp3'
        with pytest.raises(SpeechServiceError, match='response ended early'):
            library._generate(target, 'A finite dimensional theorem.',
                              SpeechSettings('breeze-tts2', 'my-voice', 1))
        assert not target.exists()
    finally:
        library.close()


def test_local_tts_segment_limits_are_independent_of_display_page_size(tmp_path, monkeypatch):
    # A readable 600-character page should never become one Breeze request.
    library = AudioLectureLibrary(cache=tmp_path / 'cache',
                                  profile='crall-math-dk-v2-breeze-tts2')
    try:
        assert library.page_chars == 600
        assert library.speech_max_words == 12
        assert library.speech_max_chars == 140
        assert library.max_audio_seconds == 12
    finally:
        library.close()
    monkeypatch.setenv('DKVIS_AUDIO_SEGMENT_WORDS', '6')
    monkeypatch.setenv('DKVIS_AUDIO_SEGMENT_CHARS', '90')
    monkeypatch.setenv('DKVIS_AUDIO_SEGMENT_SECONDS', '7')
    smaller = AudioLectureLibrary(cache=tmp_path / 'cache',
                                   profile='crall-math-dk-v2-breeze-tts2')
    try:
        assert smaller.speech_max_words == 6
        assert smaller.speech_max_chars == 90
        assert smaller.max_audio_seconds == 7
    finally:
        smaller.close()


def test_breeze_synthesizes_short_requests_even_without_duration_warning(tmp_path, monkeypatch):
    """A clipped-but-plausible WAV cannot be detected by duration heuristics.

    A local service may accept 20 words and return valid audio containing
    fewer words, with duration far below its 60s server cap. Prevent those
    long requests by limiting the text sent to the service in the first place.
    """
    import io
    import wave
    import urllib.request
    from dkvis.presentation.audio_library import SpeechSettings
    from dkvis.presentation.media import duration

    requests = []

    class Response(io.BytesIO):
        headers = {'Content-Type': 'audio/wav'}

    def endpoint(request, timeout):
        payload = json.loads(request.data)
        words = len(payload['input'].split())
        requests.append((words, len(payload['input'])))
        # At >=16 words this fake endpoint silently drops speech but still
        # gives back a valid WAV of plausible duration: no duration error.
        seconds = 5 if words >= 16 else 0.37 * words
        raw = io.BytesIO()
        with wave.open(raw, 'wb') as wav:
            wav.setnchannels(1)
            wav.setsampwidth(2)
            wav.setframerate(8000)
            wav.writeframes(b'\0\0' * round(seconds * 8000))
        return Response(raw.getvalue())

    monkeypatch.setattr(urllib.request, 'urlopen', endpoint)
    library = AudioLectureLibrary(cache=tmp_path / 'cache',
                                  profile='crall-math-dk-v2-breeze-tts2')
    try:
        destination = tmp_path/'speech.mp3'
        text = ' '.join(f'concept{i}' for i in range(90)) + '.'
        library._send_speech(text, SpeechSettings('breeze-tts2', 'custom-voice', 1), destination)
        assert len(requests) >= 8
        assert all(words <= 12 and chars <= 140 for words, chars in requests)
        assert duration(destination) > 20
        markers = json.loads((tmp_path/'speech.mp3.timings.json').read_text())
        assert sum(row['words'] for row in markers['chunks']) == 90
    finally:
        library.close()


def test_pronunciation_expansions_obey_spoken_segment_limits(tmp_path, monkeypatch):
    import io
    import wave
    import urllib.request
    from dkvis.presentation.audio_library import SpeechSettings

    observed = []

    class Response(io.BytesIO):
        headers = {'Content-Type': 'audio/wav'}

    def fake_open(request, timeout):
        words = json.loads(request.data)['input'].split()
        observed.append(words)
        raw = io.BytesIO()
        with wave.open(raw, 'wb') as wav:
            wav.setnchannels(1)
            wav.setsampwidth(2)
            wav.setframerate(8000)
            wav.writeframes(b'\0\0' * round(max(0.6, len(words) * .37) * 8000))
        return Response(raw.getvalue())

    monkeypatch.setattr(urllib.request, 'urlopen', fake_open)
    library = AudioLectureLibrary(cache=tmp_path/'cache',
                                  profile='crall-math-dk-v2-breeze-tts2')
    library.pronunciation_replacements = {'QED': 'the proof of the statement is now complete'}
    try:
        library._send_speech(' '.join(['QED'] * 9),
                             SpeechSettings('breeze-tts2', 'custom-voice', 1),
                             tmp_path/'expanded.mp3')
        assert len(observed) >= 3
        assert all(len(words) <= 12 for words in observed)
        assert sum(len(words) for words in observed) == 9 * 8
    finally:
        library.close()


def test_local_foobar_profile_is_distinct_from_crall_voice_override(tmp_path, monkeypatch):
    from dkvis.presentation import tts
    from dkvis.presentation.audio_library import AudioLectureHub
    local = tmp_path / 'tts.local.toml'
    local.write_text('''profile = "foobar-v1-breeze-tts2"
[profiles.foobar-v1-breeze-tts2]
endpoint = "http://127.0.0.1:8821/v1/audio/speech"
model = "breeze-tts2"
voice = "foobar-v1"
response_format = "wav"
max_chars = 750
max_words = 110
[profiles.foobar-v1-breeze-tts2.request]
instruction = "Speak as Foobar."
cfg_scale = 2.0
''')
    monkeypatch.setattr(tts, 'LOCAL_CONFIG', local)
    monkeypatch.delenv('DKVIS_AUDIO_TTS_PROFILE', raising=False)
    monkeypatch.delenv('DKVIS_AUDIO_PAGE_CHARS', raising=False)
    hub = AudioLectureHub(cache=tmp_path / 'audio-cache')
    try:
        foobar = hub.engine('foobar-v1-breeze-tts2')
        crall = hub.engine('crall-math-dk-v2-breeze-tts2')
        assert foobar.profile == 'foobar-v1-breeze-tts2'
        assert foobar.model == 'breeze-tts2'
        assert foobar.default_voice == 'foobar-v1'
        assert foobar.request_settings['instruction'] == 'Speak as Foobar.'
        assert crall.request_settings['instruction'] != foobar.request_settings['instruction']
        assert crall.settings(voice='foobar-v1').voice == foobar.default_voice
        assert foobar.page_chars == 600
        assert foobar.speech_max_chars == 140
        assert foobar.speech_max_words == 12
        assert foobar.max_audio_seconds == 12
    finally:
        hub.close()
