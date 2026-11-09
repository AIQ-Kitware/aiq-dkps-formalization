"""G1/G2/G3 selection and isolated on-demand TTS requests."""
import json
from pathlib import Path
import re
import time

from starlette.testclient import TestClient
from dkvis.presentation.audio_library import AudioLectureHub, SOURCE_DIRECTORY, PAPER_DIRECTORY, narration_extractor
from dkvis.presentation.serve import create_app


def test_g3_syllabus_has_26_complete_spoken_lectures():
    plan = json.loads((PAPER_DIRECTORY / 'track.json').read_text())
    rows = plan['lectures']
    assert len(rows) == 26
    assert len({row['id'] for row in rows}) == 26
    assert len(list(PAPER_DIRECTORY.glob('[0-9]' * 6 + '-*.md'))) == 26
    assert rows[0]['section'] == 'orientation'
    assert [row['section'] for row in rows[-6:]] == ['result'] * 6
    assert [row['source_g2'] for row in rows[-6:]] == [
        '110000', '112000', '116000', '117000', '134000', '145000']
    for row in rows:
        path = PAPER_DIRECTORY / row['file']
        raw = path.read_text()
        assert raw.count('<!-- BEGIN SPOKEN LECTURE -->') == 1
        assert raw.count('<!-- END SPOKEN LECTURE -->') == 1
        spoken = narration_extractor(path)
        assert len(spoken.split()) >= 1150, row['file']
        assert len(spoken.split()) <= 1750, row['file']
        assert 'Source declaration excerpts' not in spoken
        assert (PAPER_DIRECTORY/'metadata'/f"{row['id']}.json").is_file()


def test_course_tracks_and_track_isolation(tmp_path):
    calls = []

    def synth(text, settings, dest):
        calls.append(text)
        dest.write_bytes(b'ID3' + b'\0' * 1024)

    hub = AudioLectureHub(cache=tmp_path / 'cache', profile='kokoro', sender=synth)
    renders = tmp_path / 'renders'
    renders.mkdir()
    with TestClient(create_app(renders, audio_library=hub)) as client:
        tracks = client.get('/api/audio-tracks').json()['tracks']
        assert [r['id'] for r in tracks] == ['g1', 'g2', 'g3']
        assert tracks[0]['url'] == '/'
        assert tracks[1]['count'] == 150
        assert tracks[2]['count'] == 26
        assert len(client.get('/api/audio-lectures').json()['items']) == 150
        assert len(client.get('/api/audio-lectures?track=g3').json()['items']) == 26
        assert client.get('/api/audio-lectures?track=g2').json()['items'][0]['id'] == '000000'
        assert client.get('/api/audio-lectures?track=g3').json()['items'][0]['id'] == '000000'
        g2 = client.get('/api/audio-lectures/000000?track=g2').json()
        g3 = client.get('/api/audio-lectures/000000?track=g3').json()
        assert g2['title'] != g3['title']
        assert 'An eigenvector can change' in g3['transcript']
        assert not any('<!-- END SPOKEN LECTURE -->' in p for p in g3['pages'])
        assert client.get('/api/audio-lectures?track=../../etc').status_code == 400
        assert client.get('/api/audio-lectures/000000?track=../../etc').status_code == 400
        assert client.post('/api/audio-lectures/000000/pages/0/render',json={'track':'../oops'}).status_code == 400
        assert client.post('/api/audio-lectures/000000/pages/0/render',json={'track':'g3','endpoint':'http://host'}).status_code == 400
        out=client.post('/api/audio-lectures/000000/pages/0/render', json={'track':'g3'})
        assert out.status_code in (200,202), out.text
        result={}
        for _ in range(50):
            result=client.get('/api/audio-lectures/000000/pages/0',params={'track':'g3'}).json()
            if result['state']=='ready': break
            time.sleep(.02)
        assert result['state']=='ready', result
        assert 'track=g3' in result['url']
        assert client.get(result['url']).status_code==200
        assert client.get('/api/audio-lectures/000000/pages/0',params={'track':'g2'}).json()['state']=='missing'
        assert 'g3' in str(hub.engine('kokoro','g3').cache)
        assert hub.engine('kokoro','g2').cache != hub.engine('kokoro','g3').cache
        assert len(calls)==1


def test_g3_learning_resources_reference_existing_catalog(tmp_path):
    hub=AudioLectureHub(cache=tmp_path/'cache')
    try:
        g3=hub.detail('025000', 'g3')
        assert g3['related_resources']
        assert all(row['url'].startswith('https://') for row in g3['related_resources'])
    finally:
        hub.close()
