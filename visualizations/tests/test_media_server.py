"""HTTP behavior needed by the lecture player, including real byte-range reads."""
import json

import pytest

pytest.importorskip('starlette')
from starlette.testclient import TestClient
from dkvis.presentation.serve import create_app


@pytest.fixture
def library(tmp_path):
    data = bytes(range(256))*64
    (tmp_path/'lecture.kokoro.narrated.mp4').write_bytes(data)
    (tmp_path/'slides.html').write_text('<h1>Lecture</h1>')
    (tmp_path/'handout.pdf').write_bytes(b'%PDF-1.4\n')
    (tmp_path/'space & name.mp4').write_bytes(data)
    (tmp_path/'notes.txt').write_text('not a media listing')
    work = tmp_path/'lecture-narrated'
    work.mkdir()
    (work/'timeline-kokoro.json').write_text(json.dumps([dict(title='Start', start=0), dict(title='Proof', start=42.5)]))
    (work/'timeline-crall.json').write_text(json.dumps([dict(title='Wrong narrator', start=0)]))
    with TestClient(create_app(tmp_path)) as client:
        yield client, tmp_path, data


def test_seeking_ranges_head_and_if_range(library):
    client, _, data = library
    url = '/files/lecture.kokoro.narrated.mp4'
    response = client.get(url, headers={'Range': 'bytes=2048-3071'})
    assert response.status_code == 206
    assert response.content == data[2048:3072]
    assert response.headers['content-range'] == f'bytes 2048-3071/{len(data)}'
    assert response.headers['accept-ranges'] == 'bytes'
    assert int(response.headers['content-length']) == 1024
    assert client.get(url, headers={'Range': 'bytes=-512'}).content == data[-512:]
    assert client.get(url, headers={'Range': 'bytes=16000-'}).content == data[16000:]
    invalid = client.get(url, headers={'Range': 'bytes=999999-'})
    assert invalid.status_code == 416
    head = client.head(url)
    assert head.status_code == 200 and not head.content
    assert int(head.headers['content-length']) == len(data)
    stale = client.get(url, headers={'Range': 'bytes=0-9', 'If-Range': '"old"'})
    assert stale.status_code == 200 and stale.content == data


def test_catalog_and_inline_documents(library):
    client, _, _ = library
    listing = client.get('/api/catalog').json()
    files = {entry['name']: entry for entry in listing['items']}
    assert files['lecture.kokoro.narrated.mp4']['kind'] == 'video'
    assert files['slides.html']['kind'] == 'slides'
    assert files['handout.pdf']['kind'] == 'pdf'
    assert files['lecture-narrated']['kind'] == 'folder'
    assert 'notes.txt' not in files
    assert client.get(files['space & name.mp4']['url']).status_code == 200
    assert client.get('/files/slides.html').headers['content-type'].startswith('text/html')
    assert client.get('/files/handout.pdf').headers['content-type'] == 'application/pdf'
    assert client.get('/').status_code == 200


def test_chapters_match_narrator_and_preview(library):
    client, root, data = library
    assert client.get('/api/chapters', params={'path': 'lecture.kokoro.narrated.mp4'}).json() == [
        dict(title='Start', start=0.), dict(title='Proof', start=42.5)]
    (root/'lecture.kokoro.preview.narrated.mp4').write_bytes(data)
    (root/'lecture-narrated/timeline-kokoro.preview.json').write_text(json.dumps([dict(title='Preview', start=0)]))
    assert client.get('/api/chapters', params={'path': 'lecture.kokoro.preview.narrated.mp4'}).json()[0]['title'] == 'Preview'
    (root/'repair').mkdir()
    (root/'repair/leveled.mp4').write_bytes(data)
    (root/'repair/timeline.json').write_text(json.dumps([dict(title='Repaired', start=0)]))
    assert client.get('/api/chapters', params={'path': 'repair/leveled.mp4'}).json()[0]['title'] == 'Repaired'


def test_paths_stay_within_media_root(library, tmp_path):
    client, root, _ = library
    outside = root.parent/'private-media-server-test.txt'
    outside.write_text('outside')
    (root/'outside.txt').symlink_to(outside)
    for path in ['..', '../private-media-server-test.txt']:
        assert client.get('/api/catalog', params={'folder': path}).status_code == 404
        assert client.get('/api/chapters', params={'path': path}).status_code == 404
    assert client.get('/files/outside.txt').status_code == 404
    assert client.get('/files/%2e%2e/private-media-server-test.txt').status_code == 404


def test_numbered_video_reuses_stable_chapter_cache(library):
    client, root, data = library
    filename = '001000_prereq-projections.kokoro.narrated.mp4'
    (root/filename).write_bytes(data)
    cache = root/'prereq-projections-narrated'
    cache.mkdir()
    chapters = [dict(title='Question', start=10.)]
    (cache/'timeline-kokoro.json').write_text(json.dumps(chapters))
    assert client.get('/api/chapters', params={'path': filename}).json() == chapters
    entries = client.get('/api/catalog').json()['items']
    entry = next(row for row in entries if row['name'] == filename)
    assert entry['title'].startswith('001000')
