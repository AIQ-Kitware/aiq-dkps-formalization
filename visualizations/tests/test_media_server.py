"""HTTP behavior needed by the lecture player, including real byte-range reads."""
import json

import pytest

pytest.importorskip('starlette')
from starlette.testclient import TestClient
from dkvis.presentation.serve import create_app


@pytest.fixture
def library(tmp_path,monkeypatch):
    from dkvis.deck_spec import DeckSpec
    from dkvis.decks import DECKS
    monkeypatch.setitem(DECKS,'lecture',DeckSpec('lecture',()))
    data = bytes(range(256))*64
    (tmp_path/'lecture.kokoro.narrated.mp4').write_bytes(data)
    (tmp_path/'lecture.standalone.html').write_text('<h1>Lecture</h1>')
    (tmp_path/'lecture.handout.pdf').write_bytes(b'%PDF-1.4\n')
    (tmp_path/'space & name.mp4').write_bytes(data)
    (tmp_path/'notes.txt').write_text('not a media listing')
    work = tmp_path/'lecture-narrated'
    work.mkdir()
    (work/'timeline-kokoro.json').write_text(json.dumps([dict(title='Start', start=0), dict(title='Proof', start=42.5)]))
    (work/'timeline-crall.json').write_text(json.dumps([dict(title='Wrong narrator', start=0)]))
    with TestClient(create_app(tmp_path, feedback_directory=tmp_path.parent/(tmp_path.name+'-feedback'))) as client:
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


def test_catalog_groups_formats_under_the_stable_deck_id(library):
    client, _, _ = library
    listing = client.get('/api/catalog').json()
    lectures = {entry['id']: entry for entry in listing['items']}
    lecture = lectures['lecture']
    assert lecture['kind'] == 'lecture'
    assert {a['kind'] for a in lecture['assets']} == {'video', 'slides', 'pdf'}
    assert not {'lecture.standalone', 'lecture.handout', 'lecture-narrated'} & lectures.keys()
    assert 'notes' not in lectures
    assert 'space & name' not in lectures
    assert client.get('/files/space%20%26%20name.mp4').status_code == 200
    assert client.get('/files/lecture.standalone.html').headers['content-type'].startswith('text/html')
    assert client.get('/files/lecture.handout.pdf').headers['content-type'] == 'application/pdf'
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
    entry = next(row for row in entries if row['id'] == 'prereq-projections')
    assert any(a['name'] == filename for a in entry['assets'])
    assert entry['title'].startswith('001000')


def test_voices_themes_and_exports_are_resources_of_one_lecture(library):
    client,root,data=library
    (root/'001000_prereq-projections.crall.narrated.mp4').write_bytes(data)
    (root/'001000_prereq-projections.kokoro.narrated.mp4').write_bytes(data)
    (root/'001000_prereq-projections-light.standalone.html').write_text('slides')
    folder=root/'001000_prereq-projections-narration'
    folder.mkdir()
    (folder/'presentation.txt').write_text('Exported speech')
    (root/'001000_prereq-projections.crall.narrated.mp4.metadata.json').write_text(json.dumps(
        dict(generated_at='2026-11-05T10:00:00+00:00',provenance={'slides':{'model':'recorded'}})))
    rows=client.get('/api/catalog').json()['items']
    lecture=next(r for r in rows if r['id']=='prereq-projections')
    assert len([r for r in rows if r['id']=='prereq-projections'])==1
    assert {a['voice'] for a in lecture['assets'] if a['kind']=='video'}=={'crall','kokoro'}
    assert any(a['theme']=='light' for a in lecture['assets'])
    assert any(a['kind']=='transcript' for a in lecture['assets'])
    assert any(a['generated_at']=='2026-11-05T10:00:00+00:00' for a in lecture['assets'])
    assert lecture['provenance']['slides']['initial_source_attribution']
    assert client.get(lecture['authored_transcript_url']).status_code==200


def test_historical_speech_cache_provides_transcript_and_optional_vtt(library):
    client,root,data=library
    raw=root/'speech.wav';raw.write_bytes(data)
    raw.with_suffix('.txt').write_text('The eigenvalue is small. The eigenspace needs a gap.')
    raw.with_suffix('.json').write_text(json.dumps(dict(seconds=4,model='test-tts',voice='test-voice')))
    processed=root/'leveled.wav';processed.write_bytes(data)
    processed.with_suffix('.json').write_text(json.dumps(dict(source=str(raw))))
    joined=root/'joined.wav';joined.write_bytes(data)
    joined.with_suffix('.parts.json').write_text(json.dumps(dict(inputs=[str(processed)],pause=.12)))
    timeline=[dict(scene='Example',title='Example',start=0,end=12,
                   builds=[dict(start=0,end=12,audio=str(joined))])]
    (root/'lecture-narrated/timeline-kokoro.json').write_text(json.dumps(timeline))
    detail=client.get('/api/media',params={'path':'lecture.kokoro.narrated.mp4'}).json()
    assert detail['transcript_complete'] and detail['captions_available']
    assert detail['models']==['test-tts'] and detail['voices']==['test-voice']
    assert detail['transcript'][0]['speech_end']==4
    text=client.get('/api/transcript',params={'path':'lecture.kokoro.narrated.mp4'}).text
    assert 'The eigenspace needs a gap.' in text
    captions=client.get('/api/captions',params={'path':'lecture.kokoro.narrated.mp4'})
    assert captions.status_code==200 and captions.headers['content-type'].startswith('text/vtt')
    assert 'WEBVTT' in captions.text and '00:00:04.000' in captions.text
    assert '00:00:12.000' not in captions.text  # Silent thinking time is not speech.
    assert client.get('/api/captions',params={'path':'lecture.crall.narrated.mp4'}).status_code==404


def test_snapshot_captions_survive_audio_cache_removal(library):
    client,root,_=library
    timeline=[dict(scene='One',title='One',start=1,end=10,builds=[dict(
        start=1,end=10,audio=str(root/'deleted.wav'),text='A < B & C.',speech_seconds=3)])]
    (root/'lecture-narrated/timeline-kokoro.json').write_text(json.dumps(timeline))
    response=client.get('/api/captions',params={'path':'lecture.kokoro.narrated.mp4'})
    assert response.status_code==200
    assert 'A &lt; B &amp; C.' in response.text
    assert '00:00:01.000 --> 00:00:04.000' in response.text


def test_metadata_cannot_read_a_transcript_outside_the_render_tree(library):
    client,root,data=library
    raw=root/'speech.wav';raw.write_bytes(data)
    secret=root.parent/'private-transcript.txt';secret.write_text('private contents')
    raw.with_suffix('.txt').symlink_to(secret)
    raw.with_suffix('.json').write_text(json.dumps(dict(seconds=2)))
    (root/'lecture-narrated/timeline-kokoro.json').write_text(json.dumps([
        dict(start=0,end=3,builds=[dict(start=0,end=3,audio=str(raw))])]))
    assert client.get('/api/transcript',params={'path':'lecture.kokoro.narrated.mp4'}).status_code==404
    assert client.get('/api/source-transcript',params={'deck':'../private'}).status_code==404


def test_explicit_output_name_keeps_deck_identity_and_voice_timeline(library):
    client,root,data=library
    filename='custom-export.mp4'
    (root/filename).write_bytes(data)
    (root/(filename+'.metadata.json')).write_text(json.dumps(dict(deck='prereq-projections',
        settings=dict(profile='crall',theme='dark',preview=False))))
    work=root/'prereq-projections-narrated';work.mkdir()
    (work/'timeline-crall.json').write_text(json.dumps([dict(title='Right deck',start=0)]))
    rows=client.get('/api/catalog').json()['items']
    lecture=next(row for row in rows if row['id']=='prereq-projections')
    assert any(a['path']==filename and a['voice']=='crall' for a in lecture['assets'])
    assert not any(row['id']=='custom-export' for row in rows)
    assert client.get('/api/chapters',params={'path':filename}).json()[0]['title']=='Right deck'


def test_feedback_persists_exact_generation_and_playback_context(library):
    import hashlib
    client,root,data=library
    filename='lecture.kokoro.narrated.mp4'
    metadata=dict(generated_at='2026-11-05T10:00:00+00:00',source_commit='old-generation',
                  settings=dict(model='kokoro',voice='af_heart'),provenance={'slides':{'model':'recorded'}})
    (root/(filename+'.metadata.json')).write_text(json.dumps(metadata))
    lecture=next(row for row in client.get('/api/catalog').json()['items'] if row['id']=='lecture')
    asset=next(a for a in lecture['assets'] if a['path']==filename)
    payload=dict(deck='lecture',path=filename,version=asset['version'],text='The equation is hard to read.',playback_seconds=44.25)
    first=client.post('/api/feedback',json=payload)
    second=client.post('/api/feedback',json={**payload,'text':'The next explanation helps.'})
    assert first.status_code==second.status_code==201
    assert first.json()['id']!=second.json()['id']
    folder=root.parent/(root.name+'-feedback')
    saved=json.loads((folder/(first.json()['id']+'.json')).read_text())
    assert saved['deck']=='lecture' and saved['text']==payload['text']
    assert saved['playback_seconds']==44.25 and saved['chapter']['title']=='Proof'
    assert saved['asset']['sha256']==hashlib.sha256(data).hexdigest()
    assert saved['asset']['version']==asset['version']
    assert saved['asset']['source_commit']=='old-generation'
    assert saved['asset']['provenance']==metadata['provenance']
    assert saved['timeline']['path']=='lecture-narrated/timeline-kokoro.json'
    # Replacing a render never rewrites the generation snapshot in old feedback.
    (root/filename).write_bytes(b'regenerated')
    assert json.loads((folder/(first.json()['id']+'.json')).read_text())==saved
    assert client.post('/api/feedback',json=payload).status_code==409
    assert client.get('/files/../'+folder.name+'/'+first.json()['id']+'.json').status_code==404


def test_feedback_supports_documents_and_unrendered_lectures(library):
    client,root,_=library
    rows=client.get('/api/catalog').json()['items']
    document=next(a for row in rows for a in row['assets'] if a['path']=='lecture.handout.pdf')
    response=client.post('/api/feedback',json=dict(deck='lecture',path=document['path'],version=document['version'],text='PDF feedback'))
    assert response.status_code==201
    response=client.post('/api/feedback',json=dict(deck='prereq-projections',path=None,text='Lecture feedback'))
    assert response.status_code==201
    folder=root.parent/(root.name+'-feedback')
    saved=json.loads((folder/(response.json()['id']+'.json')).read_text())
    assert saved['asset'] is None and saved['playback_seconds'] is None


def test_feedback_rejects_invalid_or_misattributed_submissions(library):
    client,root,_=library
    lecture=next(row for row in client.get('/api/catalog').json()['items'] if row['id']=='lecture')
    asset=next(a for a in lecture['assets'] if a['kind']=='video')
    payload=dict(deck='lecture',path=asset['path'],version=asset['version'],text='Feedback')
    for changes,status in [({'text':'  '},400),({'text':'x'*10001},400),({'text':[]},400),
                           ({'deck':'other'},404),({'path':'../private.mp4'},404),
                           ({'version':'stale'},409),({'playback_seconds':-1},400),
                           ({'playback_seconds':True},400),({'playback_seconds':'12'},400)]:
        assert client.post('/api/feedback',json={**payload,**changes}).status_code==status
    assert client.post('/api/feedback',json=[]).status_code==400
    assert client.post('/api/feedback',content='{',headers={'content-type':'application/json'}).status_code==400
    assert client.post('/api/feedback',json=payload,headers={'origin':'http://another-site.invalid'}).status_code==403
    assert client.post('/api/feedback',data={'text':'form submission'}).status_code==415
    assert not (root.parent/(root.name+'-feedback')).exists()


def test_loose_previews_and_orphan_transcripts_are_not_lectures(library):
    client,root,data=library
    preview=root/'matrix-exponential-opening.mp4'
    preview.write_bytes(data)
    (root/'unregistered.mp4').write_bytes(data)
    (root/'unregistered.mp4.metadata.json').write_text(json.dumps(dict(deck='not-registered')))
    orphan=root/'orphan-narration';orphan.mkdir()
    (orphan/'presentation.txt').write_text('Preview narration')
    rows=client.get('/api/catalog').json()['items']
    assert not {'matrix-exponential-opening','not-registered','orphan'} & {r['id'] for r in rows}
    assert all(a['path']!=preview.name for row in rows for a in row['assets'])
    # Filtering the library preserves the artifact for direct inspection.
    assert preview.read_bytes()==data
    assert client.get('/files/'+preview.name).status_code==200
