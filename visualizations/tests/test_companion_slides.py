"""Companion slides remain readable alone and build independently of TTS."""
import base64
import json
from pathlib import Path

import pytest
from starlette.testclient import TestClient

from dkvis.presentation.companion_slides import CompanionSlideLibrary, SOURCE_DIR
from dkvis.presentation.serve import create_app


TINY_PNG = base64.b64decode(
    'iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO+yq6cAAAAASUVORK5CYII='
)


@pytest.fixture
def stub_slide_renderer(monkeypatch):
    """Keep integration tests fast; deck HTML should not require Manim here."""
    from dkvis.presentation import companion_slides as mod
    monkeypatch.setattr(mod, 'render_slide_png',
                        lambda deck, slide, index, count, cache_dir=None: TINY_PNG)


def test_first_two_g3_decks_are_readable_source_files():
    lib = CompanionSlideLibrary()
    entries = lib.catalog()
    assert [r['id'] for r in entries[:2]] == ['dkps-fast-path', 'finite-spectral-picture']
    assert len(entries) >= 27
    assert [r['slide_count'] for r in entries[:2]] == [12, 13]
    assert [r['lecture_nodes'] for r in entries[:2]] == [['g3:000000'], ['g3:001000']]
    assert {r['lecture_nodes'][0] for r in entries if r['lecture_nodes'][0].startswith('g3:')} == {f'g3:{n:03}000' for n in range(26)} | {'g3:018500'}
    for entry in (entry for entry in entries if entry['lecture_nodes'][0].startswith('g3:')):
        source = json.loads((SOURCE_DIR / f'{entry["id"]}.json').read_text(encoding='utf-8'))
        assert len({s['id'] for s in source['slides']}) == entry['slide_count']
        assert all(s['title'] and s['lead'] and (s['body'] or len(s['lead'].split()) >= 20) for s in source['slides'])
        if entry['id'] in {'dkps-fast-path', 'finite-spectral-picture'}:
            assert all(s.get('takeaway') for s in source['slides'])
        else:
            assert 10 <= entry['slide_count'] <= 25
            assert sum(bool(s.get('diagram')) for s in source['slides']) >= 4
        assert all(len((' '.join([s['lead'], *s['body'], *s.get('bullets', []), s.get('takeaway', '')])).split()) >= 35 for s in source['slides'])
    intro = (SOURCE_DIR / 'dkps-fast-path.json').read_text()
    theorem = (SOURCE_DIR / 'finite-spectral-picture.json').read_text()
    assert 'Sylvester' in intro and 'counterexample' in intro and 'matching' in intro
    assert 'induction' in theorem and 'P₃' in theorem and 'symmetric' in theorem


def test_build_cache_and_source_revision(tmp_path, stub_slide_renderer):
    source = tmp_path / 'source'
    source.mkdir()
    for f in SOURCE_DIR.glob('*.json'):
        (source / f.name).write_bytes(f.read_bytes())
    lib = CompanionSlideLibrary(source, tmp_path / 'cache')
    assert not lib.status('dkps-fast-path')['built']
    with pytest.raises(FileNotFoundError):
        lib.rendered('dkps-fast-path')
    first = lib.build('dkps-fast-path')
    assert first['built']
    rendered = lib.rendered('dkps-fast-path')
    raw = rendered.read_text(encoding='utf-8')
    assert raw.count('<section class="slide slide--image"') == 12
    assert raw.count('data:image/png;base64,') == 12
    assert 'No audio required' not in raw
    assert 'The stability question' in raw
    assert 'cdn.' not in raw and '<script src=' not in raw
    assert lib.build('dkps-fast-path')['built']
    assert rendered == lib.rendered('dkps-fast-path')
    src = source / 'dkps-fast-path.json'
    data = json.loads(src.read_text())
    data['slides'][0]['lead'] = 'New explanatory heading'
    src.write_text(json.dumps(data), encoding='utf-8')
    assert not lib.status('dkps-fast-path')['built']
    again = lib.build('dkps-fast-path')
    assert again['built']
    assert lib.rendered('dkps-fast-path') != rendered
    assert 'New explanatory heading' in lib.rendered('dkps-fast-path').read_text()


def test_html_escaping_of_authored_slide_text(stub_slide_renderer):
    from dkvis.presentation.companion_slides import render_html
    data = json.loads((SOURCE_DIR / 'finite-spectral-picture.json').read_text())
    data['slides'][0]['lead'] = '<script>alert(1)</script>'
    rendered = render_html(data)
    assert '&lt;script&gt;alert(1)&lt;/script&gt;' in rendered
    assert '<script>alert(1)</script>' not in rendered


def test_companion_api_and_lecture_associations(tmp_path, stub_slide_renderer):
    renders = tmp_path / 'renders'
    renders.mkdir()
    lib = CompanionSlideLibrary(SOURCE_DIR, tmp_path / 'slide-cache')
    with TestClient(create_app(renders, slide_library=lib)) as client:
        response = client.get('/api/slide-decks')
        assert response.status_code == 200
        assert len(response.json()['items']) >= 27
        node = client.get('/api/course-graph').json()['nodes']['g3:000000']
        assert node['companion_slides'] == ['dkps-fast-path']
        assert client.get('/api/course-graph').json()['nodes']['g2:000000']['companion_slides']
        lecture = client.get('/api/audio-lectures/000000?track=g3').json()
        assert lecture['companion_slides'][0]['title'] == 'A fast path to Davis–Kahan'
        assert not lecture['companion_slides'][0]['built']
        assert client.get('/slide-decks/dkps-fast-path').status_code == 409
        assert client.get('/api/slide-decks/missing').status_code == 404
        assert client.post('/api/slide-decks/missing/build').status_code == 404
        assert client.post('/api/slide-decks/dkps-fast-path/build', headers={'origin': 'https://malicious.invalid'}).status_code == 403
        built = client.post('/api/slide-decks/dkps-fast-path/build')
        assert built.status_code == 200 and built.json()['built']
        page = client.get('/slide-decks/dkps-fast-path')
        assert page.status_code == 200
        assert 'text/html' in page.headers['content-type']
        assert 'The stability question' in page.text
        result = client.get('/api/slide-decks/dkps-fast-path/download')
        assert result.status_code == 200 and 'attachment' in result.headers['content-disposition']
        assert client.get('/api/audio-lectures/000000?track=g3').json()['companion_slides'][0]['built']
        assert client.get('/api/audio-lectures/001000?track=g2').json()['companion_slides']


def test_reader_exposes_slide_controls_before_build():
    reader = (Path(__file__).parents[1] / 'dkvis/presentation/audio_library.html').read_text()
    assert 'id="slidesPanel"' in reader
    assert 'id="toggleSlides"' in reader
    assert 'id="buildSlides"' in reader
    assert 'id="slidesFrame"' in reader
    assert '.learning-layout:not(.has-slides) .slides-panel{display:none}' not in reader
    assert "resetSlides(doc)" in reader
    assert '.learning-layout.has-slides{display:flex;flex-direction:column' in reader
    assert 'article:has(.learning-layout.has-slides){max-width:none' in reader
    assert '.slides-panel iframe{display:block;width:100%;height:auto;aspect-ratio:16/9' in reader
    assert 'grid-template-columns:minmax(420px' not in reader
    assert reader.index('id="slidesPanel"') < reader.index('class="transcript-col"')


def test_all_g3_companions_render_as_local_image_decks(tmp_path, stub_slide_renderer):
    lib = CompanionSlideLibrary(SOURCE_DIR, tmp_path / 'cache')
    for row in lib.catalog():
        status = lib.build(row['id'])
        html = lib.rendered(row['id']).read_text(encoding='utf8')
        assert status['built']
        assert html.count('<section class="slide slide--image"') == status['slide_count']
        assert html.count('data:image/png;base64,') == status['slide_count']
        assert '<script src=' not in html and '<link rel="stylesheet"' not in html


def test_new_g3_decks_link_to_graph_and_audio_api(tmp_path, stub_slide_renderer):
    source = CompanionSlideLibrary(SOURCE_DIR, tmp_path / 'cache')
    renders = tmp_path / 'renders'
    renders.mkdir()
    with TestClient(create_app(renders, slide_library=source)) as client:
        for lecture in ['002000', '004000', '008000', '020000', '024000', '025000']:
            node = client.get('/api/course-graph').json()['nodes']['g3:' + lecture]
            assert len(node['companion_slides']) == 1
            entry = client.get('/api/audio-lectures/' + lecture + '?track=g3').json()
            assert entry['companion_slides'][0]['id'] == node['companion_slides'][0]
            ident = node['companion_slides'][0]
            assert client.post('/api/slide-decks/' + ident + '/build').status_code == 200
            assert client.get('/slide-decks/' + ident).status_code == 200


def test_manim_slide_html_uses_images_not_raw_formula_text(stub_slide_renderer):
    from dkvis.presentation.companion_slides import render_html
    deck = json.loads((SOURCE_DIR / 'dkps-fast-path.json').read_text(encoding='utf8'))
    output = render_html(deck)
    assert output.count('class="slide-image"') == len(deck['slides'])
    assert output.count('data:image/png;base64,') == len(deck['slides'])
    assert '<script src=' not in output
    assert deck['slides'][1]['mathtex'] not in output
