"""G2 038000–045000 companion decks: substantive and renderable upgrades."""
import json
from pathlib import Path
import subprocess
import sys
from xml.etree import ElementTree

from dkvis.presentation.companion_figures import figure_svg
from dkvis.presentation.companion_slides import CompanionSlideLibrary, SOURCE_DIR


BATCH_NODES = tuple(f'g2:{n:03}000' for n in range(38, 46))


def test_g2_batch2_math_figures_and_sources():
    entries = {r['lecture_nodes'][0]: r for r in CompanionSlideLibrary().catalog()}
    for node in BATCH_NODES:
        entry = entries[node]
        assert entry['editorial_stage'] == 'expanded'
        assert not entry['needs_expansion']
        deck = json.loads((SOURCE_DIR / (entry['id'] + '.json')).read_text())
        lecture = SOURCE_DIR.parent / deck['source_lecture']
        assert '<!-- BEGIN SPOKEN LECTURE -->' in lecture.read_text()
        assert len(deck['slides']) >= 9
        assert len({s['id'] for s in deck['slides']}) == len(deck['slides'])
        assert sum(bool(s.get('mathtex')) for s in deck['slides']) >= 4
        assert sum(bool(s.get('diagram')) for s in deck['slides']) >= 4
        assert all(not s['eyebrow'].endswith('first-pass outline') for s in deck['slides'])
        assert all(len(' '.join((s['lead'], *s['body'])).split()) >= 38 for s in deck['slides'])
        for slide in deck['slides']:
            if fig := slide.get('diagram'):
                assert ElementTree.fromstring(figure_svg(fig)).tag.endswith('svg'), (node, fig)


def test_g2_batch2_renders_independently(tmp_path, monkeypatch):
    from dkvis.presentation import companion_slides as renderer
    monkeypatch.setattr(renderer, 'render_slide_png', lambda deck, slide, index, count, cache_dir=None: b'PNG')
    library = CompanionSlideLibrary(SOURCE_DIR, tmp_path/'cache')
    for node in BATCH_NODES:
        entry = next(e for e in library.catalog() if node in e['lecture_nodes'])
        result = library.build(entry['id'])
        html = library.rendered(entry['id']).read_text()
        assert result['slide_count'] >= 9
        assert html.count('<section class="slide slide--') == result['slide_count']
        assert 'BASELINE · NEEDS EXPANSION' not in html
        assert '<script src=' not in html
        assert 'data:image/png;base64,' in html


def test_g2_batch2_promotion_cli_is_idempotent():
    root = Path(__file__).resolve().parents[1]
    action = subprocess.run([sys.executable, str(root/'tools/promote_g2_038000_045000.py'), '--check'],
                            cwd=root, capture_output=True, text=True)
    assert action.returncode == 0, action.stdout + action.stderr


def test_g2_batch2_manifest_promotion_keeps_other_rows(tmp_path, monkeypatch):
    import shutil
    from tools import promote_g2_038000_045000 as promotion

    source_manifest = json.loads((SOURCE_DIR / 'manifest.json').read_text())
    target_manifest = json.loads(json.dumps(source_manifest))
    for entry in target_manifest['decks']:
        if entry['lecture_nodes'][0] in BATCH_NODES:
            entry['editorial_stage'] = 'baseline'
    target_manifest['decks'][0]['other_agent_field'] = {'preserve': ['yes']}

    target_root = tmp_path / 'companion-slides'
    target_root.mkdir()
    (target_root / 'manifest.json').write_text(json.dumps(target_manifest, indent=2))
    for entry in target_manifest['decks']:
        if entry['lecture_nodes'][0] in BATCH_NODES:
            shutil.copy2(SOURCE_DIR / entry['source'], target_root / entry['source'])

    monkeypatch.setattr(promotion, 'COMPANION_DIR', target_root)
    assert len(promotion.promote_g2_038000_045000_manifest(write=False)) == 8
    assert len(promotion.promote_g2_038000_045000_manifest(write=True)) == 8
    assert promotion.promote_g2_038000_045000_manifest(write=False) == []

    result = json.loads((target_root / 'manifest.json').read_text())
    assert result['decks'][0]['other_agent_field'] == {'preserve': ['yes']}
    original_unrelated = [e for e in target_manifest['decks'] if e['lecture_nodes'][0] not in BATCH_NODES]
    resulting_unrelated = [e for e in result['decks'] if e['lecture_nodes'][0] not in BATCH_NODES]
    assert original_unrelated == resulting_unrelated
