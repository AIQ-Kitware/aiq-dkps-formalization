"""Regression tests for the G3 Proposition 4.3 and listening-order repair."""
import json
from pathlib import Path

from dkvis.presentation.audio_library import AudioLectureHub, PAPER_DIRECTORY
from dkvis.presentation.companion_slides import CompanionSlideLibrary
from dkvis.presentation.course_graph import build_course_graph
from tools.audit_g3_presentation import audit_g3_presentation_contract


def test_g3_repaired_order_and_audio_catalog(tmp_path):
    plan = json.loads((PAPER_DIRECTORY / 'track.json').read_text(encoding='utf8'))
    ids = [r['id'] for r in plan['lectures']]
    assert ids[17:21] == ['020000','021000','022000','023000']
    assert ids[-6:] == ['017000','018000','018500','019000','024000','025000']
    graph = build_course_graph()
    assert graph['tracks'][2]['path'] == ['g3:' + ident for ident in ids]
    hub = AudioLectureHub(cache=tmp_path/'cache', profile='kokoro',
                          sender=lambda *args: None)
    try:
        assert [row['id'] for row in hub.catalog('g3')] == ids
        assert hub.detail('018500','g3')['words'] > 1200
    finally:
        hub.close()


def test_g3_narration_and_new_companion_are_standalone(tmp_path):
    contract = audit_g3_presentation_contract()
    assert contract['lecture_count'] == 27, contract
    assert contract['issues'] == [], contract
    library = CompanionSlideLibrary(cache=tmp_path/'slide-cache')
    deck = library.status('g3-018500-whole-space-squared-displacement')
    assert deck['slide_count'] == 12
    assert deck['editorial_stage'] == 'expanded'
    assert not deck['needs_expansion']
    assert library.build(deck['id'])['built']
    html = library.rendered(deck['id']).read_text(encoding='utf8')
    assert html.count('<section class="slide slide--') == 12
    assert 'squared displacement' in html.lower()
    assert 'squared-displacement-prefix' not in html  # SVG is embedded, no image URL.
    assert '<svg' in html


def test_reader_integration_patch_is_purely_targeted():
    source = (Path(__file__).resolve().parents[1] / 'dkvis/presentation/audio_library.py').read_text(encoding='utf8')
    assert "self.sources / 'track.json'" in source
    assert "return [paths[name] for name in names]" in source
    assert 'G3 listening path and transcript inventory differ' in source
