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
    # Integration tests for Manim imagery use a tiny PNG stub to avoid slow rendering.
    from dkvis.presentation import companion_slides as mod
    mod.render_slide_png = lambda deck, slide, index, count, cache_dir=None: b'\x89PNG\r\n\x1a\n'
    assert library.build(deck['id'])['built']
    html = library.rendered(deck['id']).read_text(encoding='utf8')
    assert html.count('<section class="slide slide--') == 12
    assert 'squared displacement' in html.lower()
    assert html.count('data:image/png;base64,') == 12


def test_reader_integration_patch_is_purely_targeted():
    source = (Path(__file__).resolve().parents[1] / 'dkvis/presentation/audio_library.py').read_text(encoding='utf8')
    assert "self.sources / 'track.json'" in source
    assert "return [paths[name] for name in names]" in source
    assert 'G3 listening path and transcript inventory differ' in source


def test_g3_audit_cli_runs_from_visualizations_directory():
    import subprocess
    import sys
    root = Path(__file__).resolve().parents[1]
    completed = subprocess.run(
        [sys.executable, 'tools/audit_g3_presentation.py'],
        cwd=root, capture_output=True, text=True, timeout=30, check=False,
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert '27 recordings' in completed.stdout
    assert '0 issue(s)' in completed.stdout


def test_g3_prop43_explains_singular_value_minmax_at_first_use():
    source = (PAPER_DIRECTORY / '018500-whole-space-squared-displacement-proposition-4-3.md').read_text(encoding='utf8')
    assert 'Courant–Fischer eigenvalue principle to the positive Gram operator' in source
    assert 'then taking square roots of its eigenvalues' in source
