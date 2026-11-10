"""Cumulative slide expansion source/renderer compatibility checks."""
from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from xml.etree import ElementTree

from dkvis.presentation.companion_figures import ADDITIONAL_FIGURES, LEGACY_FIGURES, figure_svg
from dkvis.presentation.companion_slides import CompanionSlideLibrary, SOURCE_DIR


def test_expanded_slide_figures_are_available_without_tracked_svg_files():
    library = CompanionSlideLibrary()
    required = set()
    for row in library.catalog():
        if row['editorial_stage'] != 'expanded':
            continue
        source = json.loads((SOURCE_DIR / (row['id'] + '.json')).read_text())
        required.update(slide['diagram'] for slide in source['slides'] if slide.get('diagram'))
    known = set(LEGACY_FIGURES) | set(ADDITIONAL_FIGURES)
    pilot = {'angle','rotation','orthogonal','spectrum','clusters','projection',
             'induction','residual','sylvester','families','matching','roadmap'}
    assert required <= known | pilot, sorted(required - known - pilot)
    for kind in required:
        assert ElementTree.fromstring(figure_svg(kind)).tag.endswith('svg')


def test_manim_composer_is_source_owned_and_browser_uses_rendered_frames():
    root = Path(__file__).resolve().parents[1]
    manim_source = (root/'dkvis/presentation/companion_manim.py').read_text()
    html_source = (root/'dkvis/presentation/companion_slides.py').read_text()
    assert 'class CompanionScene(Scene)' in manim_source
    assert 'MathTex(' in manim_source
    assert 'SVGMobject(' in manim_source
    assert 'tempconfig(' in manim_source
    assert 'data:image/png;base64,' not in manim_source
    assert 'render_slide_png' in html_source
    assert "f'data:{mime};base64,'" in html_source


def test_cumulative_editorial_inventory():
    library = CompanionSlideLibrary()
    stages = Counter(row['editorial_stage'] for row in library.catalog())
    assert stages['expanded'] >= 97
    assert stages['baseline'] <= 80
    for start, end in [(30,37),(38,45),(46,53),(54,61),(62,69)]:
        for index in range(start, end+1):
            key=f'g2:{index:03d}000'
            deck=library.list_for_lecture(key)
            assert len(deck)==1
            assert deck[0]['editorial_stage']=='expanded'
