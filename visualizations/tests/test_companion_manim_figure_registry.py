"""Cumulative slide expansion source/renderer compatibility checks."""
from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from dkvis.presentation.companion_geometry import FIGURE_KINDS, companion_figure_kind
from dkvis.presentation.companion_slides import CompanionSlideLibrary, SOURCE_DIR


def test_companion_figures_have_native_manim_geometry_registry():
    library = CompanionSlideLibrary()
    required = set()
    for row in library.catalog():
        source = json.loads((SOURCE_DIR / (row['id'] + '.json')).read_text())
        required.update(slide['diagram'] for slide in source['slides'] if slide.get('diagram'))
    assert required <= set(FIGURE_KINDS)
    assert all(companion_figure_kind(identifier) in
               {'angle', 'graph', 'spectrum', 'contour', 'block', 'kyfan',
                'norm', 'matrix', 'flow', 'matching', 'polar', 'abstract'}
               for identifier in required)


def test_manim_composer_has_native_geometry_and_browser_uses_rendered_frames():
    root = Path(__file__).resolve().parents[1]
    manim_source = (root / 'dkvis/presentation/companion_manim.py').read_text()
    html_source = (root / 'dkvis/presentation/companion_slides.py').read_text()
    assert 'class CompanionScene(Scene)' in manim_source
    assert 'MathTex(' in manim_source
    assert 'build_companion_geometry(' in manim_source
    assert 'SVGMobject(' not in manim_source
    assert 'tempconfig(' in manim_source
    assert 'render_slide_png' in html_source
    assert "f'data:{mime};base64,'" in html_source


def test_cumulative_editorial_inventory():
    library = CompanionSlideLibrary()
    stages = Counter(row['editorial_stage'] for row in library.catalog())
    assert stages['expanded'] >= 97
    assert stages['baseline'] >= 84
    assert stages['baseline'] + stages['expanded'] == len(library.catalog())
    for lecture in ('091250','091500','092250','099500'):
        assert len(library.list_for_lecture('g2:' + lecture)) == 1
    for start, end in [(30,37),(38,45),(46,53),(54,61),(62,69)]:
        for index in range(start, end+1):
            key=f'g2:{index:03d}000'
            deck=library.list_for_lecture(key)
            assert len(deck)==1
            assert deck[0]['editorial_stage']=='expanded'
