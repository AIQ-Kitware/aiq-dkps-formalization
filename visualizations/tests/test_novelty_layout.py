"""Test the *actual layout plan* without importing Manim or rendering TeX.

This supplements the slide LaTeX test. The original handout had collisions
between groups with individually correct TeX: the intro prose overlapped the
header, the optimization note crossed the footer, smoothed results overlapped
the main theorem, and chart labels collided with the theorem panel. Keeping
these bounds tested prevents center-positioning from reintroducing those bugs.
"""

from __future__ import annotations

import ast
import math
from pathlib import Path

from dkvis.decks import get_deck
from dkvis.novelty_layout import BODY_TOP, LAYOUTS, resolved_region, validate_layouts

SOURCE = Path(__file__).resolve().parents[1] / "dkvis" / "slides_novelty.py"


def test_all_scene_layouts_are_in_frame_and_nonoverlapping():
    validate_layouts()
    assert set(LAYOUTS) == set(get_deck("novelty-tour").scene_names)
    for scene, slots in LAYOUTS.items():
        assert len(slots) >= 3, scene
        for name, r in slots.items():
            assert r.width > 0.35, (scene, name)
            assert r.height > 0.24, (scene, name)


def test_rendered_header_can_shrink_body_region():
    for scene, slots in LAYOUTS.items():
        if scene == "N00Title":
            continue  # Custom title page, no shared deck header.
        for key, region in slots.items():
            clamped = resolved_region(scene, key, content_top=1.65)
            if region.top == BODY_TOP:
                assert math.isclose(clamped.top, 1.53)
                assert clamped.height > 0.3
            else:
                assert clamped == region


def test_every_layout_slot_is_used_by_its_scene():
    source = ast.parse(SOURCE.read_text())
    for cls in (n for n in source.body if isinstance(n, ast.ClassDef) and n.name in LAYOUTS):
        text = ast.get_source_segment(SOURCE.read_text(), cls)
        assert text is not None
        for name in LAYOUTS[cls.name]:
            # N01 uses zip(("a", "b", "c"), cols) to apply its three cells.
            assert f'"{name}"' in text, (cls.name, name)
    assert "def place(slide:" in SOURCE.read_text()


def test_actual_placement_helper_fits_tall_and_wide_mobjects():
    """Exercise the real `place` implementation with geometry-only doubles.

    This deliberately extracts the function's AST so the test does not need
    Manim/LaTeX, but still detects accidentally removed width/height fitting.
    """
    source = ast.parse(SOURCE.read_text())
    func = next(n for n in source.body if isinstance(n, ast.FunctionDef) and n.name == "place")
    intro_type = type("N00Title", (), {})
    scope = {
        "DeckSlide": object,
        "N00Title": intro_type,
        "resolved_region": resolved_region,
    }
    exec(compile(ast.Module(body=[func], type_ignores=[]), str(SOURCE), "exec"), scope)
    place = scope["place"]

    class Dummy:
        def __init__(self):
            self.width = 22.0
            self.height = 13.0
            self.x = self.y = 0.0

        def scale(self, s):
            self.width *= s
            self.height *= s

        def move_to(self, center):
            self.x, self.y = center[:2]

        def get_left(self):
            return (self.x - self.width / 2, self.y, 0)

        def get_right(self):
            return (self.x + self.width / 2, self.y, 0)

        def get_bottom(self):
            return (self.x, self.y - self.height / 2, 0)

        def get_top(self):
            return (self.x, self.y + self.height / 2, 0)

    for name, regions in LAYOUTS.items():
        scene = intro_type() if name == "N00Title" else type(name, (), {"content_top": 1.65})()
        for slot in regions:
            cell = resolved_region(name, slot, None if name == "N00Title" else 1.65)
            for align_top in (False, True):
                obj = Dummy()
                assert place(scene, slot, obj, align_top=align_top) is obj
                assert obj.get_left()[0] >= cell.left - 1e-4
                assert obj.get_right()[0] <= cell.right + 1e-4
                assert obj.get_bottom()[1] >= cell.bottom - 1e-4
                assert obj.get_top()[1] <= cell.top + 1e-4
