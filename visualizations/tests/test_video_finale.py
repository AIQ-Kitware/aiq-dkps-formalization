"""Structural tests: a movie-backed finale must not create a static lead-in.

Do not assert text, labels, or slide copy. Those are editorial details.
"""

import ast
from pathlib import Path

from dkvis.build_slides import handout_frame_file
from dkvis.decks import get_deck


def test_friday_ends_with_one_vtk_scene_after_summary():
    names = get_deck("friday").scene_names
    assert names[-2:] == ["S14Summary", "V01VTKFinale"]
    assert "V00Manim3DFinale" not in names


def test_vtk_finale_has_only_one_external_video_build():
    path = Path(__file__).resolve().parents[1] / "dkvis/slides_vtk_finale.py"
    tree = ast.parse(path.read_text())
    cls = next(node for node in tree.body
               if isinstance(node, ast.ClassDef) and node.name == "V01VTKFinale")
    body = next(node for node in cls.body
                if isinstance(node, ast.FunctionDef) and node.name == "body")
    calls = [node for node in ast.walk(body) if isinstance(node, ast.Call)]
    slide_calls = [node for node in calls if isinstance(node.func, ast.Attribute)
                   and isinstance(node.func.value, ast.Name)
                   and node.func.value.id == "self"]
    # No `play`, `wait`, `add` or `next_slide` before the external-video build.
    assert [call.func.attr for call in slide_calls] == ["say"]
    say = slide_calls[0]
    kwargs = {arg.arg: arg.value for arg in say.keywords}
    assert isinstance(kwargs["src"], ast.Name)
    assert kwargs["src"].id == "MOVIE"
    assert isinstance(kwargs["loop"], ast.Constant)
    assert kwargs["loop"].value is True


def test_handout_selects_a_movie_frame_for_src_only_scene():
    assert handout_frame_file([{"file": "movie.mp4", "src": "movie.mp4"}]) == "movie.mp4"
    assert handout_frame_file([
        {"file": "drawn.mp4", "src": None},
        {"file": "movie.mp4", "src": "movie.mp4"},
    ]) == "drawn.mp4"
