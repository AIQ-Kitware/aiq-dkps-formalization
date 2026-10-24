"""Fast regression checks for the standalone novelty Manim deck.

The old deck registry test merely parses the scene source.  That did not
catch a tab inside ``\\textbf`` or doubled ``\\\\emph``/``\\\\sin`` commands.  These
checks do not require Manim and can run before a lengthy scene render.
"""

from __future__ import annotations

import ast
import math
from pathlib import Path
import shutil
import subprocess

import pytest

from dkvis.notation import expand, latex_preamble
from dkvis.novelty_math import optimal_phase_three_halves

SOURCE = Path(__file__).resolve().parents[1] / "dkvis" / "slides_novelty.py"
HELPERS = {"tex", "math", "para", "wrapped_bullets", "piece_box", "threshold_strip"}


def _static_string(node: ast.expr) -> str | None:
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    if isinstance(node, ast.JoinedStr):
        # Manim's two dynamic plot captions contain only formatted angles.
        return "".join(
            part.value if isinstance(part, ast.Constant) else "80.0"
            for part in node.values
        )
    return None


def _tex_fragments() -> list[tuple[str, str]]:
    fragments = []
    tree = ast.parse(SOURCE.read_text())
    for call in ast.walk(tree):
        if not isinstance(call, ast.Call) or not isinstance(call.func, ast.Name):
            continue
        helper = call.func.id
        if helper not in HELPERS:
            continue
        if helper == "threshold_strip":
            nodes = [(arg, "text") for arg in call.args[:2]] + [
                (kw.value, "math") for kw in call.keywords if kw.arg == "tag"
            ]
        else:
            kind = "math" if helper in {"math", "piece_box"} else "text"
            nodes = [(arg, kind) for arg in call.args]
        for node, kind in nodes:
            body = _static_string(node)
            if body is not None:
                fragments.append((kind, body))
    # The N01 three-card contents are data in a local specification instead
    # of immediate arguments to wrapped_bullets(). Check their LaTeX as well.
    known_bodies = {body for _, body in fragments}
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            if (r"\textbf" in node.value or r"\sin" in node.value) and node.value not in known_bodies and node.value.count("{") == node.value.count("}"):
                fragments.append(("text", node.value))
                known_bodies.add(node.value)
    return fragments


def test_novelty_markup_has_no_accidental_escape_sequences():
    source = SOURCE.read_text()
    assert "\t" not in source
    for forbidden in (r"\\emph", r"\\sin", r"\\textbf"):
        assert forbidden not in source
    assert len(_tex_fragments()) >= 80


@pytest.mark.skipif(shutil.which("latex") is None, reason="TeX installation unavailable")
def test_novelty_static_tex_fragments_compile(tmp_path):
    preamble = (
        r"\documentclass{article}" + "\n"
        r"\usepackage{lmodern}" + "\n"
        r"\renewcommand{\familydefault}{\sfdefault}" + "\n"
        r"\usepackage{amsmath,amssymb,xcolor}" + "\n"
        r"\newcommand{\norm}[1]{\lVert #1\rVert}" + "\n"
        + latex_preamble() + "\n"
        r"\begin{document}" + "\n"
    )
    chunks = [preamble]
    for index, (kind, body) in enumerate(_tex_fragments()):
        chunks.append(f"\\typeout{{NOVELTY-TEX-{index}}}\n")
        expanded = expand(body)
        if kind == "math":
            chunks.append(r"\[" + expanded + r"\]" + "\n")
        else:
            chunks.append(r"\noindent " + expanded + r"\par" + "\n")
    chunks.append(r"\end{document}" + "\n")
    (tmp_path / "novelty.tex").write_text("".join(chunks))
    result = subprocess.run(
        ["latex", "-halt-on-error", "-interaction=nonstopmode", "novelty.tex"],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert result.returncode == 0, result.stdout[-3000:]


def _phase_power(theta: float, delta: float) -> float:
    return (2.0 * math.sin((theta + delta) / 2)) ** 1.5 + (
        2.0 * math.sin((theta - delta) / 2)
    ) ** 1.5


def test_three_halves_phase_avoids_out_of_domain_acos():
    for degrees in (0, 25, 45, 65, math.degrees(math.acos(1 / 3))):
        assert optimal_phase_three_halves(math.radians(degrees)) == 0.0


def test_three_halves_phase_supercritical_is_global_scalar_minimum():
    theta = math.radians(80.0)
    minimum_phase = optimal_phase_three_halves(theta)
    assert 0 < minimum_phase < theta
    cost = _phase_power(theta, minimum_phase)
    for i in range(1001):
        assert cost <= _phase_power(theta, theta * i / 1000) + 1e-9


def test_three_halves_phase_rejects_invalid_angles():
    for theta in (-0.1, math.pi, math.nan, math.inf):
        with pytest.raises(ValueError):
            optimal_phase_three_halves(theta)
