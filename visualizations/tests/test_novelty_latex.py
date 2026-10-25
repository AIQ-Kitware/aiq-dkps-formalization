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


def test_smoothed_two_by_two_example_matches_exact_formula():
    from dkvis.novelty_math import (
        canonical_smoothed_cost, optimal_smoothed_cost,
        optimal_smoothed_phase, smoothed_cutoff, smoothing_radius,
    )

    tau = 1.0
    eta = smoothing_radius(tau)
    threshold = smoothed_cutoff(tau)
    assert math.isclose(eta, (1 + math.sqrt(5)) / 2, abs_tol=1e-12)
    assert math.isclose(math.degrees(threshold), 67.54448480141833, abs_tol=1e-8)
    low = math.radians(45)
    high = math.radians(80)
    assert low < threshold < high
    assert optimal_smoothed_phase(tau, low) == 0
    assert math.isclose(math.degrees(optimal_smoothed_phase(tau, high)), 62.95971681332988, abs_tol=1e-8)
    assert math.isclose(optimal_smoothed_cost(tau, low), canonical_smoothed_cost(tau, low), abs_tol=1e-10)
    assert math.isclose(optimal_smoothed_cost(tau, low), 0.5185602534995306, abs_tol=1e-8)
    assert math.isclose(optimal_smoothed_cost(tau, high), 1.1869048335163286, abs_tol=1e-8)
    assert math.isclose(canonical_smoothed_cost(tau, high), 1.257424531537846, abs_tol=1e-8)
    assert optimal_smoothed_cost(tau, high) < canonical_smoothed_cost(tau, high)
    assert math.sin(low) < math.sqrt(1 - eta ** -4) < math.sin(high)


def test_critical_phase_gap_is_fourth_order_not_second():
    from dkvis.novelty_math import critical_phase_excess

    tau = 1.0
    q1, q2, q3 = (critical_phase_excess(tau, t) for t in (0.2, 0.1, 0.05))
    assert q1 > q2 > q3 > 0
    # Halving the phase asymptotically divides the excess by sixteen.
    assert abs(q1 / q2 - 16) < 0.1
    assert abs(q2 / q3 - 16) < 0.1
    assert q3 / 0.05 ** 2 < q2 / 0.1 ** 2


def test_smoothed_scalar_illustrations_reject_bad_inputs():
    from dkvis.novelty_math import (
        canonical_smoothed_cost, optimal_smoothed_cost,
        optimal_smoothed_phase, smoothing_radius,
    )

    for tau in (-1, 0, float('nan'), float('inf')):
        with pytest.raises(ValueError):
            smoothing_radius(tau)
    for theta in (-0.1, math.pi, float('nan'), float('inf')):
        with pytest.raises(ValueError):
            canonical_smoothed_cost(1, theta)
        with pytest.raises(ValueError):
            optimal_smoothed_cost(1, theta)
        with pytest.raises(ValueError):
            optimal_smoothed_phase(1, theta)


def test_transport_roles_match_manuscript_without_changing_legacy_keys():
    from dkvis.notation import SYMBOLS, concept_color
    from dkvis.palette import PALETTE

    assert SYMBOLS["Usource"] == (r"U", "trial")
    assert SYMBOLS["Vtarget"] == (r"V", "wanted")
    assert SYMBOLS["ProjSource"] == (r"P_U", "trial")
    assert SYMBOLS["ProjTarget"] == (r"P_V", "wanted")
    assert concept_color("Usource") == PALETTE["TRIAL"]
    assert concept_color("Vtarget") == PALETTE["WANTED"]
    # Historical sine-theta slides use U exact and V trial; keep them stable.
    assert SYMBOLS["U"][1] == "wanted"
    assert SYMBOLS["V"][1] == "trial"
    assert r"\sym{U}" not in SOURCE.read_text()
    assert r"\sym{V}" not in SOURCE.read_text()


def test_unrestricted_schatten_two_angle_example_matches_verified_formula():
    from dkvis.novelty_math import (
        schatten_two_angle_example_three_halves,
        schatten_phase_power_three_halves,
    )
    z = schatten_two_angle_example_three_halves()
    assert math.isclose(z["cutoff_deg"], 70.52877936550931, abs_tol=1e-8)
    assert z["low_phase_deg"] == 0.0
    assert math.isclose(z["high_phase_deg"], 74.57097698955464, abs_tol=1e-8)
    assert math.isclose(z["canonical_sum"], 4.254419090242005, abs_tol=1e-8)
    assert math.isclose(z["global_sum"], 4.093350305605767, abs_tol=1e-8)
    assert z["global_sum"] < z["canonical_sum"]
    theta = math.radians(80)
    attained = schatten_phase_power_three_halves(theta, math.radians(z["high_phase_deg"]))
    for k in range(501):
        assert attained <= schatten_phase_power_three_halves(theta, theta * k / 500) + 1e-9
    for theta, delta in [(-1, 0), (math.pi, 0), (0.5, -0.1), (0.5, 0.6)]:
        with pytest.raises(ValueError):
            schatten_phase_power_three_halves(theta, delta)


def test_simple_active_schatten_sign_families():
    from dkvis.novelty_math import (
        schatten_simple_active_signs_three_halves,
        schatten_signed_phase_power_three_halves,
    )
    z = schatten_simple_active_signs_three_halves()
    assert z["angles_deg"] == (75.0, 80.0)
    assert len(z["choices"]) == 4
    assert len(set(z["choices"])) == 4
    assert min(z["phases_deg"]) > 0
    assert max(z["costs"]) - min(z["costs"]) < 1e-12
    assert math.isclose(z["costs"][0], 5.398844412803351, abs_tol=1e-10)
    for (a, b), cost in zip(z["choices"], z["costs"]):
        assert math.isclose(cost,
            schatten_signed_phase_power_three_halves(math.radians(75), a)
            + schatten_signed_phase_power_three_halves(math.radians(80), b),
            abs_tol=1e-12)
    for phase in (-math.pi, math.pi, float('nan'), float('inf')):
        with pytest.raises(ValueError):
            schatten_signed_phase_power_three_halves(math.radians(80), phase)
