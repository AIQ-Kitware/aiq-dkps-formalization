"""Exact scalar model and the journal color registry for the DK geometry slide.

This module has no Manim dependency, so its numerical and provenance checks
can be run without a graphics environment.
"""

from __future__ import annotations

from dataclasses import dataclass
import math
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PAPER_COLORS = ROOT / "papers/dk_formalization_journal/math_symbol_colors.tex"

# Different from the paper's 40-degree Figure 1: a near-alignment illustration.
TRIAL_ANGLE_DEGREES = 12.0
WANTED_EIGENVALUE = 1.9
COMPLEMENTARY_EIGENVALUE = 0.7

COLOR_KEYS = {
    "ink": "dkfg",
    "muted": "dkmuted",
    "ambient": "dkambient",
    "wanted": "dkwanted",
    "unwanted": "dkunwanted",
    "trial": "dktrial",
    "angle": "dksine",
    "residual": "dkresid",
    "gap": "dkgap",
}


def read_dk_journal_colors() -> dict[str, str]:
    """Read exact, current hex values from the paper's semantic registry."""
    content = PAPER_COLORS.read_text(encoding="utf8")
    values = dict(re.findall(
        r"\\definecolor\{(dk\w+)\}\{HTML\}\{([0-9a-fA-F]{6})\}",
        content,
    ))
    missing = set(COLOR_KEYS.values()) - values.keys()
    if missing:
        raise ValueError(f"Missing paper colors: {sorted(missing)}")
    return {role: "#" + values[name].upper() for role, name in COLOR_KEYS.items()}


@dataclass(frozen=True)
class SineThetaSlice:
    theta: float
    cosine: float
    sine: float
    trial_rayleigh: float
    unwanted_value: float
    gap: float
    residual_x: float
    residual_y: float


def compute_dk_rank_one_slice(angle_degrees: float = TRIAL_ANGLE_DEGREES) -> SineThetaSlice:
    """Calculate the paper-compatible 2D model used to position the drawing."""
    angle = math.radians(angle_degrees)
    c, s = math.cos(angle), math.sin(angle)
    rho = WANTED_EIGENVALUE * c * c + COMPLEMENTARY_EIGENVALUE * s * s
    return SineThetaSlice(
        theta=angle,
        cosine=c,
        sine=s,
        trial_rayleigh=rho,
        unwanted_value=COMPLEMENTARY_EIGENVALUE,
        gap=rho - COMPLEMENTARY_EIGENVALUE,
        residual_x=(WANTED_EIGENVALUE - rho) * c,
        residual_y=(COMPLEMENTARY_EIGENVALUE - rho) * s,
    )


def audit_dk_sine_theta_slice() -> SineThetaSlice:
    """Check the decomposition, residual identity, and gap in scalar coordinates."""
    s = compute_dk_rank_one_slice()
    tol = 1e-12
    assert 0 < s.theta < math.pi / 2
    assert s.gap > 0
    assert math.isclose(s.cosine**2 + s.sine**2, 1, abs_tol=tol)
    assert math.isclose(s.cosine * s.residual_x + s.sine * s.residual_y, 0, abs_tol=tol)
    # X(1)=sin(theta), F1* R(1)=residual_y.
    assert math.isclose((s.unwanted_value-s.trial_rayleigh)*s.sine, s.residual_y, abs_tol=tol)
    assert math.isclose(s.gap*s.sine, abs(s.residual_y), abs_tol=tol)
    assert abs(s.residual_y) <= math.hypot(s.residual_x, s.residual_y) + tol
    assert set(read_dk_journal_colors()) == set(COLOR_KEYS)
    return s


if __name__ == "__main__":
    m = audit_dk_sine_theta_slice()
    print(
        "PASS: angle={:.1f} deg, rho={:.9f}, delta={:.9f}, sin(theta)={:.9f}".format(
            math.degrees(m.theta), m.trial_rayleigh, m.gap, m.sine
        )
    )
    print(f"PASS: colors read from {PAPER_COLORS.relative_to(ROOT)}")
