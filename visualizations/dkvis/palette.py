"""The deck palette, shared by the manim slides and the VTK scenes.

One color per mathematical role (see :mod:`dkvis.slide_style`): blue is what
we want, amber what we computed, cyan the exact part we do not want, pink how
much of the computation points into it, green the residual that exposes that,
violet the separation that keeps it from hiding.  Which role each *symbol* plays
is set in :mod:`dkvis.notation`.

A second, quieter tier says where an operator comes from, each a muted relative
of its eigenvectors' color: ``OLD`` (tan, the old ``A``, whose eigenvectors are
the amber trial), ``CURRENT`` (steel, ``Ã``, whose eigenvectors are the blue and
cyan wanted and unwanted directions) and ``PERTURB`` (vermilion, ``H``, the one new
hue).  ``REFUTED`` (red) marks a claim shown false and nothing else; it is close
to vermilion, so the two do not share a slide.  Every other pair of colors here is at
least 15 apart in CIEDE2000 in both themes; check a new color against all of
them before adding it.  ``MUTED`` and ``FAINT`` are
presentation only (secondary labels, guides) and never carry a role.  Set
``DKVIS_THEME=light`` for the light variant.
"""

from __future__ import annotations

import os

DARK = {
    "BG": "#0E1319",
    "FG": "#ECEFF3",
    "MUTED": "#8B95A3",
    "FAINT": "#2A323D",
    "PANEL": "#161D26",
    "WANTED": "#5AA9FF",
    "UNWANTED": "#31C7D9",
    "TRIAL": "#FFC24B",
    "SINE": "#FF5CA8",
    "RESID": "#4ADE80",
    "GAP": "#B69CFF",
    "OLD": "#A38848",
    "CURRENT": "#4096B2",
    "PERTURB": "#F26B3A",
    "REFUTED": "#E8484E",
}

LIGHT = {
    "BG": "#FBFBF8",
    "FG": "#1B1F24",
    "MUTED": "#6B7280",
    "FAINT": "#D5D9DE",
    "PANEL": "#EEF0F2",
    "WANTED": "#1F6FD1",
    "UNWANTED": "#007C91",
    "TRIAL": "#C77C00",
    "SINE": "#D12A7B",
    "RESID": "#138A4B",
    "GAP": "#6E4BD8",
    "OLD": "#705519",
    "CURRENT": "#054669",
    "PERTURB": "#D9541E",
    "REFUTED": "#C62828",
}

THEMES = {"dark": DARK, "light": LIGHT}
THEME = os.environ.get("DKVIS_THEME", "dark").lower()
if THEME not in THEMES:
    raise ValueError(f"DKVIS_THEME={THEME!r}: expected one of {', '.join(THEMES)}")
PALETTE = THEMES[THEME]
#: Appended to every output name (``slides-<deck>-light/``, ``renders/<deck>-light.html``,
#: ``media/vtk3d-light/``) so the themes never overwrite each other's renders.
OUTPUT_SUFFIX = "" if THEME == "dark" else f"-{THEME}"


def tint(hex_value: str, amount: float = 0.12) -> str:
    """``hex_value`` mixed into the background: a panel surface in that role's tint."""
    bg = rgb(PALETTE["BG"])
    mixed = [amount * c + (1 - amount) * b for c, b in zip(rgb(hex_value), bg)]
    return "#" + "".join(f"{round(255 * c):02X}" for c in mixed)


def rgb(hex_value: str) -> tuple[float, float, float]:
    """``"#RRGGBB"`` to floats in ``[0, 1]``."""
    value = hex_value.lstrip("#")
    return tuple(int(value[i : i + 2], 16) / 255.0 for i in (0, 2, 4))
