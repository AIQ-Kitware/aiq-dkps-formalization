"""The deck palette, shared by the manim slides and the VTK scenes.

One color per mathematical role (see :mod:`dkvis.slide_style`).  Set
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
    "EXACT": "#5AA9FF",
    "TRIAL": "#FFC24B",
    "SINE": "#FF5CA8",
    "RESID": "#4ADE80",
    "GAP": "#B69CFF",
}

LIGHT = {
    "BG": "#FBFBF8",
    "FG": "#1B1F24",
    "MUTED": "#6B7280",
    "FAINT": "#D5D9DE",
    "PANEL": "#EEF0F2",
    "EXACT": "#1F6FD1",
    "TRIAL": "#C77C00",
    "SINE": "#D12A7B",
    "RESID": "#138A4B",
    "GAP": "#6E4BD8",
}

THEME = os.environ.get("DKVIS_THEME", "dark").lower()
PALETTE = LIGHT if THEME == "light" else DARK


def rgb(hex_value: str) -> tuple[float, float, float]:
    """``"#RRGGBB"`` to floats in ``[0, 1]``."""
    value = hex_value.lstrip("#")
    return tuple(int(value[i : i + 2], 16) / 255.0 for i in (0, 2, 4))
