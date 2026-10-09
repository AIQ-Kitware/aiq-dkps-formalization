"""Friday-only VTK video finale, without a static lead-in slide.

Manim Slides accepts an external movie as a single presentation slide via
``next_slide(src=...)``.  Do not ``play`` or ``wait`` before it: any rendered
animation becomes an unwanted extra slide before the eye-candy finale.
"""

from __future__ import annotations

from pathlib import Path

from dkvis.palette import OUTPUT_SUFFIX
from dkvis.slide_style import DeckSlide

ROOT = Path(__file__).resolve().parent.parent
ASSETS = ROOT / "media" / f"vtk3d{OUTPUT_SUFFIX}"
# New filename intentionally invalidates the earlier caption-less cached movie.
MOVIE = ASSETS / "finale-tilt-vtk-caption.mp4"


def prepare(refresh: bool = False) -> None:
    """Generate only the VTK video that this one-slide finale displays."""
    if refresh or not MOVIE.exists():
        from dkvis import vtk_sine_theta_3d as vtk3d

        MOVIE.parent.mkdir(parents=True, exist_ok=True)
        vtk3d.write_movie("finale-tilt", MOVIE)


class V01VTKFinale(DeckSlide):
    """Exactly one looping external-video slide; no still, title or lead-in."""

    title = ""
    kicker = ""
    section = ""

    def make_chrome(self):
        # The external movie already contains its labels and the VTK credit.
        # No footer/number/title should be typeset over (or before) it.
        return None

    def body(self) -> None:
        if not MOVIE.is_file():
            raise FileNotFoundError("Missing VTK finale video; render through dkvis.build_slides")
        # src creates the slide directly; never insert a FadeIn before it.
        self.say(
            "The final slide is a VTK rendering of the three-dimensional sine-theta model. "
            "The exact plane is range F zero and the trial plane range E zero. "
            "The trial plane tilts while the camera moves, and the movie loops.",
            src=MOVIE,
            loop=True,
        )
