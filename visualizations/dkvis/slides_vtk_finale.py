"""Friday-only VTK closing slide (adds a scene, does not replace the summary).

Reuses the mathematical model and offscreen renderer from vtk_sine_theta_3d.
Unlike the longer 3D study deck, it only prepares the still + loop it displays.
"""

from __future__ import annotations

from pathlib import Path

from manim import FadeIn, ImageMobject

from dkvis.palette import OUTPUT_SUFFIX
from dkvis.slide_style import DeckSlide

ROOT = Path(__file__).resolve().parent.parent
ASSETS = ROOT / "media" / f"vtk3d{OUTPUT_SUFFIX}"


def prepare(refresh: bool = False) -> None:
    """Build just the needed VTK assets, reusing cached study-deck media."""
    still = ASSETS / "finale-residual-e0f0.png"
    movie = ASSETS / "finale-tilt.mp4"
    if (refresh or not still.exists()) or (refresh or not movie.exists()):
        from dkvis import vtk_sine_theta_3d as vtk3d
        ASSETS.mkdir(parents=True, exist_ok=True)
        if refresh or not still.exists():
            vtk3d.write_still("still-residual", still, width=1800, height=1000)
        if refresh or not movie.exists():
            vtk3d.write_movie("finale-tilt", movie)


class V01VTKFinale(DeckSlide):
    title = "A final look: the sine-theta geometry in 3D"
    kicker = r"VTK rendering of $\operatorname{range}(\sym{E0})$, $\operatorname{range}(\sym{F0})$, residuals, and the ellipsoid"
    section = "Davis--Kahan: a geometric closing view"

    def body(self) -> None:
        still = ASSETS / "finale-residual-e0f0.png"
        movie = ASSETS / "finale-tilt.mp4"
        if not still.is_file() or not movie.is_file():
            raise FileNotFoundError("Missing VTK finale assets; build with dkvis.build_slides to run prepare()")
        image = ImageMobject(str(still))
        # The finale still is 1800x1000; retain aspect ratio and keep clear of
        # the deck chrome. The looping video itself is full-frame.
        image.height = 5.35
        image.move_to([0, -0.43, 0])
        if image.width > 11.0:
            image.scale_to_fit_width(11.0)
        self.say(
            "One final look at the actual VTK visualization. This is the three-dimensional "
            "sine-theta model, not a projection of the four-dimensional Proposition 4.4 "
            "counterexample. The labels now match the deck notation: the exact plane is "
            "range F zero, the trial plane is range E zero, and the residual geometry comes "
            "from the project's numerical model."
        )
        self.play(FadeIn(image))
        self.say(
            "Instead of a static model with the camera simply orbiting, the trial plane now tilts "
            "through the sine-theta geometry while the scene rotates. The animation loops until we "
            "advance. This is an extra closing slide after the summary, not a replacement for it.",
            src=movie,
            loop=True,
        )
