"""Friday-only native Manim 3D companion to the closing VTK visualization.

The 3D movie is rendered from the same numerical sine-theta model as the VTK
scene.  Its geometry changes: range(E0) tilts relative to range(F0), while
both the sine-theta drop and Rayleigh-Ritz residual update with the angle.
The VTK visualization deliberately remains the last Friday slide.
"""

from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

import numpy as np
from manim import (
    DEGREES,
    DOWN,
    FadeIn,
    ImageMobject,
    Line,
    Surface,
    Text,
    ThreeDAxes,
    ThreeDScene,
    ValueTracker,
    always_redraw,
    rate_functions,
)

from dkvis import sine_theta_3d as model
from dkvis.palette import OUTPUT_SUFFIX
from dkvis.slide_style import (
    DeckSlide, FAINT, FG, MUTED, PANEL, RESID, SINE, TRIAL, WANTED,
)

ROOT = Path(__file__).resolve().parent.parent
ASSETS = ROOT / "media" / f"manim3d{OUTPUT_SUFFIX}"
STILL = ASSETS / "finale-manim3d.png"
MOVIE = ASSETS / "finale-manim3d.mp4"


class Manim3DFinaleAsset(ThreeDScene):
    """Standalone Manim renderer for the model's trial-frame tilt."""

    def construct(self) -> None:
        theta_deg = ValueTracker(8.0)
        lam = model.DEFAULT_EIGENVALUES

        def configuration():
            return model.tilted_trial(np.radians(theta_deg.get_value()))

        # Ahat maps the unit sphere to an ellipsoid with these semiaxes.
        ellipsoid = Surface(
            lambda u, v: np.array([
                lam[0] * np.cos(u) * np.cos(v),
                lam[1] * np.sin(u) * np.cos(v),
                lam[2] * np.sin(v),
            ]),
            u_range=[0.0, 2 * np.pi],
            v_range=[-np.pi / 2, np.pi / 2],
            resolution=(22, 16),
            checkerboard_colors=[PANEL, PANEL],
            fill_opacity=0.13,
            stroke_color=FAINT,
            stroke_width=0.7,
        )
        exact = Surface(
            lambda u, v: np.array([u, v, 0.0]),
            u_range=[-2.0, 2.0],
            v_range=[-2.0, 2.0],
            resolution=(8, 8),
            checkerboard_colors=[WANTED, WANTED],
            fill_opacity=0.27,
            stroke_color=WANTED,
            stroke_width=0.9,
        )

        def trial_plane():
            theta = np.radians(theta_deg.get_value())
            return Surface(
                lambda u, v: np.array([u, v * np.cos(theta), v * np.sin(theta)]),
                u_range=[-2.0, 2.0],
                v_range=[-2.0, 2.0],
                resolution=(8, 8),
                checkerboard_colors=[TRIAL, TRIAL],
                fill_opacity=0.33,
                stroke_color=TRIAL,
                stroke_width=0.9,
            )

        def sine_drop():
            cfg = configuration()
            tilted = cfg.E0[:, 1]
            foot = cfg.F0 @ (cfg.F0.T @ tilted)
            return Line(foot, tilted, color=SINE, stroke_width=9)

        def residual():
            cfg = configuration()
            tilted = cfg.E0[:, 1]
            r = cfg.R[:, 1]
            return Line(tilted, tilted + r, color=RESID, stroke_width=9)

        axes = ThreeDAxes(
            x_range=[-3, 3, 1], y_range=[-3, 3, 1], z_range=[-3, 3, 1],
            x_length=6.0, y_length=6.0, z_length=6.0,
        )
        hinge = Line([-2.35, 0, 0], [2.35, 0, 0], color=FG, stroke_width=4)
        self.set_camera_orientation(phi=65 * DEGREES, theta=-43 * DEGREES, zoom=0.84)
        self.add(axes, ellipsoid, exact, always_redraw(trial_plane), hinge,
                 always_redraw(sine_drop), always_redraw(residual))

        # Labels stay in the camera plane; the source theorem uses frames, not U/V.
        labels = [
            Text("range(F0): exact plane", font_size=26, color=WANTED),
            Text("range(E0): trial plane", font_size=26, color=TRIAL),
            Text("pink: sine-theta drop", font_size=22, color=SINE),
            Text("green: residual R", font_size=22, color=RESID),
        ]
        for i, label in enumerate(labels):
            label.move_to([-4.65, 3.15 - i * 0.38, 0])
        angle_label = always_redraw(
            lambda: Text(f"tilt = {theta_deg.get_value():.0f} deg", font_size=27, color=FG)
            .move_to([4.8, 3.0, 0])
        )
        self.add_fixed_in_frame_mobjects(*labels, angle_label)

        self.wait(0.3)
        self.play(theta_deg.animate.set_value(72.0), run_time=4.0,
                  rate_func=rate_functions.smooth)
        self.play(theta_deg.animate.set_value(8.0), run_time=4.0,
                  rate_func=rate_functions.smooth)
        self.wait(0.3)


def _render_assets(refresh: bool) -> None:
    if not refresh and STILL.is_file() and MOVIE.is_file():
        return
    ASSETS.mkdir(parents=True, exist_ok=True)
    quality = os.environ.get("DKVIS_MANIM3D_QUALITY", "m")
    if quality not in {"l", "m", "h", "p", "k"}:
        raise ValueError("DKVIS_MANIM3D_QUALITY must be one of l, m, h, p, k")
    with tempfile.TemporaryDirectory(prefix="dkvis-manim3d-") as folder:
        media_dir = Path(folder) / "media"
        args = [
            sys.executable, "-m", "manim",
            f"--media_dir={media_dir}", f"--quality={quality}", "--fps=30",
            "-o", "manim3d-finale.mp4", str(Path(__file__).resolve()),
            "Manim3DFinaleAsset",
        ]
        print("+", " ".join(args), flush=True)
        subprocess.run(args, cwd=ROOT, check=True)
        videos = list(media_dir.rglob("manim3d-finale.mp4"))
        if len(videos) != 1:
            raise RuntimeError(f"expected one Manim 3D video, found {videos}")
        shutil.copy2(videos[0], MOVIE)
    subprocess.run([
        "ffmpeg", "-hide_banner", "-loglevel", "error", "-y",
        "-ss", "2.0", "-i", str(MOVIE), "-frames:v", "1", str(STILL),
    ], check=True)


def prepare(refresh: bool = False) -> None:
    """Prepare only the native Manim movie, without rebuilding VTK assets."""
    _render_assets(refresh)


class V00Manim3DFinale(DeckSlide):
    title = "The sine-theta geometry, built in Manim"
    kicker = (
        r"The trial plane $\operatorname{range}(\sym{E0})$ tilts relative to "
        r"the exact plane $\operatorname{range}(\sym{F0})$"
    )
    section = "Davis--Kahan: a geometric closing view"

    def body(self) -> None:
        if not STILL.is_file() or not MOVIE.is_file():
            raise FileNotFoundError("Missing Manim 3D assets; render through dkvis.build_slides")
        image = ImageMobject(str(STILL))
        image.height = 5.35
        image.move_to([0, -0.43, 0])
        if image.width > 11.0:
            image.scale_to_fit_width(11.0)
        self.say(
            "Manim can render this geometry directly. The exact plane is range F zero, "
            "while the trial plane range E zero rotates around their shared line. "
            "The pink segment measures the perpendicular subspace error; the green segment "
            "is the Rayleigh-Ritz residual computed from the same numerical model as VTK."
        )
        self.play(FadeIn(image))
        self.say(
            "Here the geometry itself rotates: the trial plane tilts from eight to seventy-two "
            "degrees and back, while the sine-theta drop and residual update. The movie loops. "
            "The next and final slide uses VTK.",
            src=MOVIE, loop=True,
        )
