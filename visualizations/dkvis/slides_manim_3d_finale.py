"""Friday-only native Manim 3D companion to the closing VTK visualization.

The 3D movie is rendered from the same numerical sine-theta model as the VTK
scene.  Its geometry changes: range(E0) tilts relative to range(F0), while the
sine-theta drop and Rayleigh--Ritz residual update with the angle.
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
    DR,
    LEFT,
    FadeIn,
    ImageMobject,
    Line,
    Surface,
    ThreeDScene,
    ValueTracker,
    VGroup,
    always_redraw,
    rate_functions,
)

from dkvis import sine_theta_3d as model
from dkvis.palette import OUTPUT_SUFFIX
from dkvis.slide_style import (
    DeckSlide,
    FAINT,
    FG,
    MUTED,
    PANEL,
    RESID,
    SINE,
    TRIAL,
    WANTED,
    panel,
    tex,
)

ROOT = Path(__file__).resolve().parent.parent
ASSETS = ROOT / "media" / f"manim3d{OUTPUT_SUFFIX}"
STILL = ASSETS / "finale-manim3d.png"
MOVIE = ASSETS / "finale-manim3d.mp4"


class Manim3DFinaleAsset(ThreeDScene):
    """Standalone Manim renderer for the model's trial-frame tilt."""

    def construct(self) -> None:
        theta_deg = ValueTracker(9.0)
        lam = model.DEFAULT_EIGENVALUES

        def configuration():
            return model.tilted_trial(np.radians(theta_deg.get_value()))

        ellipsoid = Surface(
            lambda u, v: np.array([
                lam[0] * np.cos(u) * np.cos(v),
                lam[1] * np.sin(u) * np.cos(v),
                lam[2] * np.sin(v),
            ]),
            u_range=[0.0, 2 * np.pi],
            v_range=[-np.pi / 2, np.pi / 2],
            resolution=(30, 22),
            checkerboard_colors=[PANEL, PANEL],
            fill_opacity=0.10,
            stroke_color=FAINT,
            stroke_width=0.8,
        )
        exact = Surface(
            lambda u, v: np.array([u, v, 0.0]),
            u_range=[-2.35, 2.35],
            v_range=[-2.35, 2.35],
            resolution=(16, 16),
            checkerboard_colors=[WANTED, WANTED],
            fill_opacity=0.24,
            stroke_color=WANTED,
            stroke_width=1.2,
        )

        def trial_plane():
            theta = np.radians(theta_deg.get_value())
            return Surface(
                lambda u, v: np.array([u, v * np.cos(theta), v * np.sin(theta)]),
                u_range=[-2.35, 2.35],
                v_range=[-2.35, 2.35],
                resolution=(16, 16),
                checkerboard_colors=[TRIAL, TRIAL],
                fill_opacity=0.30,
                stroke_color=TRIAL,
                stroke_width=1.3,
            )

        def shared_line():
            return Line([-2.55, 0.0, 0.0], [2.55, 0.0, 0.0], color=FG, stroke_width=5)

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

        self.set_camera_orientation(phi=66 * DEGREES, theta=-48 * DEGREES, zoom=0.96)
        self.add(
            ellipsoid,
            exact,
            always_redraw(trial_plane),
            always_redraw(shared_line),
            always_redraw(sine_drop),
            always_redraw(residual),
        )
        self.begin_ambient_camera_rotation(rate=0.08)

        legend_lines = VGroup(
            tex(r"$\operatorname{range}(\sym{F0})$ exact plane", size=24, color=WANTED),
            tex(r"$\operatorname{range}(\sym{E0})$ trial plane", size=24, color=TRIAL),
            tex(r"shared line / rotation axis", size=22, color=MUTED),
            tex(r"pink: $\sin \theta$ drop", size=22, color=SINE),
            tex(r"green: residual $R$", size=22, color=RESID),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.10)
        legend = VGroup(panel(legend_lines, pad=0.20), legend_lines)
        legend.to_corner(DR).shift([-0.18, 0.22, 0.0])

        angle_label = always_redraw(
            lambda: tex(
                rf"$\theta = {theta_deg.get_value():.0f}^\circ$",
                size=25,
                color=SINE,
            ).move_to([4.95, 3.12, 0.0])
        )
        self.add_fixed_in_frame_mobjects(legend, angle_label)

        self.wait(0.25)
        self.play(theta_deg.animate.set_value(70.0), run_time=3.6, rate_func=rate_functions.smooth)
        self.play(theta_deg.animate.set_value(20.0), run_time=2.8, rate_func=rate_functions.smooth)
        self.play(theta_deg.animate.set_value(56.0), run_time=2.5, rate_func=rate_functions.smooth)
        self.play(theta_deg.animate.set_value(9.0), run_time=2.1, rate_func=rate_functions.smooth)
        self.wait(0.55)


def _render_assets(refresh: bool) -> None:
    if not refresh and STILL.is_file() and MOVIE.is_file():
        return
    ASSETS.mkdir(parents=True, exist_ok=True)
    quality = os.environ.get("DKVIS_MANIM3D_QUALITY", "h")
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
        "-ss", "2.8", "-i", str(MOVIE), "-frames:v", "1", str(STILL),
    ], check=True)


def prepare(refresh: bool = False) -> None:
    """Prepare only the native Manim movie, without rebuilding VTK assets."""
    _render_assets(refresh)


class V00Manim3DFinale(DeckSlide):
    title = ""
    kicker = ""
    section = ""

    def body(self) -> None:
        if not STILL.is_file() or not MOVIE.is_file():
            raise FileNotFoundError("Missing Manim 3D assets; render through dkvis.build_slides")
        image = ImageMobject(str(STILL))
        image.move_to([0, 0, 0])
        image.scale_to_fit_height(6.75)
        if image.width > 12.2:
            image.scale_to_fit_width(12.2)
        self.play(FadeIn(image))
        self.say(
            "Eye-candy closing slide: native Manim 3D sine-theta geometry with correctly labeled exact and trial planes, "
            "the shared rotation axis, the sine-theta drop, and the residual.",
            src=MOVIE,
            loop=True,
        )
