"""Slides: the sine-theta theorem in three dimensions, built on the VTK demo.

Stills and movies come from :mod:`dkvis.vtk_sine_theta_3d` and are written to
``media/vtk3d/`` by :func:`prepare` (``dkvis.build_slides`` calls it).  Still
builds show a VTK render beside LaTeX text; movie builds are full-frame VTK
videos that loop until the presenter advances.  The same scene runs live::

    uv run --extra vtk python -m dkvis.vtk_sine_theta_3d

These scenes stand alone (``sine-theta-3d``) and are also spliced into the full
deck (``sine-theta-full``) after the perturbation payoff slide.
"""

from __future__ import annotations

import math as pymath
import subprocess
import sys
from pathlib import Path

from manim import DOWN, LEFT, UP, FadeIn, FadeOut, Group, ImageMobject, Rectangle, VGroup

from dkvis import sine_theta_3d as m3
from dkvis.palette import OUTPUT_SUFFIX
from dkvis.slide_style import MUTED, PANEL, DeckSlide, boxed, math, mono, para, tex

ROOT = Path(__file__).resolve().parent.parent
ASSETS = ROOT / "media" / f"vtk3d{OUTPUT_SUFFIX}"
ASSET_NAMES = [
    "still-exact.png",
    "still-planes.png",
    "still-sine.png",
    "still-residual.png",
    "still-perturb.png",
    "app.png",
    "orbit.mp4",
    "sweep-theta.mp4",
    "sweep-lambda3.mp4",
    "perturb.mp4",
]


def prepare(refresh: bool = False) -> None:
    """Render the VTK stills and movies these slides use (a few minutes)."""
    if not refresh and all((ASSETS / name).exists() for name in ASSET_NAMES):
        return
    cmd = [sys.executable, "-m", "dkvis.vtk_sine_theta_3d", "--slide-assets", str(ASSETS)]
    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=ROOT, check=True)


def asset(name: str) -> Path:
    path = ASSETS / name
    if not path.exists():
        raise FileNotFoundError(f"{path} is missing; run `make assets` (with the same DKVIS_THEME) to render it")
    return path


TEXT_X = 0.75
TEXT_W = 6.1


def picture(name: str) -> Group:
    """An uncropped still within the actual left column of the 3D slides.

    Earlier versions set the *height* to 6.1 units.  At the VTK stills' wide
    aspect ratio that produced an 11-unit-wide image, cropping the left edge
    and overlapping the explanatory text.  Fit the width instead, with a
    quiet outline; the full-screen movie builds retain their native size.
    """
    img = ImageMobject(str(asset(name)))
    img.width = 6.65
    img.move_to([-3.35, -0.35, 0])
    border = Rectangle(
        width=img.width + 0.06,
        height=img.height + 0.06,
        stroke_color=MUTED,
        stroke_width=1.0,
    ).move_to(img)
    return Group(border, img)


def text_block(*paras: str, top: float, size: float = 27) -> VGroup:
    group = VGroup(*[para(p, width=TEXT_W, size=size) for p in paras])
    group.arrange(DOWN, aligned_edge=LEFT, buff=0.32)
    group.move_to([TEXT_X, top, 0], aligned_edge=UP + LEFT)
    return group


class D3Slide(DeckSlide):
    section = "The Davis--Kahan $\\sin\\Theta$ theorem $\\cdot$ in three dimensions"

    def swap_picture(self, old: Group | None, name: str, *extra) -> Group:
        new = picture(name)
        anims = [FadeIn(new)] + ([FadeOut(old)] if old is not None else []) + [FadeIn(m) for m in extra]
        self.play(*anims, run_time=0.8)
        return new


class D01Planes(D3Slide):
    title = "The same picture in three dimensions"
    kicker = r"Subspaces, not just vectors: two planes in $\mathbb{R}^3$"

    def body(self) -> None:
        top = self.content_top - 0.2
        paras = [
            r"With positive eigenvalues, $\sym{Ahat}=\operatorname{diag}(\lambda_1,\lambda_2,\lambda_3)$ maps the unit "
            r"sphere of $\mathbb{R}^3$ to an ellipsoid. "
            r"The exact wanted frame $\sym{F0}=[f_1\ f_2]$ spans the plane of the two short axes; "
            r"$\sym{F1}=[f_3]$ spans the exact unwanted direction and $\sym{Lambda1}=[\like{Lambda1}{\lambda_3}]$.",
            r"A trial plane $\operatorname{range}(\sym{E0})$, tilted by $\sym{theta}$ about a line in $\operatorname{range}(\sym{F0})$. "
            r"Two planes in $\mathbb{R}^3$ always share a line, so the principal angles are $(\theta,0)$.",
            r"One nonzero sine: $\norm{\sym{sinTheta0}}=\norm{\sym{F1}^{\mathsf T}\sym{E0}}=\sin\theta$, "
            r"the pink drop from $\operatorname{range}(\sym{E0})$ to $\operatorname{range}(\sym{F0})$.",
            r"With the Rayleigh--Ritz choice $A_0=E_0^{\mathsf T}\sym{Ahat}E_0$ we get $E_0^{\mathsf T}R=0$: "
            r"the \cx{resid}{residuals} leave $\operatorname{range}(\sym{E0})$ at right angles.",
        ]
        texts = text_block(*paras, top=top, size=25)

        self.say(
            "Same story, one dimension up. This A hat has positive eigenvalues, so it maps the unit sphere "
            "to an ellipsoid. The wanted "
            "exact wanted frame F0 spans the plane of the two short axes, f1 and f2; F1 is the unwanted direction."
        )
        img = self.swap_picture(None, "still-exact.png", texts[0])

        self.say(
            "Now range E0 is a trial plane, tilted by theta about a line in range F0. Two planes in R^3 always "
            "meet in a line, so one principal angle is zero and the other is theta."
        )
        img = self.swap_picture(img, "still-planes.png", texts[1])

        self.say(
            "So sin Theta0 has one nonzero singular value: sin theta, the pink drop from the "
            "tilted trial vector to range F0. Its norm is the same in every unitarily invariant norm."
        )
        img = self.swap_picture(img, "still-sine.png", texts[2])

        self.say(
            "With the Rayleigh-Ritz trial matrix, E0-transpose R is zero: the residual of each "
            "trial vector sticks straight out of the trial plane."
        )
        img = self.swap_picture(img, "still-residual.png", texts[3])

        self.say(
            "The whole configuration, orbiting. This is a VTK render of the live demo. (Loops.)",
            src=asset("orbit.mp4"),
            loop=True,
        )


class D02Tilt(D3Slide):
    depth = "*"
    title = "Watching the theorem"
    kicker = r"Tilt the trial plane; compare $\delta\norm{\sin\Theta_0}$ with $\norm{R}$"

    def body(self) -> None:
        rows = []
        for deg in (10, 45, 80):
            cfg = m3.tilted_trial(pymath.radians(deg))
            mu = cfg.ritz_values
            rows.append(
                rf"{deg}^\circ & {mu[1]:.3f} & {cfg.delta:.3f} & {cfg.theorem_lhs:.3f} & {cfg.residual_norm_2:.3f}\\"
            )
        lam3 = m3.DEFAULT_EIGENVALUES[2]
        table = math(
            r"\renewcommand{\arraystretch}{1.35}\begin{array}{c|cc|cc}"
            r"\theta & \like{mu}{\mu_2} & \sym{delta} & \sym{delta}\sym{sintheta} & \norm{\sym{R}}_2\\ \hline"
            + "".join(rows)
            + r"\end{array}",
            size=34,
        )
        caption = tex(rf"$\lambda_3={lam3}$; \ $\mu_2$ is the larger Ritz value, $\delta=|\mu_2-\lambda_3|$", size=24, color=MUTED)
        points = [
            r"\textbf{Small tilt:} the bound is nearly tight.",
            r"\textbf{Large tilt:} $\operatorname{range}(\sym{E0})$ leans into $\like{w}{f_3}$, so the Ritz value $\like{mu}{\mu_2}$ climbs toward $\like{Lambda1}{\lambda_3}$. "
            r"The certified separation $\sym{delta}$ closes and the bound says less.",
            r"It never fails: $\sym{delta}\norm{\sym{sinTheta0}}\le\norm{\sym{R}}$ at every angle.",
        ]
        block = VGroup(table, caption).arrange(DOWN, buff=0.2)
        block.move_to([-3.2, 0.1, 0])
        texts = text_block(*points, top=self.content_top - 0.35, size=27)

        self.say(
            "Before the movie, the numbers at three tilts. Note that the theorem separation is measured "
            "from the Ritz values of this trial plane, and it moves as the plane tilts."
        )
        self.play(FadeIn(block), FadeIn(texts[0]))

        self.say(
            "At large tilt the trial plane leans into the unwanted direction, the larger Ritz "
            "value approaches lambda3, and delta collapses. The inequality still holds, but loosely."
        )
        self.play(FadeIn(texts[1]), FadeIn(texts[2]))

        self.say(
            "The movie sweeps the tilt from 4 to 82 degrees and back. Watch the violet gap in "
            "the spectrum strip and the two bars on the right. (Loops.)",
            src=asset("sweep-theta.mp4"),
            loop=True,
        )


class D03Gap(D3Slide):
    depth = "*"
    title = r"Moving the unwanted eigenvalue"
    kicker = r"Same tilt, $\lambda_3$ slides down past the wanted eigenvalues"

    def body(self) -> None:
        points = [
            r"Here $\Lambda_1=[\lambda_3]$ is a single point, so the separation hypothesis holds in its "
            r"exchanged form ($\operatorname{spec}\Lambda_1$ in an interval, $\operatorname{spec}A_0$ outside "
            r"its $\delta$-neighbourhood) with",
            r"$$\sym{delta}=\min_i\,|\like{mu}{\mu_i}-\lambda_3|,$$",
            r"wherever $\lambda_3$ sits, even between $\lambda_1$ and $\lambda_2$.",
            r"When $\lambda_3$ nears a Ritz value, $\delta\to0$ and the theorem is silent, "
            r"though $\sin\theta$ has not changed.",
        ]
        texts = text_block(*points, top=self.content_top - 0.3, size=27)
        img = picture("still-residual.png")

        self.say(
            "Keep the tilt fixed and move lambda3 instead. With a single unwanted eigenvalue "
            "delta is simply the distance from lambda3 to the nearest Ritz value."
        )
        self.play(FadeIn(img), FadeIn(texts))

        self.say(
            "The movie slides lambda3 from 2.8 down to 0.6 and back. The angle never changes; "
            "only what the theorem can certify does. (Loops.)",
            src=asset("sweep-lambda3.mp4"),
            loop=True,
        )


class D04Perturb(D3Slide):
    depth = "*"
    title = "Perturbing the matrix, in 3D"
    kicker = r"$\operatorname{range}(\sym{E0})$ is the original eigenspace; exact $\operatorname{range}(\sym{F0})$ moves"

    def body(self) -> None:
        eq = math(
            r"\sym{Ahat}=\sym{A}+\varepsilon\sym{H},\qquad "
            r"\sym{R}=\sym{Ahat}\sym{E0}-\sym{E0}\sym{A0}=\varepsilon\sym{H}\sym{E0}",
            size=32,
        )
        bound = boxed(
            math(r"\norm{\sym{sinTheta0}(\sym{E0},\sym{F0})}\le\frac{\norm{\sym{R}}}{\sym{delta}}\le\frac{\varepsilon}{\sym{delta}}", size=34),
            color=MUTED,
        )
        note = para(
            r"$\sym{E0}=[e_1\ e_2]$ and $\sym{A0}=\operatorname{diag}(\lambda_1,\lambda_2)$ are the \emph{unperturbed} "
            r"eigenpairs; $\sym{H}$ is a fixed symmetric direction with $\norm{\sym{H}}_2=1$, and $\sym{delta}$ is measured "
            r"to the perturbed $\lambda_3(\varepsilon)$.",
            width=TEXT_W,
            size=24,
            color=MUTED,
        )
        cfg = m3.perturbed(0.8)
        numbers = math(
            rf"\varepsilon=0.8:\quad \cx{{sine}}{{\sin\theta}}={cfg.sin_theta:.3f}\ \le\ "
            rf"\frac{{\norm{{\sym{{R}}}}_2}}{{\sym{{delta}}}}={cfg.residual_norm_2 / cfg.delta:.3f}",
            size=30,
        )
        col = VGroup(eq, bound, note, numbers).arrange(DOWN, aligned_edge=LEFT, buff=0.35)
        col.move_to([TEXT_X, self.content_top - 0.3, 0], aligned_edge=UP + LEFT)
        img = picture("still-perturb.png")

        self.say(
            "The payoff slide again, in 3D. The trial plane is the old eigenspace; the operator "
            "becomes A hat = A + eps H, so the residual is eps H E0 and the exact frame F0 tilts away."
        )
        self.play(FadeIn(img), FadeIn(eq), FadeIn(bound))
        self.say("Here are the numbers at eps = 0.8.")
        self.play(FadeIn(note), FadeIn(numbers))

        self.say(
            "The movie grows eps from 0 to 1.1 and back: watch the ellipsoid deform, the blue "
            "plane tilt away from the amber one, and the bars stay ordered. (Loops.)",
            src=asset("perturb.mp4"),
            loop=True,
        )


class D05TryIt(D3Slide):
    depth = "*"
    title = "Inside the 3D explorer"
    kicker = "The interactive VTK application behind the animated examples"

    def body(self) -> None:
        shot = ImageMobject(str(asset("app.png")))
        shot.width = 7.4
        shot.move_to([-3.05, -0.35, 0])
        frame = Rectangle(width=shot.width + 0.08, height=shot.height + 0.08, stroke_color=MUTED, stroke_width=1.5).move_to(shot)
        cmd = mono("uv run --extra vtk \\\n  python -m dkvis.vtk_sine_theta_3d", size=17)
        cmd_bg = Rectangle(width=cmd.width + 0.35, height=cmd.height + 0.3, fill_color=PANEL, fill_opacity=1, stroke_width=0).move_to(cmd)
        cmd_group = VGroup(cmd_bg, cmd)
        controls = para(
            r"\textbf{mouse}: drag to rotate, scroll to zoom, shift-drag to pan\\[0.3em]"
            r"\textbf{sliders}: tilt $\theta$, hinge azimuth $\varphi$, perturbation $\varepsilon$, eigenvalue $\lambda_3$\\[0.3em]"
            r"\textbf{keys}: \texttt{m} trial/perturb mode, \texttt{space} play, \texttt{e} ellipsoid, "
            r"\texttt{x} residuals, \texttt{r} reset view, \texttt{s} screenshot",
            width=5.6,
            size=24,
        )
        col = VGroup(cmd_group, controls).arrange(DOWN, aligned_edge=LEFT, buff=0.45)
        col.move_to([1.25, self.content_top - 0.3, 0], aligned_edge=UP + LEFT)

        self.say(
            "Everything on the last few slides is this program. Run it, drag the sliders, "
            "and every number on the right is recomputed and checked against the theorem."
        )
        self.play(FadeIn(shot), FadeIn(frame), FadeIn(col))


SCENES = [D01Planes, D02Tilt, D03Gap, D04Perturb, D05TryIt]
