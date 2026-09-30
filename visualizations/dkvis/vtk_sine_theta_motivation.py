"""Slide-oriented motivation scene for why ``sin(theta)`` appears."""

from __future__ import annotations

import argparse
from pathlib import Path

import numpy as np

from .sine_theta import SineThetaModel
from .vtk_sine_theta_common import BaseScene2D, COLORS, line_actor, polyline_actor, small_label, text_actor


class SineThetaMotivationScene(BaseScene2D):
    def __init__(
        self,
        model: SineThetaModel,
        *,
        width: int = 1400,
        height: int = 900,
        offscreen: bool = False,
    ) -> None:
        self.model = model
        super().__init__(width=width, height=height, offscreen=offscreen, title="Davis--Kahan sine-theta motivation")
        self._build_scene()

    def _build_scene(self) -> None:
        m = self.model
        offset = np.array([-2.0, 0.0])
        origin = offset
        v = offset + m.trial_vector
        p = offset + m.desired_projection

        for start, end in [
            (offset + np.array([-1.45, 0.0]), offset + np.array([1.45, 0.0])),
            (offset + np.array([0.0, -1.35]), offset + np.array([0.0, 1.55])),
        ]:
            _, actor = line_actor(start, end, color=COLORS["axes"], width=1.0)
            self.renderer.AddActor(actor)

        _, desired = line_actor(offset + np.array([-1.35, 0.0]), offset + np.array([1.35, 0.0]), color=COLORS["desired"], width=6.0)
        _, vector = line_actor(origin, v, color=COLORS["trial"], width=8.0)
        _, projection = line_actor(origin, p, color=COLORS["projection"], width=7.0)
        _, sine = line_actor(p, v, color=COLORS["sine"], width=8.0)
        _, guide_h = line_actor(p, v, color=COLORS["muted"], width=2.0)
        _, guide_v = line_actor(origin, p, color=COLORS["muted"], width=2.0)
        guide_h.GetProperty().SetOpacity(0.30)
        guide_v.GetProperty().SetOpacity(0.30)
        for actor in [desired, guide_v, guide_h, vector, projection, sine]:
            self.renderer.AddActor(actor)

        arc_angles = np.linspace(0.0, m.theta, 28)
        radius = 0.34
        arc_points = offset + np.column_stack([radius * np.cos(arc_angles), radius * np.sin(arc_angles)])
        _, arc_actor = polyline_actor(arc_points, color=COLORS["angle"], width=4.0)
        self.renderer.AddActor(arc_actor)

        labels = [
            small_label("U", tuple(offset + np.array([1.05, -0.17])), scale=0.08),
            small_label("v_theta", (v[0] + 0.04, v[1] + 0.03), scale=0.070),
            small_label("sin theta", (p[0] + 0.10, 0.52 * v[1]), scale=0.065),
            small_label("cos theta", (offset[0] + 0.25, 0.10), scale=0.065),
            small_label("theta", tuple(offset + np.array([0.23, 0.11])), scale=0.065),
        ]
        for actor in labels:
            actor.SetCamera(self.renderer.GetActiveCamera())
            self.renderer.AddActor(actor)

        title = text_actor("Why does sin(theta) appear?", x=28, y=840, size=28)
        subtitle = text_actor("The proof-facing object is the rectangular block S = (I - P_U) E_0.", x=28, y=802, size=21)
        formulas = text_actor(
            "On the unit trial coordinate 1:\n"
            "v_theta = E_0(1) = (cos theta, sin theta)\n"
            "P_U v_theta        = (cos theta, 0)\n"
            "(I - P_U) v_theta  = (0, sin theta)\n\n"
            "Therefore\n"
            "||(I - P_U) v_theta||_2 = sin(theta).\n\n"
            "Because the trial coordinate is 1-dimensional,\n"
            "the positive operator sin Theta_0 is just this scalar.",
            x=840,
            y=520,
            size=20,
        )
        takeaway = text_actor(
            "Takeaway:\n"
            "  the theorem's literal ||sin Theta_0|| becomes\n"
            "  the length of the vertical leg.\n\n"
            "This is the geometric bridge from the abstract\n"
            "theorem statement to the visible angle theta.",
            x=840,
            y=250,
            size=18,
        )
        caption = text_actor(
            "Use this after the setup slide: it motivates the name 'sine-theta' before the residual and spectral gap are introduced.",
            x=28,
            y=24,
            size=18,
        )

        for actor in [title, subtitle, formulas, takeaway, caption]:
            self.renderer.AddViewProp(actor)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--theta", type=float, default=35.0)
    parser.add_argument("--delta", type=float, default=1.0)
    parser.add_argument("--rho", type=float, default=0.0)
    parser.add_argument("--lambda-desired", type=float, default=0.0)
    parser.add_argument("--screenshot", type=Path)
    parser.add_argument("--no-interact", action="store_true")
    return parser


def main() -> None:
    args = _parser().parse_args()
    model = SineThetaModel.from_degrees(
        args.theta,
        delta=args.delta,
        rho=args.rho,
        lambda_desired=args.lambda_desired,
    )
    scene = SineThetaMotivationScene(model, offscreen=args.no_interact)
    if args.screenshot:
        scene.screenshot(args.screenshot)
        print(args.screenshot)
    if args.no_interact:
        if not args.screenshot:
            scene.render()
        return
    scene.interact()


if __name__ == "__main__":
    main()
