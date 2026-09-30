"""Slide-oriented introductory VTK scene for the sine-theta theorem.

This scene is meant to answer: what are the geometric objects before the
inequality appears?
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path

import numpy as np

from .sine_theta import SineThetaModel
from .vtk_sine_theta_common import BaseScene2D, COLORS, line_actor, polyline_actor, small_label, text_actor


class SineThetaIntroScene(BaseScene2D):
    def __init__(
        self,
        model: SineThetaModel,
        *,
        width: int = 1400,
        height: int = 900,
        offscreen: bool = False,
    ) -> None:
        self.model = model
        super().__init__(width=width, height=height, offscreen=offscreen, title="Davis--Kahan sine-theta introduction")
        self._build_scene()

    def _build_scene(self) -> None:
        m = self.model
        offset = np.array([-2.0, 0.0])
        v = offset + m.trial_vector
        origin = offset

        # Main geometry occupies the left side.
        for start, end in [
            (offset + np.array([-1.45, 0.0]), offset + np.array([1.45, 0.0])),
            (offset + np.array([0.0, -1.35]), offset + np.array([0.0, 1.55])),
        ]:
            _, actor = line_actor(start, end, color=COLORS["axes"], width=1.0)
            self.renderer.AddActor(actor)

        _, desired = line_actor(offset + np.array([-1.35, 0.0]), offset + np.array([1.35, 0.0]), color=COLORS["desired"], width=6.0)
        _, trial = line_actor(origin - 1.30 * m.trial_vector, origin + 1.30 * m.trial_vector, color=COLORS["trial"], width=5.0)
        _, vector = line_actor(origin, v, color=COLORS["trial"], width=8.0)
        self.renderer.AddActor(desired)
        self.renderer.AddActor(trial)
        self.renderer.AddActor(vector)

        arc_angles = np.linspace(0.0, m.theta, 28)
        radius = 0.34
        arc_points = offset + np.column_stack([radius * np.cos(arc_angles), radius * np.sin(arc_angles)])
        _, arc_actor = polyline_actor(arc_points, color=COLORS["angle"], width=4.0)
        self.renderer.AddActor(arc_actor)

        labels = [
            small_label("U = span(e_1)", tuple(offset + np.array([0.85, -0.18])), scale=0.075),
            small_label("U^perp = span(e_2)", tuple(offset + np.array([0.07, 1.06])), scale=0.060),
            small_label("V = span(v_theta)", (v[0] - 0.35, v[1] + 0.12), scale=0.070),
            small_label("v_theta", (v[0] + 0.04, v[1] + 0.02), scale=0.070),
            small_label("theta", tuple(offset + np.array([0.23, 0.11])), scale=0.065),
        ]
        for actor in labels:
            actor.SetCamera(self.renderer.GetActiveCamera())
            self.renderer.AddActor(actor)

        title = text_actor("Sine-theta setup: what are the objects?", x=28, y=840, size=28)
        theorem = text_actor("Public theorem:   delta ||sin Theta_0|| <= ||R||", x=28, y=802, size=22)
        info = text_actor(
            "Ambient space E = R^2\n"
            "Exact spectral subspace\n  U = span(e_1)\n"
            "Complementary subspace\n  U^perp = span(e_2)\n"
            "Trial subspace\n  V = span(v_theta)\n"
            f"Principal angle\n  theta = {m.theta_degrees:5.1f} deg\n"
            "Unit trial vector\n  v_theta = (cos theta, sin theta)",
            x=840,
            y=612,
            size=19,
        )
        coordinates = text_actor(
            "Coordinate maps used by the Lean theorem\n"
            "F_0 : R -> E    exact coordinate map\n"
            "E_0 : R -> E    trial coordinate map\n\n"
            "In this rank-one model:\n"
            "F_0(1) = e_1\n"
            f"E_0(1) = v_theta = ({m.trial_vector[0]:.3f}, {m.trial_vector[1]:.3f})\n\n"
            "So the theorem compares the trial direction\n"
            "against the exact eigenspace U.",
            x=840,
            y=360,
            size=19,
        )
        caption = text_actor(
            "Use this slide first: it introduces U, U^perp, V, and v_theta before any operator formulas appear.",
            x=28,
            y=24,
            size=18,
        )

        for actor in [title, theorem, info, coordinates, caption]:
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
    scene = SineThetaIntroScene(model, offscreen=args.no_interact)
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
