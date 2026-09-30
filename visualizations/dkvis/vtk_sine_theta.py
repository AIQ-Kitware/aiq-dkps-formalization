"""Interactive VTK explorer for the rank-one sine-theta theorem.

Run from ``visualizations/`` with:

    uv run --extra vtk python -m dkvis.vtk_sine_theta

This version is deliberately slide-friendly: the exact subspace, the trial
subspace, the projection, the sine block, the residual, and the theorem
statement remain visible for arbitrary slider positions, so screenshots are
useful at any point in the interaction.
"""

from __future__ import annotations

import argparse
from pathlib import Path

import numpy as np
import vtk

from .sine_theta import SineThetaModel
from .vtk_sine_theta_common import BaseScene2D, COLORS, line_actor, polyline_actor, small_label, text_actor


class SineThetaVTKScene(BaseScene2D):
    def __init__(
        self,
        model: SineThetaModel,
        *,
        width: int = 1400,
        height: int = 900,
        offscreen: bool = False,
    ) -> None:
        self.delta = model.delta
        self.rho = model.rho
        self.lambda_desired = model.lambda_desired
        self.model = model
        super().__init__(width=width, height=height, offscreen=offscreen, title="Davis--Kahan sine-theta explorer")
        self.offset = np.array([-2.0, 0.0])
        self._build_static_geometry()
        self._build_dynamic_geometry()
        self._build_overlay()
        self._build_slider()
        self.update(model.theta_degrees)

    def _build_static_geometry(self) -> None:
        for start, end in [
            (self.offset + np.array([-1.45, 0.0]), self.offset + np.array([1.45, 0.0])),
            (self.offset + np.array([0.0, -1.35]), self.offset + np.array([0.0, 1.55])),
        ]:
            _, actor = line_actor(start, end, color=COLORS["axes"], width=1.0)
            self.renderer.AddActor(actor)

        _, desired = line_actor(self.offset + np.array([-1.35, 0.0]), self.offset + np.array([1.35, 0.0]), color=COLORS["desired"], width=6.0)
        self.renderer.AddActor(desired)

    def _build_dynamic_geometry(self) -> None:
        zero = np.zeros(2)
        self.trial_source, trial_actor = line_actor(zero, zero, color=COLORS["trial"], width=4.0)
        self.vector_source, vector_actor = line_actor(zero, zero, color=COLORS["trial"], width=8.0)
        self.proj_source, proj_actor = line_actor(zero, zero, color=COLORS["projection"], width=7.0)
        self.sine_source, sine_actor = line_actor(zero, zero, color=COLORS["sine"], width=8.0)
        self.residual_source, residual_actor = line_actor(zero, zero, color=COLORS["residual"], width=6.0)
        self.angle_data, angle_actor = polyline_actor(np.zeros((24, 2)), color=COLORS["angle"], width=4.0)
        self.reference_source, reference_actor = line_actor(np.zeros(2), np.zeros(2), color=COLORS["muted"], width=2.0)
        reference_actor.GetProperty().SetOpacity(0.45)

        for actor in [trial_actor, vector_actor, proj_actor, sine_actor, residual_actor, angle_actor, reference_actor]:
            self.renderer.AddActor(actor)

        self.label_u = small_label("U", tuple(self.offset + np.array([1.05, -0.17])), scale=0.08)
        self.label_v = small_label("V", tuple(self.offset + np.array([1.0, 0.2])), scale=0.065)
        self.label_vector = small_label("v_theta", tuple(self.offset + np.array([0.85, 0.35])), scale=0.065)
        self.label_proj = small_label("P_U v", tuple(self.offset + np.array([0.40, -0.18])), scale=0.060)
        self.label_sine = small_label("sin theta", tuple(self.offset + np.array([0.45, 0.30])), scale=0.060)
        self.label_residual = small_label("r", tuple(self.offset + np.array([0.25, 0.85])), scale=0.070)
        self.label_theta = small_label("theta", tuple(self.offset + np.array([0.26, 0.12])), scale=0.060)
        for actor in [
            self.label_u,
            self.label_v,
            self.label_vector,
            self.label_proj,
            self.label_sine,
            self.label_residual,
            self.label_theta,
        ]:
            actor.SetCamera(self.renderer.GetActiveCamera())
            self.renderer.AddActor(actor)

    def _build_overlay(self) -> None:
        self.title = text_actor("Sine-theta theorem: residual controls subspace error", x=28, y=840, size=28)
        self.subtitle = text_actor(
            "Rank-one sharp model: the magenta vertical leg is ||sin Theta_0|| and the cyan arrow is the residual.",
            x=28,
            y=804,
            size=19,
        )
        self.left_info = text_actor("", x=28, y=585, size=18)
        self.right_info = text_actor("", x=800, y=585, size=17)
        self.footer = text_actor(
            "white U   yellow V/v_theta   green P_U v   magenta sin(theta) component   cyan residual r",
            x=28,
            y=24,
            size=17,
        )
        for actor in [self.title, self.subtitle, self.left_info, self.right_info, self.footer]:
            self.renderer.AddViewProp(actor)

    def _build_slider(self) -> None:
        rep = vtk.vtkSliderRepresentation2D()
        rep.SetMinimumValue(0.0)
        rep.SetMaximumValue(85.0)
        rep.SetValue(self.model.theta_degrees)
        rep.SetTitleText("theta (degrees)")
        rep.GetPoint1Coordinate().SetCoordinateSystemToNormalizedDisplay()
        rep.GetPoint1Coordinate().SetValue(0.58, 0.09)
        rep.GetPoint2Coordinate().SetCoordinateSystemToNormalizedDisplay()
        rep.GetPoint2Coordinate().SetValue(0.94, 0.09)
        rep.SetSliderLength(0.025)
        rep.SetSliderWidth(0.03)
        rep.SetTubeWidth(0.008)
        rep.ShowSliderLabelOff()
        rep.GetTitleProperty().SetColor(*COLORS["text"])
        rep.GetLabelProperty().SetColor(*COLORS["text"])

        self.slider = vtk.vtkSliderWidget()
        self.slider.SetInteractor(self.interactor)
        self.slider.SetRepresentation(rep)
        self.slider.SetAnimationModeToAnimate()
        self.slider.AddObserver(vtk.vtkCommand.InteractionEvent, self._on_slider)
        self.slider.EnabledOn()

    def _on_slider(self, _obj: object, _event: object) -> None:
        value = self.slider.GetRepresentation().GetValue()
        self.update(float(value))
        self.window.Render()

    @staticmethod
    def _set_line(source: vtk.vtkLineSource, start: np.ndarray, end: np.ndarray) -> None:
        source.SetPoint1(float(start[0]), float(start[1]), 0.0)
        source.SetPoint2(float(end[0]), float(end[1]), 0.0)
        source.Modified()

    def _set_label_positions(self, m: SineThetaModel) -> None:
        v = self.offset + m.trial_vector
        p = self.offset + m.desired_projection
        s_mid = 0.5 * (p + v)
        r = m.residual
        r_end = self.offset + r
        self.label_v.SetPosition(float(0.96 * v[0]), float(0.96 * v[1] + 0.19), 0.0)
        self.label_vector.SetPosition(float(v[0] + 0.05), float(v[1] + 0.03), 0.0)
        self.label_proj.SetPosition(float(max(self.offset[0] + 0.18, self.offset[0] + 0.40 * (p[0] - self.offset[0]))), -0.18, 0.0)
        self.label_sine.SetPosition(float(s_mid[0] + 0.06), float(s_mid[1] + 0.04), 0.0)
        self.label_residual.SetPosition(float(r_end[0] + 0.05), float(r_end[1] + 0.05), 0.0)

    def update(self, theta_degrees: float) -> None:
        self.model = SineThetaModel.from_degrees(
            theta_degrees,
            delta=self.delta,
            rho=self.rho,
            lambda_desired=self.lambda_desired,
        )
        self.model.verify()
        m = self.model
        v0 = m.trial_vector
        p0 = m.desired_projection
        r = m.residual
        v = self.offset + v0
        p = self.offset + p0

        self._set_line(self.trial_source, self.offset - 1.30 * v0, self.offset + 1.30 * v0)
        self._set_line(self.vector_source, self.offset, v)
        self._set_line(self.proj_source, self.offset, p)
        self._set_line(self.sine_source, p, v)
        self._set_line(self.residual_source, self.offset, self.offset + r)
        self._set_line(self.reference_source, p, np.array([p[0], v[1]]))

        arc_angles = np.linspace(0.0, m.theta, 24)
        radius = 0.28
        points = self.offset + np.column_stack([radius * np.cos(arc_angles), radius * np.sin(arc_angles)])
        vtk_points = self.angle_data.GetPoints()
        for idx, (x, y) in enumerate(points):
            vtk_points.SetPoint(idx, float(x), float(y), 0.0)
        vtk_points.Modified()
        self.angle_data.Modified()

        self._set_label_positions(m)

        relation = "=" if m.is_sharp else "<="
        self.left_info.SetInput(
            "Geometry\n"
            f"theta              = {m.theta_degrees:6.2f} deg\n"
            f"v_theta            = ({v0[0]:6.3f}, {v0[1]:6.3f})\n"
            f"P_U v_theta        = ({p0[0]:6.3f}, {p0[1]:6.3f})\n"
            f"sin(theta) leg      = {m.sin_theta:6.3f}\n"
            f"||sin Theta_0||     = {m.sin_theta:6.3f}"
        )
        self.right_info.SetInput(
            "Operator data\n"
            f"A = diag({m.lambda_desired:5.2f}, {m.complement_eigenvalue:5.2f})\n"
            f"A_0 = [{m.rho:5.2f}]\n"
            f"delta            = {m.delta:6.3f}\n"
            f"r = A v_theta - rho v_theta\n"
            f"residual         = ({r[0]:6.3f}, {r[1]:6.3f})\n"
            f"||r||_2          = {m.residual_norm:6.3f}\n"
            f"delta sin(theta) = {m.theorem_lhs:6.3f}\n\n"
            f"THEOREM\n"
            f"  delta * ||sin Theta_0||\n"
            f"  {relation} ||R||\n"
            f"  {m.theorem_lhs:6.3f} {relation} {m.residual_norm:6.3f}"
        )

    def main_slide_text(self) -> str:
        return "Interactive explorer for the rank-one sine-theta theorem"


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--theta", type=float, default=35.0)
    parser.add_argument("--delta", type=float, default=1.0)
    parser.add_argument("--rho", type=float, default=0.0)
    parser.add_argument("--lambda-desired", type=float, default=0.0)
    parser.add_argument("--screenshot", type=Path)
    parser.add_argument(
        "--no-interact",
        action="store_true",
        help="render once and exit; useful with --screenshot or in CI",
    )
    return parser


def main() -> None:
    args = _parser().parse_args()
    model = SineThetaModel.from_degrees(
        args.theta,
        delta=args.delta,
        rho=args.rho,
        lambda_desired=args.lambda_desired,
    )
    scene = SineThetaVTKScene(model, offscreen=args.no_interact)
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
