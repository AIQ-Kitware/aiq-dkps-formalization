"""Interactive VTK explorer for the rank-one sine-theta theorem.

Run from ``visualizations/`` with, for example:

    uv run --extra vtk python -m dkvis.vtk_sine_theta

Drag the slider to rotate the trial subspace.  The scene shows the exact
subspace, the trial vector, its projection, the complementary projection
(the rectangular sine block), and the residual entering the theorem.
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path

import numpy as np
import vtk

from .sine_theta import SineThetaModel


def _rgb(hex_value: str) -> tuple[float, float, float]:
    value = hex_value.lstrip("#")
    return tuple(int(value[i : i + 2], 16) / 255.0 for i in (0, 2, 4))


COLORS = {
    "background": _rgb("#10141c"),
    "axes": _rgb("#667085"),
    "desired": _rgb("#f2f4f7"),
    "trial": _rgb("#fdb022"),
    "projection": _rgb("#32d583"),
    "sine": _rgb("#ee46bc"),
    "residual": _rgb("#36bffa"),
    "angle": _rgb("#f97066"),
    "text": _rgb("#f9fafb"),
}


def _line_actor(
    start: np.ndarray,
    end: np.ndarray,
    *,
    color: tuple[float, float, float],
    width: float = 3.0,
    dashed: bool = False,
) -> tuple[vtk.vtkLineSource, vtk.vtkActor]:
    source = vtk.vtkLineSource()
    source.SetPoint1(float(start[0]), float(start[1]), 0.0)
    source.SetPoint2(float(end[0]), float(end[1]), 0.0)
    mapper = vtk.vtkPolyDataMapper()
    mapper.SetInputConnection(source.GetOutputPort())
    actor = vtk.vtkActor()
    actor.SetMapper(mapper)
    actor.GetProperty().SetColor(*color)
    actor.GetProperty().SetLineWidth(width)
    if dashed:
        actor.GetProperty().SetLineStipplePattern(0x00FF)
        actor.GetProperty().SetLineStippleRepeatFactor(1)
    return source, actor


def _polyline_actor(
    points: np.ndarray,
    *,
    color: tuple[float, float, float],
    width: float = 3.0,
) -> tuple[vtk.vtkPolyData, vtk.vtkActor]:
    vtk_points = vtk.vtkPoints()
    for x, y in points:
        vtk_points.InsertNextPoint(float(x), float(y), 0.0)
    cells = vtk.vtkCellArray()
    cells.InsertNextCell(len(points))
    for idx in range(len(points)):
        cells.InsertCellPoint(idx)
    data = vtk.vtkPolyData()
    data.SetPoints(vtk_points)
    data.SetLines(cells)
    mapper = vtk.vtkPolyDataMapper()
    mapper.SetInputData(data)
    actor = vtk.vtkActor()
    actor.SetMapper(mapper)
    actor.GetProperty().SetColor(*color)
    actor.GetProperty().SetLineWidth(width)
    return data, actor


def _text_actor(text: str, *, x: int, y: int, size: int = 20) -> vtk.vtkTextActor:
    actor = vtk.vtkTextActor()
    actor.SetInput(text)
    actor.SetDisplayPosition(x, y)
    prop = actor.GetTextProperty()
    prop.SetFontSize(size)
    prop.SetColor(*COLORS["text"])
    prop.SetFontFamilyToCourier()
    return actor


class SineThetaVTKScene:
    def __init__(
        self,
        model: SineThetaModel,
        *,
        width: int = 1100,
        height: int = 760,
        offscreen: bool = False,
    ) -> None:
        self.delta = model.delta
        self.rho = model.rho
        self.lambda_desired = model.lambda_desired
        self.model = model

        self.renderer = vtk.vtkRenderer()
        self.renderer.SetBackground(*COLORS["background"])
        self.window = vtk.vtkRenderWindow()
        self.window.SetSize(width, height)
        self.window.SetWindowName("Davis--Kahan sine-theta explorer")
        self.window.AddRenderer(self.renderer)
        if offscreen:
            self.window.SetOffScreenRendering(1)

        self.interactor = vtk.vtkRenderWindowInteractor()
        self.interactor.SetRenderWindow(self.window)
        style = vtk.vtkInteractorStyleTrackballCamera()
        self.interactor.SetInteractorStyle(style)

        self._build_static_geometry()
        self._build_dynamic_geometry()
        self._build_overlay()
        self._build_slider()
        self.update(model.theta_degrees)

        camera = self.renderer.GetActiveCamera()
        camera.SetPosition(0.0, 0.0, 6.0)
        camera.SetFocalPoint(0.0, 0.0, 0.0)
        camera.SetViewUp(0.0, 1.0, 0.0)
        camera.ParallelProjectionOn()
        camera.SetParallelScale(1.65)

    def _build_static_geometry(self) -> None:
        _, x_axis = _line_actor(
            np.array([-1.45, 0.0]), np.array([1.45, 0.0]), color=COLORS["axes"], width=1.0
        )
        _, y_axis = _line_actor(
            np.array([0.0, -1.45]), np.array([0.0, 1.45]), color=COLORS["axes"], width=1.0
        )
        _, desired = _line_actor(
            np.array([-1.35, 0.0]), np.array([1.35, 0.0]), color=COLORS["desired"], width=5.0
        )
        self.renderer.AddActor(x_axis)
        self.renderer.AddActor(y_axis)
        self.renderer.AddActor(desired)

    def _build_dynamic_geometry(self) -> None:
        zero = np.zeros(2)
        self.trial_source, trial_actor = _line_actor(zero, zero, color=COLORS["trial"], width=4.0)
        self.vector_source, vector_actor = _line_actor(zero, zero, color=COLORS["trial"], width=8.0)
        self.proj_source, proj_actor = _line_actor(zero, zero, color=COLORS["projection"], width=6.0)
        self.sine_source, sine_actor = _line_actor(zero, zero, color=COLORS["sine"], width=8.0)
        self.residual_source, residual_actor = _line_actor(zero, zero, color=COLORS["residual"], width=5.0)
        self.angle_data, angle_actor = _polyline_actor(
            np.zeros((24, 2)), color=COLORS["angle"], width=4.0
        )

        for actor in [trial_actor, vector_actor, proj_actor, sine_actor, residual_actor, angle_actor]:
            self.renderer.AddActor(actor)

    def _build_overlay(self) -> None:
        self.title = _text_actor("Davis--Kahan sin Theta: rank-one sharp model", x=24, y=710, size=26)
        self.info = _text_actor("", x=24, y=500, size=19)
        self.legend = _text_actor(
            "white: exact U    yellow: trial V / v\n"
            "green: P_U v     magenta: (I-P_U)v\n"
            "cyan: residual r = A v - rho v",
            x=24,
            y=28,
            size=17,
        )
        self.renderer.AddViewProp(self.title)
        self.renderer.AddViewProp(self.info)
        self.renderer.AddViewProp(self.legend)

    def _build_slider(self) -> None:
        rep = vtk.vtkSliderRepresentation2D()
        rep.SetMinimumValue(0.0)
        rep.SetMaximumValue(85.0)
        rep.SetValue(self.model.theta_degrees)
        rep.SetTitleText("theta (degrees)")
        rep.GetPoint1Coordinate().SetCoordinateSystemToNormalizedDisplay()
        rep.GetPoint1Coordinate().SetValue(0.58, 0.08)
        rep.GetPoint2Coordinate().SetCoordinateSystemToNormalizedDisplay()
        rep.GetPoint2Coordinate().SetValue(0.94, 0.08)
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

    def update(self, theta_degrees: float) -> None:
        self.model = SineThetaModel.from_degrees(
            theta_degrees,
            delta=self.delta,
            rho=self.rho,
            lambda_desired=self.lambda_desired,
        )
        self.model.verify()
        m = self.model
        v = m.trial_vector
        p = m.desired_projection
        s = m.sine_block_vector
        r = m.residual

        self._set_line(self.trial_source, -1.35 * v, 1.35 * v)
        self._set_line(self.vector_source, np.zeros(2), v)
        self._set_line(self.proj_source, np.zeros(2), p)
        self._set_line(self.sine_source, p, v)

        self._set_line(self.residual_source, np.zeros(2), r)

        arc_angles = np.linspace(0.0, m.theta, 24)
        radius = 0.28
        points = np.column_stack([radius * np.cos(arc_angles), radius * np.sin(arc_angles)])
        vtk_points = self.angle_data.GetPoints()
        for idx, (x, y) in enumerate(points):
            vtk_points.SetPoint(idx, float(x), float(y), 0.0)
        vtk_points.Modified()
        self.angle_data.Modified()

        relation = "=" if m.is_sharp else "<="
        self.info.SetInput(
            f"theta            = {m.theta_degrees:6.2f} deg\n"
            f"sin(theta)       = {m.sin_theta:6.3f}\n"
            f"delta            = {m.delta:6.3f}\n"
            f"residual norm    = {m.residual_norm:6.3f}\n"
            f"delta sin(theta) = {m.theorem_lhs:6.3f}\n\n"
            f"THEOREM: {m.theorem_lhs:6.3f} {relation} {m.residual_norm:6.3f}"
        )

    def render(self) -> None:
        self.window.Render()

    def interact(self) -> None:
        self.render()
        self.interactor.Initialize()
        self.interactor.Start()

    def screenshot(self, path: Path) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        self.render()
        capture = vtk.vtkWindowToImageFilter()
        capture.SetInput(self.window)
        capture.SetScale(1)
        capture.SetInputBufferTypeToRGB()
        capture.ReadFrontBufferOff()
        capture.Update()
        writer = vtk.vtkPNGWriter()
        writer.SetFileName(str(path))
        writer.SetInputConnection(capture.GetOutputPort())
        writer.Write()


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
