"""Interactive 4D-to-3D explorer for the Proposition 4.4 counterexample.

Run from ``visualizations/`` with:

    uv run --extra vtk python -m dkvis.vtk_prop44

Two synchronized panels show the actual R^4 direct rotation and competitor
under the same orthogonal 4D-to-3D projection.  Drag the motion slider to see
paths from the identity to the endpoint operators, and drag the 4D-view slider
to rotate one visible coordinate into the hidden fourth coordinate.

Only the endpoints at motion t=1 are the two admissible operators compared in
Proposition 4.4.  Intermediate t values are explanatory interpolation paths.
Projected distances are not used for the theorem; text reports the true R^4
singular values and trace displacement.
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path

import numpy as np
import vtk

from .prop44 import Prop44Model


def _rgb(hex_value: str) -> tuple[float, float, float]:
    value = hex_value.lstrip("#")
    return tuple(int(value[i : i + 2], 16) / 255.0 for i in (0, 2, 4))


COLORS = {
    "background": _rgb("#10141c"),
    "ghost": _rgb("#667085"),
    "u": _rgb("#f2f4f7"),
    "v": _rgb("#f97066"),
    "connector": _rgb("#98a2b3"),
    "text": _rgb("#f9fafb"),
    "m0": _rgb("#f79009"),
    "m1": _rgb("#36bffa"),
    "m2": _rgb("#32d583"),
    "m3": _rgb("#b692f6"),
}
M_COLORS = [COLORS[f"m{i}"] for i in range(4)]


def _line_actor(
    color: tuple[float, float, float],
    *,
    width: float = 3.0,
    opacity: float = 1.0,
) -> tuple[vtk.vtkLineSource, vtk.vtkActor]:
    source = vtk.vtkLineSource()
    mapper = vtk.vtkPolyDataMapper()
    mapper.SetInputConnection(source.GetOutputPort())
    actor = vtk.vtkActor()
    actor.SetMapper(mapper)
    actor.GetProperty().SetColor(*color)
    actor.GetProperty().SetLineWidth(width)
    actor.GetProperty().SetOpacity(opacity)
    return source, actor


def _polyline_actor(
    color: tuple[float, float, float],
    *,
    width: float = 2.0,
    opacity: float = 1.0,
) -> tuple[vtk.vtkPolyData, vtk.vtkActor]:
    data = vtk.vtkPolyData()
    mapper = vtk.vtkPolyDataMapper()
    mapper.SetInputData(data)
    actor = vtk.vtkActor()
    actor.SetMapper(mapper)
    actor.GetProperty().SetColor(*color)
    actor.GetProperty().SetLineWidth(width)
    actor.GetProperty().SetOpacity(opacity)
    return data, actor


def _set_polyline(data: vtk.vtkPolyData, points: np.ndarray, *, closed: bool = False) -> None:
    points = np.asarray(points, dtype=float)
    vtk_points = vtk.vtkPoints()
    for p in points:
        vtk_points.InsertNextPoint(float(p[0]), float(p[1]), float(p[2]))
    cells = vtk.vtkCellArray()
    n = len(points)
    count = n + 1 if closed and n else n
    cells.InsertNextCell(count)
    for idx in range(n):
        cells.InsertCellPoint(idx)
    if closed and n:
        cells.InsertCellPoint(0)
    data.SetPoints(vtk_points)
    data.SetLines(cells)
    data.Modified()


def _text_actor(
    text: str,
    *,
    x: float,
    y: float,
    size: int = 18,
    color: tuple[float, float, float] | None = None,
) -> vtk.vtkTextActor:
    actor = vtk.vtkTextActor()
    actor.SetInput(text)
    actor.GetPositionCoordinate().SetCoordinateSystemToNormalizedViewport()
    actor.SetPosition(x, y)
    prop = actor.GetTextProperty()
    prop.SetFontSize(size)
    prop.SetFontFamilyToCourier()
    prop.SetColor(*(color or COLORS["text"]))
    prop.SetVerticalJustificationToTop()
    return actor


def _sphere_actor(
    color: tuple[float, float, float], *, radius: float = 0.035
) -> vtk.vtkActor:
    source = vtk.vtkSphereSource()
    source.SetRadius(radius)
    source.SetThetaResolution(18)
    source.SetPhiResolution(18)
    mapper = vtk.vtkPolyDataMapper()
    mapper.SetInputConnection(source.GetOutputPort())
    actor = vtk.vtkActor()
    actor.SetMapper(mapper)
    actor.GetProperty().SetColor(*color)
    return actor


class _Panel:
    def __init__(
        self,
        renderer: vtk.vtkRenderer,
        *,
        model: Prop44Model,
        title: str,
        kind: str,
    ) -> None:
        self.renderer = renderer
        self.model = model
        self.title = title
        self.kind = kind

        self.u_data, self.u_actor = _polyline_actor(COLORS["u"], width=2.0, opacity=0.42)
        self.image_data, self.image_actor = _polyline_actor(COLORS["v"], width=4.0, opacity=0.95)
        renderer.AddActor(self.u_actor)
        renderer.AddActor(self.image_actor)

        self.ghost_lines: list[vtk.vtkLineSource] = []
        self.current_lines: list[vtk.vtkLineSource] = []
        self.connectors: list[vtk.vtkLineSource] = []
        self.trail_data: list[vtk.vtkPolyData] = []
        self.endpoints: list[vtk.vtkActor] = []
        self.labels: list[vtk.vtkBillboardTextActor3D] = []

        for idx in range(4):
            ghost_source, ghost_actor = _line_actor(COLORS["ghost"], width=2.0, opacity=0.30)
            current_source, current_actor = _line_actor(M_COLORS[idx], width=5.0, opacity=1.0)
            connector_source, connector_actor = _line_actor(
                COLORS["connector"], width=2.0, opacity=0.55
            )
            trail_data, trail_actor = _polyline_actor(M_COLORS[idx], width=2.0, opacity=0.55)
            endpoint = _sphere_actor(M_COLORS[idx])
            label = vtk.vtkBillboardTextActor3D()
            label.SetInput(f"m{idx}")
            label.GetTextProperty().SetFontSize(15)
            label.GetTextProperty().SetColor(*M_COLORS[idx])

            self.ghost_lines.append(ghost_source)
            self.current_lines.append(current_source)
            self.connectors.append(connector_source)
            self.trail_data.append(trail_data)
            self.endpoints.append(endpoint)
            self.labels.append(label)

            renderer.AddActor(ghost_actor)
            renderer.AddActor(trail_actor)
            renderer.AddActor(connector_actor)
            renderer.AddActor(current_actor)
            renderer.AddActor(endpoint)
            renderer.AddActor(label)

        self.title_actor = _text_actor(title, x=0.03, y=0.96, size=23)
        self.info_actor = _text_actor("", x=0.03, y=0.88, size=16)
        self.legend_actor = _text_actor(
            "gray loop: U    red loop: current image of U\n"
            "colored arrows: common m-basis images\n"
            "gray connectors: projected displacement",
            x=0.03,
            y=0.18,
            size=13,
            color=COLORS["ghost"],
        )
        renderer.AddViewProp(self.title_actor)
        renderer.AddViewProp(self.info_actor)
        renderer.AddViewProp(self.legend_actor)

    def operator_at(self, t: float) -> np.ndarray:
        if self.kind == "direct":
            return self.model.direct_rotation_at(t)
        if self.kind == "competitor":
            return self.model.competitor_at(t)
        raise KeyError(self.kind)

    def endpoint_operator(self) -> np.ndarray:
        return self.model.R if self.kind == "direct" else self.model.W

    def update(self, t: float, view_angle: float) -> None:
        transform = self.operator_at(t)
        M = self.model.m_basis

        initial = self.model.project(M.T, view_angle)
        current4 = (transform @ M).T
        current = self.model.project(current4, view_angle)

        zero = np.zeros(3)
        for idx in range(4):
            self.ghost_lines[idx].SetPoint1(*zero)
            self.ghost_lines[idx].SetPoint2(*initial[idx])
            self.current_lines[idx].SetPoint1(*zero)
            self.current_lines[idx].SetPoint2(*current[idx])
            self.connectors[idx].SetPoint1(*initial[idx])
            self.connectors[idx].SetPoint2(*current[idx])
            self.endpoints[idx].SetPosition(*current[idx])
            label_pos = 1.07 * current[idx]
            self.labels[idx].SetPosition(*label_pos)

            sample_t = np.linspace(0.0, t, 60)
            trail4 = np.array([self.operator_at(float(s)) @ M[:, idx] for s in sample_t])
            _set_polyline(self.trail_data[idx], self.model.project(trail4, view_angle))

        u_circle = self.model.circle_in_u()
        image_circle = u_circle @ transform.T
        _set_polyline(self.u_data, self.model.project(u_circle, view_angle), closed=True)
        _set_polyline(self.image_data, self.model.project(image_circle, view_angle), closed=True)

        sv = self.model.displacement_singular_values(transform)
        trace = float(sv.sum())
        sv_text = ", ".join(f"{x:.3f}" for x in sv)
        if self.kind == "direct":
            mechanism = (
                "endpoint invariant planes:\n"
                "  span(e0,e3): +45 deg\n"
                "  span(e1,e2): -45 deg"
            )
        else:
            mechanism = (
                "endpoint invariant planes:\n"
                "  span(m0,m1): +90 deg\n"
                "  span(m2,m3): fixed"
            )
        endpoint_note = "ENDPOINT: admissible U -> V" if abs(t - 1.0) < 1e-9 else "interpolation only"
        self.info_actor.SetInput(
            f"t = {t:.3f}   {endpoint_note}\n"
            f"true 4D sigma(I-T) = [{sv_text}]\n"
            f"true 4D trace norm = {trace:.6f}\n"
            f"{mechanism}"
        )


class Prop44VTKScene:
    """Side-by-side 4D projection of the direct rotation and competitor."""

    def __init__(self, *, t: float = 1.0, view_angle_degrees: float = 24.0, offscreen: bool = False):
        self.model = Prop44Model()
        self.model.verify()
        self.t = float(np.clip(t, 0.0, 1.0))
        self.view_angle = math.radians(view_angle_degrees)

        self.window = vtk.vtkRenderWindow()
        self.window.SetWindowName("Davis--Kahan Proposition 4.4 counterexample")
        self.window.SetSize(1500, 820)
        if offscreen:
            self.window.SetOffScreenRendering(1)

        self.left = vtk.vtkRenderer()
        self.right = vtk.vtkRenderer()
        self.left.SetViewport(0.0, 0.0, 0.5, 1.0)
        self.right.SetViewport(0.5, 0.0, 1.0, 1.0)
        for renderer in [self.left, self.right]:
            renderer.SetBackground(*COLORS["background"])
            self.window.AddRenderer(renderer)

        self.direct_panel = _Panel(
            self.left,
            model=self.model,
            title="Direct rotation R",
            kind="direct",
        )
        self.competitor_panel = _Panel(
            self.right,
            model=self.model,
            title="Competitor W",
            kind="competitor",
        )

        camera = vtk.vtkCamera()
        camera.SetPosition(3.3, 2.6, 3.7)
        camera.SetFocalPoint(0.0, 0.0, 0.0)
        camera.SetViewUp(0.0, 0.0, 1.0)
        camera.ParallelProjectionOn()
        camera.SetParallelScale(1.55)
        self.left.SetActiveCamera(camera)
        self.right.SetActiveCamera(camera)

        self.interactor = vtk.vtkRenderWindowInteractor()
        self.interactor.SetRenderWindow(self.window)
        style = vtk.vtkInteractorStyleTrackballCamera()
        self.interactor.SetInteractorStyle(style)

        self.footer_left = _text_actor(
            "Both endpoint operators carry the same U onto the same V.\n"
            "Principal angles(U,V) = (45 deg, 45 deg) < 60 deg.",
            x=0.03,
            y=0.09,
            size=14,
        )
        self.footer_right = _text_actor(
            "At t=1:  ||I-W||_* = 2 sqrt(2) = 2.828427\n"
            "          ||I-R||_* = 4 sqrt(2-sqrt(2)) = 3.061467\n"
            "So W beats R in trace norm.",
            x=0.03,
            y=0.09,
            size=14,
        )
        self.left.AddViewProp(self.footer_left)
        self.right.AddViewProp(self.footer_right)

        self.motion_slider: vtk.vtkSliderWidget | None = None
        self.view_slider: vtk.vtkSliderWidget | None = None
        if not offscreen:
            self._add_sliders()

        self.update()

    def _slider(
        self,
        *,
        title: str,
        minimum: float,
        maximum: float,
        value: float,
        y: float,
    ) -> vtk.vtkSliderWidget:
        rep = vtk.vtkSliderRepresentation2D()
        rep.SetMinimumValue(minimum)
        rep.SetMaximumValue(maximum)
        rep.SetValue(value)
        rep.SetTitleText(title)
        rep.GetPoint1Coordinate().SetCoordinateSystemToNormalizedDisplay()
        rep.GetPoint1Coordinate().SetValue(0.22, y)
        rep.GetPoint2Coordinate().SetCoordinateSystemToNormalizedDisplay()
        rep.GetPoint2Coordinate().SetValue(0.78, y)
        rep.SetSliderLength(0.02)
        rep.SetSliderWidth(0.025)
        rep.SetTubeWidth(0.005)
        rep.GetTitleProperty().SetColor(*COLORS["text"])
        rep.GetLabelProperty().SetColor(*COLORS["text"])
        rep.GetSliderProperty().SetColor(*COLORS["v"])
        rep.GetTubeProperty().SetColor(*COLORS["ghost"])

        widget = vtk.vtkSliderWidget()
        widget.SetInteractor(self.interactor)
        widget.SetRepresentation(rep)
        widget.SetAnimationModeToAnimate()
        widget.EnabledOn()
        return widget

    def _add_sliders(self) -> None:
        self.motion_slider = self._slider(
            title="motion t (endpoint comparison is t=1)",
            minimum=0.0,
            maximum=1.0,
            value=self.t,
            y=0.055,
        )
        self.view_slider = self._slider(
            title="4D view angle (degrees)",
            minimum=0.0,
            maximum=360.0,
            value=math.degrees(self.view_angle) % 360.0,
            y=0.018,
        )

        def motion_callback(widget, _event):
            self.t = float(widget.GetRepresentation().GetValue())
            self.update()
            self.window.Render()

        def view_callback(widget, _event):
            self.view_angle = math.radians(float(widget.GetRepresentation().GetValue()))
            self.update()
            self.window.Render()

        self.motion_slider.AddObserver(vtk.vtkCommand.InteractionEvent, motion_callback)
        self.view_slider.AddObserver(vtk.vtkCommand.InteractionEvent, view_callback)

    def update(self) -> None:
        self.direct_panel.update(self.t, self.view_angle)
        self.competitor_panel.update(self.t, self.view_angle)

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
    parser.add_argument("--t", type=float, default=1.0, help="motion parameter in [0,1]")
    parser.add_argument("--view-angle", type=float, default=24.0, help="4D view angle in degrees")
    parser.add_argument("--screenshot", type=Path)
    parser.add_argument(
        "--no-interact",
        action="store_true",
        help="render once and exit; useful with --screenshot or in CI",
    )
    return parser


def main() -> None:
    args = _parser().parse_args()
    if not 0.0 <= args.t <= 1.0:
        raise SystemExit("--t must lie in [0,1]")
    scene = Prop44VTKScene(
        t=args.t,
        view_angle_degrees=args.view_angle,
        offscreen=args.no_interact,
    )
    if args.screenshot is not None:
        scene.screenshot(args.screenshot)
    if args.no_interact:
        scene.render()
    else:
        scene.interact()


if __name__ == "__main__":
    main()
