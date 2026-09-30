"""Interactive exact 2D invariant-plane view of Proposition 4.4.

Run from ``visualizations/`` with::

    uv run --extra vtk python -m dkvis.vtk_prop44

The four panels are exact two-dimensional restrictions of the two endpoint
operators in the R^4 counterexample.  No 4D-to-3D projection is used.

Left column -- direct rotation R:

* span(e0,e3): +45 degree rotation;
* span(e1,e2): -45 degree rotation.

Right column -- admissible competitor W:

* span(m0,m1): +90 degree rotation;
* span(m2,m3): identity.

The common motion slider interpolates each local rotation from the identity to
its endpoint.  Only t=1 is the Proposition 4.4 comparison; intermediate values
are explanatory animation states.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
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
    "control_background": _rgb("#171c26"),
    "ghost": _rgb("#667085"),
    "text": _rgb("#f9fafb"),
    "muted": _rgb("#98a2b3"),
    "basis0": _rgb("#f79009"),
    "basis1": _rgb("#36bffa"),
    "displacement": _rgb("#d0d5dd"),
    "arc": _rgb("#f97066"),
    "direct": _rgb("#84caff"),
    "competitor": _rgb("#73e2a3"),
}


@dataclass(frozen=True)
class PlaneSpec:
    title: str
    basis_names: tuple[str, str]
    endpoint_angle: float
    source_note: str
    family: str

    @property
    def endpoint_degrees(self) -> float:
        return math.degrees(self.endpoint_angle)


def _text_actor(
    text: str,
    *,
    x: float,
    y: float,
    size: int = 16,
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
    for point in points:
        vtk_points.InsertNextPoint(float(point[0]), float(point[1]), float(point[2]))
    cells = vtk.vtkCellArray()
    n = len(points)
    cells.InsertNextCell(n + (1 if closed and n else 0))
    for idx in range(n):
        cells.InsertCellPoint(idx)
    if closed and n:
        cells.InsertCellPoint(0)
    data.SetPoints(vtk_points)
    data.SetLines(cells)
    data.Modified()


def _line_actor(
    color: tuple[float, float, float],
    *,
    width: float = 2.0,
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


def _arrow_actor(
    color: tuple[float, float, float],
    *,
    opacity: float = 1.0,
) -> vtk.vtkActor:
    source = vtk.vtkArrowSource()
    source.SetTipResolution(24)
    source.SetShaftResolution(24)
    source.SetTipLength(0.20)
    source.SetTipRadius(0.07)
    source.SetShaftRadius(0.018)
    mapper = vtk.vtkPolyDataMapper()
    mapper.SetInputConnection(source.GetOutputPort())
    actor = vtk.vtkActor()
    actor.SetMapper(mapper)
    actor.GetProperty().SetColor(*color)
    actor.GetProperty().SetOpacity(opacity)
    return actor


def _set_arrow(actor: vtk.vtkActor, vector: np.ndarray) -> None:
    vector = np.asarray(vector, dtype=float)
    length = float(np.linalg.norm(vector[:2]))
    angle = math.degrees(math.atan2(float(vector[1]), float(vector[0]))) if length else 0.0
    actor.SetPosition(0.0, 0.0, 0.0)
    actor.SetOrientation(0.0, 0.0, angle)
    actor.SetScale(length, 1.0, 1.0)


def _label3d(text: str, color: tuple[float, float, float]) -> vtk.vtkBillboardTextActor3D:
    actor = vtk.vtkBillboardTextActor3D()
    actor.SetInput(text)
    prop = actor.GetTextProperty()
    prop.SetFontSize(15)
    prop.SetColor(*color)
    prop.SetJustificationToCentered()
    return actor


class PlanePanel:
    """One exact 2D invariant-plane restriction of R or W."""

    def __init__(self, renderer: vtk.vtkRenderer, model: Prop44Model, spec: PlaneSpec) -> None:
        self.renderer = renderer
        self.model = model
        self.spec = spec

        circle_angles = np.linspace(0.0, 2.0 * math.pi, 129)
        circle = np.column_stack(
            [np.cos(circle_angles), np.sin(circle_angles), np.zeros_like(circle_angles)]
        )
        self.circle_data, self.circle_actor = _polyline_actor(COLORS["ghost"], width=1.5, opacity=0.45)
        _set_polyline(self.circle_data, circle)
        renderer.AddActor(self.circle_actor)

        self.axis_x_source, self.axis_x_actor = _line_actor(COLORS["ghost"], width=1.0, opacity=0.30)
        self.axis_y_source, self.axis_y_actor = _line_actor(COLORS["ghost"], width=1.0, opacity=0.30)
        self.axis_x_source.SetPoint1(-1.22, 0.0, 0.0)
        self.axis_x_source.SetPoint2(1.22, 0.0, 0.0)
        self.axis_y_source.SetPoint1(0.0, -1.22, 0.0)
        self.axis_y_source.SetPoint2(0.0, 1.22, 0.0)
        renderer.AddActor(self.axis_x_actor)
        renderer.AddActor(self.axis_y_actor)

        self.initial_arrows = [
            _arrow_actor(COLORS["ghost"], opacity=0.32),
            _arrow_actor(COLORS["ghost"], opacity=0.32),
        ]
        self.current_arrows = [
            _arrow_actor(COLORS["basis0"]),
            _arrow_actor(COLORS["basis1"]),
        ]
        for actor in self.initial_arrows + self.current_arrows:
            renderer.AddActor(actor)
        _set_arrow(self.initial_arrows[0], np.array([1.0, 0.0, 0.0]))
        _set_arrow(self.initial_arrows[1], np.array([0.0, 1.0, 0.0]))

        self.connectors: list[vtk.vtkLineSource] = []
        for _ in range(2):
            source, actor = _line_actor(COLORS["displacement"], width=2.0, opacity=0.65)
            self.connectors.append(source)
            renderer.AddActor(actor)

        self.arc_data, self.arc_actor = _polyline_actor(COLORS["arc"], width=4.0, opacity=0.95)
        renderer.AddActor(self.arc_actor)

        self.initial_labels = [
            _label3d(spec.basis_names[0], COLORS["muted"]),
            _label3d(spec.basis_names[1], COLORS["muted"]),
        ]
        for actor in self.initial_labels:
            renderer.AddActor(actor)
        self.initial_labels[0].SetPosition(1.16, -0.08, 0.0)
        self.initial_labels[1].SetPosition(0.10, 1.14, 0.0)

        family_color = COLORS["direct"] if spec.family == "R" else COLORS["competitor"]
        self.title_actor = _text_actor(spec.title, x=0.025, y=0.965, size=20, color=family_color)
        self.info_actor = _text_actor("", x=0.025, y=0.855, size=14)
        self.note_actor = _text_actor(spec.source_note, x=0.025, y=0.125, size=12, color=COLORS["muted"])
        renderer.AddViewProp(self.title_actor)
        renderer.AddViewProp(self.info_actor)
        renderer.AddViewProp(self.note_actor)

        camera = vtk.vtkCamera()
        camera.SetPosition(0.0, 0.0, 5.0)
        camera.SetFocalPoint(0.0, 0.0, 0.0)
        camera.SetViewUp(0.0, 1.0, 0.0)
        camera.ParallelProjectionOn()
        camera.SetParallelScale(1.63)
        renderer.SetActiveCamera(camera)

    def update(self, t: float) -> None:
        angle = float(t) * self.spec.endpoint_angle
        c = math.cos(angle)
        s = math.sin(angle)
        current = [np.array([c, s, 0.0]), np.array([-s, c, 0.0])]
        initial = [np.array([1.0, 0.0, 0.0]), np.array([0.0, 1.0, 0.0])]

        for idx in range(2):
            _set_arrow(self.current_arrows[idx], current[idx])
            self.connectors[idx].SetPoint1(*initial[idx])
            self.connectors[idx].SetPoint2(*current[idx])

        if abs(angle) < 1e-12:
            arc = np.array([[0.72, 0.0, 0.0], [0.72, 0.0, 0.0]])
        else:
            samples = np.linspace(0.0, angle, 48)
            arc = np.column_stack(
                [0.72 * np.cos(samples), 0.72 * np.sin(samples), np.zeros_like(samples)]
            )
        _set_polyline(self.arc_data, arc)

        sigma = self.model.rotation_plane_singular_value(angle)
        trace_contribution = self.model.rotation_plane_trace_displacement(angle)
        endpoint = "endpoint" if abs(t - 1.0) < 1e-9 else "interpolation"
        self.info_actor.SetInput(
            f"angle = {math.degrees(angle):+6.1f} deg   ({endpoint})\n"
            f"plane sigma(I-T) = [{sigma:.6f}, {sigma:.6f}]\n"
            f"trace contribution = {trace_contribution:.6f}"
        )


class Prop44VTKScene:
    """Four synchronized exact 2D views of the Proposition 4.4 witness."""

    def __init__(self, *, t: float = 1.0, offscreen: bool = False) -> None:
        self.model = Prop44Model()
        self.model.verify()
        self.t = float(np.clip(t, 0.0, 1.0))

        self.window = vtk.vtkRenderWindow()
        self.window.SetWindowName("Davis--Kahan Proposition 4.4: exact 2D plane decompositions")
        self.window.SetSize(1500, 950)
        if offscreen:
            self.window.SetOffScreenRendering(1)

        control_fraction = 0.20
        split_y = (1.0 + control_fraction) / 2.0
        viewports = [
            (0.0, split_y, 0.5, 1.0),
            (0.0, control_fraction, 0.5, split_y),
            (0.5, split_y, 1.0, 1.0),
            (0.5, control_fraction, 1.0, split_y),
        ]
        self.renderers: list[vtk.vtkRenderer] = []
        for viewport in viewports:
            renderer = vtk.vtkRenderer()
            renderer.SetViewport(*viewport)
            renderer.SetBackground(*COLORS["background"])
            self.window.AddRenderer(renderer)
            self.renderers.append(renderer)

        specs = [
            PlaneSpec(
                title="R plane 1: span(e0,e3)",
                basis_names=("e0", "e3"),
                endpoint_angle=self.model.direct_plane_angles[0],
                source_note="U intersects this plane in span(e0).  R rotates that U direction toward V by +45 deg.",
                family="R",
            ),
            PlaneSpec(
                title="R plane 2: span(e1,e2)",
                basis_names=("e1", "e2"),
                endpoint_angle=self.model.direct_plane_angles[1],
                source_note="U intersects this plane in span(e1).  R rotates that U direction toward V by -45 deg.",
                family="R",
            ),
            PlaneSpec(
                title="W moving plane: span(m0,m1)",
                basis_names=("m0", "m1"),
                endpoint_angle=self.model.competitor_plane_angles[0],
                source_note="U projected into this plane: e0 -> m0/sqrt(2), e1 -> m1/sqrt(2).\nW quarter-turns both projected components.",
                family="W",
            ),
            PlaneSpec(
                title="W fixed plane: span(m2,m3)",
                basis_names=("m2", "m3"),
                endpoint_angle=self.model.competitor_plane_angles[1],
                source_note="U projected into this plane: e0 -> m2/sqrt(2), e1 -> m3/sqrt(2).\nW leaves both projected components fixed.",
                family="W",
            ),
        ]
        self.panels = [
            PlanePanel(self.renderers[idx], self.model, specs[idx]) for idx in range(4)
        ]

        self.controls = vtk.vtkRenderer()
        self.controls.SetViewport(0.0, 0.0, 1.0, control_fraction)
        self.controls.SetBackground(*COLORS["control_background"])
        self.window.AddRenderer(self.controls)

        self.summary_left = _text_actor("", x=0.018, y=0.91, size=14)
        self.summary_right = _text_actor("", x=0.505, y=0.91, size=14)
        self.global_fact = _text_actor("", x=0.018, y=0.35, size=12, color=COLORS["muted"])
        self.motion_help = _text_actor("", x=0.018, y=0.13, size=12, color=COLORS["muted"])
        for actor in [self.summary_left, self.summary_right, self.global_fact, self.motion_help]:
            self.controls.AddViewProp(actor)

        self.interactor = vtk.vtkRenderWindowInteractor()
        self.interactor.SetRenderWindow(self.window)
        self.interactor.SetInteractorStyle(vtk.vtkInteractorStyleImage())

        self.motion_slider = self._make_slider()
        self.motion_slider.AddObserver(vtk.vtkCommand.InteractionEvent, self._motion_callback)

        self.update()

    def _make_slider(self) -> vtk.vtkSliderWidget:
        rep = vtk.vtkSliderRepresentation2D()
        rep.SetMinimumValue(0.0)
        rep.SetMaximumValue(1.0)
        rep.SetValue(self.t)
        rep.SetTitleText("")
        rep.ShowSliderLabelOff()
        rep.GetPoint1Coordinate().SetCoordinateSystemToNormalizedDisplay()
        rep.GetPoint1Coordinate().SetValue(0.58, 0.040)
        rep.GetPoint2Coordinate().SetCoordinateSystemToNormalizedDisplay()
        rep.GetPoint2Coordinate().SetValue(0.95, 0.040)
        rep.SetSliderLength(0.018)
        rep.SetSliderWidth(0.022)
        rep.SetTubeWidth(0.004)
        rep.GetSliderProperty().SetColor(*COLORS["arc"])
        rep.GetTubeProperty().SetColor(*COLORS["ghost"])

        widget = vtk.vtkSliderWidget()
        widget.SetInteractor(self.interactor)
        widget.SetRepresentation(rep)
        widget.SetAnimationModeToAnimate()
        widget.EnabledOn()
        return widget

    def _motion_callback(self, widget, _event) -> None:
        self.t = float(widget.GetRepresentation().GetValue())
        self.update()
        self.window.Render()

    def update(self) -> None:
        for panel in self.panels:
            panel.update(self.t)

        direct_angles = [self.t * angle for angle in self.model.direct_plane_angles]
        competitor_angles = [self.t * angle for angle in self.model.competitor_plane_angles]
        direct_contrib = [
            self.model.rotation_plane_trace_displacement(angle) for angle in direct_angles
        ]
        competitor_contrib = [
            self.model.rotation_plane_trace_displacement(angle) for angle in competitor_angles
        ]
        direct_total = sum(direct_contrib)
        competitor_total = sum(competitor_contrib)

        endpoint_note = "PROPOSITION 4.4 ENDPOINT" if abs(self.t - 1.0) < 1e-9 else "explanatory interpolation"
        self.summary_left.SetInput(
            "DIRECT ROTATION R\n"
            f"plane contributions: {direct_contrib[0]:.6f} + {direct_contrib[1]:.6f}\n"
            f"trace norm of I-R(t) = {direct_total:.6f}"
        )
        comparison = "W < R" if competitor_total < direct_total - 1e-12 else "compare at t=1"
        self.summary_right.SetInput(
            "COMPETITOR W\n"
            f"plane contributions: {competitor_contrib[0]:.6f} + {competitor_contrib[1]:.6f}\n"
            f"trace norm of I-W(t) = {competitor_total:.6f}    {comparison}"
        )
        self.global_fact.SetInput(
            "At t=1: both operators carry the same U to V; principal angles(U,V)=(45 deg,45 deg)<60 deg.  "
            "Gray = initial plane basis; orange/blue = its image."
        )
        self.motion_help.SetInput(f"MOTION t = {self.t:.3f}   {endpoint_note}")

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
    scene = Prop44VTKScene(t=args.t, offscreen=args.no_interact)
    if args.screenshot is not None:
        scene.screenshot(args.screenshot)
    if args.no_interact:
        scene.render()
    else:
        scene.interact()


if __name__ == "__main__":
    main()
