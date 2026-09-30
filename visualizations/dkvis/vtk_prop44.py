"""Interactive exact 2D invariant-plane view of Proposition 4.4.

Run from ``visualizations/`` with::

    uv run --extra vtk python -m dkvis.vtk_prop44

The scene avoids any 4D-to-3D projection.  Instead it shows four exact
2-dimensional restrictions of the two operators acting between the two
2-planes

* U = span(e0, e1),
* V = R(U) = W(U)  inside R^4.

The source slice U and the destination slice V stay visible at every slider
position, so any screenshot can serve directly as a slide.  White arrows show
where the current interpolation sits between source and endpoint.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import math
from pathlib import Path

import numpy as np
import vtk

from .prop44 import Prop44Model
from .vtk_prop44_common import (
    COLORS,
    add_reference_frame,
    arrow_actor,
    configure_2d_camera,
    label3d,
    line_actor,
    polyline_actor,
    set_arrow,
    set_polyline,
    text_actor,
)


def _rotation_block(angle: float) -> np.ndarray:
    c = math.cos(angle)
    s = math.sin(angle)
    return np.array([[c, -s], [s, c]], dtype=float)


@dataclass
class PlaneSpec:
    title: str
    basis_names: tuple[str, str]
    endpoint_angle: float
    source_note: str
    family: str
    source_frame: np.ndarray
    endpoint_frame: np.ndarray
    source_names: tuple[str, str]
    endpoint_names: tuple[str, str]


class PlanePanel:
    """One exact 2D invariant-plane restriction of R or W."""

    def __init__(
        self,
        renderer: vtk.vtkRenderer,
        model: Prop44Model,
        spec: PlaneSpec,
        *,
        show_current: bool = True,
    ) -> None:
        self.renderer = renderer
        self.model = model
        self.spec = spec
        self.show_current = show_current

        add_reference_frame(renderer)

        self.axis_labels = [
            label3d(spec.basis_names[0], COLORS["muted"]),
            label3d(spec.basis_names[1], COLORS["muted"]),
        ]
        self.axis_labels[0].SetPosition(1.16, -0.08, 0.0)
        self.axis_labels[1].SetPosition(0.10, 1.14, 0.0)
        for actor in self.axis_labels:
            renderer.AddActor(actor)

        self.source_arrows = [
            arrow_actor(COLORS["u0"], opacity=0.82, shaft_radius=0.014, tip_radius=0.055),
            arrow_actor(COLORS["u1"], opacity=0.82, shaft_radius=0.014, tip_radius=0.055),
        ]
        self.endpoint_arrows = [
            arrow_actor(COLORS["v0"], opacity=0.94, shaft_radius=0.016, tip_radius=0.060),
            arrow_actor(COLORS["v1"], opacity=0.94, shaft_radius=0.016, tip_radius=0.060),
        ]
        self.current_arrows = [
            arrow_actor(COLORS["current"], opacity=0.98, shaft_radius=0.012, tip_radius=0.048),
            arrow_actor(COLORS["current"], opacity=0.98, shaft_radius=0.012, tip_radius=0.048),
        ]
        for actor in self.source_arrows + self.endpoint_arrows + self.current_arrows:
            renderer.AddActor(actor)
        if not self.show_current:
            for actor in self.current_arrows:
                actor.SetVisibility(False)

        self.source_labels = [label3d(spec.source_names[0], COLORS["u0"]), label3d(spec.source_names[1], COLORS["u1"])]
        self.endpoint_labels = [
            label3d(spec.endpoint_names[0], COLORS["v0"]),
            label3d(spec.endpoint_names[1], COLORS["v1"]),
        ]
        self.current_labels = [label3d("T_t", COLORS["current"], size=13), label3d("T_t", COLORS["current"], size=13)]
        for actor in self.source_labels + self.endpoint_labels + self.current_labels:
            renderer.AddActor(actor)
        if not self.show_current:
            for actor in self.current_labels:
                actor.SetVisibility(False)

        self.connectors: list[vtk.vtkLineSource] = []
        self.connector_actors = []
        for _ in range(2):
            source, actor = line_actor(COLORS["connector"], width=2.0, opacity=0.40)
            self.connectors.append(source)
            self.connector_actors.append(actor)
            renderer.AddActor(actor)
        if not self.show_current:
            for actor in self.connector_actors:
                actor.SetVisibility(False)

        self.arc_data, self.arc_actor = polyline_actor(COLORS["accent"], width=4.0, opacity=0.95)
        renderer.AddActor(self.arc_actor)

        family_color = COLORS["direct"] if spec.family == "R" else COLORS["competitor"]
        self.title_actor = text_actor(spec.title, x=0.025, y=0.965, size=20, color=family_color)
        self.info_actor = text_actor("", x=0.025, y=0.850, size=14)
        self.note_actor = text_actor(spec.source_note, x=0.025, y=0.150, size=12, color=COLORS["muted"])
        renderer.AddViewProp(self.title_actor)
        renderer.AddViewProp(self.info_actor)
        renderer.AddViewProp(self.note_actor)

        configure_2d_camera(renderer)

    def _set_label_position(self, actor: vtk.vtkBillboardTextActor3D, vec2: np.ndarray, visible: bool) -> None:
        if not visible:
            actor.SetVisibility(False)
            return
        norm = float(np.linalg.norm(vec2))
        unit = vec2 / norm if norm > 1e-9 else np.array([1.0, 0.0])
        offset = 0.12 * unit
        actor.SetPosition(float(vec2[0] + offset[0]), float(vec2[1] + offset[1]), 0.0)
        actor.SetVisibility(True)

    def update(self, t: float) -> None:
        angle = float(t) * self.spec.endpoint_angle
        current_frame = _rotation_block(angle) @ self.spec.source_frame

        for idx in range(self.spec.source_frame.shape[1]):
            source_vec = self.spec.source_frame[:, idx]
            endpoint_vec = self.spec.endpoint_frame[:, idx]
            current_vec = current_frame[:, idx]

            source_visible = set_arrow(self.source_arrows[idx], np.r_[source_vec, 0.0])
            endpoint_visible = set_arrow(self.endpoint_arrows[idx], np.r_[endpoint_vec, 0.0])
            current_visible = False
            if self.show_current:
                current_visible = set_arrow(self.current_arrows[idx], np.r_[current_vec, 0.0])
            else:
                self.current_arrows[idx].SetVisibility(False)

            self._set_label_position(self.source_labels[idx], source_vec, source_visible)
            self._set_label_position(self.endpoint_labels[idx], endpoint_vec, endpoint_visible)
            self._set_label_position(self.current_labels[idx], current_vec, current_visible)

            if self.show_current:
                self.connectors[idx].SetPoint1(float(current_vec[0]), float(current_vec[1]), 0.0)
                self.connectors[idx].SetPoint2(float(endpoint_vec[0]), float(endpoint_vec[1]), 0.0)

        if abs(angle) < 1e-12:
            arc = np.array([[0.72, 0.0, 0.0], [0.72, 0.0, 0.0]])
        else:
            samples = np.linspace(0.0, angle, 48)
            arc = np.column_stack(
                [0.72 * np.cos(samples), 0.72 * np.sin(samples), np.zeros_like(samples)]
            )
        set_polyline(self.arc_data, arc)

        sigma = self.model.rotation_plane_singular_value(angle)
        trace_contribution = self.model.rotation_plane_trace_displacement(angle)
        endpoint = "endpoint" if abs(t - 1.0) < 1e-9 else "interpolation"
        self.info_actor.SetInput(
            f"plane angle = {math.degrees(angle):+6.1f} deg   ({endpoint})\n"
            f"plane sigma(I-T_t) = [{sigma:.6f}, {sigma:.6f}]\n"
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
        self.window.SetSize(1600, 980)
        if offscreen:
            self.window.SetOffScreenRendering(1)

        control_fraction = 0.24
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
            renderer.SetBackground(*COLORS["panel_background"])
            self.window.AddRenderer(renderer)
            self.renderers.append(renderer)

        direct_sources = self.model.direct_source_local_frames
        direct_endpoints = self.model.direct_endpoint_local_frames
        competitor_sources = self.model.competitor_source_local_frames
        competitor_endpoints = self.model.competitor_endpoint_local_frames
        specs = [
            PlaneSpec(
                title="R plane 1: span(e0,e3)",
                basis_names=("e0", "e3"),
                endpoint_angle=self.model.direct_plane_angles[0],
                source_note="This plane contains the source direction e0.\nThe direct rotation carries e0 to R e0.",
                family="R",
                source_frame=direct_sources[0],
                endpoint_frame=direct_endpoints[0],
                source_names=("e0", "e1"),
                endpoint_names=("Re0", "Re1"),
            ),
            PlaneSpec(
                title="R plane 2: span(e1,e2)",
                basis_names=("e1", "e2"),
                endpoint_angle=self.model.direct_plane_angles[1],
                source_note="This plane contains the source direction e1.\nThe direct rotation carries e1 to R e1.",
                family="R",
                source_frame=direct_sources[1],
                endpoint_frame=direct_endpoints[1],
                source_names=("e0", "e1"),
                endpoint_names=("Re0", "Re1"),
            ),
            PlaneSpec(
                title="W moving plane: span(m0,m1)",
                basis_names=("m0", "m1"),
                endpoint_angle=self.model.competitor_plane_angles[0],
                source_note="Both source directions project into this plane.\nW quarter-turns those projected components.",
                family="W",
                source_frame=competitor_sources[0],
                endpoint_frame=competitor_endpoints[0],
                source_names=("e0", "e1"),
                endpoint_names=("We0", "We1"),
            ),
            PlaneSpec(
                title="W fixed plane: span(m2,m3)",
                basis_names=("m2", "m3"),
                endpoint_angle=self.model.competitor_plane_angles[1],
                source_note="The remaining projected components lie here.\nW leaves this entire plane fixed.",
                family="W",
                source_frame=competitor_sources[1],
                endpoint_frame=competitor_endpoints[1],
                source_names=("e0", "e1"),
                endpoint_names=("We0", "We1"),
            ),
        ]
        self.panels = [
            PlanePanel(self.renderers[idx], self.model, specs[idx]) for idx in range(4)
        ]

        self.controls = vtk.vtkRenderer()
        self.controls.SetViewport(0.0, 0.0, 1.0, control_fraction)
        self.controls.SetBackground(*COLORS["control_background"])
        self.window.AddRenderer(self.controls)

        self.headline = text_actor(
            "Direct rotation between two 2-planes U and V in R^4",
            x=0.018,
            y=0.955,
            size=18,
            color=COLORS["text"],
        )
        self.summary_left = text_actor("", x=0.018, y=0.83, size=14)
        self.summary_right = text_actor("", x=0.505, y=0.83, size=14)
        self.global_fact = text_actor("", x=0.018, y=0.33, size=12, color=COLORS["muted"])
        self.motion_help = text_actor("", x=0.018, y=0.13, size=12, color=COLORS["muted"])
        for actor in [self.headline, self.summary_left, self.summary_right, self.global_fact, self.motion_help]:
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
        rep.GetPoint1Coordinate().SetValue(0.58, 0.048)
        rep.GetPoint2Coordinate().SetCoordinateSystemToNormalizedDisplay()
        rep.GetPoint2Coordinate().SetValue(0.95, 0.048)
        rep.SetSliderLength(0.020)
        rep.SetSliderWidth(0.024)
        rep.SetTubeWidth(0.005)
        rep.GetSliderProperty().SetColor(*COLORS["accent"])
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
            "source plane U = span(e0,e1)\n"
            "destination plane V = R(U)\n"
            f"plane contributions: {direct_contrib[0]:.6f} + {direct_contrib[1]:.6f}\n"
            f"trace norm of I-R(t) = {direct_total:.6f}"
        )
        comparison = "W < R at t=1" if competitor_total < direct_total - 1e-12 else "compare at t=1"
        self.summary_right.SetInput(
            "COMPETITOR W\n"
            "same source plane U, same destination subspace V = W(U)\n"
            "but decomposed in the m-basis planes\n"
            f"plane contributions: {competitor_contrib[0]:.6f} + {competitor_contrib[1]:.6f}\n"
            f"trace norm of I-W(t) = {competitor_total:.6f}    {comparison}"
        )
        self.global_fact.SetInput(
            "Orange/cyan = source U directions or their projections.  Green/red = endpoint image of those same vectors.  "
            "White = current interpolation T_t(source).  Principal angles(U,V) = (45 deg, 45 deg) < 60 deg."
        )
        self.motion_help.SetInput(
            f"MOTION t = {self.t:.3f}   {endpoint_note}   "
            "The source and endpoint stay visible, so screenshots are slide-ready at any slider position."
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
