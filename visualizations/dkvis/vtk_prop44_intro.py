"""Explanatory introduction scene for the Proposition 4.4 counterexample.

Run from ``visualizations/`` with::

    uv run --extra vtk python -m dkvis.vtk_prop44_intro

This scene is intended as a slide-building companion to the interactive main
visualization.  It introduces the actual mathematical objects:

* ambient space R^4,
* source 2-plane U = span(e0,e1),
* destination 2-plane V = R(U) = W(U),
* the two exact decompositions used to explain the direct rotation R and the
  admissible competitor W.
"""

from __future__ import annotations

import argparse
from pathlib import Path

import numpy as np
import vtk

from .prop44 import Prop44Model
from .vtk_prop44 import PlanePanel, PlaneSpec
from .vtk_prop44_common import COLORS, text_actor


class Prop44IntroScene:
    """Static introduction slide for the Prop. 4.4 geometric objects."""

    def __init__(self, *, offscreen: bool = False) -> None:
        self.model = Prop44Model()
        self.model.verify()

        self.window = vtk.vtkRenderWindow()
        self.window.SetWindowName("Davis--Kahan Proposition 4.4: introduction")
        self.window.SetSize(1600, 1100)
        if offscreen:
            self.window.SetOffScreenRendering(1)

        header_fraction = 0.28
        panel_top = 1.0 - header_fraction
        split_y = panel_top / 2.0
        panel_viewports = [
            (0.0, split_y, 0.5, panel_top),
            (0.5, split_y, 1.0, panel_top),
            (0.0, 0.0, 0.5, split_y),
            (0.5, 0.0, 1.0, split_y),
        ]
        self.renderers: list[vtk.vtkRenderer] = []
        for viewport in panel_viewports:
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
                title="Source split for the direct rotation",
                basis_names=("e0", "e3"),
                endpoint_angle=self.model.direct_plane_angles[0],
                source_note="Top row: the direct rotation uses two invariant planes.\nHere the active source direction is e0.",
                family="R",
                source_frame=direct_sources[0],
                endpoint_frame=direct_endpoints[0],
                source_names=("e0", "e1"),
                endpoint_names=("Re0", "Re1"),
            ),
            PlaneSpec(
                title="Destination split for the direct rotation",
                basis_names=("e1", "e2"),
                endpoint_angle=self.model.direct_plane_angles[1],
                source_note="The other direct plane contains the active source direction e1.\nTogether the two direct planes produce R(U).",
                family="R",
                source_frame=direct_sources[1],
                endpoint_frame=direct_endpoints[1],
                source_names=("e0", "e1"),
                endpoint_names=("Re0", "Re1"),
            ),
            PlaneSpec(
                title="Moving part of the competitor",
                basis_names=("m0", "m1"),
                endpoint_angle=self.model.competitor_plane_angles[0],
                source_note="Bottom row: in the m-basis decomposition both source directions project here.\nW quarter-turns these projected components.",
                family="W",
                source_frame=competitor_sources[0],
                endpoint_frame=competitor_endpoints[0],
                source_names=("e0", "e1"),
                endpoint_names=("We0", "We1"),
            ),
            PlaneSpec(
                title="Fixed part of the competitor",
                basis_names=("m2", "m3"),
                endpoint_angle=self.model.competitor_plane_angles[1],
                source_note="The remaining projected components land here.\nThis whole plane is fixed by W.",
                family="W",
                source_frame=competitor_sources[1],
                endpoint_frame=competitor_endpoints[1],
                source_names=("e0", "e1"),
                endpoint_names=("We0", "We1"),
            ),
        ]
        self.panels = [
            PlanePanel(self.renderers[idx], self.model, specs[idx], show_current=False)
            for idx in range(4)
        ]
        for panel in self.panels:
            panel.update(1.0)

        self.header = vtk.vtkRenderer()
        self.header.SetViewport(0.0, panel_top, 1.0, 1.0)
        self.header.SetBackground(*COLORS["band_background"])
        self.window.AddRenderer(self.header)

        self.header_text = [
            text_actor(
                "What are the objects in Proposition 4.4?",
                x=0.018,
                y=0.95,
                size=22,
                color=COLORS["text"],
            ),
            text_actor(
                "ambient space: R^4\n"
                "source 2-plane: U = span(e0, e1)\n"
                "destination 2-plane: V = R(U) = W(U)\n"
                "direct rotation: R is the Davis-Kahan direct rotation between U and V",
                x=0.018,
                y=0.77,
                size=16,
                color=COLORS["text"],
            ),
            text_actor(
                "competitor: W is another orthogonal map with W(U)=V\n"
                "principal angles(U,V) = (45 deg, 45 deg) < 60 deg\n"
                "trace comparison: ||I-W||_* < ||I-R||_*\n"
                f"                 {self.model.competitor_trace_displacement:.6f} < {self.model.direct_trace_displacement:.6f}",
                x=0.50,
                y=0.77,
                size=16,
                color=COLORS["text"],
            ),
            text_actor(
                "Color key: orange/cyan = source directions or their projected pieces; "
                "green/red = their endpoint images.\n"
                "Top row = the two exact invariant planes for the direct rotation.  "
                "Bottom row = the moving and fixed planes for the competitor.",
                x=0.018,
                y=0.33,
                size=13,
                color=COLORS["muted"],
            ),
        ]
        for actor in self.header_text:
            self.header.AddViewProp(actor)

        self.interactor = vtk.vtkRenderWindowInteractor()
        self.interactor.SetRenderWindow(self.window)
        self.interactor.SetInteractorStyle(vtk.vtkInteractorStyleImage())

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
    parser.add_argument("--screenshot", type=Path)
    parser.add_argument(
        "--no-interact",
        action="store_true",
        help="render once and exit; useful with --screenshot or in CI",
    )
    return parser


def main() -> None:
    args = _parser().parse_args()
    scene = Prop44IntroScene(offscreen=args.no_interact)
    if args.screenshot is not None:
        scene.screenshot(args.screenshot)
    if args.no_interact:
        scene.render()
    else:
        scene.interact()


if __name__ == "__main__":
    main()
