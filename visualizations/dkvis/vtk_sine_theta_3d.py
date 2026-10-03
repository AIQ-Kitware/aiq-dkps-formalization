"""Interactive 3D VTK demo of the Davis--Kahan sine-theta theorem.

Run from ``visualizations/``::

    uv run --extra vtk python -m dkvis.vtk_sine_theta_3d                # trial mode
    uv run --extra vtk python -m dkvis.vtk_sine_theta_3d --mode perturb # A -> A + eps H

The scene lives in ``R^3``.  ``A`` is drawn as the ellipsoid ``{A x : |x| = c}``;
the exact invariant subspace ``U`` (blue disk) is the plane of its two wanted
axes ``f1, f2``, and ``f3`` spans the unwanted direction ``U-perp``.  The trial
plane ``V = range E0`` (amber disk) meets ``U`` in a line, so the principal angles
are ``(theta, 0)``; the pink segment is the one nonzero sine.  Green arrows are
the residuals ``R c`` of the two principal trial vectors, drawn from their tips.

* **trial mode** -- tilt ``V`` by ``theta`` about a hinge line at azimuth
  ``phi``; ``A0 = E0^T A E0`` (Rayleigh--Ritz), so the residuals leave ``V`` at
  right angles.  Moving ``lambda3`` shows how the gap controls the bound.
* **perturb mode** -- keep ``V`` = the old eigenspace and perturb
  ``A -> A + eps H``; now the ellipsoid and the exact plane move, and
  ``R = eps H E0``.

The strip under the 3D view is the spectrum: filled blue dots are the wanted
eigenvalues, the hollow blue dot is ``lambda3``, amber triangles are
``spec(A0)``, and the violet bar is the gap ``delta = min |mu_i - lambda3|``.

Mouse: drag to rotate, scroll to zoom, shift-drag to pan.
Keys:  ``m`` mode, ``space`` play/pause, ``e`` ellipsoid, ``x`` residuals,
``r`` reset view, ``s`` screenshot, ``h`` help, ``q`` quit.

Headless export (also used to build the slides)::

    uv run --extra vtk python -m dkvis.vtk_sine_theta_3d --screenshot out.png
    uv run --extra vtk python -m dkvis.vtk_sine_theta_3d --movie sweep-theta --out out.mp4
    uv run --extra vtk python -m dkvis.vtk_sine_theta_3d --slide-assets DIR
"""

from __future__ import annotations

import argparse
import functools
import math
import shutil
import subprocess
import time
from dataclasses import dataclass, replace
from pathlib import Path

import numpy as np
import vtk
from vtk.util.numpy_support import vtk_to_numpy

from dkvis import sine_theta_3d as m3
from dkvis.palette import PALETTE, rgb

C = {k: rgb(v) for k, v in PALETTE.items()}

PLANE_RADIUS = 1.45
ELLIPSOID_SCALE = 0.72
CAMERA_POSITION = (4.6, -5.4, 2.9)
SPECTRUM_RANGE = (0.0, 4.2)


# ----------------------------------------------------------------------------
# Fonts
# ----------------------------------------------------------------------------


@functools.cache
def font_file(family: str) -> str | None:
    """Path of an installed font (``fc-match``), or ``None`` to use VTK's own."""
    if shutil.which("fc-match") is None:
        return None
    out = subprocess.run(["fc-match", "-f", "%{file}", family], capture_output=True, text=True)
    path = out.stdout.strip()
    return path if path and Path(path).exists() else None


TITLE_FONT = "Latin Modern Sans"
MATH_FONT = "DejaVu Sans"


def style_text(prop: vtk.vtkTextProperty, *, size: int, color, family: str = MATH_FONT, bold: bool = False) -> None:
    path = font_file(family)
    if path:
        prop.SetFontFamily(vtk.VTK_FONT_FILE)
        prop.SetFontFile(path)
    else:
        prop.SetFontFamilyToArial()
    prop.SetFontSize(int(size))
    prop.SetColor(*color)
    prop.SetBold(bold)
    prop.SetShadow(False)


# ----------------------------------------------------------------------------
# Scene state
# ----------------------------------------------------------------------------


@dataclass(frozen=True)
class State:
    mode: str = "trial"  # "trial" | "perturb"
    theta_deg: float = 35.0
    phi_deg: float = -25.0
    lambda3: float = m3.DEFAULT_EIGENVALUES[2]
    eps: float = 0.5
    show_ellipsoid: bool = True
    show_trial: bool = True
    show_sine: bool = True
    show_residual: bool = True
    show_hud: bool = True

    @property
    def eigenvalues(self) -> tuple[float, float, float]:
        l1, l2, _ = m3.DEFAULT_EIGENVALUES
        return (l1, l2, self.lambda3)

    def configuration(self) -> m3.Configuration:
        if self.mode == "perturb":
            return m3.perturbed(self.eps, self.eigenvalues)
        return m3.tilted_trial(math.radians(self.theta_deg), math.radians(self.phi_deg), self.eigenvalues)


# ----------------------------------------------------------------------------
# Updatable 3D primitives
# ----------------------------------------------------------------------------


def _actor(source_port, color, opacity: float = 1.0) -> vtk.vtkActor:
    mapper = vtk.vtkPolyDataMapper()
    mapper.SetInputConnection(source_port)
    actor = vtk.vtkActor()
    actor.SetMapper(mapper)
    prop = actor.GetProperty()
    prop.SetColor(*color)
    prop.SetOpacity(opacity)
    return actor


class Disk:
    """A translucent filled disk with an opaque rim."""

    def __init__(self, renderer, color, radius: float = PLANE_RADIUS, opacity: float = 0.26):
        self.fill = vtk.vtkRegularPolygonSource()
        self.rim = vtk.vtkRegularPolygonSource()
        for src in (self.fill, self.rim):
            src.SetNumberOfSides(120)
            src.SetRadius(radius)
        self.rim.GeneratePolygonOff()
        self.fill_actor = _actor(self.fill.GetOutputPort(), color, opacity)
        self.fill_actor.GetProperty().SetAmbient(0.35)
        self.fill_actor.GetProperty().BackfaceCullingOff()
        self.rim_actor = _actor(self.rim.GetOutputPort(), color, 0.95)
        self.rim_actor.GetProperty().SetLineWidth(3)
        for a in (self.fill_actor, self.rim_actor):
            renderer.AddActor(a)

    def update(self, normal) -> None:
        for src in (self.fill, self.rim):
            src.SetNormal(*map(float, normal))
            src.Modified()

    def visible(self, on: bool) -> None:
        self.fill_actor.SetVisibility(on)
        self.rim_actor.SetVisibility(on)


class Segment:
    """A tube between two points."""

    def __init__(self, renderer, color, radius: float = 0.012, opacity: float = 1.0):
        self.line = vtk.vtkLineSource()
        self.tube = vtk.vtkTubeFilter()
        self.tube.SetInputConnection(self.line.GetOutputPort())
        self.tube.SetRadius(radius)
        self.tube.SetNumberOfSides(18)
        self.tube.CappingOn()
        self.actor = _actor(self.tube.GetOutputPort(), color, opacity)
        self.actor.GetProperty().SetSpecular(0.3)
        renderer.AddActor(self.actor)

    def update(self, start, end) -> None:
        self.line.SetPoint1(*map(float, start))
        self.line.SetPoint2(*map(float, end))
        self.line.Modified()

    def visible(self, on: bool) -> None:
        self.actor.SetVisibility(on)


class Arrow:
    """A tube shaft with a cone head; hidden when too short to draw."""

    def __init__(self, renderer, color, radius: float = 0.022, head: float = 0.12):
        self.shaft = Segment(renderer, color, radius)
        self.cone = vtk.vtkConeSource()
        self.cone.SetResolution(28)
        self.cone.SetRadius(head * 0.42)
        self.head = head
        self.cone_actor = _actor(self.cone.GetOutputPort(), color)
        self.cone_actor.GetProperty().SetSpecular(0.3)
        renderer.AddActor(self.cone_actor)
        self._on = True

    def update(self, start, end) -> None:
        start, end = np.asarray(start, float), np.asarray(end, float)
        d = end - start
        length = float(np.linalg.norm(d))
        drawable = length > 1e-3
        self.shaft.actor.SetVisibility(self._on and drawable)
        self.cone_actor.SetVisibility(self._on and drawable)
        if not drawable:
            return
        u = d / length
        head = min(self.head, 0.45 * length)
        base = end - head * u
        self.shaft.update(start, base)
        self.cone.SetHeight(head)
        self.cone.SetRadius(head * 0.42)
        self.cone.SetCenter(*(base + 0.5 * head * u))
        self.cone.SetDirection(*u)
        self.cone.Modified()

    def visible(self, on: bool) -> None:
        self._on = on
        self.shaft.visible(on)
        self.cone_actor.SetVisibility(on)


class Polyline:
    def __init__(self, renderer, color, n: int, width: float = 3.0):
        self.points = vtk.vtkPoints()
        self.points.SetNumberOfPoints(n)
        lines = vtk.vtkCellArray()
        lines.InsertNextCell(n)
        for i in range(n):
            lines.InsertCellPoint(i)
            self.points.SetPoint(i, 0, 0, 0)
        self.data = vtk.vtkPolyData()
        self.data.SetPoints(self.points)
        self.data.SetLines(lines)
        mapper = vtk.vtkPolyDataMapper()
        mapper.SetInputData(self.data)
        self.actor = vtk.vtkActor()
        self.actor.SetMapper(mapper)
        self.actor.GetProperty().SetColor(*color)
        self.actor.GetProperty().SetLineWidth(width)
        renderer.AddActor(self.actor)

    def update(self, pts) -> None:
        for i, p in enumerate(pts):
            self.points.SetPoint(i, *map(float, p))
        self.points.Modified()
        self.data.Modified()


class Label3D:
    def __init__(self, renderer, text: str, color, size: int):
        self.actor = vtk.vtkBillboardTextActor3D()
        self.actor.SetInput(text)
        style_text(self.actor.GetTextProperty(), size=size, color=color)
        self.actor.GetTextProperty().SetJustificationToCentered()
        self.actor.GetTextProperty().SetVerticalJustificationToCentered()
        renderer.AddActor(self.actor)

    def update(self, pos, text: str | None = None) -> None:
        self.actor.SetPosition(*map(float, pos))
        if text is not None:
            self.actor.SetInput(text)

    def visible(self, on: bool) -> None:
        self.actor.SetVisibility(on)


class Ellipsoid:
    def __init__(self, renderer, color):
        self.sphere = vtk.vtkSphereSource()
        self.sphere.SetThetaResolution(72)
        self.sphere.SetPhiResolution(48)
        self.transform = vtk.vtkTransform()
        self.filter = vtk.vtkTransformFilter()
        self.filter.SetInputConnection(self.sphere.GetOutputPort())
        self.filter.SetTransform(self.transform)
        normals = vtk.vtkPolyDataNormals()
        normals.SetInputConnection(self.filter.GetOutputPort())
        self.actor = _actor(normals.GetOutputPort(), color, 0.12)
        prop = self.actor.GetProperty()
        prop.SetSpecular(0.6)
        prop.SetSpecularPower(40)
        renderer.AddActor(self.actor)
        # The three principal cross-sections make the shape legible.
        self.sections = [Polyline(renderer, color, 121, width=1.5) for _ in range(3)]
        for sec in self.sections:
            sec.actor.GetProperty().SetOpacity(0.55)

    def update(self, A: np.ndarray) -> None:
        M = np.eye(4)
        M[:3, :3] = ELLIPSOID_SCALE * A
        mat = vtk.vtkMatrix4x4()
        for i in range(4):
            for j in range(4):
                mat.SetElement(i, j, float(M[i, j]))
        self.transform.SetMatrix(mat)
        self.filter.Modified()
        lam, vecs = np.linalg.eigh(A)
        t = np.linspace(0.0, 2 * np.pi, 121)
        for sec, (i, j) in zip(self.sections, [(0, 1), (1, 2), (0, 2)]):
            pts = ELLIPSOID_SCALE * (
                np.outer(np.cos(t), lam[i] * vecs[:, i]) + np.outer(np.sin(t), lam[j] * vecs[:, j])
            )
            sec.update(pts)

    def visible(self, on: bool) -> None:
        self.actor.SetVisibility(on)
        for sec in self.sections:
            sec.actor.SetVisibility(on)


# ----------------------------------------------------------------------------
# 2D overlay primitives
# ----------------------------------------------------------------------------


class Text2D:
    def __init__(self, renderer, x: float, y: float, *, size: int, color, family: str = MATH_FONT, valign: str = "top"):
        self.actor = vtk.vtkTextActor()
        coord = self.actor.GetPositionCoordinate()
        coord.SetCoordinateSystemToNormalizedViewport()
        coord.SetValue(x, y)
        prop = self.actor.GetTextProperty()
        style_text(prop, size=size, color=color, family=family)
        {"top": prop.SetVerticalJustificationToTop, "center": prop.SetVerticalJustificationToCentered,
         "bottom": prop.SetVerticalJustificationToBottom}[valign]()
        prop.SetLineSpacing(1.15)
        renderer.AddViewProp(self.actor)

    def set(self, text: str) -> None:
        self.actor.SetInput(text)

    def visible(self, on: bool) -> None:
        self.actor.SetVisibility(on)


class Rect2D:
    """An axis-aligned rectangle in normalized-viewport coordinates."""

    def __init__(self, renderer, color, opacity: float = 1.0):
        self.points = vtk.vtkPoints()
        self.points.SetNumberOfPoints(4)
        poly = vtk.vtkCellArray()
        poly.InsertNextCell(4)
        for i in range(4):
            poly.InsertCellPoint(i)
        self.data = vtk.vtkPolyData()
        self.data.SetPoints(self.points)
        self.data.SetPolys(poly)
        coord = vtk.vtkCoordinate()
        coord.SetCoordinateSystemToNormalizedViewport()
        mapper = vtk.vtkPolyDataMapper2D()
        mapper.SetInputData(self.data)
        mapper.SetTransformCoordinate(coord)
        self.actor = vtk.vtkActor2D()
        self.actor.SetMapper(mapper)
        self.actor.GetProperty().SetColor(*color)
        self.actor.GetProperty().SetOpacity(opacity)
        renderer.AddViewProp(self.actor)

    def update(self, x0: float, y0: float, x1: float, y1: float) -> None:
        for i, (x, y) in enumerate([(x0, y0), (x1, y0), (x1, y1), (x0, y1)]):
            self.points.SetPoint(i, x, y, 0.0)
        self.points.Modified()
        self.data.Modified()

    def visible(self, on: bool) -> None:
        self.actor.SetVisibility(on)


# ----------------------------------------------------------------------------
# The scene
# ----------------------------------------------------------------------------

VIEW_3D = (0.0, 0.17, 0.63, 0.86)
VIEW_SPECTRUM = (0.025, 0.02, 0.63, 0.165)
PANEL_X = 0.655


class SineTheta3D:
    def __init__(
        self,
        state: State = State(),
        *,
        width: int = 1600,
        height: int = 900,
        offscreen: bool = False,
        layout: str = "app",  # "app" (HUD) or "still" (3D view only)
        interactive: bool = True,
    ) -> None:
        self.state = state
        self.layout = layout
        self.interactive = interactive
        self.W, self.H = width, height
        self.playing = False
        self._t0 = time.monotonic()

        self.window = vtk.vtkRenderWindow()
        self.window.SetSize(width, height)
        self.window.SetWindowName("Davis-Kahan sin Θ in 3D")
        self.window.SetAlphaBitPlanes(1)
        self.window.SetMultiSamples(0)
        if offscreen:
            self.window.SetOffScreenRendering(1)

        self.overlay = vtk.vtkRenderer()
        self.overlay.SetBackground(*C["BG"])
        self.view = vtk.vtkRenderer()
        self.view.SetBackground(*C["BG"])
        self.view.SetUseDepthPeeling(1)
        self.view.SetMaximumNumberOfPeels(12)
        self.view.SetOcclusionRatio(0.0)
        self.view.UseFXAAOn()
        self.spectrum = vtk.vtkRenderer()
        self.spectrum.SetBackground(*C["PANEL"])
        # Labels live in a second layer that shares the 3D camera, so the
        # translucent disks never wash them out.
        self.labels = vtk.vtkRenderer()
        self.labels.SetLayer(1)
        self.labels.InteractiveOff()
        self.labels.SetActiveCamera(self.view.GetActiveCamera())
        self.window.SetNumberOfLayers(2)

        if layout == "still":
            self.view.SetViewport(0, 0, 1, 1)
            self.labels.SetViewport(0, 0, 1, 1)
            self.window.AddRenderer(self.view)
        else:
            self.overlay.SetViewport(0, 0, 1, 1)
            self.view.SetViewport(*VIEW_3D)
            self.labels.SetViewport(*VIEW_3D)
            self.spectrum.SetViewport(*VIEW_SPECTRUM)
            for r in (self.overlay, self.view, self.spectrum):
                self.window.AddRenderer(r)
        self.window.AddRenderer(self.labels)

        self._build_3d()
        if layout != "still":
            self._build_spectrum()
            self._build_hud()
        self.reset_camera()

        self.interactor = None
        if self.interactive:
            self._build_interaction()
        self.update()

    # -- construction ----------------------------------------------------------
    def px(self, frac: float) -> int:
        return max(8, int(round(frac * self.H)))

    def _build_3d(self) -> None:
        r = self.view
        light = vtk.vtkLight()
        light.SetLightTypeToCameraLight()
        light.SetPosition(1, 1, 1)
        light.SetIntensity(0.55)
        r.AddLight(light)
        r.AutomaticLightCreationOn()

        # Translucent context (planes, ellipsoid, axes) in the base layer ...
        # The operator itself is neutral; only its wanted and unwanted parts carry role colors.
        self.ellipsoid = Ellipsoid(r, C["CURRENT"])
        self.axis_lines = [Segment(r, C["WANTED"], radius=0.006, opacity=0.55) for _ in range(3)]
        self.U = Disk(r, C["WANTED"])
        self.V = Disk(r, C["TRIAL"])
        self.hinge = Segment(r, C["FG"], radius=0.008, opacity=0.8)
        # ... and the vectors the argument is about in the top layer, so the
        # disks they lie in never tint or hide them.
        f = self.labels
        self.f3 = Arrow(f, C["UNWANTED"], radius=0.02)
        self.u1 = Arrow(f, C["TRIAL"])
        self.u2 = Arrow(f, C["TRIAL"])
        self.proj = Segment(f, C["MUTED"], radius=0.012)
        self.drop = Segment(f, C["SINE"], radius=0.026)
        self.arc = Polyline(f, C["FG"], 40, width=3)
        self.r1 = Arrow(f, C["RESID"], radius=0.02, head=0.1)
        self.r2 = Arrow(f, C["RESID"], radius=0.02, head=0.1)

        lr = self.labels
        s = self.px(0.03)
        self.lbl_U = Label3D(lr, "U", C["WANTED"], s)
        self.lbl_V = Label3D(lr, "V", C["TRIAL"], s)
        self.lbl_f3 = Label3D(lr, "f₃", C["UNWANTED"], s)
        self.lbl_hinge = Label3D(lr, "U ∩ V", C["FG"], self.px(0.022))
        self.lbl_sin = Label3D(lr, "sin θ", C["SINE"], self.px(0.026))
        self.lbl_theta = Label3D(lr, "θ", C["FG"], self.px(0.024))
        self.lbl_r = Label3D(lr, "R", C["RESID"], self.px(0.026))

    def _build_spectrum(self) -> None:
        r = self.spectrum
        lo, hi = SPECTRUM_RANGE
        self.spec_axis = Segment(r, C["MUTED"], radius=0.006)
        self.spec_axis.update((lo, 0, 0), (hi, 0, 0))
        self.spec_ticks = []
        for v in range(int(lo), int(hi) + 1):
            seg = Segment(r, C["MUTED"], radius=0.006)
            seg.update((v, -0.05, 0), (v, 0.05, 0))
            lbl = Label3D(r, f"{v}", C["MUTED"], self.px(0.017))
            lbl.update((v, -0.15, 0))
            self.spec_ticks.append((seg, lbl))
        self.spec_window = vtk.vtkPlaneSource()
        self.spec_window_actor = _actor(self.spec_window.GetOutputPort(), C["GAP"], 0.22)
        r.AddActor(self.spec_window_actor)
        self.spec_gap = Segment(r, C["GAP"], radius=0.018)
        self.spec_gap_lbl = Label3D(r, "δ", C["GAP"], self.px(0.02))

        def disc(color, filled=True):
            src = vtk.vtkRegularPolygonSource()
            src.SetNumberOfSides(40)
            src.SetRadius(0.055)
            if not filled:
                src.GeneratePolygonOff()
            a = _actor(src.GetOutputPort(), color)
            a.GetProperty().SetLineWidth(3)
            a.GetProperty().LightingOff()
            r.AddActor(a)
            return src

        self.spec_wanted = [disc(C["WANTED"]) for _ in range(2)]
        self.spec_unwanted = disc(C["UNWANTED"], filled=False)
        self.spec_unwanted_lbl = Label3D(r, "λ₃", C["UNWANTED"], self.px(0.019))

        def tri(color):
            src = vtk.vtkRegularPolygonSource()
            src.SetNumberOfSides(3)
            src.SetRadius(0.06)
            a = _actor(src.GetOutputPort(), color)
            a.GetProperty().LightingOff()
            r.AddActor(a)
            return src

        self.spec_ritz = [tri(C["TRIAL"]) for _ in range(2)]
        self.spec_ritz_lbl = Label3D(r, "spec(A₀)", C["TRIAL"], self.px(0.017))

        cam = r.GetActiveCamera()
        cam.ParallelProjectionOn()
        mid = 0.5 * (lo + hi)
        cam.SetFocalPoint(mid, 0.02, 0)
        cam.SetPosition(mid, 0.02, 10)
        cam.SetViewUp(0, 1, 0)
        vx0, vy0, vx1, vy1 = VIEW_SPECTRUM
        aspect = ((vx1 - vx0) * self.W) / ((vy1 - vy0) * self.H)
        cam.SetParallelScale((hi - lo + 0.5) / (2 * aspect))

    def _build_hud(self) -> None:
        o = self.overlay
        self.title = Text2D(o, 0.03, 0.965, size=self.px(0.046), color=C["FG"], family=TITLE_FONT)
        self.subtitle = Text2D(o, 0.03, 0.9, size=self.px(0.023), color=C["MUTED"])
        rows = [
            ("mode", C["MUTED"]),
            ("angle", C["SINE"]),
            ("angles", C["MUTED"]),
            ("ritz", C["TRIAL"]),
            ("lambda", C["FG"]),
            ("delta", C["GAP"]),
            ("resid", C["RESID"]),
        ]
        y, dy = 0.85, 0.04
        self.rows = {}
        for key, color in rows:
            self.rows[key] = Text2D(o, PANEL_X, y, size=self.px(0.022), color=color)
            y -= dy
        # The theorem as two bars that can be compared at a glance.
        y -= 0.012
        self.thm_title = Text2D(o, PANEL_X, y, size=self.px(0.025), color=C["FG"])
        self.thm_title.set("theorem:  δ ‖sin Θ₀‖  ≤  ‖R‖")
        self.meter_y = (y - 0.063, y - 0.108)  # bar centre lines
        self.meter_x = (PANEL_X + 0.1, PANEL_X + 0.27)
        bar = 0.011
        self.meter_track = [Rect2D(o, C["FAINT"]) for _ in range(2)]
        self.meter_fill = [Rect2D(o, C["SINE"]), Rect2D(o, C["RESID"])]
        self.meter_lbl, self.meter_val = [], []
        for k, (name, color) in enumerate([("δ ‖sin Θ₀‖", C["SINE"]), ("‖R‖₂", C["RESID"])]):
            yc = self.meter_y[k]
            self.meter_track[k].update(self.meter_x[0], yc - bar, self.meter_x[1], yc + bar)
            lbl = Text2D(o, PANEL_X, yc, size=self.px(0.022), color=color, valign="center")
            lbl.set(name)
            self.meter_lbl.append(lbl)
            self.meter_val.append(Text2D(o, self.meter_x[1] + 0.012, yc, size=self.px(0.022), color=color, valign="center"))
        self._bar = bar
        self.legend = Text2D(o, PANEL_X, self.meter_y[1] - 0.035, size=self.px(0.019), color=C["MUTED"])
        self.help = Text2D(o, PANEL_X, self.meter_y[1] - 0.105, size=self.px(0.018), color=C["MUTED"])
        self.help.set(
            "drag rotate · scroll zoom · shift-drag pan\n"
            "m mode · space play · e ellipsoid · x residuals\n"
            "r reset view · s screenshot · h help · q quit"
        )
        self.help.visible(self.interactive)

    # -- interaction -----------------------------------------------------------
    def _slider(self, title: str, lo: float, hi: float, value: float, y: float, fmt: str, cb):
        """A slider whose title shows its value, e.g. ``tilt θ = 35.0°``.

        ``title`` is a format string applied to the current value.
        """
        rep = vtk.vtkSliderRepresentation2D()
        rep.SetMinimumValue(lo)
        rep.SetMaximumValue(hi)
        rep.SetValue(value)
        rep.SetTitleText(title.format(value))
        rep.ShowSliderLabelOff()
        rep.GetPoint1Coordinate().SetCoordinateSystemToNormalizedDisplay()
        rep.GetPoint1Coordinate().SetValue(PANEL_X + 0.03, y)
        rep.GetPoint2Coordinate().SetCoordinateSystemToNormalizedDisplay()
        rep.GetPoint2Coordinate().SetValue(0.965, y)
        rep.SetSliderLength(0.018)
        rep.SetSliderWidth(0.028)
        rep.SetTubeWidth(0.006)
        rep.SetEndCapLength(0.006)
        rep.SetTitleHeight(0.022)
        rep.SetLabelHeight(0.02)
        style_text(rep.GetTitleProperty(), size=self.px(0.022), color=C["FG"])
        style_text(rep.GetLabelProperty(), size=self.px(0.02), color=C["MUTED"])
        rep.GetSliderProperty().SetColor(*C["FG"])
        rep.GetTubeProperty().SetColor(*C["FAINT"])
        rep.GetCapProperty().SetColor(*C["MUTED"])
        rep.GetSelectedProperty().SetColor(*C["TRIAL"])
        widget = vtk.vtkSliderWidget()
        widget.SetInteractor(self.interactor)
        widget.SetRepresentation(rep)
        widget.SetCurrentRenderer(self.overlay)
        widget.SetAnimationModeToJump()
        widget.AddObserver(vtk.vtkCommand.InteractionEvent, lambda w, _e: cb(w.GetRepresentation().GetValue()))
        widget.EnabledOn()
        self._slider_titles[widget] = title
        return widget

    def _build_interaction(self) -> None:
        self.interactor = vtk.vtkRenderWindowInteractor()
        self.interactor.SetRenderWindow(self.window)
        style = vtk.vtkInteractorStyleTrackballCamera()
        style.SetDefaultRenderer(self.view)
        # Replacing the style's CharEvent handler disables VTK's built-in
        # single-key bindings (e.g. 'e' exits, 's' switches to surfaces).
        style.AddObserver(vtk.vtkCommand.CharEvent, lambda *_: None)
        self.interactor.SetInteractorStyle(style)
        self.interactor.AddObserver(vtk.vtkCommand.KeyPressEvent, self._on_key)
        self.interactor.AddObserver(vtk.vtkCommand.TimerEvent, self._on_timer)

        s = self.state
        self._slider_titles = {}
        self.sliders = {
            "theta": self._slider("tilt  θ = {:.1f}°", 0.0, 89.0, s.theta_deg, 0.255, "", lambda v: self.set(theta_deg=v)),
            "phi": self._slider("hinge azimuth  φ = {:.0f}°", -90.0, 90.0, s.phi_deg, 0.17, "", lambda v: self.set(phi_deg=v)),
            "eps": self._slider("perturbation  ε = ‖H‖₂ = {:.2f}", 0.0, 1.2, s.eps, 0.255, "", lambda v: self.set(eps=v)),
            "lambda3": self._slider("unwanted eigenvalue  λ₃ = {:.2f}", 0.2, 4.0, s.lambda3, 0.085, "", lambda v: self.set(lambda3=v)),
        }
        self._sync_sliders()

    def _sync_sliders(self) -> None:
        if not self.interactive:
            return
        trial = self.state.mode == "trial"
        self.sliders["theta"].SetEnabled(trial)
        self.sliders["phi"].SetEnabled(trial)
        self.sliders["eps"].SetEnabled(not trial)
        values = {"theta": self.state.theta_deg, "phi": self.state.phi_deg, "eps": self.state.eps, "lambda3": self.state.lambda3}
        for key, widget in self.sliders.items():
            rep = widget.GetRepresentation()
            rep.SetValue(values[key])
            rep.SetTitleText(self._slider_titles[widget].format(values[key]))

    def _on_key(self, obj, _event) -> None:
        key = obj.GetKeySym()
        s = self.state
        if key == "m":
            self.state = replace(s, mode="perturb" if s.mode == "trial" else "trial")
            self._sync_sliders()
        elif key == "space":
            self.playing = not self.playing
            self._t0 = time.monotonic()
            if self.playing:
                self._timer = self.interactor.CreateRepeatingTimer(33)
            else:
                self.interactor.DestroyTimer(self._timer)
        elif key == "e":
            self.state = replace(s, show_ellipsoid=not s.show_ellipsoid)
        elif key == "x":
            self.state = replace(s, show_residual=not s.show_residual)
        elif key == "r":
            self.reset_camera()
        elif key == "h":
            self.help.visible(not self.help.actor.GetVisibility())
        elif key == "s":
            path = Path("renders") / f"sine-theta-3d-{time.strftime('%Y%m%d-%H%M%S')}.png"
            self.screenshot(path)
            print(f"saved {path}")
        elif key in ("q", "Escape"):
            self.interactor.TerminateApp()
            return
        else:
            return
        self.update()
        self.window.Render()

    def _on_timer(self, _obj, _event) -> None:
        if not self.playing:
            return
        t = time.monotonic() - self._t0
        wave = 0.5 - 0.5 * math.cos(2 * math.pi * t / 8.0)  # 0 -> 1 -> 0 every 8 s
        if self.state.mode == "trial":
            self.state = replace(self.state, theta_deg=3.0 + 80.0 * wave)
        else:
            self.state = replace(self.state, eps=1.1 * wave)
        self._sync_sliders()
        self.update()
        self.window.Render()

    # -- updates ---------------------------------------------------------------
    def set(self, **changes) -> None:
        self.state = replace(self.state, **changes)
        self._sync_sliders()
        self.update()
        self.window.Render()

    def reset_camera(self) -> None:
        cam = self.view.GetActiveCamera()
        cam.SetFocalPoint(0.0, 0.0, 0.15)
        cam.SetPosition(*CAMERA_POSITION)
        cam.SetViewUp(0.0, 0.0, 1.0)
        cam.SetViewAngle(28.0)
        self.view.ResetCameraClippingRange()

    def update(self) -> None:
        s = self.state
        cfg = s.configuration()
        cfg.verify()
        self.cfg = cfg
        O = np.zeros(3)

        # Exact data.
        self.ellipsoid.update(cfg.A)
        self.ellipsoid.visible(s.show_ellipsoid)
        order = [i for i in range(3) if i != cfg.unwanted] + [cfg.unwanted]
        for seg, idx in zip(self.axis_lines, order):
            f = cfg.eigenvectors[:, idx]
            reach = 1.9 if idx != cfg.unwanted else 0.0
            seg.update(-reach * f, reach * f)
            seg.visible(s.show_ellipsoid and idx != cfg.unwanted)
        nU = cfg.normal_U if cfg.normal_U[2] >= 0 else -cfg.normal_U
        self.U.update(nU)
        self.f3.update(O, 1.75 * nU)
        self.lbl_f3.update(1.95 * nU)
        # Trial data.
        hinge, tilted = cfg.principal_vectors
        # Put the U label on U's rim, across the hinge from the sine segment.
        w = _unit(np.cross(nU, hinge))
        if w @ tilted > 0:
            w = -w
        self.lbl_U.update(1.2 * w + 0.35 * hinge)
        self.V.update(cfg.normal_V)
        self.V.visible(s.show_trial)
        self.hinge.update(-1.6 * hinge, 1.6 * hinge)
        self.lbl_hinge.update(1.78 * hinge)
        self.u1.update(O, hinge)
        self.u2.update(O, tilted)
        self.lbl_V.update(1.3 * _unit(hinge - 0.6 * tilted))
        for a in (self.hinge, self.u1, self.u2, self.lbl_V, self.lbl_hinge):
            a.visible(s.show_trial)

        # The nonzero sine: drop the tilted trial vector onto U.
        p = cfg.F0 @ (cfg.F0.T @ tilted)
        self.proj.update(O, p)
        self.drop.update(p, tilted)
        self.lbl_sin.update(0.5 * (p + tilted) + 0.16 * _unit(p))
        pn = _unit(p) if np.linalg.norm(p) > 1e-9 else tilted
        angles = np.linspace(0.0, 1.0, 40)
        arc = [0.42 * _unit((1 - t) * pn + t * tilted) for t in angles]
        self.arc.update(arc)
        self.lbl_theta.update(0.58 * _unit(pn + tilted))
        on = s.show_trial and s.show_sine and cfg.sin_theta > 1e-3
        for a in (self.proj, self.drop, self.lbl_sin, self.lbl_theta):
            a.visible(on)
        self.arc.actor.SetVisibility(on)

        # Residuals of the principal trial vectors, drawn from their tips.
        coords_h = cfg.E0.T @ hinge
        coords_t = cfg.E0.T @ tilted
        r_h = cfg.R @ coords_h
        r_t = cfg.R @ coords_t
        self.r1.update(hinge, hinge + r_h)
        self.r2.update(tilted, tilted + r_t)
        big = r_t if np.linalg.norm(r_t) >= np.linalg.norm(r_h) else r_h
        base = tilted if big is r_t else hinge
        self.lbl_r.update(base + big + 0.12 * _unit(big) if np.linalg.norm(big) > 1e-6 else base)
        for a in (self.r1, self.r2, self.lbl_r):
            a.visible(s.show_trial and s.show_residual)
        self.view.ResetCameraClippingRange()

        if self.layout != "still":
            self._update_spectrum(cfg)
            self._update_hud(cfg)

    def _update_spectrum(self, cfg: m3.Configuration) -> None:
        lw = sorted(cfg.lambda_wanted)
        for src, v in zip(self.spec_wanted, lw):
            src.SetCenter(float(v), 0.0, 0.0)
            src.Modified()
        l3 = cfg.lambda_unwanted
        self.spec_unwanted.SetCenter(l3, 0.0, 0.0)
        self.spec_unwanted.Modified()
        self.spec_unwanted_lbl.update((l3, -0.17, 0.0))
        mu = cfg.ritz_values
        for src, v in zip(self.spec_ritz, mu):
            src.SetCenter(float(v), 0.13, 0.0)
            src.Modified()
        self.spec_ritz_lbl.update((float(np.min(mu)) - 0.42, 0.13, 0.0))
        near = cfg.nearest_ritz
        self.spec_gap.update((near, 0.13, 0.0), (l3, 0.13, 0.0))
        self.spec_gap_lbl.update((0.5 * (near + l3), 0.25, 0.0))
        # The delta-window around lambda3 (exchanged form: Lambda1 is the point
        # lambda3, and spec(A0) must avoid (lambda3 - delta, lambda3 + delta)).
        d = cfg.delta
        self.spec_window.SetOrigin(l3 - d, -0.08, -0.01)
        self.spec_window.SetPoint1(l3 + d, -0.08, -0.01)
        self.spec_window.SetPoint2(l3 - d, 0.08, -0.01)
        self.spec_window.Modified()

    def _update_hud(self, cfg: m3.Configuration) -> None:
        s = self.state
        if s.mode == "trial":
            self.title.set("sin Θ in three dimensions: tilting the trial plane")
            self.subtitle.set("A fixed;  trial plane V tilted about a line in U;  A₀ = E₀ᵀAE₀ (Rayleigh–Ritz)")
            self.rows["mode"].set(f"tilt θ = {s.theta_deg:.1f}°,  hinge azimuth φ = {s.phi_deg:.0f}°")
        else:
            self.title.set("sin Θ in three dimensions: perturbing the matrix")
            self.subtitle.set("A → A + εH;  trial V = old eigenspace span(e₁, e₂);  A₀ = diag(λ₁, λ₂);  R = εHE₀")
            self.rows["mode"].set(f"perturbation ε = ‖H‖₂ = {s.eps:.2f}")
        th = np.degrees(cfg.principal_angles)
        self.rows["angle"].set(f"‖sin Θ₀‖ = ‖F₁ᵀE₀‖ = {cfg.sin_theta:.3f}")
        self.rows["angles"].set(f"principal angles ({th[0]:.1f}°, {th[1]:.1f}°)")
        mu = cfg.ritz_values
        self.rows["ritz"].set(f"spec(A₀) = {{{mu[0]:.3f}, {mu[1]:.3f}}}")
        lw = sorted(cfg.lambda_wanted)
        self.rows["lambda"].set(f"wanted λ₁, λ₂ = {lw[0]:.3f}, {lw[1]:.3f};  unwanted λ₃ = {cfg.lambda_unwanted:.3f}")
        self.rows["delta"].set(f"gap δ = min ∣μᵢ − λ₃∣ = {cfg.delta:.3f}")
        self.rows["resid"].set(f"‖R‖₂ = {cfg.residual_norm_2:.3f},   ‖R‖_F = {cfg.residual_norm_F:.3f}")
        lhs, rhs = cfg.theorem_lhs, cfg.residual_norm_2
        scale = max(rhs, lhs, 1e-9)
        full = self.meter_x[1] - self.meter_x[0]
        for k, value in enumerate((lhs, rhs)):
            yc = self.meter_y[k]
            self.meter_fill[k].update(self.meter_x[0], yc - self._bar, self.meter_x[0] + full * value / scale, yc + self._bar)
            self.meter_val[k].set(f"{value:.3f}")
        self.legend.set(
            "blue: exact U = span(f₁, f₂), with f₃ spanning U⊥\n"
            "amber: trial plane V;  pink: sin θ;  green: residuals"
        )

    # -- output ----------------------------------------------------------------
    def render(self) -> None:
        self.window.Render()

    def interact(self) -> None:
        self.render()
        self.interactor.Initialize()
        self.interactor.Start()

    def grab(self) -> np.ndarray:
        """The current frame as an ``(H, W, 3)`` uint8 array, top row first."""
        self.render()
        capture = vtk.vtkWindowToImageFilter()
        capture.SetInput(self.window)
        capture.SetInputBufferTypeToRGB()
        capture.ReadFrontBufferOff()
        capture.Update()
        img = capture.GetOutput()
        w, h, _ = img.GetDimensions()
        arr = vtk_to_numpy(img.GetPointData().GetScalars()).reshape(h, w, 3)
        return np.ascontiguousarray(arr[::-1])

    def screenshot(self, path: Path) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        self.render()
        capture = vtk.vtkWindowToImageFilter()
        capture.SetInput(self.window)
        capture.SetInputBufferTypeToRGB()
        capture.ReadFrontBufferOff()
        capture.Update()
        writer = vtk.vtkPNGWriter()
        writer.SetFileName(str(path))
        writer.SetInputConnection(capture.GetOutputPort())
        writer.Write()

    def orbit(self, degrees: float) -> None:
        self.view.GetActiveCamera().Azimuth(degrees)
        self.view.ResetCameraClippingRange()


def _unit(v) -> np.ndarray:
    v = np.asarray(v, float)
    n = np.linalg.norm(v)
    return v / n if n > 1e-12 else v


# ----------------------------------------------------------------------------
# Movies and slide assets
# ----------------------------------------------------------------------------

FPS = 30


def _smooth(t: float) -> float:
    """0 -> 1 -> 0 over ``t`` in [0, 1], with zero velocity at both ends (loops cleanly)."""
    return 0.5 - 0.5 * math.cos(2 * math.pi * t)


MOVIES = {
    # name: (state, seconds, per-frame state function, orbit degrees over the movie)
    "orbit": (State(theta_deg=35), 12.0, None, 360.0),
    "sweep-theta": (State(theta_deg=4), 10.0, lambda s, t: replace(s, theta_deg=4 + 78 * _smooth(t)), 0.0),
    "sweep-lambda3": (State(theta_deg=35), 10.0, lambda s, t: replace(s, lambda3=2.8 - 2.2 * _smooth(t)), 0.0),
    "perturb": (State(mode="perturb", eps=0.0), 10.0, lambda s, t: replace(s, eps=1.1 * _smooth(t)), 0.0),
}


def write_movie(name: str, out: Path, *, width: int = 1920, height: int = 1080, fps: int = FPS) -> Path:
    """Render one of :data:`MOVIES` offscreen and encode it with ffmpeg."""
    state, seconds, step, orbit = MOVIES[name]
    scene = SineTheta3D(state, width=width, height=height, offscreen=True, interactive=False)
    n = int(round(seconds * fps))
    out.parent.mkdir(parents=True, exist_ok=True)
    cmd = [
        "ffmpeg", "-y", "-loglevel", "error",
        "-f", "rawvideo", "-pix_fmt", "rgb24", "-s", f"{width}x{height}", "-r", str(fps), "-i", "-",
        "-c:v", "libx264", "-pix_fmt", "yuv420p", "-crf", "18", "-movflags", "+faststart", str(out),
    ]
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE)
    try:
        for k in range(n):
            t = k / n
            if step is not None:
                scene.state = step(state, t)
                scene.update()
            if k and orbit:
                scene.orbit(orbit / n)
            proc.stdin.write(scene.grab().tobytes())
    finally:
        proc.stdin.close()
        if proc.wait() != 0:
            raise RuntimeError(f"ffmpeg failed writing {out}")
    return out


STILLS = {
    "still-exact": State(show_trial=False),
    "still-planes": State(show_sine=False, show_residual=False),
    "still-sine": State(show_residual=False),
    "still-residual": State(),
    "still-perturb": State(mode="perturb", eps=0.8),
}


def write_still(name: str, out: Path, *, width: int = 1200, height: int = 1000) -> Path:
    scene = SineTheta3D(STILLS[name], width=width, height=height, offscreen=True, interactive=False, layout="still")
    cam = scene.view.GetActiveCamera()
    cam.SetViewAngle(34.0)
    scene.screenshot(out)
    return out


def write_app_screenshot(out: Path, *, width: int = 1920, height: int = 1080) -> Path:
    """The full interactive layout (sliders and help included), rendered offscreen."""
    scene = SineTheta3D(State(), width=width, height=height, offscreen=True, interactive=True)
    scene.screenshot(out)
    return out


def write_slide_assets(directory: Path) -> list[Path]:
    directory.mkdir(parents=True, exist_ok=True)
    made = [write_still(name, directory / f"{name}.png") for name in STILLS]
    made.append(write_app_screenshot(directory / "app.png"))
    made += [write_movie(name, directory / f"{name}.mp4") for name in MOVIES]
    return made


# ----------------------------------------------------------------------------
# CLI
# ----------------------------------------------------------------------------


def _parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--mode", choices=["trial", "perturb"], default="trial")
    p.add_argument("--theta", type=float, default=35.0, help="trial-plane tilt in degrees")
    p.add_argument("--phi", type=float, default=-25.0, help="hinge azimuth in degrees")
    p.add_argument("--lambda3", type=float, default=m3.DEFAULT_EIGENVALUES[2], help="unwanted eigenvalue")
    p.add_argument("--eps", type=float, default=0.5, help="perturbation size (perturb mode)")
    p.add_argument("--size", default="1600x900", help="window size WxH")
    p.add_argument("--screenshot", type=Path, help="render once offscreen to this PNG and exit")
    p.add_argument("--movie", choices=sorted(MOVIES), help="render a movie offscreen (see --out)")
    p.add_argument("--out", type=Path, help="output path for --movie")
    p.add_argument("--slide-assets", type=Path, metavar="DIR", help="write every still and movie the 3D slides use")
    return p


def main() -> None:
    args = _parser().parse_args()
    if args.slide_assets:
        for path in write_slide_assets(args.slide_assets):
            print(path)
        return
    if args.movie:
        print(write_movie(args.movie, args.out or Path("renders") / f"sine-theta-3d-{args.movie}.mp4"))
        return
    width, height = (int(v) for v in args.size.lower().split("x"))
    state = State(mode=args.mode, theta_deg=args.theta, phi_deg=args.phi, lambda3=args.lambda3, eps=args.eps)
    if args.screenshot:
        scene = SineTheta3D(state, width=width, height=height, offscreen=True, interactive=False)
        scene.screenshot(args.screenshot)
        print(args.screenshot)
        return
    SineTheta3D(state, width=width, height=height).interact()


if __name__ == "__main__":
    main()
