"""Shared VTK helpers for the Proposition 4.4 visualizations."""

from __future__ import annotations

import math

import numpy as np
import vtk


def _rgb(hex_value: str) -> tuple[float, float, float]:
    value = hex_value.lstrip("#")
    return tuple(int(value[i : i + 2], 16) / 255.0 for i in (0, 2, 4))


COLORS = {
    "background": _rgb("#10141c"),
    "panel_background": _rgb("#10141c"),
    "band_background": _rgb("#151b25"),
    "control_background": _rgb("#171c26"),
    "ghost": _rgb("#667085"),
    "text": _rgb("#f9fafb"),
    "muted": _rgb("#98a2b3"),
    "u0": _rgb("#f79009"),
    "u1": _rgb("#36bffa"),
    "v0": _rgb("#73e2a3"),
    "v1": _rgb("#f97066"),
    "current": _rgb("#f2f4f7"),
    "direct": _rgb("#84caff"),
    "competitor": _rgb("#73e2a3"),
    "accent": _rgb("#f97066"),
    "connector": _rgb("#d0d5dd"),
}


def text_actor(
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


def label3d(
    text: str,
    color: tuple[float, float, float],
    *,
    size: int = 15,
) -> vtk.vtkBillboardTextActor3D:
    actor = vtk.vtkBillboardTextActor3D()
    actor.SetInput(text)
    prop = actor.GetTextProperty()
    prop.SetFontSize(size)
    prop.SetColor(*color)
    prop.SetJustificationToCentered()
    return actor


def polyline_actor(
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


def set_polyline(data: vtk.vtkPolyData, points: np.ndarray, *, closed: bool = False) -> None:
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


def line_actor(
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


def arrow_actor(
    color: tuple[float, float, float],
    *,
    opacity: float = 1.0,
    shaft_radius: float = 0.018,
    tip_radius: float = 0.07,
    tip_length: float = 0.20,
) -> vtk.vtkActor:
    source = vtk.vtkArrowSource()
    source.SetTipResolution(24)
    source.SetShaftResolution(24)
    source.SetTipLength(tip_length)
    source.SetTipRadius(tip_radius)
    source.SetShaftRadius(shaft_radius)
    mapper = vtk.vtkPolyDataMapper()
    mapper.SetInputConnection(source.GetOutputPort())
    actor = vtk.vtkActor()
    actor.SetMapper(mapper)
    actor.GetProperty().SetColor(*color)
    actor.GetProperty().SetOpacity(opacity)
    return actor


def set_arrow(actor: vtk.vtkActor, vector: np.ndarray, *, hide_below: float = 1e-7) -> bool:
    vector = np.asarray(vector, dtype=float)
    length = float(np.linalg.norm(vector[:2]))
    if length < hide_below:
        actor.SetVisibility(False)
        return False
    angle = math.degrees(math.atan2(float(vector[1]), float(vector[0])))
    actor.SetVisibility(True)
    actor.SetPosition(0.0, 0.0, 0.0)
    actor.SetOrientation(0.0, 0.0, angle)
    actor.SetScale(length, 1.0, 1.0)
    return True


def configure_2d_camera(renderer: vtk.vtkRenderer, *, scale: float = 1.63) -> None:
    camera = vtk.vtkCamera()
    camera.SetPosition(0.0, 0.0, 5.0)
    camera.SetFocalPoint(0.0, 0.0, 0.0)
    camera.SetViewUp(0.0, 1.0, 0.0)
    camera.ParallelProjectionOn()
    camera.SetParallelScale(scale)
    renderer.SetActiveCamera(camera)


def add_reference_frame(renderer: vtk.vtkRenderer, *, radius: float = 1.0) -> None:
    circle_angles = np.linspace(0.0, 2.0 * math.pi, 129)
    circle = np.column_stack(
        [radius * np.cos(circle_angles), radius * np.sin(circle_angles), np.zeros_like(circle_angles)]
    )
    circle_data, circle_actor = polyline_actor(COLORS["ghost"], width=1.5, opacity=0.45)
    set_polyline(circle_data, circle)
    renderer.AddActor(circle_actor)

    axis_x_source, axis_x_actor = line_actor(COLORS["ghost"], width=1.0, opacity=0.30)
    axis_y_source, axis_y_actor = line_actor(COLORS["ghost"], width=1.0, opacity=0.30)
    axis_x_source.SetPoint1(-1.22, 0.0, 0.0)
    axis_x_source.SetPoint2(1.22, 0.0, 0.0)
    axis_y_source.SetPoint1(0.0, -1.22, 0.0)
    axis_y_source.SetPoint2(0.0, 1.22, 0.0)
    renderer.AddActor(axis_x_actor)
    renderer.AddActor(axis_y_actor)
