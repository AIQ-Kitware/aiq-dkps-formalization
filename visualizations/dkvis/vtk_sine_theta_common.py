"""Shared VTK helpers for sine-theta scenes."""

from __future__ import annotations

from pathlib import Path

import numpy as np
import vtk


def rgb(hex_value: str) -> tuple[float, float, float]:
    value = hex_value.lstrip("#")
    return tuple(int(value[i : i + 2], 16) / 255.0 for i in (0, 2, 4))


COLORS = {
    "background": rgb("#10141c"),
    "axes": rgb("#667085"),
    "desired": rgb("#f2f4f7"),
    "trial": rgb("#fdb022"),
    "projection": rgb("#32d583"),
    "sine": rgb("#ee46bc"),
    "residual": rgb("#36bffa"),
    "angle": rgb("#f97066"),
    "text": rgb("#f9fafb"),
    "muted": rgb("#98a2b3"),
    "accent": rgb("#7cd4fd"),
}


def line_actor(
    start: np.ndarray,
    end: np.ndarray,
    *,
    color: tuple[float, float, float],
    width: float = 3.0,
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
    return source, actor


def polyline_actor(
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


def text_actor(text: str, *, x: int, y: int, size: int = 20) -> vtk.vtkTextActor:
    actor = vtk.vtkTextActor()
    actor.SetInput(text)
    actor.SetDisplayPosition(x, y)
    prop = actor.GetTextProperty()
    prop.SetFontSize(size)
    prop.SetColor(*COLORS["text"])
    prop.SetFontFamilyToCourier()
    return actor


def small_label(text: str, position: tuple[float, float], *, scale: float = 0.085) -> vtk.vtkFollower:
    vector = vtk.vtkVectorText()
    vector.SetText(text)
    mapper = vtk.vtkPolyDataMapper()
    mapper.SetInputConnection(vector.GetOutputPort())
    actor = vtk.vtkFollower()
    actor.SetMapper(mapper)
    actor.SetScale(scale, scale, scale)
    actor.SetPosition(float(position[0]), float(position[1]), 0.0)
    actor.GetProperty().SetColor(*COLORS["text"])
    return actor


class BaseScene2D:
    """Minimal helper for 2D VTK slide-style scenes."""

    def __init__(self, *, width: int = 1400, height: int = 900, offscreen: bool = False, title: str = "Davis--Kahan visualization") -> None:
        self.renderer = vtk.vtkRenderer()
        self.renderer.SetBackground(*COLORS["background"])
        self.window = vtk.vtkRenderWindow()
        self.window.SetSize(width, height)
        self.window.SetWindowName(title)
        self.window.AddRenderer(self.renderer)
        if offscreen:
            self.window.SetOffScreenRendering(1)

        self.interactor = vtk.vtkRenderWindowInteractor()
        self.interactor.SetRenderWindow(self.window)
        style = vtk.vtkInteractorStyleTrackballCamera()
        self.interactor.SetInteractorStyle(style)

        camera = self.renderer.GetActiveCamera()
        camera.SetPosition(0.0, 0.0, 7.0)
        camera.SetFocalPoint(0.0, 0.0, 0.0)
        camera.SetViewUp(0.0, 1.0, 0.0)
        camera.ParallelProjectionOn()
        camera.SetParallelScale(2.3)

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
