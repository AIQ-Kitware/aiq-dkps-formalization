"""The same trial-plane drawing and explicit semantic colors throughout the lesson."""
import numpy as np
from manim import Arrow, Dot, Line, Polygon, Rectangle, VGroup, DOWN
from dkvis.slide_style import CURRENT, TRIAL, RESID, MUTED, FG, math, tex


def formula(*parts, size=31):
    """Color whole mathematical terms by role, never by bare-letter matching."""
    text=[p[0] if isinstance(p, tuple) else p for p in parts]
    result=math(*text,size=size)
    for i,p in enumerate(parts):
        if isinstance(p,tuple):
            result[i].set_color(p[1])
    return result


def matrix_tiles(n, color, cell=.28):
    tiles=VGroup()
    for row in range(n):
        for col in range(n):
            square=Rectangle(width=cell,height=cell,color=color,stroke_width=1,
                             fill_color=color,fill_opacity=.08+.05*((row+col)%3))
            square.move_to([col*(cell+.035),-row*(cell+.035),0])
            tiles.add(square)
    return tiles.move_to([0,0,0])


class TrialPlane(VGroup):
    """Perspective sketch of span(e1,e2); vertical arrows represent its normal.

    The screen map is a drawing projection, not an isometry. Norms refer to
    the actual 3D vectors from model.py, not their foreshortened screen lengths.
    """
    def __init__(self, origin=(-3.25,-.45,0), scale=.75):
        super().__init__()
        self.origin=np.array(origin,dtype=float)
        self.unit=scale
        self.plane=Polygon(*(self.point([x,y,0]) for x,y in
            [(-2.2,-2.2),(2.2,-2.2),(2.2,2.2),(-2.2,2.2)]),
            color=TRIAL,fill_color=TRIAL,fill_opacity=.07,stroke_width=2)
        self.grid=VGroup()
        for v in [-2,-1,0,1,2]:
            self.grid.add(Line(self.point([v,-2.2,0]),self.point([v,2.2,0]),
                               color=TRIAL,stroke_opacity=.18,stroke_width=1),
                          Line(self.point([-2.2,v,0]),self.point([2.2,v,0]),
                               color=TRIAL,stroke_opacity=.18,stroke_width=1))
        self.origin_dot=Dot(self.origin,radius=.035,color=MUTED)
        self.label=math(r'\mathcal T',size=35,color=TRIAL).move_to(self.point([-1.7,1.8,0]))
        self.caption=tex('Trial plane, drawn in perspective',size=21,color=MUTED).move_to([self.origin[0],-2.02,0])
        self.add(self.plane,self.grid,self.origin_dot,self.label,self.caption)

    def point(self, vector):
        x,y,z=np.asarray(vector,dtype=float)
        return self.origin+self.unit*np.array([x-.6*y,.22*x+.65*y+z,0])

    def arrow(self, end, color, start=None, width=5):
        start=np.zeros(3) if start is None else np.asarray(start)
        end=np.asarray(end)
        if np.linalg.norm(end-start)<1e-9:
            return Dot(self.point(end),radius=.045,color=color)
        return Arrow(self.point(start),self.point(end),buff=0,color=color,
                     stroke_width=width,max_tip_length_to_length_ratio=.18)

    def basis(self):
        arrows=VGroup(self.arrow([1,0,0],TRIAL),self.arrow([0,1,0],TRIAL))
        labels=VGroup(math('q_1',size=25,color=TRIAL).move_to(self.point([1.25,-.2,0])),
                      math('q_2',size=25,color=TRIAL).move_to(self.point([-.15,1.35,0])))
        return VGroup(arrows,labels)

    def selection(self, true, retained):
        """The output and its decomposition, sharing exact endpoints."""
        return VGroup(self.arrow(true,CURRENT),self.arrow(retained,TRIAL),
                      self.arrow(true,RESID,start=retained))
