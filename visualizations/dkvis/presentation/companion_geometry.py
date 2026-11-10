"""Native Manim geometry for companion-slide figures.

All figure identifiers used in the companion curriculum have an explicit visual
family. A new identifier must be registered here rather than falling back to
an unrelated generic diagram. These are geometric sketches for instruction;
worked numerical examples and all formulas remain authored in deck JSON.

No SVGs are read, authored, or exported by this module.
"""
from __future__ import annotations

import math

from dkvis.palette import PALETTE

FIGURE_KINDS = {
    'analysis-synthesis': 'abstract',
    'angle': 'angle',
    'basis-change': 'abstract',
    'block-operator': 'block',
    'block-reflection': 'block',
    'cauchy-convergence': 'abstract',
    'clusters': 'spectrum',
    'complex-rotation': 'angle',
    'counterexample': 'matching',
    'doubled-angle': 'angle',
    'dual-functional': 'norm',
    'families': 'abstract',
    'g2-acute-vs-uniform': 'angle',
    'g2-angle-operators': 'angle',
    'g2-banach-fixedpoint': 'flow',
    'g2-block-diagonal': 'block',
    'g2-compact-angle-spectrum': 'spectrum',
    'g2-continuous-angle': 'spectrum',
    'g2-convex-transfer': 'kyfan',
    'g2-cosine-compression': 'polar',
    'g2-counterexample-norm': 'matrix',
    'g2-cs-block': 'block',
    'g2-decay-flow': 'flow',
    'g2-defect-quarterturn': 'matching',
    'g2-direct-half-angle': 'angle',
    'g2-directed-sine': 'polar',
    'g2-entry-solution': 'matrix',
    'g2-frobenius-columns': 'kyfan',
    'g2-gauge-balls': 'norm',
    'g2-gram-order': 'matrix',
    'g2-graph-transversality': 'graph',
    'g2-halmos-angle-limit': 'angle',
    'g2-halmos-blocks': 'angle',
    'g2-halmos-six-space': 'matching',
    'g2-intertwiner': 'angle',
    'g2-kron-map': 'matrix',
    'g2-kyfan-frames': 'kyfan',
    'g2-kyfan-staircase': 'kyfan',
    'g2-loewner-square': 'graph',
    'g2-majorization-bars': 'kyfan',
    'g2-majorization-transfer': 'kyfan',
    'g2-majorization-weights': 'kyfan',
    'g2-matrix-flow': 'flow',
    'g2-mixed-gap': 'spectrum',
    'g2-norm-hierarchy': 'norm',
    'g2-operator-trig': 'angle',
    'g2-pinching-average': 'block',
    'g2-polar-support': 'polar',
    'g2-principal-overlap': 'angle',
    'g2-rank-truncation': 'kyfan',
    'g2-rosenblum-contour': 'contour',
    'g2-rosenblum-multiloop': 'matching',
    'g2-scalar-gap': 'spectrum',
    'g2-schatten-profile': 'norm',
    'g2-singular-minmax': 'kyfan',
    'g2-skew-flow': 'flow',
    'g2-sylvester-bridge': 'matrix',
    'g2-sylvester-gap': 'spectrum',
    'g2-sylvester-grid': 'matrix',
    'g2-sylvester-types': 'block',
    'g2-unitary-orbit': 'norm',
    'g2-zero-denominator': 'spectrum',
    'g2-zero-padding': 'block',
    'gram-geometry': 'graph',
    'graph-subspace': 'graph',
    'hilbert-coordinates': 'graph',
    'induction': 'abstract',
    'ky-fan': 'kyfan',
    'matching': 'matching',
    'matching-graph': 'matching',
    'norm-balls': 'norm',
    'operator-ball': 'norm',
    'operator-ideal': 'norm',
    'orthogonal': 'graph',
    'orthogonal-projection': 'graph',
    'principal-angle': 'angle',
    'principal-pairs': 'angle',
    'projection': 'graph',
    'rayleigh-quotient': 'graph',
    'residual': 'abstract',
    'resolvent-spectrum': 'spectrum',
    'roadmap': 'abstract',
    'rotation': 'angle',
    'rotation-chord': 'angle',
    'sine-theta': 'angle',
    'spectral-cutoff': 'spectrum',
    'spectral-gap': 'spectrum',
    'spectrum': 'spectrum',
    'squared-displacement-prefix': 'kyfan',
    'sylvester': 'matrix',
    'trial-plane': 'graph',
}


def companion_figure_kind(identifier: str) -> str:
    """Return the authored Manim figure family; refuse undeclared symbols."""
    return FIGURE_KINDS[identifier]


def build_companion_geometry(identifier: str):
    """Construct a 5.2 by 3.0-unit figure from native Manim primitives."""
    from manim import (
        DOWN, LEFT, RIGHT, UP, Arrow, Arc, Circle, DashedLine, Dot,
        Line, Rectangle, RoundedRectangle, Text, VGroup, VMobject,
    )
    kind = companion_figure_kind(identifier)
    p = PALETTE
    fg, blue, gold, pink = p['FG'], p['WANTED'], p['TRIAL'], p['SINE']
    faint, green, gap = p['FAINT'], p['RESID'], p['GAP']
    out = VGroup()

    def label(t, x, y, color=fg, size=19):
        mob = Text(t, font='DejaVu Sans', font_size=size, color=color)
        mob.move_to([x, y, 0]); out.add(mob)
        return mob

    def seg(x1,y1,x2,y2,color=fg,weight=3,dashed=False):
        cls = DashedLine if dashed else Line
        line = cls([x1,y1,0],[x2,y2,0],color=color,stroke_width=weight)
        out.add(line); return line

    def spot(x,y,color=blue,r=.075):
        d=Dot([x,y,0],radius=r,color=color);out.add(d);return d

    def box(x,y,w,h,color=blue,fill=.12):
        r=RoundedRectangle(width=w,height=h,corner_radius=.08,stroke_color=color,
                           stroke_width=2,fill_color=color,fill_opacity=fill)
        r.move_to([x,y,0]);out.add(r);return r

    title={
        'angle':'Principal-plane geometry','graph':'Subspace and projection geometry',
        'spectrum':'Spectral location','contour':'Spectral contour',
        'block':'Block operator structure','kyfan':'Singular-value comparison',
        'norm':'Operator-norm geometry','matrix':'Sylvester operator',
        'flow':'Operator evolution','matching':'Transport and matching',
        'polar':'Polar support','abstract':'Logical construction',
    }[kind]
    label(title,0,1.29,p['MUTED'],18)

    if kind == 'angle':
        ox,oy=-1.65,-.88
        seg(ox,oy,2.05,oy,blue,5)
        angle=.54 if 'doubled' not in identifier else .86
        length=3.50
        seg(ox,oy,ox+length*math.cos(angle),oy+length*math.sin(angle),gold,5)
        out.add(Arc(radius=.66,start_angle=0,angle=angle,arc_center=[ox,oy,0],color=pink,stroke_width=3))
        spot(ox,oy,fg,.055)
        label('U',1.96,-1.10,blue,22)
        label('V',ox+length*math.cos(angle)+.1,oy+length*math.sin(angle)+.1,gold,22)
        label('θ',-.78,-.50,pink,23)
        if 'cosine' in identifier or 'overlap' in identifier:
            label('cos θ',0,-1.14,gold,18)
        elif 'sine' in identifier:
            label('sin θ',.25,-1.14,pink,18)
    elif kind == 'graph':
        seg(-2.2,-.85,2.25,-.85,blue,3)
        seg(-1.68,-1.17,-1.68,1.08,faint,2)
        seg(-1.68,-.85,1.65,.59,gold,5)
        seg(1.15,-.85,1.15,.37,pink,3,True)
        spot(1.15,.37,gold)
        label('U',1.8,-1.06,blue,21)
        label('U⊥',-2,.96,p['MUTED'],18)
        label('residual',1.75,.12,pink,18)
        label('projected component',-.21,-1.13,fg,16)
    elif kind == 'spectrum':
        seg(-2.26,-.52,2.24,-.52,faint,3)
        for x in [-1.85,-1.20,-.91]:spot(x,-.52,blue,.085)
        for x in [.88,1.52,1.93]:spot(x,-.52,gold,.085)
        seg(-.72,.16,.72,.16,gap,2)
        seg(-.72,.02,-.72,.30,gap,2)
        seg(.72,.02,.72,.30,gap,2)
        label('δ',0,.47,gap,26)
        label('selected',-1.36,-.93,blue,20)
        label('other',1.46,-.93,gold,20)
    elif kind == 'contour':
        seg(-2.15,-.82,2.15,-.82,faint,2)
        seg(-1.85,-1.18,-1.85,1.02,faint,2)
        for x in [-1.36,-.84,-.18]: spot(x,-.82,blue,.08)
        for x in [1.39,1.90]: spot(x,-.82,gold,.08)
        circle=Circle(radius=.97,color=gap,stroke_width=3).move_to([-.76,-.62,0]);out.add(circle)
        label('Γ',-.75,.55,gap,23);label('σ(A)',-1.13,-1.17,blue,18);label('σ(B)',1.63,-1.18,gold,18)
    elif kind == 'block':
        for x in [-.90,.90]:
            for y in [-.33,.46]:
                color=blue if (x*y<0) else gold
                box(x,y,1.58,.68,color,.12)
        for x,y,t,c in [(-.90,.46,'A',blue),(.90,.46,'B',pink),(-.90,-.33,'C',pink),(.90,-.33,'D',gold)]:
            label(t,x,y,c,27)
        label('diagonal',-.91,-1.13,blue,17)
        label('coupling',1.06,-1.13,pink,17)
    elif kind == 'kyfan':
        seg(-2.25,-.98,2.25,-.98,faint,2)
        h1=[1.45,1.12,.78,.36];h2=[1.19,1.02,.87,.61]
        for j,(u,v) in enumerate(zip(h1,h2)):
            x=-1.78+j*1.05
            b=Rectangle(width=.29,height=u,stroke_width=0,fill_color=blue,fill_opacity=.9).move_to([x,-.98+u/2,0]);out.add(b)
            b=Rectangle(width=.29,height=v,stroke_width=0,fill_color=gold,fill_opacity=.83).move_to([x+.31,-.98+v/2,0]);out.add(b)
            label(str(j+1),x+.16,-1.21,p['MUTED'],15)
        label('s₁',-1.82,.72,blue,17)
        label('prefix sums control comparisons',0,.88,fg,15)
    elif kind == 'norm':
        for rad,color in [(1.03,p['GAP']),(.79,blue),(.50,gold)]:
            c=Circle(radius=rad,color=color,stroke_width=3);c.stretch(1.55,0);out.add(c)
        label('S₂',-1.52,.52,p['GAP'],21);label('S₁',-.95,.11,blue,22)
        label('norms read singular values',0,-1.22,fg,17)
    elif kind == 'matrix':
        for x in [-.68,.68]:
            for y in [-.42,.37]:
                box(x,y,1.19,.68,blue if x<0 else gold,.10)
        for x,y,t in [(-.68,.37,'a₁−b₁'),(.68,.37,'a₁−b₂'),(-.68,-.42,'a₂−b₁'),(.68,-.42,'a₂−b₂')]:
            label(t,x,y,fg,18)
        label('AX − XB = C',0,-1.14,pink,21)
    elif kind == 'flow':
        seg(-2.2,-.99,2.22,-.99,faint,2)
        seg(-2.2,-.99,-2.2,.99,faint,2)
        curve=VMobject(color=blue,stroke_width=4)
        curve.set_points_as_corners([[-2.05+4.0*t/60, -.87+1.63*math.exp(-3.3*t/60),0] for t in range(61)])
        out.add(curve)
        curve2=VMobject(color=gold,stroke_width=3)
        curve2.set_points_as_corners([[-2.05+4.0*t/60, -.87+1.29*math.exp(-1.5*t/60),0] for t in range(61)])
        out.add(curve2)
        label('t',2.30,-1.02,fg,18);label('contraction',.28,.90,blue,20)
    elif kind == 'matching':
        for x in [-1.87,-.67,.67,1.87]: spot(x,.24,blue,.16)
        for x in [-1.87,-.67,.67,1.87]: spot(x,-.81,gold,.16)
        for x in [-1.87,-.67,.67,1.87]: seg(x,.12,x,-.69,pink,4)
        label('source',-2.02,.72,blue,18)
        label('target',-2.04,-1.24,gold,18)
        label('pairwise transport',.55,.90,fg,17)
    elif kind == 'polar':
        box(-1.42,-.30,1.38,1.05,blue,.10)
        box(1.42,-.30,1.38,1.05,gold,.10)
        label('support',-1.42,-.25,blue,20)
        label('range',1.42,-.25,gold,20)
        a=Arrow([-.52,-.30,0],[.46,-.30,0],color=pink,stroke_width=4,buff=.08)
        out.add(a);label('partial isometry',0,.55,pink,18)
    elif kind == 'abstract':
        for x,t,c in [(-1.77,'hypothesis',blue),(0,'construction',pink),(1.77,'conclusion',gold)]:
            box(x,-.24,1.50,.84,c,.10)
            label(t,x,-.24,c,16)
        out.add(Arrow([-1.00,-.24,0],[-.85,-.24,0],buff=0,color=fg))
        out.add(Arrow([.85,-.24,0],[1.02,-.24,0],buff=0,color=fg))
        label('deduction',0,-1.17,fg,18)
    else:
        raise AssertionError(kind)

    if out.width > 5.25:
        out.scale_to_fit_width(5.25)
    if out.height > 3.15:
        out.scale_to_fit_height(3.15)
    out.move_to([0,0,0])
    return out
