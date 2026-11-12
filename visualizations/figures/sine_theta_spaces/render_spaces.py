#!/usr/bin/env python3
"""Auditable spaces-first Davis--Kahan sine-theta figure (matplotlib, not Manim).

Usage (from the repository root):
  python visualizations/figures/sine_theta_spaces/render_spaces.py
  python visualizations/figures/sine_theta_spaces/render_spaces.py --check

Generated text-based SVG is committed, while PNG is a local preview only.
Palette values are loaded from the journal's actual math_symbol_colors.tex.
"""
from __future__ import annotations

import argparse
import math
import re
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch, Polygon
from matplotlib import colors as mcolors

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
COLOR_SOURCE = ROOT / "papers/dk_formalization_journal/math_symbol_colors.tex"
SVG_OUT = HERE / "sine_theta_spaces.svg"
PNG_OUT = HERE / "sine_theta_spaces_preview.png"

# Illustrative 3D model; separate from the journal's 2D Figure 1 example.
THETA_DEG = 12.0  # Tilt of trial plane away from exact wanted plane.
FRAME_ROTATION_DEG = 24.0  # F_0 basis rotated within the wanted plane.
TRIAL_FRAME_ROTATION_DEG = -17.0  # E_0 basis rotated within trial plane.
EXACT_EIGENVALUES = (1.90, 1.65, 0.70)
REQUIRED_COLORS = (
    "dkfg", "dkmuted", "dkambient", "dkwanted", "dkunwanted",
    "dktrial", "dksine", "dkresid", "dkgap",
    "dkwantedframe", "dkunwantedframe", "dktrialframe",
    "dkwantedprojection", "dkwantedspectrum", "dkunwantedspectrum",
)


def paper_palette(source: Path = COLOR_SOURCE) -> dict[str, str]:
    raw = source.read_text(encoding="utf8")
    found = dict(re.findall(r"\\definecolor\{([^}]+)\}\{HTML\}\{([0-9A-Fa-f]{6})\}", raw))
    missing = set(REQUIRED_COLORS) - set(found)
    if missing:
        raise ValueError(f"Journal palette is missing: {sorted(missing)}")
    return {name: "#" + found[name].upper() for name in REQUIRED_COLORS}


def model() -> dict[str, np.ndarray | float]:
    theta = math.radians(THETA_DEG)
    alpha = math.radians(FRAME_ROTATION_DEG)
    beta = math.radians(TRIAL_FRAME_ROTATION_DEG)
    ex, ey, ez = np.eye(3)
    # W = span(ex, ey). U = span(ez). This is the EXACT splitting.
    f0 = np.column_stack((math.cos(alpha)*ex + math.sin(alpha)*ey,
                          -math.sin(alpha)*ex + math.cos(alpha)*ey))
    f1 = ez.reshape(3, 1)
    t2 = math.cos(theta)*ey + math.sin(theta)*ez
    # Trial plane T = span(ex, t2); rotate its coordinate basis to stress that
    # the abstract choice of F coordinates is independent of ambient axes.
    e0 = np.column_stack((math.cos(beta)*ex + math.sin(beta)*t2,
                          -math.sin(beta)*ex + math.cos(beta)*t2))
    pex = f0 @ f0.T
    pperp = f1 @ f1.T
    ahat = np.diag(EXACT_EIGENVALUES)
    lambda0 = f0.T @ ahat @ f0
    lambda1 = f1.T @ ahat @ f1
    a0 = e0.T @ ahat @ e0
    # A unit trial vector, not necessarily a coordinate-basis vector.
    v = t2
    wanted = pex @ v
    unwanted = pperp @ v
    return locals()


def check_model() -> dict[str, float]:
    d = model()
    I = np.eye(3)
    def close(a, b):
        assert np.allclose(a, b, rtol=0, atol=1e-12), (a, b)
    close(d['f0'].T @ d['f0'], np.eye(2))
    close(d['f1'].T @ d['f1'], np.eye(1))
    close(d['e0'].T @ d['e0'], np.eye(2))
    close(d['f0'].T @ d['f1'], np.zeros((2,1)))
    close(d['pex'] + d['pperp'], I)
    close(d['pex'] @ d['pex'], d['pex'])
    close(d['pex'] @ d['pperp'], np.zeros((3,3)))
    close(d['v'], d['wanted'] + d['unwanted'])
    close(d['v'], d['e0'] @ (d['e0'].T @ d['v']))
    close(d['f0'] @ d['lambda0'], d['ahat'] @ d['f0'])
    close(d['f1'] @ d['lambda1'], d['ahat'] @ d['f1'])
    close(np.sort(np.linalg.eigvalsh(d['lambda0'])), np.array([1.65,1.90]))
    close(d['lambda1'], np.array([[0.70]]))
    close(np.array([np.linalg.norm(d['unwanted'])]), np.array([math.sin(d['theta'])]))
    assert abs(d['theta']-math.radians(12)) < 1e-12
    return {"trial_angle_deg": THETA_DEG,
            "projection_norm": float(np.linalg.norm(d['unwanted'])),
            "exact_complement_eigenvalue": float(d['lambda1'][0, 0]),
            "wanted_eigenvalues": tuple(np.linalg.eigvalsh(d['lambda0']))}


def softened(color: str, fraction: float = 0.92) -> tuple[float, float, float]:
    rgb = np.array(mcolors.to_rgb(color))
    return tuple((1 - fraction)*rgb + fraction*np.ones(3))


def box(fig, x, y, w, h, *, face='#ffffff', edge='#D6DFE9', roundness=.014):
    fig.add_artist(FancyBboxPatch(
        (x,y),w,h,boxstyle=f'round,pad=0.003,rounding_size={roundness}',
        transform=fig.transFigure, linewidth=1.0, facecolor=face,
        edgecolor=edge, zorder=0, clip_on=False))


def figtext(fig, x, y, s, *, size=14, color='#1B1F24', weight=None,
            va='center', ha='left', math=False):
    return fig.text(x,y,s,transform=fig.transFigure,fontsize=size,color=color,
                    fontfamily='STIXGeneral',
                    weight=weight,va=va,ha=ha)


def arrow(ax, p, q, color, *, lw=2.4, ms=12, z=10, alpha=1.0):
    a=FancyArrowPatch(p,q,arrowstyle='-|>',mutation_scale=ms,
                      color=color,linewidth=lw, zorder=z, alpha=alpha)
    ax.add_patch(a)


def place(ax,x,y,s,*,size=13,color='#1B1F24',ha='left',va='center',weight='normal',rotation=0):
    return ax.text(x,y,s,fontsize=size,color=color,ha=ha,va=va,
                   fontfamily='STIXGeneral',weight=weight,rotation=rotation,zorder=30)


def build_figure(color: dict[str,str]):
    plt.rcParams.update({
        'font.family':'serif', 'font.serif':['STIXGeneral','DejaVu Serif'],
        'mathtext.fontset':'stix', 'svg.fonttype':'path', 'svg.hashsalt':'dk-sine-theta-spaces-v1', 'figure.facecolor':'white',
        'savefig.facecolor':'white',
    })
    wanted, unwanted, trial = color['dkwanted'],color['dkunwanted'],color['dktrial']
    angle, ink, muted = color['dksine'],color['dkfg'],color['dkmuted']
    fig=plt.figure(figsize=(16,9),dpi=160)
    # Layout in normalized figure coordinates: three intentionally distinct panels.
    box(fig,.033,.160,.596,.688)
    box(fig,.641,.448,.326,.400)
    box(fig,.641,.160,.326,.274)
    box(fig,.033,.032,.934,.108,face='#F7F9FC')

    figtext(fig,.048,.930,'Spaces and embeddings in the sine-theta setup',size=30,weight='bold')
    figtext(fig,.049,.881,'Exact orthogonal subspaces, an approximate trial subspace, and independent coordinate frames',size=15,color=muted)

    figtext(fig,.053,.812,'1   Subspaces of one ambient Hilbert space',size=18,weight='bold')
    figtext(fig,.053,.771,r'Illustrative slice: $E=\mathbb{R}^{3}$',size=13.2,color=muted,math=True)
    figtext(fig,.418,.771,r'$E=\operatorname{ran}(F_0)\oplus\operatorname{ran}(F_1)$',size=17,math=True,ha='center')

    # Geometry panel. The plane/line are *subspaces*, not separate regions
    # partitioning a rectangular picture: both pass through the origin.
    ax=fig.add_axes([.048,.218,.565,.518]);ax.set_aspect('equal');ax.axis('off')
    ax.set_xlim(0,10);ax.set_ylim(0,7.5)
    x0=np.array([4.35,3.48]); sx=np.array([1.08,-.245]); sy=np.array([.46,.58]); sz=np.array([0,1.18])
    def proj(v:np.ndarray)->np.ndarray:
        return x0 + v[0]*sx + v[1]*sy + v[2]*sz
    theta=math.radians(THETA_DEG)
    t2=np.array([0,math.cos(theta),math.sin(theta)])
    # Two 2D planes of dimension 2, both extending beyond shown crop.
    def corners(axis2):
        return np.array([proj(a*np.array([1.,0.,0.])+b*axis2) for a,b in
                         [(-2.20,-1.72),(2.20,-1.72),(2.20,1.72),(-2.20,1.72)]])
    # Wanted plane first, approximate tilted plane second.
    wp=Polygon(corners(np.array([0.,1.,0.])),facecolor=softened(wanted,.83),edgecolor=wanted,
               linewidth=2.1,alpha=.90,zorder=2)
    tp=Polygon(corners(t2),facecolor=softened(trial,.80),edgecolor=trial,
               linewidth=2.2,alpha=.34,zorder=3)
    ax.add_patch(wp);ax.add_patch(tp)
    # Ambient reference axes; gray axes are NOT distinguished mathematical data.
    for vec,txt,offset in [(np.array([1.,0,0]),r'$e_1$',(.02,-.14)),
                           (np.array([0.,1.,0]),r'$e_2$',(.16,-.02))]:
        end=proj(2.4*vec); arrow(ax,x0,end,'#9BA5B2',lw=1.25,ms=10,z=4,alpha=.7)
        place(ax,*(end+offset),txt,size=13,color='#8795A4')
    # Orthogonal exact complement is the 1D line, not a cyan planar region.
    below=proj(np.array([0.,0.,-2.35])); above=proj(np.array([0.,0.,2.6]))
    ax.plot([below[0],above[0]],[below[1],above[1]],color=unwanted,lw=2.8,zorder=5)
    arrow(ax,proj(np.array([0.,0.,1.85])),above,unwanted,lw=2.2,ms=13,z=7)
    # Chosen blue basis F_0 is rotated within its plane, independently of
    # the optional gray ambient reference coordinate frame.
    alpha=math.radians(FRAME_ROTATION_DEG)
    b1=np.array([math.cos(alpha),math.sin(alpha),0.])
    b2=np.array([-math.sin(alpha),math.cos(alpha),0.])
    for basis,label,scale in [(b1,r'$F_0 f_1$',1.25),(b2,r'$F_0 f_2$',1.20)]:
        pt=proj(scale*basis);arrow(ax,x0,pt,wanted,lw=1.5,ms=9,z=7,alpha=.85)
        offs=np.array([.05,.18]) if label.endswith('1$') else np.array([-.22,.18])
        place(ax,*(pt+offs),label,size=12.5,color=wanted)
    # Decompose a *single unit trial vector* v into orthogonal exact pieces.
    v=t2; pv=np.array([0.,math.cos(theta),0.]); uv=np.array([0.,0.,math.sin(theta)])
    p_v, p_pv=proj(2.10*v),proj(2.10*pv)
    arrow(ax,x0,p_pv,wanted,lw=2.8,ms=12,z=12)
    arrow(ax,p_pv,p_v,unwanted,lw=2.7,ms=11,z=13)
    arrow(ax,x0,p_v,trial,lw=3.4,ms=13,z=14)
    # Show a dashed amber trial *direction*, not a standalone vector only.
    u1=proj(-2.0*v);u2=proj(2.55*v)
    ax.plot([u1[0],u2[0]],[u1[1],u2[1]],color=trial,lw=1.2,ls='--',alpha=.7,zorder=9)
    # Mark points and controlled callouts (placed in verified open regions).
    ax.scatter(*x0,s=22,color=ink,zorder=15)
    ax.scatter(*p_v,s=27,color=trial,zorder=15)
    ax.scatter(*p_pv,s=24,color=wanted,zorder=15)
    place(ax,7.35,5.85,r'$T=\operatorname{ran}(E_0)$',size=16,color=trial,ha='center')
    place(ax,7.40,5.49,'trial plane',size=12,color=muted,ha='center')
    place(ax,1.08,2.42,r'$W=\operatorname{ran}(F_0)$',size=16,color=wanted)
    place(ax,1.10,2.06,'wanted exact plane',size=12,color=muted)
    place(ax,4.83,7.00,r'$U=\operatorname{ran}(F_1)$',size=15,color=unwanted)
    place(ax,4.88,6.67,'exact orthogonal complement',size=11.5,color=muted)
    place(ax,5.55,5.72,r'$v=E_0x$',size=15,color=trial)
    place(ax,6.30,4.17,r'$P_{\mathrm{ex}}v$',size=14.5,color=wanted)
    place(ax,6.26,5.03,r'$(I-P_{\mathrm{ex}})v$',size=13.5,color=unwanted)
    place(ax,1.1,.40,r'Gray: optional ambient axes. Blue arrows: a rotated $F_0$ frame.',size=11.8,color=muted)

    # Right upper panel: type-correct abstract coordinate systems.
    figtext(fig,.659,.807,'2   Coordinate spaces and maps',size=18,weight='bold')
    figtext(fig,.661,.762,'Abstract coordinates',size=11.5,color=muted)
    figtext(fig,.855,.762,'Their images inside $E$',size=11.5,color=muted,math=True)
    rows=[(.687,r'$F_{\mathrm{ex}}$',r'$F_0$',r'$\operatorname{ran}(F_0)$',wanted),
          (.607,r'$G$',r'$F_1$',r'$\operatorname{ran}(F_1)$',unwanted),
          (.527,r'$F$',r'$E_0$',r'$\operatorname{ran}(E_0)$',trial)]
    for y,domain,mapping,codomain,col in rows:
        box(fig,.662,y-.025,.088,.055,face=softened(col,.91),edge=softened(col,.55),roundness=.007)
        figtext(fig,.705,y,domain,size=19,color=col,ha='center',math=True)
        ar=FancyArrowPatch((.755,y),(.847,y),transform=fig.transFigure,
                           arrowstyle='-|>',mutation_scale=13,linewidth=1.65,color=col)
        fig.add_artist(ar)
        figtext(fig,.802,y+.018,mapping,size=13.8,color=col,ha='center',math=True)
        figtext(fig,.856,y,codomain,size=16,color=col,math=True)
    figtext(fig,.661,.473,'All three coordinate spaces are separate, not nested.',size=11.7,color=muted)

    # Right lower: place spectral labels on the correct coordinate spaces.
    figtext(fig,.659,.393,'3   Projection and spectral labels',size=17.5,weight='bold')
    figtext(fig,.660,.349,r'$P_{\mathrm{ex}}=F_0F_0^*\;:\;E\to E$',size=16,color=color['dkwantedprojection'],math=True)
    figtext(fig,.660,.310,r'$I-P_{\mathrm{ex}}=F_1F_1^*$',size=15.5,color=unwanted,math=True)
    figtext(fig,.660,.257,r'$\Lambda_0:F_{\mathrm{ex}}\to F_{\mathrm{ex}}\qquad\lambda_0\in\sigma(\Lambda_0)$',size=14.2,color=color['dkwantedspectrum'],math=True)
    figtext(fig,.660,.216,r'$\Lambda_1:G\to G\qquad\lambda_1\in\sigma(\Lambda_1)$',size=14.2,color=color['dkunwantedspectrum'],math=True)
    figtext(fig,.660,.175,r'$A_0:F\to F$   (trial-coordinate operator)',size=13.2,color=trial,math=True)

    # The conceptual equation is deliberately at full size in a separate line.
    figtext(fig,.053,.110,'One trial vector',size=15,weight='bold')
    figtext(fig,.054,.073,'Two exact components inside the same E.',size=12,color=muted)
    figtext(fig,.392,.081,r'$E_0x\;=\;F_0(F_0^*E_0x)\;+\;F_1(F_1^*E_0x)$',size=20.5,math=True)

    return fig


def audit_text_layout(fig) -> None:
    """Reject off-canvas text and overlapping labels in any one text layer.

    Annotation arrows and plane fills are allowed to meet their labels. The
    annotation boxes, title/footer, and geometric labels are each individually
    checked after exact STIX/mathtext glyph extents are known to Matplotlib.
    """
    fig.canvas.draw()
    renderer = fig.canvas.get_renderer()
    canvas = fig.bbox
    for layer in [fig.texts, *(ax.texts for ax in fig.axes)]:
        for i, a in enumerate(layer):
            aa = a.get_window_extent(renderer=renderer)
            if not canvas.contains(aa.x0, aa.y0) or not canvas.contains(aa.x1, aa.y1):
                raise AssertionError(f"Text outside canvas: {a.get_text()}")
            for b in layer[i+1:]:
                bb = b.get_window_extent(renderer=renderer)
                if aa.overlaps(bb):
                    raise AssertionError(f"Text collision: {a.get_text()!r} / {b.get_text()!r}")


def render(*, check_only=False, png=False):
    vals=check_model()
    colors=paper_palette()
    fig=build_figure(colors)
    audit_text_layout(fig)
    if check_only:
        plt.close(fig)
        print(f"OK: exact decomposition, isometric frames, spectral blocks; trial angle {vals['trial_angle_deg']} degrees")
        print(f"OK: journal palette and text-layout bounding boxes")
        return
    fig.savefig(SVG_OUT,format='svg',bbox_inches=None,metadata={'Date':None})
    if png:
        fig.savefig(PNG_OUT,format='png',dpi=160,bbox_inches=None)
    plt.close(fig)
    print('Wrote',SVG_OUT)
    if png:
        print('Wrote',PNG_OUT)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true',help='check exact linear algebra and paper palette; do not draw')
    parser.add_argument('--png',action='store_true',help='also write a local PNG preview (not intended for Git)')
    args=parser.parse_args()
    render(check_only=args.check,png=args.png)
