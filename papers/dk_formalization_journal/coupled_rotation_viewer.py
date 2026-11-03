#!/usr/bin/env python3
"""Two transporters, one target plane: interactive browser view + paper export.

Interactive (stdlib only; opens a self-contained local HTML application):
    python3 coupled_rotation_viewer.py

Publication-quality vector figure (requires numpy and matplotlib):
    python3 coupled_rotation_viewer.py --export-figure comparison.svg --theta 45
    python3 coupled_rotation_viewer.py --export-figure comparison.pdf --theta 45

Test the mathematics (requires numpy):
    python3 coupled_rotation_viewer.py --self-test

Coordinates are (x,y,z,t), with t treated as a FOURTH EUCLIDEAN coordinate.
We do not model relativistic time or physically realizable time evolution.

K = span(ex,ey). The direct rotation R(theta) rotates each of the two
principal planes through theta and maps K to L(theta).

The coupled rotation W(theta) rotates M=span(u,v) by 2*theta and fixes
F=span(a,b), where
    u=(ex+ez)/sqrt(2), v=(ey+et)/sqrt(2),
    a=(ex-ez)/sqrt(2), b=(ey-et)/sqrt(2).

Both maps send K to exactly the same target L(theta), at every theta.
R has four displacement singular values 2*sin(theta/2); W has two
2*sin(theta) singular values and two zeros. Thus, for theta>0,
    ||I-W||_1 = 4*sin(theta) < 8*sin(theta/2) = ||I-R||_1.
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path
import sys
import webbrowser


def model(theta_deg: float):
    """Return orthogonal R, W and the source basis, using NumPy."""
    import numpy as np
    theta = math.radians(theta_deg)
    c, s = math.cos(theta), math.sin(theta)
    # Coordinates ordered x,y,z,t. Direct rotation in (x,t) and (y,z).
    direct = np.array([
        [c, 0, 0, -s],
        [0, c, s, 0],
        [0, -s, c, 0],
        [s, 0, 0, c],
    ], dtype=float)
    ex, ey, ez, et = np.eye(4)
    rt2 = math.sqrt(2)
    u = (ex + ez) / rt2
    v = (ey + et) / rt2
    a = (ex - ez) / rt2
    b = (ey - et) / rt2
    frame = np.column_stack([u, v, a, b])
    phi = 2 * theta
    cf, sf = math.cos(phi), math.sin(phi)
    block = np.eye(4)
    block[:2, :2] = [[cf, -sf], [sf, cf]]
    coupled = frame @ block @ frame.T
    source = np.column_stack([ex, ey])
    return direct, coupled, source


def test_math() -> None:
    import numpy as np
    for theta in np.linspace(0, 90, 181):
        direct, coupled, source = model(theta)
        dr, dw = direct @ source, coupled @ source
        eye = np.eye(4)
        assert np.allclose(direct.T @ direct, eye, atol=2e-14)
        assert np.allclose(coupled.T @ coupled, eye, atol=2e-14)
        assert np.allclose(dr @ dr.T, dw @ dw.T, atol=2e-14), theta
        assert np.allclose(dr.T @ dr, np.eye(2), atol=2e-14)
        assert np.allclose(dw.T @ dw, np.eye(2), atol=2e-14)
        theta_rad = math.radians(theta)
        principal_cosines = np.linalg.svd(source.T @ dr, compute_uv=False)
        assert np.allclose(principal_cosines, [math.cos(theta_rad)]*2, atol=1e-12)
        sd = np.linalg.svd(eye-direct, compute_uv=False)
        sw = np.linalg.svd(eye-coupled, compute_uv=False)
        assert np.allclose(sd, [2*math.sin(theta_rad/2)]*4, atol=1e-12)
        assert np.allclose(sw, [2*math.sin(theta_rad)]*2 + [0,0], atol=1e-12)
        assert np.isclose(sum(sd), 8*math.sin(theta_rad/2), atol=1e-12)
        assert np.isclose(sum(sw), 4*math.sin(theta_rad), atol=1e-12)
        assert np.isclose(np.linalg.det(direct), 1.0)
        assert np.isclose(np.linalg.det(coupled), 1.0)
        if theta > 0:
            assert sum(sw) < sum(sd)
    print('PASS: 181 angles; orthogonality, common target, principal angles,')
    print('      displacement singular values, costs, and determinants.')


def export_paper_figure(destination: Path, theta_deg: float, *, dpi: int = 240) -> None:
    """Create an editable vector PDF/SVG (or high-res PNG) for LaTeX inclusion.

    The figure shows the 3D spatial projection of a 4D unit disk, so the
    plotted shape is a projection, NOT a physical t=constant cross section.
    """
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    import numpy as np
    from matplotlib.patches import Polygon
    from matplotlib.lines import Line2D

    destination = destination.expanduser().resolve()
    if destination.suffix.lower() not in ('.svg', '.pdf', '.png'):
        raise ValueError('Figure filename must end in .svg, .pdf, or .png')
    direct, coupled, source = model(theta_deg)
    bases = (direct @ source, coupled @ source)
    t = math.radians(theta_deg)
    direct_s = 2*math.sin(t/2)
    coupled_s = 2*math.sin(t)
    direct_cost = 4*direct_s
    coupled_cost = 2*coupled_s

    slate, ghost, outline = '#1F3046', '#B5BECA', '#D9E2EB'
    accents = ('#376EAF', '#168E86')
    source_colors = ('#E48D31', '#9B64B8')
    yaw, elev = math.radians(20), math.radians(-35)

    def project(p):
        x,y,z = p[:3]
        return np.array([
            math.cos(yaw)*x + math.sin(yaw)*y,
            -math.sin(yaw)*math.sin(elev)*x
            + math.cos(yaw)*math.sin(elev)*y + math.cos(elev)*z
        ])

    ring = np.linspace(0, 2*math.pi, 192, endpoint=False)
    circle = np.column_stack([np.cos(ring), np.sin(ring)])
    fig = plt.figure(figsize=(12.0, 7.35), facecolor='white')
    grid = fig.add_gridspec(2, 2, height_ratios=[1.18, 0.79],
                           left=.065, right=.975, top=.824, bottom=.145,
                           wspace=.19, hspace=.36)
    fig.suptitle('Two orthogonal transports of the same two-plane',
                 fontsize=17, fontweight='bold', color=slate, x=.5, y=.981)
    fig.text(.5, .918,
             f'Principal angles: both {theta_deg:g} degrees. '
             'The transported plane is identical; the pointwise maps differ.',
             ha='center', va='center', fontsize=10.3, color='#56657A')

    for index, (basis, name, color) in enumerate(zip(
        bases, ('(a)  Direct rotation R', '(b)  Diagonal coupled rotation W'), accents
    )):
        ax = fig.add_subplot(grid[0,index]); ax.set_aspect('equal')
        ax.set_xlim(-1.53,1.53); ax.set_ylim(-1.4,1.4)
        ax.set_facecolor('#FBFCFE')
        for spine in ax.spines.values(): spine.set_visible(False)
        ax.set_xticks([]); ax.set_yticks([])
        ax.set_title(name, loc='left', fontsize=13.1, color=slate, pad=12,
                     fontweight='bold')
        for coord, name_axis in zip(np.eye(3)*1.12, 'xyz'):
            start = project(-coord); end = project(coord)
            ax.plot([start[0],end[0]],[start[1],end[1]],
                    color='#E0E6EF', lw=1.0, zorder=0)
            ax.text(*(project(coord*1.12)+np.array([.05,.05])), name_axis,
                    fontsize=9, color='#98A6B9')
        orig = (circle @ source.T)
        orig2 = np.array([project(v) for v in orig])
        ax.add_patch(Polygon(orig2, closed=True, facecolor=ghost, alpha=.085,
                             edgecolor=ghost, linewidth=1.0, linestyle='--', zorder=1))
        pts = circle @ basis.T
        uv = np.array([project(v) for v in pts])
        ax.add_patch(Polygon(uv, closed=True, facecolor=color, alpha=.10,
                             edgecolor=color, linewidth=2.2, zorder=2))
        # A grid attached to the SOURCE basis is not the same for R and W.
        # It reveals pointwise differences even when the target disk coincides.
        for h in np.linspace(-.8,.8,7):
            spread = math.sqrt(1-h*h)
            for params in (
                np.column_stack([np.full(24,h), np.linspace(-spread,spread,24)]),
                np.column_stack([np.linspace(-spread,spread,24), np.full(24,h)]),
            ):
                visible = np.array([project(v) for v in params @ basis.T])
                ax.plot(visible[:,0],visible[:,1],color=color,alpha=.34,lw=.84,zorder=3)
        for col,arrow_color,label in zip(range(2),source_colors,('e1','e2')):
            p = project(basis[:,col]); q = project(source[:,col])
            ax.plot([q[0],p[0]],[q[1],p[1]], color=arrow_color,alpha=.33,
                    linestyle='--',lw=1.3,zorder=4)
            ax.annotate('',xy=p,xytext=(0,0),
                        arrowprops={'arrowstyle':'-|>','mutation_scale':14,
                                    'lw':2.3,'color':arrow_color}, zorder=6)
            ax.text(*(p+np.array([.06,.06])),label,fontsize=10.7,
                    color=arrow_color,weight='bold',zorder=7)
        description = (f'Two principal planes rotate by {theta_deg:g} degrees'
                       if index == 0 else
                       f'One diagonal plane rotates by {2*theta_deg:g} degrees; '
                       'the other is fixed')
        ax.text(.025,.02,description,transform=ax.transAxes,va='bottom',
                color='#65748A',fontsize=9.0)

    ax = fig.add_subplot(grid[1,:])
    ax.set_title('(c)  Displacement singular values of the ambient maps',
                 loc='left',fontsize=12.2,fontweight='bold',color=slate,pad=13)
    xx = np.arange(4)
    ax.bar(xx-.19,[direct_s]*4,width=.34,color=accents[0],label='Direct R')
    ax.bar(xx+.19,[coupled_s]*2+[0,0],width=.34,color=accents[1],label='Coupled W')
    ax.set_ylim(0,max(2.12,2.1*max(direct_s,coupled_s)))
    ax.set_yticks([0, .5, 1, 1.5, 2])
    ax.set_xticks(xx,['s1','s2','s3','s4'])
    ax.set_ylabel('Singular value',fontsize=10,color=slate)
    ax.grid(axis='y',color=outline,alpha=.8,lw=.8)
    ax.set_axisbelow(True)
    for sp in ('top','right'): ax.spines[sp].set_visible(False)
    ax.spines['left'].set_color(outline); ax.spines['bottom'].set_color(outline)
    ax.tick_params(colors='#526377')
    ax.legend(frameon=False, loc='upper right')
    ax.text(.02,.92,
            f'Trace costs: direct {direct_cost:.3f}; coupled {coupled_cost:.3f}',
            transform=ax.transAxes,fontsize=10.0,color=slate,va='top',
            bbox={'facecolor':'white','edgecolor':'none','alpha':.8,'pad':3})
    fig.text(.065,.047,
             'Source K = span(e_x, e_y).  Panels (a) and (b) project a unit disk '
             'from 4D to x-y-z; fourth-coordinate t is hidden.\n'
             'Orange/purple arrows track images of the SAME input basis vectors. '
             'Both maps have the same image L.  Cost = nuclear norm of I minus transporter.',
             color='#546477',fontsize=9.2,va='bottom')
    destination.parent.mkdir(parents=True,exist_ok=True)
    fig.savefig(destination,dpi=dpi,facecolor='white',metadata={'Creator':'DKPS transport viewer'})
    plt.close(fig)
    print(f'Wrote paper-ready figure: {destination}')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--self-test', action='store_true', help='Check geometry numerically.')
    parser.add_argument('--export-figure', type=Path, metavar='FILE',
                        help='Save paper-ready comparison as PDF, SVG, or PNG.')
    parser.add_argument('--theta', type=float, default=45.,
                        help='Principal angle in degrees (0..90), default 45.')
    parser.add_argument('--angle', type=float, default=None,
                        help='Previous viewer compatibility: coupled rotation angle = 2*theta.')
    parser.add_argument('--time', type=float, default=0.,
                        help='Initial Euclidean time slice (-1.1..1.1), default 0.')
    parser.add_argument('--save-preview', type=Path, default=None,
                        help='Compatibility alias for static --export-figure (PNG/SVG/PDF).')
    parser.add_argument('--no-open', action='store_true',
                        help='Print local HTML URL rather than opening the browser.')
    args = parser.parse_args()
    if args.angle is not None:
        args.theta = args.angle / 2.0
    if not 0 <= args.theta <= 90:
        parser.error('--theta must be between 0 and 90 degrees')
    if not -1.1 <= args.time <= 1.1:
        parser.error('--time must be between -1.1 and 1.1')
    if args.save_preview is not None and args.export_figure is not None:
        parser.error('use either --save-preview or --export-figure')
    if args.self_test:
        test_math()
        return
    export_path = args.export_figure or args.save_preview
    if export_path is not None:
        export_paper_figure(export_path,args.theta)
        return
    html_file = Path(__file__).with_name('coupled_rotation_explorer.html').resolve()
    if not html_file.exists():
        parser.error(f'Companion HTML not found: {html_file}. Install both files from the ZIP.')
    url = html_file.as_uri() + f'?theta={args.theta:g}&time={args.time:g}'
    print('Interactive viewer:', url)
    if not args.no_open:
        if not webbrowser.open(url):
            print('Open that URL in your browser to use the viewer.')


if __name__ == '__main__':
    main()
