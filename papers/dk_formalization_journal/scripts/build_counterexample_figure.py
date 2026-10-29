#!/usr/bin/env python3
"""Render the manuscript's Proposition 4.4 figure as editable SVG and vector PDF.

Geometry and singular values come from the existing Prop44Model. The four
circles use different invariant-plane coordinates, not one projection of R^4.
"""
from __future__ import annotations

import math
from pathlib import Path
import sys

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch
from matplotlib.path import Path as MplPath
import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT / 'visualizations'))
from dkvis.prop44 import Prop44Model

PAPER_ROOT = Path(__file__).resolve().parents[1]
FG = '#1B1F24'
MUTED = '#6B7280'
GUIDE = '#D5D9DE'
SOURCE = '#A66705'
TARGET = '#1F6FD1'
ANGLE = '#D12A7B'
DISPLACEMENT = '#226C50'
ROTATION = '#4248B0'
COMPETITOR = '#A04D10'


def arrow(ax, start, end, color, *, dashed=False, width=2.0):
    patch = FancyArrowPatch(start, end, arrowstyle='-|>', mutation_scale=12,
                            linewidth=width, color=color,
                            linestyle=(0, (4, 3)) if dashed else '-',
                            shrinkA=0, shrinkB=0, zorder=4)
    ax.add_patch(patch)


def plane(fig, box, operator, basis, *, source_label, image_label, length_label,
          source_color=MUTED, fixed=False):
    ax = fig.add_axes(box)
    ax.set_aspect('equal')
    ax.set_xlim(-1.28, 1.66)
    ax.set_ylim(-1.38, 1.38)
    ax.axis('off')
    local = basis.T @ operator @ basis
    start = np.array([1.0, 0.0])
    end = local @ start
    ax.add_patch(Circle((0, 0), 1, edgecolor=GUIDE, facecolor='none', linewidth=1.4))
    ax.plot(0, 0, 'o', color=MUTED, markersize=2.5)
    arrow(ax, (0, 0), start, source_color, dashed=True, width=2.1)
    arrow(ax, (0, 0), end, TARGET, width=2.0)
    if fixed:
        ax.plot(*start, 'o', color=TARGET, markersize=5, zorder=6)
        ax.text(0.15, 0.17, image_label, color=TARGET, fontsize=17, ha='left')
        ax.text(0.18, -0.30, r'$(I-W)z=0$', color=DISPLACEMENT, fontsize=16)
    else:
        # The chord points from the image back to the input: (I-T)q.
        arrow(ax, end, start, DISPLACEMENT, width=2.7)
        phi = math.atan2(end[1], end[0])
        angles = np.linspace(0, phi, 70)
        arc = np.column_stack([.40 * np.cos(angles), .40 * np.sin(angles)])
        ax.add_patch(FancyArrowPatch(path=MplPath(arc), arrowstyle='-|>',
                                    mutation_scale=10, color=ANGLE, linewidth=1.5))
        ax.text(1.04, -0.23, source_label, color=source_color, fontsize=17, ha='center')
        if phi > 1:
            ax.text(-.13, 1.12, image_label, color=TARGET, fontsize=17, ha='center')
            xy, offset = (.5, .5), (.85, .78)
        elif phi > 0:
            ax.text(.35, 1.08, image_label, color=TARGET, fontsize=17, ha='center')
            xy, offset = (start + end) / 2, (1.32, .57)
        else:
            ax.text(.26, -1.23, image_label, color=TARGET, fontsize=17, ha='center')
            xy, offset = (start + end) / 2, (1.32, -.65)
        ax.annotate(length_label, xy=xy, xytext=offset, color=DISPLACEMENT,
                    fontsize=18, ha='center', va='center',
                    arrowprops=dict(arrowstyle='-', color=DISPLACEMENT, lw=.9))
    return ax


def spectrum(fig, box, values, positive_label, groups):
    ax = fig.add_axes(box)
    x = np.arange(4)
    ax.bar(x, values, width=.56, color=DISPLACEMENT, alpha=.90, zorder=3)
    for j, value in enumerate(values):
        if value < 1e-10:
            ax.plot(j, 0, marker='o', markersize=5, markerfacecolor='white',
                    markeredgecolor=DISPLACEMENT, zorder=5, clip_on=False)
        ax.text(j, value + .055, positive_label if value > 1e-10 else '$0$',
                ha='center', va='bottom', color=DISPLACEMENT, fontsize=17)
    ax.set_xlim(-.55, 3.55)
    ax.set_ylim(0, 1.72)
    ax.set_xticks(x, [rf'$s_{j+1}$' for j in x], fontsize=15)
    ax.set_yticks([0, .5, 1, 1.5], ['0', '0.5', '1.0', '1.5'], fontsize=13)
    ax.tick_params(axis='both', length=0, pad=5, colors=MUTED)
    ax.grid(axis='y', color=GUIDE, linewidth=.6, zorder=0)
    ax.spines[['top', 'right', 'left']].set_visible(False)
    ax.spines['bottom'].set_color(GUIDE)
    for center, label in zip([.5, 2.5], groups):
        ax.text(center, -.30, label, transform=ax.get_xaxis_transform(),
                ha='center', va='top', fontsize=15, color=FG)
    return ax


def main():
    plt.rcParams.update({'font.family': 'DejaVu Sans', 'mathtext.fontset': 'dejavusans',
                         'svg.fonttype': 'none', 'svg.hashsalt': 'dkps-prop44-planes', 'pdf.fonttype': 42})
    model = Prop44Model()
    model.verify()
    a = model.direct_singular_values[0]
    b = model.competitor_singular_values[0]
    fig = plt.figure(figsize=(12.4, 8.0), facecolor='white')
    fig.text(.5, .964, r'$U=\mathrm{span}\{e_0,e_1\},\quad V=R(U)=W(U),\quad '
             r'\theta_1=\theta_2=45^\circ$', ha='center', fontsize=18, color=FG)
    fig.text(.25, .900, r'Direct rotation $R$', ha='center', fontsize=22, color=ROTATION)
    fig.text(.75, .900, r'Competitor $W$', ha='center', fontsize=22, color=COMPETITOR)
    fig.text(.25, .861, r'$\Pi_1\oplus\Pi_2=\mathbb{R}^4$  (principal planes)',
             ha='center', fontsize=16, color=MUTED)
    fig.text(.75, .861, r'$M\oplus Z=\mathbb{R}^4$  (moving and fixed planes)',
             ha='center', fontsize=16, color=MUTED)
    fig.add_artist(plt.Line2D([.5, .5], [.065, .92], transform=fig.transFigure,
                             color=GUIDE, linewidth=1))

    centers = [.135, .375, .635, .875]
    headings = [r'$\Pi_1=\mathrm{span}\{e_0,e_3\}$',
                r'$\Pi_2=\mathrm{span}\{e_1,e_2\}$',
                r'$M=\mathrm{range}(W-I)$', r'$Z=\mathrm{ker}(W-I)$']
    for center, heading in zip(centers, headings):
        fig.text(center, .810, heading, ha='center', fontsize=16, color=FG)
    boxes = [(center - .116, .510, .232, .285) for center in centers]
    plane(fig, boxes[0], model.R, model.direct_plane_bases[0],
          source_label=r'$u_1$', image_label=r'$Ru_1$', length_label='$a$', source_color=SOURCE)
    plane(fig, boxes[1], model.R, model.direct_plane_bases[1],
          source_label=r'$u_2$', image_label=r'$Ru_2$', length_label='$a$', source_color=SOURCE)
    plane(fig, boxes[2], model.W, model.competitor_plane_bases[0],
          source_label='$x$', image_label='$Wx$', length_label='$b$')
    plane(fig, boxes[3], model.W, model.competitor_plane_bases[1],
          source_label='$z$', image_label='$z=Wz$', length_label='$0$', fixed=True)
    rotations = [r'$+45^\circ$', r'$-45^\circ$', r'$+90^\circ$', r'$0^\circ$ (fixed)']
    for center, rotation in zip(centers, rotations):
        fig.text(center, .492, rotation, ha='center', fontsize=18, color=ANGLE)

    # Common legend: arrow styles also distinguish the roles in monochrome.
    for x, color, style, label in [(.09, MUTED, '--', r'Unit input $q$'),
                                  (.36, TARGET, '-', r'Image $Tq$'),
                                  (.70, DISPLACEMENT, '-', r'Displacement $(I-T)q$')]:
        fig.add_artist(FancyArrowPatch((x-.045, .444), (x-.010, .444),
                       transform=fig.transFigure, arrowstyle='-|>', mutation_scale=11,
                       color=color, linestyle=style, linewidth=2))
        fig.text(x, .444, label, va='center', fontsize=15, color=FG)
    for center, operator in [(.25, 'R'), (.75, 'W')]:
        fig.text(center, .393, rf'Singular values of $I-{operator}$',
                 ha='center', fontsize=16, color=FG)
    fig.text(.25, .350, rf'$a=\sqrt{{2-\sqrt{{2}}}}\approx{a:.3f}$',
             ha='center', fontsize=16, color=FG)
    fig.text(.75, .350, rf'$b=\sqrt{{2}}\approx{b:.3f}$',
             ha='center', fontsize=16, color=FG)
    spectrum(fig, [.075, .160, .370, .170], model.direct_singular_values, '$a$',
             [r'from $\Pi_1$', r'from $\Pi_2$'])
    spectrum(fig, [.575, .160, .370, .170], model.competitor_singular_values, '$b$',
             [r'from $M$', r'from $Z$'])
    fig.text(.25, .045, rf'$\Vert I-R\Vert_1=4a\approx{model.direct_trace_displacement:.3f}$',
             ha='center', fontsize=21, color=FG)
    fig.text(.50, .045, '$>$', ha='center', fontsize=27, color=FG)
    fig.text(.75, .045, rf'$\Vert I-W\Vert_1=2b\approx{model.competitor_trace_displacement:.3f}$',
             ha='center', fontsize=21, color=FG)

    output = PAPER_ROOT / 'figures' / 'prop44_displacement_planes'
    metadata = {'Creator': 'build_counterexample_figure.py; geometry from dkvis.prop44.Prop44Model'}
    fig.savefig(output.with_suffix('.pdf'), metadata=metadata | {'CreationDate': None, 'ModDate': None})
    fig.savefig(output.with_suffix('.svg'), metadata={'Creator': metadata['Creator'], 'Date': None,
                'Description': 'Invariant-plane actions, displacement chords, individual singular values, '
                'and trace norms for the verified real Proposition 4.4 counterexample.'})
    svg_path = output.with_suffix('.svg')
    svg_path.write_text('\n'.join(line.rstrip() for line in svg_path.read_text().splitlines()) + '\n')
    plt.close(fig)
    print(f'Wrote {output.with_suffix(".pdf")} and editable SVG')


if __name__ == '__main__':
    main()
