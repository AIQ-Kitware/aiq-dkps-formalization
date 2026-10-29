#!/usr/bin/env python3
"""Render the Proposition 4.4 diagram with live LaTeX labels and vector exports.

Geometry and singular values come from the existing Prop44Model. The four
circles use different invariant-plane coordinates, not one projection of R^4.
"""
from __future__ import annotations

import math
from pathlib import Path
import sys

import matplotlib
matplotlib.use('pgf')
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch
from matplotlib.path import Path as MplPath
import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT / 'visualizations'))
from dkvis.prop44 import Prop44Model
from figure_style import configure, save

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
        ax.text(0.18, -0.30, r'$(I-\sym{Wcompetitor})\like{FigureInput}{z}=0$', color=DISPLACEMENT, fontsize=16)
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
        ax.text(j, value + .055, positive_label if value > 1e-10 else r'$\like{DisplacementSingular}{0}$',
                ha='center', va='bottom', color=DISPLACEMENT, fontsize=17)
    ax.set_xlim(-.55, 3.55)
    ax.set_ylim(0, 1.72)
    ax.set_xticks(x, [rf'$\like{{DisplacementSingular}}{{s_{j+1}}}$' for j in x], fontsize=15)
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
    configure()
    model = Prop44Model()
    model.verify()
    a = model.direct_singular_values[0]
    b = model.competitor_singular_values[0]
    fig = plt.figure(figsize=(12.4, 8.0), facecolor='white')
    fig.text(.5, .964, r'$\sym{Usource}=\mathrm{span}\{e_0,e_1\},\quad\sym{Vtarget}=\sym{Rrotation}(\sym{Usource})=\sym{Wcompetitor}(\sym{Usource}),\quad '
             r'\like{theta}{\theta_1}=\like{theta}{\theta_2}=45^\circ$', ha='center', fontsize=18, color=FG)
    fig.text(.25, .900, r'Direct rotation $\sym{Rrotation}$', ha='center', fontsize=22, color=ROTATION)
    fig.text(.75, .900, r'Competitor $\sym{Wcompetitor}$', ha='center', fontsize=22, color=COMPETITOR)
    fig.text(.25, .861, r'$\sym{CounterPrincipalOne}\oplus\sym{CounterPrincipalTwo}=\mathbb{R}^4$  (principal planes)',
             ha='center', fontsize=16, color=MUTED)
    fig.text(.75, .861, r'$\sym{CounterMovingPlane}\oplus\sym{CounterFixedPlane}=\mathbb{R}^4$  (moving and fixed planes)',
             ha='center', fontsize=16, color=MUTED)
    fig.add_artist(plt.Line2D([.5, .5], [.065, .92], transform=fig.transFigure,
                             color=GUIDE, linewidth=1))

    centers = [.135, .375, .635, .875]
    headings = [r'$\sym{CounterPrincipalOne}=\mathrm{span}\{e_0,e_3\}$',
                r'$\sym{CounterPrincipalTwo}=\mathrm{span}\{e_1,e_2\}$',
                r'$\sym{CounterMovingPlane}=\mathrm{range}(\sym{Wcompetitor}-I)$', r'$\sym{CounterFixedPlane}=\mathrm{ker}(\sym{Wcompetitor}-I)$']
    for center, heading in zip(centers, headings):
        fig.text(center, .810, heading, ha='center', fontsize=16, color=FG)
    boxes = [(center - .116, .510, .232, .285) for center in centers]
    plane(fig, boxes[0], model.R, model.direct_plane_bases[0],
          source_label=r'$\like{SourceVector}{u_1}$', image_label=r'$\like{FigureImage}{Ru_1}$', length_label=r'$\sym{CounterChordA}$', source_color=SOURCE)
    plane(fig, boxes[1], model.R, model.direct_plane_bases[1],
          source_label=r'$\like{SourceVector}{u_2}$', image_label=r'$\like{FigureImage}{Ru_2}$', length_label=r'$\sym{CounterChordA}$', source_color=SOURCE)
    plane(fig, boxes[2], model.W, model.competitor_plane_bases[0],
          source_label=r'$\like{FigureInput}{x}$', image_label=r'$\like{FigureImage}{Wx}$', length_label=r'$\sym{CounterChordB}$')
    plane(fig, boxes[3], model.W, model.competitor_plane_bases[1],
          source_label=r'$\like{FigureInput}{z}$', image_label=r'$\like{FigureInput}{z}=\like{FigureImage}{Wz}$', length_label=r'$\like{DisplacementVector}{0}$', fixed=True)
    rotations = [r'$\like{PlaneRotationAngle}{+45^\circ}$', r'$\like{PlaneRotationAngle}{-45^\circ}$', r'$\like{PlaneRotationAngle}{+90^\circ}$', r'$\like{PlaneRotationAngle}{0^\circ}$ (fixed)']
    for center, rotation in zip(centers, rotations):
        fig.text(center, .492, rotation, ha='center', fontsize=18, color=ANGLE)

    # Common legend: arrow styles also distinguish the roles in monochrome.
    for x, color, style, label in [(.09, MUTED, '--', r'Unit input $\sym{FigureInput}$'),
                                  (.36, TARGET, '-', r'Image $\sym{FigureImage}$'),
                                  (.70, DISPLACEMENT, '-', r'Displacement $\sym{DisplacementVector}$')]:
        fig.add_artist(FancyArrowPatch((x-.045, .444), (x-.010, .444),
                       transform=fig.transFigure, arrowstyle='-|>', mutation_scale=11,
                       color=color, linestyle=style, linewidth=2))
        fig.text(x, .444, label, va='center', fontsize=15, color=FG)
    for center, operator in [(.25, 'R'), (.75, 'W')]:
        fig.text(center, .393, rf'Singular values of $I-\sym{{{"Rrotation" if operator == "R" else "Wcompetitor"}}}$',
                 ha='center', fontsize=16, color=FG)
    fig.text(.25, .350, rf'$\sym{{CounterChordA}}=\sqrt{{2-\sqrt{{2}}}}\approx{a:.3f}$',
             ha='center', fontsize=16, color=FG)
    fig.text(.75, .350, rf'$\sym{{CounterChordB}}=\sqrt{{2}}\approx{b:.3f}$',
             ha='center', fontsize=16, color=FG)
    spectrum(fig, [.075, .160, .370, .170], model.direct_singular_values, r'$\sym{CounterChordA}$',
             [r'from $\sym{CounterPrincipalOne}$', r'from $\sym{CounterPrincipalTwo}$'])
    spectrum(fig, [.575, .160, .370, .170], model.competitor_singular_values, r'$\sym{CounterChordB}$',
             [r'from $\sym{CounterMovingPlane}$', r'from $\sym{CounterFixedPlane}$'])
    fig.text(.25, .045, rf'$\Vert I-\sym{{Rrotation}}\Vert_1=4\sym{{CounterChordA}}\approx{model.direct_trace_displacement:.3f}$',
             ha='center', fontsize=21, color=FG)
    fig.text(.50, .045, '$>$', ha='center', fontsize=27, color=FG)
    fig.text(.75, .045, rf'$\Vert I-\sym{{Wcompetitor}}\Vert_1=2\sym{{CounterChordB}}\approx{model.competitor_trace_displacement:.3f}$',
             ha='center', fontsize=21, color=FG)

    save(fig, 'prop44_displacement_planes',
         'Invariant-plane actions, displacement chords, singular values, and trace norms '
         'for the verified real Proposition 4.4 counterexample.')


if __name__ == '__main__':
    main()
