#!/usr/bin/env python3
"""Vector teaching figures using the numerical models shared with Manim.

The rank-one construction combines S05Residual with the exact-coordinate
component geometry of S08Why. The graph example is shared with N08MatchingGraph.
"""
from pathlib import Path
import sys

import matplotlib
matplotlib.use('pgf')
import matplotlib.pyplot as plt
from matplotlib.patches import Arc, Circle, FancyArrowPatch, Rectangle
import numpy as np

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'visualizations'))
from dkvis import sine_theta_story as story
from dkvis.novelty_math import nuclear_matching_graph_example
from dkvis.palette import LIGHT
from figure_style import configure, save

OUT = Path(__file__).resolve().parents[1] / 'figures'
FG, MUTED, GUIDE = (LIGHT[key] for key in ('FG', 'MUTED', 'FAINT'))
TRIAL, WANTED, SINE = (LIGHT[key] for key in ('TRIAL', 'WANTED', 'SINE'))
RESIDUAL, GAP, COST = (LIGHT[key] for key in ('RESID', 'GAP', 'CURRENT'))
UNWANTED = LIGHT['UNWANTED']


def arrow(ax, start, end, color, width=2.5):
    ax.add_patch(FancyArrowPatch(start, end, arrowstyle='-|>', mutation_scale=14,
                                color=color, linewidth=width, shrinkA=0, shrinkB=0))


def sine_theta():
    # The actual S05Residual data and its initial 40-degree trial direction.
    ex = story.TwoDirections(*story.RESIDUAL_EIGENVALUES, np.radians(40))
    ex.verify()
    model = ex.model
    v, pv = model.v, np.array([model.v[0], 0.0])
    fig = plt.figure(figsize=(12.4, 4.8), facecolor='white')
    fig.text(.25, .94, '(a) Subspace error', ha='center', fontsize=21, color=FG)
    fig.text(.75, .94, '(b) Residual triangle', ha='center', fontsize=21, color=FG)
    fig.add_artist(plt.Line2D([.5, .5], [.10, .89], transform=fig.transFigure,
                             color=GUIDE, lw=1))
    axes = []
    for box in [[.055, .08, .415, .78], [.55, .08, .415, .78]]:
        ax = fig.add_axes(box)
        # Identical scales in both panels: vector lengths are comparable.
        ax.set(xlim=(-.18, 1.85), ylim=(-.16, 1.20), aspect='equal')
        ax.axis('off')
        ax.plot([-.10, 1.72], [0, 0], color=WANTED, lw=1.2)
        ax.plot([0, 0], [0, 1.06], color=UNWANTED, lw=1.2)
        ax.text(.04, 1.10, r'$\mathrm{range}(\sym{F1})$', fontsize=17, color=FG)
        ax.text(1.72, -.13, r'$\mathrm{range}(\sym{F0})$', fontsize=17,
                color=FG, ha='right')
        axes.append(ax)

    ax = axes[0]
    arrow(ax, (0, 0), v, TRIAL)
    arrow(ax, (0, 0), pv, WANTED)
    arrow(ax, pv, v, SINE, 3)
    ax.add_patch(Arc((0, 0), .53, .53, theta1=0, theta2=40, color=SINE, lw=1.5))
    ax.text(.29, .075, r'$\sym{theta}$', fontsize=22, color=FG)
    ax.text(.44, .78, r'$\sym{v}=\sym{E0}(1)$', fontsize=21, color=FG, ha='center')
    ax.text(.41, -.13, r'$\sym{Pexact}\sym{v}$', fontsize=21, color=FG, ha='center')
    ax.text(.87, .38, r'$\sym{S}(1)$', fontsize=21, color=FG)
    ax.text(.87, .22, r'$\Vert\sym{S}(1)\Vert=\sym{sintheta}$', fontsize=18, color=FG)
    ax.plot([pv[0]-.055, pv[0]-.055, pv[0]], [0, .055, .055], color=GUIDE, lw=1)

    ax = axes[1]
    ax.plot(*np.array([[0, 0], 1.55*v]).T, color=TRIAL, lw=1.2, ls='--', alpha=.65)
    arrow(ax, (0, 0), model.rho_v, TRIAL, 2.8)
    arrow(ax, (0, 0), model.Av, COST, 2.8)
    # The residual is the endpoint-to-endpoint difference, not an origin arrow.
    arrow(ax, model.rho_v, model.Av, RESIDUAL, 3.5)
    corner = np.array([model.Av[0], model.rho_v[1]])
    ax.plot(*np.array([model.rho_v, corner, model.Av]).T,
            color=GUIDE, lw=1.7, ls=(0, (4, 3)), zorder=1)
    # Rayleigh--Ritz makes the residual perpendicular to the trial line.
    toward_origin = -v
    along_residual = model.residual / model.residual_norm
    marker = np.array([model.rho_v+.075*toward_origin,
                       model.rho_v+.075*(toward_origin+along_residual),
                       model.rho_v+.075*along_residual])
    ax.plot(*marker.T, color=MUTED, lw=1)
    ax.text(.93, 1.04, r'$\sym{rho}\,\sym{v}$', fontsize=21, color=FG, ha='center')
    ax.text(1.53, .23, r'$\sym{Acurrent}\sym{v}$', fontsize=21, color=FG, ha='center')
    ax.text(1.20, .64, r'$\sym{r}$', fontsize=24, color=FG, ha='center')
    ax.text(1.31, 1.04, r'$\sym{Pexact}\sym{r}$', fontsize=20, color=FG, ha='center')
    ax.text(1.65, .68, r'$\sym{PexactPerp}\sym{r}$', fontsize=20, color=FG, ha='center')
    save(fig, 'sine_theta_residual_geometry',
         'Rayleigh residual triangle from S05Residual, combined with the exact-coordinate '
         'projection geometry of S08Why. Ahat=diag(1.9,0.7), theta=40 degrees; '
         'the residual joins rho*v to Ahat*v and is perpendicular to the trial line.')


def matching():
    ex = nuclear_matching_graph_example()
    fig = plt.figure(figsize=(12.4, 4.25), facecolor='white')
    ax = fig.add_axes([.025, .09, .46, .86]); ax.axis('off')
    ax.set(xlim=(-.30, 4.9), ylim=(-.8, 3.15), aspect='equal')
    points = np.array([[.55, 2.05], [4.05, 2.05], [2.30, -.05]])
    label_pos = {(0, 1):(2.30, 2.21), (0, 2):(.78, .89), (1, 2):(3.90, .89)}
    for (i,j), gain in ex['savings'].items():
        chosen = (i,j) in ex['pairs']
        ax.plot(*points[[i,j]].T, color=COST if chosen else GUIDE,
                linewidth=4 if chosen else 2, linestyle='-' if chosen else '--', zorder=1)
        ax.text(*label_pos[(i,j)], rf'$\like{{MatchingSaving}}{{{gain:+.4f}}}$', ha='center', va='center',
                fontsize=19, color=COST if chosen else MUTED,
                bbox={'facecolor':'white','edgecolor':'none','pad':3}, zorder=4)
    for i, ((x,y), theta, single) in enumerate(zip(points, ex['angles_deg'], ex['singleton_costs'])):
        ax.add_patch(Circle((x,y), .105, facecolor='white', edgecolor=SINE, lw=2.4, zorder=3))
        top = i < 2
        ax.text(x, y+(.61 if top else -.36), rf'$\like{{theta}}{{\theta_{i+1}}}={theta:.0f}^\circ$',
                ha='center', va='center', fontsize=20, color=SINE)
        ax.text(x, y+(.31 if top else -.68), rf'$\like{{SingletonCost}}{{s_{i+1}}}={single:.4f}$',
                ha='center', va='center', fontsize=17, color=MUTED)

    table = fig.add_axes([.54, .12, .42, .73]); table.axis('off')
    table.set(xlim=(0,1), ylim=(0,1))
    table.text(.01,.94,r'$\sym{Matching}$',fontsize=17,color=MUTED)
    table.text(.99,.94,r'$\like{TraceCost}{C(M)}$',fontsize=17,color=MUTED,ha='right')
    entries = [(r'$\like{Matching}{\varnothing}$', ex['all_singletons'], False)]
    entries += [(rf'$\like{{Matching}}{{\{{\{{{i+1},{j+1}\}}\}}}}$', ex['all_singletons']-gain,
                 (i,j) in ex['pairs']) for (i,j),gain in ex['savings'].items()]
    for y,(label,value,chosen) in zip([.74,.53,.32,.11],entries):
        if chosen:
            table.add_patch(Rectangle((-.025,y-.085),1.05,.18,color='#EBF1F4',clip_on=False))
        table.text(.02,y,label,fontsize=21,color=COST if chosen else FG,va='center')
        table.text(.99,y,rf'$\like{{TraceCost}}{{{value:.4f}}}$',fontsize=21,color=COST if chosen else FG,ha='right',va='center')
    fig.add_artist(plt.Line2D([.5,.5],[.13,.89],transform=fig.transFigure,color=GUIDE,lw=1))
    save(fig, 'real_nuclear_matching',
         'Three labeled principal angles 30,45,75 degrees. Edge savings, all four feasible matchings, '
         'and the attaining four-dimensional paired block plus two-dimensional singleton reflection.')


def main():
    configure()
    (OUT.parent / 'build').mkdir(exist_ok=True)
    sine_theta()
    matching()


if __name__ == '__main__':
    main()
