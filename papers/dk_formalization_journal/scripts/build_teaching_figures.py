#!/usr/bin/env python3
"""Vector teaching figures using the numerical models shared with Manim.

The rank-one construction follows S08Why/S10Sharp without changing those
preserved scenes. The graph example is shared with N08MatchingGraph.
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
from dkvis.sine_theta import SineThetaModel
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
    model = SineThetaModel.from_degrees(35, delta=1.3)
    model.verify()
    v, pv = model.trial_vector, model.desired_projection
    fig = plt.figure(figsize=(12.4, 5.7), facecolor='white')
    fig.text(.245, .94, '(a) Project the trial vector', ha='center', fontsize=20, color=FG)
    fig.text(.75, .94, '(b) Scale the unwanted component', ha='center', fontsize=20, color=FG)
    fig.add_artist(plt.Line2D([.5, .5], [.26, .89], transform=fig.transFigure, color=GUIDE, lw=1))
    ax = fig.add_axes([.055, .29, .405, .57])
    ax.set(xlim=(-.16, 1.3), ylim=(-.19, 1.02), aspect='equal')
    ax.axis('off')
    ax.plot([-.1, 1.2], [0, 0], color=WANTED, lw=1.3)
    ax.plot([0, 0], [0, .93], color=UNWANTED, lw=1.3)
    ax.add_patch(Arc((0, 0), 2, 2, theta1=0, theta2=90, color=GUIDE, lw=1))
    arrow(ax, (0, 0), v, TRIAL)
    arrow(ax, (0, 0), pv, WANTED)
    arrow(ax, pv, v, SINE, 3)
    ax.add_patch(Arc((0, 0), .52, .52, theta1=0, theta2=35, color=SINE, lw=1.6))
    ax.text(.29, .075, r'$\sym{theta}$', fontsize=21, color=SINE)
    ax.text(.40, .52, r'$\like{v}{v_\theta}=\sym{E0}(1)$', fontsize=18, color=TRIAL, ha='center')
    ax.text(.48, -.12, r'$\sym{Pexact}\like{v}{v_\theta}$', fontsize=18, color=WANTED, ha='center')
    ax.text(.86, .28, r'$\sym{S}(1)$', fontsize=19, color=SINE)
    ax.text(.86, .17, r'$\Vert\sym{S}(1)\Vert=\sym{sintheta}$', fontsize=16, color=SINE)
    ax.text(.05, .90, r'$\mathrm{range}(\sym{F1})$', fontsize=16, color=UNWANTED)
    ax.text(1.26, -.12, r'$\mathrm{range}(\sym{F0})$', fontsize=16, color=WANTED, ha='right')
    ax.plot([pv[0]-.055, pv[0]-.055, pv[0]], [.0, .055, .055], color=GUIDE, lw=1)

    fig.text(.75, .85, r'$\sym{Acurrent}=\mathrm{diag}(0,\sym{delta}),\quad\sym{A0}=0$',
             fontsize=19, ha='center', color=FG)
    spec = fig.add_axes([.60, .68, .30, .10])
    spec.set(xlim=(-.2, 1.5), ylim=(-.40, .4)); spec.axis('off')
    spec.plot([-.12, 1.42], [0, 0], color=GUIDE, lw=1.6)
    spec.plot(0, 0, 'o', color=TRIAL, markersize=7)
    spec.plot(1.3, 0, 'o', color=GAP, markersize=7)
    spec.text(0, -.16, r'$\sym{A0}:0$', ha='center', va='top', fontsize=16, color=TRIAL)
    spec.text(1.3, -.16, r'$\sym{Lambda1}:\sym{delta}$', ha='center', va='top', fontsize=16, color=GAP)
    spec.annotate('', (0, .25), (1.3, .25), arrowprops={'arrowstyle':'|-|','color':GAP})
    spec.text(.65, .28, r'gap $\sym{delta}$', ha='center', va='bottom', fontsize=16, color=GAP)
    ax = fig.add_axes([.57, .29, .37, .31])
    ax.set(xlim=(-.25, 1.75), ylim=(-.16, .91), aspect='equal'); ax.axis('off')
    arrow(ax, (0, 0), (0, model.sin_theta), SINE, 3)
    arrow(ax, (.95, 0), (.95, model.residual_norm), RESIDUAL, 3)
    ax.text(-.06, -.10, r'$\sym{S}(1)$', color=SINE, fontsize=18, ha='center')
    ax.text(1.0, -.10, r'$\sym{R}(1)$', color=RESIDUAL, fontsize=18, ha='center')
    ax.text(.08, .29, r'$\sym{sintheta}$', color=SINE, fontsize=17)
    ax.text(1.03, .40, r'$\sym{delta}\sym{sintheta}$', color=RESIDUAL, fontsize=17)
    ax.annotate(r'$\times\sym{delta}$', (.87, .65), (.16, .65), fontsize=18, ha='left', color=GAP,
                arrowprops={'arrowstyle':'->','color':GAP, 'connectionstyle':'arc3,rad=-.25'})
    fig.text(.5, .18, r'$\sym{E0}:\mathbb{R}\to\mathbb{R}^2,\ x\mapsto x\like{v}{v_\theta}'
             r'\qquad\sym{S}:\mathbb{R}\to\mathbb{R}^2,\ x\mapsto(0,x\sym{sintheta})$',
             ha='center', fontsize=18, color=FG)
    fig.text(.5, .085, r'$\sym{sinTheta0}:\mathbb{R}\to\mathbb{R},\ x\mapsto x\sym{sintheta}'
             r'\qquad\sym{delta}\Vert\sym{sinTheta0}\Vert_{\mathrm{op}}=\Vert\sym{R}\Vert_{\mathrm{op}}$',
             ha='center', fontsize=18, color=FG)
    save(fig, 'sine_theta_residual_geometry',
         'Rank-one sine-theta equality example: trial frame, exact projection, complementary error, '
         'certified spectral gap, residual, and the two sine-operator carriers. Theta=35 degrees, delta=1.3.')


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
