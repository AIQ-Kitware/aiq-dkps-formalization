#!/usr/bin/env python3
"""Vector teaching figures using the numerical models shared with Manim.

The rank-one construction follows S08Why/S10Sharp without changing those
preserved scenes. The graph example is shared with N08MatchingGraph.
"""
from pathlib import Path
import sys

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Arc, Circle, FancyArrowPatch, Rectangle
import numpy as np

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'visualizations'))
from dkvis.sine_theta import SineThetaModel
from dkvis.novelty_math import nuclear_matching_graph_example
from dkvis.palette import LIGHT

OUT = Path(__file__).resolve().parents[1] / 'figures'
FG, MUTED, GUIDE = (LIGHT[key] for key in ('FG', 'MUTED', 'FAINT'))
TRIAL, WANTED, SINE = (LIGHT[key] for key in ('TRIAL', 'WANTED', 'SINE'))
RESIDUAL, GAP, COST = (LIGHT[key] for key in ('RESID', 'GAP', 'CURRENT'))
UNWANTED = LIGHT['UNWANTED']


def arrow(ax, start, end, color, width=2.5):
    ax.add_patch(FancyArrowPatch(start, end, arrowstyle='-|>', mutation_scale=14,
                                color=color, linewidth=width, shrinkA=0, shrinkB=0))


def save(fig, name, description):
    stem = OUT / name
    fig.savefig(stem.with_suffix('.pdf'), metadata={
        'Creator': 'build_teaching_figures.py; checked dkvis numerical models',
        'CreationDate': None, 'ModDate': None})
    fig.savefig(stem.with_suffix('.svg'), metadata={'Date': None, 'Description': description})
    svg = stem.with_suffix('.svg')
    svg.write_text('\n'.join(line.rstrip() for line in svg.read_text().splitlines()) + '\n')
    fig.savefig(OUT.parent / 'build' / f'{name}-preview.png', dpi=140)
    plt.close(fig)
    print(f'Wrote {stem}.pdf and editable SVG')


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
    ax.text(.29, .075, r'$\theta$', fontsize=21, color=SINE)
    ax.text(.40, .52, r'$v_\theta=E_0(1)$', fontsize=18, color=TRIAL, ha='center')
    ax.text(.48, -.12, r'$Pv_\theta$', fontsize=18, color=WANTED, ha='center')
    ax.text(.86, .28, r'$S(1)$', fontsize=19, color=SINE)
    ax.text(.86, .17, r'$\Vert S(1)\Vert=\sin\theta$', fontsize=16, color=SINE)
    ax.text(.05, .90, r'$\mathrm{range}(F_1)$', fontsize=16, color=UNWANTED)
    ax.text(1.26, -.12, r'$\mathrm{range}(F_0)$', fontsize=16, color=WANTED, ha='right')
    ax.plot([pv[0]-.055, pv[0]-.055, pv[0]], [.0, .055, .055], color=GUIDE, lw=1)

    fig.text(.75, .85, r'$\widehat A=\mathrm{diag}(0,\delta),\quad A_0=0$',
             fontsize=19, ha='center', color=FG)
    spec = fig.add_axes([.60, .68, .30, .10])
    spec.set(xlim=(-.2, 1.5), ylim=(-.40, .4)); spec.axis('off')
    spec.plot([-.12, 1.42], [0, 0], color=GUIDE, lw=1.6)
    spec.plot(0, 0, 'o', color=TRIAL, markersize=7)
    spec.plot(1.3, 0, 'o', color=GAP, markersize=7)
    spec.text(0, -.16, r'$A_0:0$', ha='center', va='top', fontsize=16, color=TRIAL)
    spec.text(1.3, -.16, r'$\Lambda_1:\delta$', ha='center', va='top', fontsize=16, color=GAP)
    spec.annotate('', (0, .25), (1.3, .25), arrowprops={'arrowstyle':'|-|','color':GAP})
    spec.text(.65, .28, r'gap $\delta$', ha='center', va='bottom', fontsize=16, color=GAP)
    ax = fig.add_axes([.57, .29, .37, .31])
    ax.set(xlim=(-.25, 1.75), ylim=(-.16, .91), aspect='equal'); ax.axis('off')
    arrow(ax, (0, 0), (0, model.sin_theta), SINE, 3)
    arrow(ax, (.95, 0), (.95, model.residual_norm), RESIDUAL, 3)
    ax.text(-.06, -.10, r'$S(1)$', color=SINE, fontsize=18, ha='center')
    ax.text(1.0, -.10, r'$R(1)$', color=RESIDUAL, fontsize=18, ha='center')
    ax.text(.08, .29, r'$\sin\theta$', color=SINE, fontsize=17)
    ax.text(1.03, .40, r'$\delta\sin\theta$', color=RESIDUAL, fontsize=17)
    ax.annotate(r'$\times\delta$', (.87, .65), (.16, .65), fontsize=18, ha='left', color=GAP,
                arrowprops={'arrowstyle':'->','color':GAP, 'connectionstyle':'arc3,rad=-.25'})
    fig.text(.5, .18, r'$E_0:\mathbb{R}\to\mathbb{R}^2,\ x\mapsto xv_\theta'
             r'\qquad S:\mathbb{R}\to\mathbb{R}^2,\ x\mapsto(0,x\sin\theta)$',
             ha='center', fontsize=18, color=FG)
    fig.text(.5, .085, r'$\sin\Theta_0:\mathbb{R}\to\mathbb{R},\ x\mapsto x\sin\theta'
             r'\qquad\delta\Vert\sin\Theta_0\Vert_{\mathrm{op}}=\Vert R\Vert_{\mathrm{op}}$',
             ha='center', fontsize=18, color=FG)
    save(fig, 'sine_theta_residual_geometry',
         'Rank-one sine-theta equality example: trial frame, exact projection, complementary error, '
         'certified spectral gap, residual, and the two sine-operator carriers. Theta=35 degrees, delta=1.3.')


def matching():
    ex = nuclear_matching_graph_example()
    fig = plt.figure(figsize=(12.4, 6.2), facecolor='white')
    fig.text(.5, .945, r'$C_0=\sum_i s_i,\qquad g_{ij}=s_i+s_j-e_{ij},\qquad'
             r' C(M)=C_0-\sum_{\{i,j\}\in M}g_{ij}$', fontsize=21, ha='center', color=FG)
    fig.text(.245, .85, 'Edge labels are savings '+r'$g_{ij}$', fontsize=19, ha='center', color=FG)
    fig.text(.745, .85, 'Compare every matching', fontsize=19, ha='center', color=FG)
    ax = fig.add_axes([.03, .25, .43, .55]); ax.axis('off')
    ax.set(xlim=(-.30, 4.9), ylim=(-.8, 3.15), aspect='equal')
    points = np.array([[.55, 2.05], [4.05, 2.05], [2.30, -.05]])
    label_pos = {(0, 1):(2.30, 2.21), (0, 2):(.78, .89), (1, 2):(3.90, .89)}
    for (i,j), gain in ex['savings'].items():
        chosen = (i,j) in ex['pairs']
        ax.plot(*points[[i,j]].T, color=COST if chosen else GUIDE,
                linewidth=4 if chosen else 2, linestyle='-' if chosen else '--', zorder=1)
        ax.text(*label_pos[(i,j)], f'{gain:+.4f}', ha='center', va='center',
                fontsize=19, color=COST if chosen else MUTED,
                bbox={'facecolor':'white','edgecolor':'none','pad':3}, zorder=4)
    for i, ((x,y), theta, single) in enumerate(zip(points, ex['angles_deg'], ex['singleton_costs'])):
        ax.add_patch(Circle((x,y), .105, facecolor='white', edgecolor=SINE, lw=2.4, zorder=3))
        top = i < 2
        ax.text(x, y+(.61 if top else -.36), rf'$\theta_{i+1}={theta:.0f}^\circ$',
                ha='center', va='center', fontsize=20, color=SINE)
        ax.text(x, y+(.31 if top else -.68), rf'$s_{i+1}={single:.4f}$',
                ha='center', va='center', fontsize=17, color=MUTED)
    ax.text(2.30, .25, 'unmatched', ha='center', fontsize=15, color=MUTED)

    table = fig.add_axes([.53, .30, .43, .48]); table.axis('off')
    table.set(xlim=(0,1), ylim=(0,1))
    table.text(.01,.94,'Selected edges',fontsize=17,color=MUTED)
    table.text(.99,.94,r'Cost $C(M)$',fontsize=17,color=MUTED,ha='right')
    entries = [(r'$\varnothing$', ex['all_singletons'], False)]
    entries += [(rf'$\{{\{{{i+1},{j+1}\}}\}}$', ex['all_singletons']-gain,
                 (i,j) in ex['pairs']) for (i,j),gain in ex['savings'].items()]
    for y,(label,value,chosen) in zip([.74,.53,.32,.11],entries):
        if chosen:
            table.add_patch(Rectangle((-.025,y-.085),1.05,.18,color='#EBF1F4',clip_on=False))
        table.text(.02,y,label,fontsize=21,color=COST if chosen else FG,va='center')
        table.text(.99,y,f'{value:.4f}',fontsize=21,color=COST if chosen else FG,ha='right',va='center')
    fig.add_artist(plt.Line2D([.5,.5],[.28,.80],transform=fig.transFigure,color=GUIDE,lw=1))
    fig.text(.5,.205,r'Chosen blocks: $W=W_{12}\oplus W_3$ on $\mathbb{R}^4\oplus\mathbb{R}^2$',
             ha='center',fontsize=19,color=FG)
    fig.text(.5,.125,r'$4\sin(37.5^\circ)+2'
             rf'\approx{ex["real_minimum"]:.4f}$',ha='center',fontsize=22,color=COST)
    fig.text(.5,.035,'Choose disjoint edges with maximum total savings; each remaining angle pays its singleton cost.',
             fontsize=16,ha='center',color=MUTED)
    save(fig, 'real_nuclear_matching',
         'Three labeled principal angles 30,45,75 degrees. Edge savings, all four feasible matchings, '
         'and the attaining four-dimensional paired block plus two-dimensional singleton reflection.')


def main():
    plt.rcParams.update({'font.family':'DejaVu Sans','mathtext.fontset':'dejavusans',
                         'svg.fonttype':'none','svg.hashsalt':'dkps-teaching-figures','pdf.fonttype':42})
    (OUT.parent / 'build').mkdir(exist_ok=True)
    sine_theta()
    matching()


if __name__ == '__main__':
    main()
