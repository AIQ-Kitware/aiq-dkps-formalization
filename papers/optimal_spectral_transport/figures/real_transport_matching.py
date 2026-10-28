"""Illustrate the real three-halves transport formula and its matching problem.

The figure evaluates explicit formulas in real_matching_transport.tex.
It is an illustration, not numerical proof evidence.
"""
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap
import numpy as np


def power(theta):
    return (2 * np.sin(theta / 2)) ** 1.5


def single(theta):
    return np.minimum(2 * power(theta), 2 ** 1.5)


def paired(theta, psi):
    h, d = (theta + psi) / 2, (theta - psi) / 2
    c, q = np.cos(h), np.cos(d)
    active = c < q / (1 + 2 * q)
    interior = 2 * np.sqrt(8 * (1 + c) * np.sqrt(np.maximum(0, 1 - 2 * c)))
    return np.where(active, interior, 2 * power(theta) + 2 * power(psi))


plt.rcParams.update(
    {"font.family": "DejaVu Serif", "font.size": 10,
     "axes.spines.top": False, "axes.spines.right": False,
     "pdf.fonttype": 42, "svg.fonttype": "none"}
)
blue, orange, green = "#0072B2", "#D55E00", "#009E73"
fig, axes = plt.subplots(1, 2, figsize=(8.6, 3.5), layout="constrained")

degrees = np.linspace(0, 90, 721)
t, s = np.meshgrid(np.radians(degrees), np.radians(degrees))
canonical = 2 * power(t) + 2 * power(s)
reflection = 2 ** 1.5 + 2 * power(s)
even = paired(t, s)
region = np.zeros(t.shape)
region[reflection < canonical - 1e-10] = 1
region[(even < canonical - 1e-10) & (even < reflection - 1e-10)] = 2
region = np.ma.masked_where(s > t, region)

ax = axes[0]
ax.pcolormesh(degrees, degrees, region,
              cmap=ListedColormap(["#CEE5F2", "#F4D4BF", "#BCE6D8"]),
              vmin=0, vmax=2, shading="nearest", rasterized=True)
ax.plot([0, 90], [0, 90], color="0.45", linewidth=0.8)
critical = np.degrees(np.arccos(1 / 3))
ax.plot([critical, critical], [0, critical], "--", color=blue, linewidth=1)
theta = np.radians(np.linspace(critical, 90, 301))
x = np.sin(theta / 2)
y = (-x + np.sqrt(4 - 3 * x * x)) / 2
ax.plot(np.degrees(theta), np.degrees(2 * np.arcsin(y)),
        color=green, linewidth=1)
cutoff = np.degrees(2 * np.arcsin(2 ** (-2 / 3)))
ax.plot([cutoff, cutoff], [0, cutoff], ":", color=orange, linewidth=1)
ax.text(35, 15, "Canonical", color=blue)
ax.text(81.5, 20, "Reflection", rotation=90, color=orange, ha="center")
ax.annotate("Coupled\nrotation", (84, 81), xytext=(38, 74), color=green,
            ha="center", fontsize=9,
            arrowprops={"arrowstyle": "->", "color": green, "linewidth": 0.8})
ax.plot(80, 75, "o", markersize=3.5, color="black")
ax.set(xlim=(0, 90), ylim=(0, 90), xticks=[0, 30, 60, 90], yticks=[0, 30, 60, 90],
       xlabel=r"Larger angle $\theta_1$ (degrees)",
       ylabel=r"Smaller angle $\theta_2$ (degrees)",
       title=r"(a) Exact real optimum at $p=3/2$")
ax.set_aspect("equal")

ax = axes[1]
angle_degrees = np.array([85, 80, 75, 70, 60, 20])
angles = np.radians(angle_degrees)
positions = np.array([[-1, 0.65], [0, 1], [0.9, 0.45],
                      [0.85, -0.65], [-0.2, -1], [-1.05, -0.4]])
gains = {(i, j): float(single(angles[i]) + single(angles[j])
                       - paired(angles[i], angles[j]))
         for i in range(len(angles)) for j in range(i + 1, len(angles))}


def best_matching(vertices):
    if not vertices:
        return 0.0, []
    i, *rest = vertices
    best = best_matching(rest)
    for j in rest:
        value, edges = best_matching([k for k in rest if k != j])
        candidate = value + gains[i, j]
        if candidate > best[0]:
            best = candidate, [(i, j)] + edges
    return best


gain, matching = best_matching(list(range(len(angles))))
for (i, j), weight in gains.items():
    if weight <= 1e-10:
        continue
    selected = (i, j) in matching
    p, q = positions[i], positions[j]
    ax.plot([p[0], q[0]], [p[1], q[1]], color=green if selected else "0.65",
            linewidth=3 if selected else 1, zorder=1)
    midpoint = (p + q) / 2
    ax.text(*midpoint, f"{weight:.3f}", ha="center", va="center", fontsize=8,
            color=green if selected else "0.4",
            bbox={"facecolor": "white", "edgecolor": "none", "pad": 1})
for i, (p, angle) in enumerate(zip(positions, angle_degrees)):
    chosen = any(i in edge for edge in matching)
    ax.scatter(*p, s=600, facecolor="white", edgecolor=green if chosen else "0.4",
               linewidth=1.5, zorder=3)
    ax.text(*p, rf"${angle}^\circ$", ha="center", va="center", zorder=4)
ax.text(0, -1.5, "Selected pair: 80° and 75°\nRemaining angles use one-plane optima",
        ha="center", va="center", fontsize=9)
ax.set(xlim=(-1.5, 1.5), ylim=(-1.8, 1.4), aspect="equal",
       title="(b) Maximum-weight matching of six angles")
ax.axis("off")

output = Path(__file__).resolve().parent
for extension in ("pdf", "svg"):
    artifact = output / f"real_transport_matching.{extension}"
    fig.savefig(artifact)
    if extension == "svg":
        artifact.write_text("\n".join(line.rstrip() for line in artifact.read_text().splitlines()) + "\n")
