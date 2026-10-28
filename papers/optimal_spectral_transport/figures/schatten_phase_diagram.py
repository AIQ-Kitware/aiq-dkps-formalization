"""Render the scalar phase diagram with NumPy, SciPy, and Matplotlib.

The numerical curves illustrate the results; they are not proof evidence.
"""
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.optimize import brentq


def critical_angle(p):
    return np.arccos((2 - p) / p)


def optimal_phase(p, theta):
    if theta <= critical_angle(p):
        return 0.0
    if p == 1.5:
        c = np.cos(theta)
        return np.arccos(c / (1 - 2 * c))
    eta = np.arccos(p * np.cos(theta) / (2 - p))

    def log_amplitude(t):
        return np.log(np.cos(t / 2)) + (p - 1) * np.log(2 * np.sin(t / 2))

    def balance(delta):
        return log_amplitude(theta + delta) - log_amplitude(theta - delta)

    return brentq(balance, eta, np.nextafter(theta, 0.0), xtol=5e-15, rtol=1e-14)


def power_sum(p, theta, delta):
    return (2 * np.sin((theta + delta) / 2)) ** p + (
        2 * np.sin((theta - delta) / 2)
    ) ** p


plt.rcParams.update(
    {"font.family": "DejaVu Serif", "font.size": 10, "axes.spines.top": False,
     "axes.spines.right": False, "pdf.fonttype": 42, "svg.fonttype": "none"}
)
fig, axes = plt.subplots(1, 3, figsize=(8, 3.1), layout="constrained")
blue, orange, purple = "#0072B2", "#D55E00", "#8A4B9F"
ps = np.linspace(1, 2, 401)
cutoffs = np.degrees(critical_angle(ps))
ax = axes[0]
ax.fill_between(ps, 0, cutoffs, color=blue, alpha=0.13)
ax.fill_between(ps, cutoffs, 90, color=orange, alpha=0.13)
ax.plot(ps, cutoffs, color="black", linewidth=1.4)
ax.text(1.6, 30, "Canonical\nphase optimal", ha="center", color=blue)
ax.text(1.025, 76, "Nonzero phase\nstrictly better", ha="left", color=orange, fontsize=9)
ax.set(xlim=(1, 2), ylim=(0, 90), xlabel=r"Exponent $p$",
       ylabel=r"Principal angle $\theta$ (degrees)", title="(a) Angle cutoff")

ax = axes[1]
fractions = np.linspace(0, 1, 501)
for degrees, color, style in [(60, blue, "-"), (80, orange, "--")]:
    theta = np.radians(degrees)
    costs = power_sum(1.5, theta, fractions * theta) / power_sum(1.5, theta, 0)
    ax.plot(fractions, costs, color=color, linestyle=style, label=rf"$\theta={degrees}^\circ$")
    delta = optimal_phase(1.5, theta)
    ax.plot(delta / theta, power_sum(1.5, theta, delta) / power_sum(1.5, theta, 0),
            "o", color=color, markersize=4)
ax.axhline(1, color="0.6", linewidth=0.7, zorder=0)
ax.set(xlim=(0, 1), xlabel=r"Phase fraction $\delta/\theta$",
       ylabel=r"Power sum $F(\delta)/F(0)$", title=r"(b) Cost at $p=3/2$")
ax.legend(frameon=False)

ax = axes[2]
angles = np.radians(np.linspace(0.1, 89.8, 600))
for p, color, style in [(1.25, blue, "-"), (1.5, orange, "--"), (1.75, purple, "-.")]:
    sample = np.sort(np.append(angles, critical_angle(p)))
    phases = np.array([optimal_phase(p, theta) for theta in sample])
    ax.plot(np.degrees(sample), np.degrees(phases), color=color, linestyle=style,
            label=rf"$p={p:g}$")
ax.plot([0, 90], [0, 90], ":", color="0.65", linewidth=0.8)
ax.set(xlim=(0, 90), ylim=(0, 90), xlabel=r"Principal angle $\theta$ (degrees)",
       ylabel=r"Optimal phase $\delta_p(\theta)$ (degrees)", title="(c) Optimal phase")
ax.legend(frameon=False, loc="upper left")
destination = Path(__file__).resolve().parent
for extension in ("pdf", "svg"):
    fig.savefig(destination / f"schatten_phase_diagram.{extension}")
