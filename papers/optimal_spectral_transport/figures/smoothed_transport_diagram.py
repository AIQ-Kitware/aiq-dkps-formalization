"""Render the exact smoothed transport formulas and their circle geometry.

The curves illustrate the proved formulas; numerical plotting is not proof
evidence. Run from any directory with NumPy and Matplotlib installed.
"""
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


def radius(tau):
    return (tau + np.sqrt(tau * tau + 4)) / 2


def phase(tau, theta):
    return np.arccos(np.clip(radius(tau) ** 2 * np.cos(theta), -1, 1))


def cost(tau, theta, delta):
    return (
        np.sqrt(tau * tau + 2 - 2 * np.cos(theta + delta))
        + np.sqrt(tau * tau + 2 - 2 * np.cos(theta - delta))
        - 2 * tau
    )


plt.rcParams.update(
    {"font.family": "DejaVu Serif", "font.size": 10,
     "axes.spines.top": False, "axes.spines.right": False,
     "pdf.fonttype": 42, "svg.fonttype": "none"}
)
blue, orange, purple = "#0072B2", "#D55E00", "#8A4B9F"
fig, axes = plt.subplots(1, 3, figsize=(8.6, 3.15), layout="constrained")

# The minimizing circle point lies on the segment between the two foci.
tau, theta = 0.25, np.pi / 3
a, b = radius(tau), 1 / radius(tau)
u = a * np.exp(1j * theta)
v = np.conj(u)
x = b * np.exp(1j * phase(tau, theta))
ax = axes[0]
t = np.linspace(0, 2 * np.pi, 501)
ax.plot(b * np.cos(t), b * np.sin(t), color=blue, linewidth=1.2)
ax.plot([u.real, v.real], [u.imag, v.imag], color=orange, linewidth=2)
ax.plot([u.real, b, v.real], [u.imag, 0, v.imag], "--", color="0.6", linewidth=1)
ax.plot([u.real, v.real], [u.imag, v.imag], "o", color=orange, markersize=4)
ax.plot(x.real, x.imag, "o", color=orange, markersize=6)
ax.plot(b, 0, "o", color=blue, markersize=4)
ax.plot(0, 0, ".", color="0.3", markersize=3)
ax.annotate(r"$ae^{i\theta}$", (u.real, u.imag), xytext=(6, 5), textcoords="offset points")
ax.annotate(r"$ae^{-i\theta}$", (v.real, v.imag), xytext=(5, -13), textcoords="offset points")
ax.annotate(r"$x_*$", (x.real, x.imag), xytext=(-23, -2), textcoords="offset points", color=orange)
ax.annotate(r"$b$", (b, 0), xytext=(5, -4), textcoords="offset points", color=blue)
ax.text(-0.87, -1.08, r"$|x|=b$,  $a=\eta$,  $b=\eta^{-1}$", fontsize=8.5)
ax.set(aspect="equal", xlim=(-1, 1.35), ylim=(-1.22, 1.22),
       title="(a) A triangle inequality")
ax.set_xticks([])
ax.set_yticks([])
ax.spines[["left", "bottom"]].set_visible(False)

ax = axes[1]
fractions = np.linspace(0, 1, 501)
critical_degrees = np.degrees(np.arccos(radius(tau) ** -2))
for degrees, color, style, label in [
    (25, blue, "-", r"$\theta=25^\circ$"),
    (critical_degrees, purple, ":", r"$\theta=c_\tau$"),
    (60, orange, "--", r"$\theta=60^\circ$"),
]:
    angle = np.radians(degrees)
    values = cost(tau, angle, fractions * angle) / cost(tau, angle, 0)
    ax.plot(fractions, values, color=color, linestyle=style,
            label=label)
    delta = phase(tau, angle)
    ax.plot(delta / angle, cost(tau, angle, delta) / cost(tau, angle, 0),
            "o", color=color, markersize=4)
ax.axhline(1, color="0.65", linewidth=0.7, zorder=0)
ax.set(xlim=(0, 1), xlabel=r"Phase fraction $\delta/\theta$",
       ylabel=r"Cost relative to $\delta=0$", title=r"(b) Cost at $\tau=1/4$")
ax.legend(frameon=False, loc="upper left")

ax = axes[2]
angles = np.radians(np.linspace(0, 90, 1001))
for smoothing, color, style in [(0.1, blue, "-"), (0.5, orange, "--"), (2, purple, "-.")]:
    cutoff = np.arccos(radius(smoothing) ** -2)
    sample = np.sort(np.append(angles, cutoff))
    ax.plot(np.degrees(sample), np.degrees(phase(smoothing, sample)), color=color,
            linestyle=style, label=rf"$\tau={smoothing:g}$")
ax.plot([0, 90], [0, 90], ":", color="0.65", linewidth=0.8)
ax.set(xlim=(0, 90), ylim=(0, 90), xlabel=r"Principal angle $\theta$ (degrees)",
       ylabel=r"Optimal phase $\delta_\tau(\theta)$ (degrees)", title="(c) Explicit optimal phase")
ax.legend(frameon=False, loc="upper left")

output = Path(__file__).resolve().parent
for extension in ("pdf", "svg"):
    artifact = output / f"smoothed_transport_diagram.{extension}"
    fig.savefig(artifact)
    if extension == "svg":
        artifact.write_text("\n".join(line.rstrip() for line in artifact.read_text().splitlines()) + "\n")
