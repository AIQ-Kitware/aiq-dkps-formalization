"""Reusable numerical readouts for Manim slide components."""

from __future__ import annotations

from manim import DOWN, RIGHT, DecimalNumber, VGroup

from dkvis.slide_style import FG, math


def live(getter, decimals: int = 3, size: float = 30, color: str = FG, unit: str | None = None) -> DecimalNumber:
    num = DecimalNumber(
        getter(), num_decimal_places=decimals, font_size=size, color=color, unit=unit
    )

    def update(m: DecimalNumber) -> None:
        value = getter()
        if round(value, decimals) != round(m.get_value(), decimals):
            m.set_value(value)

    num.add_updater(update)
    return num


def readout_rows(rows, size: float = 30, buff: float = 0.22) -> VGroup:
    """Rows of ``(label_tex, getter, color, decimals, unit)`` with aligned values."""
    labels = VGroup(*[math(lbl, size=size, color=color) for lbl, _, color, _, _ in rows])
    labels.arrange(DOWN, aligned_edge=RIGHT, buff=buff)
    values = VGroup()
    for label, (_, getter, color, decimals, unit) in zip(labels, rows):
        value = live(getter, decimals=decimals, size=size, color=color, unit=unit)
        value.next_to(label, RIGHT, buff=0.2)
        value.add_updater(lambda m, label=label: m.next_to(label, RIGHT, buff=0.2))
        values.add(value)
    return VGroup(labels, values)
