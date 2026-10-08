"""Reusable numerical readouts for Manim slide components."""

from __future__ import annotations

from manim import DOWN, LEFT, RIGHT, UP, DecimalNumber, Line, VGroup

from dkvis.slide_style import FG, math


def live(
    getter,
    decimals: int = 3,
    size: float = 30,
    color: str = FG,
    unit: str | None = None,
    *,
    include_sign: bool = False,
) -> DecimalNumber:
    num = DecimalNumber(
        getter(),
        num_decimal_places=decimals,
        font_size=size,
        color=color,
        unit=unit,
        include_sign=include_sign,
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


def live_matrix_2x2(
    getter,
    *,
    label: str | None = None,
    decimals: int = 2,
    size: float = 24,
    color: str = FG,
) -> VGroup:
    """A compact live 2x2 numerical matrix.

    ``getter`` returns an array-like object supporting ``m[i, j]``.  Each entry
    is a :class:`~manim.DecimalNumber`, so changing the underlying tracker does
    not re-run LaTeX every frame.  Signs are always shown to keep the columns
    from jumping as an entry crosses zero.
    """

    entries = []
    for i in range(2):
        for j in range(2):
            entries.append(
                live(
                    lambda i=i, j=j: float(getter()[i, j]),
                    decimals=decimals,
                    size=size,
                    color=color,
                    include_sign=True,
                )
            )
    row0 = VGroup(entries[0], entries[1]).arrange(RIGHT, buff=0.28)
    row1 = VGroup(entries[2], entries[3]).arrange(RIGHT, buff=0.28)
    grid = VGroup(row0, row1).arrange(DOWN, buff=0.08)

    pad_y, cap = 0.07, 0.11
    y_top = grid.get_top()[1] + pad_y
    y_bot = grid.get_bottom()[1] - pad_y
    x_l = grid.get_left()[0] - 0.12
    x_r = grid.get_right()[0] + 0.12
    left = VGroup(
        Line([x_l, y_bot, 0], [x_l, y_top, 0], color=color, stroke_width=2),
        Line([x_l, y_top, 0], [x_l + cap, y_top, 0], color=color, stroke_width=2),
        Line([x_l, y_bot, 0], [x_l + cap, y_bot, 0], color=color, stroke_width=2),
    )
    right = VGroup(
        Line([x_r, y_bot, 0], [x_r, y_top, 0], color=color, stroke_width=2),
        Line([x_r - cap, y_top, 0], [x_r, y_top, 0], color=color, stroke_width=2),
        Line([x_r - cap, y_bot, 0], [x_r, y_bot, 0], color=color, stroke_width=2),
    )
    matrix = VGroup(left, grid, right)
    if label is None:
        return matrix
    lab = math(label, size=size)
    return VGroup(lab, matrix).arrange(RIGHT, buff=0.18)

