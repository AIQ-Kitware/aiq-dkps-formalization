"""Manim typeset slide for the Davis--Kahan sine-theta coordinate geometry.

Render from the repository's visualizations directory:

    uv run --extra manim python -m manim -s -qh \
        figures/sine_theta_players/manim_scene.py SineThetaGeometryScene

The slide is intentionally separate from the journal paper and its build.
All formulas are real MathTex objects, and typesetting controls label extents.
Colors are read from the paper's math_symbol_colors.tex, not restyled by hand.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
from manim import (
    Arc, Arrow, Circle, DOWN, LEFT, Line, MathTex,
    RIGHT, RoundedRectangle, Scene, Tex, TexTemplate, UP, VGroup, config,
)

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
from sine_theta_figure_model import (  # noqa: E402
    audit_dk_sine_theta_slice,
    read_dk_journal_colors,
)

# Fixed 16:9 design grid; the CLI's -qh controls the raster resolution.
config.frame_width = 128 / 9
config.frame_height = 8.0
config.background_color = "#FFFFFF"

COLORS = read_dk_journal_colors()
PAPER = "#FFFFFF"
PALE = "#F6F8FC"
BORDER = "#D7E0EA"

TEX_TEMPLATE = TexTemplate()
TEX_TEMPLATE.add_to_preamble(
    r"\usepackage[T1]{fontenc}\usepackage{lmodern}"
    r"\usepackage{amsmath,amssymb}"
    r"\renewcommand{\familydefault}{\rmdefault}"
)


def dk_slide_math(source: str, color: str = "ink", size: int = 30) -> MathTex:
    return MathTex(source, color=COLORS[color], font_size=size, tex_template=TEX_TEMPLATE)


def dk_slide_prose(source: str, color: str = "ink", size: int = 24) -> Tex:
    return Tex(source, color=COLORS[color], font_size=size, tex_template=TEX_TEMPLATE)


def dk_slide_position(mob, x: float, y: float, max_width: float | None = None):
    """Position an already typeset mobject, shrinking only when necessary."""
    if max_width and mob.width > max_width:
        mob.scale_to_fit_width(max_width)
    mob.move_to([x, y, 0])
    return mob


def dk_slide_panel(x: float, y: float, width: float, height: float):
    panel = RoundedRectangle(
        width=width, height=height, corner_radius=0.16,
        stroke_color=BORDER, stroke_width=1.3,
        fill_color=PAPER, fill_opacity=1,
    )
    panel.move_to([x, y, 0])
    return panel


class SineThetaGeometryScene(Scene):
    """One precise, journal-adjacent explanatory slide (no animation assets)."""

    def construct(self) -> None:
        data = audit_dk_sine_theta_slice()
        marks = []

        def remember(name, mob):
            marks.append((name, mob))
            return mob

        def at_math(name, expression, x, y, role="ink", size=29, width=None):
            obj = dk_slide_math(expression, role, size)
            remember(name, obj)
            return dk_slide_position(obj, x, y, width)

        def at_prose(name, sentence, x, y, role="ink", size=22, width=None):
            obj = dk_slide_prose(sentence, role, size)
            remember(name, obj)
            return dk_slide_position(obj, x, y, width)

        self.add(
            at_prose("title", r"\textbf{Geometry and Notation of the Sine-Theta Theorem}",
                     0, 3.48, size=37, width=12.8),
            at_prose("subtitle", "Exact spectral coordinates and an approximate trial subspace",
                     0, 2.99, role="muted", size=22, width=12.0),
        )

        # Two roomy panels, with margins sized for latex-rendered text.
        self.add(
            dk_slide_panel(-3.32, -0.06, 6.60, 5.42),
            dk_slide_panel(3.32, -0.06, 6.60, 5.42),
            dk_slide_panel(0, -3.45, 13.23, 0.95),
        )

        self.add(
            at_prose("geometry-heading", r"\textbf{An exact splitting of the ambient space}",
                     -3.38, 2.26, size=23, width=5.9),
            at_prose("coordinate-heading", r"\textbf{Three coordinate embeddings into $E$}",
                     3.32, 2.26, size=23, width=5.9),
        )

        # Left: E is the *entire plane*. F0 and F1 are orthogonal axes;
        # the trial subspace is another line in that same plane.
        ambient = RoundedRectangle(
            width=5.90, height=3.90, corner_radius=0.10,
            fill_color=PALE, fill_opacity=1,
            stroke_color=BORDER, stroke_width=0.8,
        ).move_to([-3.32, -0.02, 0])
        self.add(ambient)
        self.add(at_math("ambient-label", "E", -5.93, 1.55, "ambient", 34))

        o = np.array([-5.20, -1.27, 0.0])
        extent = 3.80
        end = o + np.array([extent*data.cosine, extent*data.sine, 0])
        projection = np.array([end[0], o[1], 0])
        self.add(
            # These axes are *spanning subspaces*, not separate boxes in E.
            Line(o + LEFT*0.65, o + RIGHT*4.37, color=COLORS["wanted"], stroke_width=5.5),
            Line(o + DOWN*0.50, o + UP*2.70, color=COLORS["unwanted"], stroke_width=5.5),
            Arrow(o, end, buff=0, color=COLORS["trial"], stroke_width=7,
                  tip_length=0.15, max_tip_length_to_length_ratio=0.16),
            Arrow(projection, end, buff=0, color=COLORS["unwanted"],
                  stroke_width=5, tip_length=0.11, max_tip_length_to_length_ratio=0.28),
            Circle(radius=0.045, color=COLORS["wanted"], fill_opacity=1).move_to(projection),
        )
        # The angle is the geometric principal angle in this rank-one slice.
        self.add(Arc(
            radius=0.86, start_angle=0, angle=data.theta, arc_center=o,
            color=COLORS["angle"], stroke_width=4,
        ))

        self.add(
            at_math("exact-wanted-line", r"\operatorname{ran}(F_0)", -1.48, -2.06, "wanted", 26, 2.20),
            at_math("exact-unwanted-line", r"\operatorname{ran}(F_1)", -3.82, 1.28, "unwanted", 26, 2.20),
            at_math("trial-vector", r"v=E_0(1)", -1.57, -0.10, "trial", 27, 2.28),
            at_math("component-vector", r"S(1)", -1.03, -0.91, "angle", 26, 0.88),
            at_math("wanted-projection", r"P_{\mathrm{ex}}v", -3.43, -1.56, "wanted", 26, 1.60),
            at_math("principal-angle", r"\theta=12^\circ", -4.14, -1.03, "angle", 26, 1.67),
            at_math("exact-direct-sum",
                    r"E=\operatorname{ran}(F_0)\oplus\operatorname{ran}(F_1)",
                    -3.32, -2.46, "ink", 29, 5.95),
        )

        # Right: each *abstract* coordinate space maps to a subspace in E.
        # Render rows from separate MathTex objects, then arrange using their
        # actual widths; the source contains no Unicode pseudo-subscripts.
        mappings = [
            (r"F_{\mathrm{ex}}", r"\xrightarrow{\ F_0\ }", r"\operatorname{ran}(F_0)\subset E", "wanted", 1.52),
            (r"G", r"\xrightarrow{\ F_1\ }", r"\operatorname{ran}(F_1)\subset E", "unwanted", 0.84),
            (r"F", r"\xrightarrow{\ E_0\ }", r"\operatorname{ran}(E_0)\subset E", "trial", 0.16),
        ]
        for i, (domain, arrow, image, color_role, y) in enumerate(mappings):
            parts = VGroup(
                dk_slide_math(domain, color_role, 29),
                dk_slide_math(arrow, color_role, 29),
                dk_slide_math(image, color_role, 29),
            )
            parts.arrange(RIGHT, buff=0.20)
            if parts.width > 5.78:
                parts.scale_to_fit_width(5.78)
            parts.move_to([3.32, y, 0])
            remember(f"embedding-row-{i}", parts)
            self.add(parts)

        self.add(
            at_prose("direct-sum-note", "The exact embeddings span all of $E$.",
                     3.32, -0.40, "muted", 20, 5.85),
            at_math("exact-decomposition", r"F_{\mathrm{ex}}\oplus G\cong E",
                    3.32, -0.91, "ink", 31, 5.75),
            at_math("trial-vector-decomposition",
                    r"E_0x=F_0(F_0^*E_0x)+F_1(F_1^*E_0x)",
                    3.32, -1.57, "ink", 29, 5.95),
            at_math("readout-equation",
                    r"X=F_1^*E_0\colon F\to G",
                    3.32, -2.08, "angle", 29, 5.80),
        )
        domains = VGroup(
            dk_slide_math(r"A_0:F\to F", "trial", 24),
            dk_slide_math(r"\Lambda_1:G\to G", "unwanted", 24),
        )
        domains.arrange(RIGHT, buff=0.75)
        if domains.width > 5.6:
            domains.scale_to_fit_width(5.6)
        domains.move_to([3.32, -2.48, 0])
        remember("operator-domain-labels", domains)
        self.add(domains)

        # Footer summarizes the analytic mechanism without crowding geometry.
        self.add(
            at_math("residual-definition", r"R=\widehat A E_0-E_0A_0",
                    -4.50, -3.25, "residual", 27, 3.90),
            at_math("sylvester-identity", r"\Lambda_1X-XA_0=F_1^*R",
                    0.88, -3.25, "ink", 27, 5.45),
            at_math("sine-bound", r"\delta\,N(\sin\Theta_0)\le N(R)",
                    2.80, -3.69, "gap", 25, 4.20),
            at_prose("gap-qualification", "under the theorem's gap and domain hypotheses",
                     -3.55, -3.69, "muted", 18, 5.85),
        )

        self._audit_dk_slide_labels(marks)
        self.wait(0.1)

    @staticmethod
    def _audit_dk_slide_labels(marks):
        """Check rendered glyph extents: source comments cannot guarantee fit."""
        half_width = config.frame_width / 2
        half_height = config.frame_height / 2
        padding = 0.06
        for name, mob in marks:
            x0, x1 = mob.get_left()[0], mob.get_right()[0]
            y0, y1 = mob.get_bottom()[1], mob.get_top()[1]
            if not (-half_width + padding < x0 and x1 < half_width - padding
                    and -half_height + padding < y0 and y1 < half_height - padding):
                raise ValueError(f"Text extends beyond slide frame: {name}")
        # Compare the actual vector boundaries, not estimated text lengths.
        # Neighboring labels intentionally adjacent are allowed small overlaps.
        for i, (name1, obj1) in enumerate(marks):
            for name2, obj2 in marks[i + 1:]:
                overlap_x = min(obj1.get_right()[0], obj2.get_right()[0]) - max(obj1.get_left()[0], obj2.get_left()[0])
                overlap_y = min(obj1.get_top()[1], obj2.get_top()[1]) - max(obj1.get_bottom()[1], obj2.get_bottom()[1])
                if overlap_x > 0.10 and overlap_y > 0.08:
                    raise ValueError(f"Overlapping labels: {name1} / {name2}")
