"""Slides: how the Davis--Kahan formalization was built.

Full deck only.  The content follows the two papers in ``papers/``:

* ``dk_formalization_workshop/paper.tex`` -- "Did We Really Formalize
  Davis--Kahan?": the workflow figure, the three sine-theta statement
  boundaries, the acceptance-reversal record and the limitations;
* ``dk_formalization_journal/paper.tex`` -- "Formalizing Davis--Kahan
  Perturbation Theory in Lean": scope, foundations, the AI-assistance account.

The dated numbers are copied from those papers' generated evidence and are
pinned to the snapshots named next to them; update them together with the papers.
"""

from __future__ import annotations

import datetime as dt
from collections import Counter

import numpy as np
from manim import (
    DOWN,
    LEFT,
    RIGHT,
    UP,
    Arrow,
    Circle,
    Create,
    Dot,
    FadeIn,
    GrowArrow,
    Line,
    RoundedRectangle,
    VGroup,
)

from dkvis.slide_style import (
    FG,
    MUTED,
    DeckSlide,
    math,
    para,
    tex,
)
from dkvis.slides_sine_theta import fit_right

# This part is about the process, not the mathematics, so it uses neutral colors only:
# the role colors (blue, amber, cyan, pink, green, violet) keep their mathematical meaning.
STAGE = FG
FRAME = MUTED

SECTION = r"The Davis--Kahan formalization $\cdot$ how it was built"

# Acceptance reversals: an accepted source comparison changed to a nonaccepted
# state at the next revision of the result register.  Workshop paper,
# generated/semantic_reversals.csv, pinned repository snapshot 5f339b74
# (4 September 2026): 14 reversals in 10 distinct results.
REVERSALS = {
    dt.date(2026, 8, 12): [r"$\sin2\Theta$", "Prop 3.4", "Thm 8.2", "Prop 3.5"],
    dt.date(2026, 8, 31): [r"$\sin2\Theta$", r"$\sin2\Theta$", r"$\sin2\Theta$", r"$\sin\Theta$", "Thm 5.1", "Prop 6.1", "Thm 6.1"],
    dt.date(2026, 9, 2): [r"$\tan2\Theta$", r"$\tan2\Theta$", "Prop 3.2"],
}
# Points at which the register reported every result accepted (workshop paper,
# review-timeline table).
CHECKPOINTS = {
    dt.date(2026, 8, 12): r"register reaches 29/29",
    dt.date(2026, 8, 17): r"review reports 29/29",
    dt.date(2026, 9, 2): r"29/29 again",
    dt.date(2026, 9, 8): r"eighth hostile review passed",
}
# Retained model telemetry at the papers' evidence snapshot 1b40ccc3
# (30 September 2026); incomplete, and the energy row is modeled.
TELEMETRY = {
    "turns": "60,178",
    "output_tokens": "59.5 million",
    "energy_kwh": "555",
}


def card(width: float, height: float, color: str, fill: float = 0.10) -> RoundedRectangle:
    return RoundedRectangle(
        width=width, height=height, corner_radius=0.15,
        stroke_color=color, stroke_width=2.5, fill_color=color, fill_opacity=fill,
    )


def titled_card(title: str, body: str, width: float, height: float, color: str, size: float = 18) -> VGroup:
    """A rounded card with a bold title and a wrapped body, laid out from its top-left corner."""
    box = card(width, height, color)
    head = tex(rf"\textbf{{{title}}}", size=size + 4, color=color)
    text = para(body, width=width - 0.3, size=size)
    content = VGroup(head, text).arrange(DOWN, aligned_edge=LEFT, buff=0.1)
    content.move_to(box.get_corner(UP + LEFT) + np.array([0.15, -0.12, 0]), aligned_edge=UP + LEFT)
    return VGroup(box, content)


def arrow(a, b, color: str = FG) -> Arrow:
    return Arrow(a, b, buff=0.08, color=color, stroke_width=4, max_tip_length_to_length_ratio=0.18)


# ----------------------------------------------------------------------------
# W1. The workflow
# ----------------------------------------------------------------------------


class W01Workflow(DeckSlide):
    depth = "*"
    section = SECTION
    title = "How the formalization was built"
    kicker = "Humans set the targets and judged statements; agents wrote the Lean"

    def body(self) -> None:
        top = self.content_top - 0.05
        h_all = top + 2.05  # height down to y = -2.05

        inputs = VGroup(
            card(2.3, h_all, FRAME, fill=0.04).move_to([-5.85, top - h_all / 2, 0]),
        )
        in_items = VGroup(
            tex(r"\textbf{Inputs}", size=24, color=FG),
            para(r"\textbf{target theorem}, e.g.\ the $\sin\Theta$ theorem", width=2.0, size=18),
            para(r"\textbf{fidelity criteria}: scope and stop conditions", width=2.0, size=18),
            para(r"\textbf{references}: paper PDFs and transcriptions", width=2.0, size=18),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.3).move_to([-6.85, top - 0.15, 0], aligned_edge=UP + LEFT)
        inputs.add(in_items)

        loop_box = card(8.5, h_all, FRAME, fill=0.03).move_to([-0.25, top - h_all / 2, 0])
        loop_title = tex(r"\textbf{Formalization loop}", size=24, color=FG).move_to(loop_box.get_corner(UP + LEFT) + np.array([0.2, -0.12, 0]), aligned_edge=UP + LEFT)

        w, h = 2.55, 1.3
        y_top, y_bot = top - 1.2, top - 3.2
        decompose = titled_card("Decompose", r"intermediate results and their dependencies", w, h, STAGE).move_to([-3.05, y_top, 0])
        find = titled_card("Find foundations", r"search Mathlib, other Lean libraries and the literature before building", w, h, STAGE).move_to([-0.25, y_top, 0])
        formalize = titled_card("Formalize", r"an orchestrator (human or LLM) hands Lean tasks to agents", w, h, STAGE).move_to([2.55, y_top, 0])
        compile_ = titled_card(
            "Compile \\& revise", r"fix errors, record failed attempts; mechanical checks: clean build, axioms", w, h + 0.15, STAGE
        ).move_to([2.55, y_bot, 0])
        review = titled_card(
            "Skeptical review",
            r"a separate pass compares statement and source. Proof-producing LLMs often overclaim success.",
            4.9, h + 0.15, STAGE,
        ).move_to([-1.85, y_bot, 0])

        a1 = arrow(decompose.get_right(), find.get_left())
        a2 = arrow(find.get_right(), formalize.get_left())
        a3 = arrow(formalize.get_bottom(), compile_.get_top())
        a4 = arrow(compile_.get_left(), review.get_right())
        back = arrow(np.array([decompose.get_center()[0], review[0].get_top()[1], 0]), decompose.get_bottom(), FRAME)
        back_lbl = tex(r"mismatch: back to an earlier stage", size=17, color=FRAME).next_to(back, RIGHT, buff=0.12)

        outputs = card(2.3, h_all, FRAME, fill=0.04).move_to([5.85, top - h_all / 2, 0])
        out_items = VGroup(
            tex(r"\textbf{Outputs}", size=24, color=FG),
            para(r"\textbf{checked theorem}: a validated Lean endpoint", width=2.0, size=18),
            para(r"\textbf{reusable foundations}: contributions upstream (Tau Ceti)", width=2.0, size=18),
            para(
                r"\textbf{Palomar submission}: the Section~2 theorems stated against Mathlib alone, with proofs; "
                r"Comparator checks the proofs match the statements",
                width=2.0, size=18,
            ),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.3).move_to([4.85, top - 0.15, 0], aligned_edge=UP + LEFT)
        y_acc = review[0].get_bottom()[1] - 0.28
        x_acc = review[0].get_center()[0]
        accepted = VGroup(
            Line(np.array([x_acc, review[0].get_bottom()[1], 0]), np.array([x_acc, y_acc, 0]), color=FG, stroke_width=4),
            arrow(np.array([x_acc, y_acc, 0]), np.array([outputs.get_left()[0], y_acc, 0]), FG),
        )
        acc_lbl = tex(r"accepted", size=19, color=FG).next_to(accepted[1], DOWN, buff=0.05)

        roles = VGroup(
            para(
                r"\textbf{Humans} chose targets, supplied source context, rejected decompositions or statements and asked "
                r"for further review, at any return through the loop.",
                width=13.6, size=19,
            ),
            para(
                r"\textbf{Agents} (ChatGPT, Claude Code, Codex) transcribed and explained sources, proposed decompositions, "
                r"searched libraries, wrote Lean, repaired it from compiler errors and compared statements with the source.",
                width=13.6, size=19, color=MUTED,
            ),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.1).move_to([-6.85, -2.25, 0], aligned_edge=UP + LEFT)

        self.say(
            "This is the process from the workshop paper. The inputs are a target theorem, fidelity criteria saying "
            "what scope counts as done, and the source paper. A target is decomposed into intermediate results, we "
            "search existing libraries before building, and agents write the Lean."
        )
        self.play(FadeIn(inputs), Create(loop_box), FadeIn(loop_title))
        self.play(FadeIn(decompose), GrowArrow(a1), FadeIn(find), GrowArrow(a2), FadeIn(formalize))

        self.say(
            "Lean's compiler drives revision. Then a separate review compares the theorem statement with the source. "
            "That step exists because proof-producing models often report success on a statement that is not the "
            "paper's. A mismatch sends the target back to an earlier stage."
        )
        self.play(GrowArrow(a3), FadeIn(compile_), GrowArrow(a4), FadeIn(review))
        self.play(Create(back), FadeIn(back_lbl))

        self.say(
            "Accepted targets become checked theorems, and the general mathematics built along the way becomes "
            "reusable foundations, being prepared for the Tau Ceti library. The Section 2 theorems are also packaged "
            "as a Palomar submission: a standalone repository whose Challenge file states five declarations, covering "
            "all four theorem families, using Mathlib alone, and whose Solution file proves them from the extracted "
            "libraries. Lean's Comparator tool checks that the proofs establish exactly those statements with only "
            "the standard axioms. Yu, Wang and Samworth are packaged the same way."
        )
        self.play(Create(accepted), FadeIn(acc_lbl), FadeIn(outputs), FadeIn(out_items))

        self.say(
            "Who did what: the humans chose targets and judged statements, and could intervene at every return "
            "through the loop. ChatGPT, Claude Code and Codex agents did the transcription, search, Lean writing, "
            "repair and source comparison. The workflow emerged during the project; it was not designed as an experiment."
        )
        self.play(FadeIn(roles))


# ----------------------------------------------------------------------------
# W2. Two checks
# ----------------------------------------------------------------------------


class W02TwoChecks(DeckSlide):
    depth = "*"
    section = SECTION
    title = "Two separate checks"
    kicker = r"Lean checks the proof; a review checks that the statement is the paper's"

    def body(self) -> None:
        top = self.content_top - 0.15
        lean = titled_card(
            "Lean's kernel",
            r"Does this proof establish this proposition?\\[0.3em]"
            r"Mechanical, and done for every result reported. It says nothing about which informal theorem was encoded.",
            6.5, 2.15, STAGE, size=21,
        ).move_to([-3.45, top - 1.075, 0])
        review = titled_card(
            "Source comparison",
            r"Is this proposition the paper's claim? Compare, clause by clause: hypotheses, mathematical objects, "
            r"real or complex scalars, dimension, bounded or unbounded operators, norm class, gap assumptions, "
            r"constants, direction.",
            6.5, 2.15, STAGE, size=21,
        ).move_to([3.45, top - 1.075, 0])

        head = tex(r"Ways a checked statement drifted from its source:", size=24).move_to([-6.75, top - 2.6, 0], aligned_edge=LEFT)
        rows = [
            (
                r"\textbf{Weaker claim.}",
                r"``all doohickeys are excellent'' becomes ``all special doohickeys are quasi-excellent'' "
                r"(Chow's illustration). It still compiles.",
            ),
            (
                r"\textbf{Reported done too early.}",
                r"an agent proves a valid theorem for bounded operators only, or finite dimensions, or a narrower gap, "
                r"and describes the task as complete.",
            ),
            (
                r"\textbf{Extra hypothesis.}",
                r"an early $\tan\Theta$ endpoint asked its caller for a dimension condition the paper imposes only from "
                r"Section~3 on; the repaired endpoint derives it from the tangent being defined.",
            ),
        ]
        lines = VGroup()
        for key, text in rows:
            k = tex(key, size=21, color=FG)
            b = para(text, width=10.4, size=21)
            lines.add(VGroup(k, b))
        key_w = max(r[0].width for r in lines)
        for r in lines:
            r[1].next_to(r[0], RIGHT, buff=0.25, aligned_edge=UP)
            r[1].shift(RIGHT * (key_w - r[0].width))
        lines.arrange(DOWN, aligned_edge=LEFT, buff=0.22).next_to(head, DOWN, aligned_edge=LEFT, buff=0.25)
        for r in lines:
            fit_right(r)

        self.say(
            "Two different questions. Lean's kernel answers whether the proof establishes the stated proposition; "
            "it does that mechanically for every result here. It cannot say whether the proposition is the one in the paper."
        )
        self.play(FadeIn(lean))

        self.say(
            "That second question is a comparison with the source, clause by clause: hypotheses, objects, scalar "
            "field, dimension, boundedness, norm class, gap assumptions, constants and direction."
        )
        self.play(FadeIn(review))

        self.say(
            "Examples of drift. Chow's illustration: an agent turns all doohickeys are excellent into all special "
            "doohickeys are quasi-excellent, which still compiles. In this project agents proved valid bounded or "
            "finite-dimensional versions and reported the job done. And one early tan Theta statement asked for an "
            "extra hypothesis from a later section of the paper; the repaired statement derives it."
        )
        self.play(FadeIn(head), FadeIn(lines))


# ----------------------------------------------------------------------------
# W3. Three sine-theta statements
# ----------------------------------------------------------------------------


class W03ThreeStatements(DeckSlide):
    """Three checked sine-theta statements compared with the paper, hypothesis by hypothesis.

    The entries come from the three signatures in the workshop paper
    (``papers/dk_formalization_workshop/generated/*_sin_theta_exact.lean``).
    Statement 1's two scalar-field typeclass hypotheses hold for both ``R`` and
    ``C`` (they are instances), so they are a footnote rather than a row.
    """

    depth = "*"
    section = SECTION
    title = r"Three checked $\sin\Theta$ statements"
    kicker = r"Same conclusion, compared with the paper one hypothesis at a time"

    # Cell kinds: "same" as the paper, "broad" (covers more cases), "narrow" (misses cases),
    # "form" (a different but related formulation).
    ROWS = [
        ("spectral gap", "finite interval/exterior, or half-infinite",
         [("finite interval/exterior only", "narrow"), ("all of them, as form bounds", "broad"), ("all of them, as form bounds", "broad")]),
        ("ambient space", "separable Hilbert space",
         [("any Hilbert space", "broad"), ("any Hilbert space", "broad"), ("separable", "same")]),
        ("trial domain", r"$\{x: E_0x\in\operatorname{dom}A\}=\operatorname{dom}A_0$",
         [("one-way inclusion", "broad"), ("one-way inclusion", "broad"), ("one-way inclusion", "broad")]),
        ("norms", "compared where both are defined",
         [(r"assumes $N(R)$ finite", "form"), (r"assumes $N(R)$ finite, proves $N(S)$ finite", "form"), ("compared where both are defined", "same")]),
        ("angle operator", r"positive $\sin\Theta_0$",
         [(r"$S=(I-F_0F_0^*)E_0$, same norms", "form"), (r"$S$, same norms", "form"), (r"positive $\sin\Theta_0$", "same")]),
    ]
    # Each cell says how the Lean hypothesis compares with the paper's, by a mark and a shade.
    KIND_MARK = {"broad": (r"$+$", 0.10), "narrow": (r"$-$", 0.32), "form": (r"$\approx$", 0.0)}

    def body(self) -> None:
        xs = [-6.9, -4.15, -1.4, 1.35, 4.1]  # left edges: label, paper, 1, 2, 3
        col_w, row_h = 2.65, 0.6
        y0 = self.content_top - 0.35

        def cell(text: str, col: int, row: int, kind: str | None, color: str = FG) -> VGroup:
            y = y0 - row * row_h
            mark, shade = self.KIND_MARK.get(kind, ("", 0.0))
            box = RoundedRectangle(
                width=col_w - 0.08, height=row_h - 0.08, corner_radius=0.08,
                stroke_width=1.5 if kind in self.KIND_MARK else 0, stroke_color=FG,
                fill_color=FG, fill_opacity=shade,
            ).move_to([xs[col] + col_w / 2, y, 0])
            words = para((mark + r"\ " if mark else "") + text, width=col_w - 0.25, size=17, color=color,
                         align="centering").move_to(box)
            return VGroup(box, words)

        headers = VGroup(
            cell(r"\textbf{Davis--Kahan}", 1, 0, None, FG),
            cell(r"\textbf{1}\ (earlier)", 2, 0, None),
            cell(r"\textbf{2}", 3, 0, None),
            cell(r"\textbf{3}\ (current)", 4, 0, None),
        )
        labels = VGroup(*[
            para(rf"\textbf{{{name}}}", width=2.5, size=18, color=MUTED).move_to([xs[0], y0 - (i + 1) * row_h, 0], aligned_edge=LEFT)
            for i, (name, _, _) in enumerate(self.ROWS)
        ])
        paper = VGroup(*[cell(src, 1, i + 1, None, FG) for i, (_, src, _) in enumerate(self.ROWS)])
        cols = [VGroup(*[cell(entries[j][0], j + 2, i + 1, entries[j][1]) for i, (_, _, entries) in enumerate(self.ROWS)]) for j in range(3)]
        rule = Line([xs[0], y0 - row_h / 2, 0], [xs[4] + col_w, y0 - row_h / 2, 0], color=MUTED, stroke_width=1.5)

        legend = para(
            r"$+$ broader than the paper (more cases) \quad $-$ narrower (misses cases, shaded) "
            r"\quad $\approx$ a different formulation",
            width=13.0, size=18, align="centering",
        ).move_to([0, y0 - 5.85 * row_h, 0])
        foot = para(
            r"Statement 1 also has two typeclass hypotheses on the scalar field, which hold for $\mathbb R$ and $\mathbb C$.",
            width=13.0, size=16, color=MUTED, align="centering",
        ).next_to(legend, DOWN, buff=0.06)

        size, w = 19, 13.6
        t1 = para(
            r"\textbf{1} is broader on two hypotheses but misses the half-infinite gaps (Appendix to "
            r"Section~6), so it does not give the paper's theorem. It was once recorded as the match.",
            width=w, size=size,
        )
        t23 = para(
            r"\textbf{2} and \textbf{3} cover every case in the paper, with bridge theorems for $S$ and the norm "
            r"conventions. \textbf{3} uses the paper's own terms except for two hypotheses the paper's imply.",
            width=w, size=size,
        )
        moral = para(
            r"\textbf{No single ``more general'' ordering exists: compare each hypothesis with the source.}",
            width=w, size=size,
        )
        text = VGroup(t1, t23, moral).arrange(DOWN, aligned_edge=LEFT, buff=0.1).next_to(foot, DOWN, buff=0.15)
        text.align_to(np.array([-6.85, 0, 0]), LEFT)

        self.say(
            "From the workshop paper: three Lean theorems in the repository, all checked, all with the same conclusion. "
            "Compare each with Davis and Kahan, one hypothesis at a time. A plus means the Lean statement assumes less "
            "than the paper, so it covers more cases; a shaded minus means it covers fewer; approximately-equal means it "
            "is formulated differently."
        )
        self.play(FadeIn(headers[0], labels, paper, legend), Create(rule))

        self.say(
            "The first allows any Hilbert space and a weaker domain condition, so it is broader there. But its gap must "
            "be a finite interval and its exterior, and Davis and Kahan also prove half-infinite gaps. So it does not "
            "give their theorem, and at one point it was recorded as the match anyway."
        )
        self.play(FadeIn(headers[1], cols[0], foot), FadeIn(t1))

        self.say(
            "The second assumes less than the paper on three hypotheses and states the norm conditions differently. "
            "The third restores separability, the paper's norm convention and the positive sin Theta0 operator, "
            "and keeps two generalizations that the paper's hypotheses imply. Both cover every case in the paper."
        )
        self.play(FadeIn(headers[2], cols[1]))
        self.play(FadeIn(headers[3], cols[2]), FadeIn(t23))

        self.say(
            "So there is no single ordering by generality. The only reliable comparison is hypothesis by hypothesis."
        )
        self.play(FadeIn(moral))


# ----------------------------------------------------------------------------
# W4. Accepted results were reopened
# ----------------------------------------------------------------------------


class W04Reversals(DeckSlide):
    depth = "*"
    section = SECTION
    title = "Accepted results were reopened"
    kicker = r"14 acceptances withdrawn in 10 of the 29 results, up to 4 September 2026"

    def body(self) -> None:
        start, end = dt.date(2026, 8, 9), dt.date(2026, 9, 10)
        x_lo, x_hi, y = -6.4, 6.4, 0.55

        def X(day: dt.date) -> np.ndarray:
            t = (day - start).days / (end - start).days
            return np.array([x_lo + t * (x_hi - x_lo), y, 0.0])

        axis = Line(X(start), X(end), color=MUTED, stroke_width=2)
        ticks = VGroup()
        for day in (dt.date(2026, 8, 10), dt.date(2026, 8, 20), dt.date(2026, 9, 1), dt.date(2026, 9, 10)):
            ticks.add(Line(X(day) + UP * 0.08, X(day) + DOWN * 0.08, color=MUTED, stroke_width=2))
            ticks.add(tex(day.strftime("%-d %b"), size=17, color=MUTED).next_to(X(day), DOWN, buff=0.14).shift(DOWN * 0.0))

        flags = VGroup()
        for i, (day, label) in enumerate(CHECKPOINTS.items()):
            h = 0.6 + 0.4 * (i % 2)
            stem = Line(X(day), X(day) + UP * h, color=FG, stroke_width=3)
            tip = Dot(X(day) + UP * h, radius=0.07, color=FG)
            txt = tex(label, size=18, color=FG).next_to(tip, UP, buff=0.06)
            fit_right(txt)
            flags.add(VGroup(stem, tip, txt))

        stacks = VGroup()
        for day, results in REVERSALS.items():
            dots = VGroup(*[Circle(radius=0.075, color=FG, stroke_width=2.5).move_to(X(day) + DOWN * (0.6 + 0.24 * k)) for k in range(len(results))])
            counts = Counter(results)
            text = ", ".join(n if k == 1 else rf"{n} $\times{k}$" for n, k in counts.items())
            names = VGroup(
                tex(rf"\textbf{{{len(results)}}} on {day.strftime('%-d %b')}", size=18, color=FG),
                tex(text, size=17, color=MUTED),
            ).arrange(DOWN, aligned_edge=LEFT, buff=0.05)
            # 31 August and 2 September are close together: label the first on its left.
            side = LEFT if day == dt.date(2026, 8, 31) else RIGHT
            names.next_to(dots, side, buff=0.15, aligned_edge=UP)
            stacks.add(VGroup(dots, names))
        legend = VGroup(
            tex(r"flags above the line: the register reported every result accepted", size=18),
            tex(r"circles below the line: one accepted source comparison withdrawn", size=18),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.06).move_to([-6.85, 2.35, 0], aligned_edge=UP + LEFT)

        size, w = 20, 13.6
        causes = para(
            r"The Lean proofs stayed valid; what was withdrawn was the judgment that they state the paper's result. "
            r"Recurring causes: scope or hypothesis mismatch (finite versus half-infinite gap), representation mismatch "
            r"(directed versus ambient angle, residual versus perturbation, argument order), and review records "
            r"naming the wrong declaration.",
            width=w, size=size,
        )
        caveat = para(
            r"No error taxonomy was fixed in advance and the reviews were not blinded, so these counts are a "
            r"retrospective record, not an error rate.",
            width=w, size=size - 1, color=MUTED,
        )
        bottom = VGroup(causes, caveat).arrange(DOWN, aligned_edge=LEFT, buff=0.12).move_to([-6.85, -1.75, 0], aligned_edge=UP + LEFT)

        self.say(
            "The project's register tracked, for each of the 29 results, whether its source comparison had been accepted. "
            "The flags above the line: the points where every result was accepted. Twelfth of August, seventeenth of August, second of September, "
            "and an eighth hostile review passing on the eighth."
        )
        self.play(Create(axis), FadeIn(ticks), FadeIn(legend))
        self.play(FadeIn(flags))

        self.say(
            "The circles below: each time an accepted result was taken back. Fourteen times, in ten different results, up to the "
            "fourth of September. sin 2 Theta alone was reopened four times."
        )
        self.play(FadeIn(stacks))

        self.say(
            "None of these were broken proofs. The proofs stayed valid; the claim that they were the paper's theorem "
            "did not. Typical causes: a gap hypothesis narrower than the paper's, a directed angle where the paper "
            "meant the ambient one, or the review record pointing at the wrong declaration. This is a record, not a "
            "measured error rate."
        )
        self.play(FadeIn(bottom))


# ----------------------------------------------------------------------------
# W5. Scale and effort
# ----------------------------------------------------------------------------


class W05Scale(DeckSlide):
    depth = "*"
    section = SECTION
    title = "What it took"
    kicker = "New operator-theory foundations, many model turns, and a different starting point"

    def body(self) -> None:
        top = self.content_top - 0.15
        size = 20
        found_head = tex(r"\textbf{Mathematics built along the way}", size=24, color=FG)
        found = VGroup(*[
            para(t, width=6.2, size=size) for t in (
                r"principal angles, projections and direct rotations",
                r"approximation numbers and symmetric operator ideals (unitarily invariant norms in infinite dimensions)",
                r"Borel spectral calculus",
                r"unbounded self-adjoint operators as domain-carrying partial maps",
                r"real/complex transfer by complexification",
                r"Sylvester equations with spectral separation",
            )
        ]).arrange(DOWN, aligned_edge=LEFT, buff=0.12)
        found_note = para(
            r"Parts adapted or generalized from the Spectra development; reusable parts are being prepared for Tau Ceti, "
            r"a Lean library downstream of Mathlib.",
            width=6.2, size=size - 1, color=MUTED,
        )
        yws = para(
            r"Also formalized: Yu--Wang--Samworth (2015) Theorems 1--3, finding two printed defects (a missing square in "
            r"equation~(4), a rank-boundary convention in Theorem~3).",
            width=6.2, size=size - 1,
        )
        left = VGroup(found_head, found, found_note, yws).arrange(DOWN, aligned_edge=LEFT, buff=0.22)
        left.move_to([-6.85, top, 0], aligned_edge=UP + LEFT)

        eff_head = tex(r"\textbf{Effort} \cx{muted}{(retained telemetry, incomplete)}", size=24, color=FG)
        nums = VGroup(
            VGroup(math(TELEMETRY["turns"], size=40, color=FG), tex(r"model turns", size=20, color=MUTED)),
            VGroup(math(r"\text{" + TELEMETRY["output_tokens"] + r"}", size=40, color=FG), tex(r"output tokens", size=20, color=MUTED)),
            VGroup(math(r"\approx" + TELEMETRY["energy_kwh"] + r"\ \text{kWh}", size=40, color=FG),
                   tex(r"modeled serving energy; excludes training and hardware", size=20, color=MUTED)),
        )
        for n in nums:
            n.arrange(RIGHT, buff=0.25, aligned_edge=DOWN)
        nums.arrange(DOWN, aligned_edge=LEFT, buff=0.22)
        systems = para(
            r"ChatGPT, Claude Code and Codex (Claude Opus 4.8, Opus 5 and Fable 5; GPT-5 and GPT-5.6 family models). "
            r"Snapshot of 30 September 2026.",
            width=6.2, size=size - 1, color=MUTED,
        )
        start = para(
            r"\textbf{Starting point.} The lead author began with no experience in formal theorem proving and had not "
            r"studied most of the operator theory involved. The expertise needed to start was far less than the "
            r"expertise in the finished development, with kernel checking paired with sustained review of what was stated.",
            width=6.2, size=size,
        )
        right = VGroup(eff_head, nums, systems, start).arrange(DOWN, aligned_edge=LEFT, buff=0.25)
        right.move_to([0.55, top, 0], aligned_edge=UP + LEFT)
        for m in right:
            fit_right(m)

        self.say(
            "Reaching the paper's full scope meant building operator theory that Lean's libraries did not have: "
            "principal angles and direct rotations, operator ideals for unitarily invariant norms in infinite "
            "dimensions, Borel spectral calculus, unbounded operators, real-complex transfer and Sylvester equations. "
            "The same machinery also formalized Yu, Wang and Samworth's statistical version, where it found two printed defects."
        )
        self.play(FadeIn(left))

        self.say(
            "The effort, from the telemetry we kept, which is incomplete: about sixty thousand model turns, sixty million "
            "output tokens, and a modeled serving energy around 555 kilowatt hours."
        )
        self.play(FadeIn(right[0]), FadeIn(right[1]), FadeIn(right[2]))

        self.say(
            "And the starting point: the lead author had never used a proof assistant and had not studied most of this "
            "operator theory. The tools made it possible to learn both while building, provided the statements were "
            "reviewed throughout."
        )
        self.play(FadeIn(right[3]))


# ----------------------------------------------------------------------------
# W6. What the evidence supports
# ----------------------------------------------------------------------------


class W06Claims(DeckSlide):
    depth = "*"
    section = SECTION
    title = "What the evidence supports"
    kicker = "An experience report from one project, in one area of operator theory"

    def body(self) -> None:
        top = self.content_top - 0.15
        size = 21
        sup = titled_card(
            "Supported",
            r"$\bullet$ every result reported here is checked by Lean's kernel\\[0.25em]"
            r"$\bullet$ 28 of the 29 results proved at the paper's scope; Proposition~4.4 refuted, with a proved repair\\[0.25em]"
            r"$\bullet$ compilation and source comparison were tracked separately, and the comparison caught real "
            r"mismatches in checked statements\\[0.25em]"
            r"$\bullet$ repeated failure to prove Proposition~4.4 led to analyzing the claim, and to the counterexample",
            6.6, 4.0, STAGE, size=size,
        ).move_to([-3.45, top - 2.0, 0])
        nots = titled_card(
            "Not established",
            r"$\bullet$ no baseline: no comparison with compile-only, human-only or other workflows\\[0.25em]"
            r"$\bullet$ no blind or independent expert review of the 29 source comparisons\\[0.25em]"
            r"$\bullet$ no residual error rate: ``29/29'' is the project's own current judgment\\[0.25em]"
            r"$\bullet$ the workflow emerged during the project; it was not designed in advance",
            6.6, 4.0, FRAME, size=size,
        ).move_to([3.45, top - 2.0, 0])
        moral = para(
            r"Read each conclusion together with the hypotheses and definitions that set its scope. Deciding whether a "
            r"checked statement is the intended mathematics stays with the people responsible for it.",
            width=13.4, size=22, align="centering",
        ).move_to([0, top - 4.55, 0], aligned_edge=UP)

        self.say(
            "What the evidence supports: every reported result is kernel checked; 28 of 29 are proved at the paper's "
            "scope and Proposition 4.4 is refuted and repaired; keeping compilation and source comparison separate "
            "caught real mismatches; and failing to prove 4.4 is what led to the counterexample."
        )
        self.play(FadeIn(sup))

        self.say(
            "What it does not establish: there was no baseline, no blind or independent human expert review (there was blind LLM review), and no error "
            "rate. 29 out of 29 is our own current judgment. This is one project's experience."
        )
        self.play(FadeIn(nots))

        self.say(
            "The practical advice: read each conclusion with the hypotheses and definitions that set its scope. "
            "Whether a checked statement is the intended mathematics remains a human responsibility."
        )
        self.play(FadeIn(moral))
