"""Slides: the notation glossary.

Full deck, last part.  One place that lists every symbol the decks use, in its
role color, with its meaning and where it appears, so the notation on every
other slide can be checked against it.  When a slide changes a symbol, change
the entry here in the same commit.
"""

from __future__ import annotations

from manim import DOWN, LEFT, RIGHT, UP, FadeIn, Line, Rectangle, VGroup

from dkvis.slide_style import (
    CURRENT,
    FG,
    GAP,
    OLD,
    PERTURB,
    REFUTED,
    MUTED,
    PANEL,
    RESID,
    SINE,
    TRIAL,
    UNWANTED,
    WANTED,
    DeckSlide,
    math,
    para,
    tex,
)

COL_X = (-6.85, 0.2)
SYMBOL_W = 1.45
MEANING_W = 5.0


def entry(symbol: str, meaning: str) -> VGroup:
    """One glossary row: the symbol, written with ``\\sym`` so it takes its color from
    :mod:`dkvis.notation`, then its meaning."""
    sym = math(symbol, size=29)
    if sym.width > SYMBOL_W:
        sym.scale_to_fit_width(SYMBOL_W)
    text = para(meaning, width=MEANING_W, size=20)
    text.move_to([sym.get_left()[0] + SYMBOL_W + 0.15, sym.get_top()[1], 0], aligned_edge=UP + LEFT)
    return VGroup(sym, text)


def glossary_column(rows: list[tuple[str, str]], x: float, top: float, buff: float = 0.2) -> VGroup:
    col = VGroup(*[entry(*row) for row in rows]).arrange(DOWN, aligned_edge=LEFT, buff=buff)
    col.move_to([x, top, 0], aligned_edge=[-1, 1, 0])
    return col


class GlossarySlide(DeckSlide):
    depth = "**"
    LEFT: list[tuple[str, str]] = []
    RIGHT: list[tuple[str, str]] = []
    LEFT_HEAD = ""
    RIGHT_HEAD = ""
    NOTES = ""
    ROW_BUFF = 0.2

    def header(self, text: str, x: float, top: float) -> VGroup:
        head = tex(rf"\textbf{{{text}}}", size=21, color=MUTED).move_to([x, top, 0], aligned_edge=[-1, 1, 0])
        rule = Line([x, head.get_bottom()[1] - 0.06, 0], [x + SYMBOL_W + MEANING_W + 0.15, head.get_bottom()[1] - 0.06, 0],
                    color=MUTED, stroke_width=1)
        return VGroup(head, rule)

    def columns(self, top: float) -> VGroup:
        out = VGroup()
        for x, head, rows in ((COL_X[0], self.LEFT_HEAD, self.LEFT), (COL_X[1], self.RIGHT_HEAD, self.RIGHT)):
            h = self.header(head, x, top)
            out.add(VGroup(h, glossary_column(rows, x, h.get_bottom()[1] - 0.15, self.ROW_BUFF)))
        # Glossary lines have different heights and sometimes wrap after an
        # editorial change.  Scale only if needed, keeping all entries clear
        # of the slide number and the footer rather than cropping the last row.
        bottom_margin = -3.35
        available_height = top - bottom_margin
        if out.height > available_height:
            out.scale_to_fit_height(available_height)
            out.shift(UP * (top - out.get_top()[1]))
        return out

    def body(self) -> None:
        self.say(self.NOTES)
        self.play(FadeIn(self.columns(self.content_top - 0.1)))


class G01Matrices(GlossarySlide):
    title = r"Notation (1/3): operators and frames"
    kicker = r"In the $\sin\Theta$ story, name the frames we can operate on; take their ranges only when needed"
    NOTES = (
        "The core notation now names frames rather than assigning extra letters to their ranges. Amber E0 and A0 "
        "are the trial pair. Blue F0 is the exact wanted frame; cyan F1 and Lambda1 are the exact unwanted pair. "
        "Steel A hat is the operator under study. Only in the perturbation application do we additionally introduce "
        "the original tan A and vermilion H with A hat equal to A plus H. Lean calls the ambient operator A; that "
        "source name corresponds to A hat on these slides."
    )
    LEFT_HEAD = "Operators"
    ROW_BUFF = 0.13
    LEFT = [
        (r"\sym{Ahat}", r"operator under study in the general theorem; Lean/source name: \texttt{A}"),
        (r"\sym{A0}", r"operator on trial coordinates paired with $\sym{E0}$; residual tests whether they intertwine"),
        (r"\sym{Lambda1}", r"exact unwanted block: $\sym{Ahat}\sym{F1}=\sym{F1}\sym{Lambda1}$"),
        (r"\sym{Lambda0}", r"exact wanted block when needed: $\sym{Ahat}\sym{F0}=\sym{F0}\sym{Lambda0}$"),
        (r"\sym{A}", r"original operator in the perturbation application only"),
        (r"\sym{H}", r"perturbation, with $\sym{Ahat}=\sym{A}+\sym{H}$"),
        (r"\sym{H0},\ \sym{B},\ \sym{H1}", r"blocks of $\sym{H}$ in the original $\sym{A}$ eigenbasis (Part 3)"),
        (r"\sym{A1}", r"exact complementary block of original $\sym{A}$ when Part 3 needs it"),
    ]
    RIGHT_HEAD = "Frames and vectors"
    RIGHT = [
        (r"\sym{E0}", r"orthonormal trial frame; its range is the trial subspace"),
        (r"\sym{F0}", r"orthonormal exact wanted frame of $\sym{Ahat}$; its range is the target"),
        (r"\sym{F1}", r"orthonormal exact unwanted frame of $\sym{Ahat}$; its range is the unwanted complement"),
        (r"\sym{v}", r"a unit trial vector; the one-column version of $\sym{E0}$"),
        (r"\sym{f0},\ \sym{f1}", r"exact wanted / unwanted eigenvectors in the one-vector proof picture"),
        (r"\sym{P}=E_0E_0^*", r"projector onto $\operatorname{range}(\sym{E0})$; neutral"),
        (r"\sym{Q}=F_0F_0^*", r"projector onto $\operatorname{range}(\sym{F0})$; neutral"),
        (r"\sym{E1}", r"a complementary frame used in some Part 3 perturbation decompositions"),
    ]

    def body(self) -> None:
        tiers = [
            [(WANTED, "exact wanted"), (TRIAL, "trial"), (UNWANTED, "exact unwanted"), (SINE, "angle, error"),
             (RESID, "residual"), (GAP, "separation"), (FG, "neutral")],
            [(OLD, r"original $\sym{A}$"), (CURRENT, r"operator $\sym{Ahat}$"), (PERTURB, r"perturbation $\sym{H}$"),
             (REFUTED, "refuted claim")],
        ]
        rows = VGroup()
        for tier in tiers:
            row = VGroup()
            for color, name in tier:
                box = Rectangle(width=0.32, height=0.22, stroke_width=0, fill_color=color, fill_opacity=1)
                row.add(VGroup(box, tex(name, size=19, color=color).next_to(box, RIGHT, buff=0.1)))
            rows.add(row.arrange(RIGHT, buff=0.35))
        swatches = rows.arrange(DOWN, buff=0.12).move_to([0, self.content_top - 0.15, 0], aligned_edge=[0, 1, 0])
        bg = Rectangle(width=swatches.width + 0.4, height=swatches.height + 0.2, fill_color=PANEL, fill_opacity=1,
                       stroke_width=0).move_to(swatches)
        self.say(self.NOTES)
        self.play(FadeIn(bg, swatches), FadeIn(self.columns(bg.get_bottom()[1] - 0.2)))


class G02Spectra(GlossarySlide):
    title = r"Notation (2/3): spectra, separation, angles, residuals"
    kicker = r"What the theorem can form, what it targets, and what must be certified"
    NOTES = (
        "On the left are the two spectra the sine-theta theorem separates. A0 belongs to the trial coordinates; "
        "Lambda1 is the exact unwanted block of A hat. Delta is a certified lower separation between those spectra, "
        "not the original perturbation eigengap g. On the right are the target angle and the residual that can be "
        "formed without knowing F0."
    )
    LEFT_HEAD = "Spectra and separation"
    LEFT = [
        (r"\operatorname{spec}(\sym{A0})", r"trial-coordinate spectrum; Ritz values for Rayleigh--Ritz $A_0=E_0^*\sym{Ahat}E_0$"),
        (r"\operatorname{spec}(\sym{Lambda1})", r"exact unwanted spectrum of $\sym{Ahat}$"),
        (r"[\beta,\alpha]", r"interval containing $\operatorname{spec}(\sym{A0})$ in the interval/exterior form"),
        (r"\sym{delta}", r"certified separation: unwanted exact spectrum stays outside the expanded trial interval"),
        (r"\sym{g}", r"original wanted/unwanted eigengap of $\sym{A}$ in the perturbation examples; not $\sym{delta}$"),
        (r"\sym{rho}", r"one-vector Rayleigh quotient $\sym{v}^{*}\sym{Ahat}\sym{v}$; the $1\times1$ analogue of $\sym{A0}$"),
        (r"\sym{a0},\ \sym{a1}", r"the two original eigenvalues of $\sym{A}$ in the $2\times2$ examples"),
        (r"\lambda_j", r"exact eigenvalues of $\sym{Ahat}$ in finite-dimensional explanatory pictures"),
    ]
    RIGHT_HEAD = "Angles and residuals"
    RIGHT = [
        (r"\sym{Theta0}(\sym{E0},\sym{F0})", r"principal-angle operator between $\operatorname{range}(\sym{E0})$ and $\operatorname{range}(\sym{F0})$"),
        (r"\sym{sinTheta0}(\sym{E0},\sym{F0})", r"$\lvert(I-F_0F_0^*)E_0\rvert$; the directed subspace error"),
        (r"\sym{theta}", r"one principal angle in a one-vector / $2\times2$ picture"),
        (r"\sym{R}", r"$\sym{Ahat}\sym{E0}-\sym{E0}\sym{A0}$; invariance defect of the trial pair"),
        (r"\sym{r}", r"one-vector residual $\sym{Ahat}\sym{v}-\sym{rho}\sym{v}$"),
        (r"\sym{X}=F_1^*E_0", r"overlap with exact unwanted directions; $\norm{X}=\norm{\sym{sinTheta0}}$"),
        (r"\sym{Theta}", r"ambient angle operator; each nonzero principal angle appears twice"),
        (r"\sym{S}", r"$(I-F_0F_0^*)E_0$, the rectangular directed-sine block"),
    ]


class G03Other(GlossarySlide):
    title = r"Notation (3/3): norms, examples, local symbols"
    kicker = r"Symbols that belong to one example or one proof"
    NOTES = (
        "Norms on the left, and the parameters of the examples. On the right, symbols that only live inside one "
        "proof or one part, mostly Davis and Kahan's own."
    )
    LEFT_HEAD = "Norms and example parameters"
    LEFT = [
        (r"\norm{\cdot}", r"any unitarily invariant norm: $\norm{UKW}=\norm{K}$ for unitary $U$, $W$"),
        (r"\norm{\cdot}_2,\ \norm{\cdot}_F", r"the operator norm (largest singular value) and the Frobenius "
                                                 r"norm"),
        (r"\norm{\cdot}_\nu", r"the Ky Fan $\nu$-norm: the sum of the $\nu$ largest singular values"),
        (r"N", r"a unitarily invariant norm as a named object (Lean statements, Proposition 4.4)"),
        (r"\varepsilon", r"the size of $\sym{H}$ in the examples, $\norm{\sym{H}}_2=\varepsilon$ (often $0.12$)"),
        (r"\sym{b}", r"the coupling entry of the $2\times2$ matrix $\begin{pmatrix}a_0&\sym{b}\\\sym{b}&a_1\end{pmatrix}$"),
        (r"t", r"a value of the bound $\norm{R}/\delta$, used on the plots of Part 3"),
    ]
    RIGHT_HEAD = "Local to one part or proof"
    RIGHT = [
        (r"U,\ V", r"named subspaces used locally in Proposition 4.4 / direct-rotation statements; not the core $\sin\Theta$ frame notation"),
        (r"\mathcal R", r"the direct rotation between the two subspaces (Parts 3 and 4); its square turns "
                            r"by $2\Theta$"),
        (r"W", r"Part 4: a competing orthogonal map with $W(U)=V$"),
        (r"\Sigma=P-P^\perp", r"the reflection across $V$ in the $\sin2\Theta$ proof (Davis and Kahan's $X$)"),
        (r"C_0,\ C_1,\ J_0", r"the cosine blocks and the partial isometry of the direct rotation (Part 3 proofs)"),
        (r"x_j,\ y_j", r"a pair of principal vectors: $x_j$ on the trial side, $y_j$ on the unwanted side"),
        (r"\varphi", r"a turning angle: of $\sym{H}$ (instability slide), of the basis (Jacobi slide), of the hinge (3D)"),
        (r"\alpha_k,\ \lambda_k", r"Theorem 8.1: ordered eigenvalues of $\sym{A1}$ and $\sym{Lambda1}$"),
    ]
