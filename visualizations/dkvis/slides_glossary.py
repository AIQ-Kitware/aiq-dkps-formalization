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
        return out

    def body(self) -> None:
        self.say(self.NOTES)
        self.play(FadeIn(self.columns(self.content_top - 0.1)))


class G01Matrices(GlossarySlide):
    title = r"Notation (1/3): colors, matrices, subspaces"
    kicker = r"Each symbol in its role color; gray only de-emphasizes and never carries a role"
    NOTES = (
        "The glossary. Colors carry roles: blue is what we want, amber what we computed, cyan the exact part "
        "we do not want, pink how much of the computation points into it, green the residual that exposes it, "
        "violet the separation that keeps it from hiding. A quieter second row says where an operator comes from: "
        "tan for the old A, whose eigenvectors are the trial; steel for A tilde, whose eigenvectors are the "
        "wanted and unwanted directions; vermilion for the perturbation H. Red marks only a refuted claim, and "
        "gray only de-emphasizes. "
        "Then the matrices and the subspaces, with one meaning each."
    )
    LEFT_HEAD = "Matrices and operators"
    ROW_BUFF = 0.13
    LEFT = [
        (r"\sym{A}", r"the old (unperturbed) self-adjoint matrix or operator"),
        (r"\sym{H}", r"the perturbation, self-adjoint; $\norm{\sym{H}}_2$ is its size"),
        (r"\sym{At}=A+H", r"the matrix we have. Lean's \texttt{A}; Davis and Kahan's $\sym{A}+\sym{H}$"),
        (r"\sym{H0},\ \sym{B},\ \sym{H1}", r"blocks of $\sym{H}$ in $\sym{A}$'s eigenbasis: within the wanted part, the coupling "
                           r"between wanted and unwanted, within the unwanted part"),
        (r"\sym{A0}", r"the trial matrix on $\sym{V}$: $E_0^*\sym{At}E_0$ (Rayleigh--Ritz), or $\sym{A}$'s wanted block "
                      r"$E_0^*\sym{A}E_0$ in the perturbation reading"),
        (r"\sym{A1}", r"the complementary block of the old $\sym{A}$, $E_1^*\sym{A}E_1$ (Part 3)"),
        (r"\sym{Lambda0}", r"$\sym{At}$ on $\sym{U}$: $\sym{At}F_0=F_0\Lambda_0$"),
        (r"\sym{Lambda1}", r"$\sym{At}$ on $\sym{Uperp}$: $\sym{At}F_1=F_1\Lambda_1$"),
        (r"\sym{P},\ \sym{Q}", r"projectors onto $\sym{V}$ and $\sym{U}$: $P=E_0E_0^*$, $Q=F_0F_0^*$; "
                               r"they belong to no role, so neutral"),
    ]
    RIGHT_HEAD = "Subspaces, bases, vectors"
    RIGHT = [
        (r"\sym{U}", r"the wanted subspace: spanned by $\sym{At}$'s wanted eigenvectors (exact, usually unknown)"),
        (r"\sym{Uperp}", r"the unwanted directions: spanned by the rest of $\sym{At}$'s eigenvectors"),
        (r"\sym{F0},\ \sym{F1}", r"orthonormal bases of $\sym{U}$ and $\sym{Uperp}$"),
        (r"\sym{u},\ \sym{w}", r"a wanted and an unwanted eigenvector of $\sym{At}$"),
        (r"\sym{V},\ \sym{v}", r"the trial subspace (e.g.\ from an eigensolver); a single trial vector"),
        (r"\sym{E0}", r"an orthonormal basis of $\sym{V}$, as columns"),
        (r"\sym{Vperp},\ \sym{E1}", r"the complement of $\sym{V}$ and a basis of it; neutral, since neither is "
                                    r"computed or wanted"),
    ]

    def body(self) -> None:
        tiers = [
            [(WANTED, "wanted"), (TRIAL, "trial"), (UNWANTED, "unwanted"), (SINE, "angle, error"),
             (RESID, "residual"), (GAP, "gap"), (FG, "neutral")],
            [(OLD, r"old $\sym{A}$"), (CURRENT, r"current $\sym{At}$"), (PERTURB, r"perturbation $\sym{H}$"),
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
    title = r"Notation (2/3): spectra, gaps, angles, residuals"
    kicker = r"What is separated, what is measured, and what is computed"
    NOTES = (
        "Spectra and gaps on the left: eigenvalues, the trial values, the Rayleigh quotient, the interval and "
        "the gap. Angles and residuals on the right: the principal angles, the directed and ambient angle "
        "operators, and the two residuals."
    )
    LEFT_HEAD = "Spectra and gaps"
    LEFT = [
        (r"\lambda,\ \lambda_j", r"eigenvalues of $\sym{At}$; in the $2\times2$ examples $\sym{lambda0}$ "
                                 r"(wanted) and $\sym{lambda1}$ (unwanted)"),
        (r"f_j", r"eigenvectors of $\sym{At}$, $\sym{At}f_j=\lambda_jf_j$; drawn blue when wanted, cyan when not"),
        (r"\sym{a0},\ \sym{a1}", r"the two eigenvalues of the old $\sym{A}$ in the $2\times2$ examples; $a_0$, the top "
                                 r"one, is the trial value"),
        (r"\like{mu}{\mu_j}", r"trial values: the eigenvalues of $\sym{A0}$ (Ritz values)"),
        (r"\sym{rho}", r"the Rayleigh quotient $v^*\sym{At}v$ of a unit trial vector"),
        (r"[\beta,\alpha]", r"an interval containing the spectrum of $\sym{A0}$ (or of the separated block)"),
        (r"\sym{delta}", r"the gap: how far the separated spectra are apart; which spectra depends on the theorem"),
        (r"\sym{g}", r"the gap between the two eigenvalues of $\sym{A}$ in the $2\times2$ examples"),
    ]
    RIGHT_HEAD = "Angles and residuals"
    RIGHT = [
        (r"\sym{theta},\ \like{theta}{\theta_j}", r"the angle(s) between $\sym{V}$ and $\sym{U}$: the principal "
                                                  r"angles, each in $[0^\circ,90^\circ]$"),
        (r"\sym{Theta0}", r"the directed angle operator, a function of the two bases: "
                          r"$\Theta_0(E_0,F_0)=\arcsin\lvert(I-F_0F_0^*)E_0\rvert$, the angles from $\sym{V}$ to $\sym{U}$"),
        (r"\sym{Theta}", r"the ambient angle operator of the whole rotation; each nonzero angle appears twice"),
        (r"\sym{sinTheta0}", r"its sine: $\sin\Theta_0(E_0,F_0)=\lvert(I-F_0F_0^*)E_0\rvert$, with "
                             r"$\lvert X\rvert=(X^*X)^{1/2}$; and $\norm{\sin\Theta}=\norm{P-Q}$"),
        (r"\sym{S}", r"$(I-F_0F_0^*)E_0$, the rectangular block with the norms of $\sin\Theta_0$"),
        (r"\sym{r}", r"the residual of one vector: $\sym{At}v-\rho v$"),
        (r"\sym{R}", r"the residual of a subspace: $\sym{At}E_0-E_0A_0$; $=\sym{H}E_0$ in the perturbation reading"),
        (r"\sym{X}", r"the overlap matrix $F_1^*E_0$ of the Sylvester equation, $\norm{X}=\norm{\sin\Theta_0}$"),
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
        (r"\mathcal R", r"the direct rotation between the two subspaces (Parts 3 and 4); its square turns "
                            r"by $2\Theta$"),
        (r"W", r"Part 4: a competing orthogonal map with $W(U)=V$"),
        (r"\Sigma=P-P^\perp", r"the reflection across $V$ in the $\sin2\Theta$ proof (Davis and Kahan's $X$)"),
        (r"C_0,\ C_1,\ J_0", r"the cosine blocks and the partial isometry of the direct rotation (Part 3 proofs)"),
        (r"x_j,\ y_j", r"a pair of principal vectors: $x_j$ on the trial side, $y_j$ on the unwanted side"),
        (r"\varphi", r"a turning angle: of $\sym{H}$ (instability slide), of the basis (Jacobi slide), of the hinge (3D)"),
        (r"\alpha_k,\ \lambda_k", r"Theorem 8.1: ordered eigenvalues of $\sym{A1}$ and $\sym{Lambda1}$"),
    ]
