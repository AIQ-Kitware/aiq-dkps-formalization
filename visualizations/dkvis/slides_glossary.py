"""Slides: the notation glossary.

Full deck, last part.  One place that lists every symbol the decks use, in its
role color, with its meaning and where it appears, so the notation on every
other slide can be checked against it.  When a slide changes a symbol, change
the entry here in the same commit.
"""

from __future__ import annotations

from manim import DOWN, LEFT, RIGHT, UP, FadeIn, Line, Rectangle, VGroup

from dkvis.slide_style import (
    EXACT,
    FG,
    GAP,
    MUTED,
    PANEL,
    RESID,
    SINE,
    TRIAL,
    DeckSlide,
    math,
    para,
    tex,
)

COL_X = (-6.85, 0.2)
SYMBOL_W = 1.45
MEANING_W = 5.0


def entry(symbol: str, color: str, meaning: str) -> VGroup:
    """One glossary row: the symbol in its role color, then its meaning."""
    sym = math(symbol, size=29, color=color)
    if sym.width > SYMBOL_W:
        sym.scale_to_fit_width(SYMBOL_W)
    text = para(meaning, width=MEANING_W, size=20)
    text.move_to([sym.get_left()[0] + SYMBOL_W + 0.15, sym.get_top()[1], 0], aligned_edge=UP + LEFT)
    return VGroup(sym, text)


def glossary_column(rows: list[tuple[str, str, str]], x: float, top: float, buff: float = 0.2) -> VGroup:
    col = VGroup(*[entry(*row) for row in rows]).arrange(DOWN, aligned_edge=LEFT, buff=buff)
    col.move_to([x, top, 0], aligned_edge=[-1, 1, 0])
    return col


class GlossarySlide(DeckSlide):
    depth = "**"
    LEFT: list[tuple[str, str, str]] = []
    RIGHT: list[tuple[str, str, str]] = []
    LEFT_HEAD = ""
    RIGHT_HEAD = ""
    NOTES = ""

    def header(self, text: str, x: float, top: float) -> VGroup:
        head = tex(rf"\textbf{{{text}}}", size=21, color=MUTED).move_to([x, top, 0], aligned_edge=[-1, 1, 0])
        rule = Line([x, head.get_bottom()[1] - 0.06, 0], [x + SYMBOL_W + MEANING_W + 0.15, head.get_bottom()[1] - 0.06, 0],
                    color=MUTED, stroke_width=1)
        return VGroup(head, rule)

    def columns(self, top: float) -> VGroup:
        out = VGroup()
        for x, head, rows in ((COL_X[0], self.LEFT_HEAD, self.LEFT), (COL_X[1], self.RIGHT_HEAD, self.RIGHT)):
            h = self.header(head, x, top)
            out.add(VGroup(h, glossary_column(rows, x, h.get_bottom()[1] - 0.15)))
        return out

    def body(self) -> None:
        self.say(self.NOTES)
        self.play(FadeIn(self.columns(self.content_top - 0.1)))


class G01Matrices(GlossarySlide):
    title = r"Notation (1/3): colors, matrices, subspaces"
    kicker = r"Each symbol in its role color; the decks should use them exactly this way"
    NOTES = (
        "The glossary. Colors carry roles: blue for the target, the exact eigenspace; amber for the trial; pink "
        "for angles; green for residuals; violet for gaps; gray for the unwanted part. Then the matrices and the "
        "subspaces, with one meaning each."
    )
    LEFT_HEAD = "Matrices and operators"
    LEFT = [
        (r"A", FG, r"the old (unperturbed) self-adjoint matrix or operator"),
        (r"H", FG, r"the perturbation, self-adjoint; $\norm{H}_2$ is its size"),
        (r"\tilde A=A+H", FG, r"the matrix we have. Lean's \texttt{A}; Davis and Kahan's $A+H$"),
        (r"H_0,\ B,\ H_1", FG, r"blocks of $H$ in $A$'s eigenbasis: within the wanted part, the coupling "
                                r"between wanted and unwanted, within the unwanted part"),
        (r"A_0", TRIAL, r"the trial matrix on $V$: $E_0^*\tilde AE_0$ (Rayleigh--Ritz), or $A$'s wanted block "
                        r"$E_0^*AE_0$ in the perturbation reading"),
        (r"A_1", FG, r"$A$'s unwanted block, $E_1^*AE_1$ (Part 3)"),
        (r"\Lambda_0,\ \Lambda_1", EXACT, r"$\tilde A$ on $U$ and on $U^\perp$: $\tilde AF_j=F_j\Lambda_j$"),
    ]
    RIGHT_HEAD = "Subspaces, bases, vectors"
    RIGHT = [
        (r"U", EXACT, r"the target subspace: spanned by $\tilde A$'s wanted eigenvectors (exact, usually unknown)"),
        (r"F_0,\ F_1", EXACT, r"orthonormal bases of $U$ and $U^\perp$"),
        (r"V", TRIAL, r"the trial subspace, e.g.\ from an eigensolver"),
        (r"E_0,\ E_1", TRIAL, r"orthonormal bases of $V$ and $V^\perp$"),
        (r"v", TRIAL, r"a single trial vector, $V=\operatorname{span}(v)$"),
        (r"P,\ Q", FG, r"projectors onto $V$ and $U$: $P=E_0E_0^*$, $Q=F_0F_0^*$"),
        (r"u,\ w", EXACT, r"a wanted and an unwanted eigenvector of $\tilde A$ (``Why it is true''); $w$ drawn gray"),
        (r"f_j", EXACT, r"eigenvectors of $\tilde A$, $\tilde Af_j=\lambda_jf_j$"),
    ]

    def body(self) -> None:
        roles = [
            (EXACT, "target, exact"), (TRIAL, "trial"), (SINE, "angle"), (RESID, "residual"),
            (GAP, "gap"), (FG, "matrices"), (MUTED, "unwanted"),
        ]
        swatches = VGroup()
        for color, name in roles:
            box = Rectangle(width=0.32, height=0.22, stroke_width=0, fill_color=color, fill_opacity=1)
            swatches.add(VGroup(box, tex(name, size=19, color=color).next_to(box, RIGHT, buff=0.1)))
        swatches.arrange(RIGHT, buff=0.35).move_to([0, self.content_top - 0.2, 0], aligned_edge=[0, 1, 0])
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
        (r"\lambda,\ \lambda_j", FG, r"eigenvalues of $\tilde A$; $\lambda_0,\lambda_1$ its two eigenvalues in "
                                     r"the $2\times2$ examples"),
        (r"a_0,\ a_1", TRIAL, r"the two eigenvalues of the old $A$ in the $2\times2$ examples"),
        (r"\mu_j", TRIAL, r"trial values: the eigenvalues of $A_0$ (Ritz values)"),
        (r"\rho", TRIAL, r"the Rayleigh quotient $v^*\tilde Av$ of a unit trial vector"),
        (r"[\beta,\alpha]", FG, r"an interval containing the spectrum of $A_0$ (or of the separated block)"),
        (r"\delta", GAP, r"the gap: how far the separated spectra are apart; which spectra depends on the theorem"),
        (r"g", GAP, r"the gap between the two eigenvalues of $A$ in the $2\times2$ examples"),
    ]
    RIGHT_HEAD = "Angles and residuals"
    RIGHT = [
        (r"\theta,\ \theta_j", SINE, r"the angle(s) between $V$ and $U$: the principal angles, each in "
                                    r"$[0^\circ,90^\circ]$"),
        (r"\Theta_0", SINE, r"the directed angle operator: the angles from $V$ to $U$, one per direction of $V$"),
        (r"\Theta", SINE, r"the ambient angle operator of the whole rotation; each nonzero angle appears twice"),
        (r"\sin\Theta_0", SINE, r"its sine: $\norm{\sin\Theta_0}=\norm{(I-Q)E_0}=\norm{F_1^*E_0}$; "
                                r"$\norm{\sin\Theta}=\norm{P-Q}$"),
        (r"S", SINE, r"$(I-F_0F_0^*)E_0$, the rectangular block with the norms of $\sin\Theta_0$"),
        (r"r", RESID, r"the residual of one vector: $\tilde Av-\rho v$"),
        (r"R", RESID, r"the residual of a subspace: $\tilde AE_0-E_0A_0$; $=HE_0$ in the perturbation reading"),
        (r"X", SINE, r"the overlap matrix $F_1^*E_0$ of the Sylvester equation, $\norm{X}=\norm{\sin\Theta_0}$"),
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
        (r"\norm{\cdot}", FG, r"any unitarily invariant norm: $\norm{UKW}=\norm{K}$ for unitary $U$, $W$"),
        (r"\norm{\cdot}_2,\ \norm{\cdot}_F", FG, r"the operator norm (largest singular value) and the Frobenius "
                                                 r"norm"),
        (r"\norm{\cdot}_\nu", FG, r"the Ky Fan $\nu$-norm: the sum of the $\nu$ largest singular values"),
        (r"N", FG, r"a unitarily invariant norm as a named object (Lean statements, Proposition 4.4)"),
        (r"\varepsilon", FG, r"the size of $H$ in the examples, $\norm{H}_2=\varepsilon$ (often $0.12$)"),
        (r"b", FG, r"the coupling entry of the $2\times2$ matrix $\begin{pmatrix}a_0&b\\b&a_1\end{pmatrix}$"),
        (r"t", FG, r"a value of the bound $\norm{R}/\delta$, used on the plots of Part 3"),
    ]
    RIGHT_HEAD = "Local to one part or proof"
    RIGHT = [
        (r"\mathcal R", FG, r"the direct rotation from $V$ to $U$ (Part 3); its square turns by $2\Theta$"),
        (r"R,\ W", FG, r"Part 4 only: the direct rotation and a competing orthogonal map, $W(U)=V$"),
        (r"X=P-P^\perp", FG, r"the reflection across $V$ in the $\sin2\Theta$ proof (Part 3)"),
        (r"C_0,\ C_1,\ J_0", FG, r"the cosine blocks and the partial isometry of the direct rotation (Part 3 proofs)"),
        (r"x_j,\ y_j", FG, r"a pair of principal vectors: $x_j$ on the trial side, $y_j$ on the unwanted side"),
        (r"\varphi", FG, r"a turning angle: of $H$ (instability slide), of the basis (Jacobi slide), of the hinge (3D)"),
        (r"\alpha_k,\ \lambda_k", FG, r"Theorem 8.1: ordered eigenvalues of $A_1$ and $\Lambda_1$"),
    ]
