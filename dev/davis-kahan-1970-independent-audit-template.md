# Davis--Kahan 1970 independent statement audit packet

This packet is organized one source claim at a time. The TeX excerpts are the exact registered mathematical passages copied from the maintained modernized transcription. The census status is a claim to audit, not evidence of semantic fidelity.

Compiler evidence and mathematical-source fidelity are intentionally separate. A compiler certificate establishes that registered declarations elaborate against `DavisKahan.All`; the auditor must decide whether their types jointly match the source passage.

- Statement map: `dev/davis-kahan-1970-statement-map.json`
- Exact source register: `prose/distilled_literature/DavisKahan1970_exact_source_register.tex`
- Census: `dev/davis-kahan-1970-full-source-census.json`
- Registered rows: **49**
- Mathematical completion obligations: **45**
- Compiler certificate: **not supplied**. The theorem-type boxes below are placeholders; do not infer compilation from this static packet.

## Verdict vocabulary

Use one of: **PASS exact**, **PASS refuted**, **FAIL scope**, **FAIL conclusion**, **FAIL missing clause**, **FAIL source register**, or **UNCERTAIN**.

At the end, separately list any mathematical claim found in the source excerpts or surrounding source context that is not represented by a row in the register.

## 1. S1-block-residual — Two reducing decompositions and the residual

- **Source anchor:** Section 1, equations (1.1)–(1.8)
- **Source kind:** `construction`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `db69a79e5384cf5ad0236a1f73abdccf8d9d8cc75422df74c0583d21f77fa816`
- **Private-transcription provenance lines:** `[[202, 204], [241, 315], [461, 503]]`

### Exact registered source passage

~~~~tex
Throughout the paper, $\Hilbert$ will denote a separable Hilbert space and its vectors will be denoted by $x,y$, etc.; the inner product of $x$ with $y$, often written $(x,y)$, will here be written $y^{*}x$.
(On the other hand, $[x,y]$ will denote the linear subspace spanned by $x$ and $y$.\,)
It will usually not matter whether the space is real or complex, or whether its dimensionality is finite.

Consequently we define
\[
  E_0:\Xspace(E_0)\to\Hilbert,
  \qquad
  E_1:\Xspace(E_1)\to\Hilbert,
\]
isometric mappings of new Hilbert spaces into $\Hilbert$, having ranges $E_0\Xspace(E_0)=P\Hilbert$ and $E_1\Xspace(E_1)=\tP\Hilbert$.
(Here we have introduced the notation $\Xspace(\cdot)$ for the ``source space'' of an isometry.
Later we shall also use the notations $\Null(\cdot)$ for null space and $\Range(\cdot)$ for range; $\Xspace(E_j)=\Range(E_j^{*})$.\,)
Now $E_0E_0^{*}=P$ and $E_1E_1^{*}=\tP$; on the other hand, $E_0^{*}E_0$ is the identity operator on $\Xspace(E_0)$, $E_1^{*}E_0$ is the zero transformation from $\Xspace(E_0)$ to $\Xspace(E_1)$, and so on.
Now we can write $x_0=E_0^{*}x$, $x_1=E_1^{*}x$, and
\begin{equation*}
  x=(E_0\ E_1)\binom{x_0}{x_1}=E_0x_0+E_1x_1,
  \tag{1.1}\label{eq:1.1}
\end{equation*}
if we want to; or we can simply say $x$ is represented by $\binom{x_0}{x_1}$.
Clearly $(E_0\ E_1)$ is an isometry onto $\Hilbert$, and
\[
  (E_0\ E_1)^{-1}=\binom{E_0^{*}}{E_1^{*}}.
\]

The corresponding notation for operators is
\begin{equation*}
\begin{aligned}
  A&=(E_0\ E_1)
  \begin{pmatrix}A_0&0\\0&A_1\end{pmatrix}
  \binom{E_0^{*}}{E_1^{*}},\\
  H&=(E_0\ E_1)
  \begin{pmatrix}H_0&B^{*}\\B&H_1\end{pmatrix}
  \binom{E_0^{*}}{E_1^{*}}.
\end{aligned}
\tag{1.2}\label{eq:1.2}
\end{equation*}
These equations define the new operators appearing in them; for instance,
$B=E_1^{*}HE_0$, an operator from $\Xspace(E_0)$ to $\Xspace(E_1)$.
The $A_j$ and $H_j$ are automatically Hermitian.
Equations like \eqref{eq:1.1} and \eqref{eq:1.2} can be written more clearly if we agree that the sign $\representedby$ is to be read as ``is represented by.''
Then we write
\[
  x\representedby\binom{x_0}{x_1},
  \qquad
  A\representedby\begin{pmatrix}A_0&0\\0&A_1\end{pmatrix},
  \qquad
  P\representedby\begin{pmatrix}1&0\\0&0\end{pmatrix},
\]
and so on.
The usual rules of matrix multiplication apply; for example,
\[
  PAP\representedby\begin{pmatrix}A_0&0\\0&0\end{pmatrix}
\]
(and neither member here is the same as $A_0$).

When we decompose $\Hilbert$ according to a reducing subspace $Q\Hilbert$ of $A+H$ instead, then we shall want to define new isometries
\[
  F_0:\Xspace(F_0)\to\Hilbert,
  \qquad
  F_1:\Xspace(F_1)\to\Hilbert,
\]
with $F_0F_0^{*}=Q$ and $F_1F_1^{*}=\tQ=1-Q$.
Now the notion of representing operators on $\Hilbert$ by $2\times2$ block matrices becomes treacherous, because there are more ways than one to represent them.
The two ways of representing $A+H$ are
\begin{equation*}
\begin{aligned}
  A+H
  &=(E_0\ E_1)
  \begin{pmatrix}A_0+H_0&B^{*}\\B&A_1+H_1\end{pmatrix}
  \binom{E_0^{*}}{E_1^{*}}\\
  &=(F_0\ F_1)
  \begin{pmatrix}\Lambda_0&0\\0&\Lambda_1\end{pmatrix}
  \binom{F_0^{*}}{F_1^{*}}.
\end{aligned}
\tag{1.3}\label{eq:1.3}
\end{equation*}
Nothing has been said about diagonalizing $A_0$ or $\Lambda_0$; choice of coordinate system in their respective spaces has not come up.
No demand has been made that the reducing projectors $P$ and $Q$ be spectral projectors either; that is, so far $A_0$ may have spectrum in common with $A_1$, or $\Lambda_0$ with $\Lambda_1$.

The numerical analyst also chooses, at each step, an $m\times m$ matrix intended to have eigenvalues approximating $\lambda_1,\ldots,\lambda_m$; this we call $A_0$.
From this is computed the residual
\begin{equation*}
  R=(A+H)E_0-E_0A_0
  \tag{1.8}\label{eq:1.8}
\end{equation*}
(if $E_0=F_0$ and $A_0=\Lambda_0$, then $R=0$).

Any choice of $A_0$ which makes $R$ small will give good approximate eigenvalues.
More explicitly, let the eigenvalues of $A_0$ in some order be $\alpha_1,\ldots,\alpha_m$ (since $m$ is relatively small, think of these also as easily computable).
Kahan has shown~\cite{Kahan1967} that then there exists an ordered $m$-tuple $(\lambda_1,\ldots,\lambda_m)$ of eigenvalues of $A+H$ such that
\[
  \sum_{j=1}^{m}(\alpha_j-\lambda_j)^2
  \leq \norm{R}_{\mathrm{sq}}^2
  \equiv \tr R^{*}R,
  \qquad
  \abs{\alpha_j-\lambda_j}\leq \norm{R}_1
  \quad (j=1,\ldots,m).
\]

Thus in the numerical-analytic interpretation of the problem of rotation of eigenspaces, though the same operator-theoretic notation can be followed, there is a slight difference which will bear on the statements of our theorems.
Instead of comparing a given operator $A+H$ to a simpler operator $A$ on the same space and saying that the difference $H$ between the two is small, we compare the given operator to an operator $A_0$ on a space of lower dimension and say that the residual $R$ is small.
In our notation $A_0$ is isometric-equivalent to a part of $A$ (see \eqref{eq:1.2}), and the numerical analyst would rather talk about that part than about $A_1$, which he does not compute.
Similarly, $R$ is essentially that part of the perturbation $H$ which he does compute.
To see the point of the notation better, the reader may want to check formally from \eqref{eq:1.3} and \eqref{eq:1.8} that $R$, left-multiplied by the isometry $\binom{E_0^{*}}{E_1^{*}}$, gives the first column of
\[
  \begin{pmatrix}H_0&B^{*}\\B&H_1\end{pmatrix},
\]
which represents $H$ (see \eqref{eq:1.2}); or that $R=HE_0$.

In two of our main theorems we shall make hypotheses that the perturbation is off-diagonal.
In one theorem, this means the strong assertion that both the $H_j$ are zero; but the numerical analyst might prefer that nothing be said about the southeast corners of our block matrices; accordingly, another theorem has as its hypothesis of off-diagonality only $H_0=0$.
It is a natural hypothesis because it means that, from the given $A+H$ and the computed vectors $E_0$, he obtains his $A_0$ by the simple rule
\[
  A_0=E_0^{*}(A+H)E_0,
\]
which is the $m\times m$ generalization of what, for $m=1$, is known as the Rayleigh quotient.
This is often a good choice, particularly in view of the fact that
\[
  R^{*}R=H_0^2+B^{*}B,
\]
so that the size of $R$ is minimized when $H_0$ is taken to be zero.
In the operator-theoretic interpretation of the problem we are less likely to have the option of declaring an $H_j$ to be zero.
~~~~

### Semantic audit clauses

- **`S1-block-residual.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Equation1_8`, `TauCeti.DavisKahan1970.equation1_8_eq_perturbation_comp`, `TauCeti.DavisKahan1970.equation1_8_norm_sq_eq_diagonal_add_offDiagonal`, `TauCeti.DavisKahan1970.equation1_8_norm_offDiagonal_le`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Equation1_8`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section1.lean:56`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.equation1_8_eq_perturbation_comp`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section1.lean:66`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.equation1_8_norm_sq_eq_diagonal_add_offDiagonal`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section1.lean:78`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.equation1_8_norm_offDiagonal_le`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section1.lean:96`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan.residual` — DavisKahan/BoundedOperator/Compat.lean:111, DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedKyFan.lean:2648, ForTauCeti/Analysis/InnerProductSpace/Residual/Ritz.lean:59
- `TauCeti.DavisKahan1970.Equation1_8` — DavisKahan/Sources/DavisKahan1970/Section1.lean:56
- `TauCeti.DavisKahan1970.equation1_8_eq_perturbation_comp` — DavisKahan/Sources/DavisKahan1970/Section1.lean:66
- `TauCeti.DavisKahan.Frontier.Section8.residual_eq_comp_subtypeL` — DavisKahan/Frontier/Section8Residual.lean:95
- `TauCeti.DavisKahan1970.equation1_8_norm_sq_eq_diagonal_add_offDiagonal` — DavisKahan/Sources/DavisKahan1970/Section1.lean:78
- `TauCeti.DavisKahan1970.equation1_8_norm_offDiagonal_le` — DavisKahan/Sources/DavisKahan1970/Section1.lean:96
- `TauCeti.DavisKahan.ExactSinTheta.PaperTheorem61Data` — DavisKahan/Sources/DavisKahan1970/SineTheta/Theorem61Universal.lean:44
- `TauCeti.DavisKahan.ExactSinTheta.UnboundedSinThetaData` — DavisKahan/SinTheta/Unbounded/Core.lean:50

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 2. S1-ui-norms — Unitary-invariant norms and Fan dominance

- **Source anchor:** Section 1, equations (1.9)–(1.13)
- **Source kind:** `framework`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `7cbf06e9a54408d0a6644b521befdf01fa99c88e2a0aaeed2378a3468e95773d`
- **Private-transcription provenance lines:** `[[505, 583]]`

### Exact registered source passage

~~~~tex
The measures we have chosen to use for magnitudes of operators are arbitrary unitary-invariant norms.
There are three good surveys~\cite[Chaps.~II--III]{GohbergKrein1965},\cite{Mirsky1960},\cite{Schatten1960} of the theory of such norms.
However, we think it will be convenient to collect here some of the leading points.

The symbol $\norm{\cdot}$, applied to bounded operators $K$ from one Hilbert space to the same or another Hilbert space, stands for a norm which, beside having the usual properties
\[
\begin{gathered}
  \norm{K}\geq 0,
  \qquad
  \norm{K}=0\Longleftrightarrow K=0,\\
  \norm{\lambda K}=\abs{\lambda}\norm{K},
  \qquad
  \norm{K+L}\leq \norm{K}+\norm{L},
\end{gathered}
\]
is unitary-invariant in the sense that
\begin{equation*}
  \norm{VKW}=\norm{K}
  \tag{1.9}\label{eq:1.9}
\end{equation*}
whenever $V$ and $W$ are unitary operators (on the respective spaces).

\emph{Normalization.}
We assume that $\norm{uv^{*}}=\norm{u}\,\norm{v}$ for the operator $uv^{*}$ of rank $1$.
(If this holds for one choice of nonzero $u$ and $v$, it holds for all.\,)

\emph{Compatibility.}
If $W$ is a contraction ($\norm{Wx}\leq\norm{x}$ for all $x$) and $V$ is a contraction, then $\norm{VKW}\leq\norm{K}$.
This follows easily from \eqref{eq:1.10} below.

We recall that, for compact $K$, the ``singular values'' $\kappa_1\geq\kappa_2\geq\cdots$ of $K$ are the square roots of the eigenvalues of $K^{*}K$.
These are the same as the eigenvalues of $KK^{*}$, except perhaps for striking out a certain number of zeros.
Now it follows from \eqref{eq:1.9} that for any unitary-invariant norm, the value of $\norm{K}$ depends only on the nonzero singular values of $K$.

\emph{Minimax characterization of singular values.}
\begin{equation*}
  \kappa_k=\inf_{\mathcal S}\ \sup_x \norm{Kx},
  \tag{1.10}\label{eq:1.10}
\end{equation*}
where the infimum is over $(k-1)$-dimensional subspaces $\mathcal S$ of the domain space, and the supremum is over unit vectors $x\perp\mathcal S$.
In particular, $\kappa_1$ is equal to the bound norm of $K$, which we write $\norm{K}_1$, and we could write instead of \eqref{eq:1.10} that
\[
  \kappa_k=\inf_{\mathcal S}\norm{K\vert_{\mathcal S^{\perp}}}_1.
\]
These formulations are applicable to general bounded operators, not only compact ones, but for noncompact operators it might be more appropriate to deal instead with the spectral multiplicity function~\cite{Halmos1951} of $K^{*}K$.
Although we shall not assume our operators compact in most of this paper, we believe the most important applications are to compact operators.

Every unitary-invariant norm is obtained as a ``symmetric gauge function'' of the singular values; the converse also holds.
For the details, see the references cited.

One of the most tractable of these norms is the Hilbert--Schmidt norm or square norm $\norm{\cdot}_{\mathrm{sq}}$:
\[
  \norm{K}_{\mathrm{sq}}^2=\sum_k\kappa_k^2=\tr K^{*}K.
\]
Particular unitary-invariant norms are
\begin{equation*}
  \norm{K}_{\nu}=\kappa_1+\kappa_2+\cdots+\kappa_{\nu},
  \qquad \nu=1,2,\ldots,
  \tag{1.11}\label{eq:1.11}
\end{equation*}
the sums of the $\nu$ highest singular values (whether or not there are that many nonzero ones).
These include the bound norm $\norm{\cdot}_1$.
The norms \eqref{eq:1.11} play a distinguished role: $K$ and $L$ being two operators, the inequality $\norm{K}\leq\norm{L}$ holds for arbitrary unitary-invariant norms if and only if it holds for all the norms $\norm{\cdot}_{\nu}$ (theorem of Ky Fan~\cite[Chap.~III, Section~3]{GohbergKrein1965}).

The following analogue of the Rayleigh--Ritz principle therefore becomes interesting:
\begin{equation*}
  \norm{K}_{\nu}=\sup_{\Omega}\norm{K\Omega}_{\nu},
  \tag{1.12}\label{eq:1.12}
\end{equation*}
the supremum being over all projectors $\Omega$ onto $\nu$-dimensional subspaces.
For $\nu=1$ this is evident, but even for higher $\nu$ it is readily reduced to familiar statements.
We shall also use the alternative form
\begin{equation*}
  \norm{K}_{\nu}
  =\sup_{\Omega,\Upsilon}\norm{\Upsilon K\Omega}_{\nu}
  =\sup \RePart\sum_{k=1}^{\nu}y_k^{*}Kx_k,
  \tag{1.13}\label{eq:1.13}
\end{equation*}
the first supremum being over pairs of $\nu$-projectors $\Omega,\Upsilon$, and the second supremum being over all orthonormal $\nu$-tuples $\{x_1,\ldots,x_{\nu}\}$ and all orthonormal $\nu$-tuples $\{y_1,\ldots,y_{\nu}\}$.
~~~~

### Semantic audit clauses

- **`S1-ui-norms.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm`, `TauCeti.DavisKahan.ExactSinTheta.paperKyFanNorm`, `TauCeti.DavisKahan1970.equation1_12`, `TauCeti.DavisKahan1970.equation1_13_compressions`, `TauCeti.DavisKahan1970.equation1_13_reSum`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SineTheta/FiniteMultiplicity.lean:266`, `DavisKahan/Sources/DavisKahan1970/SineTheta/FiniteMultiplicity.lean:280`, `DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:55`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan.ExactSinTheta.paperKyFanNorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Ideals/KyFanNorm.lean:209`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.equation1_12`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section1UnitaryInvariantNorms.lean:141`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.equation1_13_compressions`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section1UnitaryInvariantNorms.lean:218`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.equation1_13_reSum`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section1UnitaryInvariantNorms.lean:263`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm` — DavisKahan/Sources/DavisKahan1970/SineTheta/FiniteMultiplicity.lean:266, DavisKahan/Sources/DavisKahan1970/SineTheta/FiniteMultiplicity.lean:280, DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNorm.lean:55
- `TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm.prefixGauge_le_of_all_kyFan_le_hetero` — DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/UnitaryInvariantNormLaws.lean:195
- `TauCeti.DavisKahan.ExactSinTheta.paperKyFanNorm` — DavisKahan/Sources/DavisKahan1970/Ideals/KyFanNorm.lean:209
- `TauCeti.DavisKahan.ExactSinTheta.paperKyFanNorm_gauge` — DavisKahan/Sources/DavisKahan1970/Ideals/KyFanNorm.lean:303
- `TauCeti.DavisKahan.ExactSinTheta.paperKyFanNorm_extendedGauge` — DavisKahan/Sources/DavisKahan1970/Ideals/KyFanNorm.lean:269
- `TauCeti.DavisKahan.ExactSinTheta.all_kyFan_le_of_every_paperNorm_extendedGauge_le` — DavisKahan/Sources/DavisKahan1970/Ideals/KyFanNorm.lean:319
- `TauCeti.DavisKahan.ExactSinTheta.all_mul_kyFan_le_of_every_paperNorm_gauge_le` — DavisKahan/Sources/DavisKahan1970/Ideals/KyFanNorm.lean:338
- `TauCeti.DavisKahan.ExactSinTheta.re_sum_inner_map_le_kyFanApproximationGauge` — DavisKahan/DoubleAngle/KyFanOrthonormal.lean:44
- `TauCeti.DavisKahan1970.equation1_12` — DavisKahan/Sources/DavisKahan1970/Section1UnitaryInvariantNorms.lean:141
- `TauCeti.DavisKahan1970.equation1_12_gauge_comp_starProjection_le` — DavisKahan/Sources/DavisKahan1970/Section1UnitaryInvariantNorms.lean:94
- `TauCeti.DavisKahan1970.equation1_13_compressions` — DavisKahan/Sources/DavisKahan1970/Section1UnitaryInvariantNorms.lean:218
- `TauCeti.DavisKahan1970.equation1_13_reSum` — DavisKahan/Sources/DavisKahan1970/Section1UnitaryInvariantNorms.lean:263
- `TauCeti.DavisKahan1970.equation1_13_gauge_starProjection_comp_le` — DavisKahan/Sources/DavisKahan1970/Section1UnitaryInvariantNorms.lean:109
- `TauCeti.ApproximationNumber.exists_orthonormal_kyFanApproximationGauge_sub_le_re_sum_inner` — ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean:716
- `TauCeti.ApproximationNumber.exists_orthonormal_kyFanApproximationGauge_sub_le_re_sum_inner_complex` — ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean:834
- `TauCeti.RectangularUnitarilyInvariantSeminorm.exists_orthonormal_re_sum_inner_map_eq_rectangularKyFanSum` — ForTauCeti/Analysis/InnerProductSpace/RectangularUnitarilyInvariantSeminorm/Instances.lean:472
- `ContinuousLinearMap.approximationNumber_comp_eq_of_leftInverse` — ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean:492
- `ContinuousLinearMap.kyFanGauge_comp_eq_of_leftInverse` — ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/KyFan.lean:159
- `TauCeti.ApproximationNumber.kyFanApproximationGauge_comp_eq_of_leftInverse` — ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean:673

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 3. S2-sin-theta — Single-angle sine theorem

- **Source anchor:** Section 2, sin theta theorem
- **Source kind:** `unnumbered_theorem`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `21065969e0e5f2a4d5c4d48143b2464dc5e8d974ca80a53196f91f0fd7db57aa`
- **Private-transcription provenance lines:** `[[719, 725]]`

### Exact registered source passage

~~~~tex
\begin{unnumberedtheorem}[The $\sin\theta$ theorem]
Assume there is an interval $[\beta,\alpha]$ and a $\delta>0$ such that the spectrum of $A_0$ lies entirely in $[\beta,\alpha]$ while that of $\Lambda_1$ lies entirely outside of $\,]\beta-\delta,\alpha+\delta[\,$ (or such that the spectrum of $\Lambda_1$ lies entirely in $[\beta,\alpha]$ while that of $A_0$ lies entirely outside of $\,]\beta-\delta,\alpha+\delta[\,$).
Then for every unitary-invariant norm,
\[
  \delta\norm{\sin\angles_0}\leq\norm{R}.
\]
\end{unnumberedtheorem}
~~~~

### Semantic audit clauses

- **`S2-sin-theta.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.sinTheta`, `TauCeti.DavisKahan1970.sinTheta_real_exactPaper`, `TauCeti.DavisKahan1970.generalizedSinTheta`, `TauCeti.DavisKahan1970.generalizedSinTheta_real_exactPaper`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.sinTheta`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/GeneralSinTheta.lean:53`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.sinTheta_real_exactPaper`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:98`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.generalizedSinTheta`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/GeneralSinTheta.lean:40`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.generalizedSinTheta_real_exactPaper`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:109`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.sinTheta` — DavisKahan/Sources/DavisKahan1970/GeneralSinTheta.lean:53
- `TauCeti.DavisKahan1970.generalizedSinTheta` — DavisKahan/Sources/DavisKahan1970/GeneralSinTheta.lean:40
- `TauCeti.DavisKahan1970.sinTheta_real_exactPaper` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:98
- `TauCeti.DavisKahan1970.generalizedSinTheta_real_exactPaper` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:109

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 4. S2-tan-theta — Single-angle tangent theorem

- **Source anchor:** Section 2, tan theta theorem
- **Source kind:** `unnumbered_theorem`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `0958988cf989bf4bbc6ca34699d7b28cda3b68be4e455e12b43a4ad712b2c9a0`
- **Private-transcription provenance lines:** `[[738, 747]]`

### Exact registered source passage

~~~~tex
\begin{unnumberedtheorem}[The $\tan\theta$ theorem]
Assume there is an interval $[\beta,\alpha]$ and a $\delta>0$ such that the spectrum of $A_0$ lies entirely in $[\beta,\alpha]$ while that of $\Lambda_1$ lies entirely in $[\alpha+\delta,\infty[$.
Assume further that $H_0=0$.
Then for every unitary-invariant norm,
\[
  \delta\norm{\tan\angles_0}\leq\norm{R},
  \qquad
  \delta\norm{\tan\angles}\leq\norm{H}.
\]
\end{unnumberedtheorem}
~~~~

### Semantic audit clauses

- **`S2-tan-theta.directed`:** Directed conclusion: delta * ||tan Theta_0|| <= ||R||.
  - Review declarations: `TauCeti.DavisKahanTheory.partIII_tanTheta_ritzResidual_uiNorm`
- **`S2-tan-theta.ambient`:** Ambient conclusion: delta * ||tan Theta|| <= ||H||, with the ambient angle rather than Theta_0.
  - Review declarations: `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm`, `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_real`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahanTheory.partIII_tanTheta_ritzResidual_uiNorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/PartIII.lean:119`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan.Section2.theorem6_3_perturbation_infiniteTrial`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section2TanThetaPerturbation.lean:175`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:1186`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:175`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:1275`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahanTheory.partIII_tanTheta_ritzResidual_uiNorm` — DavisKahan/Sources/DavisKahan1970/PartIII.lean:119
- `TauCeti.DavisKahanExt.tanTheta_spectrum` — DavisKahan/TanTheta/Spectrum.lean:224
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_generalizedTanTheta_of_formBounds_equalRank` — DavisKahan/TanTheta/Theorem63FiniteSource.lean:1151
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_generalizedTanTheta_equalRank_spectral` — DavisKahan/TanTheta/Theorem63FiniteSource.lean:1174
- `TauCeti.DavisKahan.Section2.theorem63Residual_eq_neg_of_invariant` — DavisKahan/Sources/DavisKahan1970/Section2TanThetaPerturbation.lean:69
- `TauCeti.DavisKahan.Section2.theorem6_3_perturbation_equalRank` — DavisKahan/Sources/DavisKahan1970/Section2TanThetaPerturbation.lean:140
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_infiniteTrial_spectral_exists` — DavisKahan/TanTheta/Theorem63InfiniteTrial.lean:871
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_infiniteTrial_of_formBounds_exists` — DavisKahan/TanTheta/Theorem63InfiniteTrial.lean:744
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_all_kyFan_core_infiniteTrial` — DavisKahan/TanTheta/Theorem63InfiniteTrial.lean:467
- `TauCeti.DavisKahan.Section2.theorem6_3_perturbation_infiniteTrial` — DavisKahan/Sources/DavisKahan1970/Section2TanThetaPerturbation.lean:175
- `TauCeti.DavisKahanExt.paperTanAngleOperatorC` — DavisKahan/Geometry/Angle/PaperTanAngle.lean:76
- `TauCeti.DavisKahanExt.paperCos_mul_paperTan` — DavisKahan/Geometry/Angle/PaperTanAngle.lean:223
- `TauCeti.ApproximationNumber.approximationNumber_le_of_gramResolvent` — ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/GramResolvent.lean:197
- `TauCeti.DavisKahan1970.twoProjection_anticommutator` — DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:129
- `TauCeti.DavisKahan1970.offDiagonal_sq` — DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:247
- `TauCeti.DavisKahan1970.paperProjectorDifference` — DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:366
- `TauCeti.DavisKahan1970.paperSecantSquared` — DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:372
- `TauCeti.DavisKahan1970.paperTanBlockRepresentative` — DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:378
- `TauCeti.DavisKahan1970.paperTanBlockRepresentative_mul_self` — DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:688
- `TauCeti.DavisKahan1970.paperTanAngleOperatorC_eq_modulus_blockRepresentative` — DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:740
- `TauCeti.DavisKahan1970.gramOperator_lowerCorner_moebius` — DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:927
- `TauCeti.DavisKahan1970.approximationNumber_lowerCorner_le` — DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:1021
- `TauCeti.DavisKahan1970.corner_all_kyFan` — DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:1093
- `TauCeti.DavisKahan1970.tanTheta_wholeSpace_all_kyFan` — DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:1117
- `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm` — DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:1186
- `TauCeti.DavisKahanExt.paperTanAngleOperatorR` — DavisKahan/Geometry/Angle/PaperOperatorAngleReal.lean:127
- `TauCeti.DavisKahanExt.complexify_paperTanAngleOperatorR` — DavisKahan/Geometry/Angle/PaperOperatorAngleReal.lean:164
- `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_real` — DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:175
- `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real_infinite` — DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:457
- `TauCeti.DavisKahan1970.theorem6_3_all_kyFan_core_infiniteTrial_real` — DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:189
- `TauCeti.DavisKahan1970.theorem63DirectedSineBlockReal` — DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:54
- `TauCeti.DavisKahan1970.theorem63ResidualReal` — DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:60
- `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real` — DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:418
- `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent` — DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:1275
- `TauCeti.DavisKahan1970.tanTheta_wholeSpace_all_kyFan_of_crossedDefectsEquivalent` — DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:1254
- `TauCeti.DavisKahan1970.norm_sinAngleOperatorC_lt_one_of_crossedDefectsEquivalent` — DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:1229
- `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real_spectral` — DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:492
- `TauCeti.DavisKahan1970.tanTheta_directed_perturbation_paperUINorm_real` — DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:607
- `TauCeti.DavisKahan1970.theorem63ResidualReal_eq_neg_of_invariant` — DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:536
- `TauCeti.DavisKahan1970.approximationSingularValue_theorem63ResidualReal_le_of_invariant` — DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:559

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 5. S2-sin-two-theta — Double-angle sine theorem

- **Source anchor:** Section 2, sin 2 theta theorem
- **Source kind:** `unnumbered_theorem`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `03db6ca98f2073a4f98a819b9a9460fb753e5587e78b8949b56a0668291fc4fb`
- **Private-transcription provenance lines:** `[[753, 761]]`

### Exact registered source passage

~~~~tex
\begin{unnumberedtheorem}[The $\sin 2\theta$ theorem]
Assume there is an interval $[\beta,\alpha]$ and a $\delta>0$ such that the spectrum of $\Lambda_0$ lies entirely in $[\beta,\alpha]$ while that of $\Lambda_1$ lies entirely outside of $\,]\beta-\delta,\alpha+\delta[\,$.
Then for every unitary-invariant norm,
\[
  \delta\norm{\sin 2\angles_0}\leq2\norm{R},
  \qquad
  \delta\norm{\sin 2\angles}\leq2\norm{H}.
\]
\end{unnumberedtheorem}
~~~~

### Semantic audit clauses

- **`S2-sin-two-theta.directed`:** Directed conclusion: delta * ||sin(2 Theta_0)|| <= 2 ||R||.
  - Review declarations: `TauCeti.DavisKahanTheory.partIII_sinTwoTheta_uiNorm`
- **`S2-sin-two-theta.ambient`:** Ambient conclusion: delta * ||sin(2 Theta)|| <= 2 ||H||.
  - Review declarations: `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm`, `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm_real`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahanTheory.partIII_sinTwoTheta_uiNorm`

Source location candidates: `Challenge/MathlibPending/DavisKahanSinTwoTheta/Conformance.lean:28`, `DavisKahan/Sources/DavisKahan1970/PartIII.lean:150`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SinTwoThetaWholeSpace.lean:723`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:217`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:166`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:344`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahanTheory.partIII_sinTwoTheta_uiNorm` — Challenge/MathlibPending/DavisKahanSinTwoTheta/Conformance.lean:28, DavisKahan/Sources/DavisKahan1970/PartIII.lean:150
- `TauCeti.DavisKahan.sinTwoTheta_addBounded_of_spectrum_gap` — DavisKahan/DoubleAngle/UnboundedIdeal.lean:509
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:166
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:254
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative_real` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:344
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative_real` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:404
- `TauCeti.DavisKahan1970.sinTwoTheta_addBounded_paperUINorm_real` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:518
- `TauCeti.DavisKahan1970.sinTwoTheta_reflectionResidual_paperUINorm_real` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:482
- `TauCeti.DavisKahan.sinTwoTheta_addBounded_gauge_real` — DavisKahan/DoubleAngle/RealUnboundedIdeal.lean:421
- `TauCeti.DavisKahan.sinTwoTheta_reflectionResidual_gauge_real` — DavisKahan/DoubleAngle/RealUnboundedIdeal.lean:180
- `TauCeti.DavisKahanExt.sinTwoTheta_perturbation` — DavisKahan/InfiniteDimensional/DoubleAngle.lean:937
- `TauCeti.DavisKahanExt.sinTwoTheta_generalSeparation` — DavisKahan/InfiniteDimensional/DoubleAngle.lean:970
- `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm` — DavisKahan/Sources/DavisKahan1970/SinTwoThetaWholeSpace.lean:723
- `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm_real` — DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:217
- `TauCeti.DavisKahanExt.paperSinTwoAngleOperatorR` — DavisKahan/Geometry/Angle/PaperOperatorAngleReal.lean:122
- `TauCeti.DavisKahanExt.complexify_paperSinTwoAngleOperatorR` — DavisKahan/Geometry/Angle/PaperOperatorAngleReal.lean:156
- `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_all_kyFan` — DavisKahan/Sources/DavisKahan1970/SinTwoThetaWholeSpace.lean:364
- `TauCeti.DavisKahan1970.symmetric_sinTheta_spectrum_all_kyFan` — DavisKahan/Sources/DavisKahan1970/SinTwoThetaWholeSpace.lean:201
- `TauCeti.DavisKahanExt.paperSinTwoAngleOperatorC_eq_modulus_starProjection_sub` — DavisKahan/Geometry/Angle/PaperDoubleAngle.lean:195
- `TauCeti.DavisKahan.norm_sinTwoThetaIdealBlock_real` — DavisKahan/DoubleAngle/RealAngleIdentification.lean:141
- `TauCeti.DavisKahan.sinTwoThetaIdealBlock_eq_comp` — DavisKahan/DoubleAngle/RealAngleIdentification.lean:103
- `TauCeti.DavisKahan.complexify_sinTwoThetaIdealBlock` — DavisKahan/DoubleAngle/RealAngleIdentification.lean:126
- `TauCeti.DavisKahanExt.norm_paperSinTwoAngleOperatorC_eq_norm_sinTwoAngleOperatorC` — DavisKahan/DoubleAngle/RealAngleIdentification.lean:68
- `TauCeti.DavisKahan1970.norm_sinTwoThetaBlock_real` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:111
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_opNorm_real` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:564
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_reflectionResidual_opNorm_real` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:569
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative_unequalDimension` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:293
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative_real_unequalDimension` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:373
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative_real_unequalDimension` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:436
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative_unequalDimension` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:220

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 6. S2-tan-two-theta — Double-angle tangent theorem

- **Source anchor:** Section 2, tan 2 theta theorem
- **Source kind:** `unnumbered_theorem`
- **Completion obligation:** `true`
- **Census claim:** `compiled_specialization` / `proved_in_build`
- **Registered source excerpt SHA-256:** `13b00134126824e941e6a613a418da4b82b8cf629a7c1c406fa2e5b89eafcdd3`
- **Private-transcription provenance lines:** `[[765, 774]]`

### Exact registered source passage

~~~~tex
\begin{unnumberedtheorem}[The $\tan 2\theta$ theorem]
Assume there is an interval $[\beta,\alpha]$ and a $\delta>0$ such that the spectrum of $A_0$ lies entirely in $[\beta,\alpha]$ while that of $A_1$ lies entirely in $[\alpha+\delta,\infty[$.
Assume further that $H_0=0$, $H_1=0$.
Then for every unitary-invariant norm,
\[
  \delta\norm{\tan 2\angles_0}\leq2\norm{R},
  \qquad
  \delta\norm{\tan 2\angles}\leq2\norm{H}.
\]
\end{unnumberedtheorem}
~~~~

### Semantic audit clauses

- **`S2-tan-two-theta.hypotheses`:** Printed source hypotheses only: ordered spectral gap between A_0 and A_1 plus H_0 = H_1 = 0; no independent pole-exclusion or perturbed-Q-block placement hypothesis.
  - Review declarations: `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_branchFree`
- **`S2-tan-two-theta.directed`:** Directed conclusion: delta * ||tan(2 Theta_0)|| <= 2 ||R|| for every source unitarily invariant norm.
  - Review declarations: `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_all_kyFan`, `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_paperUINorm_arbitrarySubspace`
- **`S2-tan-two-theta.ambient`:** Ambient conclusion: delta * ||tan(2 Theta)|| <= 2 ||H|| for every source unitarily invariant norm, from only the printed hypotheses. This is the currently reopened exact-wrapper obligation.
  - Review declarations: `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_branchFree`, `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahanTheory.partIII_tanTwoTheta_opNorm`

Source location candidates: `Challenge/MathlibPending/DavisKahanTanTwoTheta/Conformance.lean:27`, `DavisKahan/Sources/DavisKahan1970/PartIII.lean:163`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:1500`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:269`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_branchFree`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean:927`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_of_corner`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:1464`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahanTheory.partIII_tanTwoTheta_opNorm` — Challenge/MathlibPending/DavisKahanTanTwoTheta/Conformance.lean:27, DavisKahan/Sources/DavisKahan1970/PartIII.lean:163
- `TauCeti.DavisKahanExt.tanTwoTheta_offDiagonalC_of_weighted_sine` — DavisKahan/TanTwoTheta/BoundedOffDiagonal.lean:143
- `TauCeti.DavisKahan.sharp_paperUnitaryInvariantNorm` — DavisKahan/Sources/DavisKahan1970/SharpIdeal.lean:99
- `TauCeti.DavisKahan.sharp_paperUnitaryInvariantNorm_selectedBranch` — DavisKahan/Sources/DavisKahan1970/SharpIdeal.lean:203
- `TauCeti.DavisKahan.paperFaithful_tanTwoTheta_uiNorm_real` — DavisKahan/InfiniteDimensional/TanTwoTheta/RealPaperFaithful.lean:105
- `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_paperUINorm` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaBranchFree.lean:86
- `TauCeti.DavisKahanTheory.paired_singularVector_gap_inequality` — DavisKahan/DoubleAngle/TanTwoThetaKyFan.lean:146
- `TauCeti.DavisKahanTheory.singularValue_ne_one` — DavisKahan/DoubleAngle/TanTwoThetaBranchFree.lean:111
- `TauCeti.DavisKahanTheory.absDoubleAngleTangent_scalar` — DavisKahan/DoubleAngle/TanTwoThetaBranchFree.lean:135
- `TauCeti.DavisKahanTheory.sum_absDoubleAngleTangent_le` — DavisKahan/DoubleAngle/TanTwoThetaBranchFree.lean:253
- `TauCeti.DavisKahanTheory.absTanTwoTheta0_offDiagonal_le` — DavisKahan/DoubleAngle/TanTwoThetaBranchFree.lean:304
- `TauCeti.DavisKahanTheory.sum_absDoubleAngleTangent_le_of_finiteDimensional_invariantSubspace` — DavisKahan/DoubleAngle/TanTwoThetaKyFanFiniteCarrier.lean:157
- `TauCeti.DavisKahanTheory.kyFan_absTanTwoTheta_le_of_finiteDimensional_invariantSubspace` — DavisKahan/DoubleAngle/TanTwoThetaKyFanFiniteCarrier.lean:555
- `TauCeti.DavisKahanTheory.absTanTwoTheta_offDiagonal_mem_and_gauge_le_of_finiteDimensional_invariantSubspace` — DavisKahan/DoubleAngle/TanTwoThetaKyFanFiniteCarrier.lean:603
- `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_paperUINorm_arbitrarySubspace` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaBranchFree.lean:140
- `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_paperUINorm_real` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaBranchFreeInfiniteReal.lean:120
- `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_kyFan_arbitrarySubspace` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaBranchFree.lean:230
- `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_prefix_arbitrarySubspace` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaBranchFree.lean:235
- `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_uiIdeal_arbitrarySubspace` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaBranchFree.lean:240
- `TauCeti.DavisKahan1970.tanTwoTheta_equation_7_6_approximate` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaBranchFree.lean:216
- `TauCeti.DavisKahan1970.tanTwoTheta_cos_ne_zero_approximate` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaBranchFree.lean:220
- `TauCeti.DavisKahan1970.tanTwoTheta_pole_separation` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaBranchFree.lean:225
- `TauCeti.DavisKahanExt.paperTanTwoAngleOperatorC` — DavisKahan/Geometry/Angle/PaperTanAngle.lean:127
- `TauCeti.DavisKahanExt.spectrum_paperAngleOperatorC_lt_pi_div_four` — DavisKahan/Geometry/Angle/PaperTanAngle.lean:141
- `TauCeti.DavisKahanExt.paperTanTwoAngleOperatorC_nonneg` — DavisKahan/Geometry/Angle/PaperTanAngle.lean:170
- `TauCeti.DavisKahan1970.paperDoubleSecant` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:281
- `TauCeti.DavisKahan1970.paperTanTwoBlockRepresentative` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:287
- `TauCeti.DavisKahan1970.paperTanTwoAngleOperatorC_eq_modulus_blockRepresentative` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:855
- `TauCeti.DavisKahan1970.paperTanTwoBlockRepresentative_lowerBlock` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:1052
- `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_all_kyFan` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:1223
- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_all_kyFan` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:1431
- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:1500
- `TauCeti.DavisKahanExt.paperTanTwoAngleOperatorR` — DavisKahan/Geometry/Angle/PaperOperatorAngleReal.lean:132
- `TauCeti.DavisKahanExt.complexify_paperTanTwoAngleOperatorR` — DavisKahan/Geometry/Angle/PaperOperatorAngleReal.lean:172
- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real` — DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:269
- `TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorC` — DavisKahan/Geometry/Angle/PaperTanAngle.lean:188
- `TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorC_nonneg` — DavisKahan/Geometry/Angle/PaperTanAngle.lean:201
- `TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorC_eq_paperTanTwoAngleOperatorC` — DavisKahan/Geometry/Angle/PaperTanAngle.lean:209
- `TauCeti.DavisKahan1970.isUnit_one_sub_two_mul_paperProjectorDifference_sq_of_cos_two_ne_zero` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:405
- `TauCeti.DavisKahan1970.paperAbsTanTwo_sq_mul_cos_two_sq` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:418
- `TauCeti.DavisKahan1970.paperAbsTanTwoAngleOperatorC_eq_modulus_blockRepresentative` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:808
- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_all_kyFan_of_corner` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:1357
- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_of_corner` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:1464
- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_all_kyFan_branchFree` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean:908
- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_branchFree` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean:927

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 7. S2-sharpness — Best constants and simultaneous equality

- **Source anchor:** Section 2, paragraph after four theorems
- **Source kind:** `source_claim`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `40c1bd8f533c1b0c08d7881fadb8617edfee2fcbfcd63ec6ca8100234a183c6e`
- **Private-transcription provenance lines:** `[[776, 777]]`

### Exact registered source passage

~~~~tex
It was mentioned earlier that the constants in all four theorems are best possible; this is seen from the $2$-dimensional case.
Furthermore, one sees by taking a direct sum of $2$-dimensional examples that, in any one of the theorems, equality in the conclusion can be attained simultaneously for all unitary-invariant norms.
~~~~

### Semantic audit clauses

- **`S2-sharpness.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahanTheory.tanTheta_model_sourceSharpness`, `TauCeti.DavisKahanTheory.tanTwoTheta_model_sourceSharpness`, `TauCeti.DavisKahanTheory.sinTheta_constant_optimal`, `TauCeti.DavisKahanTheory.sinTwoTheta_constant_optimal`, `TauCeti.DavisKahanTheory.single_double_sine_tangent_ratios_tendsto_one`, `TauCeti.DavisKahanTheory.sinTheta_model_equality`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahanTheory.tanTheta_model_sourceSharpness`

Source location candidates: `DavisKahan/FiniteDimensional/Sharpness.lean:2005`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahanTheory.tanTwoTheta_model_sourceSharpness`

Source location candidates: `DavisKahan/FiniteDimensional/Sharpness.lean:2390`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahanTheory.sinTheta_constant_optimal`

Source location candidates: `DavisKahan/FiniteDimensional/Sharpness.lean:1047`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahanTheory.sinTwoTheta_constant_optimal`

Source location candidates: `DavisKahan/FiniteDimensional/Sharpness.lean:1084`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahanTheory.single_double_sine_tangent_ratios_tendsto_one`

Source location candidates: `DavisKahan/FiniteDimensional/Sharpness.lean:1321`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahanTheory.sinTheta_model_equality`

Source location candidates: `DavisKahan/FiniteDimensional/Sharpness.lean:794`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahanTheory.sinTheta_constant_optimal` — DavisKahan/FiniteDimensional/Sharpness.lean:1047
- `TauCeti.DavisKahanTheory.sinTwoTheta_constant_optimal` — DavisKahan/FiniteDimensional/Sharpness.lean:1084
- `TauCeti.DavisKahanTheory.single_double_sine_tangent_ratios_tendsto_one` — DavisKahan/FiniteDimensional/Sharpness.lean:1321
- `TauCeti.DavisKahanTheory.sinTheta_model_equality` — DavisKahan/FiniteDimensional/Sharpness.lean:794
- `TauCeti.DavisKahanTheory.tanTheta_model_equality` — DavisKahan/FiniteDimensional/Sharpness.lean:828
- `TauCeti.DavisKahanTheory.tanTwoTheta_model_equality` — DavisKahan/FiniteDimensional/Sharpness.lean:995
- `TauCeti.DavisKahanTheory.sinTwoTheta_model_operatorNorm_equality` — DavisKahan/FiniteDimensional/Sharpness.lean:866
- `TauCeti.DavisKahanTheory.sinTwoTheta_model_equality` — DavisKahan/FiniteDimensional/Sharpness.lean:936
- `TauCeti.DavisKahanTheory.sinTwoTheta_model_equality_fails_beyond_operatorNorm` — DavisKahan/FiniteDimensional/Sharpness.lean:892
- `TauCeti.DavisKahanTheory.norm_sinTwoAngle_model_eq_norm_sinAngle_doubled` — DavisKahan/FiniteDimensional/Sharpness.lean:976
- `TauCeti.DavisKahanTheory.model_all_four_equalities` — DavisKahan/FiniteDimensional/Sharpness.lean:1129
- `TauCeti.DavisKahanTheory.sinTheta_directSum_model_equality` — DavisKahan/FiniteDimensional/Sharpness.lean:1174
- `TauCeti.DavisKahanTheory.tanTheta_directSum_model_equality` — DavisKahan/FiniteDimensional/Sharpness.lean:1195
- `TauCeti.DavisKahanTheory.sinTwoTheta_directSum_model_equality` — DavisKahan/FiniteDimensional/Sharpness.lean:1219
- `TauCeti.DavisKahanTheory.tanTwoTheta_directSum_model_equality` — DavisKahan/FiniteDimensional/Sharpness.lean:1245
- `TauCeti.DavisKahanTheory.directSum_model_all_four_equalities` — DavisKahan/FiniteDimensional/Sharpness.lean:1277
- `TauCeti.RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum_linearIsometryEquiv` — ForTauCeti/Analysis/InnerProductSpace/RectangularUnitarilyInvariantSeminorm/BlockSum.lean:220
- `TauCeti.RectangularUnitarilyInvariantSeminorm.singularValues_orthogonalBlockSum_congr` — ForTauCeti/Analysis/InnerProductSpace/RectangularUnitarilyInvariantSeminorm/BlockSum.lean:296
- `TauCeti.RectangularUnitarilyInvariantSeminorm.apply_orthogonalBlockSum_eq_of_singularValues_smul_eq` — ForTauCeti/Analysis/InnerProductSpace/RectangularUnitarilyInvariantSeminorm/BlockSum.lean:320
- `TauCeti.DavisKahanTheory.sinTheta_model_isAdmissiblePair` — DavisKahan/FiniteDimensional/Sharpness.lean:1713
- `TauCeti.DavisKahanTheory.sinTheta_perturbation_le_model_equality` — DavisKahan/FiniteDimensional/Sharpness.lean:1738
- `TauCeti.DavisKahanTheory.tanTheta_model_isAdmissiblePair` — DavisKahan/FiniteDimensional/Sharpness.lean:1961
- `TauCeti.DavisKahanTheory.tanTheta_perturbation_le_model_equality` — DavisKahan/FiniteDimensional/Sharpness.lean:1983
- `TauCeti.DavisKahanTheory.sinTwoTheta_model_isAdmissiblePair` — DavisKahan/FiniteDimensional/Sharpness.lean:2107
- `TauCeti.DavisKahanTheory.sinTwoTheta_perturbation_le_model_operatorNorm_equality` — DavisKahan/FiniteDimensional/Sharpness.lean:2143
- `TauCeti.DavisKahanTheory.sinTwoTheta_model_equality_of_admissiblePair` — DavisKahan/FiniteDimensional/Sharpness.lean:2158
- `TauCeti.DavisKahanTheory.tanTwoTheta_model_isAdmissiblePair` — DavisKahan/FiniteDimensional/Sharpness.lean:2352
- `TauCeti.DavisKahanTheory.tanTwoTheta_perturbation_le_model_equality` — DavisKahan/FiniteDimensional/Sharpness.lean:2370
- `TauCeti.DavisKahanTheory.projection_orthogonalBlockSumSubmodule` — DavisKahan/FiniteDimensional/Sharpness.lean:2436, ForTauCeti/Analysis/InnerProductSpace/AngleGeometryBlockSum.lean:138
- `TauCeti.RectangularUnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule` — ForTauCeti/Analysis/InnerProductSpace/RectangularUnitarilyInvariantSeminorm/BlockSum.lean:239
- `TauCeti.RectangularUnitarilyInvariantSeminorm.mem_orthogonalBlockSumSubmodule`
- `TauCeti.RectangularUnitarilyInvariantSeminorm.starProjection_orthogonalBlockSumSubmodule` — ForTauCeti/Analysis/InnerProductSpace/RectangularUnitarilyInvariantSeminorm/BlockSum.lean:262
- `TauCeti.selfAdjointFunctionalCalculus_intertwines` — ForTauCeti/Analysis/InnerProductSpace/SelfAdjointFunctionalCalculus.lean:274
- `TauCeti.RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum_sub`
- `TauCeti.RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum_isSymmetric` — ForTauCeti/Analysis/InnerProductSpace/RectangularUnitarilyInvariantSeminorm/BlockSum.lean:156
- `TauCeti.RectangularUnitarilyInvariantSeminorm.orthogonalBlockSum_isPositive` — ForTauCeti/Analysis/InnerProductSpace/RectangularUnitarilyInvariantSeminorm/BlockSum.lean:169
- `TauCeti.RectangularUnitarilyInvariantSeminorm.operatorAbs_orthogonalBlockSum` — ForTauCeti/Analysis/InnerProductSpace/RectangularUnitarilyInvariantSeminorm/BlockSum.lean:202
- `TauCeti.selfAdjointFunctionalCalculus_orthogonalBlockSum` — ForTauCeti/Analysis/InnerProductSpace/AngleGeometryBlockSum.lean:84
- `TauCeti.projection_orthogonalBlockSumSubmodule` — DavisKahan/FiniteDimensional/Sharpness.lean:2436, ForTauCeti/Analysis/InnerProductSpace/AngleGeometryBlockSum.lean:138
- `TauCeti.sinAngleOperator_orthogonalBlockSumSubmodule` — ForTauCeti/Analysis/InnerProductSpace/AngleGeometryBlockSum.lean:150
- `TauCeti.DavisKahanTheory.angleOperator_orthogonalBlockSumSubmodule` — DavisKahan/FiniteDimensional/Core/AngleOperatorBlockSum.lean:26
- `TauCeti.DavisKahanTheory.tanAngleOperator_orthogonalBlockSumSubmodule` — DavisKahan/FiniteDimensional/Core/AngleOperatorBlockSum.lean:75
- `TauCeti.DavisKahanTheory.tanTwoAngleOperator_orthogonalBlockSumSubmodule` — DavisKahan/FiniteDimensional/Core/AngleOperatorBlockSum.lean:115
- `TauCeti.DavisKahanTheory.tanTheta_model_sourceSharpness` — DavisKahan/FiniteDimensional/Sharpness.lean:2005
- `TauCeti.DavisKahanTheory.sinTwoTheta_reflectionDefect_model_le` — DavisKahan/FiniteDimensional/Sharpness.lean:2172
- `TauCeti.DavisKahanTheory.modelTanTwoThetaPerturbedResidual_offDiagonal` — DavisKahan/FiniteDimensional/Sharpness.lean:2325
- `TauCeti.DavisKahanTheory.tanTwoTheta_model_sourceSharpness` — DavisKahan/FiniteDimensional/Sharpness.lean:2390
- `TauCeti.DavisKahanTheory.directSumModelSubspace` — DavisKahan/FiniteDimensional/Sharpness.lean:2450
- `TauCeti.DavisKahanTheory.directSumRotatedModelSubspace` — DavisKahan/FiniteDimensional/Sharpness.lean:2456
- `TauCeti.DavisKahanTheory.sinAngleOperator_directSumModelSubspaces` — DavisKahan/FiniteDimensional/Sharpness.lean:2463
- `TauCeti.DavisKahanTheory.angleOperator_directSumModelSubspaces` — DavisKahan/FiniteDimensional/Sharpness.lean:2476
- `TauCeti.DavisKahanTheory.tanAngleOperator_directSumModelSubspaces` — DavisKahan/FiniteDimensional/Sharpness.lean:2489
- `TauCeti.DavisKahanTheory.tanTwoAngleOperator_directSumModelSubspaces` — DavisKahan/FiniteDimensional/Sharpness.lean:2502
- `TauCeti.DavisKahanTheory.sinTheta_directSum_subspace_equality` — DavisKahan/FiniteDimensional/Sharpness.lean:2515
- `TauCeti.DavisKahanTheory.tanTheta_directSum_subspace_equality` — DavisKahan/FiniteDimensional/Sharpness.lean:2528
- `TauCeti.DavisKahanTheory.sinTwoTheta_directSum_subspace_equality` — DavisKahan/FiniteDimensional/Sharpness.lean:2541
- `TauCeti.DavisKahanTheory.tanTwoTheta_directSum_subspace_equality` — DavisKahan/FiniteDimensional/Sharpness.lean:2554

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 8. S2-unbounded-scope — Unbounded self-adjoint scope

- **Source anchor:** Section 2, final paragraphs
- **Source kind:** `scope_claim`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `e25372d3c1f23d592684090e06ab59344253ceac7704650a868c0846d748272d`
- **Private-transcription provenance lines:** `[[216, 218], [781, 785]]`

### Exact registered source passage

~~~~tex
The subject throughout will be a bounded Hermitian operator $A$ acting upon $\Hilbert$, together with a modified Hermitian operator $A+H$, where $H$ will usually be thought of as small.
The results and proofs also apply to unbounded self-adjoint $A$, provided the domain of $H$ contains that of $A$.
(Some of the results are vacuous when certain norms fail to exist, but we shall not need to make special mention of this.\,)

Unbounded self-adjoint operators, important in several applications, are covered by our theorems or slight extensions thereof, although we must assume $H$ or $R$ bounded to draw useful inferences.
The theorems above contain references to a finite interval $[\beta,\alpha]$; they remain valid after this interval is extended to $]-\infty,\alpha]$ and $]\beta-\delta,\alpha+\delta[$ to $]-\infty,\alpha+\delta[$.
As long as the spectra of $A_i$ and $\Lambda_i$ satisfy their respective hypotheses concerning the gap $\delta$, they may be otherwise unbounded without invalidating the theorems.
However, to free our theorems from all inessential boundedness hypotheses, we have had to complicate the proofs substantially.
These complications have been confined to two passages---\TheoremRef{5.2}, and the \AppendixSixRef---in order to avoid distracting those readers not concerned with the utmost generality.
~~~~

### Semantic audit clauses

- **`S2-unbounded-scope.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing_real`, `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_of_reducing_real`, `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_real`, `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_real`, `TauCeti.DavisKahan1970.theorem6_3_all_kyFan_core_infiniteData_real`, `TauCeti.DavisKahan1970.canonical_generalizedSinTheta`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean:368`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_of_reducing_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean:394`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean:534`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean:559`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.theorem6_3_all_kyFan_core_infiniteData_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean:251`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.canonical_generalizedSinTheta`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:47`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.canonical_generalizedSinTheta` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:47
- `TauCeti.DavisKahan1970.unbounded_sinTheta_opNorm` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:57
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_ideal_directedTangent_of_reducing` — DavisKahan/TanTheta/Theorem63Unbounded.lean:487
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_ideal_of_reducing` — DavisKahan/TanTheta/Theorem63Unbounded.lean:458
- `TauCeti.DavisKahan.ExactTanTheta.crossed_lower_of_reducing` — DavisKahan/TanTheta/Theorem63Unbounded.lean:119, DavisKahan/TanTheta/Theorem63UnboundedCompression.lean:178
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_ideal_directedTangent` — DavisKahan/TanTheta/Theorem63Unbounded.lean:402
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_ideal` — DavisKahan/TanTheta/Theorem63Unbounded.lean:375
- `TauCeti.DavisKahan.ExactTanTheta.Theorem63TrialData.all_kyFan_core_of_formBounds` — DavisKahan/TanTheta/Theorem63TrialData.lean:536
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing` — DavisKahan/TanTheta/Theorem63UnboundedInfiniteTrial.lean:588
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_of_reducing` — DavisKahan/TanTheta/Theorem63UnboundedInfiniteTrial.lean:614
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists` — DavisKahan/TanTheta/Theorem63UnboundedInfiniteTrial.lean:640
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:166
- `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_residual_opNorm` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedResidual.lean:92
- `TauCeti.DavisKahan.ExactSinTheta.sinTheta_unbounded_real` — DavisKahan/SinTheta/Real/Unbounded.lean:37
- `TauCeti.DavisKahan.ExactSinTheta.generalizedSinTheta_unbounded_real` — DavisKahan/SinTheta/Real/Generalized.lean:42
- `TauCeti.DavisKahan.ExactSinTheta.sinTheta_unbounded_real_spectralSubspace` — DavisKahan/SinTheta/Natural/Real.lean:113
- `TauCeti.DavisKahan.ExactSinTheta.generalizedSinTheta_unbounded_real_spectralSubspace` — DavisKahan/SinTheta/Natural/Real.lean:155
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative_real` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:344
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_opNorm_real` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:564
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_reflectionResidual_opNorm_real` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:569
- `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing_real` — DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean:368
- `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_of_reducing_real` — DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean:394
- `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_real` — DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean:534
- `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_real` — DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean:559
- `TauCeti.DavisKahan1970.theorem6_3_all_kyFan_core_infiniteData_real` — DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean:251
- `TauCeti.DavisKahan1970.gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan_real` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedGramReal.lean:486
- `TauCeti.DavisKahan1970.mem_and_gauge_le_reflectionTangentCorner_real` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedGramReal.lean:640
- `TauCeti.DavisKahan1970.gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan_ambient_real` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedGramReal.lean:608
- `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_residual_opNorm_real` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedGramReal.lean:731
- `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_residual_div_real` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedGramReal.lean:854

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 9. DK-3.1-def — Direct rotation

- **Source anchor:** Definition 3.1
- **Source kind:** `definition`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `161814de6687dea957ba7408dd53b56c71b504b2d3065002a19efdcc026f94cc`
- **Private-transcription provenance lines:** `[[834, 845]]`

### Exact registered source passage

~~~~tex
\begin{definition}\label{def:3.1}
A unitary solution
\[
  V\representedby\begin{pmatrix}C_0&-S_1\\S_0&C_1\end{pmatrix}
\]
of $VP=QV$ will be called a \emph{direct rotation} from $P\Hilbert$ to $Q\Hilbert$ if it satisfies the following additional conditions:
\begin{enumerate}[label=(\roman*)]
\item $C_0\geq0$, $C_1\geq0$;
\item $S_1=S_0^{*}$.
\end{enumerate}
The symbol $U$ will be reserved for direct rotations.
\end{definition}
~~~~

### Semantic audit clauses

- **`DK-3.1-def.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.complex_directRotation`, `TauCeti.DavisKahan1970.real_directRotation`, `TauCeti.DavisKahan1970.real_directRotation_orthogonal`, `TauCeti.DavisKahan1970.real_directRotation_intertwines`, `TauCeti.DavisKahan1970.real_directRotation_diagonalBlock`, `TauCeti.DavisKahan1970.real_directRotation_complementaryDiagonalBlock`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.complex_directRotation`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:128`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.real_directRotation`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:225`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.real_directRotation_orthogonal`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:226`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.real_directRotation_intertwines`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:228`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.real_directRotation_diagonalBlock`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:237`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.real_directRotation_complementaryDiagonalBlock`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:239`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.complex_directRotation` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:128
- `TauCeti.DavisKahan.spectraCanonicalIntertwiner` — DavisKahan/Geometry/Polar/DirectRotation.lean:69
- `TauCeti.DavisKahan.Frontier.IsPaperDirectRotation` — DavisKahan/Geometry/Halmos/GenericRotationPredicates.lean:47
- `TauCeti.DavisKahanTheory.angleComplexStructure` — DavisKahan/FiniteDimensional/DirectRotation.lean:55
- `TauCeti.DavisKahanTheory.directRotation_eq_cos_add_J_sin` — DavisKahan/FiniteDimensional/DirectRotation.lean:129
- `TauCeti.DavisKahanTheory.directRotationCosine_eq_half_smul_add` — DavisKahan/FiniteDimensional/DirectRotation.lean:302
- `TauCeti.DavisKahanTheory.directRotation_sub_cosine_eq_half_smul_sub` — DavisKahan/FiniteDimensional/DirectRotation.lean:318
- `TauCeti.DavisKahanTheory.directRotation_sub_cosine_comp_self` — DavisKahan/FiniteDimensional/DirectRotation.lean:678
- `TauCeti.DavisKahanTheory.angleComplexStructure_comp_self` — DavisKahan/FiniteDimensional/DirectRotation.lean:736
- `TauCeti.DavisKahanTheory.angleComplexStructure_comp_angleOperator_comp_self` — DavisKahan/FiniteDimensional/DirectRotation/Exponential.lean:199
- `TauCeti.DavisKahanTheory.directRotationCosine_eq_calculus` — DavisKahan/FiniteDimensional/DirectRotation/Exponential.lean:103
- `TauCeti.DavisKahanTheory.sinAngleOperator_eigenvalues_mem_Icc` — DavisKahan/FiniteDimensional/DirectRotation/Exponential.lean:78
- `TauCeti.DavisKahanTheory.directRotation_eq_exp_angleComplexStructure_comp_angleOperator` — DavisKahan/FiniteDimensional/DirectRotation/Exponential.lean:247
- `TauCeti.DavisKahan1970.real_directRotation` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:225
- `TauCeti.DavisKahan1970.real_directRotation_orthogonal` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:226
- `TauCeti.DavisKahan1970.real_directRotation_intertwines` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:228
- `TauCeti.DavisKahan1970.real_directRotation_diagonalBlock` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:237
- `TauCeti.DavisKahan1970.real_directRotation_complementaryDiagonalBlock` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:239
- `TauCeti.DavisKahan.canonicalAbsoluteValueR` — DavisKahan/Geometry/Polar/DirectRotationReal.lean:141
- `TauCeti.DavisKahan.complexify_directRotationR` — DavisKahan/Geometry/Polar/DirectRotationReal.lean:211

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 10. DK-3.2-def — Acute case

- **Source anchor:** Definition 3.2
- **Source kind:** `definition`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `565defff648c593393e79ca50a2ed8e93e969c41351f67ac63aed945ac77014f`
- **Private-transcription provenance lines:** `[[847, 849]]`

### Exact registered source passage

~~~~tex
\begin{definition}\label{def:3.2}
Subspaces $P\Hilbert$ and $Q\Hilbert$ are said to be in the \emph{acute case} if $P\Hilbert\cap\tQ\Hilbert$ and $\tP\Hilbert\cap Q\Hilbert$ are zero.
\end{definition}
~~~~

### Semantic audit clauses

- **`DK-3.2-def.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.IsAcute`, `TauCeti.isAcute_iff_inf_orthogonal_eq_bot`, `TauCeti.DavisKahan1970.Section3AcuteCounterexample.exists_isAcute_projectionGap_eq_one`

### Primary Lean declarations for semantic review

#### `TauCeti.IsAcute`

Source location candidates: `ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean:151`, `ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean:428`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.isAcute_iff_inf_orthogonal_eq_bot`

Source location candidates: `ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean:212`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section3AcuteCounterexample.exists_isAcute_projectionGap_eq_one`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3AcuteCounterexample.lean:285`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.IsAcute` — ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean:151, ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean:428
- `TauCeti.isAcute_iff_inf_orthogonal_eq_bot` — ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean:212
- `TauCeti.DavisKahan.IsUniformlyAcute` — DavisKahan/BoundedOperator/Compat.lean:98
- `TauCeti.isAcute_of_projectionGap_lt_one` — ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean:241
- `TauCeti.directedProjectionGap_lt_one_of_transverse` — ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean:260
- `TauCeti.projectionGap_lt_one_of_isAcute` — ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean:346
- `TauCeti.isAcute_iff_projectionGap_lt_one` — ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean:398
- `TauCeti.one_le_projectionGap_of_forall_exists_unit_lt` — ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean:367
- `TauCeti.DavisKahan1970.Section3AcuteCounterexample.exists_isAcute_projectionGap_eq_one` — DavisKahan/Sources/DavisKahan1970/Section3AcuteCounterexample.lean:285

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 11. DK-3.1-prop — Acute direct rotation existence and uniqueness

- **Source anchor:** Proposition 3.1
- **Source kind:** `proposition`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `46a75530e2d8da8c3c9f8871f2df1807511b073f02ed0208842730243a3c1f02`
- **Private-transcription provenance lines:** `[[850, 852]]`

### Exact registered source passage

~~~~tex
\begin{proposition}\label{prop:3.1}
In the acute case the direct rotation exists, is unique, and is characterized by property~(i) alone.
\end{proposition}
~~~~

### Semantic audit clauses

- **`DK-3.1-prop.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.complex_directRotation`, `TauCeti.DavisKahan1970.complex_directRotation_unique`, `TauCeti.DavisKahan1970.complex_directRotation_diagonalBlock`, `TauCeti.DavisKahan1970.complex_directRotation_complementaryDiagonalBlock`, `TauCeti.DavisKahan1970.complex_directRotation_reflectionConjugate`, `TauCeti.DavisKahan1970.complex_directRotation_of_diagonalBlocks`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.complex_directRotation`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:128`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.complex_directRotation_unique`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:134`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.complex_directRotation_diagonalBlock`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:160`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.complex_directRotation_complementaryDiagonalBlock`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:162`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.complex_directRotation_reflectionConjugate`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:184`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.complex_directRotation_of_diagonalBlocks`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:186`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.complex_directRotation` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:128
- `TauCeti.DavisKahan1970.complex_directRotation_unique` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:134
- `TauCeti.DavisKahan1970.complex_directRotation_diagonalBlock` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:160
- `TauCeti.DavisKahan1970.complex_directRotation_complementaryDiagonalBlock` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:162
- `TauCeti.DavisKahan1970.complex_directRotation_reflectionConjugate` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:184
- `TauCeti.DavisKahan1970.complex_directRotation_of_diagonalBlocks` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:186
- `TauCeti.DavisKahan1970.complex_directRotation_iff_diagonalBlocks` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:188
- `TauCeti.DavisKahan1970.real_directRotation` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:225
- `TauCeti.DavisKahan1970.real_directRotation_orthogonal` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:226
- `TauCeti.DavisKahan1970.real_directRotation_intertwines` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:228
- `TauCeti.DavisKahan1970.real_directRotation_maps_subspace` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:230
- `TauCeti.DavisKahan1970.real_directRotation_maps_orthogonalComplement` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:232
- `TauCeti.DavisKahan1970.real_directRotation_diagonalBlock` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:237
- `TauCeti.DavisKahan1970.real_directRotation_complementaryDiagonalBlock` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:239
- `TauCeti.DavisKahan1970.real_directRotation_principal_of_sq` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:241
- `TauCeti.DavisKahan1970.real_directRotation_of_diagonalBlocks` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:243
- `TauCeti.DavisKahan1970.real_directRotation_iff_diagonalBlocks` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:245
- `TauCeti.DavisKahan1970.complex_directRotation_reflectionConjugate_of_positiveDiagonalBlocks` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:205
- `TauCeti.DavisKahan1970.complex_directRotation_of_positiveDiagonalBlocks` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:207
- `TauCeti.DavisKahan1970.complex_directRotation_iff_positiveDiagonalBlocks` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:209
- `TauCeti.DavisKahan1970.real_directRotation_of_positiveDiagonalBlocks` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:211
- `TauCeti.DavisKahan1970.real_directRotation_iff_positiveDiagonalBlocks` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:213
- `TauCeti.DavisKahan.eq_directRotationR_iff_diagonalBlocks_pos` — DavisKahan/Geometry/Polar/DirectRotationReal.lean:738
- `TauCeti.DavisKahan.isPositive_of_complexify` — DavisKahan/Geometry/Polar/DirectRotationReal.lean:651
- `TauCeti.DavisKahan.isPositive_canonicalAbsoluteValueR` — DavisKahan/Geometry/Polar/DirectRotationReal.lean:683
- `TauCeti.DavisKahan1970.acute_directRotation` — DavisKahan/Sources/DavisKahan1970/Section3AcuteDirectRotation.lean:50
- `TauCeti.DavisKahan1970.acute_directRotation_existsUnique` — DavisKahan/Sources/DavisKahan1970/Section3AcuteDirectRotation.lean:150
- `TauCeti.DavisKahan1970.acute_directRotation_iff_positiveDiagonalBlocks` — DavisKahan/Sources/DavisKahan1970/Section3AcuteDirectRotation.lean:133
- `TauCeti.DavisKahan1970.complex_acute_directRotation_iff_positiveDiagonalBlocks` — DavisKahan/Sources/DavisKahan1970/Section3AcuteDirectRotation.lean:198
- `TauCeti.DavisKahan1970.real_directRotation_eq_acute_directRotation` — DavisKahan/Sources/DavisKahan1970/Section3AcuteDirectRotation.lean:242

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 12. DK-3.2-prop — Nonacute existence criterion

- **Source anchor:** Proposition 3.2
- **Source kind:** `proposition`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `7fa0afb04717e112c11b6069c69102c2ea9cb3b29337c0a88464921f02a37777`
- **Private-transcription provenance lines:** `[[901, 909]]`

### Exact registered source passage

~~~~tex
\begin{proposition}\label{prop:3.2}
In the nonacute case, a direct rotation exists if and only if
\begin{equation*}
  \dim(P\Hilbert\cap\tQ\Hilbert)
  =\dim(\tP\Hilbert\cap Q\Hilbert).
  \tag{3.5}\label{eq:3.5}
\end{equation*}
It is not unique.
\end{proposition}
~~~~

### Semantic audit clauses

- **`DK-3.2-prop.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_exists_iff_crossedDefectsEquivalent`, `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_parameterized_nonuniqueness`, `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_exists_iff_crossedDefectsEquivalent_real`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_exists_iff_crossedDefectsEquivalent`

Source location candidates: `DavisKahan/Frontier/Section3.lean:2038`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_parameterized_nonuniqueness`

Source location candidates: `DavisKahan/Frontier/Section3.lean:2046`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_exists_iff_crossedDefectsEquivalent_real`

Source location candidates: `DavisKahan/Frontier/Section3.lean:3330`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_exists_iff_crossedDefectsEquivalent` — DavisKahan/Frontier/Section3.lean:2038
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_parameterized_nonuniqueness` — DavisKahan/Frontier/Section3.lean:2046
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_not_unique` — DavisKahan/Frontier/Section3.lean:2092
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_not_existsUnique` — DavisKahan/Frontier/Section3.lean:2120
- `TauCeti.DavisKahan.Frontier.Section3.remark3_2_bilateralShift_separates_dimensionHypotheses` — DavisKahan/Frontier/Section3BilateralShift.lean:388
- `TauCeti.DavisKahan.Frontier.Section3.halmosSourceDefect_coordinateHalfSpace` — DavisKahan/Frontier/Section3BilateralShift.lean:252
- `TauCeti.DavisKahan.Frontier.Section3.halmosTargetDefect_coordinateHalfSpace` — DavisKahan/Frontier/Section3BilateralShift.lean:278
- `TauCeti.DavisKahan.Frontier.Section3.halmosSourceDefect_ne_bot_of_not_isAcute` — DavisKahan/Frontier/Section3.lean:2062
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_exists_iff_crossedDefectsEquivalent_real` — DavisKahan/Frontier/Section3.lean:3330
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_parameterized_nonuniqueness_real` — DavisKahan/Frontier/Section3.lean:3339
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_not_unique_real` — DavisKahan/Frontier/Section3.lean:3354
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_not_existsUnique_real` — DavisKahan/Frontier/Section3.lean:3366
- `TauCeti.DavisKahan.Frontier.Section3.remark3_2_bilateralShift_separates_dimensionHypotheses_real` — DavisKahan/Frontier/Section3BilateralShift.lean:446
- `TauCeti.DavisKahan.Frontier.Section3.directedGap_asymmetric_coordinateHalfSpace` — DavisKahan/Frontier/Section3BilateralShift.lean:353
- `TauCeti.DavisKahan.Frontier.Section3.coordinateHalfSpace_le_coordinateHalfSpace` — DavisKahan/Frontier/Section3BilateralShift.lean:324

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 13. DK-3.3-prop — Principal square-root characterization

- **Source anchor:** Proposition 3.3
- **Source kind:** `proposition`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `87620ffbc1a3ee6e3c1eb880ee359423e4cc4888b4e5c601f71c31b33ee7a8c5`
- **Private-transcription provenance lines:** `[[961, 968], [1008, 1011]]`

### Exact registered source passage

~~~~tex
We shall assume \eqref{eq:3.5} as well as \eqref{eq:1.5} except where stated otherwise.
Consequently the direct rotation will always exist, and rather than the more general $V$ of \eqref{eq:1.6} we shall deal mostly with its direct special case
\begin{equation*}
  U\representedby
  \begin{pmatrix}C_0&-S_0^{*}\\S_0&C_1\end{pmatrix},
  \qquad C_j\geq0.
  \tag{3.6}\label{eq:3.6}
\end{equation*}

\begin{proposition}\label{prop:3.3}
Any direct rotation of $P\Hilbert$ to $Q\Hilbert$ is a principal square root of $(Q-\tQ)(P-\tP)$, that is, a unitary square root with spectrum in the right half-plane.
Any principal square root of $(Q-\tQ)(P-\tP)$ is a direct rotation of $P\Hilbert$ to $Q\Hilbert$ provided it takes $P\Hilbert\cap\tQ\Hilbert$ onto $\tP\Hilbert\cap Q\Hilbert$.
\end{proposition}
~~~~

### Semantic audit clauses

- **`DK-3.3-prop.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.complex_directRotation_sq`, `TauCeti.DavisKahan1970.complex_directRotation_hermitianPart`, `TauCeti.DavisKahan1970.complex_directRotation_principal_of_sq`, `TauCeti.DavisKahan1970.real_directRotation_sq`, `TauCeti.DavisKahan1970.real_directRotation_hermitianPart`, `TauCeti.DavisKahan1970.real_directRotation_principal_of_sq`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.complex_directRotation_sq`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:130`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.complex_directRotation_hermitianPart`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:156`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.complex_directRotation_principal_of_sq`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:158`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.real_directRotation_sq`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:234`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.real_directRotation_hermitianPart`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:235`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.real_directRotation_principal_of_sq`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:241`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.complex_directRotation_sq` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:130
- `TauCeti.DavisKahan1970.complex_directRotation_hermitianPart` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:156
- `TauCeti.DavisKahan1970.complex_directRotation_principal_of_sq` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:158
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_3_principalSquareRoot_forward` — DavisKahan/Frontier/Section3.lean:1234
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_3_principalSquareRoot_converse` — DavisKahan/Frontier/Section3.lean:737
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_3_principalSquareRoot_iff` — DavisKahan/Frontier/Section3.lean:1293
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_3_principalSquareRoot_forward_of_nonneg_blocks` — DavisKahan/Frontier/Section3.lean:1256
- `TauCeti.DavisKahan1970.real_directRotation_sq` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:234
- `TauCeti.DavisKahan1970.real_directRotation_hermitianPart` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:235
- `TauCeti.DavisKahan1970.real_directRotation_principal_of_sq` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:241

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 14. DK-3.4-prop — Square as a direct rotation

- **Source anchor:** Proposition 3.4
- **Source kind:** `proposition`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `821c742e5042b7ae1d62ca7267f13353c0dc72719849ccb9e9b73519fa175575`
- **Private-transcription provenance lines:** `[[961, 968], [1035, 1037]]`

### Exact registered source passage

~~~~tex
We shall assume \eqref{eq:3.5} as well as \eqref{eq:1.5} except where stated otherwise.
Consequently the direct rotation will always exist, and rather than the more general $V$ of \eqref{eq:1.6} we shall deal mostly with its direct special case
\begin{equation*}
  U\representedby
  \begin{pmatrix}C_0&-S_0^{*}\\S_0&C_1\end{pmatrix},
  \qquad C_j\geq0.
  \tag{3.6}\label{eq:3.6}
\end{equation*}

\begin{proposition}\label{prop:3.4}
If $C_0^2\geq\tfrac12$, then $U^2$ is the direct rotation of $Q_-\Hilbert$ to $Q\Hilbert$.
\end{proposition}
~~~~

### Semantic audit clauses

- **`DK-3.4-prop.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan.Frontier.Section3.proposition3_4_source_full`, `TauCeti.DavisKahan.Frontier.Section3.proposition3_4_source_eq_directRotation`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan.Frontier.Section3.proposition3_4_source_full`

Source location candidates: `DavisKahan/Frontier/Section3.lean:1830`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section3.proposition3_4_source_eq_directRotation`

Source location candidates: `DavisKahan/Frontier/Section3.lean:1981`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan.Frontier.Section3.proposition3_4_source` — DavisKahan/Frontier/Section3.lean:1925
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_4_source_eq_directRotation` — DavisKahan/Frontier/Section3.lean:1981
- `TauCeti.DavisKahan.Frontier.Section3.crossedDefect_image_of_unitary_sq` — DavisKahan/Frontier/Section3.lean:1172
- `TauCeti.DavisKahan.Frontier.Section3.norm_projection_apply_le_of_forall_mem_source` — DavisKahan/Frontier/Section3.lean:1535
- `TauCeti.DavisKahan.Frontier.Section3.re_inner_halmosCosineSq_sub_half_nonneg_of_source` — DavisKahan/Frontier/Section3.lean:1740
- `TauCeti.DavisKahan.Frontier.Section3.re_inner_halmosCosineSq_self` — DavisKahan/Frontier/Section3.lean:1650
- `TauCeti.DavisKahan.Frontier.Section3.isSelfAdjoint_source_block_spectraDirectRotation` — DavisKahan/Frontier/Section3.lean:1490
- `TauCeti.DavisKahan.Frontier.Section3.isSelfAdjoint_complement_block_spectraDirectRotation` — DavisKahan/Frontier/Section3.lean:1505
- `TauCeti.DavisKahan.Frontier.Section3.nonneg_add_star_of_re_inner_nonneg` — DavisKahan/Frontier/Section3.lean:1802
- `TauCeti.DavisKahan.Frontier.Section3.reflectionOperator_mul_projection_self` — DavisKahan/Frontier/Section3.lean:1787
- `TauCeti.DavisKahan.Frontier.Section3.projection_mul_reflectionOperator_self` — DavisKahan/Frontier/Section3.lean:1795
- `TauCeti.DavisKahanTheory.directRotation_sq` — DavisKahan/Experimental/InfiniteDimensional/DirectRotation.lean:656, DavisKahan/FiniteDimensional/DirectRotation/Basic.lean:554
- `TauCeti.DavisKahan1970.complex_directRotation_sq` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:130
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_4_square_is_reflected_directRotation` — DavisKahan/Frontier/Section3.lean:1408
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_4_source_full` — DavisKahan/Frontier/Section3.lean:1830

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 15. DK-3.1-thm — Classification of pairs of subspaces

- **Source anchor:** Theorem 3.1
- **Source kind:** `theorem`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `885d6b1c497533c6c2c1c0ef2940fd9f882249aaae51c85ea0392067b7dd5ed7`
- **Private-transcription provenance lines:** `[[961, 968], [1083, 1093]]`

### Exact registered source passage

~~~~tex
We shall assume \eqref{eq:3.5} as well as \eqref{eq:1.5} except where stated otherwise.
Consequently the direct rotation will always exist, and rather than the more general $V$ of \eqref{eq:1.6} we shall deal mostly with its direct special case
\begin{equation*}
  U\representedby
  \begin{pmatrix}C_0&-S_0^{*}\\S_0&C_1\end{pmatrix},
  \qquad C_j\geq0.
  \tag{3.6}\label{eq:3.6}
\end{equation*}

\begin{theorem}\label{thm:3.1}
For a pair of subspaces $P\Hilbert,Q\Hilbert$, subject to
\[
  \dim P\Hilbert=\dim Q\Hilbert,
  \qquad
  \dim(P\Hilbert\cap\tQ\Hilbert)=\dim(\tP\Hilbert\cap Q\Hilbert),
\]
a complete system of invariants under isometric equivalence is afforded by the spectral multiplicity functions of $\angles_0,\angles_1$.
These are arbitrary Hermitian operators satisfying the following conditions:
$0\leq\angles_j\leq\pi/2$; the dimensionalities of their domains sum to that of $\Hilbert$; and the spectral multiplicity functions of the $\angles_j$ are the same except for a possible difference in the multiplicity of $\{0\}$.
\end{theorem}
~~~~

### Semantic audit clauses

- **`DK-3.1-thm.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan.Frontier.Section3.theorem3_1_spectralMultiplicity_classification`, `TauCeti.DavisKahan.Frontier.Section3.theorem3_1_realization`, `TauCeti.DavisKahan.Frontier.Section3.theorem3_1_spectralMultiplicity_classification_real`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan.Frontier.Section3.theorem3_1_spectralMultiplicity_classification`

Source location candidates: `DavisKahan/Frontier/Section3.lean:2636`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section3.theorem3_1_realization`

Source location candidates: `DavisKahan/Frontier/Section3.lean:2722`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section3.theorem3_1_spectralMultiplicity_classification_real`

Source location candidates: `DavisKahan/Frontier/Section3Real.lean:132`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan.SameHalmosCosineBlockInvariant` — DavisKahan/Geometry/Halmos/GenericReconstruction.lean:459
- `TauCeti.DavisKahan.pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant` — DavisKahan/Geometry/Halmos/GenericReconstruction.lean:490
- `TauCeti.DavisKahan.exists_cosineBlockEquiv_of_pairEquiv` — DavisKahan/Geometry/Halmos/GenericReconstruction.lean:424
- `TauCeti.DavisKahan.pairOfSubspacesUnitaryEquivalent_of_cosineBlockEquiv` — DavisKahan/Geometry/Halmos/GenericReconstruction.lean:395
- `TauCeti.DavisKahan.genericTransport` — DavisKahan/Geometry/Halmos/GenericReconstruction.lean:270
- `TauCeti.DavisKahan.pairOfSubspacesUnitaryEquivalent_of_summandEquivs` — DavisKahan/Geometry/Halmos/Assembly.lean:569
- `TauCeti.DavisKahan.Frontier.SameSpectralMultiplicity` — DavisKahan/Frontier/Core.lean:81
- `TauCeti.DavisKahan.Frontier.sameSpectralMultiplicity_iff_unitarilyEquivalent` — DavisKahan/Frontier/Core.lean:155
- `TauCeti.DavisKahan.Frontier.unitarilyEquivalent_of_sameSpectralMultiplicity` — DavisKahan/Frontier/Core.lean:106
- `TauCeti.DavisKahan.Frontier.sameSpectralMultiplicity_of_unitarilyEquivalent` — DavisKahan/Frontier/Core.lean:123
- `TauCeti.DavisKahan.Frontier.Section3.theorem3_1_spectralMultiplicity_classification` — DavisKahan/Frontier/Section3.lean:2636
- `TauCeti.DavisKahan.Frontier.Section3.twoProjection_operator_classification` — DavisKahan/Frontier/Section3.lean:2305, DavisKahan/Geometry/Polar/TwoProjectionOperatorClassification.lean:285
- `TauCeti.DavisKahan.HalmosAngleDatum` — DavisKahan/Geometry/Halmos/Realization.lean:1019, DavisKahan/Geometry/Halmos/Realization.lean:1050, DavisKahan/Geometry/Halmos/Realization.lean:1056
- `TauCeti.DavisKahan.HalmosAngleDatum.starProjection_targetSubspace_apply` — DavisKahan/Geometry/Halmos/Realization.lean:658
- `TauCeti.DavisKahan.HalmosAngleDatum.compress_source_eq` — DavisKahan/Geometry/Halmos/Realization.lean:686
- `TauCeti.DavisKahan.HalmosAngleDatum.compress_sourceOrthogonal_eq` — DavisKahan/Geometry/Halmos/Realization.lean:695
- `TauCeti.DavisKahan.HalmosAngleDatum.halmosCommonPart_eq` — DavisKahan/Geometry/Halmos/Realization.lean:762
- `TauCeti.DavisKahan.HalmosAngleDatum.halmosSourceDefect_eq` — DavisKahan/Geometry/Halmos/Realization.lean:796
- `TauCeti.DavisKahan.HalmosAngleDatum.halmosTargetDefect_eq` — DavisKahan/Geometry/Halmos/Realization.lean:845
- `TauCeti.DavisKahan.HalmosAngleDatum.halmosExteriorPart_eq` — DavisKahan/Geometry/Halmos/Realization.lean:817
- `TauCeti.DavisKahan.HalmosAngleDatum.crossedDefectEquiv` — DavisKahan/Geometry/Halmos/Realization.lean:886
- `TauCeti.DavisKahan.HalmosAngleDatum.nonempty_halmosSourceDefect_equiv_targetDefect` — DavisKahan/Geometry/Halmos/Realization.lean:921
- `TauCeti.DavisKahan.trivialHalmosAngleDatum` — DavisKahan/Geometry/Halmos/Realization.lean:945
- `TauCeti.DavisKahan.trivial_halmosCommonPart_eq` — DavisKahan/Geometry/Halmos/Realization.lean:976
- `TauCeti.DavisKahan.trivial_halmosExteriorPart_eq` — DavisKahan/Geometry/Halmos/Realization.lean:987
- `TauCeti.DavisKahan.Frontier.Section3.theorem3_1_realization` — DavisKahan/Frontier/Section3.lean:2722
- `TauCeti.DavisKahan.Frontier.Section3.theorem3_1_realization_zeroAngle_unconstrained` — DavisKahan/Frontier/Section3.lean:2846
- `TauCeti.DavisKahan.Frontier.Section3.twoProjection_operator_classification_real` — DavisKahan/Frontier/Section3.lean:3164
- `TauCeti.DavisKahan.Frontier.Section3.theorem3_1_realization_ofAngles` — DavisKahan/Frontier/Section3.lean:2795
- `TauCeti.DavisKahan.Frontier.Section3.theorem3_1_spectralMultiplicity_classification_real` — DavisKahan/Frontier/Section3Real.lean:132
- `TauCeti.DavisKahan.Frontier.sameSpectralMultiplicity_iff_unitarilyEquivalent_real` — DavisKahan/Frontier/Section3Real.lean:94
- `TauCeti.DavisKahan.Frontier.sameSpectralMultiplicity_of_unitarilyEquivalent_real` — DavisKahan/Frontier/Section3Real.lean:81
- `TauCeti.DavisKahan.Frontier.unitarilyEquivalent_of_sameSpectralMultiplicity_real` — DavisKahan/Frontier/Section3Real.lean:66
- `TauCeti.DavisKahan.RealSpectralRestriction.exists_hasMultiplicityModel_real` — DavisKahan/SpectralTheory/Real/RealMultiplicityModel.lean:72
- `TauCeti.BorelCalculus.exists_hasMultiplicityModel_star` — ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/MultiplicityModelReal.lean:512
- `TauCeti.operatorUnitaryEquiv_of_measureEquiv_real` — ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/MultiplicityModelReal.lean:447
- `TauCeti.StarOperatorUnitaryEquiv` — ForTauCeti/Analysis/InnerProductSpace/OperatorUnitaryEquiv.lean:116, ForTauCeti/Analysis/InnerProductSpace/OperatorUnitaryEquiv.lean:126, ForTauCeti/Analysis/InnerProductSpace/OperatorUnitaryEquiv.lean:132
- `TauCeti.starOperatorUnitaryEquiv_of_isHilbertSum` — ForTauCeti/Analysis/InnerProductSpace/HilbertSumIntertwine.lean:167
- `TauCeti.star_linearIsometryEquiv_trans_symm_of_isHilbertSum` — ForTauCeti/Analysis/InnerProductSpace/HilbertSumIntertwine.lean:77
- `TauCeti.operatorUnitaryEquiv_retype_real_of_starOperatorUnitaryEquiv` — ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/MultiplicityModelReal.lean:397

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 16. DK-3.1-cor — Compact classification by angle eigenvalues

- **Source anchor:** Corollary 3.1
- **Source kind:** `corollary`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `fa52f58d0a2c0378b7d41e22854d1b88b1d4e73c6906c9a5bd13affa588f2c38`
- **Private-transcription provenance lines:** `[[961, 968], [1118, 1132]]`

### Exact registered source passage

~~~~tex
We shall assume \eqref{eq:3.5} as well as \eqref{eq:1.5} except where stated otherwise.
Consequently the direct rotation will always exist, and rather than the more general $V$ of \eqref{eq:1.6} we shall deal mostly with its direct special case
\begin{equation*}
  U\representedby
  \begin{pmatrix}C_0&-S_0^{*}\\S_0&C_1\end{pmatrix},
  \qquad C_j\geq0.
  \tag{3.6}\label{eq:3.6}
\end{equation*}

\begin{corollary}\label{cor:3.1}
For a pair of subspaces $P\Hilbert,Q\Hilbert$, subject to
\[
  \dim P\Hilbert=\dim Q\Hilbert,
  \qquad
  \dim(P\Hilbert\cap\tQ\Hilbert)=\dim(\tP\Hilbert\cap Q\Hilbert),
\]
and such that $P\tQ P$ is compact, a complete system of invariants under isometric equivalence is afforded by the eigenvalues (multiplicity counted) of $\angles_0,\angles_1$.
The eigenvalues $\theta_i$ of $\angles_0$ are an arbitrary sequence satisfying
\[
  \pi/2\geq\theta_1\geq\theta_2\geq\cdots
\]
and approaching $0$, together with a possible eigenvalue $0$.
The eigenvalues of $\angles_1$ must be the same except perhaps for the multiplicity of $0$.
\end{corollary}
~~~~

### Semantic audit clauses

- **`DK-3.1-cor.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_compact_defectBlock_angleList_classification`, `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_compact_classification_real`, `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_realization`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_compact_defectBlock_angleList_classification`

Source location candidates: `DavisKahan/Frontier/Section3.lean:2464`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_compact_classification_real`

Source location candidates: `DavisKahan/Frontier/Section3.lean:3210`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_realization`

Source location candidates: `DavisKahan/Frontier/Section3.lean:2895`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan.SameCompactAngleData` — DavisKahan/Geometry/Halmos/CompactClassification.lean:128
- `TauCeti.DavisKahan.pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData` — DavisKahan/Geometry/Halmos/CompactClassification.lean:203
- `TauCeti.DavisKahan.isCompactOperator_genericCosineBlock` — DavisKahan/Geometry/Halmos/CompactClassification.lean:89
- `TauCeti.DavisKahan.eigenspace_genericCosineBlock_zero` — DavisKahan/Geometry/Halmos/CompactClassification.lean:98
- `TauCeti.DavisKahan.finrank_eigenspace_eq_of_intertwiner` — DavisKahan/Geometry/Halmos/CompactClassification.lean:141
- `TauCeti.exists_linearIsometryEquiv_intertwining_of_finrank_eigenspace_eq` — ForTauCeti/Analysis/InnerProductSpace/CompactSelfAdjointClassification.lean:128
- `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_compact_defectBlock_angleList_classification` — DavisKahan/Frontier/Section3.lean:2464
- `TauCeti.DavisKahan.Frontier.Section3.pairOfSubspacesUnitaryEquivalent_orthogonal_right_iff` — DavisKahan/Frontier/Section3.lean:2234
- `TauCeti.DavisKahan.Frontier.Section3.sameHalmosTrivialDimensions_orthogonal_right_iff` — DavisKahan/Frontier/Section3.lean:2257
- `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_compact_classification_real` — DavisKahan/Frontier/Section3.lean:3210
- `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_compact_angleList_classification_real` — DavisKahan/Frontier/Section3.lean:3235
- `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_realization` — DavisKahan/Frontier/Section3.lean:2895
- `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_realization_zeroMultiplicity` — DavisKahan/Frontier/Section3.lean:2946
- `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_prescribedAngleSequence_classification` — DavisKahan/Frontier/Section3.lean:3113
- `TauCeti.DavisKahan.Frontier.Section3.approximationNumber_genericCosineBlock_eq_ambient` — DavisKahan/Frontier/Section3.lean:2576
- `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_compact_defectBlock_angleList_classification_complex` — DavisKahan/Frontier/Section3.lean:2662
- `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_compact_defectBlock_angleList_classification_real` — DavisKahan/Frontier/Section3.lean:3259
- `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_prescribedAngleSequence_classification_real` — DavisKahan/Frontier/Section3.lean:3289

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 17. DK-3.5-prop — Angle commutation and eigenspace geometry

- **Source anchor:** Proposition 3.5
- **Source kind:** `proposition`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `2b467fb17b6fbfdd563e339abcd67e54cbaad60faf4ff6a692dbb6916beceb70`
- **Private-transcription provenance lines:** `[[961, 968], [1143, 1152]]`

### Exact registered source passage

~~~~tex
We shall assume \eqref{eq:3.5} as well as \eqref{eq:1.5} except where stated otherwise.
Consequently the direct rotation will always exist, and rather than the more general $V$ of \eqref{eq:1.6} we shall deal mostly with its direct special case
\begin{equation*}
  U\representedby
  \begin{pmatrix}C_0&-S_0^{*}\\S_0&C_1\end{pmatrix},
  \qquad C_j\geq0.
  \tag{3.6}\label{eq:3.6}
\end{equation*}

\begin{proposition}\label{prop:3.5}
$\angles$ commutes with $P$, with $Q$, with $J$, and with $U$.
For every eigenvalue $\theta$, the eigenvectors $x$ satisfy $\angle(x,Ux)=\theta$.
In the acute case, for every eigenvalue $\theta$, the eigenspace $\Omega(\{\theta\})\Hilbert$ is the unique maximal subspace with the properties
\begin{enumerate}[label=(\alph*)]
\item it reduces $P$ and $Q$;
\item for every nonzero vector $x$ of $P\Hilbert$ lying in it, $\angle(x,Qx)=\theta$;
\item for every nonzero vector $x$ of $\tP\Hilbert$ lying in it, $\angle(x,\tQ x)=\theta$.
\end{enumerate}
\end{proposition}
~~~~

### Semantic audit clauses

- **`DK-3.5-prop.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.proposition3_5_directRotation_resolution`, `TauCeti.DavisKahan1970.proposition3_5_commutations`, `TauCeti.DavisKahan1970.proposition3_5_eigenvector_angle`, `TauCeti.DavisKahan1970.proposition3_5_angleEigenspace_eq_fixedCosineSubspace`, `TauCeti.DavisKahan1970.proposition3_5_angleEigenspace_uniqueMaximal`, `TauCeti.DavisKahan1970.proposition3_5_angleOperator`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.proposition3_5_directRotation_resolution`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:80`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_5_commutations`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:235`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_5_eigenvector_angle`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:249`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_5_angleEigenspace_eq_fixedCosineSubspace`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:257`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_5_angleEigenspace_uniqueMaximal`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:268`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_5_angleOperator`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:43`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.bounded_angle_commute` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:100
- `TauCeti.DavisKahan1970.bounded_sinAngleOperatorC_norm` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:95
- `TauCeti.DavisKahan.Frontier.Section3.IsFixedCosineReducingSubspace` — DavisKahan/Frontier/Section3.lean:103
- `TauCeti.DavisKahan.Frontier.Section3.fixedCosineSubspace` — DavisKahan/Frontier/Section3.lean:256
- `TauCeti.DavisKahan.Frontier.Section3.fixedCosineSubspace_isFixedCosineReducing` — DavisKahan/Frontier/Section3.lean:359
- `TauCeti.DavisKahan.Frontier.Section3.fixedCosineSubspace_maximal` — DavisKahan/Frontier/Section3.lean:385
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_5_fixedAngle_maximal` — DavisKahan/Frontier/Section3.lean:514
- `TauCeti.DavisKahan.halmosCosineSq_commute_projection` — DavisKahan/Geometry/Halmos/TwoProjections.lean:663
- `TauCeti.DavisKahan.Frontier.Section3.halmosCosineSq_commute_projection_right` — DavisKahan/Frontier/Section3.lean:292
- `TauCeti.DavisKahanTheory.sq_sinAngleOperator_add_sq_directRotationCosine` — DavisKahan/FiniteDimensional/DirectRotation.lean:381
- `TauCeti.DavisKahanTheory.projection_comm_sinAngleOperator` — DavisKahan/FiniteDimensional/DirectRotation.lean:465
- `TauCeti.DavisKahanTheory.projection_right_comm_sinAngleOperator` — DavisKahan/FiniteDimensional/DirectRotation.lean:508
- `TauCeti.DavisKahanTheory.directRotation_comm_sinAngleOperator` — DavisKahan/FiniteDimensional/DirectRotation.lean:427
- `TauCeti.DavisKahanTheory.angleOperator_comm_projection` — DavisKahan/FiniteDimensional/DirectRotation.lean:536
- `TauCeti.DavisKahanTheory.angleOperator_comm_projection_right` — DavisKahan/FiniteDimensional/DirectRotation.lean:544
- `TauCeti.DavisKahanTheory.angleOperator_comm_directRotation` — DavisKahan/FiniteDimensional/DirectRotation.lean:526
- `TauCeti.adjoint_moorePenroseInverse_of_isSymmetric` — ForTauCeti/Analysis/InnerProductSpace/MoorePenroseInverse.lean:380
- `TauCeti.comp_moorePenroseInverse_comm_of_isSymmetric` — ForTauCeti/Analysis/InnerProductSpace/MoorePenroseInverse.lean:390
- `TauCeti.moorePenroseInverse_comm_of_isSymmetric` — ForTauCeti/Analysis/InnerProductSpace/MoorePenroseInverse.lean:408
- `TauCeti.DavisKahanTheory.directRotationCosine_comm_sinAngleOperator` — DavisKahan/FiniteDimensional/DirectRotation.lean:555
- `TauCeti.DavisKahanTheory.angleOperator_comm_directRotationCosine` — DavisKahan/FiniteDimensional/DirectRotation.lean:586
- `TauCeti.DavisKahanTheory.angleOperator_comm_sinAngleOperator` — DavisKahan/FiniteDimensional/DirectRotation.lean:594
- `TauCeti.DavisKahanTheory.angleOperator_comm_moorePenroseInverse_sinAngleOperator` — DavisKahan/FiniteDimensional/DirectRotation.lean:604
- `TauCeti.DavisKahanTheory.angleOperator_comm_angleComplexStructure` — DavisKahan/FiniteDimensional/DirectRotation.lean:619
- `TauCeti.complementaryProjection_eq_id_sub` — ForTauCeti/Analysis/InnerProductSpace/Spectral/Subspace.lean:135
- `TauCeti.DavisKahanTheory.vectorAngle_directRotation_eq_of_angleOperator_apply` — DavisKahan/FiniteDimensional/DirectRotation/EigenvectorAngle.lean:220
- `TauCeti.DavisKahanTheory.adjoint_angleComplexStructure` — DavisKahan/FiniteDimensional/DirectRotation/EigenvectorAngle.lean:76
- `TauCeti.DavisKahanTheory.re_inner_angleComplexStructure_apply_self` — DavisKahan/FiniteDimensional/DirectRotation/EigenvectorAngle.lean:124
- `TauCeti.DavisKahanTheory.sinAngleOperator_apply_of_angleOperator_apply` — DavisKahan/FiniteDimensional/DirectRotation/EigenvectorAngle.lean:143
- `TauCeti.DavisKahanTheory.directRotationCosine_apply_of_angleOperator_apply` — DavisKahan/FiniteDimensional/DirectRotation/EigenvectorAngle.lean:161
- `TauCeti.DavisKahanTheory.angleOperator_eigenvalue_mem_Icc` — DavisKahan/FiniteDimensional/DirectRotation/EigenvectorAngle.lean:179
- `TauCeti.vectorAngle` — ForTauCeti/Analysis/InnerProductSpace/VectorAngle.lean:68
- `TauCeti.vectorAngle_real_eq_angle` — ForTauCeti/Analysis/InnerProductSpace/VectorAngle.lean:87
- `TauCeti.vectorAngle_eq_angle_rclikeToReal` — ForTauCeti/Analysis/InnerProductSpace/VectorAngle.lean:103
- `TauCeti.vectorAngle_comm` — ForTauCeti/Analysis/InnerProductSpace/VectorAngle.lean:81
- `TauCeti.vectorAngle_eq_of_re_inner_eq` — ForTauCeti/Analysis/InnerProductSpace/VectorAngle.lean:131
- `TauCeti.repr_eq_zero_of_calculus_apply_eq_smul` — ForTauCeti/Analysis/InnerProductSpace/SelfAdjointFunctionalCalculus.lean:311
- `TauCeti.selfAdjointFunctionalCalculus_apply_of_calculus_apply_eq_smul` — ForTauCeti/Analysis/InnerProductSpace/SelfAdjointFunctionalCalculus.lean:347
- `TauCeti.exists_eigenvalue_of_calculus_apply_eq_smul` — ForTauCeti/Analysis/InnerProductSpace/SelfAdjointFunctionalCalculus.lean:370
- `TauCeti.DavisKahanExt.commute_paperAngleOperatorC_starProjection` — DavisKahan/Geometry/Angle/PaperOperatorAngle.lean:265
- `TauCeti.DavisKahanExt.commute_paperAngleOperatorC_starProjection_right` — DavisKahan/Geometry/Angle/PaperOperatorAngle.lean:273
- `TauCeti.DavisKahanExt.commute_sinAngleOperatorC_starProjection` — DavisKahan/Geometry/Angle/PaperOperatorAngle.lean:219
- `TauCeti.DavisKahanExt.commute_sinAngleOperatorC_starProjection_right` — DavisKahan/Geometry/Angle/PaperOperatorAngle.lean:242
- `TauCeti.DavisKahanExt.adjoint_starProjection_sub` — DavisKahan/Geometry/Angle/PaperOperatorAngle.lean:210
- `TauCeti.DavisKahan.Frontier.Section3.IsPrintedFixedCosineReducingSubspace` — DavisKahan/Frontier/Section3.lean:460
- `TauCeti.DavisKahan.Frontier.Section3.fixedCosineSubspace_maximal_printed` — DavisKahan/Frontier/Section3.lean:469
- `TauCeti.DavisKahan.Frontier.Section3.isPrintedFixedCosineReducingSubspace_of_isFixedCosineReducingSubspace` — DavisKahan/Frontier/Section3.lean:490
- `TauCeti.DavisKahan.Frontier.Section3.isFixedCosineReducingSubspace_of_printed` — DavisKahan/Frontier/Section3.lean:478
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_5_fixedAngle_maximal_uniformlyAcute_form` — DavisKahan/Frontier/Section3.lean:526
- `TauCeti.DavisKahan.Frontier.Section3.halmosCosineSq_isSymmetric` — DavisKahan/Frontier/Section3.lean:113
- `TauCeti.DavisKahan.Frontier.Section3.halmosCosineSq_sub_smul_isSymmetric` — DavisKahan/Frontier/Section3.lean:141
- `TauCeti.DavisKahan1970.proposition3_5_directRotation_resolution` — DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:80
- `TauCeti.DavisKahan1970.proposition3_5_commutations` — DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:235
- `TauCeti.DavisKahan1970.proposition3_5_eigenvector_angle` — DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:249
- `TauCeti.DavisKahan1970.proposition3_5_angleEigenspace_eq_fixedCosineSubspace` — DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:257
- `TauCeti.DavisKahan1970.proposition3_5_angleEigenspace_uniqueMaximal` — DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:268
- `TauCeti.DavisKahan1970.proposition3_5_angleOperator` — DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:43
- `TauCeti.DavisKahan1970.proposition3_5_directRotation` — DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:46
- `TauCeti.DavisKahan1970.proposition3_5_quarterTurn` — DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:49
- `TauCeti.DavisKahan1970.proposition3_5_angleEigenspace` — DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:66
- `TauCeti.LinearPMap.cfc_apply_of_apply_eq_real_smul` — ForTauCeti/Analysis/InnerProductSpace/SeparatedIntertwiner.lean:264

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 18. DK-3.2-cor — Reversal symmetry

- **Source anchor:** Corollary 3.2
- **Source kind:** `corollary`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `c680a31852c56ff741530933bb1230243b41cf60da3333c60aca4a31e0ebda7d`
- **Private-transcription provenance lines:** `[[961, 968], [1207, 1209]]`

### Exact registered source passage

~~~~tex
We shall assume \eqref{eq:3.5} as well as \eqref{eq:1.5} except where stated otherwise.
Consequently the direct rotation will always exist, and rather than the more general $V$ of \eqref{eq:1.6} we shall deal mostly with its direct special case
\begin{equation*}
  U\representedby
  \begin{pmatrix}C_0&-S_0^{*}\\S_0&C_1\end{pmatrix},
  \qquad C_j\geq0.
  \tag{3.6}\label{eq:3.6}
\end{equation*}

\begin{corollary}\label{cor:3.2}
If the roles of $P$ and $Q$ are interchanged, $\angles$ remains the same, while $J$ is replaced by $-J$.
\end{corollary}
~~~~

### Semantic audit clauses

- **`DK-3.2-cor.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.corollary3_2_source`, `TauCeti.DavisKahan1970.corollary3_2_paperQuarterTurn_symm`, `TauCeti.DavisKahan1970.corollary3_2_nonacute_directRotation_resolution`, `TauCeti.DavisKahan1970.complex_directRotation_reversal`, `TauCeti.DavisKahan1970.real_directRotation_reversal`, `TauCeti.DavisKahan.Frontier.Section3.corollary3_2_reversal_source_form`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.corollary3_2_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:200`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.corollary3_2_paperQuarterTurn_symm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:170`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.corollary3_2_nonacute_directRotation_resolution`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:152`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.complex_directRotation_reversal`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:132`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.real_directRotation_reversal`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:247`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section3.corollary3_2_reversal_source_form`

Source location candidates: `DavisKahan/Frontier/Section3.lean:1448`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.complex_directRotation_reversal` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:132
- `TauCeti.DavisKahanTheory.directRotation_symm` — DavisKahan/FiniteDimensional/DirectRotation.lean:82
- `TauCeti.DavisKahan.Frontier.Section3.corollary3_2_reversal` — DavisKahan/Frontier/Section3.lean:1467
- `TauCeti.DavisKahan.Frontier.Section3.corollary3_2_reversal_source_form` — DavisKahan/Frontier/Section3.lean:1448
- `TauCeti.DavisKahan.Frontier.Section3.corollary3_2_sinAngleOperator_symm` — DavisKahan/Frontier/Section3.lean:1458
- `TauCeti.DavisKahanTheory.angleComplexStructure_symm` — DavisKahan/FiniteDimensional/DirectRotation.lean:360
- `TauCeti.DavisKahanTheory.angleOperator_comm` — DavisKahan/FiniteDimensional/DirectRotation.lean:517
- `TauCeti.DavisKahanTheory.sinAngleOperator_comm` — DavisKahan/FiniteDimensional/DirectRotation.lean:331
- `TauCeti.DavisKahanTheory.directRotationCosine_comm` — DavisKahan/FiniteDimensional/DirectRotation.lean:343
- `TauCeti.DavisKahan1970.real_directRotation_reversal` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:247
- `TauCeti.DavisKahan1970.corollary3_2_source` — DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:200
- `TauCeti.DavisKahan1970.corollary3_2_nonacute_directRotation_resolution` — DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:152
- `TauCeti.DavisKahan1970.corollary3_2_paperQuarterTurn_symm` — DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:170

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 19. DK-4.1-prop — Pointwise and singular-value extremality of the direct rotation

- **Source anchor:** Proposition 4.1
- **Source kind:** `proposition`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `09ada1a08832709c40382ecedb51bfaad20b3f6662d61ce7f4ca26c709c8fc64`
- **Private-transcription provenance lines:** `[[1223, 1237], [1239, 1245]]`

### Exact registered source passage

~~~~tex
The present section is not required for the rest of the paper.

We shall make the hypotheses of \TheoremRef{3.1} and \CorollaryRef{3.1} (leaving to the reader the modifications entailed in the absence of compactness).
The notation will be
\[
  U\representedby\begin{pmatrix}C_0&-S_0^{*}\\S_0&C_1\end{pmatrix},
  \qquad V=UZ,
  \qquad Z\representedby\begin{pmatrix}Z_0&0\\0&Z_1\end{pmatrix}.
\]
We have introduced the angles $\theta_1\geq\theta_2\geq\cdots$ associated with $P\Hilbert$ and $Q\Hilbert$.
We showed how the sines of these angles can be recovered from any unitary taking $P\Hilbert$ to $Q\Hilbert$.
Among these, the ``direct rotation'' $U$ of \DefinitionRef{3.1} was singled out in two respects: the simple canonical construction of it in terms of $P$ and $Q$ (see \eqref{eq:3.8}) and the decomposition of the space by \eqref{eq:1.18} and \TheoremRef{3.1}.
But the motivation for the direct rotation was the notion of taking elements of $P\Hilbert$ to $Q\Hilbert$ by the most economical route.
This notion cannot be taken naively, for if (say) $\theta_1=\pi/4$, $\theta_2=\pi/6$, then a unitary cannot take every unit vector in $P\Hilbert$ to the unit vector in $Q\Hilbert$ closest to it.
It can almost do this, however, as we now show.

\begin{proposition}\label{prop:4.1}
Given any unitary $V$ which maps $P\Hilbert$ onto $Q\Hilbert$, there exist orthonormal $v_1,v_2,\ldots\in P\Hilbert$ such that for all $k$, $\angle(v_k,Vv_k)\geq\theta_k$.
Equivalent statement: among all such $V$, the singular values $\lambda_1\geq\lambda_2\geq\cdots$ of $(1-V)|_{P\Hilbert}$ are all minimized when $V=U$, and their values then are
\[
  \lambda_k=2\sin(\theta_k/2).
\]
\end{proposition}
~~~~

### Semantic audit clauses

- **`DK-4.1-prop.vector`:** First printed formulation: an orthonormal principal-vector family v_k in P H with angle(v_k, V v_k) >= theta_k.
  - Review declarations: `TauCeti.DavisKahan1970.Proposition4_1_compact_orthonormalVectors`, `TauCeti.DavisKahan1970.Proposition4_1_compact_orthonormalVectors_real`
- **`DK-4.1-prop.singular`:** Equivalent singular-value/approximation-number minimality formulation, including the direct-rotation value 2 sin(theta_k/2).
  - Review declarations: `TauCeti.DavisKahan1970.Proposition4_1_compact_orthonormalVectors`, `TauCeti.DavisKahan1970.Proposition4_1_compact_orthonormalVectors_real`, `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute`, `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_real`, `TauCeti.DavisKahan1970.Proposition4_1_directRotationValues`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Proposition4_1_compact_orthonormalVectors`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4.lean:120`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Proposition4_1_compact_orthonormalVectors_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4Real.lean:965`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4.lean:226`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4Real.lean:1075`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Proposition4_1_directRotationValues`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4.lean:47`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahanTheory.singularValues_restrictedDisplacement_le` — DavisKahan/FiniteDimensional/DirectRotation/PrincipalPlanes/Variational.lean:323
- `TauCeti.DavisKahanTheory.singularValues_restrictedDisplacement_directRotation` — DavisKahan/FiniteDimensional/DirectRotation/PrincipalPlanes/Variational.lean:200
- `TauCeti.DavisKahan1970.Proposition4_1` — DavisKahan/Sources/DavisKahan1970/Section4.lean:42
- `TauCeti.DavisKahan1970.Proposition4_1_directRotationValues` — DavisKahan/Sources/DavisKahan1970/Section4.lean:47
- `TauCeti.DavisKahan1970.Proposition4_1_infiniteDimensional` — DavisKahan/Sources/DavisKahan1970/Section4.lean:89
- `TauCeti.DavisKahan1970.Proposition4_1_real` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:443
- `TauCeti.DavisKahan1970.restrictedDisplacementDominance_real` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:460
- `TauCeti.DavisKahan1970.Proposition4_1_infiniteDimensional_nonacute` — DavisKahan/Sources/DavisKahan1970/Section4.lean:96
- `TauCeti.positiveApproximationEigenvector` — ForTauCeti/Analysis/InnerProductSpace/CompactSpectralDecomposition.lean:283
- `TauCeti.orthonormal_positiveApproximationEigenvector` — ForTauCeti/Analysis/InnerProductSpace/CompactSpectralDecomposition.lean:329
- `TauCeti.apply_positiveApproximationEigenvector` — ForTauCeti/Analysis/InnerProductSpace/CompactSpectralDecomposition.lean:396
- `TauCeti.DavisKahan1970.Proposition4_1_compact_orthonormalVectors` — DavisKahan/Sources/DavisKahan1970/Section4.lean:120
- `TauCeti.DavisKahan1970.Proposition4_1_compact_orthonormalVectors_real` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:965
- `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute` — DavisKahan/Sources/DavisKahan1970/Section4.lean:226
- `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_real` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:1075

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 20. DK-4.1-cor — UI-norm minimality of direct rotation displacement

- **Source anchor:** Corollary 4.1
- **Source kind:** `corollary`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `7a3c0e3316724cc7e8f7639f2c9c23faf124a5bc657d8b16d4ad3efdf4b0b341`
- **Private-transcription provenance lines:** `[[1223, 1237], [1247, 1249]]`

### Exact registered source passage

~~~~tex
The present section is not required for the rest of the paper.

We shall make the hypotheses of \TheoremRef{3.1} and \CorollaryRef{3.1} (leaving to the reader the modifications entailed in the absence of compactness).
The notation will be
\[
  U\representedby\begin{pmatrix}C_0&-S_0^{*}\\S_0&C_1\end{pmatrix},
  \qquad V=UZ,
  \qquad Z\representedby\begin{pmatrix}Z_0&0\\0&Z_1\end{pmatrix}.
\]
We have introduced the angles $\theta_1\geq\theta_2\geq\cdots$ associated with $P\Hilbert$ and $Q\Hilbert$.
We showed how the sines of these angles can be recovered from any unitary taking $P\Hilbert$ to $Q\Hilbert$.
Among these, the ``direct rotation'' $U$ of \DefinitionRef{3.1} was singled out in two respects: the simple canonical construction of it in terms of $P$ and $Q$ (see \eqref{eq:3.8}) and the decomposition of the space by \eqref{eq:1.18} and \TheoremRef{3.1}.
But the motivation for the direct rotation was the notion of taking elements of $P\Hilbert$ to $Q\Hilbert$ by the most economical route.
This notion cannot be taken naively, for if (say) $\theta_1=\pi/4$, $\theta_2=\pi/6$, then a unitary cannot take every unit vector in $P\Hilbert$ to the unit vector in $Q\Hilbert$ closest to it.
It can almost do this, however, as we now show.

\begin{corollary}\label{cor:4.1}
For every unitary-invariant norm, $\norm{(1-V)P}$ is minimized when $V=U$.
\end{corollary}
~~~~

### Semantic audit clauses

- **`DK-4.1-cor.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Corollary4_1_compact_nonacute`, `TauCeti.DavisKahan1970.Corollary4_1_compact_nonacute_real`, `TauCeti.DavisKahan1970.Corollary4_1_infiniteDimensional_nonacute`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Corollary4_1_compact_nonacute`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4.lean:250`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Corollary4_1_compact_nonacute_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4Real.lean:1095`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Corollary4_1_infiniteDimensional_nonacute`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4.lean:281`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahanTheory.uiNorm_restrictedDisplacement_le` — DavisKahan/FiniteDimensional/DirectRotation/PrincipalPlanes/Variational.lean:355
- `TauCeti.DavisKahanTheory.directRotation_minimizes_restrictedDisplacement_uiNorm` — DavisKahan/FiniteDimensional/DirectRotation.lean:194
- `TauCeti.DavisKahan1970.Corollary4_1` — DavisKahan/Sources/DavisKahan1970/Section4.lean:54
- `TauCeti.DavisKahan1970.Corollary4_1_minimizer` — DavisKahan/Sources/DavisKahan1970/Section4.lean:57
- `TauCeti.DavisKahan.Frontier.Section4.corollary4_1_restrictedDisplacement_idealGauge` — DavisKahan/Frontier/Section4.lean:86
- `TauCeti.DavisKahan1970.Corollary4_1_real` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:477
- `TauCeti.DavisKahan1970.Corollary4_1_opNorm_real` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:489
- `TauCeti.DavisKahan1970.Corollary4_1_infiniteDimensional_nonacute` — DavisKahan/Sources/DavisKahan1970/Section4.lean:281
- `TauCeti.DavisKahan1970.Corollary4_1_compact_nonacute` — DavisKahan/Sources/DavisKahan1970/Section4.lean:250
- `TauCeti.DavisKahan1970.Corollary4_1_compact_nonacute_real` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:1095

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 21. DK-4.2-prop — Basis-angle square-sum extremality

- **Source anchor:** Proposition 4.2
- **Source kind:** `proposition`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `6076a83e13dd47c93f09465c856f90fa3e7010dad4d8710b122b70bc5b9a5835`
- **Private-transcription provenance lines:** `[[1223, 1237], [1323, 1329], [1330, 1345]]`

### Exact registered source passage

~~~~tex
The present section is not required for the rest of the paper.

We shall make the hypotheses of \TheoremRef{3.1} and \CorollaryRef{3.1} (leaving to the reader the modifications entailed in the absence of compactness).
The notation will be
\[
  U\representedby\begin{pmatrix}C_0&-S_0^{*}\\S_0&C_1\end{pmatrix},
  \qquad V=UZ,
  \qquad Z\representedby\begin{pmatrix}Z_0&0\\0&Z_1\end{pmatrix}.
\]
We have introduced the angles $\theta_1\geq\theta_2\geq\cdots$ associated with $P\Hilbert$ and $Q\Hilbert$.
We showed how the sines of these angles can be recovered from any unitary taking $P\Hilbert$ to $Q\Hilbert$.
Among these, the ``direct rotation'' $U$ of \DefinitionRef{3.1} was singled out in two respects: the simple canonical construction of it in terms of $P$ and $Q$ (see \eqref{eq:3.8}) and the decomposition of the space by \eqref{eq:1.18} and \TheoremRef{3.1}.
But the motivation for the direct rotation was the notion of taking elements of $P\Hilbert$ to $Q\Hilbert$ by the most economical route.
This notion cannot be taken naively, for if (say) $\theta_1=\pi/4$, $\theta_2=\pi/6$, then a unitary cannot take every unit vector in $P\Hilbert$ to the unit vector in $Q\Hilbert$ closest to it.
It can almost do this, however, as we now show.

\begin{proposition}\label{prop:4.2}
Given any unitary $V$ which maps $P\Hilbert$ onto $Q\Hilbert$, and given any orthonormal basis $\{v_1,v_2,\ldots\}$ of $P\Hilbert$, we have
\[
  \sum_{k=1}^{\infty}\sin^2\angle(v_k,Vv_k)
  \geq\sum_{k=1}^{\infty}\sin^2\theta_k.
\]
\end{proposition}

\begin{proof}
Writing again $v_k\representedby\binom{v_{0k}}{0}$, we have
\[
\begin{aligned}
  \sum_k\sin^2\angle(v_k,Vv_k)
  &=\sum_k\bigl(1-\cos^2\angle(v_k,Vv_k)\bigr)\\
  &=\sum_k\bigl(1-(\RePart v_{0k}^{*}C_0Z_0v_{0k})^2\bigr)\\
  &\geq\sum_k\bigl(1-\abs{v_{0k}^{*}C_0Z_0v_{0k}}^2\bigr)\\
  &\geq\sum_k\left(1-\sum_l\abs{v_{0k}^{*}C_0Z_0v_{0l}}^2\right)\\
  &=\sum_k(1-v_{0k}^{*}C_0^2v_{0k})
   =\tr S_0^{*}S_0\\
  &=\sum_k\sin^2\theta_k,
\end{aligned}
\]
even if the rightmost member is infinite.
This completes the proof.
~~~~

### Semantic audit clauses

- **`DK-4.2-prop.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Proposition4_2_infiniteDimensional`, `TauCeti.DavisKahan1970.tsum_displacementAngleSineSqR_ge_tsum_sq_sin_principalAngleSequence`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Proposition4_2_infiniteDimensional`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4.lean:304`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tsum_displacementAngleSineSqR_ge_tsum_sq_sin_principalAngleSequence`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4Real.lean:696`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan.Section4.sum_displacementAngleSineSq_ge` — DavisKahan/Geometry/Angle/BasisAngleEnergy.lean:213
- `TauCeti.DavisKahan.Section4.displacementAngleSineSq_directRotation_eq_of_smul` — DavisKahan/Geometry/Angle/BasisAngleEnergy.lean:289
- `TauCeti.DavisKahan.Section4.norm_absoluteValue_apply_eq_norm_projection` — DavisKahan/Geometry/Angle/BasisAngleEnergy.lean:92
- `TauCeti.DavisKahan.Section4.norm_inner_competitor_le` — DavisKahan/Geometry/Angle/BasisAngleEnergy.lean:148
- `TauCeti.DavisKahan.Section4.sum_displacementAngleSineSq_ge_of_mem` — DavisKahan/Geometry/Angle/BasisAngleEnergy.lean:249
- `TauCeti.DavisKahan.Section4.tsum_displacementAngleSineSq_ge_of_mem` — DavisKahan/Geometry/Angle/BasisAngleEnergy.lean:268
- `TauCeti.DavisKahan1970.displacementAngleSineSqR` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:501
- `TauCeti.DavisKahan1970.displacementAngleSineSq_ge_real` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:516
- `TauCeti.DavisKahan1970.sum_displacementAngleSineSq_ge_of_mem_real` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:536
- `TauCeti.DavisKahan1970.tsum_displacementAngleSineSq_ge_of_mem_real` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:549
- `TauCeti.DavisKahan.Section4.sum_one_sub_sq_norm_absoluteValue_eq_sum_sq_principalSines` — DavisKahan/Geometry/Angle/BasisAngleEnergy.lean:420
- `TauCeti.DavisKahan.Section4.sum_displacementAngleSineSq_ge_sum_sq_principalSines` — DavisKahan/Geometry/Angle/BasisAngleEnergy.lean:445
- `TauCeti.DavisKahan.Frontier.Section4.proposition4_2_basisAngleSquareSum_principalSines` — DavisKahan/Frontier/Section4.lean:267
- `TauCeti.DavisKahan1970.norm_canonicalAbsoluteValueR_apply_eq_norm_projection` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:581
- `TauCeti.DavisKahan1970.sum_one_sub_sq_norm_canonicalAbsoluteValueR_eq_sum_sq_principalSines` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:604
- `TauCeti.DavisKahan1970.sum_displacementAngleSineSqR_ge_sum_sq_principalSines` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:627
- `TauCeti.DavisKahan1970.Proposition4_2_infiniteDimensional` — DavisKahan/Sources/DavisKahan1970/Section4.lean:304
- `TauCeti.DavisKahan1970.tsum_displacementAngleSineSqR_ge_tsum_sq_principalSineSequence` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:678
- `TauCeti.principalSineSequence` — ForTauCeti/Analysis/InnerProductSpace/PrincipalSineSequence.lean:54
- `TauCeti.principalAngleSequence` — ForTauCeti/Analysis/InnerProductSpace/PrincipalAngleSequence.lean:40
- `TauCeti.sin_principalAngleSequence` — ForTauCeti/Analysis/InnerProductSpace/PrincipalAngleSequence.lean:58
- `TauCeti.DavisKahan.Section4.tsum_displacementAngleSineSq_ge_tsum_sq_sin_principalAngleSequence` — DavisKahan/Geometry/Angle/BasisAngleEnergy.lean:378
- `TauCeti.DavisKahan1970.tsum_displacementAngleSineSqR_ge_tsum_sq_sin_principalAngleSequence` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:696

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 22. DK-4.3-prop — Squared displacement UI-norm minimality

- **Source anchor:** Proposition 4.3
- **Source kind:** `proposition`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `6da0c42a78ae20ed9f7478a157b3f87bbb2699ea1c45ed0a2e09a8833d4a6c1d`
- **Private-transcription provenance lines:** `[[1223, 1237], [1500, 1502]]`

### Exact registered source passage

~~~~tex
The present section is not required for the rest of the paper.

We shall make the hypotheses of \TheoremRef{3.1} and \CorollaryRef{3.1} (leaving to the reader the modifications entailed in the absence of compactness).
The notation will be
\[
  U\representedby\begin{pmatrix}C_0&-S_0^{*}\\S_0&C_1\end{pmatrix},
  \qquad V=UZ,
  \qquad Z\representedby\begin{pmatrix}Z_0&0\\0&Z_1\end{pmatrix}.
\]
We have introduced the angles $\theta_1\geq\theta_2\geq\cdots$ associated with $P\Hilbert$ and $Q\Hilbert$.
We showed how the sines of these angles can be recovered from any unitary taking $P\Hilbert$ to $Q\Hilbert$.
Among these, the ``direct rotation'' $U$ of \DefinitionRef{3.1} was singled out in two respects: the simple canonical construction of it in terms of $P$ and $Q$ (see \eqref{eq:3.8}) and the decomposition of the space by \eqref{eq:1.18} and \TheoremRef{3.1}.
But the motivation for the direct rotation was the notion of taking elements of $P\Hilbert$ to $Q\Hilbert$ by the most economical route.
This notion cannot be taken naively, for if (say) $\theta_1=\pi/4$, $\theta_2=\pi/6$, then a unitary cannot take every unit vector in $P\Hilbert$ to the unit vector in $Q\Hilbert$ closest to it.
It can almost do this, however, as we now show.

\begin{proposition}\label{prop:4.3}
For every unitary-invariant norm, $\norm{(1-V^{*})(1-V)}$ is minimized when $V=U$.
\end{proposition}
~~~~

### Semantic audit clauses

- **`DK-4.3-prop.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Proposition4_3_infiniteDimensional_idealGauge`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Proposition4_3_infiniteDimensional_idealGauge`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4.lean:359`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahanTheory.directRotation_displacementSquare_kyFan` — DavisKahan/FiniteDimensional/DirectRotation/Majorization.lean:499
- `TauCeti.DavisKahanTheory.directRotation_displacementSquare_uiNorm` — DavisKahan/FiniteDimensional/DirectRotation/Majorization.lean:611
- `TauCeti.DavisKahanTheory.directRotation_minimizes_displacementSquare_uiNorm` — DavisKahan/FiniteDimensional/DirectRotation.lean:171
- `TauCeti.DavisKahan1970.Proposition4_3` — DavisKahan/Sources/DavisKahan1970/Section4.lean:73
- `TauCeti.DavisKahan1970.Proposition4_3_kyFan` — DavisKahan/Sources/DavisKahan1970/Section4.lean:69
- `TauCeti.DavisKahan1970.Proposition4_3_minimizer` — DavisKahan/Sources/DavisKahan1970/Section4.lean:76
- `TauCeti.DavisKahan1970.Proposition4_3_infiniteDimensional` — DavisKahan/Sources/DavisKahan1970/Section4.lean:314
- `TauCeti.DavisKahanTheory.directRotation_minimizes_sum_sq_basis_angles` — DavisKahan/FiniteDimensional/DirectRotation.lean:241
- `TauCeti.DavisKahan1970.Proposition4_3_real` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:1131
- `TauCeti.DavisKahan1970.Proposition4_3_infiniteDimensional_idealGauge` — DavisKahan/Sources/DavisKahan1970/Section4.lean:359
- `TauCeti.DavisKahan1970.Proposition4_3_real_idealGauge` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:1160
- `TauCeti.DavisKahan1970.Proposition4_3_infiniteDimensional_nonacute` — DavisKahan/Sources/DavisKahan1970/Section4.lean:319
- `TauCeti.DavisKahan1970.Proposition4_3_infiniteDimensional_nonacute_idealGauge` — DavisKahan/Sources/DavisKahan1970/Section4.lean:376
- `TauCeti.DavisKahan1970.Proposition4_3_nonacute_real` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:867
- `TauCeti.DavisKahan1970.Proposition4_3_nonacute_real_idealGauge` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:945
- `TauCeti.DavisKahan1970.Proposition4_3_compact_nonacute_idealGauge` — DavisKahan/Sources/DavisKahan1970/Section4.lean:395
- `TauCeti.DavisKahan1970.Proposition4_3_compact_nonacute_real_idealGauge` — DavisKahan/Sources/DavisKahan1970/Section4Real.lean:1110

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 23. DK-4.4-prop — Real-space full displacement minimality below pi/3

- **Source anchor:** Proposition 4.4
- **Source kind:** `proposition`
- **Completion obligation:** `true`
- **Census claim:** `refuted_as_transcribed` / `proved_in_build`
- **Registered source excerpt SHA-256:** `66ac9b6a665e40b0ce3946285d0891bb9b26bd01eb9d496dadbfa5cc0aed2aa1`
- **Private-transcription provenance lines:** `[[1223, 1237], [1534, 1537], [1570, 1570]]`

### Exact registered source passage

~~~~tex
The present section is not required for the rest of the paper.

We shall make the hypotheses of \TheoremRef{3.1} and \CorollaryRef{3.1} (leaving to the reader the modifications entailed in the absence of compactness).
The notation will be
\[
  U\representedby\begin{pmatrix}C_0&-S_0^{*}\\S_0&C_1\end{pmatrix},
  \qquad V=UZ,
  \qquad Z\representedby\begin{pmatrix}Z_0&0\\0&Z_1\end{pmatrix}.
\]
We have introduced the angles $\theta_1\geq\theta_2\geq\cdots$ associated with $P\Hilbert$ and $Q\Hilbert$.
We showed how the sines of these angles can be recovered from any unitary taking $P\Hilbert$ to $Q\Hilbert$.
Among these, the ``direct rotation'' $U$ of \DefinitionRef{3.1} was singled out in two respects: the simple canonical construction of it in terms of $P$ and $Q$ (see \eqref{eq:3.8}) and the decomposition of the space by \eqref{eq:1.18} and \TheoremRef{3.1}.
But the motivation for the direct rotation was the notion of taking elements of $P\Hilbert$ to $Q\Hilbert$ by the most economical route.
This notion cannot be taken naively, for if (say) $\theta_1=\pi/4$, $\theta_2=\pi/6$, then a unitary cannot take every unit vector in $P\Hilbert$ to the unit vector in $Q\Hilbert$ closest to it.
It can almost do this, however, as we now show.

\begin{proposition}\label{prop:4.4}
Assume $V$ a unitary taking $P\Hilbert$ onto $Q\Hilbert$ in a real space $\Hilbert$; assume also that $\angles\leq\pi/3$.
Then $\norm{1-V}$ is minimized, for every unitary-invariant norm, when $V=U$.
\end{proposition}

If $\theta$ gets any larger, the conclusion fails because of Example~4.1; in complex space, it fails because of Example~4.2.
~~~~

### Semantic audit clauses

- **`DK-4.4-prop.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahanTheory.DavisKahanProposition4_4_Finite`, `TauCeti.DavisKahanTheory.not_davisKahanProposition4_4_Finite`, `TauCeti.DavisKahanTheory.shortRotation_fullDisplacement_refuted`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahanTheory.DavisKahanProposition4_4_Finite`

Source location candidates: `DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean:639`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahanTheory.not_davisKahanProposition4_4_Finite`

Source location candidates: `DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean:663`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahanTheory.shortRotation_fullDisplacement_refuted`

Source location candidates: `DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean:610`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahanTheory.shortRotation_fullDisplacement_refuted` — DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean:610
- `TauCeti.DavisKahanTheory.DavisKahanProposition4_4_Finite` — DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean:639
- `TauCeti.DavisKahanTheory.not_davisKahanProposition4_4_Finite` — DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean:663

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 24. DK-5.1-thm — Banach-space Sylvester lower bound

- **Source anchor:** Theorem 5.1
- **Source kind:** `theorem`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `0137368cd5d5331a76f9afd4abbec946f3b6450ff0715418372f6776b52636bc`
- **Private-transcription provenance lines:** `[[1576, 1590], [1607, 1607], [1648, 1650]]`

### Exact registered source passage

~~~~tex
\begin{theorem}\label{thm:5.1}
Let $\mathcal X$ and $\mathcal Y$ be Banach spaces; let operators $A$ on $\mathcal Y$ and $B$ on $\mathcal X$ satisfy
\[
  \norm{B}\leq\alpha,
  \qquad
  \norm{A^{-1}}\leq(\alpha+\delta)^{-1}
\]
for some $\alpha\geq0$, $\delta>0$, and for the bound norms on the respective spaces.
For linear transformations from $\mathcal X$ to $\mathcal Y$, use any norm compatible with the bound norms.
Assume $AX-XB=C$.
Then
\[
  \norm{C}\geq\delta\norm{X}.
\]
\end{theorem}

Note that the roles of $A$ and $B$ are symmetrical, so the hypotheses upon them may be interchanged.

Another variation upon the theme of \TheoremRef{5.1} concerns unbounded operators.
Although that theorem was stated for bounded operators $B$ and $X$, its statement and proof encompass the case where $A$ is an unbounded operator with domain dense in $\mathcal Y$; for example, $A$ could be the inverse of a compact operator with dense range (so that $AA^{-1}=1$).
Here is a further variation which allows $B$ to be unbounded too.
~~~~

### Semantic audit clauses

- **`DK-5.1-thm.bounded`:** Printed bounded Banach-space theorem with a genuine inverse A^{-1}, its norm bound, an arbitrary compatible cross-operator norm, AX-XB=C, and delta ||X|| <= ||C||.
  - Review declarations: `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_exact`
- **`DK-5.1-thm.interchange`:** Printed prose remark interchanging the roles/hypotheses of A and B.
  - Review declarations: `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_interchanged_exact`
- **`DK-5.1-thm.unboundedA`:** Printed prose extension allowing densely-defined unbounded A while B and X remain bounded.
  - Review declarations: `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_unboundedA`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:269`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_interchanged_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:274`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_unboundedA`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:276`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.bounded_sylvester_neumann_solution` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:53
- `TauCeti.DavisKahan1970.banach_sylvester_lower_bound` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:264
- `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_uiNorm` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:266
- `TauCeti.DavisKahan.Frontier.RemainingSourceSurface.theorem5_1_banach_sylvester` — DavisKahan/Sources/DavisKahan1970/RemainingSourceSurface.lean:171
- `TauCeti.DavisKahan.Frontier.RemainingSourceSurface.theorem5_1_banach_sylvester_interchanged` — DavisKahan/Sources/DavisKahan1970/RemainingSourceSurface.lean:254
- `TauCeti.DavisKahan.Frontier.RemainingSourceSurface.theorem5_1_banach_sylvester_unboundedA` — DavisKahan/Sources/DavisKahan1970/RemainingSourceSurface.lean:297
- `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_interchanged` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:271
- `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_unboundedA` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:276
- `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_exact` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:269
- `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_interchanged_exact` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:274
- `TauCeti.DavisKahan.Frontier.RemainingSourceSurface.theorem5_1_banach_sylvester_exact` — DavisKahan/Sources/DavisKahan1970/RemainingSourceSurface.lean:233
- `TauCeti.DavisKahan.Frontier.RemainingSourceSurface.theorem5_1_banach_sylvester_interchanged_exact` — DavisKahan/Sources/DavisKahan1970/RemainingSourceSurface.lean:275

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 25. DK-5-hermitian-inequalities — Square-norm and rank-corrected Sylvester inequalities

- **Source anchor:** Section 5, inequalities (5.1) and (5.2)
- **Source kind:** `equation`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `e276ec25f4fbc471721a7a8d9c50f6f761c02f785130051ccd3d724eeb2b01da`
- **Private-transcription provenance lines:** `[[1613, 1646]]`

### Exact registered source passage

~~~~tex
Here is an adumbration of the difficulties.
Suppose $A$ and $B$ are Hermitian matrices, possibly of different dimensions, and suppose $0<\delta\leq\abs{\lambda-\mu}$ for every eigenvalue $\lambda$ of $A$ and $\mu$ of $B$.
Let $C=AX-XB$.
Then the inequality
\begin{equation*}
  \norm{C}_{\mathrm{sq}}\geq\delta\norm{X}_{\mathrm{sq}}
  \qquad\bigl(=\delta\sqrt{\tr X^{*}X}\bigr)
  \tag{5.1}\label{eq:5.1}
\end{equation*}
is easy to prove via the unitary diagonalization of $A$ and $B$.
However, sometimes $\norm{C}_1\ngeq\delta\norm{X}_1$.
To be sure, we may infer from \eqref{eq:5.1} that
\begin{equation*}
  \norm{C}_1\sqrt{\rank C}\geq\delta\norm{X}_1;
  \tag{5.2}\label{eq:5.2}
\end{equation*}
and this inequality has been discovered independently and applied by G.~W. Stewart III~\cite[Theorem~4.6]{Stewart1968} to obtain results similar to but slightly weaker than our $\sin\theta$ \TheoremRef{6.1} and \TheoremRef{6.2}.
But inequality \eqref{eq:5.2} does not promise much help for infinite-dimensional applications.
Besides, \eqref{eq:5.2} is not best possible unless $\rank C\leq1$, whereas \TheoremRef{5.1} and inequality \eqref{eq:5.1} are best possible in a nontrivial sense.
Whether $\rank C$ in \eqref{eq:5.2} can be replaced by a constant is an open
question; certainly the constant $1$ is too small, as can be seen from
\[
  X=\begin{pmatrix}3&-3\\-3&1\end{pmatrix},
  \qquad
  A=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
  \qquad
  B=\begin{pmatrix}0&0\\0&2\end{pmatrix},
  \qquad \delta=1,
\]
for which
\[
  \delta\norm{X}_1=2+\sqrt{10}=5.16\ldots
  >\norm{AX-XB}_1=3\sqrt2=4.24\ldots.
\]
~~~~

### Semantic audit clauses

- **`DK-5-hermitian-inequalities.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan.ExactSinTheta.paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap`, `TauCeti.DavisKahan.ExactSinTheta.paperOperatorNorm_sylvester_le_of_pairwiseSpectrumGap`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan.ExactSinTheta.paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Sylvester/PaperHilbertSchmidt.lean:78`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan.ExactSinTheta.paperOperatorNorm_sylvester_le_of_pairwiseSpectrumGap`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Sylvester/PaperOperatorNorm.lean:73`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan.ExactSinTheta.paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap` — DavisKahan/Sources/DavisKahan1970/Sylvester/PaperHilbertSchmidt.lean:78
- `TauCeti.DavisKahan.ExactSinTheta.paperHilbertSchmidt_sylvester_real_le_of_pairwiseSpectrumGap` — DavisKahan/Sources/DavisKahan1970/Sylvester/PaperHilbertSchmidt.lean:96
- `TauCeti.DavisKahan.ExactSinTheta.paperHilbertSchmidtEnergy_sylvester_le_of_pairwiseSpectrumGap` — DavisKahan/Sources/DavisKahan1970/Sylvester/PaperHilbertSchmidt.lean:38
- `TauCeti.DavisKahan.ExactSinTheta.paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct` — DavisKahan/Sources/DavisKahan1970/Sylvester/HilbertSchmidtPairwise.lean:66
- `TauCeti.DavisKahan.ExactSinTheta.paperOperatorNorm_sylvester_le_of_pairwiseSpectrumGap` — DavisKahan/Sources/DavisKahan1970/Sylvester/PaperOperatorNorm.lean:73
- `TauCeti.DavisKahan.ExactSinTheta.paperOperatorNorm_sylvester_real_le_of_pairwiseSpectrumGap` — DavisKahan/Sources/DavisKahan1970/Sylvester/PaperOperatorNorm.lean:97
- `TauCeti.DavisKahan.ExactSinTheta.paperOperatorNorm_sylvester_le_finrank_range` — DavisKahan/Sources/DavisKahan1970/Sylvester/PaperOperatorNorm.lean:126
- `TauCeti.DavisKahan.ExactSinTheta.sharp52_constant_one_too_small` — DavisKahan/Sources/DavisKahan1970/Sylvester/PaperOperatorNorm.lean:346
- `TauCeti.DavisKahan.ExactSinTheta.sharp52_sylvester` — DavisKahan/Sources/DavisKahan1970/Sylvester/PaperOperatorNorm.lean:266
- `TauCeti.DavisKahan.ExactSinTheta.sharp52_gap` — DavisKahan/Sources/DavisKahan1970/Sylvester/PaperOperatorNorm.lean:334
- `TauCeti.DavisKahan.ExactSinTheta.sharp52_opNorm_X` — DavisKahan/Sources/DavisKahan1970/Sylvester/PaperOperatorNorm.lean:256
- `TauCeti.DavisKahan.ExactSinTheta.sharp52_opNorm_C` — DavisKahan/Sources/DavisKahan1970/Sylvester/PaperOperatorNorm.lean:261

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 26. DK-5.2-thm — Semibounded self-adjoint Sylvester theorem

- **Source anchor:** Theorem 5.2
- **Source kind:** `theorem`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `9b7653bd5df0f630c73e2b3b2963be6cb99f5907d7ef396e09c20c64b55707df`
- **Private-transcription provenance lines:** `[[1652, 1664]]`

### Exact registered source passage

~~~~tex
\begin{theorem}\label{thm:5.2}
Let $\mathcal X$ and $\mathcal Y$ be Hilbert spaces; let $A$ on $\mathcal Y$ and $B$ on $\mathcal X$ be semibounded self-adjoint operators satisfying
\[
  A\geq\gamma+\delta>\gamma\geq B
\]
for some scalars $\gamma$ and $\delta$.
Assume $AX=XB+C$, where $X$ and $C$ are bounded operators from $\mathcal X$ to $\mathcal Y$.
Then
\[
  \norm{C}\geq\delta\norm{X}
\]
for every unitary-invariant norm.
\end{theorem}
~~~~

### Semantic audit clauses

- **`DK-5.2-thm.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Theorem5_2`, `TauCeti.DavisKahan1970.unbounded_sylvester_intervalExterior_uiNorm_genuineSpectrum`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Theorem5_2`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section5.lean:51`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.unbounded_sylvester_intervalExterior_uiNorm_genuineSpectrum`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:89`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan.ExactSinTheta.directOrderedSylvesterEngine_lowerUpper` — DavisKahan/Sylvester/Unbounded/OrderedEngineDirect.lean:25
- `TauCeti.DavisKahan1970.unbounded_sylvester_intervalExterior_uiNorm_genuineSpectrum` — DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:89
- `TauCeti.DavisKahan1970.Theorem5_2` — DavisKahan/Sources/DavisKahan1970/Section5.lean:51
- `TauCeti.DavisKahan.ExactSinTheta.davisKahan1970_sylvester_real` — DavisKahan/Sylvester/RealUnbounded.lean:76
- `TauCeti.DavisKahan.ExactSinTheta.real_unbounded_sylvester_kyFan` — DavisKahan/Sylvester/RealUnbounded.lean:41

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 27. DK-5.1-lem — Strong-cutoff convergence of singular values

- **Source anchor:** Lemma 5.1
- **Source kind:** `lemma`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `fd5f92ac854b05b1737f4e121ce4de1d815a786d4f8966093a2479dad0408c81`
- **Private-transcription provenance lines:** `[[1700, 1703]]`

### Exact registered source passage

~~~~tex
\begin{lemma}\label{lem:5.1}
Let $\Omega(\tau)$ be a family of projectors such that $\Omega(\tau)\to1$ strongly as $\tau\to\infty$; let $\kappa_\nu$ and $\kappa_\nu(\tau)$ be the $\nu$th singular values of $K$ and $K\Omega(\tau)$ respectively.
Then $\kappa_\nu(\tau)\to\kappa_\nu$ also.
\end{lemma}
~~~~

### Semantic audit clauses

- **`DK-5.1-lem.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Lemma5_1`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Lemma5_1`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section5.lean:35`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan.ExactSinTheta.approximationSingularValue_comp_strongProjection_tendsto` — DavisKahan/OperatorIdeal/ApproximationNumbers/ScalarGeneric.lean:132
- `TauCeti.DavisKahan1970.Lemma5_1` — DavisKahan/Sources/DavisKahan1970/Section5.lean:35

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 28. DK-6.1-lem — Direct-sum UI-norm comparison and converse

- **Source anchor:** Lemma 6.1
- **Source kind:** `lemma`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `862500c7811f1974bb6ce020aec9cedba22f3f28f61e8981769fa615c530edac`
- **Private-transcription provenance lines:** `[[1742, 1759]]`

### Exact registered source passage

~~~~tex
\begin{lemma}\label{lem:6.1}
Let $\Omega$ and $\Upsilon$ be projectors.
If
\[
  \norm{\Omega K\Upsilon}\leq\norm{\Omega L\Upsilon}
  \quad\text{and}\quad
  \norm{\widetilde\Omega K\widetilde\Upsilon}
  \leq\norm{\widetilde\Omega L\widetilde\Upsilon}
\]
for all unitary-invariant norms, then
\[
  \norm{\Omega K\Upsilon+\widetilde\Omega K\widetilde\Upsilon}
  \leq
  \norm{\Omega L\Upsilon+\widetilde\Omega L\widetilde\Upsilon}
\]
for all unitary-invariant norms.
The converse holds whenever $\Omega K\Upsilon$ has the same singular values as $\widetilde\Omega K\widetilde\Upsilon$ and $\Omega L\Upsilon$ has the same singular values as $\widetilde\Omega L\widetilde\Upsilon$.
\end{lemma}
~~~~

### Semantic audit clauses

- **`DK-6.1-lem.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.lemma6_1`, `TauCeti.DavisKahan1970.lemma6_1_converse`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.lemma6_1`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:77`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.lemma6_1_converse`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:78`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.lemma6_1` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:77
- `TauCeti.DavisKahan1970.lemma6_1_converse` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:78

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 29. DK-6.2-lem — Reflection-pinch contraction

- **Source anchor:** Lemma 6.2
- **Source kind:** `lemma`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `08a31e182ed2cc092d989a785ee0e01fe7a484f3e8748be4d9d0c35cee3b7760`
- **Private-transcription provenance lines:** `[[1763, 1771]]`

### Exact registered source passage

~~~~tex
\begin{lemma}\label{lem:6.2}
Let $\Omega$ and $\Upsilon$ be projectors.
Then
\[
  \norm{\Omega K\Upsilon+\widetilde\Omega K\widetilde\Upsilon}
  \leq\norm{K}
\]
for all unitary-invariant norms.
\end{lemma}
~~~~

### Semantic audit clauses

- **`DK-6.2-lem.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.lemma6_2`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.lemma6_2`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:79`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.lemma6_2` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:79

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 30. DK-6.1-prop — Symmetric sine theorem

- **Source anchor:** Proposition 6.1
- **Source kind:** `proposition`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `0898b12bd89f52b80c9fb5be54d2b5f803254b87723e1d2907865f825332dd73`
- **Private-transcription provenance lines:** `[[1831, 1836]]`

### Exact registered source passage

~~~~tex
\begin{proposition}[Symmetric $\sin\theta$ theorem]\label{prop:6.1}
For given $\delta>0$, assume that the spectra of $A_0$ and $\Lambda_1$ are separated as in the hypotheses of the $\sin\theta$ theorem, and assume that the spectra of $A_1$ and $\Lambda_0$ are also separated as in the hypotheses of the $\sin\theta$ theorem. Then for every unitary-invariant norm,
\[
  \delta\norm{\sin\angles}\leq \norm{H}.
\]
\end{proposition}
~~~~

### Semantic audit clauses

- **`DK-6.1-prop.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Proposition6_1`, `TauCeti.DavisKahan1970.Proposition6_1_real`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Proposition6_1`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:115`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Proposition6_1_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:127`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.Proposition6_1` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:115
- `TauCeti.DavisKahan1970.RealSymmetricSinThetaProblem` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:126
- `TauCeti.DavisKahan1970.Proposition6_1_real` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:127
- `TauCeti.DavisKahan1970.Proposition6_1_real_kyFan` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:129
- `TauCeti.DavisKahan1970.Proposition6_1_real_sinTheta_singularValues` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:131
- `TauCeti.DavisKahan1970.Proposition6_1_real_sinTheta_eq_literalFullSinAngle` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:133
- `TauCeti.DavisKahan1970.Proposition6_1_real_representative` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:135

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 31. DK-6.1-thm — Generalized sine theorem

- **Source anchor:** Theorem 6.1
- **Source kind:** `theorem`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `f97020c4ed2e67a8509af2e2985a797f8564a4d102e44a64b0e10f971609c68b`
- **Private-transcription provenance lines:** `[[1859, 1870]]`

### Exact registered source passage

~~~~tex
\begin{theorem}[Generalized $\sin\theta$ theorem]\label{thm:6.1}
Assume the Hermitian operator $A+H$ satisfies~\eqref{eq:1.3} and $R$ is given by~\eqref{eq:1.8}. Assume as before that $F_0$ and $F_1$ are isometries with
\[
  F_0F_0^*+F_1F_1^*=1,
\]
but assume regarding $E_0$ only that $E_0^*E_0\geq \varepsilon^2$ for some $\varepsilon>0$. Let $P$ and $Q$ be the projectors onto $\Range(E_0)$ and $\Range(F_0)$, without any hypothesis upon the dimensionality of these subspaces. Let $\sin\angles_0$ be any operator with the same singular values as $P\tQ$.

Assume there is an interval $[\beta,\alpha]$ and a $\delta>0$ such that the spectrum of $A_0$ lies entirely in $[\beta,\alpha]$ while that of $\Lambda_1$ lies entirely outside $({\beta-\delta},{\alpha+\delta})$; or such that the spectrum of $\Lambda_1$ lies entirely in $[\beta,\alpha]$ while that of $A_0$ lies entirely outside $({\beta-\delta},{\alpha+\delta})$. Then, for every unitary-invariant norm,
\[
  \delta\varepsilon\norm{\sin\angles_0}\leq \norm{R}.
\]
\end{theorem}
~~~~

### Semantic audit clauses

- **`DK-6.1-thm.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Theorem6_1`, `TauCeti.DavisKahan1970.Theorem6_1_real`, `TauCeti.DavisKahan1970.Theorem6_1_real_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_1_real_commonCore`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Theorem6_1`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:102`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Theorem6_1_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:105`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Theorem6_1_real_commonDomain`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:200`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Theorem6_1_real_commonCore`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:221`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.Theorem6_1` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:102
- `TauCeti.DavisKahan1970.Theorem6_1_real` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:105
- `TauCeti.DavisKahan1970.Theorem6_1_real_commonDomain` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:200
- `TauCeti.DavisKahan1970.Theorem6_1_real_commonCore` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:221

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 32. DK-6.2-thm — Pairwise-gap square-norm sine theorem

- **Source anchor:** Theorem 6.2
- **Source kind:** `theorem`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `b2dfa6c1c441067a8946addd9e2ccf11d6acb21bd084bbd3a1294e7f9b72b13d`
- **Private-transcription provenance lines:** `[[1908, 1918]]`

### Exact registered source passage

~~~~tex
\begin{theorem}[Second generalized $\sin\theta$ theorem]\label{thm:6.2}
Assume the same as in \TheoremRef{6.1}, except that the only restriction on the spectra is
\[
  \abs{\lambda-a}\geq\delta>0
\]
for every $\lambda\in\spec(\Lambda_1)$ and $a\in\spec(A_0)$. Then
\[
  \delta\varepsilon\norm{\sin\angles_0}_{\mathrm{sq}}
  \leq \norm{R}_{\mathrm{sq}}.
\]
\end{theorem}
~~~~

### Semantic audit clauses

- **`DK-6.2-thm.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Theorem6_2`, `TauCeti.DavisKahan1970.Theorem6_2_real`, `TauCeti.DavisKahan1970.Theorem6_2_real_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_2_real_commonCore`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Theorem6_2`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:142`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Theorem6_2_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:146`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Theorem6_2_real_commonDomain`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:204`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Theorem6_2_real_commonCore`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:224`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.Theorem6_2` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:142
- `TauCeti.DavisKahan1970.Theorem6_2_real` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:146
- `TauCeti.DavisKahan1970.Theorem6_2_real_commonDomain` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:204
- `TauCeti.DavisKahan1970.Theorem6_2_real_commonCore` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:224
- `TauCeti.DavisKahan.ExactSinTheta.PaperTheorem62Data.operatorNorm_result_across_of_rank_le` — DavisKahan/Sources/DavisKahan1970/SineTheta/Theorem62.lean:248, DavisKahan/Sources/DavisKahan1970/SineTheta/Theorem62.lean:455
- `TauCeti.DavisKahan.ExactSinTheta.PaperRealTheorem62Data.operatorNorm_result_across_of_rank_le` — DavisKahan/Sources/DavisKahan1970/SineTheta/Theorem62.lean:248, DavisKahan/Sources/DavisKahan1970/SineTheta/Theorem62.lean:455

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 33. DK-6.3-thm — Generalized tangent theorem

- **Source anchor:** Theorem 6.3
- **Source kind:** `theorem`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `53279da9472354f0db70b73667be22dae5fb2a3e8305f99310bdeed0b0d1a156`
- **Private-transcription provenance lines:** `[[2060, 2073]]`

### Exact registered source passage

~~~~tex
\begin{theorem}[Generalized $\tan\theta$ theorem]\label{thm:6.3}
Assume the Hermitian operator $A+H$ satisfies~\eqref{eq:1.3}, and $R$ is given by~\eqref{eq:1.8} with $A_0=E_0^*(A+H)E_0$. Assume that $E_0,E_1,F_0,F_1$ are isometries satisfying
\[
  E_0E_0^*+E_1E_1^*=F_0F_0^*+F_1F_1^*=1,
\]
whose ranges are invariant subspaces of $A$ and $A+H$, respectively, but assume
\[
  \dim\Xspace(E_0)<\dim\Xspace(F_0)
\]
instead of~\eqref{eq:1.5}. Let $\sin\angles_0$ be any operator whose singular values are the same as those of $E_0^*F_1$. Assume there is a gap of width $\delta>0$ between an interval $[\beta,\alpha]$ containing $A_0$'s spectrum and $[\alpha+\delta,\infty)$ containing the spectrum of $\Lambda_1=F_1^*(A+H)F_1$. Then, for every unitary-invariant norm,
\[
  \delta\norm{\tan\angles_0}\leq\norm{R}.
\]
\end{theorem}
~~~~

### Semantic audit clauses

- **`DK-6.3-thm.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Theorem6_3`, `TauCeti.DavisKahan1970.theorem6_3_all_kyFan_core_infiniteTrial_real`, `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm`, `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Theorem6_3`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanTheta.lean:90`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.theorem6_3_all_kyFan_core_infiniteTrial_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:189`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Directed.lean:73`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:418`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_all_kyFan_core` — DavisKahan/Sources/DavisKahan1970/RemainingSourceSurface.lean:389, DavisKahan/TanTheta/Theorem63FiniteSource.lean:783
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_generalizedTanTheta_source_ideal` — DavisKahan/Sources/DavisKahan1970/RemainingSourceSurface.lean:393, DavisKahan/TanTheta/Theorem63FiniteSource.lean:846
- `TauCeti.DavisKahan.ExactTanTheta.theorem63DirectedTangent` — DavisKahan/TanTheta/Theorem63FiniteSource.lean:950
- `TauCeti.DavisKahan.ExactTanTheta.hasTheorem63DirectedTangentApproximationNumbers_theorem63DirectedTangent` — DavisKahan/TanTheta/Theorem63FiniteSource.lean:990
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_all_kyFan_core_directedTangent` — DavisKahan/TanTheta/Theorem63FiniteSource.lean:1072
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_generalizedTanTheta_source_ideal_directedTangent` — DavisKahan/TanTheta/Theorem63FiniteSource.lean:1092
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_generalizedTanTheta_of_formBounds_equalRank` — DavisKahan/TanTheta/Theorem63FiniteSource.lean:1151
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_generalizedTanTheta_equalRank_spectral` — DavisKahan/TanTheta/Theorem63FiniteSource.lean:1174
- `TauCeti.DavisKahan1970.Theorem6_3` — DavisKahan/Sources/DavisKahan1970/TanTheta.lean:90
- `TauCeti.DavisKahan1970.theorem6_3_all_kyFan_core_infiniteTrial_real` — DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:189
- `TauCeti.DavisKahan1970.theorem63DirectedTangentReal` — DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:322
- `TauCeti.DavisKahan1970.exists_hasTheorem63DirectedTangentApproximationNumbersReal` — DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:388
- `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real` — DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:418
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_infiniteTrial_source_ideal` — DavisKahan/TanTheta/Theorem63InfiniteTrial.lean:804
- `TauCeti.DavisKahan.ExactTanTheta.hasTheorem63DirectedTangentApproximationNumbers_iff_infinite` — DavisKahan/TanTheta/Theorem63InfiniteTrial.lean:777
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_generalizedTanTheta_source_ideal_of_infiniteTrial` — DavisKahan/TanTheta/Theorem63InfiniteTrial.lean:845
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_infiniteTrial_spectral_exists` — DavisKahan/TanTheta/Theorem63InfiniteTrial.lean:871
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_infiniteTrial_of_formBounds` — DavisKahan/TanTheta/Theorem63InfiniteTrial.lean:642
- `TauCeti.DavisKahan.ExactTanTheta.exists_hasTheorem63DirectedTangentApproximationNumbersInfinite` — DavisKahan/TanTheta/Theorem63InfiniteTrial.lean:703
- `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm` — DavisKahan/Sources/DavisKahan1970/Directed.lean:73
- `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_spectral` — DavisKahan/Sources/DavisKahan1970/Directed.lean:122

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 34. DK-6-appendix — Unbounded-operator passage

- **Source anchor:** Appendix to Section 6, equations (6.7)–(6.11)
- **Source kind:** `appendix`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `90f1b6bc70ee4592d14153fc2d901df3e929d8f1638f7707a7fa0748a151f8af`
- **Private-transcription provenance lines:** `[[2118, 2193], [2218, 2260]]`

### Exact registered source passage

~~~~tex
The $\sin\theta$ theorem as stated admits unbounded $\Lambda_1$ (or $A_0$, but not both). It remains valid in the following more general form: assume there is an interval containing the spectrum of $A_0$, while the spectrum of $\Lambda_1$ lies entirely at distance at least $\delta$ from that interval.

If the interval is finite, the conclusion $\delta\norm{\sin\angles_0}\leq\norm{R}$ follows from \TheoremRef{5.1}. If the interval is infinite, say $(-\infty,\alpha]$, there is no conclusion unless $R$ is bounded. We therefore assume that $(A+H)E_0$ and $E_0A_0$ have a common dense domain on which the $R$ defined by~\eqref{eq:1.8} is bounded, and extend $R$ by continuity. \TheoremRef{5.2} then applies exactly as \TheoremRef{5.1} did. The hypotheses of \PropositionRef{6.1} and \TheoremRef{6.1} may be relaxed similarly.

The $\tan\theta$ theorem requires more care because we must both use the technique of \TheoremRef{5.2} and allow for noncompact $\angles$. We give the proof in the general case.

As before, $A_0\leq\alpha$ and $\Lambda_1\geq\alpha+\delta$, but both may now be unbounded. We still have $\norm{R}=\norm{B}$, and only the finite case is interesting. Equation~\eqref{eq:6.5} holds on the common dense domain of $S_0A_0$ and $\Lambda_1S_0$.

Fix $\nu=1,2,\ldots$ and $\varepsilon>0$. We shall choose a $\nu$-projector $\Upsilon$ on $\Xspace(E_0)$ such that the singular values
\[
  \sin\phi_1\geq\sin\phi_2\geq\cdots
\]
of $S_0\Upsilon$ satisfy
\begin{equation*}
  \sum_{k=1}^{\nu}\tan\phi_k
  >\sum_{k=1}^{\nu}\tan\theta_k-\varepsilon
\tag{6.7}\label{eq:6.7}
\end{equation*}
and
\begin{equation*}
  \sum_{k=1}^{\nu}\sin^2\phi_k
  >\sum_{k=1}^{\nu}\sin^2\theta_k-\varepsilon^2.
\tag{6.8}\label{eq:6.8}
\end{equation*}
We shall prove
\[
  \norm{B\Upsilon}_\nu
  \geq\delta\sum_{k=1}^{\nu}\tan\phi_k-\gamma_\varepsilon,
  \qquad \gamma_\varepsilon\to0.
\]
This implies the desired $\nu$-norm estimate and hence, by Ky Fan's theorem, the full result.

By~\eqref{eq:1.13}, there is some $\nu$-projector $\Pi$ satisfying~\eqref{eq:6.8}. For the spectral resolution of $A_0$, write
\[
  -A_0=\int_{-\alpha}^{\infty}\lambda\,d\Omega(\lambda).
\]
Consider $\Omega(\tau)\Pi$ as $\tau\to\infty$. Since $\norm{\widetilde\Omega(\tau)\Pi}\to0$, the subspace $\Omega(\tau)\Pi\Xspace(E_0)$ is ultimately $\nu$-dimensional and approaches $\Pi\Xspace(E_0)$. Let $\Upsilon_\tau$ be its projector. The singular values of $S_0\Upsilon_\tau$ approach those of $S_0\Pi$, so for sufficiently large $\tau$ they satisfy~\eqref{eq:6.8}. Moreover,
\[
  \Upsilon_\tau=\Omega(\tau)\Upsilon_\tau,
  \qquad
  A_0\Upsilon_\tau=\Omega(\tau)A_0\Omega(\tau)\Upsilon_\tau,
\]
and the truncated self-adjoint operator $\Omega(\tau)A_0\Omega(\tau)$ has spectrum in $[-\tau,\alpha]$.

Let $\sin\psi_1\geq\sin\psi_2\geq\cdots$ be the singular values of $S_0\Omega(\tau)$. Then
\[
  \sum_{k=1}^{\nu}\sin^2\psi_k
  -\sum_{k=1}^{\nu}\sin^2\theta_k+\varepsilon^2>0.
\]
Choose $\eta>0$ with $\eta^2$ less than this quantity. Applying~\eqref{eq:1.13} once more, choose a $\nu$-projector $\Upsilon=\Omega(\tau)\Upsilon$ such that the singular values $\sin\phi_k$ of $S_0\Upsilon=S_0\Omega(\tau)\Upsilon$ satisfy
\begin{equation*}
  \sum_{k=1}^{\nu}\sin^2\phi_k
  >\sum_{k=1}^{\nu}\sin^2\psi_k-\eta^2.
\tag{6.9}\label{eq:6.9}
\end{equation*}
They then satisfy~\eqref{eq:6.8} as well.

Choose an orthonormal basis $x_{01},\ldots,x_{0\nu}$ of $\Upsilon\Xspace(E_0)$ consisting of eigenvectors of $\Upsilon S_0^*S_0\Upsilon$, with $x_{0k}$ corresponding to $\sin^2\phi_k$. Choose orthonormal $y_{11},\ldots,y_{1\nu}$ satisfying
\[
  S_0x_{0k}=-\sin\phi_ky_{1k},
  \qquad
  \Upsilon S_0^*y_{1k}=-\sin\phi_kx_{0k},
\]
using vectors from $\Null(\Upsilon S_0^*)$ when necessary. Let
\[
  \Gamma=\sum_{k=1}^{\nu}y_{1k}y_{1k}^*.
\]
Then $S_0\Upsilon=\Gamma S_0\Upsilon$. Multiplying~\eqref{eq:6.5} on the left by $\Gamma$ and on the right by $\Upsilon$ gives
\begin{equation*}
  -\Gamma C_1B\Upsilon
  +\Gamma S_0\bigl(\Omega(\tau)A_0\Omega(\tau)\bigr)\Upsilon
  =(\Gamma\Lambda_1\Gamma)\Gamma S_0\Upsilon.
\tag{6.10}\label{eq:6.10}
\end{equation*}
Both sides are bounded; thus $\Gamma\Lambda_1\Gamma$ is bounded on $\Gamma\Xspace(E_1)$ and has spectrum in $[\alpha+\delta,\infty)$.


Decompose the second term of~\eqref{eq:6.10} as
\[
\begin{aligned}
 \Gamma S_0\bigl(\Omega(\tau)A_0\Omega(\tau)\bigr)\Upsilon
  &=\Gamma S_0\Upsilon(\Upsilon A_0\Upsilon)\\
  &\quad+
  (\Gamma S_0\widetilde\Upsilon\Omega(\tau))
  (\Omega(\tau)A_0\Omega(\tau)\Upsilon).
\end{aligned}
\]
Call the second term $F$. By~\eqref{eq:6.9} and \LemmaRef{6.3},
\[
  \norm{\Gamma S_0\widetilde\Upsilon\Omega(\tau)}_1\leq\eta,
\]
so $\norm{F}_1\leq\eta\tau$. We may choose $\eta$ small enough that $\eta\tau\leq\varepsilon$.

The first term is $\Gamma S_0\Upsilon$ multiplied by a self-adjoint operator whose spectrum is at most $\alpha$. Apply $y_{1k}^*$ on the left and $x_{0k}$ on the right in~\eqref{eq:6.10}, exactly as in~\eqref{eq:6.6}, to obtain
\begin{equation*}
  y_{1k}^*C_1Bx_{0k}+y_{1k}^*Fx_{0k}
  \geq\delta\sin\phi_k.
\tag{6.11}\label{eq:6.11}
\end{equation*}
We have $\abs{y_{1k}^*Fx_{0k}}\leq\varepsilon$.

The Gram matrix of $C_1y_{11},\ldots,C_1y_{1\nu}$ has entries
\[
\begin{aligned}
 y_{1j}^*C_1^2y_{1k}
 &=y_{1j}^*(1-S_0S_0^*)y_{1k}\\
 &=y_{1j}^*(1-S_0\Upsilon S_0^*)y_{1k}
   -y_{1j}^*S_0\widetilde\Upsilon S_0^*y_{1k}.
\end{aligned}
\]
The first term is $\delta_{jk}\cos^2\phi_k$. By~\eqref{eq:6.8} and \LemmaRef{6.3}, $\norm{\Gamma S_0\widetilde\Upsilon}_1\leq\varepsilon$, so the second term is smaller than $\varepsilon^2$.

From~\eqref{eq:6.11} we first obtain the crude estimate
\[
  \delta\sin\phi_k
  \leq\norm{B}_1\norm{C_1y_{1k}}+\varepsilon
  \leq\norm{B}_1(\cos\phi_k+\varepsilon)+\varepsilon.
\]
Letting $\varepsilon\to0$ proves the bound-norm case and provides a positive lower bound on every $\cos\phi_k$, independent of $\varepsilon$. Hence the vectors $(\sec\phi_k)C_1y_{1k}$ can be approximated by an orthonormal set with an error tending to zero. Together with~\eqref{eq:6.7}, this completes the proof for all unitary-invariant norms. The same method allows \TheoremRef{6.3} to be applied to unbounded operators.
~~~~

### Semantic audit clauses

- **`DK-6-appendix.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Theorem6_1_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_1_commonCore`, `TauCeti.DavisKahan1970.Theorem6_1_real_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_1_real_commonCore`, `TauCeti.DavisKahan1970.Theorem6_2_real_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_2_real_commonCore`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Theorem6_1_commonDomain`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:155`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Theorem6_1_commonCore`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:216`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Theorem6_1_real_commonDomain`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:200`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Theorem6_1_real_commonCore`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:221`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Theorem6_2_real_commonDomain`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:204`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Theorem6_2_real_commonCore`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:224`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.Theorem6_1_commonDomain` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:155
- `TauCeti.DavisKahan1970.Theorem6_1_commonCore` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:216
- `TauCeti.DavisKahan1970.Theorem6_1_real_commonDomain` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:200
- `TauCeti.DavisKahan1970.Theorem6_1_real_commonCore` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:221
- `TauCeti.DavisKahan1970.Theorem6_2_real_commonDomain` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:204
- `TauCeti.DavisKahan1970.Theorem6_2_real_commonCore` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:224
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing` — DavisKahan/TanTheta/Theorem63UnboundedInfiniteTrial.lean:588
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_of_reducing` — DavisKahan/TanTheta/Theorem63UnboundedInfiniteTrial.lean:614
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists` — DavisKahan/TanTheta/Theorem63UnboundedInfiniteTrial.lean:640
- `TauCeti.DavisKahan1970.theorem6_3_all_kyFan_core_infiniteData_real` — DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean:251
- `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing_real` — DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean:368
- `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_real` — DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean:534
- `TauCeti.DavisKahan.ExactSinTheta.PaperCommonDomainSymmetricSinThetaProblem` — DavisKahan/Sources/DavisKahan1970/SineTheta/CommonDomainSymmetric.lean:122
- `TauCeti.DavisKahan.ExactSinTheta.PaperCommonDomainSymmetricSinThetaProblem.perturbation_isSymmetric` — DavisKahan/Sources/DavisKahan1970/SineTheta/CommonDomainSymmetric.lean:177
- `TauCeti.DavisKahan.ExactSinTheta.PaperCommonDomainSymmetricSinThetaProblem.forward_all_kyFan` — DavisKahan/Sources/DavisKahan1970/SineTheta/CommonDomainSymmetric.lean:302, DavisKahan/Sources/DavisKahan1970/SineTheta/Symmetric.lean:159, DavisKahan/Sources/DavisKahan1970/SineTheta/SymmetricReal.lean:265
- `TauCeti.DavisKahan.ExactSinTheta.PaperCommonDomainSymmetricSinThetaProblem.reverse_all_kyFan` — DavisKahan/Sources/DavisKahan1970/SineTheta/CommonDomainSymmetric.lean:356, DavisKahan/Sources/DavisKahan1970/SineTheta/Symmetric.lean:226, DavisKahan/Sources/DavisKahan1970/SineTheta/SymmetricReal.lean:326
- `TauCeti.DavisKahan.ExactSinTheta.PaperCommonDomainSymmetricSinThetaProblem.symmetric_all_kyFan` — DavisKahan/Sources/DavisKahan1970/SineTheta/CommonDomainSymmetric.lean:543, DavisKahan/Sources/DavisKahan1970/SineTheta/Symmetric.lean:295
- `TauCeti.DavisKahan.ExactSinTheta.PaperCommonDomainSymmetricSinThetaProblem.result_every_unitarilyInvariantNorm` — DavisKahan/Sources/DavisKahan1970/SineTheta/CommonDomainSymmetric.lean:560, DavisKahan/Sources/DavisKahan1970/SineTheta/CommonDomainTheorems.lean:128, DavisKahan/Sources/DavisKahan1970/SineTheta/CommonDomainTheorems.lean:273
- `TauCeti.DavisKahan.ExactSinTheta.PaperCommonDomainSymmetricSinThetaProblem.ofBounded` — DavisKahan/Sources/DavisKahan1970/SineTheta/CommonDomainSymmetric.lean:573, DavisKahan/SpectralTheory/ClosedOperator/Basic.lean:187, DavisKahan/TanTheta/Theorem63TrialData.lean:135
- `TauCeti.DavisKahan1970.CommonDomainSymmetricSinThetaProblem` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:167
- `TauCeti.DavisKahan1970.Proposition6_1_commonDomain` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:169
- `TauCeti.DavisKahan1970.Proposition6_1_commonDomain_kyFan` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:171
- `TauCeti.DavisKahan1970.Proposition6_1_commonDomain_ofBounded` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:173
- `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_of_reducing_real` — DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean:394
- `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_real` — DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean:559
- `TauCeti.DavisKahan1970.Proposition6_1_real_commonDomain` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:192
- `TauCeti.DavisKahan1970.Proposition6_1_real_commonDomain_kyFan` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:194
- `TauCeti.DavisKahan1970.Proposition6_1_real_commonDomain_ofBounded` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:196
- `TauCeti.DavisKahan1970.Proposition6_1_commonDomain_crossSineSum` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:186
- `TauCeti.DavisKahan1970.Proposition6_1_commonDomain_crossSineSum_kyFan` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:188
- `TauCeti.DavisKahan1970.Proposition6_1_commonDomain_sinTheta_singularValues` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:190
- `TauCeti.DavisKahan.ExactTanTheta.UnboundedCompressionTrialData` — DavisKahan/TanTheta/Theorem63UnboundedCompression.lean:99
- `TauCeti.DavisKahan.ExactTanTheta.UnboundedCompressionTrialData.ofBounded` — DavisKahan/Sources/DavisKahan1970/SineTheta/CommonDomainSymmetric.lean:573, DavisKahan/SpectralTheory/ClosedOperator/Basic.lean:187, DavisKahan/TanTheta/Theorem63TrialData.lean:135
- `TauCeti.DavisKahan.ExactTanTheta.UnboundedCompressionTrialData.ideal_of_formBounds` — DavisKahan/TanTheta/Theorem63TrialData.lean:556, DavisKahan/TanTheta/Theorem63UnboundedCompression.lean:763
- `TauCeti.DavisKahan.ExactTanTheta.UnboundedCompressionTrialData.ideal_of_formBounds_exists` — DavisKahan/TanTheta/Theorem63UnboundedCompression.lean:792
- `TauCeti.DavisKahan.ExactTanTheta.UnboundedCompressionTrialData.ideal_of_reducing_exists` — DavisKahan/TanTheta/Theorem63UnboundedCompression.lean:831
- `TauCeti.DavisKahan.ExactTanTheta.Theorem63TrialData.ofAction` — DavisKahan/TanTheta/Theorem63TrialData.lean:243
- `TauCeti.DavisKahan1970.all_kyFan_core_unboundedCompression_real` — DavisKahan/Sources/DavisKahan1970/UnboundedCompressionReal.lean:266
- `TauCeti.DavisKahan1970.theorem6_3_unboundedCompression_ideal_exists_real` — DavisKahan/Sources/DavisKahan1970/UnboundedCompressionReal.lean:310
- `TauCeti.DavisKahan1970.theorem6_3_unboundedCompression_ideal_of_reducing_exists_real` — DavisKahan/Sources/DavisKahan1970/UnboundedCompressionReal.lean:380
- `TauCeti.DavisKahan1970.theorem6_3_unboundedCompression_ideal_real` — DavisKahan/Sources/DavisKahan1970/UnboundedCompressionReal.lean:345

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 35. DK-6.3-lem — Finite-rank near-maximizer leakage estimate

- **Source anchor:** Lemma 6.3
- **Source kind:** `lemma`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `715e416fd75ce6791ef252fc199779397ebb66f9474ff506d7ae2d2b6b498677`
- **Private-transcription provenance lines:** `[[2194, 2204]]`

### Exact registered source passage

~~~~tex
\begin{lemma}\label{lem:6.3}
Let $K$ have singular values $\kappa_1\geq\kappa_2\geq\cdots$. Let $\Gamma$ and $\Psi$ be $\nu$-projectors such that $K\Psi=\Gamma K\Psi$, and let $\eta>0$. If the singular values $\mu_1\geq\mu_2\geq\cdots$ of $K\Psi$ satisfy
\[
  \sum_{k=1}^{\nu}\mu_k^2
  >\sum_{k=1}^{\nu}\kappa_k^2-\eta^2,
\]
then
\[
  \norm{\Gamma K\widetilde\Psi}_1\leq\eta.
\]
\end{lemma}
~~~~

### Semantic audit clauses

- **`DK-6.3-lem.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan.Frontier.Section6Appendix.lemma6_3_approximationNumber_leakage`, `TauCeti.DavisKahan.Frontier.Section6Appendix.lemma6_3_singularValue_leakage`, `TauCeti.DavisKahan.Frontier.Section6Appendix.lemma6_3_approximationNumber_leakage_real`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan.Frontier.Section6Appendix.lemma6_3_approximationNumber_leakage`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakage.lean:352`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section6Appendix.lemma6_3_singularValue_leakage`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakage.lean:372`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section6Appendix.lemma6_3_approximationNumber_leakage_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakageReal.lean:114`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan.Frontier.Section6Appendix.lemma6_3_approximationNumber_leakage` — DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakage.lean:352
- `TauCeti.DavisKahan.Frontier.Section6Appendix.lemma6_3_singularValue_leakage` — DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakage.lean:372
- `TauCeti.DavisKahan.Frontier.Section6Appendix.lemma6_3_approximationNumber_leakage_of_energySplit` — DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakage.lean:242
- `TauCeti.DavisKahan.Frontier.Section6Appendix.paperHilbertSchmidtEnergy_domain_projection_add_real` — DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakageReal.lean:80
- `TauCeti.DavisKahan.Frontier.Section6Appendix.lemma6_3_approximationNumber_leakage_real` — DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakageReal.lean:114
- `TauCeti.DavisKahan.Frontier.Section6Appendix.lemma6_3_singularValue_leakage_real` — DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakageReal.lean:133

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 36. DK-7-sin2-proof — Reflection proof of the sine double-angle theorem

- **Source anchor:** Section 7, equations (7.1)–(7.5)
- **Source kind:** `proof_package`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `52d975254bf2edd6bf06bdb3b707e8d32d3d0ba2d8e30d1e257b34e59d0d7769`
- **Private-transcription provenance lines:** `[[2263, 2352]]`

### Exact registered source passage

~~~~tex
The new idea is the symmetric perturbation. We use the notation of~\eqref{eq:6.2} and~\eqref{eq:6.3}.
Recall the definitions $X=P-\tP$ and $Q_-=XQX$ and the discussion in \SectionRef{3}. Consider $A+H$ together with the symmetric perturbation
\begin{equation*}
  A+XHX\representedby
  \begin{pmatrix}A_0+H_0&-B^*\\-B&A_1+H_1\end{pmatrix}.
\tag{7.1}\label{eq:7.1}
\end{equation*}
Because it is obtained from $A+H$ by a unitary similarity, it has the same diagonal form; corresponding to~\eqref{eq:6.3},
\begin{equation*}
\begin{pmatrix}A_0+H_0&-B^*\\-B&A_1+H_1\end{pmatrix}
\begin{pmatrix}C_0&S_0^*\\-S_0&C_1\end{pmatrix}
=
\begin{pmatrix}C_0&S_0^*\\-S_0&C_1\end{pmatrix}
\begin{pmatrix}\Lambda_0&0\\0&\Lambda_1\end{pmatrix}.
\tag{7.2}\label{eq:7.2}
\end{equation*}
The unitary appearing here is the inverse of the one in~\eqref{eq:6.2} and~\eqref{eq:6.3}.

Combining~\eqref{eq:6.3} and~\eqref{eq:7.2},
\begin{equation*}
\begin{pmatrix}A_0+H_0&B^*\\B&A_1+H_1\end{pmatrix}
\begin{pmatrix}C_0&-S_0^*\\S_0&C_1\end{pmatrix}^{2}
=
\begin{pmatrix}C_0&-S_0^*\\S_0&C_1\end{pmatrix}^{2}
\begin{pmatrix}A_0+H_0&-B^*\\-B&A_1+H_1\end{pmatrix},
\tag{7.3}\label{eq:7.3}
\end{equation*}
or simply
\[
  (A+H)U^2=U^2(A+XHX).
\]
The unitary is
\begin{equation*}
U^2\representedby
\begin{pmatrix}
  2C_0^2-1&-2C_0S_0^*\\
  2S_0C_0&2C_1^2-1
\end{pmatrix}
=
\begin{pmatrix}
  \cos2\angles_0&-J_0^*\sin2\angles_1\\
  J_0\sin2\angles_0&\cos2\angles_1
\end{pmatrix}.
\tag{7.4}\label{eq:7.4}
\end{equation*}
By \PropositionRef{3.4}, although this unitary need not be the direct rotation from $Q_-\Hilbert$ to $Q\Hilbert$, it satisfies $U^2Q_-=QU^2$.

We obtain the $\sin2\theta$ theorem by regarding $A+H$ as a perturbation not of $A$, but of $A+XHX$. The perturbation is $H-XHX$. The parts of $A+H$ on $Q\Hilbert$ and $\tQ\Hilbert$ remain
\[
  \Lambda_j=F_j^*(A+H)F_j.
\]
The roles of $A_0,A_1$ are now taken by the parts of $A+XHX$ on $Q_-\Hilbert$ and $\widetilde Q_-\Hilbert$:
\[
  \Lambda_j=(XF_j)^*(A+XHX)XF_j.
\]
Thus the hypotheses on the spectra of $\Lambda_0$ and $\Lambda_1$ permit us to invoke \PropositionRef{6.1}. In place of $E_0^*F_1$ we examine
\[
  (XF_0)^*F_1=2(F_0^*E_0)(E_0^*F_1),
\]
whose relevant singular values are those of $\sin2\angles_0$. \PropositionRef{6.1} yields
\begin{equation*}
  \delta\norm{\sin2\angles}
  \leq\norm{H-XHX}
  \leq\norm{H}+\norm{XHX}
  =2\norm{H}.
\tag{7.5}\label{eq:7.5}
\end{equation*}
To obtain the residual version, rewrite the first inequality as
\[
  \delta
  \norm{\begin{pmatrix}
    0&-\sin2\angles_0J_0^*\\
    J_0\sin2\angles_0&0
  \end{pmatrix}}
  \leq
  \norm{\begin{pmatrix}0&B^*\\B&0\end{pmatrix}}
\]
and invoke \LemmaRef{6.1}. Hence
\[
  \delta\norm{\sin2\angles_0}\leq\norm{B}\leq\norm{R}.
\]
This completes the proof of the $\sin2\theta$ theorem.

The inference $\delta\norm{\sin2\angles}\leq2\norm{H}$ may also be drawn from one or two gaps of width $\delta$ in the spectrum of $A$ instead of $\Lambda$, by interchanging $A$ and $A+H$. The residual inference is asymmetric: if
\[
  A\representedby\begin{pmatrix}0&0\\0&\delta\end{pmatrix},
  \qquad
  H\representedby\begin{pmatrix}0&1\\1&-\delta\end{pmatrix},
\]
then $2\norm{R}=2$, whereas $\delta\norm{\sin2\angles_0}=\delta$ can be arbitrarily large.
~~~~

### Semantic audit clauses

- **`DK-7-sin2-proof.reflection`:** Reflection/symmetric-perturbation identities (7.1)-(7.4), including the doubled-angle overlap representation.
  - Review declarations: `TauCeti.DavisKahan1970.sinTwoTheta_mirrorDefect_eq_perturbationDefect`, `TauCeti.DavisKahan1970.sinTwoTheta_reflectedOverlap_norm`
- **`DK-7-sin2-proof.ambient`:** Ambient estimate (7.5): delta ||sin 2 Theta|| <= ||H-XHX|| <= 2 ||H||.
  - Review declarations: `TauCeti.DavisKahan1970.sinTwoTheta_mirrorDefect_le_two_mul`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative`
- **`DK-7-sin2-proof.directed`:** Sharper directed residual conclusion: delta ||sin 2 Theta_0|| <= ||B|| <= ||R||, without the ambient factor two.
  - Review declarations: `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative`

> **Audit warning:** The maintained modernized transcription records a factor-one directed residual step in Section 7, while the Section 2 theorem prints factor two and repository repair notes question the block normalization. Preserve the transcription in this register, but compare this passage against the original paper page image before deciding whether the factor-one line is an independent source obligation or a transcription/source defect.

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.sinTwoTheta_mirrorDefect_eq_perturbationDefect`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:70`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.sinTwoTheta_mirrorDefect_le_two_mul`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:80`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.sinTwoTheta_reflectedOverlap_norm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:97`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.sinTwoTheta_mirrorDefect_eq_perturbationDefect` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:70
- `TauCeti.DavisKahan1970.sinTwoTheta_mirrorDefect_le_two_mul` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:80
- `TauCeti.DavisKahan1970.sinTwoTheta_reflectedOverlap_norm` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:97
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:166
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative` — DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:254

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 37. DK-7-tan2-proof — Singular-vector proof of the tangent double-angle theorem

- **Source anchor:** Section 7, equation (7.6) and following argument
- **Source kind:** `proof_package`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `a1c1d0ae88cf3ad76b63fe564b68e426cb2f6d0aeda61b4751598de187533786`
- **Private-transcription provenance lines:** `[[2354, 2414]]`

### Exact registered source passage

~~~~tex
\paragraph{Proof of the $\tan2\theta$ theorem.}
The proof imitates the $\tan\theta$ proof rather than applying a single-angle theorem. We give details for bounded operators and compact $S_0$; the extension is analogous to the one above.

The hypotheses are
\[
  H_0=H_1=0,
  \qquad A_0\leq\alpha,
  \qquad \alpha+\delta\leq A_1.
\]
From~\eqref{eq:1.7},
\[
  F_0^*(A+H)F_1
  =(C_0\;S_0^*)
  \begin{pmatrix}A_0&B^*\\B&A_1\end{pmatrix}
  \begin{pmatrix}-S_0^*\\C_1\end{pmatrix}=0,
\]
so
\begin{equation*}
  -C_0B^*C_1+S_0^*BS_0^*
  =S_0^*A_1C_1-C_0A_0S_0^*.
\tag{7.6}\label{eq:7.6}
\end{equation*}
Let $x_{01},\ldots,x_{0\nu}$ and $y_{11},\ldots,y_{1\nu}$ be orthonormal eigenvectors of $S_0^*S_0$ and $S_0S_0^*$, respectively, arranged so that
\[
  S_0x_{0j}=\mp\sin\theta_jy_{1j},
  \qquad
  S_0^*y_{1j}=\mp\sin\theta_jx_{0j}.
\]
The sign will be chosen momentarily. Applying these vectors to~\eqref{eq:7.6} yields
\[
\begin{aligned}
 &\pm\bigl(\cos^2\theta_j\,x_{0j}^*B^*y_{1j}
       -\sin^2\theta_j\,y_{1j}^*Bx_{0j}\bigr)\\
 &\qquad
 =\pm x_{0j}^*(C_0B^*C_1-S_0^*BS_0^*)y_{1j}\\
 &\qquad
 =\sin\theta_j\cos\theta_j
   \bigl(y_{1j}^*A_1y_{1j}-x_{0j}^*A_0x_{0j}\bigr)\\
 &\qquad\geq\delta\sin\theta_j\cos\theta_j,
\end{aligned}
\]
and hence
\[
  \pm2\cos2\theta_j\,
  \RePart(y_{1j}^*Bx_{0j})
  \geq\delta\sin2\theta_j.
\]
Thus $\cos2\theta_j\ne0$. Choose the sign so that
\[
  2\RePart(y_{1j}^*Bx_{0j})
  \geq\delta\abs{\tan2\theta_j}.
\]
Therefore
\[
  2\norm{B}_\nu\geq\delta\norm{\tan2\angles_0}_\nu.
\]
Ky Fan's theorem gives
\[
  \delta\norm{\tan2\angles_0}\leq2\norm{R}.
\]
The whole-space estimate follows by \LemmaRef{6.1}.
~~~~

### Semantic audit clauses

- **`DK-7-tan2-proof.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.tanTwoTheta_uiNorm`, `TauCeti.DavisKahan1970.tanTwoTheta_kyFan`, `TauCeti.DavisKahan1970.tanTwoTheta_sharp_opNorm`, `TauCeti.DavisKahan1970.tanTwoTheta_spectral_repulsion`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.tanTwoTheta_uiNorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanTwoTheta.lean:132`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_kyFan`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanTwoTheta.lean:136`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_sharp_opNorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanTwoTheta.lean:177`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_spectral_repulsion`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanTwoTheta.lean:182`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.tanTwoTheta_uiNorm` — DavisKahan/Sources/DavisKahan1970/TanTwoTheta.lean:132
- `TauCeti.DavisKahan1970.tanTwoTheta_kyFan` — DavisKahan/Sources/DavisKahan1970/TanTwoTheta.lean:136
- `TauCeti.DavisKahan1970.tanTwoTheta_uiIdeal_infinite` — DavisKahan/Sources/DavisKahan1970/TanTwoTheta.lean:150
- `TauCeti.DavisKahan1970.tanTwoTheta_kyFan_infinite` — DavisKahan/Sources/DavisKahan1970/TanTwoTheta.lean:155
- `TauCeti.DavisKahan1970.tanTwoTheta_sharp_opNorm` — DavisKahan/Sources/DavisKahan1970/TanTwoTheta.lean:177
- `TauCeti.DavisKahan1970.tanTwoTheta_spectral_repulsion` — DavisKahan/Sources/DavisKahan1970/TanTwoTheta.lean:182
- `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_residual_opNorm` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedResidual.lean:92
- `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_residual_div` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedResidual.lean:124

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 38. DK-8.1-thm — Branch selection and spectral repulsion

- **Source anchor:** Theorem 8.1
- **Source kind:** `theorem`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `dad2a4e3936fd9e312e170375c57ed7fb19f3a0bd54b3f811fec8da4f477679a`
- **Private-transcription provenance lines:** `[[2426, 2455]]`

### Exact registered source passage

~~~~tex
\begin{theorem}\label{thm:8.1}
Assume the hypotheses of the $\tan2\theta$ theorem. Then $\angles\leq\pi/4$ if and only if
\[
  \Lambda_1\geq\alpha+\delta,
  \qquad
  \Lambda_0\leq\alpha.
\]
For fixed $A,P,H$, there always exists a reducing projector $Q$ with these properties. For this $Q$ the following stronger inequalities hold.
\begin{enumerate}[label=(\roman*)]
\item
\[
  A_1-\alpha\leq C_1(\Lambda_1-\alpha)C_1,
\]
with a similar relation for $A_0$.
\item In finite dimensions, if $\lambda_1\leq\lambda_2\leq\cdots$ are the eigenvalues of $\Lambda_1$ and $\alpha_1\leq\alpha_2\leq\cdots$ those of $A_1$, then
\[
  \alpha_k-\alpha\leq\norm{C_1}_1^2(\lambda_k-\alpha),
\]
with a similar relation for $\Lambda_0$, and natural infinite-dimensional extensions.
\item In finite dimensions,
\[
  \Phi(\alpha_1-\alpha,\ldots,\alpha_n-\alpha)
  \leq
  \Phi\bigl((\lambda_1-\alpha)\cos^2\theta_1,
             \ldots,
             (\lambda_n-\alpha)\cos^2\theta_n\bigr)
\]
for every symmetric gauge function $\Phi$, with a similar relation for $\Lambda_0$.
\end{enumerate}
\end{theorem}
~~~~

### Semantic audit clauses

- **`DK-8.1-thm.branch`:** Theta <= pi/4 iff the selected Lambda blocks lie on the prescribed sides of alpha, together with existence of a reducing projector Q having those properties.
  - Review declarations: `TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch`, `TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_spectrumIn`
- **`DK-8.1-thm.i`:** Part (i): operator compression/sandwich inequality for A_1-alpha and C_1(Lambda_1-alpha)C_1, and the analogous lower block.
  - Review declarations: `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_source`
- **`DK-8.1-thm.ii`:** Part (ii): finite-dimensional eigenvalue inequalities and their natural infinite-dimensional approximation-number extensions.
  - Review declarations: `TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_source`
- **`DK-8.1-thm.iii`:** Part (iii): symmetric-gauge/weak-majorization inequalities with principal-cosine weights, plus the analogous lower-block relation.
  - Review declarations: `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_source`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_source`

Source location candidates: `DavisKahan/Frontier/Section8.lean:1015`, `DavisKahan/Frontier/Section8SourceSurface.lean:96`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_source`

Source location candidates: `DavisKahan/Frontier/Section8.lean:1063`, `DavisKahan/Frontier/Section8SourceSurface.lean:101`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSandwichApproximation_source`

Source location candidates: `DavisKahan/Frontier/Section8PartII.lean:339`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSandwichApproximation_source`

Source location candidates: `DavisKahan/Frontier/Section8PartII.lean:484`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch` — DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81.lean:249
- `TauCeti.DavisKahan1970.Section8.theorem8_1_eq_canonicalBranch_of_maximalAngle_le` — DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81.lean:394
- `TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_spectrumIn` — DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81.lean:494
- `TauCeti.DavisKahan1970.Section8.Theorem81Conclusion` — DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81.lean:221
- `TauCeti.DavisKahan1970.Section8.canonicalLowBranch` — DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81.lean:210
- `TauCeti.DavisKahan.realSpectrum_add_offDiagonal_subset_exterior_of_form_gap` — DavisKahan/InfiniteDimensional/TanTwoTheta/OffDiagonalSpectralRepulsion.lean:90
- `TauCeti.DavisKahanExt.re_inner_le_of_mem_boundedSelfAdjointSpectralSubspace_Iic` — DavisKahan/SpectralTheory/SpectralGapFormBounds.lean:136
- `TauCeti.DavisKahanExt.le_re_inner_of_mem_boundedSelfAdjointSpectralSubspace_Iic_orthogonal` — DavisKahan/SpectralTheory/SpectralGapFormBounds.lean:209
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_source` — DavisKahan/Frontier/Section8.lean:1015, DavisKahan/Frontier/Section8SourceSurface.lean:96
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_source` — DavisKahan/Frontier/Section8.lean:1063, DavisKahan/Frontier/Section8SourceSurface.lean:101
- `TauCeti.DavisKahan.Frontier.Section8.theorem8_1_upperCompressionRepulsion_canonicalBranch` — DavisKahan/Frontier/Section8.lean:870
- `TauCeti.DavisKahan.Frontier.Section8.theorem8_1_lowerCompressionRepulsion_canonicalBranch` — DavisKahan/Frontier/Section8.lean:937
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSandwichApproximation_source` — DavisKahan/Frontier/Section8PartII.lean:339
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSandwichApproximation_source` — DavisKahan/Frontier/Section8PartII.lean:484
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_source` — DavisKahan/Frontier/Section8PartII.lean:419
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_source` — DavisKahan/Frontier/Section8PartII.lean:548
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_angle_source` — DavisKahan/Frontier/Section8SourceDictionary.lean:301
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_angle_source` — DavisKahan/Frontier/Section8SourceDictionary.lean:321
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperWeightedWeakMajorization_source` — DavisKahan/Frontier/Section8PartIII.lean:120
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerWeightedWeakMajorization_source` — DavisKahan/Frontier/Section8PartIII.lean:221
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_source` — DavisKahan/Frontier/Section8PartIII.lean:180
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_source` — DavisKahan/Frontier/Section8PartIII.lean:280
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_source` — DavisKahan/Frontier/Section8SourceDictionary.lean:350
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_source` — DavisKahan/Frontier/Section8SourceDictionary.lean:390
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_source` — DavisKahan/Frontier/Section8SourceDictionary.lean:437
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev_source` — DavisKahan/Frontier/Section8SourceDictionary.lean:490
- `TauCeti.singularValues_adjoint_sandwich_weaklyMajorized` — ForTauCeti/Analysis/InnerProductSpace/SandwichMajorization.lean:365
- `TauCeti.approximationNumber_adjoint_sandwich_weaklyMajorized` — ForTauCeti/Analysis/InnerProductSpace/SandwichMajorization.lean:390
- `TauCeti.DavisKahan1970.Section8.approximationNumber_eq_eigenvalues_of_isPositive` — DavisKahan/Frontier/Section8SourceDictionary.lean:147
- `TauCeti.DavisKahan1970.Section8.approximationNumber_upperBlockShift_eq_zero_of_le` — DavisKahan/Frontier/Section8SourceDictionary.lean:185
- `TauCeti.DavisKahan1970.Section8.approximationNumber_lowerBlockShift_eq_zero_of_le` — DavisKahan/Frontier/Section8SourceDictionary.lean:194
- `TauCeti.DavisKahan1970.Section8.approximationNumber_cosineBlock_eq_principalCosines` — DavisKahan/Frontier/Section8SourceDictionary.lean:211
- `TauCeti.DavisKahan1970.Section8.approximationNumber_lowerCosineBlock_eq_principalCosines` — DavisKahan/Frontier/Section8SourceDictionary.lean:222
- `TauCeti.DavisKahan1970.Section8.norm_cosineBlock_eq_principalCosines_zero` — DavisKahan/Frontier/Section8SourceDictionary.lean:263
- `TauCeti.DavisKahan1970.Section8.norm_lowerCosineBlock_eq_principalCosines_zero` — DavisKahan/Frontier/Section8SourceDictionary.lean:271
- `TauCeti.DavisKahan1970.Section8.cos_arccos_approximationNumber_cosineBlock` — DavisKahan/Frontier/Section8SourceDictionary.lean:247
- `TauCeti.DavisKahan1970.Section8.maximalAngle_le_pi_div_six_iff` — DavisKahan/Frontier/Section8SourceDictionary.lean:848
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_of_rotatedBlockData` — DavisKahan/Sources/DavisKahan1970/Section8/SourceSurface.lean:100
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_of_rotatedBlockData` — DavisKahan/Sources/DavisKahan1970/Section8/SourceSurface.lean:104
- `TauCeti.DavisKahan1970.Section8.Theorem81ConclusionReal` — DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81Real.lean:48
- `TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch_real` — DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81Real.lean:78
- `TauCeti.DavisKahan1970.Section8.theorem8_1_eq_of_maximalAngle_le_real` — DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81Real.lean:175
- `TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_spectrumIn_real` — DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81Real.lean:240
- `TauCeti.DavisKahan.Foundation.realSpectrum_subset_Iic_of_re_inner_le_generic` — DavisKahan/SpectralTheory/FormSpectrumBounds.lean:35
- `TauCeti.DavisKahan.Foundation.realSpectrum_subset_Ici_of_le_re_inner_generic` — DavisKahan/SpectralTheory/FormSpectrumBounds.lean:60
- `TauCeti.DavisKahan.Foundation.spectrumIn_Iic_of_re_inner_le_generic` — DavisKahan/SpectralTheory/FormSpectrumBounds.lean:89
- `TauCeti.DavisKahan.Foundation.spectrumIn_Ici_of_le_re_inner_generic` — DavisKahan/SpectralTheory/FormSpectrumBounds.lean:103
- `TauCeti.DavisKahan1970.Section8.complexify_upperBlockShift` — DavisKahan/Frontier/Section8PartIIReal.lean:81
- `TauCeti.DavisKahan1970.Section8.complexify_cosineBlock` — DavisKahan/Frontier/Section8PartIIReal.lean:92
- `TauCeti.DavisKahan1970.Section8.complexify_lowerBlockShift` — DavisKahan/Frontier/Section8PartIIReal.lean:100
- `TauCeti.DavisKahan1970.Section8.complexify_lowerCosineBlock` — DavisKahan/Frontier/Section8PartIIReal.lean:111
- `TauCeti.DavisKahan1970.Section8.complexify_adjoint_sandwich` — DavisKahan/Frontier/Section8PartIIReal.lean:118
- `TauCeti.DavisKahan1970.Section8.theorem8_1_spectralRepulsion_real` — DavisKahan/Frontier/Section8PartIIReal.lean:131
- `TauCeti.DavisKahan1970.Section8.canonicalLowBranchReal` — DavisKahan/Frontier/Section8PartIIReal.lean:150
- `TauCeti.DavisKahan1970.Section8.complexifySubmodule_canonicalLowBranchReal` — DavisKahan/Frontier/Section8PartIIReal.lean:182
- `TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch_complexified` — DavisKahan/Frontier/Section8PartIIReal.lean:207
- `TauCeti.DavisKahan1970.Section8.canonicalLowBranchReal_form_low` — DavisKahan/Frontier/Section8PartIIReal.lean:233
- `TauCeti.DavisKahan1970.Section8.canonicalLowBranchReal_form_high` — DavisKahan/Frontier/Section8PartIIReal.lean:259
- `TauCeti.DavisKahan1970.Section8.theorem8_1_perturbedUpperBlockShift_nonneg_real` — DavisKahan/Frontier/Section8PartIIReal.lean:289
- `TauCeti.DavisKahan1970.Section8.theorem8_1_perturbedLowerBlockShift_nonneg_real` — DavisKahan/Frontier/Section8PartIIReal.lean:307
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSandwichApproximation_real` — DavisKahan/Frontier/Section8PartIIReal.lean:471
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_real` — DavisKahan/Frontier/Section8PartIIReal.lean:536
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSandwichApproximation_real` — DavisKahan/Frontier/Section8PartIIReal.lean:560
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_real` — DavisKahan/Frontier/Section8PartIIReal.lean:622
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperWeightedWeakMajorization_real` — DavisKahan/Frontier/Section8PartIIIReal.lean:75
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_real` — DavisKahan/Frontier/Section8PartIIIReal.lean:131
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerWeightedWeakMajorization_real` — DavisKahan/Frontier/Section8PartIIIReal.lean:163
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_real` — DavisKahan/Frontier/Section8PartIIIReal.lean:216
- `TauCeti.DavisKahan1970.Section8.isPositive_toLinearMap_of_nonneg` — DavisKahan/Frontier/Section8SourceDictionary.lean:158
- `TauCeti.DavisKahan1970.Section8.range_upperBlockShift_le` — DavisKahan/Frontier/Section8SourceDictionary.lean:166
- `TauCeti.DavisKahan1970.Section8.range_lowerBlockShift_le` — DavisKahan/Frontier/Section8SourceDictionary.lean:174
- `TauCeti.DavisKahan1970.Section8.norm_cosineBlock_le_one` — DavisKahan/Frontier/Section8SourceDictionary.lean:234
- `TauCeti.DavisKahan1970.Section8.arcsin_one_div_two` — DavisKahan/Frontier/Section8SourceDictionary.lean:841
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_angle_real` — DavisKahan/Frontier/Section8SourceDictionary.lean:581
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_angle_real` — DavisKahan/Frontier/Section8SourceDictionary.lean:604
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_real` — DavisKahan/Frontier/Section8SourceDictionary.lean:632
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_real` — DavisKahan/Frontier/Section8SourceDictionary.lean:673
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_real` — DavisKahan/Frontier/Section8SourceDictionary.lean:715
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev_real` — DavisKahan/Frontier/Section8SourceDictionary.lean:770
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_real` — DavisKahan/Frontier/Section8PartIIReal.lean:341
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_real` — DavisKahan/Frontier/Section8PartIIReal.lean:404

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 39. DK-8.2-thm — Smallness selects the acute branch

- **Source anchor:** Theorem 8.2
- **Source kind:** `theorem`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `bd514c221ed24a8644c82ed2f1af807064b2ed250c875bebffe88c2d6fa76b31`
- **Private-transcription provenance lines:** `[[2514, 2528]]`

### Exact registered source passage

~~~~tex
\begin{theorem}\label{thm:8.2}
Add to the hypotheses of the $\sin2\theta$ theorem either
\[
  \norm{H}_1<\delta/2
  \qquad\text{or}\qquad
  \norm{R}_1<\delta/2,
\]
and assume the spectrum of $A_0$ lies in $[\beta-\delta/2,\alpha+\delta/2]$. Then, in addition to
\[
  \delta\norm{\sin2\angles}\leq2\norm{H}
  \quad\text{or}\quad
  \delta\norm{\sin2\angles_0}\leq2\norm{R},
\]
we have $\angles<\pi/4$.
\end{theorem}
~~~~

### Semantic audit clauses

- **`DK-8.2-thm.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_paperUINorm`, `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_real_paperUINorm`, `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_source_paperUINorm`, `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_directed`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_paperUINorm`

Source location candidates: `DavisKahan/Frontier/Section8SourceSurface.lean:207`, `DavisKahan/Frontier/Section8SourceTheorem82.lean:431`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_real_paperUINorm`

Source location candidates: `DavisKahan/Frontier/Section8SourceSurface.lean:284`, `DavisKahan/Frontier/Section8SourceTheorem82Real.lean:553`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_source_paperUINorm`

Source location candidates: `DavisKahan/Frontier/Section8SourceSurface.lean:216`, `DavisKahan/Frontier/Section8SourceTheorem82.lean:507`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_directed`

Source location candidates: `DavisKahan/Frontier/Section8SourceSurface.lean:123`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_source` — DavisKahan/Frontier/Section8Perturbation.lean:1130, DavisKahan/Frontier/Section8SourceSurface.lean:112
- `TauCeti.DavisKahan1970.Section8.theorem8_2_residualHalfGap_source` — DavisKahan/Frontier/Section8Residual.lean:159, DavisKahan/Frontier/Section8SourceSurface.lean:117
- `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_directed` — DavisKahan/Frontier/Section8SourceSurface.lean:123
- `TauCeti.DavisKahan1970.Section8.theorem8_2_krein_completion_source` — DavisKahan/Frontier/Section8SourceSurface.lean:195
- `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source` — DavisKahan/Frontier/Section8SourceSurface.lean:156, DavisKahan/Frontier/Section8SourceTheorem82.lean:275
- `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_source` — DavisKahan/Frontier/Section8SourceSurface.lean:184, DavisKahan/Frontier/Section8SourceTheorem82.lean:303
- `TauCeti.DavisKahan1970.Section8.subspaceGap_eq_directedGap_of_finrank_eq` — DavisKahan/Frontier/Section8SourceSurface.lean:128, DavisKahan/Frontier/Section8SourceTheorem82.lean:198
- `TauCeti.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_source_maximalAngle_lt` — DavisKahan/Frontier/Section8SourceSurface.lean:143, DavisKahan/Frontier/Section8SourceTheorem82.lean:541
- `TauCeti.DavisKahan1970.Section8.theorem8_2_residualHalfGap_source_maximalAngle_lt` — DavisKahan/Frontier/Section8SourceSurface.lean:147, DavisKahan/Frontier/Section8SourceTheorem82.lean:556
- `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_maximalAngle_lt` — DavisKahan/Frontier/Section8SourceSurface.lean:151, DavisKahan/Frontier/Section8SourceTheorem82.lean:571
- `TauCeti.DavisKahan1970.Section8.theorem8_2_source` — DavisKahan/Frontier/Section8SourceSurface.lean:190, DavisKahan/Frontier/Section8SourceTheorem82.lean:627
- `TauCeti.DavisKahan.Frontier.Section8.theorem8_2_perturbationHalfGap_source_angle_lt` — DavisKahan/Frontier/Section8Perturbation.lean:1315
- `TauCeti.DavisKahan.Frontier.Section8.theorem8_2_residualHalfGap_source_angle_lt` — DavisKahan/Frontier/Section8Residual.lean:225
- `TauCeti.DavisKahan.Frontier.Section8.residual_eq_comp_subtypeL` — DavisKahan/Frontier/Section8Residual.lean:95
- `TauCeti.DavisKahan.Frontier.Krein.exists_selfAdjoint_completion_eq_norm_restriction` — DavisKahan/Frontier/Section8Krein.lean:171
- `TauCeti.DavisKahan1970.Section8.PerturbationHalfGapBridge` — DavisKahan/Sources/DavisKahan1970/Section8/Smallness.lean:45
- `TauCeti.DavisKahan1970.Section8.ResidualHalfGapBridge` — DavisKahan/Sources/DavisKahan1970/Section8/Smallness.lean:57
- `TauCeti.DavisKahan1970.Section8.theorem82_branch_of_residualHalfGapBridge` — DavisKahan/Sources/DavisKahan1970/Section8/Smallness.lean:75
- `TauCeti.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_selectedBranch` — DavisKahan/Frontier/Section8.lean:838, DavisKahan/Sources/DavisKahan1970/Section8/SourceSurface.lean:94
- `TauCeti.DavisKahan1970.Section8.subspaceGap_eq_directedGap_of_crossedDefects` — DavisKahan/Frontier/Section8SourceSurface.lean:134, DavisKahan/Frontier/Section8SourceTheorem82.lean:235
- `TauCeti.DavisKahan1970.Section8.maximalAngle_lt_pi_div_four_of_crossedDefects` — DavisKahan/Frontier/Section8SourceSurface.lean:139, DavisKahan/Frontier/Section8SourceTheorem82.lean:250
- `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_paperUINorm` — DavisKahan/Frontier/Section8SourceSurface.lean:207, DavisKahan/Frontier/Section8SourceTheorem82.lean:431
- `TauCeti.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_source_real` — DavisKahan/Frontier/Section8SourceSurface.lean:242, DavisKahan/Frontier/Section8SourceTheorem82Real.lean:267
- `TauCeti.DavisKahan1970.Section8.theorem8_2_residualHalfGap_source_real` — DavisKahan/Frontier/Section8SourceSurface.lean:246, DavisKahan/Frontier/Section8SourceTheorem82Real.lean:294
- `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_directed_real` — DavisKahan/Frontier/Section8SourceSurface.lean:251, DavisKahan/Frontier/Section8SourceTheorem82Real.lean:319
- `TauCeti.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_source_real_maximalAngle_lt` — DavisKahan/Frontier/Section8SourceSurface.lean:256, DavisKahan/Frontier/Section8SourceTheorem82Real.lean:353
- `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_real_maximalAngle_lt_of_crossedDefects` — DavisKahan/Frontier/Section8SourceSurface.lean:261, DavisKahan/Frontier/Section8SourceTheorem82Real.lean:380
- `TauCeti.DavisKahan.Frontier.Section8.spectrum_compressOperator_subset_of_spectrumIn` — DavisKahan/Frontier/Section8SourceTheorem82.lean:410
- `TauCeti.DavisKahan.Frontier.Section8.norm_residual_complexify` — DavisKahan/Frontier/Section8SourceTheorem82Real.lean:136
- `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_real` — DavisKahan/Frontier/Section8SourceSurface.lean:271, DavisKahan/Frontier/Section8SourceTheorem82Real.lean:464
- `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_source_real` — DavisKahan/Frontier/Section8SourceSurface.lean:278, DavisKahan/Frontier/Section8SourceTheorem82Real.lean:488
- `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_real_paperUINorm` — DavisKahan/Frontier/Section8SourceSurface.lean:284, DavisKahan/Frontier/Section8SourceTheorem82Real.lean:553
- `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_real_maximalAngle_lt` — DavisKahan/Frontier/Section8SourceSurface.lean:266, DavisKahan/Frontier/Section8SourceTheorem82Real.lean:400
- `TauCeti.DavisKahan1970.Section8.theorem8_2_source_real` — DavisKahan/Frontier/Section8SourceSurface.lean:296, DavisKahan/Frontier/Section8SourceTheorem82Real.lean:677
- `TauCeti.DavisKahan.Frontier.Section8.spectrum_compressOperatorReal_subset_of_spectrumIn` — DavisKahan/Frontier/Section8SourceTheorem82Real.lean:525
- `TauCeti.DavisKahan.Frontier.Section8.complexify_sinTwoAngleOperator` — DavisKahan/Frontier/Section8SourceTheorem82Real.lean:432
- `TauCeti.DavisKahan.Frontier.Section8.norm_sinTwoAngleOperator_complexifySubmodule` — DavisKahan/Frontier/Section8SourceTheorem82Real.lean:450
- `TauCeti.DavisKahan.Frontier.Section8.theorem8_2_residualHalfGap_selectedBranch` — DavisKahan/Frontier/Section8.lean:849
- `TauCeti.DavisKahan.Frontier.Section8.theorem8_2_sinTwoTheta_residual_source_all_kyFan` — DavisKahan/Frontier/Section8SourceSurface.lean:221, DavisKahan/Frontier/Section8SourceTheorem82.lean:473
- `TauCeti.DavisKahan.Frontier.Section8.theorem8_2_sinTwoTheta_residual_source_paperUINorm` — DavisKahan/Frontier/Section8SourceSurface.lean:216, DavisKahan/Frontier/Section8SourceTheorem82.lean:507
- `TauCeti.DavisKahan.Frontier.Section8.theorem8_2_sinTwoTheta_residual_source_real_paperUINorm` — DavisKahan/Frontier/Section8SourceSurface.lean:290, DavisKahan/Frontier/Section8SourceTheorem82Real.lean:608
- `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_source_paperUINorm` — DavisKahan/Frontier/Section8SourceSurface.lean:216, DavisKahan/Frontier/Section8SourceTheorem82.lean:507
- `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_source_all_kyFan` — DavisKahan/Frontier/Section8SourceSurface.lean:221, DavisKahan/Frontier/Section8SourceTheorem82.lean:473
- `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_maximalAngle_lt_of_crossedDefects` — DavisKahan/Frontier/Section8SourceSurface.lean:227, DavisKahan/Frontier/Section8SourceTheorem82.lean:595

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 40. DK-9-model — Fourth-derivative Rayleigh–Ritz model

- **Source anchor:** Section 9, problem setup
- **Source kind:** `numerical_model`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `74832d3be5476a43a706c8866a795303c93d349c6094965d676b34545ffe1c41`
- **Private-transcription provenance lines:** `[[2562, 2625]]`

### Exact registered source passage

~~~~tex
The following example was used by H.~F. Weinberger to illustrate his eigenvector estimates. It illustrates our notation and theorems and permits comparison of bounds obtained by different procedures.

\paragraph{The problem.}
Let $\Hilbert$ be the real space $L^2(0,1)$, with
\[
  u^*v=\int_0^1u(t)v(t)\,dt.
\]
The operator $(d/dt)^4$ acting on functions satisfying
\[
  u''(0)=u'''(0)=u''(1)=u'''(1)=0
\]
has a self-adjoint closure, denoted by $A$. Let $H$ be multiplication by $\varepsilon t$, where $0<\varepsilon<100$.

We study the two lowest eigenvalues of $A+H$ and their eigenvectors. In differential-equation notation,
\[
  u^{(4)}+\varepsilon tu=\lambda u,
  \qquad
  u''(0)=u'''(0)=u''(1)=u'''(1)=0.
\]
The comparison problem for $A$ is
\[
  w^{(4)}=\alpha w,
  \qquad
  w''(0)=w'''(0)=w''(1)=w'''(1)=0.
\]
The eigenvalues are
\[
  \alpha_1=0=\alpha_2<\alpha_3<\cdots,
\]
where, for $k>2$, the $\alpha_k$ are the positive roots of
\[
  \cos\alpha_k^{1/4}\cosh\alpha_k^{1/4}=1;
\]
all exceed $500$. Two orthonormal linear eigenfunctions for $\alpha_1,\alpha_2$ are
\[
  w_k(t)=\frac{1+(-1)^k\sqrt3(2t-1)}{\sqrt2},
  \qquad k=1,2.
\]
We put $e_k=w_k$ and $E_0=(e_1\;e_2):\mathbb R^2\to\Hilbert$.

Let $\lambda_1\leq\lambda_2\leq\cdots$ be the eigenvalues of $A+H$, with corresponding orthonormal eigenfunctions $f_1,f_2,\ldots$, and put $F_0=(f_1\;f_2)$. The problem is to bound the difference between $E_0\mathbb R^2$ and $F_0\mathbb R^2$.

Since $H\geq0$, we have $\lambda_3\geq\alpha_3>500$, or $\Lambda_1>500$ in our notation. The straightforward comparison matrix is
\[
  A_0=E_0^*AE_0=\begin{pmatrix}0&0\\0&0\end{pmatrix}.
\]
The residual is
\[
  R=(A+H)E_0-E_0\cdot0=HE_0=(r_1\;r_2),
\]
where
\[
  r_k(t)=\varepsilon te_k(t)
  =\frac{\varepsilon t\bigl(1+(-1)^k\sqrt3(2t-1)\bigr)}{\sqrt2}.
\]
A direct computation gives
\[
  R^*R=\frac{\varepsilon^2}{30}
  \begin{pmatrix}
    11-\sqrt{75}&-1\\
    -1&11+\sqrt{75}
  \end{pmatrix},
\]
with eigenvalues $\varepsilon^2(11\pm\sqrt{76})/30$.
~~~~

### Semantic audit clauses

- **`DK-9-model.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Section9.real_freeBeam_operator_source`, `TauCeti.DavisKahan1970.Section9.real_freeBeam_spectrum_source`, `TauCeti.DavisKahan1970.Section9.real_freeBeam_zero_mode_source`, `TauCeti.DavisKahan1970.Section9.real_freeBeam_finiteData_source`, `TauCeti.DavisKahan1970.Section9.real_freeBeam_trial_and_perturbation_source`, `TauCeti.DavisKahan1970.Section9.real_freeBeam_positive_spectrum_source`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Section9.real_freeBeam_operator_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:44`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.real_freeBeam_spectrum_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:54`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.real_freeBeam_zero_mode_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:88`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.real_freeBeam_finiteData_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:97`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.real_freeBeam_trial_and_perturbation_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:103`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.real_freeBeam_positive_spectrum_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:67`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan.FreeBeam.Model.beamOperator` — DavisKahan/SpectralTheory/FormMethod/BeamFormSpace.lean:566, DavisKahan/SpectralTheory/FormMethod/BeamFormSpaceReal.lean:79, DavisKahan/SpectralTheory/FormMethod/BeamFormSpaceScalar.lean:592
- `TauCeti.DavisKahan.FreeBeam.Model.beamOperator_isSelfAdjoint` — DavisKahan/SpectralTheory/FormMethod/BeamFormSpace.lean:569, DavisKahan/SpectralTheory/FormMethod/BeamFormSpaceReal.lean:83, DavisKahan/SpectralTheory/FormMethod/BeamFormSpaceScalar.lean:595
- `TauCeti.DavisKahan.FreeBeam.Model.realSpectrum_beamOperator_subset_gap` — DavisKahan/SpectralTheory/FormMethod/BeamSpectrum.lean:1055, DavisKahan/SpectralTheory/FormMethod/BeamSpectrumReal.lean:249
- `TauCeti.DavisKahan.FreeBeam.Model.realSpectrum_beamOperator_subset_sharp` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:740
- `TauCeti.DavisKahan.FreeBeam.Model.beamTrial_orthonormal` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:993, DavisKahan/SpectralTheory/FormMethod/BeamTrialReal.lean:413
- `TauCeti.DavisKahan.FreeBeam.Model.inner_centeredAffineLp` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:958, DavisKahan/SpectralTheory/FormMethod/BeamTrialReal.lean:387
- `TauCeti.DavisKahan.FreeBeam.Model.inner_centeredAffineLp_mul` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:968, DavisKahan/SpectralTheory/FormMethod/BeamTrialReal.lean:394
- `TauCeti.DavisKahan.FreeBeam.Model.inner_mul_centeredAffineLp_mul` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:979, DavisKahan/SpectralTheory/FormMethod/BeamTrialReal.lean:402
- `TauCeti.DavisKahan.FreeBeam.Model.beamRitz_matrix` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1016, DavisKahan/SpectralTheory/FormMethod/BeamTrialReal.lean:500
- `TauCeti.DavisKahan.FreeBeam.Model.beamResidualGram_matrix` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1033, DavisKahan/SpectralTheory/FormMethod/BeamTrialReal.lean:516
- `TauCeti.DavisKahan.FreeBeam.Model.beamFiniteDataCertificate` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1067, DavisKahan/SpectralTheory/FormMethod/BeamSection9Real.lean:33
- `TauCeti.DavisKahan1970.Section9.CenteredAffine` — DavisKahan/Sources/DavisKahan1970/Section9/TrialSubspace.lean:27
- `TauCeti.DavisKahan1970.Section9.ritz_matrix_from_affine_moments` — DavisKahan/Sources/DavisKahan1970/Section9/TrialSubspace.lean:179
- `TauCeti.DavisKahan1970.Section9.FreeBeamFiniteDataCertificate` — DavisKahan/Sources/DavisKahan1970/Section9/ExactData.lean:257
- `TauCeti.DavisKahan.FreeBeam.Model.exists_pos_eigenpair_beamOperator` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:398
- `TauCeti.DavisKahan.FreeBeam.Model.exists_five_hundred_lt_mem_realSpectrum_beamOperator` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:94, DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:433
- `TauCeti.DavisKahan.FreeBeam.Model.exists_mem_realSpectrum_beamOperator_ne_zero` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:101, DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:442
- `TauCeti.DavisKahan.FreeBeam.Model.beamQuadLp` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:323
- `TauCeti.DavisKahan.FreeBeam.Model.inner_affineLp_beamQuadLp` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:328
- `TauCeti.DavisKahan.FreeBeam.Model.beamQuadLp_mem_beamTrial_orthogonal` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:345
- `TauCeti.DavisKahan.FreeBeam.Model.norm_beamQuadLp_sq` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:352
- `TauCeti.DavisKahan.FreeBeam.Model.beamQuadLp_ne_zero` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:376
- `TauCeti.DavisKahan.FreeBeam.Model.eigenspace_beamResolvent_one_le_beamTrial` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:384
- `TauCeti.DavisKahan.FreeBeam.Model.exists_beamOperator_apply_of_beamResolvent_smul` — DavisKahan/SpectralTheory/FormMethod/BeamSpectrum.lean:794, DavisKahan/SpectralTheory/FormMethod/BeamSpectrumReal.lean:56
- `TauCeti.DavisKahan.FreeBeam.Model.exists_affine_of_beamResolvent_eq_self` — DavisKahan/SpectralTheory/FormMethod/BeamSpectrum.lean:825, DavisKahan/SpectralTheory/FormMethod/BeamSpectrumReal.lean:84
- `TauCeti.LinearPMap.mem_realSpectrum_of_eigenvector` — ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean:1000
- `TauCeti.exists_hasEigenvalue_eigenspace_not_le` — ForTauCeti/Analysis/InnerProductSpace/CompactSelfAdjointClassification.lean:101
- `TauCeti.DavisKahan.FreeBeam.Model.not_finiteDimensional_beamL2` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:80, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:32
- `TauCeti.DavisKahan.FreeBeam.Model.exists_pos_eigenpair_beamOperator_gt` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:95, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:42
- `TauCeti.DavisKahan.FreeBeam.Model.exists_lt_five_hundred_lt_mem_realSpectrum_beamOperator` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:145, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:86
- `TauCeti.DavisKahan.FreeBeam.Model.not_bddAbove_realSpectrum_beamOperator` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:153, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:107
- `TauCeti.DavisKahan.FreeBeam.Model.beamEigenvalues` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:163, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:115
- `TauCeti.DavisKahan.FreeBeam.Model.finite_beamEigenvalues_inter_Iic` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:223, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:171
- `TauCeti.DavisKahan.FreeBeam.Model.exists_lt_mem_beamEigenvalues` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:276, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:211
- `TauCeti.DavisKahan.FreeBeam.Model.exists_strictMono_mem_realSpectrum_beamOperator` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:287, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:218
- `TauCeti.DavisKahan.FreeBeam.Model.infinite_five_hundred_lt_mem_realSpectrum_beamOperator` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:381, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:292
- `TauCeti.DavisKahan.FreeBeam.Model.beamResolvent_apply_of_beamOperator_eigen` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:184, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:151
- `TauCeti.DavisKahan.FreeBeam.Model.eigenspace_beamResolvent_zero_eq_bot` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:84, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:36
- `TauCeti.not_finiteDimensional_lpTwo_unitIocMeasure` — ForTauCeti/MeasureTheory/LpInfiniteDimensional.lean:96
- `TauCeti.not_finiteDimensional_lpTwo_of_pairwise_disjoint` — ForTauCeti/MeasureTheory/LpInfiniteDimensional.lean:56
- `TauCeti.finite_setOf_hasEigenvalue_le_norm` — ForTauCeti/Analysis/InnerProductSpace/CompactSelfAdjointClassification.lean:248
- `TauCeti.exists_hasEigenvalue_norm_lt` — ForTauCeti/Analysis/InnerProductSpace/CompactSelfAdjointClassification.lean:334
- `TauCeti.exists_isLeast_of_finite_inter_Iic` — ForTauCeti/Order/DiscreteEnumeration.lean:56
- `TauCeti.nonempty_orderIso_nat_of_unbounded_of_finite_inter_Iic` — ForTauCeti/Order/DiscreteEnumeration.lean:73
- `TauCeti.exists_strictMono_range_eq_of_unbounded_of_finite_inter_Iic` — ForTauCeti/Order/DiscreteEnumeration.lean:101
- `TauCeti.DavisKahan.FreeBeam.Model.nonneg_of_beamOperator_eigen` — DavisKahan/SpectralTheory/FormMethod/BeamClassicalReal.lean:1307, DavisKahan/SpectralTheory/FormMethod/BeamSpectrum.lean:747
- `TauCeti.DavisKahan.FreeBeam.Model.exists_eigenvector_of_mem_realSpectrum_beamOperator` — DavisKahan/SpectralTheory/FormMethod/BeamSpectrum.lean:917, DavisKahan/SpectralTheory/FormMethod/BeamSpectrumReal.lean:125
- `TauCeti.DavisKahan.FreeBeam.Model.zero_mem_realSpectrum_beamOperator` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:309, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:237
- `TauCeti.DavisKahan.FreeBeam.Model.realSpectrum_beamOperator_eq_insert_zero` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:327, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:249
- `TauCeti.DavisKahan.FreeBeam.Model.finite_realSpectrum_beamOperator_inter_Iic` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:343, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:263
- `TauCeti.DavisKahan.FreeBeam.Model.nonempty_orderIso_nat_beamEigenvalues` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:358, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:273
- `TauCeti.DavisKahan.FreeBeam.Model.exists_strictMono_range_eq_beamEigenvalues` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:367, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:278
- `TauCeti.DavisKahan1970.Section9.real_freeBeam_operator_source` — DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:44
- `TauCeti.DavisKahan1970.Section9.real_freeBeam_spectrum_source` — DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:54
- `TauCeti.DavisKahan1970.Section9.real_freeBeam_zero_mode_source` — DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:88
- `TauCeti.DavisKahan1970.Section9.real_freeBeam_finiteData_source` — DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:97
- `TauCeti.DavisKahan1970.Section9.real_freeBeam_trial_and_perturbation_source` — DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:103
- `TauCeti.DavisKahan1970.Section9.RealBeamL2` — DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:27
- `TauCeti.DavisKahan1970.Section9.realBeamOperator` — DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:31
- `TauCeti.DavisKahan1970.Section9.realClassicalFreeBeamGraph` — DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:36
- `TauCeti.DavisKahan.FreeBeam.Model.Real.BeamL2` — DavisKahan/SpectralTheory/FormMethod/BeamFormSpace.lean:48, DavisKahan/SpectralTheory/FormMethod/BeamFormSpaceReal.lean:28, DavisKahan/SpectralTheory/FormMethod/BeamFormSpaceScalar.lean:51
- `TauCeti.DavisKahan.FreeBeam.Model.Real.beamOperator` — DavisKahan/SpectralTheory/FormMethod/BeamFormSpace.lean:566, DavisKahan/SpectralTheory/FormMethod/BeamFormSpaceReal.lean:79, DavisKahan/SpectralTheory/FormMethod/BeamFormSpaceScalar.lean:592
- `TauCeti.DavisKahan.FreeBeam.Model.Real.ClassicalFreeBeamRepresentative` — DavisKahan/SpectralTheory/FormMethod/BeamClassicalReal.lean:323
- `TauCeti.DavisKahan.FreeBeam.Model.Real.classicalFreeBeamGraph` — DavisKahan/SpectralTheory/FormMethod/BeamClassicalReal.lean:350
- `TauCeti.DavisKahan.FreeBeam.Model.Real.beamOperator_is_closure_of_classical_freeBeam_fourthDerivative` — DavisKahan/SpectralTheory/FormMethod/BeamClassicalReal.lean:945
- `TauCeti.DavisKahan.FreeBeam.Model.Real.closure_classicalFreeBeamGraph_eq_graph` — DavisKahan/SpectralTheory/FormMethod/BeamClassicalReal.lean:934
- `TauCeti.DavisKahan.FreeBeam.Model.Real.classicalFreeBeamGraph_subset_graph` — DavisKahan/SpectralTheory/FormMethod/BeamClassicalReal.lean:887
- `TauCeti.DavisKahan.FreeBeam.Model.Real.exists_characteristic_of_eigen` — DavisKahan/SpectralTheory/FormMethod/BeamClassicalReal.lean:1128, DavisKahan/SpectralTheory/FormMethod/BeamSpectrum.lean:490
- `TauCeti.DavisKahan.FreeBeam.Model.Real.realSpectrum_beamOperator_subset` — DavisKahan/SpectralTheory/FormMethod/BeamSpectrum.lean:1041, DavisKahan/SpectralTheory/FormMethod/BeamSpectrumReal.lean:238
- `TauCeti.DavisKahan.FreeBeam.Model.Real.beamEigenvalues` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:163, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:115
- `TauCeti.DavisKahan.FreeBeam.Model.Real.exists_strictMono_range_eq_beamEigenvalues` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:367, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:278
- `TauCeti.DavisKahan.FreeBeam.Model.Real.five_hundred_lt_of_mem_beamEigenvalues` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:168, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:139
- `TauCeti.DavisKahan.FreeBeam.Model.Real.not_finiteDimensional_beamL2` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:80, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:32
- `TauCeti.DavisKahan.FreeBeam.Model.Real.beamFiniteDataCertificate` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1067, DavisKahan/SpectralTheory/FormMethod/BeamSection9Real.lean:33
- `TauCeti.DavisKahan.FreeBeam.Model.Real.beamTrial_le_domain` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:106, DavisKahan/SpectralTheory/FormMethod/BeamTrialReal.lean:67
- `TauCeti.DavisKahan.FreeBeam.Model.Real.beamOperator_apply_trial` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:112, DavisKahan/SpectralTheory/FormMethod/BeamTrialReal.lean:73
- `TauCeti.DavisKahan.FreeBeam.Classical.characteristic_iff_exists_nontrivial_freeBoundary` — DavisKahan/Sources/DavisKahan1970/Section9/FreeBeamCharacteristicConverse.lean:140
- `TauCeti.DavisKahan.FreeBeam.Classical.exists_nontrivial_freeBoundary_of_characteristic` — DavisKahan/Sources/DavisKahan1970/Section9/FreeBeamCharacteristicConverse.lean:126
- `TauCeti.DavisKahan1970.Section9.real_freeBeam_positive_spectrum_source` — DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:67
- `TauCeti.DavisKahan1970.Section9.real_freeBeam_trial_le_domain` — DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:75
- `TauCeti.DavisKahan1970.Section9.real_freeBeam_operator_apply_trial` — DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:81
- `TauCeti.DavisKahan.FreeBeam.Model.Real.beamEigenvalues_eq_characteristicFourthPowers` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:128
- `TauCeti.DavisKahan.FreeBeam.Model.Real.pow_four_mem_beamEigenvalues_of_characteristic` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:121
- `TauCeti.DavisKahan.FreeBeam.Model.Real.exists_eigenpair_of_characteristic` — DavisKahan/SpectralTheory/FormMethod/BeamClassicalReal.lean:1092
- `TauCeti.DavisKahan.FreeBeam.Model.Real.beamRealPositiveSpectrum_sourceFacts` — DavisKahan/SpectralTheory/FormMethod/BeamSection9Real.lean:68

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 41. DK-9.1-9.4 — Initial sine and sine-double-angle bounds

- **Source anchor:** Equations (9.1)–(9.4)
- **Source kind:** `numerical_claims`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `5a3c208371c79e6baf9a2b9af2b75d955fe9ab6b884da7b8400cb39329dcba03`
- **Private-transcription provenance lines:** `[[2627, 2643]]`

### Exact registered source passage

~~~~tex
The $\sin\theta$ theorem applies with $\delta=500$. For the bound norm,
\begin{equation*}
  \sin\theta_1<0.001622\varepsilon.
\tag{9.1}\label{eq:9.1}
\end{equation*}
The $\sin2\theta$ theorem, with $A$ and $A+H$ interchanged, gives the slightly weaker
\begin{equation*}
  \sin2\theta_1<0.004\varepsilon.
\tag{9.2}\label{eq:9.2}
\end{equation*}
For the norm equal to the sum of the two largest singular values, the corresponding bounds are
\begin{align*}
  \sin\theta_1+\sin\theta_2&<0.00218\varepsilon,
  \tag{9.3}\label{eq:9.3}\\
  \sin2\theta_1+\sin2\theta_2&<0.008\varepsilon.
  \tag{9.4}\label{eq:9.4}
\end{align*}
~~~~

### Semantic audit clauses

- **`DK-9.1-9.4.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Section9.equation_9_1`, `TauCeti.DavisKahan1970.Section9.equation_9_2`, `TauCeti.DavisKahan1970.Section9.equation_9_3`, `TauCeti.DavisKahan1970.Section9.equation_9_4`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Section9.equation_9_1`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/NumericalBounds.lean:231`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.equation_9_2`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/NumericalBounds.lean:239`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.equation_9_3`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/NumericalBounds.lean:246`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.equation_9_4`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/NumericalBounds.lean:253`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.Section9.initial_residual_gram_from_affine_moments` — DavisKahan/Sources/DavisKahan1970/Section9/TrialSubspace.lean:192
- `TauCeti.DavisKahan1970.Section9.residualGram_eigenvalueHigh_charAt` — DavisKahan/Sources/DavisKahan1970/Section9/ExactData.lean:161
- `TauCeti.DavisKahan1970.Section9.equation_9_1` — DavisKahan/Sources/DavisKahan1970/Section9/NumericalBounds.lean:231
- `TauCeti.DavisKahan1970.Section9.equation_9_4` — DavisKahan/Sources/DavisKahan1970/Section9/NumericalBounds.lean:253
- `TauCeti.DavisKahan.FreeBeam.Model.beamSinTheta_le` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:651
- `TauCeti.DavisKahan.FreeBeam.Model.beamSinTwoTheta_lt` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:868
- `TauCeti.DavisKahan.FreeBeam.Model.norm_beamPerturbation_comp_trialIncl_le` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:584
- `TauCeti.DavisKahan.FreeBeam.Model.beamSpecProjection_lowSet_eq_singleton` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:775
- `TauCeti.DavisKahan.FreeBeam.Model.beamSinTwoThetaSum_lt` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1127
- `TauCeti.DavisKahan.FreeBeam.Model.beamKyFanTwo_gaugeReal_le` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1094
- `TauCeti.DavisKahan.FreeBeam.Model.beamTrialVec_span_eq_top` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1214
- `TauCeti.DavisKahan.FreeBeam.Model.exists_beamTrialVec_repr` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1261
- `TauCeti.DavisKahan.FreeBeam.Model.beamResidual_gram` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1272
- `TauCeti.DavisKahan.FreeBeam.Model.beamGram_orthogonal_direction` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1290
- `TauCeti.DavisKahan.FreeBeam.Model.beamResidualRankOne_rank_le` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1360
- `TauCeti.DavisKahan.FreeBeam.Model.beamResidual_sub_rankOne_apply` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1456
- `TauCeti.DavisKahan.FreeBeam.Model.beamResidual_orthogonal_norm_sq` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1322
- `TauCeti.DavisKahan.FreeBeam.Model.norm_beamResidual_sub_rankOne_le` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1493
- `TauCeti.DavisKahan.FreeBeam.Model.approximationSingularValue_one_beamResidual_le` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1543
- `TauCeti.DavisKahan.FreeBeam.Model.kyFanTwo_beamResidual_le` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1554
- `TauCeti.DavisKahan.FreeBeam.Model.beamSinThetaSum_le` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1588
- `TauCeti.DavisKahan1970.Section9.equation_9_2` — DavisKahan/Sources/DavisKahan1970/Section9/NumericalBounds.lean:239
- `TauCeti.DavisKahan1970.Section9.equation_9_3` — DavisKahan/Sources/DavisKahan1970/Section9/NumericalBounds.lean:246

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 42. DK-9.5-9.7 — Rayleigh–Ritz tangent refinements

- **Source anchor:** Equations (9.5)–(9.7)
- **Source kind:** `numerical_claims`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `c38f0b52a80497c632c09dda0635e326b35f0098cc1994a78a03e52673f53cc0`
- **Private-transcription provenance lines:** `[[2645, 2696]]`

### Exact registered source passage

~~~~tex
A refinement is to choose the comparison matrix so that $H_0=0$. Keep the same subspaces but use the generalized Rayleigh--Ritz quotient
\[
  \widehat A_0=E_0^*(A+H)E_0
  =\frac{\varepsilon}{2}
  \begin{pmatrix}
    1-1/\sqrt3&0\\
    0&1+1/\sqrt3
  \end{pmatrix}.
\]
Then
\[
  \widehat R=(A+H)E_0-E_0\widehat A_0
  =R-E_0\widehat A_0=(\widehat r_1\;\widehat r_2),
\]
and, since $E_0^*\widehat R=0$,
\[
  \widehat R^*\widehat R
  =R^*R-\widehat A_0^2
  =\frac{\varepsilon^2}{30}
   \begin{pmatrix}1&-1\\-1&1\end{pmatrix}.
\]
Thus
\[
  \norm{\widehat R}_1=\norm{\widehat R}_2
  =\varepsilon/\sqrt{15}=0.2582\varepsilon.
\]
Let $\widehat\alpha_1<\widehat\alpha_2$ be the eigenvalues of $\widehat A_0$:
\begin{equation*}
  \widehat\alpha_k
  =\frac{\varepsilon}{2}
   \left(1+\frac{(-1)^k}{\sqrt3}\right).
\tag{9.5}\label{eq:9.5}
\end{equation*}
Hence $\widehat A_0<0.7887\varepsilon$ and the $\tan\theta$ theorem may use $\delta=500-0.7887\varepsilon$. For the bound norm,
\begin{equation*}
  \tan\theta_1
  <\frac{0.0005164\varepsilon}{1-0.0015774\varepsilon}.
\tag{9.6}\label{eq:9.6}
\end{equation*}
The same bound applies to $\tan\theta_1+\tan\theta_2$ in the $2$-norm.

For the $\tan2\theta$ theorem we also replace $A_1$ by
\[
  \widehat A_1=E_1^*(A+H)E_1.
\]
Since $\widehat A_1-A_1=E_1^*HE_1\geq0$, still $\widehat A_1>500$. The bound-norm result is
\begin{equation*}
  \tan2\theta_1
  <\frac{0.0010328\varepsilon}{1-0.0015774\varepsilon},
\tag{9.7}\label{eq:9.7}
\end{equation*}
with the same right side bounding $\tan2\theta_1+\tan2\theta_2$ in the $2$-norm.
~~~~

### Semantic audit clauses

- **`DK-9.5-9.7.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Section9.equation_9_5_low`, `TauCeti.DavisKahan1970.Section9.equation_9_5_high`, `TauCeti.DavisKahan1970.Section9.equation_9_6`, `TauCeti.DavisKahan1970.Section9.equation_9_7`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Section9.equation_9_5_low`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/NumericalBounds.lean:260`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.equation_9_5_high`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/NumericalBounds.lean:267`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.equation_9_6`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/NumericalBounds.lean:274`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.equation_9_7`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/NumericalBounds.lean:283`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.Section9.recentered_residual_gram_from_affine_moments` — DavisKahan/Sources/DavisKahan1970/Section9/TrialSubspace.lean:204
- `TauCeti.DavisKahan1970.Section9.equation_9_5_low` — DavisKahan/Sources/DavisKahan1970/Section9/NumericalBounds.lean:260
- `TauCeti.DavisKahan1970.Section9.equation_9_6` — DavisKahan/Sources/DavisKahan1970/Section9/NumericalBounds.lean:274
- `TauCeti.DavisKahan1970.Section9.equation_9_7` — DavisKahan/Sources/DavisKahan1970/Section9/NumericalBounds.lean:283
- `TauCeti.DavisKahan.FreeBeam.Model.beamResidual_inner_trial` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1708
- `TauCeti.DavisKahan.FreeBeam.Model.norm_beamRitzResidual_le` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1831
- `TauCeti.DavisKahan.FreeBeam.Model.beamRitz_form_le` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1878
- `TauCeti.DavisKahan1970.Section9.equation_9_5_high` — DavisKahan/Sources/DavisKahan1970/Section9/NumericalBounds.lean:267
- `TauCeti.DavisKahan.FreeBeam.Model.beamPerturbed_specProjection_Ioo_eq_zero` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:2067
- `TauCeti.DavisKahan.FreeBeam.Model.beamTanTheta_le` — DavisKahan/SpectralTheory/FormMethod/BeamTangent.lean:248
- `TauCeti.DavisKahan.FreeBeam.Model.beamTanTheta_lt_printed` — DavisKahan/SpectralTheory/FormMethod/BeamTangent.lean:288
- `TauCeti.DavisKahan.FreeBeam.Model.norm_beamRitzResidual_sq_le` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1739
- `TauCeti.DavisKahan.FreeBeam.Model.beamRitzResidual_vecOne_add_vecTwo_eq_zero` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1862
- `TauCeti.DavisKahan.FreeBeam.Model.beamTrialBlock_residual_vecOne_add_vecTwo` — DavisKahan/SpectralTheory/FormMethod/BeamTangent.lean:146
- `TauCeti.DavisKahan.FreeBeam.Model.beamTrialBlock_residual_vecTwo` — DavisKahan/SpectralTheory/FormMethod/BeamTangent.lean:153
- `TauCeti.DavisKahan.FreeBeam.Model.beamTrialBlock_residual_rank_le` — DavisKahan/SpectralTheory/FormMethod/BeamTangent.lean:161
- `TauCeti.DavisKahan.FreeBeam.Model.approximationSingularValue_one_beamTrialBlock_residual_le` — DavisKahan/SpectralTheory/FormMethod/BeamTangent.lean:184
- `TauCeti.DavisKahan.FreeBeam.Model.kyFanTwo_beamTrialBlock_residual_le` — DavisKahan/SpectralTheory/FormMethod/BeamTangent.lean:193
- `TauCeti.DavisKahan.FreeBeam.Model.beamTanThetaSum_le` — DavisKahan/SpectralTheory/FormMethod/BeamTangent.lean:315
- `TauCeti.DavisKahan.FreeBeam.Model.beamTanThetaSum_lt_printed` — DavisKahan/SpectralTheory/FormMethod/BeamTangent.lean:352
- `TauCeti.DavisKahan.FreeBeam.Model.beamComparison_reduces` — DavisKahan/SpectralTheory/FormMethod/BeamDoubleTangent.lean:324
- `TauCeti.DavisKahan.FreeBeam.Model.beamRitzOffDiagonal_isOddFor` — DavisKahan/SpectralTheory/FormMethod/BeamDoubleTangent.lean:352
- `TauCeti.DavisKahan.FreeBeam.Model.norm_beamRitzOffDiagonal_le` — DavisKahan/SpectralTheory/FormMethod/BeamDoubleTangent.lean:192
- `TauCeti.DavisKahan.FreeBeam.Model.beamComparison_form_le_of_mem_beamTrial` — DavisKahan/SpectralTheory/FormMethod/BeamDoubleTangent.lean:368
- `TauCeti.DavisKahan.FreeBeam.Model.beamComparison_form_ge_of_mem_orthogonal` — DavisKahan/SpectralTheory/FormMethod/BeamDoubleTangent.lean:382
- `TauCeti.DavisKahan.FreeBeam.Model.beamLowReflection_comm` — DavisKahan/SpectralTheory/FormMethod/BeamDoubleTangent.lean:513
- `TauCeti.DavisKahan.FreeBeam.Model.beamTanTwoTheta_le` — DavisKahan/SpectralTheory/FormMethod/BeamDoubleTangent.lean:644
- `TauCeti.DavisKahan.FreeBeam.Model.beamTanTwoTheta_lt_printed` — DavisKahan/SpectralTheory/FormMethod/BeamDoubleTangent.lean:649
- `TauCeti.DavisKahan.FreeBeam.Model.beamTanTwoThetaSum` — DavisKahan/Sources/DavisKahan1970/Section9/BeamDoubleTangentKyFan.lean:186
- `TauCeti.DavisKahan.FreeBeam.Model.beamTanTwoThetaSum_le` — DavisKahan/Sources/DavisKahan1970/Section9/BeamDoubleTangentKyFan.lean:198
- `TauCeti.DavisKahan.FreeBeam.Model.beamTanTwoThetaSum_lt_printed` — DavisKahan/Sources/DavisKahan1970/Section9/BeamDoubleTangentKyFan.lean:242

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 43. DK-9.8 — Comparison with Weinberger bounds

- **Source anchor:** Equation (9.8)
- **Source kind:** `comparison_claim`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `740fea893adc19c56bcdc1bda015e9d6f1eab315d2c720cabc92482566c3da0c`
- **Private-transcription provenance lines:** `[[2698, 2751]]`

### Exact registered source passage

~~~~tex
We now compare these estimates with Weinberger's. His method uses the Rayleigh--Ritz upper bounds $\widehat\alpha_1,\widehat\alpha_2$, lower bounds $\check\alpha_1,\check\alpha_2$, and $\widehat\alpha_2<500<\lambda_3$. His theorem gives
\[
  \sin^2\phi_k
  \leq\frac{\widehat\alpha_k-\check\alpha_k}{500-\check\alpha_k},
  \qquad k=1,2,
\]
where $\phi_k$ is the angle between $e_k$ and $F_0\mathbb R^2$.

The best lower bounds deducible from $\widehat A_0$, $\widehat R^*\widehat R$, and $\widehat A_1>500$ are the two lower eigenvalues of
\[
  \begin{pmatrix}
    \widehat\alpha_1&0&\varepsilon/\sqrt{30}\\
    0&\widehat\alpha_2&\varepsilon/\sqrt{30}\\
    \varepsilon/\sqrt{30}&\varepsilon/\sqrt{30}&500
  \end{pmatrix}.
\]
The deduction follows Weinberger and Lehmann. For $0<\varepsilon<100$,
\[
  \frac{\varepsilon^2/30}{500-\widehat\alpha_k}
  >\widehat\alpha_k-\check\alpha_k
  =\frac{\varepsilon^2/30}{500-\widehat\alpha_k}-O(\varepsilon^4),
\]
whence
\begin{equation*}
\begin{aligned}
  \tan\phi_1&<\frac{0.0005164\varepsilon}{1-0.0004227\varepsilon},\\
  \tan\phi_2&<\frac{0.0005164\varepsilon}{1-0.0015774\varepsilon}.
\end{aligned}
\tag{9.8}\label{eq:9.8}
\end{equation*}
These bounds answer a different question from ours: $\theta_1$ is the largest angle made by any vector in $E_0\mathbb R^2$ with $F_0\mathbb R^2$, whereas $\phi_k$ concerns the specific vector $e_k$. Thus $\theta_1\geq\phi_k$, although
\[
  \sin^2\phi_1+\sin^2\phi_2
  =\sin^2\theta_1+\sin^2\theta_2.
\]

To estimate $\phi_k$ directly by our method, apply \TheoremRef{6.3} with $E_0=e_k$, $A_0=\widehat\alpha_k=e_k^*(A+H)e_k$, and
\[
  R=(A+H)e_k-e_k\widehat\alpha_k=\widehat r_k.
\]
The gap is $500-\widehat\alpha_k$, giving
\[
  \tan\phi_1
  <\frac{\varepsilon/\sqrt{30}}{500-\widehat\alpha_1}
  =\frac{0.0003652\varepsilon}{1-0.0004227\varepsilon},
\]
\[
  \tan\phi_2
  <\frac{\varepsilon/\sqrt{30}}{500-\widehat\alpha_2}
  =\frac{0.0003652\varepsilon}{1-0.0015774\varepsilon},
\]
which are sharper than~\eqref{eq:9.8}.

Neither approach supplants the other. Our estimates are inferred from a residual or perturbation norm and a spectral gap. Weinberger's use both Rayleigh--Ritz upper and lower bounds, and can exploit independent lower-bound information that our results do not use.
~~~~

### Semantic audit clauses

- **`DK-9.8.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Section9.equation_9_8_lower`, `TauCeti.DavisKahan1970.Section9.equation_9_8_upper`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Section9.equation_9_8_lower`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/WeinbergerComparison.lean:136`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.equation_9_8_upper`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/WeinbergerComparison.lean:149`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.Section9.ArrowheadThreeByThree` — DavisKahan/Sources/DavisKahan1970/Section9/WeinbergerComparison.lean:30
- `TauCeti.DavisKahan1970.Section9.tangent_sq_le_of_weinberger_sine_sq` — DavisKahan/Sources/DavisKahan1970/Section9/WeinbergerComparison.lean:84
- `TauCeti.DavisKahan1970.Section9.equation_9_8_lower` — DavisKahan/Sources/DavisKahan1970/Section9/WeinbergerComparison.lean:136
- `TauCeti.DavisKahan1970.Section9.equation_9_8_upper` — DavisKahan/Sources/DavisKahan1970/Section9/WeinbergerComparison.lean:149
- `TauCeti.DavisKahan.FreeBeam.Model.beamTanPhi_low_lt_printed` — DavisKahan/SpectralTheory/FormMethod/BeamTangent.lean:859
- `TauCeti.DavisKahan.FreeBeam.Model.beamTanPhi_high_lt_printed` — DavisKahan/SpectralTheory/FormMethod/BeamTangent.lean:866
- `TauCeti.DavisKahan.FreeBeam.Model.beamTanPhi_low_le` — DavisKahan/SpectralTheory/FormMethod/BeamTangent.lean:796
- `TauCeti.DavisKahan.FreeBeam.Model.beamTanPhi_high_le` — DavisKahan/SpectralTheory/FormMethod/BeamTangent.lean:827
- `TauCeti.DavisKahan.FreeBeam.Model.beamColumn_tangent_le` — DavisKahan/SpectralTheory/FormMethod/BeamTangent.lean:652
- `TauCeti.DavisKahan.FreeBeam.Model.norm_beamColumnResidual_low` — DavisKahan/SpectralTheory/FormMethod/BeamTangent.lean:721
- `TauCeti.DavisKahan.FreeBeam.Model.norm_beamColumnResidual_high` — DavisKahan/SpectralTheory/FormMethod/BeamTangent.lean:746
- `TauCeti.DavisKahan.FreeBeam.Model.beam_equation_9_8_lower` — DavisKahan/SpectralTheory/FormMethod/BeamWeinberger.lean:37
- `TauCeti.DavisKahan.FreeBeam.Model.beam_equation_9_8_upper` — DavisKahan/SpectralTheory/FormMethod/BeamWeinberger.lean:54
- `TauCeti.DavisKahan.FreeBeam.Model.beam_equation_9_8` — DavisKahan/SpectralTheory/FormMethod/BeamWeinberger.lean:67
- `TauCeti.DavisKahan1970.Section9.weinberger_sine_sq_le_of_coupled_energy` — DavisKahan/Sources/DavisKahan1970/Section9/WeinbergerAngle.lean:50
- `TauCeti.DavisKahan1970.Section9.naive_second_scalar_lower_bound_tripwire` — DavisKahan/Sources/DavisKahan1970/Section9/WeinbergerAngle.lean:80

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 44. DK-9-infinite-residual-counterexample — Residual-infinite limitation example

- **Source anchor:** Section 9, l2 example after (9.8)
- **Source kind:** `example`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `1c9a418ebfeb827fb472bf6229506bd73f5cb5a6077f98cb467f7255ef069cb3`
- **Private-transcription provenance lines:** `[[2753, 2771]]`

### Exact registered source passage

~~~~tex
For example, take a small $\mu\ll0.6$ and
\[
  e=(1,\mu,\mu^2,\ldots,\mu^n,\ldots)^*\in\ell_2,
  \qquad
  A+H=\diag(1,\mu^{-1},\mu^{-2},\ldots,\mu^{-n},\ldots).
\]
Strictly, $e$ is not in the domain of $A+H$ because $(A+H)e=(1,1,1,\ldots)^*$ has infinite norm, but an arbitrarily small change remedies this. We have
\[
  \widehat\alpha=e^*(A+H)e/e^*e=1+\mu,
\]
but the residual has infinite norm, so none of our theorems applies. If, however, one knows lower bounds $\check\alpha_1\leq\lambda_1=1$ and $\check\alpha_2\leq\lambda_2=\mu^{-1}$ with $\check\alpha_2>\check\alpha_1$, Weinberger's theorem gives
\[
  \sin^2\theta
  \leq\frac{1+\mu-\check\alpha_1}{\check\alpha_2-\check\alpha_1}
\]
for the angle $\theta=\arcsin\mu$ between $e$ and the first eigenvector. With the best lower bounds,
\[
  (\mu=)\sin\theta\leq\frac{\mu}{\sqrt{1-\mu}}.
\]
~~~~

### Semantic audit clauses

- **`DK-9-infinite-residual-counterexample.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Section9.rawDiagonalImage_eq_one`, `TauCeti.DavisKahan1970.Section9.rawDiagonalImage_partial_energy`, `TauCeti.DavisKahan1970.Section9.truncatedDiagonalImage_energy`, `TauCeti.DavisKahan1970.Section9.diagonalOperator`, `TauCeti.DavisKahan1970.Section9.geometricTrial_notMem_diagonalDomain`, `TauCeti.DavisKahan1970.Section9.geometricTrial_form_summable`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Section9.rawDiagonalImage_eq_one`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:63`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.rawDiagonalImage_partial_energy`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:70`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.truncatedDiagonalImage_energy`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:110`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.diagonalOperator`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:177`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.geometricTrial_notMem_diagonalDomain`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:254`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.geometricTrial_form_summable`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:277`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.Section9.rawDiagonalImage_eq_one` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:63
- `TauCeti.DavisKahan1970.Section9.rawDiagonalImage_partial_energy` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:70
- `TauCeti.DavisKahan1970.Section9.truncatedDiagonalImage_energy` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:110
- `TauCeti.DavisKahan1970.Section9.diagonalOperator` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:177
- `TauCeti.DavisKahan1970.Section9.geometricTrial_notMem_diagonalDomain` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:254
- `TauCeti.DavisKahan1970.Section9.geometricTrial_form_summable` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:277
- `TauCeti.DavisKahan1970.Section9.truncatedTrial_mem_diagonalDomain` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:306
- `TauCeti.DavisKahan1970.Section9.diagonalOperator_domain` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:183
- `TauCeti.DavisKahan1970.Section9.diagonalOperator_isSelfAdjoint` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:199
- `TauCeti.DavisKahan1970.Section9.diagonalOperator_isSymmetric` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:205
- `TauCeti.DavisKahan1970.Section9.dense_diagonalDomain` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:211
- `TauCeti.DavisKahan1970.Section9.geometricTrial_hasSum_sq` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:334
- `TauCeti.DavisKahan1970.Section9.geometricTrial_norm_sq` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:345
- `TauCeti.DavisKahan1970.Section9.geometricTrial_hasSum_form` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:359
- `TauCeti.DavisKahan1970.Section9.geometricTrial_rayleighQuotient` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:376
- `TauCeti.DavisKahan1970.Section9.geometricTrial_normalizedForm_apply` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:387
- `TauCeti.DavisKahan1970.Section9.geometricTrial_hasSum_normalizedForm` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:398
- `TauCeti.DavisKahan1970.Section9.geometricTrial_hasSum_normalizedFormTail` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:409
- `TauCeti.DavisKahan1970.Section9.geometricTrial_normalizedForm_zero` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:425
- `TauCeti.DavisKahan1970.Section9.geometricTrial_normalizedForm_split` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:433
- `TauCeti.DavisKahan1970.Section9.firstEigenvector` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:445
- `TauCeti.DavisKahan1970.Section9.firstEigenvector_def` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:448
- `TauCeti.DavisKahan1970.Section9.firstEigenvector_apply` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:453
- `TauCeti.DavisKahan1970.Section9.norm_firstEigenvector` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:464
- `TauCeti.DavisKahan1970.Section9.firstEigenvector_mem_diagonalDomain` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:469
- `TauCeti.DavisKahan1970.Section9.diagonalOperator_firstEigenvector` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:476
- `TauCeti.DavisKahan1970.Section9.inner_geometricTrial_firstEigenvector` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:490
- `TauCeti.DavisKahan1970.Section9.cos_angle_geometricTrial` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:497
- `TauCeti.DavisKahan1970.Section9.sin_angle_geometricTrial` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:510
- `TauCeti.DavisKahan1970.Section9.geometricTrial_weinberger_sin_sq_le` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:532
- `TauCeti.DavisKahan1970.Section9.geometricTrial_weinberger_best_sin_sq_le` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:552
- `TauCeti.DavisKahan1970.Section9.geometricTrial_weinberger_best_sin_le` — DavisKahan/Sources/DavisKahan1970/Section9/DomainLimitation.lean:573
- `TauCeti.LinearPMap.lpDiagonal` — ForTauCeti/Analysis/InnerProductSpace/LinearPMap/DiagonalMultiplication.lean:105
- `TauCeti.LinearPMap.lpDiagonal_isSelfAdjoint` — ForTauCeti/Analysis/InnerProductSpace/LinearPMap/DiagonalMultiplication.lean:225
- `TauCeti.LinearPMap.lpDiagonal_isSymmetric` — ForTauCeti/Analysis/InnerProductSpace/LinearPMap/DiagonalMultiplication.lean:183
- `TauCeti.LinearPMap.dense_lpDiagonal_domain` — ForTauCeti/Analysis/InnerProductSpace/LinearPMap/DiagonalMultiplication.lean:170
- `TauCeti.LinearPMap.adjoint_domain_le_lpDiagonal_domain` — ForTauCeti/Analysis/InnerProductSpace/LinearPMap/DiagonalMultiplication.lean:196
- `TauCeti.LinearPMap.lpDiagonalDomain` — ForTauCeti/Analysis/InnerProductSpace/LinearPMap/DiagonalMultiplication.lean:72
- `TauCeti.LinearPMap.mem_lpDiagonalDomain_iff` — ForTauCeti/Analysis/InnerProductSpace/LinearPMap/DiagonalMultiplication.lean:100
- `TauCeti.LinearPMap.lpDiagonal_domain` — ForTauCeti/Analysis/InnerProductSpace/LinearPMap/DiagonalMultiplication.lean:127
- `TauCeti.LinearPMap.lpDiagonal_apply` — ForTauCeti/Analysis/InnerProductSpace/LinearPMap/DiagonalMultiplication.lean:131
- `TauCeti.LinearPMap.single_mem_lpDiagonal_domain` — ForTauCeti/Analysis/InnerProductSpace/LinearPMap/DiagonalMultiplication.lean:141
- `TauCeti.LinearPMap.lpDiagonal_single` — ForTauCeti/Analysis/InnerProductSpace/LinearPMap/DiagonalMultiplication.lean:155

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 45. DK-9.9-9.11 — Individual eigenvector identification inside a cluster

- **Source anchor:** Equations (9.9)–(9.11) and final bounds
- **Source kind:** `numerical_claims`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Registered source excerpt SHA-256:** `b363c295b3d268f41be6cab25ddb80342b4b24e029cacb81b6d648a75df9f061`
- **Private-transcription provenance lines:** `[[2773, 2883]]`

### Exact registered source passage

~~~~tex
So far neither approach has separately identified the eigenvectors $f_k$ within a cluster of nearly indistinguishable eigenvalues. Return to Weinberger's example. We know orthonormal $e_1,e_2$ spanning $\Range(E_0)$ and $f_1,f_2$ spanning $\Range(F_0)$. We estimated the subspace angles $\theta_1,\theta_2$ and the angles $\phi_i$ between $e_i$ and $\Range(F_0)$. We now estimate $\omega_k$, the angle between the one-dimensional subspaces $[e_k]$ and $[f_k]$.

Let $g_k$ be the unit vector in $\Range(E_0)$ closest to $f_k$, and put
\[
  \eta_k=\arccos(g_k^*f_k),
  \qquad
  Pf_k=(\cos\eta_k)g_k.
\]
Let $\psi_k$ be the angle between $[g_k]$ and $[e_k]$. Then
\[
  \cos\omega_k=\cos\eta_k\cos\psi_k,
\]
and, less precisely,
\[
  \omega_k^2\leq\psi_k^2+\eta_k^2.
\]

Write
\[
  e_k\representedby\begin{pmatrix}u_k\\0\end{pmatrix},
  \qquad
  f_k\representedby\begin{pmatrix}x_k\\y_k\end{pmatrix},
  \qquad
  u_k,x_k\in\mathbb R^2.
\]
Then
\begin{equation*}
  \begin{pmatrix}\widehat A_0&B^*\\B&\widehat A_1\end{pmatrix}
  \begin{pmatrix}x_k\\y_k\end{pmatrix}
  =\lambda_k\begin{pmatrix}x_k\\y_k\end{pmatrix},
\tag{9.9}\label{eq:9.9}
\end{equation*}
and
\[
  (\cos\eta_k)g_k=\begin{pmatrix}x_k\\0\end{pmatrix}.
\]
Here $B^*B=\widehat R^*\widehat R$, $\widehat A_0=\diag(\widehat\alpha_1,\widehat\alpha_2)$, and $\widehat A_1>500$, while $\lambda_1,\lambda_2<500$. Thus
\begin{align*}
  y_k&=(\lambda_k-\widehat A_1)^{-1}Bx_k,
  \tag{9.10}\label{eq:9.10}\\
  \bigl[\widehat A_0+B^*(\lambda_k-\widehat A_1)^{-1}B\bigr]x_k
  &=\lambda_kx_k.
  \tag{9.11}\label{eq:9.11}
\end{align*}
Thus $\lambda_k$ and $x_k$ form the eigenproblem~\eqref{eq:9.11} in two-space.

The matrix in~\eqref{eq:9.11} is the sum of the diagonal matrix
\[
  \widehat A_0-\frac{\varepsilon^2}{30\gamma_k}
\]
and an off-diagonal perturbation
\[
  \widehat H=\frac{\varepsilon^2}{30\gamma_k}
  \begin{pmatrix}0&1\\1&0\end{pmatrix}
\]
for some $\gamma_k>500-\lambda_k$. Indeed,
\[
  0\leq\frac{\varepsilon^2}{30\gamma_k}-\widehat H
  =B^*(\widehat A_1-\lambda_k)^{-1}B
  \leq\frac{B^*B}{500-\lambda_k},
\]
and $B^*B$ has rank one.

Here $\psi_k$ is the angle between $[x_k]$ and the eigenspace $[u_k]$ of the diagonal matrix. The $\tan2\theta$ theorem gives
\[
  (\widehat\alpha_2-\widehat\alpha_1)\tan2\psi_k
  \leq2\norm{\widehat H}_1
  <\frac{\varepsilon^2}{15(500-\lambda_k)}.
\]
For $0<\varepsilon<100$, \TheoremRef{8.1} also gives $0\leq\psi_k<\pi/4$, using the bounds
\[
  \widehat\alpha_k-\frac{\varepsilon^2}{15000-30\widehat\alpha_k}
  <\check\alpha_k\leq\lambda_k\leq\widehat\alpha_k.
\]
Consequently,
\[
  2\psi_k
  <\arctan\left(
    \frac{\varepsilon}{\sqrt{75}(500-\widehat\alpha_k)}
  \right).
\]

The angle $\eta_k$ is less than $\theta_1$, but a $\tan\theta$ estimate is more convenient. From~\eqref{eq:9.10},
\[
  \tan\eta_k
  =\frac{\norm{y_k}}{\norm{x_k}}
  <\frac{\norm{B}_1}{500-\lambda_k}
  \leq\frac{\varepsilon}{\sqrt{15}(500-\widehat\alpha_k)}.
\]
Combining the estimates through
\[
  \omega_k^2\leq\psi_k^2+\eta_k^2
  <\left(\frac12\tan2\psi_k\right)^2+\tan^2\eta_k,
\]
we obtain
\[
  \omega_1<\frac{0.00053\varepsilon}{1-0.00043\varepsilon},
  \qquad
  \omega_2<\frac{0.00053\varepsilon}{1-0.0016\varepsilon}.
\]
These surprisingly small bounds, despite the closeness of the eigenvalues compared with $\norm{H}_1=\varepsilon$, further support the use of Rayleigh--Ritz approximations.

The bounds can be improved. The best possible bound on $\omega_k$ for $k=1,2$ is the angle between the $k$th coordinate vector and the $k$th eigenvector of
\[
  \begin{pmatrix}
    \widehat\alpha_1&0&\varepsilon/\sqrt{30}\\
    0&\widehat\alpha_2&\varepsilon/\sqrt{30}\\
    \varepsilon/\sqrt{30}&\varepsilon/\sqrt{30}&500
  \end{pmatrix},
\]
but the proof must await investigation of Question~10.2.
~~~~

### Semantic audit clauses

- **`DK-9.9-9.11.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Section9.block_eigenproblem_iff`, `TauCeti.DavisKahan1970.Section9.schur_complement_reduction`, `TauCeti.DavisKahan1970.Section9.individual_angle_le_exact_envelope`, `TauCeti.DavisKahan1970.Section9.final_lower_individual_angle_bound`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Section9.block_eigenproblem_iff`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/SchurComplement.lean:71`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.schur_complement_reduction`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/SchurComplement.lean:110`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.individual_angle_le_exact_envelope`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/IndividualAngles.lean:62`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.final_lower_individual_angle_bound`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/NumericalBounds.lean:310`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.Section9.half_tanTwoPsi_ratio_lt_of_eigenvalue_upper` — DavisKahan/Sources/DavisKahan1970/Section9/RankOneCorrection.lean:111
- `TauCeti.DavisKahan1970.Section9.block_eigenproblem_iff` — DavisKahan/Sources/DavisKahan1970/Section9/SchurComplement.lean:71
- `TauCeti.DavisKahan1970.Section9.schur_complement_reduction` — DavisKahan/Sources/DavisKahan1970/Section9/SchurComplement.lean:110
- `TauCeti.DavisKahan1970.Section9.individual_angle_le_exact_envelope` — DavisKahan/Sources/DavisKahan1970/Section9/IndividualAngles.lean:62
- `TauCeti.DavisKahan1970.Section9.final_lower_individual_angle_bound` — DavisKahan/Sources/DavisKahan1970/Section9/NumericalBounds.lean:310
- `TauCeti.DavisKahan1970.Section9.NumericalExampleCertificate` — DavisKahan/Sources/DavisKahan1970/Section9/FullExample.lean:121, DavisKahan/Sources/DavisKahan1970/Section9/FullExample.lean:65
- `TauCeti.DavisKahan1970.Section9.norm_lower_coordinate_le` — DavisKahan/Sources/DavisKahan1970/Section9/SchurComplement.lean:161
- `TauCeti.DavisKahan1970.Section9.schurCoefficient_nonneg` — DavisKahan/Sources/DavisKahan1970/Section9/SchurComplement.lean:176
- `TauCeti.DavisKahan1970.Section9.schurCoefficient_le` — DavisKahan/Sources/DavisKahan1970/Section9/SchurComplement.lean:190
- `TauCeti.DavisKahan1970.Section9.lower_coordinate_eq_zero_of_residual_eq_zero` — DavisKahan/Sources/DavisKahan1970/Section9/SchurComplement.lean:205
- `TauCeti.DavisKahan1970.Section9.individual_angle_le_exact_envelope_of_tangents` — DavisKahan/Sources/DavisKahan1970/Section9/IndividualAngles.lean:180
- `TauCeti.DavisKahan1970.Section9.individual_angle_le_exact_envelope_of_subspace` — DavisKahan/Sources/DavisKahan1970/Section9/IndividualAngles.lean:209
- `TauCeti.DavisKahan.FreeBeam.Model.rank_beamLowFiveHundred_le` — DavisKahan/SpectralTheory/FormMethod/BeamEigenbasis.lean:80
- `TauCeti.DavisKahan.FreeBeam.Model.finiteDimensional_beamLowFiveHundred` — DavisKahan/SpectralTheory/FormMethod/BeamEigenbasis.lean:109
- `TauCeti.DavisKahan.FreeBeam.Model.finrank_beamLowFiveHundred` — DavisKahan/SpectralTheory/FormMethod/BeamEigenbasis.lean:134
- `TauCeti.DavisKahan.FreeBeam.Model.beamLowFiveHundred_eq_specRange_ritzHigh` — DavisKahan/SpectralTheory/FormMethod/BeamEigenbasis.lean:152
- `TauCeti.DavisKahan.FreeBeam.Model.beamLowOperator` — DavisKahan/SpectralTheory/FormMethod/BeamEigenbasis.lean:185
- `TauCeti.DavisKahan.FreeBeam.Model.beamLowOperator_isSymmetric` — DavisKahan/SpectralTheory/FormMethod/BeamEigenbasis.lean:201
- `TauCeti.DavisKahan.FreeBeam.Model.beamLowEigenbasis` — DavisKahan/SpectralTheory/FormMethod/BeamEigenbasis.lean:210
- `TauCeti.DavisKahan.FreeBeam.Model.beamLowEigenvector` — DavisKahan/SpectralTheory/FormMethod/BeamEigenbasis.lean:217
- `TauCeti.DavisKahan.FreeBeam.Model.beamLowEigenvalue` — DavisKahan/SpectralTheory/FormMethod/BeamEigenbasis.lean:221
- `TauCeti.DavisKahan.FreeBeam.Model.beamPerturbed_apply_beamLowEigenvector` — DavisKahan/SpectralTheory/FormMethod/BeamEigenbasis.lean:248
- `TauCeti.DavisKahan.FreeBeam.Model.beamLowEigenvector_orthonormal` — DavisKahan/SpectralTheory/FormMethod/BeamEigenbasis.lean:237
- `TauCeti.DavisKahan.FreeBeam.Model.beamLowEigenvalue_lt_five_hundred` — DavisKahan/SpectralTheory/FormMethod/BeamEigenbasis.lean:260
- `TauCeti.DavisKahan.FreeBeam.Model.beam_lower_block_equation` — DavisKahan/SpectralTheory/FormMethod/BeamEigenbasis.lean:322
- `TauCeti.DavisKahan.FreeBeam.Model.beam_lower_block_form_ge` — DavisKahan/SpectralTheory/FormMethod/BeamEigenbasis.lean:369
- `TauCeti.DavisKahan.FreeBeam.Model.beam_norm_residual_column_le` — DavisKahan/SpectralTheory/FormMethod/BeamEigenbasis.lean:389
- `TauCeti.DavisKahan.FreeBeam.Model.beam_norm_orthogonal_part_le` — DavisKahan/SpectralTheory/FormMethod/BeamEigenbasis.lean:398
- `TauCeti.DavisKahan.FreeBeam.Model.beam_starProjection_ne_zero` — DavisKahan/SpectralTheory/FormMethod/BeamEigenbasis.lean:410
- `TauCeti.DavisKahan.FreeBeam.Model.beam_tan_eta_le` — DavisKahan/SpectralTheory/FormMethod/BeamEigenbasis.lean:430
- `TauCeti.DavisKahan1970.Section9.arccos_ratio_lt_pi_div_four` — DavisKahan/Sources/DavisKahan1970/Section9/IndividualAngles.lean:132
- `TauCeti.DavisKahan1970.Section9.half_tan_two_arccos_ratio` — DavisKahan/Sources/DavisKahan1970/Section9/IndividualAngles.lean:153
- `TauCeti.DavisKahan.FreeBeam.Model.beamRitzColumnMap` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:78
- `TauCeti.DavisKahan.FreeBeam.Model.beamRitzColumnMap_vecTwo` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:88
- `TauCeti.DavisKahan.FreeBeam.Model.norm_beamRitzColumnMap_vecOne_sq_le` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:96
- `TauCeti.DavisKahan.FreeBeam.Model.beam_ritz_compression_vecOne` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:105
- `TauCeti.DavisKahan.FreeBeam.Model.beam_ritz_compression_vecTwo` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:128
- `TauCeti.DavisKahan.FreeBeam.Model.beam_ritz_coordinate_identity` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:160
- `TauCeti.DavisKahan.FreeBeam.Model.beamTrial_starProjection_eq` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:205
- `TauCeti.DavisKahan.FreeBeam.Model.norm_beamTrial_starProjection_sq` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:234
- `TauCeti.DavisKahan.FreeBeam.Model.beam_residual_at_starProjection` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:248
- `TauCeti.DavisKahan.FreeBeam.Model.beam_angle_of_ritz_coordinates` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:275
- `TauCeti.DavisKahan.FreeBeam.Model.two_coordinate_schur_identity` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:305
- `TauCeti.DavisKahan.FreeBeam.Model.beam_ritz_scalar_data` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:323
- `TauCeti.DavisKahan.FreeBeam.Model.inplane_ratio_bound` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:421
- `TauCeti.DavisKahan.FreeBeam.Model.schur_gap_bound_of_sum_nonneg` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:476
- `TauCeti.DavisKahan.FreeBeam.Model.schur_gap_bound_of_sum_nonpos` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:489
- `TauCeti.DavisKahan.FreeBeam.Model.beam_individual_angle_le` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:506
- `TauCeti.DavisKahan.FreeBeam.Model.beam_individual_angle_le_printed` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:629
- `TauCeti.DavisKahan.FreeBeam.Model.beamLowEigenvector_individual_angle_le` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:649
- `TauCeti.DavisKahan.FreeBeam.Model.beam_eigenvalue_le_ritzHigh` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:668
- `TauCeti.DavisKahan.FreeBeam.Model.beam_individual_envelope_lt_pi_div_four` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:694
- `TauCeti.DavisKahan.FreeBeam.Model.beamLowEigenvector_not_both_near` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:713
- `TauCeti.DavisKahan.FreeBeam.Model.beamLowEigenvector_ritz_pairing` — DavisKahan/SpectralTheory/FormMethod/BeamInPlaneAngle.lean:755

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 46. DK-10.1 — Sine bounds under arbitrary pairwise spectral distance

- **Source anchor:** Question 10.1
- **Source kind:** `open_question`
- **Completion obligation:** `false`
- **Census claim:** `resolved_by_modern_development` / `proved_in_build`
- **Registered source excerpt SHA-256:** `868b898f474a0d303a83f6f0232f91baebb2edc1bf016994ac1629615ec9d1fe`
- **Private-transcription provenance lines:** `[[2887, 2888]]`

### Exact registered source passage

~~~~tex
\paragraph{Question 10.1.}
If the spectra of $A_0$ and $\Lambda_1$ are known only to be at distance at least $\delta$, how well can $\angles_0$ be bounded in terms of $R$? Compare the discussions after Theorems~5.1 and~6.2.
~~~~

### Semantic audit clauses

- **`DK-10.1.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Theorem6_2`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Theorem6_2`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:142`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.Theorem6_2` — DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:142

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 47. DK-10.2 — Three-way subspace decompositions

- **Source anchor:** Question 10.2
- **Source kind:** `open_question`
- **Completion obligation:** `false`
- **Census claim:** `not_a_completion_obligation` / `not_applicable`
- **Registered source excerpt SHA-256:** `c8431b7396b6b7d629f0986f6ef0d71f011c957cf27023cffc47fae994844e1c`
- **Private-transcription provenance lines:** `[[2890, 2903]]`

### Exact registered source passage

~~~~tex
\paragraph{Question 10.2.}
Generalizing \SectionRef{1}, let $E_0,E_1,E_2$ be isometric mappings into $\Hilbert$ such that
\[
  E_0E_0^*+E_1E_1^*+E_2E_2^*=1,
\]
and let $F_0,F_1,F_2$ satisfy the analogous relation. The difference between the two decompositions might be measured by the off-diagonal entries of
\[
  \begin{pmatrix}
    E_0^*F_0&E_0^*F_1&E_0^*F_2\\
    E_1^*F_0&E_1^*F_1&E_1^*F_2\\
    E_2^*F_0&E_2^*F_1&E_2^*F_2
  \end{pmatrix},
\]
just as~\eqref{eq:1.7} was used here. If the decompositions are associated with reducing subspaces of two nearby operators, can estimates parallel to those in this paper be found?
~~~~

### Semantic audit clauses

- **`DK-10.2.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: *(none; inspect the row mapping/source context)*

### Primary Lean declarations for semantic review

No primary Lean declaration is registered for this non-obligation source question.

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- *(none)*

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 48. DK-10.3 — Joint eigenvalue–eigenvector bounds

- **Source anchor:** Question 10.3
- **Source kind:** `open_question`
- **Completion obligation:** `false`
- **Census claim:** `not_a_completion_obligation` / `not_applicable`
- **Registered source excerpt SHA-256:** `3eef588dbf2a6d19dbb738db58853081f4ef70dbbe6223423b6f84cf8187bb33`
- **Private-transcription provenance lines:** `[[2905, 2906]]`

### Exact registered source passage

~~~~tex
\paragraph{Question 10.3.}
Pursuing the remark after \TheoremRef{8.1}, seek best possible bounds on expressions involving both eigenvalue changes and eigenvector changes.
~~~~

### Semantic audit clauses

- **`DK-10.3.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: *(none; inspect the row mapping/source context)*

### Primary Lean declarations for semantic review

No primary Lean declaration is registered for this non-obligation source question.

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- *(none)*

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

## 49. DK-10.4 — Perturbation bounds for functional calculus

- **Source anchor:** Question 10.4
- **Source kind:** `open_question`
- **Completion obligation:** `false`
- **Census claim:** `not_a_completion_obligation` / `not_applicable`
- **Registered source excerpt SHA-256:** `4969fbdfdb8b7a27fd5a31e5918f89c9601862cbf2f8c2fd3d254dbdb3c3630b`
- **Private-transcription provenance lines:** `[[2908, 2925]]`

### Exact registered source passage

~~~~tex
\paragraph{Question 10.4.}
The spectral decomposition
\[
  A=\int_{-\infty}^{\infty}\lambda\,d\Omega(\lambda)
\]
defines
\[
  f(A)=\int_{-\infty}^{\infty}f(\lambda)\,d\Omega(\lambda)
\]
for many real functions $f$. The algebraic and topological properties of this functional calculus are well known, but little is known about bounds on $f(A+H)-f(A)$ in terms of $H$.

For example, let $f(\xi)=1$ for $\xi\leq\alpha$ and $f(\xi)=0$ for $\alpha+\delta\leq\xi$. Under the $\tan2\theta$ hypotheses, $f(A)=P$, $f(A+H)=Q$, and $f(A_0)=1$, so
\[
  \norm{f(A+H)-f(A)}=\norm{Q-P}=\norm{\sin\angles},
\]
where
\[
  \delta\norm{\tan2\angles}\leq2\norm{H},
~~~~

### Semantic audit clauses

- **`DK-10.4.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: *(none; inspect the row mapping/source context)*

### Primary Lean declarations for semantic review

No primary Lean declaration is registered for this non-obligation source question.

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- *(none)*

</details>

### Independent audit checklist

- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every mathematical clause in the registered source excerpt.
- [ ] Real/complex scalar scope matches the source, including any source statement that is field-independent.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.
- [ ] Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.
- [ ] If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.

### Auditor verdict

- **Verdict:** _fill in_
- **Reasoning / mismatch details:** _fill in_
- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_
- **Unregistered source clause discovered, if any:** _fill in_

---

# Final independent conclusion

- **45 mathematical completion obligations reviewed:** yes / no
- **43 census-claimed exact obligations independently accepted:** yes / no
- **1 census-claimed refuted obligations independently accepted:** yes / no
- **Nonterminal census rows:** `S2-tan-two-theta` (compiled_specialization)
- **Any unregistered mathematical claims found:** yes / no
- **Compiler certificate clean and complete:** yes / no
- **Is the repository's claim of 100% theorem-statement-level Davis--Kahan 1970 coverage justified?** yes / no / uncertain

## Findings requiring action

1. _none recorded yet_
