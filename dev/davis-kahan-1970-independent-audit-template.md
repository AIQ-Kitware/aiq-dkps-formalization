# Davis--Kahan 1970 independent result audit packet

## Claim boundary presented to the reviewer

The repository does **not** claim that every mathematical sentence, proof equation, worked example, historical comparison, or open question in the paper is separately formalized as a Lean theorem. It claims exact formal coverage of every result that Davis and Kahan actually establish in the paper.

The two accounting layers are deliberately both visible:

- **Source fidelity:** `dev/davis-kahan-1970-source-atom-inventory.json` contains **272 atoms** in paper order, including all **64 numbered equations**. Every atom has an explicit result-boundary reason code and names any counted result(s) it supports.
- **Formalization denominator:** `dev/davis-kahan-1970-formalization-result-inventory.json` contains exactly **29 counted results**: the four Section 2 headline theorems plus every named theorem, proposition, lemma, and corollary Davis--Kahan actually establish.
- Section 10 questions, explicitly deferred/unproved claims, definitions, proof-only derivations, examples, numerical working, historical/external results, and theorem-adjacent remarks remain visible in source fidelity but do not enlarge the denominator.
- A false counted result remains in the denominator and requires exact formal refutation plus the repository's separate best-effort repair disposition.

Each counted result carries a **source-alignment classification**, and the three values are not interchangeable:

1. `locally_exact` — the printed statement is self-contained and Lean matches it directly.
2. `paper_faithful_nonlocal_source_interpretation` — the result is true and Lean is faithful, but the correspondence relies on source semantics stated elsewhere in the paper (a global convention, a later standing assumption, an inherited proof context). Lean therefore says something the printed display does not literally say, and the packet discloses exactly what.
3. `refuted_as_transcribed` — the printed statement is meaningful and mathematically false; an exact counterexample and a separate repair record are required.

Category 2 is never a softened category 3. If a reviewer concludes that a category 2 result is actually false as printed, that is a FAIL and the repository is asking to be told.

Current result-level status: **29/29 terminal**, **0 awaiting semantic closure**.
Result-selection/boundary review: **accepted** under policy `dk_established_results_only`.

A hostile reviewer should challenge both layers independently: (1) whether the fidelity inventory omitted source material or misclassified an exclusion, and (2) whether each of the 29 counted result statements is represented exactly in Lean.

## Authoritative checked-in materials

- Distributable source specification: `prose/distilled_literature/DavisKahan1970_part_III.tex`
- Source-fidelity inventory: `dev/davis-kahan-1970-source-atom-inventory.json`
- Formalization-result inventory: `dev/davis-kahan-1970-formalization-result-inventory.json`
- Source census: `dev/davis-kahan-1970-full-source-census.json`
- Organizational statement map: `dev/davis-kahan-1970-statement-map.json`
- Compiler certificate: **not supplied**; theorem types below are placeholders.

## Result-level verdict vocabulary

Use one of: **PASS exact**, **PASS refuted + repair**, **FAIL boundary**, **FAIL scope**, **FAIL conclusion**, **FAIL missing clause**, **FAIL evidence**, or **UNCERTAIN**.

A result whose printed statement is **not locally self-contained** carries an extra section headed **NONLOCAL SOURCE-SEMANTICS DEPENDENCY**, with its own verdict: **PASS paper-faithful nonlocal interpretation**, **FAIL illicit strengthening**, or **UNCERTAIN source interpretation**. That section discloses, before you read the Lean evidence, exactly which qualification the printed statement omits and which nonlocal source material the repository used to read it. Those results are listed here so they cannot be missed: `S2-tan-theta`.

## 1. S2-sin-theta — Single-angle sine theorem

- **Counted result kind:** `unnumbered_theorem`
- **Exact source anchor:** Section 2, sin theta theorem
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `8e5e36e64c718f1cdb002dd3c5a191c8919fa22bad64020bdbf8f22adb6a3f72`

### Atoms inside the counted printed result

- `S2-sin-theta.ui-norm-scope` — **counted_result_scope** — Every norm in the four headline theorem statements is an arbitrary unitary-invariant norm.
- `S2-sin-theta.gap-hypothesis` — **counted_result_hypothesis** — The sine theorem uses interval/exterior separation, allowing the A0 and Lambda1 roles to be interchanged.
- `S2-sin-theta.directed-conclusion` — **counted_result_statement** — delta ||sin Theta0|| <= ||R||.
- `S2-unbounded-scope.infinite-dimensional-scope` — **counted_result_scope** *(shared/cross-block scope)* — All four main results apply in infinite as well as finite dimension.
- `S2-unbounded-scope.arbitrary-ui-scope` — **counted_result_scope** *(shared/cross-block scope)* — All four main results apply to arbitrary UI norms.
- `S2-unbounded-scope.unbounded-selfadjoint-scope` — **counted_result_scope** *(shared/cross-block scope)* — The results extend to unbounded self-adjoint A under the stated domain condition.
- `S2-unbounded-scope.bounded-residual-needed` — **counted_result_scope** *(shared/cross-block scope)* — Useful unbounded conclusions require the pertinent perturbation or residual to extend boundedly.
- `S2-unbounded-scope.half-infinite-gap-intervals` — **counted_result_scope** *(shared/cross-block scope)* — Gap intervals may be half-infinite and the remaining spectra unbounded.

### Same-block material explicitly outside the counted result

- `S2-sin-theta.family-distinctness` — **expository_commentary_not_result** — The four Section 2 theorem families are distinct rather than mere restatements.
  - Boundary rationale: This atom is explanatory/source-scope commentary rather than a counted Davis--Kahan result statement.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
The four Section~2 statements are distinct theorem families; the source does not present them as cosmetic reformulations of one another.  Every displayed norm in these theorem statements is an arbitrary unitary-invariant norm in the source sense.

Assume that for some interval $[\beta,\alpha]$ and $\delta>0$, either
\[
 \spec(A_0)\subset[\beta,\alpha],
 \qquad
 \spec(\Lambda_1)\cap(\beta-\delta,\alpha+\delta)=\varnothing,
\]
or the same condition with $A_0$ and $\Lambda_1$ interchanged.  Then, for every unitary-invariant norm,
\[
 \boxed{\delta\norm{\sin\Theta_0}\le\norm{R}.}
\]
~~~~

### Source-facing Lean declarations

#### `DavisKahan1970.sinTheta_headline`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SineTheta/PaperSurface.lean:140`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.sinTheta_headline_generic`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SineTheta/HeadlineGeneric.lean:102`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.sinTheta`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/GeneralSinTheta.lean:53`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.sinTheta_real_exactPaper`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:98`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.generalizedSinTheta`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/GeneralSinTheta.lean:40`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.generalizedSinTheta_real_exactPaper`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:109`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `DavisKahan1970.sinTheta_complex`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/GeneralSinTheta.lean:57`, `DavisKahan/Sources/DavisKahan1970/SineTheta/PaperSurface.lean:234`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `DavisKahan1970.sinTheta_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/GeneralSinTheta.lean:61`, `DavisKahan/Sources/DavisKahan1970/SineTheta/PaperSurface.lean:322`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `DavisKahan1970.sinTheta_complex_of_intervalExterior`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SineTheta/PaperSurface.lean:285`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `DavisKahan1970.sinTheta_real_of_intervalExterior`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SineTheta/PaperSurface.lean:373`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 2. S2-tan-theta — Single-angle tangent theorem

- **Counted result kind:** `unnumbered_theorem`
- **Exact source anchor:** Section 2, tan theta theorem
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `paper_faithful_nonlocal_source_interpretation`
- **Printed statement locally self-contained:** `False`
- **Organizational source-block hash:** `c85f8a2839187dd9ae4d020608816821c3b1f30e401eb5e52d4cbce093e82b3c`

### ⚠ NONLOCAL SOURCE-SEMANTICS DEPENDENCY

**This printed result is not locally self-contained. Read this section before the Lean evidence.**

- **Interpretation review status:** `accepted`
- **Classification:** `paper_faithful_nonlocal_source_interpretation`
- **Reviewed on:** 2026-08-12
- **Kept distinct from the repository's canonical refutation:** `DK-4.4-prop`

#### 1. What the printed statement actually says

The full registered source block appears below under *Full registered source block*. The clause at issue and the qualification it does not carry:

The printed Section 2 tangent theorem states only the ordered spectral gap and H_0 = 0. It states neither the matching-dimension condition (1.5) nor the crossed-dimension condition (3.5), and (3.5) is not introduced anywhere in the paper until Section 3. The Lean statements of the ambient conclusion nevertheless carry a crossed-defect hypothesis corresponding to (3.5). A reviewer must decide whether that hypothesis formalizes semantics the paper already imposes nonlocally, or strengthens the printed result.

#### 2. Where the paper supplies the missing semantics

- Section 1 paper-wide convention that some results are vacuous when certain norms fail to exist, with no repetition of the qualification at the individual statements.
- Section 3 standing convention, fixed immediately after the proof of Proposition 3.2, that (3.5) as well as (1.5) is assumed for the remainder of the paper except where the contrary is stated.
- Proposition 3.2 and its remark: (3.5) is equivalent to direct-rotation existence outside the acute case, is automatic when either P-space or its orthocomplement is finite-dimensional, and is not implied by (1.5) in infinite dimension (bilateral-shift example).
- Section 3 angle-operator/polar passage: the partial isometry J_0 with J_0 Theta_0 = Theta_1 J_0 exists as described in the direct-rotation setting fixed by that standing convention.
- Section 6 proof context: the printed ambient conclusion is proved in Section 6, inside the standing scope, by comparing the two tangent corners through J_0 and applying Lemmas 6.1 and 6.2.

#### 3. Exact source atoms used to interpret the statement

| Atom | Interpretive role | Source location | Content |
|---|---|---|---|
| `S1-block-residual.norm-existence-vacuity-convention` | `paper_wide_convention` | Section 1, paper-wide convention stated with the bounded/unbounded scope sentences preceding (1.1). | Paper-wide convention: some of the paper's results are vacuous when certain norms occurring in them fail to exist, and the source will not repeat that qualification at the individual statements. |
| `S1-block-residual.eq-1-5` | `related_dimension_condition` | Equation (1.5) | Exact mathematical content of source equation (1.5) as reconstructed in the distributable TeX. |
| `S1-ui-norms.ambient-angle-doubling` | `related_unqualified_claim` | Section 1, equations (1.9)--(1.18). | Section 1 states, in anticipation of the Section 3 direct-rotation construction and without restating a dimension hypothesis, that the nonzero angle data of the ambient angle operator are those of Theta_0 occurring twice, once from each side. |
| `S2-tan-theta.ambient-conclusion` | `printed_statement_clause` | Section 2, second unnumbered theorem. | delta \|\|tan Theta\|\| <= \|\|H\|\|. |
| `DK-3.2-prop.eq-3-5` | `omitted_qualification` | Equation (3.5) | Exact mathematical content of source equation (3.5) as reconstructed in the distributable TeX. |
| `DK-3.2-prop.finite-crossing-automatic` | `automatic_case` | Remark following Proposition 3.2 and equation (3.5). | Under the assumed (1.5), condition (3.5) holds automatically whenever either dim P-space or dim P-perp-space is finite. |
| `DK-3.2-prop.bilateral-shift-counterexample` | `scope_separating_example` | Proposition 3.2 and equation (3.5). | The bilateral-shift example on two-sided square-summable sequences satisfies (1.5) with nested P-space and Q-space, has crossing subspaces of dimensions 1 and 0, and therefore fails (3.5): the matching-dimension conditions do not imply the crossing-dimension condition in infinite dimension. |
| `S3-standing-scope.crossed-dimension-standing-assumption` | `later_standing_assumption` | Section 3, standing convention stated immediately after the proof of Proposition 3.2. | Standing convention: (3.5) is assumed as well as (1.5) for the remainder of the paper, except where the contrary is explicitly stated, so a direct rotation always exists and the development uses its direct special case (3.6). |
| `DK-3.1-thm.angle-operator-partial-isometry` | `proof_context_dependency` | Section 3, the angle-operator/polar passage preceding Theorem 3.1, under the standing conventions fixed after Proposition 3.2. | For the direct rotation, Theta_j = arccos C_j, the two angle operators are isometric-equivalent apart from the dimensionalities of their null spaces, and the polar resolution S_0 = J_0 sin Theta_0 gives a partial isometry J_0 of the closed range of Theta_0 onto that of Theta_1 with J_0 Theta_0 = Theta_1 J_0. |
| `DK-6.3-thm.tangent-proof-temporary-boundedness` | `proof_context_dependency` | Section 6, proof of the tangent theorem, immediately before the Ky Fan estimate. | The Section 6 tangent proof temporarily supposes that all operators are bounded and that S_0 is compact, and defers the removal of both restrictions to the Appendix to Section 6. |
| `DK-6.3-thm.ambient-wholeSpace-assembly` | `proof_context_dependency` | Section 6, the whole-space step of the tangent proof, following the directed Ky Fan estimate. | The ambient conclusion is assembled from the directed one: tan Theta has the two-corner block form built from J_0, tan Theta_0 and tan Theta_1, the two corners have equal unitarily invariant norms through J_0, and Lemmas 6.1 and 6.2 then give delta \|\|tan Theta\|\| <= \|\|H\|\|. |

The source passages that carry these atoms are reproduced verbatim here so the reading can be checked without the original paper:

<details><summary>Source block <code>S1-block-residual</code></summary>

~~~~tex
Let $\Hsp$ be a separable Hilbert space, real or complex; finite dimensionality is not assumed.  In the main bounded setting $A=A^*$ and $A+H=(A+H)^*$ are bounded.  The paper also allows self-adjoint unbounded $A$ when the later domain conditions are met, specifically when the domain of $H$ contains that of $A$.

At this same point the source fixes a paper-wide semantic convention: some of its results are vacuous when certain norms occurring in them fail to exist, and it announces that it will not make special mention of this at the individual statements.

Let $P$ reduce $A$, with isometries $E_0,E_1$ onto $P\Hsp$ and $P^\perp\Hsp$.  Every $x\in\Hsp$ has the coordinate representation
\begin{equation}
 x=E_0x_0+E_1x_1,
 \qquad x_j=E_j^*x.
 \tag{1.1}
\end{equation}
Relative to this decomposition,
\begin{equation}
 A\sim\begin{pmatrix}A_0&0\\0&A_1\end{pmatrix},
 \qquad
 H\sim\begin{pmatrix}H_0&B^*\\B&H_1\end{pmatrix},
 \qquad B=E_1^*HE_0.
 \tag{1.2}
\end{equation}
Let $Q$ reduce $A+H$, with isometries $F_0,F_1$ onto $Q\Hsp,Q^\perp\Hsp$.  Then
\begin{equation}
 A+H\sim_F\begin{pmatrix}\Lambda_0&0\\0&\Lambda_1\end{pmatrix}.
 \tag{1.3}
\end{equation}
No assumption is made here that $P$ or $Q$ is a spectral projector or that the two diagonal spectral sets are disjoint.

A unitary $V$ carries $P\Hsp$ onto $Q\Hsp$ precisely through
\begin{equation}
 VP=QV \quad(\text{hence }VP^\perp=Q^\perp V),
 \tag{1.4}
\end{equation}
which requires
\begin{equation}
 \dim P\Hsp=\dim Q\Hsp,
 \qquad \dim P^\perp\Hsp=\dim Q^\perp\Hsp.
 \tag{1.5}
\end{equation}
Writing $W_j=F_j^*VE_j$, the $W_j$ are unitary between the corresponding coordinate spaces, and conversely any such pair determines $V$.  In $E$-coordinates the block form is
\begin{equation}
 V\sim\begin{pmatrix}C_0&-S_1\\S_0&C_1\end{pmatrix},
 \tag{1.6}
\end{equation}
with
\begin{equation}
 \begin{pmatrix}C_0&-S_1\\S_0&C_1\end{pmatrix}
 =
 \begin{pmatrix}E_0^*F_0&E_0^*F_1\\E_1^*F_0&E_1^*F_1\end{pmatrix}
 \begin{pmatrix}W_0&0\\0&W_1\end{pmatrix}.
 \tag{1.7}
\end{equation}
Thus changing the unitary $V$ only changes the within-subspace unitary coordinates $W_0,W_1$.

For the numerical-approximation interpretation, $E_0$ contains orthonormal trial vectors and $A_0$ is a trial/Ritz operator.  The residual is
\begin{equation}
 R=(A+H)E_0-E_0A_0.
 \tag{1.8}
\end{equation}
When $A_0$ is the block inherited from $A$, this gives $R=HE_0$ and the $E$-coordinate column of $R$ is the first column of the block matrix for $H$.  If instead the Rayleigh--Ritz choice
\[
 A_0=E_0^*(A+H)E_0
\]
is made, then $H_0=0$ and
\[
 R^*R=H_0^2+B^*B=B^*B.
\]
More generally the identity $R^*R=H_0^2+B^*B$ shows that the Rayleigh--Ritz choice minimizes residual size among these block choices.  The source distinguishes this one-sided off-diagonality $H_0=0$ from the stronger condition $H_0=H_1=0$ used by a different main theorem.

The paper also records the standard residual-to-eigenvalue consequence: if $\alpha_1,\ldots,\alpha_m$ are the eigenvalues of $A_0$, then an ordering of $m$ eigenvalues $\lambda_j$ of $A+H$ can be chosen so that
\[
 \sum_j(\alpha_j-\lambda_j)^2\le \norm{R}_{\mathrm{sq}}^2,
 \qquad
 |\alpha_j-\lambda_j|\le \norm{R}_1.
\]
~~~~

</details>

<details><summary>Source block <code>S1-ui-norms</code></summary>

~~~~tex
For bounded operators between Hilbert spaces, $\norm{\cdot}$ denotes an arbitrary normalized unitary-invariant norm: besides the norm axioms,
\begin{equation}
 \norm{VKW}=\norm{K}
 \tag{1.9}
\end{equation}
for unitary $V,W$, rank-one operators satisfy $\norm{uv^*}=\norm{u}\norm{v}$, and left/right multiplication by contractions cannot increase the norm.

For compact $K$, write its singular values as $\kappa_1\ge\kappa_2\ge\cdots$.  They satisfy the minimax characterization
\begin{equation}
 \kappa_k=\inf_{\dim\mathcal S=k-1}\ \sup_{\substack{\norm{x}=1\\x\perp\mathcal S}}\norm{Kx}.
 \tag{1.10}
\end{equation}
The same minimax expression makes sense for general bounded operators; in the noncompact case the source warns that spectral-multiplicity language may be more appropriate.  The Hilbert--Schmidt norm is $\norm{K}_{\mathrm{sq}}^2=\sum_k\kappa_k^2=\operatorname{tr}(K^*K)$, and the Ky Fan norms are
\begin{equation}
 \norm{K}_\nu=\kappa_1+\cdots+\kappa_\nu.
 \tag{1.11}
\end{equation}
Fan dominance is used in the strong form: $\norm{K}\le\norm{L}$ for every unitary-invariant norm iff the inequality holds for every Ky Fan norm.  The source also uses
\begin{equation}
 \norm{K}_\nu=\sup_{\Omega}\norm{K\Omega}_\nu
 \tag{1.12}
\end{equation}
and
\begin{equation}
 \norm{K}_\nu
 =\sup_{\Omega,\Upsilon}\norm{\Upsilon K\Omega}_\nu
 =\sup\Re\sum_{k=1}^{\nu}y_k^*Kx_k,
 \tag{1.13}
\end{equation}
where $\Omega,\Upsilon$ range over rank-$\nu$ orthogonal projectors and the last supremum ranges over orthonormal $\nu$-tuples $x_k,y_k$.

For nonzero vectors the source uses
\begin{equation}
 \angle(x,y)=\arccos\frac{\Re(y^*x)}{\norm{x}\norm{y}},
 \tag{1.14}
\end{equation}
and this convention preserves the cosine-law identity
\[
 \norm{x+y}^2=\norm{x}^2+\norm{y}^2
 +2\norm{x}\norm{y}\cos\angle(x,y).
\]
The angle between the one-dimensional subspaces they span is
\begin{equation}
 \arccos\frac{|y^*x|}{\norm{x}\norm{y}}.
 \tag{1.15}
\end{equation}
For the pair $P,Q$, the intrinsic angle operators are
\begin{equation}
 \Theta_j=\arccos(C_jC_j^*)^{1/2},\qquad 0\le\Theta_j\le\pi/2,
 \tag{1.16}
\end{equation}
and
\begin{equation}
 \Theta\sim\begin{pmatrix}\Theta_0&0\\0&\Theta_1\end{pmatrix}.
 \tag{1.17}
\end{equation}
The singular values of $S_0$ are $\sin\theta_k$, where $\theta_k$ are the spectral/singular-angle data of $\Theta_0$.  The source states here, in anticipation of the Section~3 construction and without restating a dimension hypothesis, that the nonzero angle data of $\Theta$ are the same as those of $\Theta_0$ but occur twice, once from each side.  In every unitary-invariant norm,
\[
 \norm{Q^\perp P}=\norm{Q^\perp E_0}=\norm{\sin\Theta_0},
 \qquad
 \norm{P-Q}=\norm{\sin\Theta}.
\]
For the operator norm the source also identifies the largest one-sided distance with $\norm{\sin\Theta}_1$ and the closest-unit-vector distance with $2\norm{\sin(\Theta/2)}_1$.

Section~3 constructs a partial isometry
\[
 J\sim\begin{pmatrix}0&-J_0^*\\J_0&0\end{pmatrix}
\]
so that the distinguished direct rotation is
\begin{equation}
 U=e^{J\Theta}=\cos\Theta+J\sin\Theta
 \sim
 \begin{pmatrix}
 \cos\Theta_0&-J_0^*\sin\Theta_1\\
 J_0\sin\Theta_0&\cos\Theta_1
 \end{pmatrix}.
 \tag{1.18}
\end{equation}
Section~4 proves the stated extremal meaning of this $U$; the four main perturbation theorems themselves are formulated only through $\Theta,\Theta_0$ and trigonometric functions thereof.
~~~~

</details>

<details><summary>Source block <code>S2-tan-theta</code></summary>

~~~~tex
Assume
\[
 \spec(A_0)\subset[\beta,\alpha],
 \qquad
 \spec(\Lambda_1)\subset[\alpha+\delta,\infty),
 \qquad \delta>0,
\]
and impose the Rayleigh--Ritz/off-diagonal condition $H_0=0$ (equivalently $A_0=E_0^*(A+H)E_0$ in this setup).  Then for every unitary-invariant norm both conclusions hold:
\[
 \boxed{\delta\norm{\tan\Theta_0}\le\norm{R}},
 \qquad
 \boxed{\delta\norm{\tan\Theta}\le\norm{H}}.
\]
The first is directed and residual-based; the second uses the ambient angle and the full perturbation.
~~~~

</details>

<details><summary>Source block <code>DK-3.2-prop</code></summary>

~~~~tex
Outside the acute case a direct rotation exists iff the two crossing subspaces have the same dimension:
\begin{equation}
 \dim(P\Hsp\cap Q^\perp\Hsp)
 =\dim(P^\perp\Hsp\cap Q\Hsp).
 \tag{3.5}
\end{equation}
When it exists it need not be unique.  On the two crossing subspaces a direct rotation satisfies $U^2x=-x$.

The source appends a remark comparing (3.5) with the earlier matching-dimension condition (1.5).  Since (1.5) is being assumed, (3.5) holds automatically whenever either $\dim P\Hsp$ or $\dim P^\perp\Hsp$ is finite.  In infinite dimensions it can fail: let $\Hsp$ be the two-sided square-summable sequences $(\ldots,a_{-1},a_0,a_1,\ldots)$, let $P\Hsp$ be those with $a_n=0$ for $n<0$, and let $Q\Hsp$ be those with $a_n=0$ for $n\le0$.  The bilateral shift $V(a_n)=(b_n)$ with $b_n=a_{n-1}$ is a unitary satisfying (1.4), so (1.5) holds; but $PQ^\perp$ is the projector onto the sequences vanishing off $n=0$ while $P^\perp Q=0$, so the two crossing subspaces of (3.5) have dimensions $1$ and $0$ and (3.5) fails.  Hence (1.5) does not imply (3.5), and by this proposition the shift pair admits no direct rotation at all.
~~~~

</details>

<details><summary>Source block <code>S3-standing-scope</code></summary>

~~~~tex
Immediately after the proof of Proposition~3.2 the source fixes a standing convention for the remainder of the paper: (3.5) is assumed as well as (1.5), except where the contrary is stated.  Consequently a direct rotation always exists, and rather than the more general unitary $V$ of (1.6) the development deals mostly with its direct special case (3.6).  Every later result that does not restate the dimension conditions is therefore read under both (1.5) and (3.5).
~~~~

</details>

<details><summary>Source block <code>DK-3.1-thm</code></summary>

~~~~tex
Before the classification the source brings in the angle operators (1.16)--(1.17) for the direct rotation, under the standing conventions just fixed: $\Theta_j=\arccos C_j$.  Because the unitarity relations give $S_0^*S_0=1-C_0^2$ on $\mathcal X(E_0)$ and $S_0S_0^*=1-C_1^2$ on $\mathcal X(E_1)$, the two operators $\Theta_0$ and $\Theta_1$ are isometric-equivalent except perhaps for different dimensionalities of their null spaces.  The polar resolution of $S_0$ is $S_0=J_0\sin\Theta_0$, where $J_0$ carries $\overline{\operatorname{Ran}\Theta_0}$ isometrically onto $\overline{\operatorname{Ran}\Theta_1}$ and satisfies $J_0\Theta_0=\Theta_1J_0$; the skew block operator $J$ of (1.18) is built from $J_0$, is unitary on $\overline{\operatorname{Ran}\Theta}$ with $J^2=-1$ there, and is set to $0$ on $\operatorname{Null}\Theta$.

Assume
\[
 \dim P\Hsp=\dim Q\Hsp,
 \qquad
 \dim(P\Hsp\cap Q^\perp\Hsp)=\dim(P^\perp\Hsp\cap Q\Hsp).
\]
A complete invariant of the pair $(P\Hsp,Q\Hsp)$ under isometric equivalence is given by the spectral multiplicity functions of $\Theta_0$ and $\Theta_1$.  Conversely, the angle operators may be arbitrary Hermitian operators satisfying
\[
 0\le\Theta_j\le\pi/2,
\]
their domain dimensions sum to $\dim\Hsp$, and their spectral multiplicity functions agree except possibly at the eigenvalue/spectral point $0$.  The proof reconstructs the pair from these angle data and the corresponding partial isometry $J_0$.
~~~~

</details>

<details><summary>Source block <code>DK-6.3-thm</code></summary>

~~~~tex
Restore the Section~1--2 hypotheses and write the direct rotation as
\begin{equation}
 U\sim
 \begin{pmatrix}C_0&-S_0^*\\S_0&C_1\end{pmatrix}
 =
 \begin{pmatrix}
 \cos\Theta_0&-J_0^*\sin\Theta_1\\
 J_0\sin\Theta_0&\cos\Theta_1
 \end{pmatrix},
 \qquad J_0\Theta_0=\Theta_1J_0,
 \quad C_j\ge0.
 \tag{6.2}
\end{equation}
The two reducing representations are related by
\begin{equation}
 \begin{pmatrix}A_0+H_0&B^*\\B&A_1+H_1\end{pmatrix}
 \begin{pmatrix}C_0&-S_0^*\\S_0&C_1\end{pmatrix}
 =
 \begin{pmatrix}C_0&-S_0^*\\S_0&C_1\end{pmatrix}
 \begin{pmatrix}\Lambda_0&0\\0&\Lambda_1\end{pmatrix},
 \tag{6.3}
\end{equation}
so in particular
\begin{equation}
 (A_0+H_0)(-S_0^*)+B^*C_1=-S_0^*\Lambda_1.
 \tag{6.4}
\end{equation}
Under $A_0\le\alpha$, $\Lambda_1\ge\alpha+\delta$, and $H_0=0$, transposing (6.4) gives
\begin{equation}
 C_1B=S_0A_0-\Lambda_1S_0.
 \tag{6.5}
\end{equation}
Under $A_0\le\alpha$, $\Lambda_1\ge\alpha+\delta$, and $H_0=0$, singular vectors for $S_0$ give the scalar estimate
\begin{equation}
 \cos\theta_j\,|y_j^*Bx_j|\ge\delta\sin\theta_j,
 \tag{6.6}
\end{equation}
so the relevant cosines are positive and Ky Fan/Fan dominance gives the directed tangent conclusion $\delta\norm{\tan\Theta_0}\le\norm{R}$.  In this argument the source temporarily supposes that all the operators are bounded and that $S_0$ is compact, and states that the Appendix to Section~6 removes both restrictions.

The ambient conclusion of the $\tan\theta$ theorem is then assembled from the directed one through the direct-rotation geometry of (6.2).  The source observes that
\[
 \tan\Theta\sim
 \begin{pmatrix}
 0&-J_0^*\tan\Theta_1\\
 J_0\tan\Theta_0&0
 \end{pmatrix},
 \qquad
 \norm{J_0\tan\Theta_0}
 =\norm{J_0^*\tan\Theta_1}
 =\norm{\tan\Theta_0}
 \le\norm B/\delta,
\]
the two off-diagonal corners being compared through the same partial isometry $J_0$ of the direct rotation.  Lemmas~6.1 and~6.2 then give
\[
 \delta\norm{\tan\Theta}
 \le\norm{\begin{pmatrix}0&B^*\\B&0\end{pmatrix}}
 \le\norm{\begin{pmatrix}0&B^*\\B&H_1\end{pmatrix}}
 =\norm H,
\]
which is the ambient conclusion $\delta\norm{\tan\Theta}\le\norm H$.  The source then gives Example~6.1 showing the one-sided placement of $\Lambda_1$ is essential: a finite matrix example has $\delta=1$ and tangent quantity $1$ while the residual is only $1/\sqrt2$ if spectral mass is allowed on the wrong side.

The generalized theorem retains exact Rayleigh--Ritz trial data.  Assume $E_0,E_1,F_0,F_1$ are exhaustive isometries whose ranges reduce $A$ and $A+H$, respectively, but allow
\[
 \dim\mathcal X(E_0)<\dim\mathcal X(F_0).
\]
Set $A_0=E_0^*(A+H)E_0$, define $R$ by (1.8), and let the directed sine data have the singular values of $E_0^*F_1$.  If
\[
 \spec(A_0)\subset[\beta,\alpha],
 \qquad
 \spec(\Lambda_1)\subset[\alpha+\delta,\infty),
\]
then the corresponding directed tangent operator satisfies, for every unitary-invariant norm,
\[
 \boxed{\delta\norm{\tan\Theta_0}\le\norm{R}.}
\]
~~~~

</details>

#### 4. The chronological mismatch

The theorem is printed in Section 2, before (3.5) exists in the exposition, and is proved in Section 6, after (3.5) has been standing since Section 3. The Section 2 display therefore does not locally carry the qualification that makes the ambient tangent quantity a meaningful finite norm in the general infinite-dimensional case.

#### 5. What Lean says, and exactly where the implicit semantics became explicit

- `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent`
  - Carries `h35 : CrossedDefectsEquivalent U V`, the constructive form of (3.5) (an isometric equivalence of the two crossed defect spaces), and concludes both `N.Mem (paperTanAngleOperatorC U V)` and the sharp inequality. Membership in the norm's ideal is a conclusion, which is the explicit form of the source's vacuity convention.
- `TauCeti.DavisKahan1970.tanTheta_unboundedCompression_ambient_paperUINorm_exact`
  - Appendix-complete complex ambient endpoint. The Ritz compression is a genuinely unbounded self-adjoint closed operator semibounded above in form; the residual and perturbation are bounded. The lower-corner Ky Fan estimate is supplied by the Appendix truncation/release theorem, (3.5) supplies ambient transversality, and norm-ideal membership is concluded.
- `TauCeti.DavisKahan1970.tanTheta_unboundedCompression_ambient_paperUINorm_real_exact`
  - Real Appendix-complete ambient endpoint with a genuinely unbounded Ritz compression. The unbounded compression data are complexified only for the spectral-cutoff/Ky-Fan proof, while the source angle operator, perturbation, crossed-defect condition, and final PaperUI statement are real; the sharp factor-one inequality and ideal membership descend exactly.
- `TauCeti.DavisKahan1970.tanTheta_unbounded_ambient_paperUINorm_exact`
  - Complex specialization with an unbounded ambient self-adjoint operator but bounded Ritz compression. It retains the same (3.5) explicitation and sharp ambient conclusion; the stronger Appendix case is certified separately by the unboundedCompression endpoint.
- `TauCeti.DavisKahan1970.tanTheta_unbounded_ambient_paperUINorm_real_exact`
  - Real specialization with an unbounded ambient self-adjoint operator but bounded Ritz compression. Uniform transversality is derived from the form bounds and (3.5); the stronger Appendix case is certified separately by the real unboundedCompression endpoint.
- `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm`
  - Alternative bounded route assuming uniform transversality `‖sin Theta‖ < 1` instead of (3.5). This is a strictly stronger hypothesis than the source's standing condition and is registered as a specialization, not as the source-shaped form.
- `TauCeti.DavisKahan1970.remark3_2_bilateralShift_separates_dimensionHypotheses`
  - Machine-checked witness that (1.5) does not imply (3.5) in infinite dimension, so the omitted qualification is substantive. It is a vacuity/nonvacuity witness, not a counterexample to the counted result.

#### 6. The repository's accepted reading

The printed theorem is read under the paper's own global semantics: the Section 1 vacuity convention governs the existence of the displayed norms, and the standing (3.5) is in force where the theorem is actually proved. On that reading a Lean statement that carries a crossed-defect hypothesis corresponding to (3.5), and that concludes rather than assumes membership of the tangent operator in the norm's ideal, is a source-faithful formalization of semantics the paper already imposes. It is not a claim that the Section 2 display literally contains (3.5).

#### 7. The strongest competing literal reading

Read only the local Section 2 hypotheses and interpret the displayed norm of tan Theta as +infinity when tan Theta is unbounded. The nested infinite-dimensional half-space configuration then satisfies every printed hypothesis with a finite (indeed zero) perturbation, the directed conclusion holds with both sides zero, and the ambient conclusion fails. Under that reading the printed ambient clause would be false as transcribed and the (3.5)-qualified theorem would be its repair.

#### 8. Why this is not classified as a refutation

In that configuration tan Theta is not a bounded operator and the displayed unitarily invariant norm does not exist, so the witness exhibits a missing nonvacuity qualification rather than a finite-valued failure of the inequality. The paper declares such cases vacuous in advance. The literal reading would equally convict the Section 1 angle-doubling sentence and later developments that silently use the direct rotation. This is therefore deliberately not classified as refuted_as_transcribed; contrast DK-4.4-prop, where all objects exist, the compared quantities are finite, and the printed conclusion is false.

#### 9. Semantic conclusion recorded by the repository

S2-tan-theta is a true counted result whose exact formal representation requires nonlocal source semantics that the repository makes explicit rather than assumes silently. The interpretation is accepted. Mathematical coverage now also includes the Appendix's genuinely unbounded Ritz-compression scope over both complex and real scalars through `tanTheta_unboundedCompression_ambient_paperUINorm_exact` and its real sibling.

#### Independent interpretation checklist

- [ ] The printed statement really does omit the qualification the repository says it omits.
- [ ] The cited earlier/later source passages really say what the repository reports them as saying.
- [ ] The paper-wide existence/vacuity convention plausibly governs the displayed norm in this statement.
- [ ] The later standing assumption is genuinely in force where the source proves this result.
- [ ] The extra Lean hypothesis corresponds to the omitted source qualification and to nothing stronger.
- [ ] The competing literal reading is stated at its strongest, not as a straw man.
- [ ] The decision not to classify this result as refuted is justified by the source's own semantics.
- [ ] The distinction from the repository's canonical refutation is real, not a softening of it.

#### Interpretation question put to the independent reviewer

> Is the extra explicit Lean structure a faithful formalization of nonlocal semantics already imposed by the paper, or an unjustified strengthening of the printed result?

- **Interpretation verdict** (choose one): `PASS paper-faithful nonlocal interpretation` / `FAIL illicit strengthening` / `UNCERTAIN source interpretation`
- **Verdict:** _fill in_
- **If FAIL or UNCERTAIN, which specific source passage or Lean hypothesis is the problem:** _fill in_
- **Would you instead classify this printed result as false as transcribed? Why:** _fill in_

---

### Atoms inside the counted printed result

- `S2-sin-theta.ui-norm-scope` — **counted_result_scope** *(shared/cross-block scope)* — Every norm in the four headline theorem statements is an arbitrary unitary-invariant norm.
- `S2-tan-theta.ordered-gap-hypothesis` — **counted_result_hypothesis** — The tangent theorem assumes A0 below Lambda1 by delta.
- `S2-tan-theta.rayleigh-ritz-hypothesis` — **counted_result_hypothesis** — The tangent theorem assumes H0=0, equivalently the Rayleigh--Ritz block choice.
- `S2-tan-theta.directed-conclusion` — **counted_result_statement** — delta ||tan Theta0|| <= ||R||.
- `S2-tan-theta.ambient-conclusion` — **counted_result_statement** — delta ||tan Theta|| <= ||H||.
- `S2-unbounded-scope.infinite-dimensional-scope` — **counted_result_scope** *(shared/cross-block scope)* — All four main results apply in infinite as well as finite dimension.
- `S2-unbounded-scope.arbitrary-ui-scope` — **counted_result_scope** *(shared/cross-block scope)* — All four main results apply to arbitrary UI norms.
- `S2-unbounded-scope.unbounded-selfadjoint-scope` — **counted_result_scope** *(shared/cross-block scope)* — The results extend to unbounded self-adjoint A under the stated domain condition.
- `S2-unbounded-scope.bounded-residual-needed` — **counted_result_scope** *(shared/cross-block scope)* — Useful unbounded conclusions require the pertinent perturbation or residual to extend boundedly.
- `S2-unbounded-scope.half-infinite-gap-intervals` — **counted_result_scope** *(shared/cross-block scope)* — Gap intervals may be half-infinite and the remaining spectra unbounded.
- `DK-6-appendix.unbounded-tangent-extension` — **counted_result_scope** *(shared/cross-block scope)* — The Appendix states the tan theta theorem in the general ordered case A0 <= alpha and Lambda1 >= alpha + delta and explicitly allows both A0 and Lambda1 to be unbounded, while the residual used by the norm estimate remains bounded.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Assume
\[
 \spec(A_0)\subset[\beta,\alpha],
 \qquad
 \spec(\Lambda_1)\subset[\alpha+\delta,\infty),
 \qquad \delta>0,
\]
and impose the Rayleigh--Ritz/off-diagonal condition $H_0=0$ (equivalently $A_0=E_0^*(A+H)E_0$ in this setup).  Then for every unitary-invariant norm both conclusions hold:
\[
 \boxed{\delta\norm{\tan\Theta_0}\le\norm{R}},
 \qquad
 \boxed{\delta\norm{\tan\Theta}\le\norm{H}}.
\]
The first is directed and residual-based; the second uses the ambient angle and the full perturbation.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.tanTheta_headline_generic_directed`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/HeadlineGeneric.lean:73`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahanTheory.partIII_tanTheta_ritzResidual_uiNorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/PartIII.lean:119`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan.Section2.theorem6_3_perturbation_infiniteTrial`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section2TanThetaPerturbation.lean:175`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:1176`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:210`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent`

Source location candidates: `Challenge/DavisKahan1970/Conformance.lean:322`, `DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:1265`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_real_of_crossedDefectsEquivalent`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:691`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_unbounded_ambient_paperUINorm_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanThetaUnboundedAmbient.lean:459`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_unbounded_ambient_paperUINorm_real_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanThetaUnboundedAmbientReal.lean:212`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_unboundedCompression_ambient_paperUINorm_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanThetaUnboundedAmbient.lean:427`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_unboundedCompression_ambient_paperUINorm_real_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanThetaUnboundedAmbientReal.lean:346`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 3. S2-sin-two-theta — Double-angle sine theorem

- **Counted result kind:** `unnumbered_theorem`
- **Exact source anchor:** Section 2, sin 2 theta theorem
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `7da711fdbd912b64b5aa6f2efc5c4255bcbe796831a18b99c92712024b81c70b`

### Atoms inside the counted printed result

- `S2-sin-theta.ui-norm-scope` — **counted_result_scope** *(shared/cross-block scope)* — Every norm in the four headline theorem statements is an arbitrary unitary-invariant norm.
- `S2-sin-two-theta.gap-hypothesis` — **counted_result_hypothesis** — The double-sine theorem separates Lambda0 from Lambda1 by an interval/exterior gap.
- `S2-sin-two-theta.directed-conclusion` — **counted_result_statement** — delta ||sin(2 Theta0)|| <= 2||R||.
- `S2-sin-two-theta.ambient-conclusion` — **counted_result_statement** — delta ||sin(2 Theta)|| <= 2||H||.
- `S2-unbounded-scope.infinite-dimensional-scope` — **counted_result_scope** *(shared/cross-block scope)* — All four main results apply in infinite as well as finite dimension.
- `S2-unbounded-scope.arbitrary-ui-scope` — **counted_result_scope** *(shared/cross-block scope)* — All four main results apply to arbitrary UI norms.
- `S2-unbounded-scope.unbounded-selfadjoint-scope` — **counted_result_scope** *(shared/cross-block scope)* — The results extend to unbounded self-adjoint A under the stated domain condition.
- `S2-unbounded-scope.bounded-residual-needed` — **counted_result_scope** *(shared/cross-block scope)* — Useful unbounded conclusions require the pertinent perturbation or residual to extend boundedly.
- `S2-unbounded-scope.half-infinite-gap-intervals` — **counted_result_scope** *(shared/cross-block scope)* — Gap intervals may be half-infinite and the remaining spectra unbounded.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Assume that for some $[\beta,\alpha]$ and $\delta>0$,
\[
 \spec(\Lambda_0)\subset[\beta,\alpha],
 \qquad
 \spec(\Lambda_1)\cap(\beta-\delta,\alpha+\delta)=\varnothing.
\]
Then for every unitary-invariant norm,
\[
 \boxed{\delta\norm{\sin(2\Theta_0)}\le2\norm{R}},
 \qquad
 \boxed{\delta\norm{\sin(2\Theta)}\le2\norm{H}}.
\]
Again the source distinguishes the directed residual statement from the ambient perturbation statement.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.sinTwoTheta_headline_generic_directed`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/HeadlineGeneric.lean:111`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm`

Source location candidates: `Challenge/DavisKahan1970/Conformance.lean:402`, `DavisKahan/Sources/DavisKahan1970/SinTwoThetaWholeSpace.lean:606`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:252`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:166`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:254`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:344`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:404`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.sinTwoTheta_unbounded_directedResidual_paperUINorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SinTwoThetaUnboundedDirectedResidual.lean:207`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.sinTwoTheta_unbounded_directedResidual_paperUINorm_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SinTwoThetaUnboundedDirectedResidualReal.lean:201`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.sinTwoTheta_unbounded_directedResidual_paperUINorm_real_of_intervalExterior`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SinTwoThetaUnboundedDirectedResidualReal.lean:245`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.sinTwoTheta_addBounded_paperUINorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:603`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 4. S2-tan-two-theta — Double-angle tangent theorem

- **Counted result kind:** `unnumbered_theorem`
- **Exact source anchor:** Section 2, tan 2 theta theorem
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `5c5b96c1cc563a42d13b8b4e06989c19ff82ec8ed6958f3da78d67dc9b2b7830`

### Atoms inside the counted printed result

- `S2-sin-theta.ui-norm-scope` — **counted_result_scope** *(shared/cross-block scope)* — Every norm in the four headline theorem statements is an arbitrary unitary-invariant norm.
- `S2-tan-two-theta.ordered-gap-hypothesis` — **counted_result_hypothesis** — The double-tangent theorem assumes A0 below A1 by delta.
- `S2-tan-two-theta.strong-offdiagonal-hypothesis` — **counted_result_hypothesis** — The double-tangent theorem assumes H0=H1=0.
- `S2-tan-two-theta.no-extra-pole-hypothesis` — **counted_result_scope** — The printed theorem has no independent tan-pole exclusion or perturbed-block spectral-placement hypothesis.
- `S2-tan-two-theta.directed-conclusion` — **counted_result_statement** — delta ||tan(2 Theta0)|| <= 2||R||.
- `S2-tan-two-theta.ambient-conclusion` — **counted_result_statement** — delta ||tan(2 Theta)|| <= 2||H||.
- `S2-unbounded-scope.infinite-dimensional-scope` — **counted_result_scope** *(shared/cross-block scope)* — All four main results apply in infinite as well as finite dimension.
- `S2-unbounded-scope.arbitrary-ui-scope` — **counted_result_scope** *(shared/cross-block scope)* — All four main results apply to arbitrary UI norms.
- `S2-unbounded-scope.unbounded-selfadjoint-scope` — **counted_result_scope** *(shared/cross-block scope)* — The results extend to unbounded self-adjoint A under the stated domain condition.
- `S2-unbounded-scope.bounded-residual-needed` — **counted_result_scope** *(shared/cross-block scope)* — Useful unbounded conclusions require the pertinent perturbation or residual to extend boundedly.
- `S2-unbounded-scope.half-infinite-gap-intervals` — **counted_result_scope** *(shared/cross-block scope)* — Gap intervals may be half-infinite and the remaining spectra unbounded.

### Same-block material explicitly outside the counted result

- `S2-tan-two-theta.pole-exclusion-derived` — **proof_or_derivation_not_result** — Section 7 derives the needed nonvanishing cosine factors from the printed hypotheses.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Assume the ordered gap
\[
 \spec(A_0)\subset[\beta,\alpha],
 \qquad
 \spec(A_1)\subset[\alpha+\delta,\infty),
 \qquad \delta>0,
\]
and the strong off-diagonal hypothesis
\[
 H_0=H_1=0.
\]
No independent hypothesis excluding the poles of $\tan(2\Theta)$, and no spectral placement hypothesis on the perturbed $Q$-blocks $\Lambda_0,\Lambda_1$, is part of the printed theorem.  For every unitary-invariant norm the two conclusions are
\[
 \boxed{\delta\norm{\tan(2\Theta_0)}\le2\norm{R}},
 \qquad
 \boxed{\delta\norm{\tan(2\Theta)}\le2\norm{H}}.
\]
Section~7 derives the nonvanishing of the relevant $\cos(2\theta_j)$ factors from these hypotheses during the proof rather than assuming it.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.tanTwoTheta_headline_generic`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/HeadlineGeneric.lean:180`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_exact`

Source location candidates: `Challenge/DavisKahan1970/Conformance.lean:453`, `DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean:1160`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_real_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:362`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_exact`

Source location candidates: `Challenge/DavisKahan1970/Conformance.lean:543`, `DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean:1297`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:433`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_directedResidual_paperUINorm_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedExact.lean:77`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_directedResidual_paperUINorm_real_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedExactReal.lean:195`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_ambient_paperUINorm_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedAmbientExact.lean:258`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_ambient_paperUINorm_real_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedExactReal.lean:343`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 5. DK-3.1-prop — Acute direct rotation existence and uniqueness

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 3.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `ff945cb6247987becf0eec9e3c5fd945ba2df2d2b8756cea6df2c7ebd00213d4`

### Atoms inside the counted printed result

- `DK-3.1-prop.existence` — **counted_result_statement** — In the acute case a direct rotation exists.
- `DK-3.1-prop.uniqueness` — **counted_result_statement** — In the acute case the direct rotation is unique.
- `DK-3.1-prop.positive-diagonal-characterization` — **counted_result_statement** — Positivity of C0,C1 characterizes the direct rotation among unitary intertwiners in the acute case.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
In the acute case, a direct rotation exists and is unique.  Moreover positivity of the diagonal blocks, $C_0,C_1\ge0$, already characterizes it among unitaries carrying $P\Hsp$ onto $Q\Hsp$: the polar-decomposition relations force the off-diagonal condition $S_1=S_0^*$ because the relevant kernels vanish in the acute case.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.proposition3_1_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3AcuteDirectRotation.lean:170`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 6. DK-3.2-prop — Nonacute existence criterion

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 3.2
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `9005afb318f41b78326c808b678267b64c6019ba67fb9cde9103197e4b25d749`

### Atoms inside the counted printed result

- `DK-3.2-prop.existence-iff-crossing-dimensions` — **counted_result_statement** — Outside the acute case, direct rotation existence is equivalent to equality of the crossing dimensions.
- `DK-3.2-prop.nonuniqueness` — **counted_result_statement** — When it exists outside the acute case it need not be unique.
- `DK-3.2-prop.eq-3-5` — **counted_result_statement** — Exact mathematical content of source equation (3.5) as reconstructed in the distributable TeX.

### Same-block material explicitly outside the counted result

- `DK-3.2-prop.crossing-square-minus-one` — **proof_detail_not_in_printed_statement** — On the crossing subspaces U^2 x=-x.
  - Boundary rationale: This atom is established or used inside the proof of the neighboring named result, but is not part of that result's printed statement.
- `DK-3.2-prop.finite-crossing-automatic` — **post_result_scope_remark_not_in_printed_statement** — Under the assumed (1.5), condition (3.5) holds automatically whenever either dim P-space or dim P-perp-space is finite.
  - Boundary rationale: A scope remark attached to Proposition 3.2 rather than part of its printed statement. It records exactly when the crossed-defect condition is automatic, and therefore delimits the configurations in which the Section 2 ambient tangent reading is at issue at all.
- `DK-3.2-prop.bilateral-shift-counterexample` — **remark_or_example_not_result** — The bilateral-shift example on two-sided square-summable sequences satisfies (1.5) with nested P-space and Q-space, has crossing subspaces of dimensions 1 and 0, and therefore fails (3.5): the matching-dimension conditions do not imply the crossing-dimension condition in infinite dimension.
  - Boundary rationale: The bilateral-shift example demonstrates that the matching-dimension conditions (1.5) do not imply the crossed-dimension condition (3.5) in infinite dimension. It is a remark/example attached to Proposition 3.2 rather than a designated result. It is not a counterexample to any counted result; its role in this repository is to show that the qualification omitted from the printed Section 2 tangent statement is mathematically substantive.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Outside the acute case a direct rotation exists iff the two crossing subspaces have the same dimension:
\begin{equation}
 \dim(P\Hsp\cap Q^\perp\Hsp)
 =\dim(P^\perp\Hsp\cap Q\Hsp).
 \tag{3.5}
\end{equation}
When it exists it need not be unique.  On the two crossing subspaces a direct rotation satisfies $U^2x=-x$.

The source appends a remark comparing (3.5) with the earlier matching-dimension condition (1.5).  Since (1.5) is being assumed, (3.5) holds automatically whenever either $\dim P\Hsp$ or $\dim P^\perp\Hsp$ is finite.  In infinite dimensions it can fail: let $\Hsp$ be the two-sided square-summable sequences $(\ldots,a_{-1},a_0,a_1,\ldots)$, let $P\Hsp$ be those with $a_n=0$ for $n<0$, and let $Q\Hsp$ be those with $a_n=0$ for $n\le0$.  The bilateral shift $V(a_n)=(b_n)$ with $b_n=a_{n-1}$ is a unitary satisfying (1.4), so (1.5) holds; but $PQ^\perp$ is the projector onto the sequences vanishing off $n=0$ while $P^\perp Q=0$, so the two crossing subspaces of (3.5) have dimensions $1$ and $0$ and (3.5) fails.  Hence (1.5) does not imply (3.5), and by this proposition the shift pair admits no direct rotation at all.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.proposition3_2_exists_iff_crossedDefectsEquivalent`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition32.lean:68`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_2_not_unique`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition32.lean:102`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_2_exists_iff_crossedDefectsEquivalent_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition32.lean:253`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_2_not_unique_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition32.lean:277`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 7. DK-3.3-prop — Principal square-root characterization

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 3.3
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `dbc77fc4c71873dbd8c706d68f5bb4ea28064a4d930ccb58c91c2640ab7bf382`

### Atoms inside the counted printed result

- `DK-3.3-prop.principal-square-root` — **counted_result_statement** — Every direct rotation is the principal unitary square root of the product of the two reflections.
- `DK-3.3-prop.square-root-converse` — **counted_result_statement** — A principal square root is a direct rotation when it maps the two crossing subspaces appropriately.

### Same-block material explicitly outside the counted result

- `DK-3.3-prop.reflection-conjugacy` — **pre_result_setup_not_in_printed_statement** — With X=P-Pperp and Q_-=XQX, U^{-1}=XUX.
  - Boundary rationale: This atom appears immediately before the named result as setup, identity, or motivation; it is outside the printed theorem/proposition statement.
- `DK-3.3-prop.eq-3-6` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (3.6) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-3.3-prop.eq-3-7` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (3.7) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-3.3-prop.eq-3-8` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (3.8) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Assuming both the matching-dimension condition (1.5) and the crossing-dimension condition (3.5), write the direct rotation as
\begin{equation}
 U\sim\begin{pmatrix}C_0&-S_0^*\\S_0&C_1\end{pmatrix},
 \qquad C_j\ge0.
 \tag{3.6}
\end{equation}
The corresponding projector has the block representation
\begin{equation}
 Q=UPU^{-1}
 \sim
 \binom{C_0}{S_0}(C_0\ \ S_0^*)
 =\begin{pmatrix}
 C_0^2&C_0S_0^*\\
 S_0C_0&S_0S_0^*
 \end{pmatrix}.
 \tag{3.7}
\end{equation}
With the reflection $X=P-P^\perp$ and $Q_-=XQX$ one has $U^{-1}=XUX$.  In particular,
\begin{equation}
 U^2=(Q-Q^\perp)(P-P^\perp).
 \tag{3.8}
\end{equation}
Every direct rotation is therefore the principal unitary square root of $(Q-Q^\perp)(P-P^\perp)$, with spectrum in the closed right half-plane.  Conversely, a principal square root of that product is a direct rotation provided it sends $P\Hsp\cap Q^\perp\Hsp$ onto $P^\perp\Hsp\cap Q\Hsp$.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.proposition3_3_complex_forward_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3PrincipalSquareRoot.lean:117`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_3_complex_converse_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3PrincipalSquareRoot.lean:140`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_3_real_forward_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3PrincipalSquareRoot.lean:262`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_3_real_converse_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3PrincipalSquareRoot.lean:304`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 8. DK-3.4-prop — Square as a direct rotation

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 3.4
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `a4914037fecd9b2f6193105f137f3a59d160e47ca70747bb4a6c430477038990`

### Atoms inside the counted printed result

- `DK-3.4-prop.u-square-direct-rotation` — **counted_result_statement** — If C0^2>=1/2, then U^2 is the direct rotation from Q_- to Q.
- `S3-standing-scope.crossed-dimension-standing-assumption` — **counted_result_scope** *(shared/cross-block scope)* — Standing convention: (3.5) is assumed as well as (1.5) for the remainder of the paper, except where the contrary is explicitly stated, so a direct rotation always exists and the development uses its direct special case (3.6).

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Under the same direct-rotation setup, if
\[
 C_0^2\ge\tfrac12
\]
(equivalently, the relevant principal angles do not exceed $\pi/4$), then $U^2$ is itself the direct rotation carrying $Q_-\Hsp$ onto $Q\Hsp$.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.proposition3_4_source_full_complex`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition34.lean:136`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_4_source_full_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition34Real.lean:117`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_4_source_full`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition34Printed.lean:66`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_4_source_eq_directRotation`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition34Printed.lean:217`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 9. DK-3.1-thm — Classification of pairs of subspaces

- **Counted result kind:** `theorem`
- **Exact source anchor:** Theorem 3.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `b4aa9b881e659bd021c3575c5475079f172a9c5d0983d82303b2a1a5832b32d8`

### Atoms inside the counted printed result

- `DK-3.1-thm.complete-invariant` — **counted_result_statement** — Spectral multiplicity functions of Theta0,Theta1 completely classify the pair under the stated dimension hypotheses.
- `DK-3.1-thm.converse-angle-data` — **counted_result_statement** — Conversely the angle operators may be arbitrary positive contractions in [0,pi/2] with matching spectral multiplicities away from zero and the stated dimensions.

### Same-block material explicitly outside the counted result

- `DK-3.1-thm.angle-operator-partial-isometry` — **pre_result_setup_not_in_printed_statement** — For the direct rotation, Theta_j = arccos C_j, the two angle operators are isometric-equivalent apart from the dimensionalities of their null spaces, and the polar resolution S_0 = J_0 sin Theta_0 gives a partial isometry J_0 of the closed range of Theta_0 onto that of Theta_1 with J_0 Theta_0 = Theta_1 J_0.
  - Boundary rationale: Section 3 setup preceding the printed Theorem 3.1 statement rather than part of it. It is recorded because the Section 6 ambient tangent proof compares its two corners through exactly this J_0, which exists as described only in the direct-rotation setting fixed by the standing (3.5).
- `DK-3.1-thm.reconstruction` — **proof_detail_not_in_printed_statement** — The pair is reconstructed from the angle data and J0.
  - Boundary rationale: This atom is established or used inside the proof of the neighboring named result, but is not part of that result's printed statement.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Before the classification the source brings in the angle operators (1.16)--(1.17) for the direct rotation, under the standing conventions just fixed: $\Theta_j=\arccos C_j$.  Because the unitarity relations give $S_0^*S_0=1-C_0^2$ on $\mathcal X(E_0)$ and $S_0S_0^*=1-C_1^2$ on $\mathcal X(E_1)$, the two operators $\Theta_0$ and $\Theta_1$ are isometric-equivalent except perhaps for different dimensionalities of their null spaces.  The polar resolution of $S_0$ is $S_0=J_0\sin\Theta_0$, where $J_0$ carries $\overline{\operatorname{Ran}\Theta_0}$ isometrically onto $\overline{\operatorname{Ran}\Theta_1}$ and satisfies $J_0\Theta_0=\Theta_1J_0$; the skew block operator $J$ of (1.18) is built from $J_0$, is unitary on $\overline{\operatorname{Ran}\Theta}$ with $J^2=-1$ there, and is set to $0$ on $\operatorname{Null}\Theta$.

Assume
\[
 \dim P\Hsp=\dim Q\Hsp,
 \qquad
 \dim(P\Hsp\cap Q^\perp\Hsp)=\dim(P^\perp\Hsp\cap Q\Hsp).
\]
A complete invariant of the pair $(P\Hsp,Q\Hsp)$ under isometric equivalence is given by the spectral multiplicity functions of $\Theta_0$ and $\Theta_1$.  Conversely, the angle operators may be arbitrary Hermitian operators satisfying
\[
 0\le\Theta_j\le\pi/2,
\]
their domain dimensions sum to $\dim\Hsp$, and their spectral multiplicity functions agree except possibly at the eigenvalue/spectral point $0$.  The proof reconstructs the pair from these angle data and the corresponding partial isometry $J_0$.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.theorem3_1_spectralMultiplicity_classification`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Classification.lean:192`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.theorem3_1_realization`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Theorem31Realization.lean:79`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.theorem3_1_spectralMultiplicity_classification_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Classification.lean:234`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 10. DK-3.1-cor — Compact classification by angle eigenvalues

- **Counted result kind:** `corollary`
- **Exact source anchor:** Corollary 3.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `2661dd05c08e61c06c54ce50c66032413a3c958bb7cda1b28638548253e30d2c`

### Atoms inside the counted printed result

- `DK-3.1-cor.compact-complete-invariants` — **counted_result_statement** — If PQperpP is compact, the eigenvalues of Theta0,Theta1 counted with multiplicity are complete invariants.
- `DK-3.1-cor.allowed-angle-sequence` — **counted_result_statement** — Theta0 eigenvalues may be any decreasing sequence in [0,pi/2] tending to zero plus possible zero eigenspace.
- `DK-3.1-cor.theta1-match` — **counted_result_statement** — Theta1 has the same nonzero eigenvalues and may differ only in zero multiplicity.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Under the hypotheses of Theorem~3.1, if $PQ^\perp P$ is compact, the complete invariants reduce to the eigenvalues of $\Theta_0,\Theta_1$, counted with multiplicity.  The eigenvalues of $\Theta_0$ may be any sequence
\[
 \pi/2\ge\theta_1\ge\theta_2\ge\cdots\to0,
\]
together with a possible eigenvalue $0$; $\Theta_1$ has the same nonzero eigenvalues and may differ only in the multiplicity of $0$.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.corollary3_1_compact_defectBlock_angleList_classification`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Corollary31.lean:159`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.corollary3_1_compact_classification_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Corollary31.lean:482`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.corollary3_1_realization`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Corollary31.lean:287`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 11. DK-3.5-prop — Angle commutation and eigenspace geometry

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 3.5
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `bdabc4530ed8ad8040dfe34d4a1071b2b52d3563d3e0e5bb9de9868287999a4e`

### Atoms inside the counted printed result

- `DK-3.5-prop.commutation` — **counted_result_statement** — Theta commutes with P,Q,J,U.
- `DK-3.5-prop.eigenvector-rotation-angle` — **counted_result_statement** — If Theta x=theta x then angle(x,Ux)=theta.
- `DK-3.5-prop.acute-maximal-characterization` — **counted_result_statement** — In the acute case each theta-eigenspace is the unique maximal P/Q-reducing subspace with the stated constant-angle properties.

### Same-block material explicitly outside the counted result

- `DK-3.5-prop.direct-rotation-exponential` — **pre_result_setup_not_in_printed_statement** — U=exp(J Theta).
  - Boundary rationale: This atom appears immediately before the named result as setup, identity, or motivation; it is outside the printed theorem/proposition statement.
- `DK-3.5-prop.cos-square-projector` — **pre_result_setup_not_in_printed_statement** — cos^2 Theta=PQP+Pperp Qperp Pperp.
  - Boundary rationale: This atom appears immediately before the named result as setup, identity, or motivation; it is outside the printed theorem/proposition statement.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
The angle operator $\Theta$ commutes with $P,Q,J,$ and $U$, and the direct rotation has $U=e^{J\Theta}$.  The source also records
\[
 \cos^2\Theta=PQP+P^\perp Q^\perp P^\perp.
\]
If $\Theta x=\theta x$, then
\[
 \angle(x,Ux)=\theta.
\]
In the acute case the $\theta$-eigenspace of $\Theta$ is the unique maximal subspace which reduces both $P$ and $Q$ and on which every nonzero $x\in P\Hsp$ has angle $\theta$ from $Qx$, while every nonzero $x\in P^\perp\Hsp$ has angle $\theta$ from $Q^\perp x$.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.proposition3_5_commutations`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:270`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_5_eigenvector_angle`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:305`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_5_angleEigenspace_eq_fixedCosineSubspace`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:323`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_5_angleEigenspace_uniqueMaximal`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:334`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_5_commutations_acute`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:284`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_5_eigenvector_angle_acute`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:315`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan.Proposition35.vectorAngle_nonacuteDirectRotation_eq_of_angleOperator_apply`

Source location candidates: `DavisKahan/Geometry/Angle/Proposition35Nonacute.lean:283`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 12. DK-3.2-cor — Reversal symmetry

- **Counted result kind:** `corollary`
- **Exact source anchor:** Corollary 3.2
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `6ef3d66483655d6bf428a2422d4d26494455fe9cba09939d61a2092809e68a9d`

### Atoms inside the counted printed result

- `DK-3.2-cor.swap-invariance` — **counted_result_statement** — Swapping P and Q leaves Theta unchanged and sends J to -J.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Interchanging the roles of $P$ and $Q$ leaves the angle operator $\Theta$ unchanged and replaces $J$ by $-J$.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.corollary3_2_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:213`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.corollary3_2_paperQuarterTurn_symm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:182`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.corollary3_2_nonacute_directRotation_resolution`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:163`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.complex_directRotation_reversal`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:131`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.real_directRotation_reversal`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:246`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.corollary3_2_reversal_source_form`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Corollary32.lean:39`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 13. DK-4.1-prop — Pointwise and singular-value extremality of the direct rotation

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 4.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `2b3c6a4dc471284a2f9e4f7e4f091d30fd00d0c04ef03648ee469d6e9e110cb3`

### Atoms inside the counted printed result

- `DK-4.1-prop.orthonormal-angle-lower-bounds` — **counted_result_statement** — For every such V there are orthonormal v_k in P with angle(v_k,Vv_k)>=theta_k.
- `DK-4.1-prop.singular-value-minimality` — **counted_result_statement** — Each singular value of (1-V)|P is minimized at V=U with value 2 sin(theta_k/2).

### Same-block material explicitly outside the counted result

- `DK-4.1-prop.vz-factorization` — **section_setup_not_result** — Every unitary V carrying P to Q is written V=UZ with Z block diagonal in the Section 4 setup.
  - Boundary rationale: This atom is section-level setup used to formulate or prove later named results; it is not itself inside a counted result statement.
- `DK-4.1-prop.closest-q-vector-proof-step` — **proof_or_derivation_not_result** — The pointwise comparison uses Qx/||Qx|| as the closest unit vector in Q-space.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-4.1-prop.eq-4-1` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (4.1) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-4.1-prop.eq-4-2` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (4.2) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
This section is logically independent of the later perturbation proofs.  Under the compact/classification setup, every unitary carrying $P\Hsp$ onto $Q\Hsp$ is written $V=UZ$ with $Z$ block diagonal relative to $P\oplus P^\perp$, and the principal angles are ordered $\theta_1\ge\theta_2\ge\cdots$.

For any such unitary $V$, there are orthonormal vectors $v_k\in P\Hsp$ such that
\[
 \angle(v_k,Vv_k)\ge\theta_k\qquad\text{for every }k.
\]
Equivalently, if $\lambda_1\ge\lambda_2\ge\cdots$ are the singular values of $(1-V)|_{P\Hsp}$, then each $\lambda_k$ is minimized by the direct rotation $V=U$, with minimum
\[
 \lambda_k=2\sin(\theta_k/2).
\]
The singular values admit the minimax description
\begin{equation}
 \lambda_k
 =\inf_{\substack{\mathcal Y\subset P\Hsp\\\dim\mathcal Y=k-1}}
   \ \sup_{\substack{x\in P\Hsp\ominus\mathcal Y\\\norm{x}=1}}
   \norm{(1-V)x},
 \tag{4.1}
\end{equation}
and the proof selects a corresponding unit vector $x$ for which
\begin{equation}
 \angle(x,Vx)\ge\theta_k=\angle(u_k,Uu_k).
 \tag{4.2}
\end{equation}
The latter follows by comparing $Vx$ with the closest unit vector in $Q\Hsp$ and using the block formula (3.7).
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4.lean:311`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4Real.lean:1258`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_directRotationValues`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4.lean:243`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_directRotationValues_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4Real.lean:1180`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 14. DK-4.1-cor — UI-norm minimality of direct rotation displacement

- **Counted result kind:** `corollary`
- **Exact source anchor:** Corollary 4.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `73cd6caf9a976a811e4836d656d566a66b0f57c7504ff38365d6891b3d75b9ba`

### Atoms inside the counted printed result

- `DK-4.1-cor.ui-minimality-on-p` — **counted_result_statement** — For every UI norm, ||(1-V)P|| is minimized at V=U.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
For every unitary-invariant norm,
\[
 \norm{(1-V)P}
\]
is minimized among unitaries carrying $P\Hsp$ onto $Q\Hsp$ by the direct rotation $V=U$.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Corollary4_1_compact_nonacute`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4.lean:342`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Corollary4_1_compact_nonacute_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4Real.lean:1285`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Corollary4_1_infiniteDimensional_nonacute`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4.lean:373`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 15. DK-4.2-prop — Basis-angle square-sum extremality

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 4.2
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `a1d36230f960f5b48427a6c4fce26c28327cc9fdff714575e4261c76ae92c4f4`

### Atoms inside the counted printed result

- `DK-4.2-prop.basis-sine-square-lower-bound` — **counted_result_statement** — For every orthonormal basis of P, sum sin^2 angle(v_k,Vv_k) >= sum sin^2 theta_k, including infinite RHS.

### Same-block material explicitly outside the counted result

- `DK-4.2-prop.trace-identification` — **proof_or_derivation_not_result** — The lower bound is identified with tr(S0* S0).
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
For every unitary $V$ carrying $P\Hsp$ onto $Q\Hsp$ and every orthonormal basis $\{v_k\}$ of $P\Hsp$,
\[
 \sum_{k=1}^{\infty}\sin^2\angle(v_k,Vv_k)
 \ge
 \sum_{k=1}^{\infty}\sin^2\theta_k,
\]
with the inequality also valid when the right-hand side is infinite.  The proof identifies the lower bound with $\operatorname{tr}(S_0^*S_0)$.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Proposition4_2_infiniteDimensional`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4.lean:418`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tsum_displacementAngleSineSqR_ge_tsum_sq_sin_principalAngleSequence`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4Real.lean:787`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 16. DK-4.3-prop — Squared displacement UI-norm minimality

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 4.3
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `efb61fbf15adb18ac47572bb82096f44ac2bd356072eaa15cd006cec8cc14dac`

### Atoms inside the counted printed result

- `DK-4.3-prop.squared-displacement-global-minimum` — **counted_result_statement** — ||(1-V*)(1-V)|| is minimized by U for every UI norm.

### Same-block material explicitly outside the counted result

- `DK-4.3-prop.plane-parameterization` — **proof_detail_not_in_printed_statement** — On each principal two-plane V has the displayed a_j,b_j parameterization.
  - Boundary rationale: This atom is established or used inside the proof of the neighboring named result, but is not part of that result's printed statement.
- `DK-4.3-prop.operator-norm-displacement-minimum` — **post_result_consequence_not_in_printed_statement** — The operator norm of 1-V is minimized by U.
  - Boundary rationale: This atom is an immediate consequence or interpretation stated after the named result; it is outside the printed result statement and is not counted separately.
- `DK-4.3-prop.hilbert-schmidt-displacement-minimum` — **post_result_consequence_not_in_printed_statement** — The Hilbert--Schmidt norm of 1-V is minimized by U.
  - Boundary rationale: This atom is an immediate consequence or interpretation stated after the named result; it is outside the printed result statement and is not counted separately.
- `DK-4.3-prop.arbitrary-ui-displacement-warning` — **post_result_consequence_not_in_printed_statement** — Arbitrary UI norms of 1-V need not be minimized by U.
  - Boundary rationale: This atom is an immediate consequence or interpretation stated after the named result; it is outside the printed result statement and is not counted separately.
- `DK-4.3-prop.eq-4-3` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (4.3) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-4.3-prop.eq-4-4` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (4.4) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-4.3-prop.eq-4-5` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (4.5) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-4.3-prop.eq-4-6` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (4.6) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
The source next studies the full operator $1-V$.  For the two-dimensional reducing planes $\Omega_k\Hsp=[u_k,Ju_k]$, its Ky Fan comparisons specialize to
\begin{equation}
\begin{aligned}
 \norm{K}_{\nu}&\ge\sum_{k=1}^{\nu/2}\norm{K\Omega_k}_2,
 &&\nu\text{ even},\\
 \norm{K}_{\nu}&\ge\sum_{k=1}^{\lfloor\nu/2\rfloor}\norm{K\Omega_k}_2
 +\norm{K\Omega_{(\nu+1)/2}}_1,
 &&\nu\text{ odd},
\end{aligned}
\tag{4.3}
\end{equation}
and, after compressing on both sides,
\begin{equation}
\begin{aligned}
 \norm{K}_{\nu}&\ge\sum_{k=1}^{\nu/2}\norm{\Omega_kK\Omega_k}_2,
 &&\nu\text{ even},\\
 \norm{K}_{\nu}&\ge\sum_{k=1}^{\lfloor\nu/2\rfloor}\norm{\Omega_kK\Omega_k}_2
 +\norm{\Omega_{(\nu+1)/2}K\Omega_{(\nu+1)/2}}_1,
 &&\nu\text{ odd}.
\end{aligned}
\tag{4.4}
\end{equation}
For one such plane write
\[
 Vu=a_0Uu+b_0w,
 \qquad
 VJu=a_1UJu+b_1x,
 \qquad |a_j|^2+|b_j|^2=1,
\]
with $w,x$ orthogonal to that plane in the appropriate $Q$ and $Q^\perp$ subspaces.  If $\mu_1\ge\mu_2$ are the singular values of $(1-V)\Omega$, and
\[
 a_0+a_1=2c+2ie,
 \qquad
 a_0-a_1=2d-2if,
\]
then
\begin{equation}
\begin{aligned}
 1-\mu_1^2/2&=c\cos\theta-\sqrt{d^2+e^2\sin^2\theta},\\
 1-\mu_2^2/2&=c\cos\theta+\sqrt{d^2+e^2\sin^2\theta},
\end{aligned}
\tag{4.5}
\end{equation}
while unitarity implies
\begin{equation}
 (c+d)^2+(e-f)^2\le1,
 \qquad
 (c-d)^2+(e+f)^2\le1.
 \tag{4.6}
\end{equation}
These formulas show term by term that the squared displacement has the source's global extremal property:
\[
 \boxed{\norm{(1-V^*)(1-V)}\ \text{is minimized when }V=U}
\]
for every unitary-invariant norm.  They also imply minimality of the operator norm and Hilbert--Schmidt norm of $1-V$, but the source warns that arbitrary unitary-invariant norms of $1-V$ need not be minimized by the direct rotation.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Proposition4_3_compact_nonacute_idealGauge`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4.lean:509`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Proposition4_3_compact_nonacute_real_idealGauge`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4Real.lean:1300`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 17. DK-4.4-prop — Full-displacement counterexamples and Proposition 4.4 as printed

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 4.4
- **Result disposition:** `refuted_as_transcribed`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `refuted_as_transcribed`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `1896dfda86994261bd007a6aeaf1fcd46b1b47e60a197caa7313cc5025ac1194`

### Atoms inside the counted printed result

- `DK-4.4-prop.printed-proposition4-4` — **counted_result_statement** — The paper asserts that in real space with Theta<=pi/3, U minimizes ||1-V|| for every UI norm.

### Same-block material explicitly outside the counted result

- `DK-4.4-prop.example4-1-real-reflection` — **remark_or_example_not_result** — Example 4.1 gives a real reflection with singular values 2,0 versus two equal direct-rotation singular values and defeats the Ky Fan 2 norm for theta>pi/3.
  - Boundary rationale: This atom belongs to a remark, example, or counterexample outside a counted result statement. It is retained for fidelity but is not a separate result obligation.
- `DK-4.4-prop.example4-2-complex-phase` — **remark_or_example_not_result** — Example 4.2 uses V=e^{i delta}U and shows the full-displacement UI minimum can fail in complex space.
  - Boundary rationale: This atom belongs to a remark, example, or counterexample outside a counted result statement. It is retained for fidelity but is not a separate result obligation.
- `DK-4.4-prop.printed-sharp-threshold` — **sharpness_commentary_not_designated_result** — The paper asserts the pi/3 threshold is sharp in view of the examples.
  - Boundary rationale: This is sharpness/equality commentary outside a designated result statement. It remains visible for fidelity but does not create an additional result obligation.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
The source exhibits failures of unrestricted full-displacement minimality.  In a real two-plane, a competing reflection has singular values $2,0$, whereas the direct rotation has both singular values $2\sin(\theta/2)$; the two-term Ky Fan comparison defeats the direct rotation once $\theta>\pi/3$.  In complex space, the competitors $V=e^{i\delta}U$ have singular values
\[
 2\sin\frac{\theta+\delta}{2},\qquad
 2\sin\frac{\theta-\delta}{2},
\]
and their sum is $4\sin(\theta/2)\cos(\delta/2)$, so the direct rotation is not generally minimizing.

After these examples the paper prints Proposition~4.4: if $\Hsp$ is real, $V$ is a unitary carrying $P\Hsp$ onto $Q\Hsp$, and
\[
 \Theta\le\pi/3,
\]
then $\norm{1-V}$ is asserted to be minimized by $V=U$ for every unitary-invariant norm.  The paper states the $\pi/3$ threshold is sharp in view of the examples.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahanTheory.DavisKahanProposition4_4_Finite`

Source location candidates: `DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean:838`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahanTheory.not_davisKahanProposition4_4_Finite`

Source location candidates: `DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean:862`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahanTheory.shortRotation_fullDisplacement_refuted`

Source location candidates: `DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean:809`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### False-source repair disposition

- **Repair status:** `proved`
- **Repair declarations:** `TauCeti.DavisKahanTheory.directRotation_fullDisplacement_qnorm`
- **Repair notes:** The printed real-space every-UI-norm full-displacement minimization claim is refuted exactly. The natural surviving Q-norm minimization theorem is proved by directRotation_fullDisplacement_qnorm.

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 18. DK-5.1-thm — Banach-space Sylvester lower bound

- **Counted result kind:** `theorem`
- **Exact source anchor:** Theorem 5.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `38590318e770b1eddea8bb6e6a45126b57c9652588f5e1c6991078f3dd8a6c4a`

### Atoms inside the counted printed result

- `DK-5.1-thm.banach-hypotheses` — **counted_result_hypothesis** — Banach-space theorem with ||B||<=alpha and ||A^{-1}||<=(alpha+delta)^{-1}, compatible cross norm.
- `DK-5.1-thm.sylvester-lower-bound` — **counted_result_statement** — AX-XB=C implies ||C||>=delta||X||.

### Same-block material explicitly outside the counted result

- `DK-5.1-thm.roles-interchange` — **post_result_scope_remark_not_in_printed_statement** — A and B roles/hypotheses may be interchanged.
  - Boundary rationale: This atom is a scope/extension remark stated after the named result, not part of the printed result environment; it is retained for fidelity without enlarging the result denominator.
- `DK-5.1-thm.one-sided-unbounded-extension` — **post_result_scope_remark_not_in_printed_statement** — The proof covers densely-defined unbounded A with bounded inverse hypothesis while B,X remain bounded.
  - Boundary rationale: This atom is a scope/extension remark stated after the named result, not part of the printed result environment; it is retained for fidelity without enlarging the result denominator.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Let $\mathcal X,\mathcal Y$ be Banach spaces.  Let $B$ be an operator on $\mathcal X$ and $A$ an operator on $\mathcal Y$ satisfying, in their bound norms,
\[
 \norm{B}\le\alpha,
 \qquad
 \norm{A^{-1}}\le(\alpha+\delta)^{-1},
 \qquad \alpha\ge0,\ \delta>0.
\]
For maps $\mathcal X\to\mathcal Y$, use any norm compatible with those bound norms.  If
\[
 AX-XB=C,
\]
then
\[
 \boxed{\norm{C}\ge\delta\norm{X}.}
\]
The roles and hypotheses of $A$ and $B$ may be interchanged.  The same proof also covers densely-defined unbounded $A$ provided the inverse hypothesis is meaningful/bounded while $B$ and $X$ remain bounded; the source then proceeds to a separate result allowing unbounded behavior on both sides in the Hilbert-space setting.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_uiNorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:265`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:268`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 19. DK-5.2-thm — Semibounded self-adjoint Sylvester theorem

- **Counted result kind:** `theorem`
- **Exact source anchor:** Theorem 5.2
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `2078bb97672c50ca247554b198c575e381bd776725924f1333057a2a10fc3d8c`

### Atoms inside the counted printed result

- `DK-5.2-thm.hilbert-unbounded-hypotheses` — **counted_result_hypothesis** — Theorem 5.2 gives the Hilbert-space unbounded Sylvester setup with separated spectra and domain/core hypotheses.
- `DK-5.2-thm.hilbert-unbounded-conclusion` — **counted_result_statement** — The corresponding delta||X|| lower bound holds in the stated UI/ideal norm scope.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Let $\mathcal X,\mathcal Y$ be Hilbert spaces and let $A$ on $\mathcal Y$, $B$ on $\mathcal X$ be semibounded self-adjoint operators satisfying
\[
 A\ge\gamma+\delta>\gamma\ge B.
\]
If $X,C:\mathcal X\to\mathcal Y$ are bounded and
\[
 AX=XB+C,
\]
then for every unitary-invariant norm
\[
 \boxed{\norm{C}\ge\delta\norm{X}.}
\]
This is the source's main Sylvester tool for the unbounded self-adjoint passages.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Theorem5_2`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section5.lean:51`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan.ExactSinTheta.davisKahan1970_sylvester_real`

Source location candidates: `DavisKahan/Sylvester/RealUnbounded.lean:76`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 20. DK-5.1-lem — Strong-cutoff convergence of singular values

- **Counted result kind:** `lemma`
- **Exact source anchor:** Lemma 5.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `4154e65f1eb46629c33da85de5866a2751ce9b5e21d9fa3956d2d6d0e677ecbd`

### Atoms inside the counted printed result

- `DK-5.1-lem.strong-cutoff-convergence` — **counted_result_statement** — The spectral-cutoff approximants converge strongly in the manner stated and support the unbounded proof.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
If orthogonal projectors $\Omega(\tau)$ converge strongly to the identity and $\kappa_\nu,\kappa_\nu(\tau)$ are the $\nu$th singular values of $K$ and $K\Omega(\tau)$, respectively, then
\[
 \kappa_\nu(\tau)\longrightarrow\kappa_\nu.
\]
This cutoff lemma lets finite spectral truncations recover the Ky Fan data required in the unbounded arguments.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Lemma5_1`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section5.lean:35`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 21. DK-6.1-lem — Direct-sum UI-norm comparison and converse

- **Counted result kind:** `lemma`
- **Exact source anchor:** Lemma 6.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `3fcdb9152000100900fc421874565b2defe8ccb6cc2a8574154d146c509eb2d5`

### Atoms inside the counted printed result

- `DK-6.1-lem.ordered-sylvester-forward` — **counted_result_statement** — The ordered spectral separation implies the stated Sylvester/UI-norm lower bound.
- `DK-6.1-lem.ordered-sylvester-converse` — **counted_result_statement** — The source includes the converse characterization used in the single-angle proof.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Let $\Omega,\Upsilon$ be orthogonal projectors.  If, for every unitary-invariant norm,
\[
 \norm{\Omega K\Upsilon}\le\norm{\Omega L\Upsilon},
 \qquad
 \norm{\Omega^\perp K\Upsilon^\perp}\le\norm{\Omega^\perp L\Upsilon^\perp},
\]
then
\[
 \norm{\Omega K\Upsilon+\Omega^\perp K\Upsilon^\perp}
 \le
 \norm{\Omega L\Upsilon+\Omega^\perp L\Upsilon^\perp}
\]
for every unitary-invariant norm.  The converse holds when the two diagonal blocks of $K$ are equisingular and the two diagonal blocks of $L$ are equisingular.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.lemma6_1`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:77`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.lemma6_1_converse`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:78`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 22. DK-6.2-lem — Reflection-pinch contraction

- **Counted result kind:** `lemma`
- **Exact source anchor:** Lemma 6.2
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `fefd468fd43df7f2d9ecb643c21a78aa0f8471b3b3909472925d347e6aa26f63`

### Atoms inside the counted printed result

- `DK-6.2-lem.pinching-contraction` — **counted_result_statement** — The reflection/pinching operation contracts every unitary-invariant norm in the stated setup.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
For orthogonal projectors $\Omega,\Upsilon$ and every unitary-invariant norm,
\[
 \boxed{\norm{\Omega K\Upsilon+\Omega^\perp K\Upsilon^\perp}\le\norm{K}.}
\]
The proof is the reflection/pinching contraction obtained by averaging $K$ with suitable unitary reflections.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.lemma6_2`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:79`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 23. DK-6.1-prop — Sine proof, ambient limitation, and symmetric sine theorem

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 6.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `ec802eefcfa341b4268ff3fd35bdb06d38211ec9cf5c72138d53e1ffdf5d11ce`

### Atoms inside the counted printed result

- `DK-6.1-prop.symmetric-sine-theorem` — **counted_result_statement** — Proposition 6.1 gives the symmetric sine-theta conclusion under two-sided spectral placement.

### Same-block material explicitly outside the counted result

- `DK-6.1-prop.sine-proof-residual-identity` — **proof_detail_not_in_printed_statement** — The symmetric sine proof rewrites the relevant off-diagonal block as the Sylvester residual identity.
  - Boundary rationale: This atom is established or used inside the proof of the neighboring named result, but is not part of that result's printed statement.
- `DK-6.1-prop.source-counterexample-need-two-sided` — **remark_or_example_not_result** — The source exhibits the failure of the ambient/symmetric conclusion when the needed two-sided placement is dropped.
  - Boundary rationale: This atom belongs to a remark, example, or counterexample outside a counted result statement. It is retained for fidelity but is not a separate result obligation.
- `DK-6.1-prop.eq-6-1` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (6.1) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Projecting the residual relation onto the complementary exact subspace gives the Sylvester equation
\[
 R^*F_1=E_0^*F_1\Lambda_1-A_0E_0^*F_1.
\]
Under the interval/exterior gap of the $\sin\theta$ theorem, Theorem~5.1/5.2 yields
\begin{equation}
 \norm{R^*F_1}\ge\delta\norm{E_0^*F_1},
 \tag{6.1}
\end{equation}
whose singular values are the directed sines, proving $\delta\norm{\sin\Theta_0}\le\norm{R}$.

The source explicitly warns that the same one-sided hypotheses do \emph{not} imply $\delta\norm{\sin\Theta}\le\norm{H}$ for every unitary-invariant norm.  A $2\times2$ example has $\delta=2$, $\theta=\pi/4$, and
\[
 \delta\norm{\sin\Theta}_{\mathrm{sq}}=2>\sqrt3=\norm{H}_{\mathrm{sq}}.
\]

The symmetric replacement is Proposition~6.1: if the $A_0$--$\Lambda_1$ spectra satisfy the sine-theorem separation of width $\delta$ and the $A_1$--$\Lambda_0$ spectra satisfy the analogous separation, then for every unitary-invariant norm
\[
 \boxed{\delta\norm{\sin\Theta}\le\norm{H}.}
\]
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Proposition6_1`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:115`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Proposition6_1_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:127`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 24. DK-6.1-thm — Generalized sine theorem

- **Counted result kind:** `theorem`
- **Exact source anchor:** Theorem 6.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `13e2036a72aaec0c5094f6014d3bfe1933167f1a43cf79f77716d5d7bf9726c7`

### Atoms inside the counted printed result

- `DK-6.1-thm.generalized-sine-hypotheses` — **counted_result_hypothesis** — The generalized sine theorem allows nonisometric E0 with E0*E0 >= epsilon^2 and the stated spectral separation.
- `DK-6.1-thm.generalized-sine-conclusion` — **counted_result_statement** — delta epsilon ||sin Theta0|| <= ||R||.
- `DK-6.1-thm.unequal-dimension-scope` — **counted_result_scope** — The generalized theorem allows unequal-dimensional comparison subspaces as stated.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Assume $A+H$ has the reducing decomposition (1.3) with exhaustive isometries $F_0,F_1$, and define $R$ by (1.8).  The trial map $E_0$ need not be isometric; assume only
\[
 E_0^*E_0\ge\varepsilon^2 I\qquad(\varepsilon>0).
\]
Let $P,Q$ be the projectors onto $\operatorname{Ran}(E_0)$ and $\operatorname{Ran}(F_0)$, with no equality-of-dimension hypothesis, and let $\sin\Theta_0$ be any operator having the same singular values as $PQ^\perp$.

If one of $A_0,\Lambda_1$ has spectrum in $[\beta,\alpha]$ and the other has spectrum outside $(\beta-\delta,\alpha+\delta)$, then for every unitary-invariant norm
\[
 \boxed{\delta\varepsilon\norm{\sin\Theta_0}\le\norm{R}.}
\]
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Theorem6_1`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:102`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Theorem6_1_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:105`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Theorem6_1_real_commonDomain`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:200`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Theorem6_1_real_commonCore`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:221`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 25. DK-6.2-thm — Pairwise-gap square-norm sine theorem

- **Counted result kind:** `theorem`
- **Exact source anchor:** Theorem 6.2
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `3d339a183924f39cbfd71c81f3745c69442b26a631b3a25921093e05277bb58d`

### Atoms inside the counted printed result

- `DK-6.2-thm.second-generalized-sine` — **counted_result_statement** — The second generalized sine theorem gives the Hilbert--Schmidt estimate under pairwise spectral separation.

### Same-block material explicitly outside the counted result

- `DK-6.2-thm.rank-corrected-operator-consequence` — **post_result_consequence_not_in_printed_statement** — The stated rank-corrected operator-norm consequence follows.
  - Boundary rationale: This atom is an immediate consequence or interpretation stated after the named result; it is outside the printed result statement and is not counted separately.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Under the same lower-frame and range assumptions as Theorem~6.1, replace the interval/exterior separation by only the pairwise distance condition
\[
 |\lambda-a|\ge\delta>0
 \quad\text{for every }\lambda\in\spec(\Lambda_1),\ a\in\spec(A_0).
\]
Then the guaranteed norm is the Hilbert--Schmidt norm:
\[
 \boxed{\delta\varepsilon\norm{\sin\Theta_0}_{\mathrm{sq}}
 \le\norm{R}_{\mathrm{sq}}.}
\]
Combining this with (5.2) also yields the rank-corrected operator-norm estimate
\[
 \delta\varepsilon\norm{\sin\Theta_0}_1
 \le\norm{R}_1\sqrt{\operatorname{rank}R}.
\]
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Theorem6_2`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:142`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Theorem6_2_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:146`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 26. DK-6.3-thm — Tangent proof machinery, Example 6.1, and generalized tangent theorem

- **Counted result kind:** `theorem`
- **Exact source anchor:** Theorem 6.3
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `3cb15263f92a74f7f5bcd986093f2a8113abc206243a8876510705b926d35919`

### Atoms inside the counted printed result

- `DK-6.3-thm.generalized-tangent-theorem` — **counted_result_statement** — Theorem 6.3 gives the generalized tangent residual bound with its exact source hypotheses.

### Same-block material explicitly outside the counted result

- `DK-6.3-thm.tangent-setup-identities` — **proof_or_derivation_not_result** — Equations (6.2)--(6.6) provide the block identities used in the generalized tangent proof.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6.3-thm.tangent-proof-temporary-boundedness` — **proof_or_derivation_not_result** — The Section 6 tangent proof temporarily supposes that all operators are bounded and that S_0 is compact, and defers the removal of both restrictions to the Appendix to Section 6.
  - Boundary rationale: A temporary proof-technical restriction inside the Section 6 argument, not a hypothesis of the printed Section 2 theorem. It is part of the inherited proof context under which the printed tangent statement is actually settled.
- `DK-6.3-thm.ambient-wholeSpace-assembly` — **proof_or_derivation_not_result** — The ambient conclusion is assembled from the directed one: tan Theta has the two-corner block form built from J_0, tan Theta_0 and tan Theta_1, the two corners have equal unitarily invariant norms through J_0, and Lemmas 6.1 and 6.2 then give delta ||tan Theta|| <= ||H||.
  - Boundary rationale: The proof of the counted ambient conclusion rather than an additional printed result. It is recorded separately because it is the exact place where the Section 2 statement inherits the direct-rotation geometry available only under the later standing conditions.
- `DK-6.3-thm.example6-1` — **remark_or_example_not_result** — Example 6.1 gives the explicit 2x2 counterexample showing one-sided placement is essential for the tangent conclusion.
  - Boundary rationale: This atom belongs to a remark, example, or counterexample outside a counted result statement. It is retained for fidelity but is not a separate result obligation.
- `DK-6.3-thm.eq-6-2` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (6.2) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6.3-thm.eq-6-3` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (6.3) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6.3-thm.eq-6-4` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (6.4) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6.3-thm.eq-6-5` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (6.5) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6.3-thm.eq-6-6` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (6.6) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Restore the Section~1--2 hypotheses and write the direct rotation as
\begin{equation}
 U\sim
 \begin{pmatrix}C_0&-S_0^*\\S_0&C_1\end{pmatrix}
 =
 \begin{pmatrix}
 \cos\Theta_0&-J_0^*\sin\Theta_1\\
 J_0\sin\Theta_0&\cos\Theta_1
 \end{pmatrix},
 \qquad J_0\Theta_0=\Theta_1J_0,
 \quad C_j\ge0.
 \tag{6.2}
\end{equation}
The two reducing representations are related by
\begin{equation}
 \begin{pmatrix}A_0+H_0&B^*\\B&A_1+H_1\end{pmatrix}
 \begin{pmatrix}C_0&-S_0^*\\S_0&C_1\end{pmatrix}
 =
 \begin{pmatrix}C_0&-S_0^*\\S_0&C_1\end{pmatrix}
 \begin{pmatrix}\Lambda_0&0\\0&\Lambda_1\end{pmatrix},
 \tag{6.3}
\end{equation}
so in particular
\begin{equation}
 (A_0+H_0)(-S_0^*)+B^*C_1=-S_0^*\Lambda_1.
 \tag{6.4}
\end{equation}
Under $A_0\le\alpha$, $\Lambda_1\ge\alpha+\delta$, and $H_0=0$, transposing (6.4) gives
\begin{equation}
 C_1B=S_0A_0-\Lambda_1S_0.
 \tag{6.5}
\end{equation}
Under $A_0\le\alpha$, $\Lambda_1\ge\alpha+\delta$, and $H_0=0$, singular vectors for $S_0$ give the scalar estimate
\begin{equation}
 \cos\theta_j\,|y_j^*Bx_j|\ge\delta\sin\theta_j,
 \tag{6.6}
\end{equation}
so the relevant cosines are positive and Ky Fan/Fan dominance gives the directed tangent conclusion $\delta\norm{\tan\Theta_0}\le\norm{R}$.  In this argument the source temporarily supposes that all the operators are bounded and that $S_0$ is compact, and states that the Appendix to Section~6 removes both restrictions.

The ambient conclusion of the $\tan\theta$ theorem is then assembled from the directed one through the direct-rotation geometry of (6.2).  The source observes that
\[
 \tan\Theta\sim
 \begin{pmatrix}
 0&-J_0^*\tan\Theta_1\\
 J_0\tan\Theta_0&0
 \end{pmatrix},
 \qquad
 \norm{J_0\tan\Theta_0}
 =\norm{J_0^*\tan\Theta_1}
 =\norm{\tan\Theta_0}
 \le\norm B/\delta,
\]
the two off-diagonal corners being compared through the same partial isometry $J_0$ of the direct rotation.  Lemmas~6.1 and~6.2 then give
\[
 \delta\norm{\tan\Theta}
 \le\norm{\begin{pmatrix}0&B^*\\B&0\end{pmatrix}}
 \le\norm{\begin{pmatrix}0&B^*\\B&H_1\end{pmatrix}}
 =\norm H,
\]
which is the ambient conclusion $\delta\norm{\tan\Theta}\le\norm H$.  The source then gives Example~6.1 showing the one-sided placement of $\Lambda_1$ is essential: a finite matrix example has $\delta=1$ and tangent quantity $1$ while the residual is only $1/\sqrt2$ if spectral mass is allowed on the wrong side.

The generalized theorem retains exact Rayleigh--Ritz trial data.  Assume $E_0,E_1,F_0,F_1$ are exhaustive isometries whose ranges reduce $A$ and $A+H$, respectively, but allow
\[
 \dim\mathcal X(E_0)<\dim\mathcal X(F_0).
\]
Set $A_0=E_0^*(A+H)E_0$, define $R$ by (1.8), and let the directed sine data have the singular values of $E_0^*F_1$.  If
\[
 \spec(A_0)\subset[\beta,\alpha],
 \qquad
 \spec(\Lambda_1)\subset[\alpha+\delta,\infty),
\]
then the corresponding directed tangent operator satisfies, for every unitary-invariant norm,
\[
 \boxed{\delta\norm{\tan\Theta_0}\le\norm{R}.}
\]
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists`

Source location candidates: `DavisKahan/TanTheta/Theorem63UnboundedInfiniteTrial.lean:640`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean:534`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_spectral`

Source location candidates: `Challenge/DavisKahan1970/Conformance.lean:299`, `DavisKahan/Sources/DavisKahan1970/Directed.lean:122`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real_spectral`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:492`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 27. DK-6.3-lem — Finite-rank near-maximizer leakage estimate

- **Counted result kind:** `lemma`
- **Exact source anchor:** Lemma 6.3
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `6709c9fbf240ea7fc10d68b73cd0c746c59536127a66d13108ba14d114d52a45`

### Atoms inside the counted printed result

- `DK-6.3-lem.approximation-number-leakage` — **counted_result_statement** — Lemma 6.3 controls the approximation/singular-number leakage used in the Appendix, including the stated finite and real forms.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Let $K$ have singular values $\kappa_1\ge\kappa_2\ge\cdots$, let $\Gamma,\Psi$ be rank-$\nu$ projectors with $K\Psi=\Gamma K\Psi$, and let the singular values of $K\Psi$ be $\mu_1\ge\cdots\ge\mu_\nu$.  If
\[
 \sum_{k=1}^{\nu}\mu_k^2
 >\sum_{k=1}^{\nu}\kappa_k^2-\eta^2,
\]
then the leakage outside $\Psi$ obeys
\[
 \boxed{\norm{\Gamma K\Psi^\perp}_1\le\eta.}
\]
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Section6Appendix.lemma6_3_approximationNumber_leakage`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakage.lean:352`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section6Appendix.lemma6_3_singularValue_leakage`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakage.lean:372`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section6Appendix.lemma6_3_approximationNumber_leakage_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakageReal.lean:114`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 28. DK-8.1-thm — Branch selection and spectral repulsion

- **Counted result kind:** `theorem`
- **Exact source anchor:** Theorem 8.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `ca616396d0bee7b303c7da3ad0904053b80ad6da1a13a172bbec402be84f7c57`

### Atoms inside the counted printed result

- `DK-8.1-thm.acute-iff-spectral-placement` — **counted_result_statement** — Theta<=pi/4 iff the chosen perturbed reducing blocks lie on the corresponding sides of the gap.
- `DK-8.1-thm.existence-correct-q` — **counted_result_statement** — A reducing spectral projector Q with the required placement exists and is unique in the stated sense.
- `DK-8.1-thm.part-i-compression` — **counted_result_statement** — The upper/lower block compression inequalities of part (i).
- `DK-8.1-thm.part-ii-eigenvalue` — **counted_result_statement** — The finite-dimensional eigenvalue displacement inequalities of part (ii), with natural infinite-dimensional extensions.
- `DK-8.1-thm.part-iii-gauge` — **counted_result_statement** — The symmetric-gauge majorization inequalities of part (iii).

### Same-block material explicitly outside the counted result

- `DK-8.1-thm.branch-problem` — **pre_result_motivation_not_result** — Small double-angle trigonometric quantities alone do not select angles near zero; the chosen reducing subspace matters.
  - Boundary rationale: This atom motivates the following counted result but is outside its printed statement.
- `DK-8.1-thm.exclude-pi-over-four` — **proof_or_derivation_not_result** — Equations (8.1)--(8.2) exclude theta=pi/4 and then theta>pi/4 under the selected placement.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-8.1-thm.spectral-repulsion-interpretation` — **post_result_interpretation_not_result** — Strong off-diagonal eigenvector rotation forces definite eigenvalue displacement as described.
  - Boundary rationale: This atom interprets a counted result after its statement/proof; it is not an additional result obligation.
- `DK-8.1-thm.eq-8-1` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (8.1) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-8.1-thm.eq-8-2` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (8.2) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Small $\sin2\Theta$ or $\tan2\Theta$ does not by itself force all principal angles near $0$: some may lie near $\pi/2$.  The reason is that the double-angle theorems initially impose no distinguished choice of the reducing subspace $Q\Hsp$ of $A+H$; even when $H=0$, a poorly matched reducing subspace can require rotations near $\pi/2$.  Section~8 identifies the spectrally corresponding acute branch.

Assume the hypotheses of the $\tan2\theta$ theorem.  Then
\[
 \Theta\le\pi/4
\]
if and only if the chosen reducing blocks of $A+H$ satisfy
\[
 \Lambda_1\ge\alpha+\delta,
 \qquad
 \Lambda_0\le\alpha.
\]
For fixed $A,P,H$ there exists a reducing projector $Q$ with these properties (take the spectral projector of $A+H$ on the appropriate side of $\alpha$).  For this $Q$:
\begin{enumerate}[label=(\roman*)]
\item the upper block obeys
\[
 A_1-\alpha\le C_1(\Lambda_1-\alpha)C_1,
\]
with the analogous lower-block inequality;
\item in finite dimensions, if $\lambda_k$ are the ordered eigenvalues of $\Lambda_1$ and $\alpha_k$ those of $A_1$,
\[
 \alpha_k-\alpha\le\norm{C_1}_1^2(\lambda_k-\alpha),
\]
with the analogous lower-block statement and natural infinite-dimensional extensions;
\item for every symmetric gauge function $\Phi$ in finite dimensions,
\[
 \Phi(\alpha_1-\alpha,\ldots,\alpha_n-\alpha)
 \le
 \Phi((\lambda_1-\alpha)\cos^2\theta_1,\ldots,
      (\lambda_n-\alpha)\cos^2\theta_n),
\]
again with the analogous lower-block relation.
\end{enumerate}
The branch proof uses the two representations
\begin{equation}
 x_0^*\Lambda_0x_0
 =x_0^*A_0x_0+\tan\theta\,x_0^*B^*y_1
 =\cot\theta\,y_1^*Bx_0+y_1^*A_1y_1
 \tag{8.1}
\end{equation}
and hence
\begin{equation}
 x_0^*B^*y_1(\tan\theta-\cot\theta)
 =y_1^*A_1y_1-x_0^*A_0x_0\ge\delta>0.
 \tag{8.2}
\end{equation}
These exclude $\theta=\pi/4$ and then $\theta>\pi/4$ under the chosen spectral placement.  The source interprets parts (ii)--(iii) as quantitative spectral repulsion: an off-diagonal perturbation that rotates all relevant eigenvectors strongly must also move eigenvalues by a definite amount.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81.lean:142`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_spectrumIn`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81.lean:387`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81Real.lean:78`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_spectrumIn_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81Real.lean:240`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/BranchRepulsion.lean:503`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/BranchRepulsion.lean:551`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/Theorem81ApproximationReal.lean:294`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/Theorem81ApproximationReal.lean:357`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/Theorem81Approximation.lean:217`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/Theorem81Approximation.lean:346`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/Theorem81ApproximationReal.lean:489`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/Theorem81ApproximationReal.lean:575`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.approximationNumber_eq_eigenvalues_of_isPositive`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/Theorem81AngleForms.lean:146`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/Theorem81AngleForms.lean:436`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/Theorem81AngleForms.lean:489`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/Theorem81AngleForms.lean:714`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/Theorem81AngleForms.lean:769`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 29. DK-8.2-thm — Smallness selects the acute branch

- **Counted result kind:** `theorem`
- **Exact source anchor:** Theorem 8.2
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Source alignment:** `locally_exact`
- **Printed statement locally self-contained:** `True`
- **Organizational source-block hash:** `8af6a38667dbf398e65e1b4460763ab627b559607ac519214c35402797c1b48e`

### Atoms inside the counted printed result

- `DK-8.2-thm.smallness-alternative` — **counted_result_hypothesis** — The theorem assumes either ||H||_1<delta/2 or ||R||_1<delta/2 plus the stated A0 interval.
- `DK-8.2-thm.double-angle-bound-retained` — **counted_result_statement** — The corresponding sin2 double-angle estimate remains valid.
- `DK-8.2-thm.acute-branch-conclusion` — **counted_result_statement** — Theta<pi/4.
- `S3-standing-scope.crossed-dimension-standing-assumption` — **counted_result_scope** *(shared/cross-block scope)* — Standing convention: (3.5) is assumed as well as (1.5) for the remainder of the paper, except where the contrary is explicitly stated, so a direct rotation always exists and the development uses its direct special case (3.6).

### Same-block material explicitly outside the counted result

- `DK-8.2-thm.homotopy-proof` — **proof_or_derivation_not_result** — The perturbation proof uses the continuous spectral-projector homotopy and the displayed arcsine bound.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-8.2-thm.residual-reduction` — **proof_or_derivation_not_result** — The residual form is reduced by changing the complementary perturbation block while preserving the residual/spectral data.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-8.2-thm.sin2-unequal-dimension-extension` — **post_result_scope_remark_not_in_printed_statement** — The source states a sin2 extension to unequal comparison dimensions.
  - Boundary rationale: This atom is a scope/extension remark stated after the named result, not part of the printed result environment; it is retained for fidelity without enlarging the result denominator.
- `DK-8.2-thm.no-tan2-unequal-dimension-extension-known` — **historical_knowledge_state** — No analogous tan2 extension was known.
  - Boundary rationale: This atom records the paper's historical knowledge state rather than a Davis--Kahan result established in the paper.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Add to the hypotheses of the $\sin2\theta$ theorem either
\[
 \norm{H}_1<\delta/2
 \quad\text{or}\quad
 \norm{R}_1<\delta/2,
\]
and assume
\[
 \spec(A_0)\subset[\beta-\delta/2,\alpha+\delta/2].
\]
Then the corresponding double-angle estimate remains valid,
\[
 \delta\norm{\sin2\Theta}\le2\norm H
 \quad\text{or}\quad
 \delta\norm{\sin2\Theta_0}\le2\norm R,
\]
and in addition the comparison is on the acute branch:
\[
 \boxed{\Theta<\pi/4.}
\]
For the perturbation form, the proof follows the homotopy $A(\sigma)=A+H-\sigma H$ and the continuously varying spectral projector $Q(\sigma)$.  If $\gamma=\norm H_1<\delta/2$, every ``close'' parameter satisfies
\[
 \theta(\sigma)
 \le\tfrac12\arcsin(2\sigma\gamma/\delta)
 \le\frac{\pi}{2}\frac{\sigma\gamma}{\delta}
 <\pi/4,
\]
which propagates closeness from $\sigma=0$ to $1$.  The residual case is reduced to this by changing $H_1$ without changing the relevant residual or spectral blocks and choosing the replacement with $\norm H_1=\norm R_1$.

The source closes Section~8 by stating that the $\sin2\theta$ theorem extends to $\dim\mathcal X(E_0)<\dim\mathcal X(F_0)$ analogously to Theorems~6.1 and~6.3, while no corresponding extension of the $\tan2\theta$ theorem was known.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_directed`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/PaperSurface.lean:123`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_paperUINorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/Theorem82Source.lean:430`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_source_paperUINorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/Theorem82Source.lean:506`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_directed_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/Theorem82SourceReal.lean:318`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_real_paperUINorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/Theorem82SourceReal.lean:552`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_source_real_paperUINorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/Theorem82SourceReal.lean:607`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_maximalAngle_lt_of_crossedDefects`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/Theorem82Source.lean:594`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_real_maximalAngle_lt_of_crossedDefects`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/Theorem82SourceReal.lean:379`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

# Appendix A — complete source-fidelity classification

Every source atom remains visible here even when it is outside the 29-result denominator. This table is the project's explicit limitation statement: an excluded item is not hidden; it has a reason code that the reviewer may challenge.

## Classification totals

- `background_theory_not_designated_result`: **2**
- `counted_result_hypothesis`: **10**
- `counted_result_scope`: **10**
- `counted_result_statement`: **49**
- `deferred_unproved_claim`: **2**
- `definition_not_result`: **9**
- `expository_commentary_not_result`: **3**
- `external_result_not_dk_result`: **3**
- `historical_knowledge_state`: **1**
- `introductory_background_not_designated_result`: **26**
- `open_question`: **5**
- `paper_wide_semantic_convention_not_result`: **1**
- `post_result_consequence_not_in_printed_statement`: **4**
- `post_result_interpretation_not_result`: **1**
- `post_result_scope_remark_not_in_printed_statement`: **4**
- `pre_result_motivation_not_result`: **1**
- `pre_result_setup_not_in_printed_statement`: **4**
- `proof_detail_not_in_printed_statement`: **4**
- `proof_or_derivation_not_result`: **67**
- `remark_or_example_not_result`: **6**
- `restatement_of_counted_result`: **6**
- `section10_motivation_not_result`: **3**
- `section9_worked_example_not_result`: **43**
- `section_setup_not_result`: **2**
- `sharpness_commentary_not_designated_result`: **6**

## All source atoms in paper order

| # | Atom | Parent block | Boundary classification | Counted result support | Source-fidelity summary |
|---:|---|---|---|---|---|
| 1 | `S1-block-residual.setup-hilbert-scope` | `S1-block-residual` | `introductory_background_not_designated_result` | — | Separable real or complex Hilbert space; bounded main setting with stated unbounded extension. |
| 2 | `S1-block-residual.norm-existence-vacuity-convention` | `S1-block-residual` | `paper_wide_semantic_convention_not_result` | — | Paper-wide convention: some of the paper's results are vacuous when certain norms occurring in them fail to exist, and the source will not repeat that qualification at the individual statements. |
| 3 | `S1-block-residual.reducing-projector-setup` | `S1-block-residual` | `introductory_background_not_designated_result` | — | P reduces A and E0,E1 are isometries onto the two reducing summands. |
| 4 | `S1-block-residual.q-reduces-perturbed` | `S1-block-residual` | `introductory_background_not_designated_result` | — | Q reduces A+H and F0,F1 give its reducing decomposition. |
| 5 | `S1-block-residual.no-spectral-projector-assumption` | `S1-block-residual` | `introductory_background_not_designated_result` | — | P and Q need not be spectral projectors and the diagonal spectral sets may overlap. |
| 6 | `S1-block-residual.unitary-intertwiner-dimension-criterion` | `S1-block-residual` | `introductory_background_not_designated_result` | — | A unitary carrying P-space to Q-space exists precisely with the two matching dimension conditions. |
| 7 | `S1-block-residual.within-subspace-coordinate-freedom` | `S1-block-residual` | `introductory_background_not_designated_result` | — | Changing the intertwining unitary changes only the within-subspace unitary coordinates W0,W1. |
| 8 | `S1-block-residual.residual-inherited-block` | `S1-block-residual` | `introductory_background_not_designated_result` | — | When A0 is inherited from A, R=H E0 and is the first block column of H. |
| 9 | `S1-block-residual.rayleigh-ritz-h0-zero` | `S1-block-residual` | `introductory_background_not_designated_result` | — | The Rayleigh--Ritz choice A0=E0*(A+H)E0 is equivalent here to H0=0. |
| 10 | `S1-block-residual.residual-gram-split` | `S1-block-residual` | `introductory_background_not_designated_result` | — | R*R=H0^2+B*B. |
| 11 | `S1-block-residual.rayleigh-ritz-minimizes-residual` | `S1-block-residual` | `introductory_background_not_designated_result` | — | The Rayleigh--Ritz choice minimizes residual size among the block choices under discussion. |
| 12 | `S1-block-residual.one-sided-vs-strong-offdiagonal` | `S1-block-residual` | `introductory_background_not_designated_result` | — | H0=0 is distinguished from the stronger H0=H1=0 condition. |
| 13 | `S1-block-residual.residual-eigenvalue-sum` | `S1-block-residual` | `introductory_background_not_designated_result` | — | There is an ordering of m exact eigenvalues with sum_j (alpha_j-lambda_j)^2 <= \|\|R\|\|_sq^2. |
| 14 | `S1-block-residual.residual-eigenvalue-pointwise` | `S1-block-residual` | `introductory_background_not_designated_result` | — | The same ordering satisfies \|alpha_j-lambda_j\| <= \|\|R\|\|_1. |
| 15 | `S1-block-residual.eq-1-1` | `S1-block-residual` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.1) as reconstructed in the distributable TeX. |
| 16 | `S1-block-residual.eq-1-2` | `S1-block-residual` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.2) as reconstructed in the distributable TeX. |
| 17 | `S1-block-residual.eq-1-3` | `S1-block-residual` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.3) as reconstructed in the distributable TeX. |
| 18 | `S1-block-residual.eq-1-4` | `S1-block-residual` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.4) as reconstructed in the distributable TeX. |
| 19 | `S1-block-residual.eq-1-5` | `S1-block-residual` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.5) as reconstructed in the distributable TeX. |
| 20 | `S1-block-residual.eq-1-6` | `S1-block-residual` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.6) as reconstructed in the distributable TeX. |
| 21 | `S1-block-residual.eq-1-7` | `S1-block-residual` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.7) as reconstructed in the distributable TeX. |
| 22 | `S1-block-residual.eq-1-8` | `S1-block-residual` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.8) as reconstructed in the distributable TeX. |
| 23 | `S1-ui-norms.ui-rank-one-normalization` | `S1-ui-norms` | `definition_not_result` | — | Rank-one operators satisfy the normalized unitary-invariant norm convention. |
| 24 | `S1-ui-norms.ui-contraction-monotonicity` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | Left and right multiplication by contractions cannot increase a unitary-invariant norm. |
| 25 | `S1-ui-norms.singular-minimax-noncompact-scope` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | The singular-value minimax expression extends to bounded noncompact operators, with spectral-multiplicity cautions. |
| 26 | `S1-ui-norms.hilbert-schmidt-identity` | `S1-ui-norms` | `definition_not_result` | — | The Hilbert--Schmidt norm is the square root of the sum of squared singular values and trace K*K. |
| 27 | `S1-ui-norms.fan-dominance` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | All-unitary-invariant-norm comparison is equivalent to comparison in every Ky Fan norm. |
| 28 | `S1-ui-norms.eq1-13-variational` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | The Ky Fan norm also equals the supremum of the real sum of y_k* K x_k over orthonormal tuples. |
| 29 | `S1-ui-norms.cosine-law` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | The vector-angle convention satisfies \|\|x+y\|\|^2=\|\|x\|\|^2+\|\|y\|\|^2+2\|\|x\|\|\|\|y\|\|cos angle(x,y). |
| 30 | `S1-ui-norms.s0-singular-values` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | The singular values of S0 are sin(theta_k) for the principal-angle data. |
| 31 | `S1-ui-norms.ambient-angle-doubling` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | Section 1 states, in anticipation of the Section 3 direct-rotation construction and without restating a dimension hypothesis, that the nonzero angle data of the ambient angle operator are those of Theta_0 occurring twice, once from each side. |
| 32 | `S1-ui-norms.directed-sine-norm` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | \|\|Q^perp P\|\|=\|\|Q^perp E0\|\|=\|\|sin Theta0\|\| for every UI norm. |
| 33 | `S1-ui-norms.ambient-sine-norm` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | \|\|P-Q\|\|=\|\|sin Theta\|\| for every UI norm. |
| 34 | `S1-ui-norms.operator-largest-one-sided-distance` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | In operator norm the largest one-sided distance is \|\|sin Theta\|\|_1. |
| 35 | `S1-ui-norms.closest-unit-vector-distance` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | The closest-unit-vector distance is 2\|\|sin(Theta/2)\|\|_1. |
| 36 | `S1-ui-norms.j-block-form` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | Section 3 constructs the skew block partial isometry J from J0. |
| 37 | `S1-ui-norms.direct-rotation-exponential` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | The distinguished direct rotation satisfies U=exp(J Theta)=cos Theta+J sin Theta with the displayed block form. |
| 38 | `S1-ui-norms.eq-1-9` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.9) as reconstructed in the distributable TeX. |
| 39 | `S1-ui-norms.eq-1-10` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.10) as reconstructed in the distributable TeX. |
| 40 | `S1-ui-norms.eq-1-11` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.11) as reconstructed in the distributable TeX. |
| 41 | `S1-ui-norms.eq-1-12` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.12) as reconstructed in the distributable TeX. |
| 42 | `S1-ui-norms.eq-1-13` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.13) as reconstructed in the distributable TeX. |
| 43 | `S1-ui-norms.eq-1-14` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.14) as reconstructed in the distributable TeX. |
| 44 | `S1-ui-norms.eq-1-15` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.15) as reconstructed in the distributable TeX. |
| 45 | `S1-ui-norms.eq-1-16` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.16) as reconstructed in the distributable TeX. |
| 46 | `S1-ui-norms.eq-1-17` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.17) as reconstructed in the distributable TeX. |
| 47 | `S1-ui-norms.eq-1-18` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.18) as reconstructed in the distributable TeX. |
| 48 | `S2-sin-theta.family-distinctness` | `S2-sin-theta` | `expository_commentary_not_result` | — | The four Section 2 theorem families are distinct rather than mere restatements. |
| 49 | `S2-sin-theta.ui-norm-scope` | `S2-sin-theta` | `counted_result_scope` | `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-tan-two-theta` | Every norm in the four headline theorem statements is an arbitrary unitary-invariant norm. |
| 50 | `S2-sin-theta.gap-hypothesis` | `S2-sin-theta` | `counted_result_hypothesis` | `S2-sin-theta` | The sine theorem uses interval/exterior separation, allowing the A0 and Lambda1 roles to be interchanged. |
| 51 | `S2-sin-theta.directed-conclusion` | `S2-sin-theta` | `counted_result_statement` | `S2-sin-theta` | delta \|\|sin Theta0\|\| <= \|\|R\|\|. |
| 52 | `S2-tan-theta.ordered-gap-hypothesis` | `S2-tan-theta` | `counted_result_hypothesis` | `S2-tan-theta` | The tangent theorem assumes A0 below Lambda1 by delta. |
| 53 | `S2-tan-theta.rayleigh-ritz-hypothesis` | `S2-tan-theta` | `counted_result_hypothesis` | `S2-tan-theta` | The tangent theorem assumes H0=0, equivalently the Rayleigh--Ritz block choice. |
| 54 | `S2-tan-theta.directed-conclusion` | `S2-tan-theta` | `counted_result_statement` | `S2-tan-theta` | delta \|\|tan Theta0\|\| <= \|\|R\|\|. |
| 55 | `S2-tan-theta.ambient-conclusion` | `S2-tan-theta` | `counted_result_statement` | `S2-tan-theta` | delta \|\|tan Theta\|\| <= \|\|H\|\|. |
| 56 | `S2-sin-two-theta.gap-hypothesis` | `S2-sin-two-theta` | `counted_result_hypothesis` | `S2-sin-two-theta` | The double-sine theorem separates Lambda0 from Lambda1 by an interval/exterior gap. |
| 57 | `S2-sin-two-theta.directed-conclusion` | `S2-sin-two-theta` | `counted_result_statement` | `S2-sin-two-theta` | delta \|\|sin(2 Theta0)\|\| <= 2\|\|R\|\|. |
| 58 | `S2-sin-two-theta.ambient-conclusion` | `S2-sin-two-theta` | `counted_result_statement` | `S2-sin-two-theta` | delta \|\|sin(2 Theta)\|\| <= 2\|\|H\|\|. |
| 59 | `S2-tan-two-theta.ordered-gap-hypothesis` | `S2-tan-two-theta` | `counted_result_hypothesis` | `S2-tan-two-theta` | The double-tangent theorem assumes A0 below A1 by delta. |
| 60 | `S2-tan-two-theta.strong-offdiagonal-hypothesis` | `S2-tan-two-theta` | `counted_result_hypothesis` | `S2-tan-two-theta` | The double-tangent theorem assumes H0=H1=0. |
| 61 | `S2-tan-two-theta.no-extra-pole-hypothesis` | `S2-tan-two-theta` | `counted_result_scope` | `S2-tan-two-theta` | The printed theorem has no independent tan-pole exclusion or perturbed-block spectral-placement hypothesis. |
| 62 | `S2-tan-two-theta.directed-conclusion` | `S2-tan-two-theta` | `counted_result_statement` | `S2-tan-two-theta` | delta \|\|tan(2 Theta0)\|\| <= 2\|\|R\|\|. |
| 63 | `S2-tan-two-theta.ambient-conclusion` | `S2-tan-two-theta` | `counted_result_statement` | `S2-tan-two-theta` | delta \|\|tan(2 Theta)\|\| <= 2\|\|H\|\|. |
| 64 | `S2-tan-two-theta.pole-exclusion-derived` | `S2-tan-two-theta` | `proof_or_derivation_not_result` | — | Section 7 derives the needed nonvanishing cosine factors from the printed hypotheses. |
| 65 | `S2-sharpness.constants-best-possible` | `S2-sharpness` | `sharpness_commentary_not_designated_result` | — | The constants in all four theorem families are best possible. |
| 66 | `S2-sharpness.two-dimensional-equality` | `S2-sharpness` | `sharpness_commentary_not_designated_result` | — | Two-dimensional examples attain the constants. |
| 67 | `S2-sharpness.direct-sum-simultaneous-equality` | `S2-sharpness` | `sharpness_commentary_not_designated_result` | — | Orthogonal sums give simultaneous equality for all UI norms. |
| 68 | `S2-sharpness.first-order-asymptotic` | `S2-sharpness` | `sharpness_commentary_not_designated_result` | — | All four estimates share the stated first-order epsilon asymptotics. |
| 69 | `S2-unbounded-scope.infinite-dimensional-scope` | `S2-unbounded-scope` | `counted_result_scope` | `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-tan-two-theta` | All four main results apply in infinite as well as finite dimension. |
| 70 | `S2-unbounded-scope.arbitrary-ui-scope` | `S2-unbounded-scope` | `counted_result_scope` | `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-tan-two-theta` | All four main results apply to arbitrary UI norms. |
| 71 | `S2-unbounded-scope.unbounded-selfadjoint-scope` | `S2-unbounded-scope` | `counted_result_scope` | `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-tan-two-theta` | The results extend to unbounded self-adjoint A under the stated domain condition. |
| 72 | `S2-unbounded-scope.bounded-residual-needed` | `S2-unbounded-scope` | `counted_result_scope` | `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-tan-two-theta` | Useful unbounded conclusions require the pertinent perturbation or residual to extend boundedly. |
| 73 | `S2-unbounded-scope.half-infinite-gap-intervals` | `S2-unbounded-scope` | `counted_result_scope` | `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-tan-two-theta` | Gap intervals may be half-infinite and the remaining spectra unbounded. |
| 74 | `DK-3.1-def.s0-s1-singular-values` | `DK-3.1-def` | `section_setup_not_result` | — | S0 and S1 have the same nonzero singular values, with the stated possible initial unit singular values from unequal C0 nullities. |
| 75 | `DK-3.1-def.direct-rotation-definition` | `DK-3.1-def` | `definition_not_result` | — | A direct rotation is a unitary intertwiner with C0,C1 positive and S1=S0*. |
| 76 | `DK-3.1-def.u-notation` | `DK-3.1-def` | `definition_not_result` | — | The paper reserves U for direct rotations. |
| 77 | `DK-3.1-def.eq-3-1` | `DK-3.1-def` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (3.1) as reconstructed in the distributable TeX. |
| 78 | `DK-3.1-def.eq-3-2` | `DK-3.1-def` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (3.2) as reconstructed in the distributable TeX. |
| 79 | `DK-3.1-def.eq-3-3` | `DK-3.1-def` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (3.3) as reconstructed in the distributable TeX. |
| 80 | `DK-3.1-def.eq-3-4` | `DK-3.1-def` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (3.4) as reconstructed in the distributable TeX. |
| 81 | `DK-3.2-def.acute-case-definition` | `DK-3.2-def` | `definition_not_result` | — | The acute case is exactly the vanishing of the two crossing intersections. |
| 82 | `DK-3.1-prop.existence` | `DK-3.1-prop` | `counted_result_statement` | `DK-3.1-prop` | In the acute case a direct rotation exists. |
| 83 | `DK-3.1-prop.uniqueness` | `DK-3.1-prop` | `counted_result_statement` | `DK-3.1-prop` | In the acute case the direct rotation is unique. |
| 84 | `DK-3.1-prop.positive-diagonal-characterization` | `DK-3.1-prop` | `counted_result_statement` | `DK-3.1-prop` | Positivity of C0,C1 characterizes the direct rotation among unitary intertwiners in the acute case. |
| 85 | `DK-3.2-prop.existence-iff-crossing-dimensions` | `DK-3.2-prop` | `counted_result_statement` | `DK-3.2-prop` | Outside the acute case, direct rotation existence is equivalent to equality of the crossing dimensions. |
| 86 | `DK-3.2-prop.nonuniqueness` | `DK-3.2-prop` | `counted_result_statement` | `DK-3.2-prop` | When it exists outside the acute case it need not be unique. |
| 87 | `DK-3.2-prop.crossing-square-minus-one` | `DK-3.2-prop` | `proof_detail_not_in_printed_statement` | — | On the crossing subspaces U^2 x=-x. |
| 88 | `DK-3.2-prop.finite-crossing-automatic` | `DK-3.2-prop` | `post_result_scope_remark_not_in_printed_statement` | — | Under the assumed (1.5), condition (3.5) holds automatically whenever either dim P-space or dim P-perp-space is finite. |
| 89 | `DK-3.2-prop.bilateral-shift-counterexample` | `DK-3.2-prop` | `remark_or_example_not_result` | — | The bilateral-shift example on two-sided square-summable sequences satisfies (1.5) with nested P-space and Q-space, has crossing subspaces of dimensions 1 and 0, and therefore fails (3.5): the matching-dimension conditions do not imply the crossing-dimension condition in infinite dimension. |
| 90 | `DK-3.2-prop.eq-3-5` | `DK-3.2-prop` | `counted_result_statement` | `DK-3.2-prop` | Exact mathematical content of source equation (3.5) as reconstructed in the distributable TeX. |
| 91 | `S3-standing-scope.crossed-dimension-standing-assumption` | `S3-standing-scope` | `counted_result_scope` | `DK-3.4-prop`, `DK-8.2-thm` | Standing convention: (3.5) is assumed as well as (1.5) for the remainder of the paper, except where the contrary is explicitly stated, so a direct rotation always exists and the development uses its direct special case (3.6). |
| 92 | `DK-3.3-prop.reflection-conjugacy` | `DK-3.3-prop` | `pre_result_setup_not_in_printed_statement` | — | With X=P-Pperp and Q_-=XQX, U^{-1}=XUX. |
| 93 | `DK-3.3-prop.principal-square-root` | `DK-3.3-prop` | `counted_result_statement` | `DK-3.3-prop` | Every direct rotation is the principal unitary square root of the product of the two reflections. |
| 94 | `DK-3.3-prop.square-root-converse` | `DK-3.3-prop` | `counted_result_statement` | `DK-3.3-prop` | A principal square root is a direct rotation when it maps the two crossing subspaces appropriately. |
| 95 | `DK-3.3-prop.eq-3-6` | `DK-3.3-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (3.6) as reconstructed in the distributable TeX. |
| 96 | `DK-3.3-prop.eq-3-7` | `DK-3.3-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (3.7) as reconstructed in the distributable TeX. |
| 97 | `DK-3.3-prop.eq-3-8` | `DK-3.3-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (3.8) as reconstructed in the distributable TeX. |
| 98 | `DK-3.4-prop.u-square-direct-rotation` | `DK-3.4-prop` | `counted_result_statement` | `DK-3.4-prop` | If C0^2>=1/2, then U^2 is the direct rotation from Q_- to Q. |
| 99 | `DK-3.1-thm.angle-operator-partial-isometry` | `DK-3.1-thm` | `pre_result_setup_not_in_printed_statement` | — | For the direct rotation, Theta_j = arccos C_j, the two angle operators are isometric-equivalent apart from the dimensionalities of their null spaces, and the polar resolution S_0 = J_0 sin Theta_0 gives a partial isometry J_0 of the closed range of Theta_0 onto that of Theta_1 with J_0 Theta_0 = Theta_1 J_0. |
| 100 | `DK-3.1-thm.complete-invariant` | `DK-3.1-thm` | `counted_result_statement` | `DK-3.1-thm` | Spectral multiplicity functions of Theta0,Theta1 completely classify the pair under the stated dimension hypotheses. |
| 101 | `DK-3.1-thm.converse-angle-data` | `DK-3.1-thm` | `counted_result_statement` | `DK-3.1-thm` | Conversely the angle operators may be arbitrary positive contractions in [0,pi/2] with matching spectral multiplicities away from zero and the stated dimensions. |
| 102 | `DK-3.1-thm.reconstruction` | `DK-3.1-thm` | `proof_detail_not_in_printed_statement` | — | The pair is reconstructed from the angle data and J0. |
| 103 | `DK-3.1-cor.compact-complete-invariants` | `DK-3.1-cor` | `counted_result_statement` | `DK-3.1-cor` | If PQperpP is compact, the eigenvalues of Theta0,Theta1 counted with multiplicity are complete invariants. |
| 104 | `DK-3.1-cor.allowed-angle-sequence` | `DK-3.1-cor` | `counted_result_statement` | `DK-3.1-cor` | Theta0 eigenvalues may be any decreasing sequence in [0,pi/2] tending to zero plus possible zero eigenspace. |
| 105 | `DK-3.1-cor.theta1-match` | `DK-3.1-cor` | `counted_result_statement` | `DK-3.1-cor` | Theta1 has the same nonzero eigenvalues and may differ only in zero multiplicity. |
| 106 | `DK-3.5-prop.commutation` | `DK-3.5-prop` | `counted_result_statement` | `DK-3.5-prop` | Theta commutes with P,Q,J,U. |
| 107 | `DK-3.5-prop.direct-rotation-exponential` | `DK-3.5-prop` | `pre_result_setup_not_in_printed_statement` | — | U=exp(J Theta). |
| 108 | `DK-3.5-prop.cos-square-projector` | `DK-3.5-prop` | `pre_result_setup_not_in_printed_statement` | — | cos^2 Theta=PQP+Pperp Qperp Pperp. |
| 109 | `DK-3.5-prop.eigenvector-rotation-angle` | `DK-3.5-prop` | `counted_result_statement` | `DK-3.5-prop` | If Theta x=theta x then angle(x,Ux)=theta. |
| 110 | `DK-3.5-prop.acute-maximal-characterization` | `DK-3.5-prop` | `counted_result_statement` | `DK-3.5-prop` | In the acute case each theta-eigenspace is the unique maximal P/Q-reducing subspace with the stated constant-angle properties. |
| 111 | `DK-3.2-cor.swap-invariance` | `DK-3.2-cor` | `counted_result_statement` | `DK-3.2-cor` | Swapping P and Q leaves Theta unchanged and sends J to -J. |
| 112 | `DK-4.1-prop.vz-factorization` | `DK-4.1-prop` | `section_setup_not_result` | — | Every unitary V carrying P to Q is written V=UZ with Z block diagonal in the Section 4 setup. |
| 113 | `DK-4.1-prop.orthonormal-angle-lower-bounds` | `DK-4.1-prop` | `counted_result_statement` | `DK-4.1-prop` | For every such V there are orthonormal v_k in P with angle(v_k,Vv_k)>=theta_k. |
| 114 | `DK-4.1-prop.singular-value-minimality` | `DK-4.1-prop` | `counted_result_statement` | `DK-4.1-prop` | Each singular value of (1-V)\|P is minimized at V=U with value 2 sin(theta_k/2). |
| 115 | `DK-4.1-prop.closest-q-vector-proof-step` | `DK-4.1-prop` | `proof_or_derivation_not_result` | — | The pointwise comparison uses Qx/\|\|Qx\|\| as the closest unit vector in Q-space. |
| 116 | `DK-4.1-prop.eq-4-1` | `DK-4.1-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (4.1) as reconstructed in the distributable TeX. |
| 117 | `DK-4.1-prop.eq-4-2` | `DK-4.1-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (4.2) as reconstructed in the distributable TeX. |
| 118 | `DK-4.1-cor.ui-minimality-on-p` | `DK-4.1-cor` | `counted_result_statement` | `DK-4.1-cor` | For every UI norm, \|\|(1-V)P\|\| is minimized at V=U. |
| 119 | `DK-4.2-prop.basis-sine-square-lower-bound` | `DK-4.2-prop` | `counted_result_statement` | `DK-4.2-prop` | For every orthonormal basis of P, sum sin^2 angle(v_k,Vv_k) >= sum sin^2 theta_k, including infinite RHS. |
| 120 | `DK-4.2-prop.trace-identification` | `DK-4.2-prop` | `proof_or_derivation_not_result` | — | The lower bound is identified with tr(S0* S0). |
| 121 | `DK-4.3-prop.plane-parameterization` | `DK-4.3-prop` | `proof_detail_not_in_printed_statement` | — | On each principal two-plane V has the displayed a_j,b_j parameterization. |
| 122 | `DK-4.3-prop.squared-displacement-global-minimum` | `DK-4.3-prop` | `counted_result_statement` | `DK-4.3-prop` | \|\|(1-V*)(1-V)\|\| is minimized by U for every UI norm. |
| 123 | `DK-4.3-prop.operator-norm-displacement-minimum` | `DK-4.3-prop` | `post_result_consequence_not_in_printed_statement` | — | The operator norm of 1-V is minimized by U. |
| 124 | `DK-4.3-prop.hilbert-schmidt-displacement-minimum` | `DK-4.3-prop` | `post_result_consequence_not_in_printed_statement` | — | The Hilbert--Schmidt norm of 1-V is minimized by U. |
| 125 | `DK-4.3-prop.arbitrary-ui-displacement-warning` | `DK-4.3-prop` | `post_result_consequence_not_in_printed_statement` | — | Arbitrary UI norms of 1-V need not be minimized by U. |
| 126 | `DK-4.3-prop.eq-4-3` | `DK-4.3-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (4.3) as reconstructed in the distributable TeX. |
| 127 | `DK-4.3-prop.eq-4-4` | `DK-4.3-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (4.4) as reconstructed in the distributable TeX. |
| 128 | `DK-4.3-prop.eq-4-5` | `DK-4.3-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (4.5) as reconstructed in the distributable TeX. |
| 129 | `DK-4.3-prop.eq-4-6` | `DK-4.3-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (4.6) as reconstructed in the distributable TeX. |
| 130 | `DK-4.4-prop.example4-1-real-reflection` | `DK-4.4-prop` | `remark_or_example_not_result` | — | Example 4.1 gives a real reflection with singular values 2,0 versus two equal direct-rotation singular values and defeats the Ky Fan 2 norm for theta>pi/3. |
| 131 | `DK-4.4-prop.example4-2-complex-phase` | `DK-4.4-prop` | `remark_or_example_not_result` | — | Example 4.2 uses V=e^{i delta}U and shows the full-displacement UI minimum can fail in complex space. |
| 132 | `DK-4.4-prop.printed-proposition4-4` | `DK-4.4-prop` | `counted_result_statement` | `DK-4.4-prop` | The paper asserts that in real space with Theta<=pi/3, U minimizes \|\|1-V\|\| for every UI norm. |
| 133 | `DK-4.4-prop.printed-sharp-threshold` | `DK-4.4-prop` | `sharpness_commentary_not_designated_result` | — | The paper asserts the pi/3 threshold is sharp in view of the examples. |
| 134 | `DK-5.1-thm.banach-hypotheses` | `DK-5.1-thm` | `counted_result_hypothesis` | `DK-5.1-thm` | Banach-space theorem with \|\|B\|\|<=alpha and \|\|A^{-1}\|\|<=(alpha+delta)^{-1}, compatible cross norm. |
| 135 | `DK-5.1-thm.sylvester-lower-bound` | `DK-5.1-thm` | `counted_result_statement` | `DK-5.1-thm` | AX-XB=C implies \|\|C\|\|>=delta\|\|X\|\|. |
| 136 | `DK-5.1-thm.roles-interchange` | `DK-5.1-thm` | `post_result_scope_remark_not_in_printed_statement` | — | A and B roles/hypotheses may be interchanged. |
| 137 | `DK-5.1-thm.one-sided-unbounded-extension` | `DK-5.1-thm` | `post_result_scope_remark_not_in_printed_statement` | — | The proof covers densely-defined unbounded A with bounded inverse hypothesis while B,X remain bounded. |
| 138 | `DK-5-hermitian-inequalities.pairwise-gap-hypothesis` | `DK-5-hermitian-inequalities` | `background_theory_not_designated_result` | — | Hermitian A,B have pairwise spectral distance at least delta. |
| 139 | `DK-5-hermitian-inequalities.operator-norm-constant-one-fails` | `DK-5-hermitian-inequalities` | `background_theory_not_designated_result` | — | The operator-norm analogue with constant 1 can fail. |
| 140 | `DK-5-hermitian-inequalities.rank-factor-not-best` | `DK-5-hermitian-inequalities` | `sharpness_commentary_not_designated_result` | — | Equation (5.2) is not best possible unless rank C<=1. |
| 141 | `DK-5-hermitian-inequalities.universal-constant-question` | `DK-5-hermitian-inequalities` | `open_question` | — | The source asks whether the rank factor can be replaced by a universal constant. |
| 142 | `DK-5-hermitian-inequalities.constant-one-explicit-counterexample` | `DK-5-hermitian-inequalities` | `remark_or_example_not_result` | — | The displayed 2x2 A,B,X example rules out universal constant 1. |
| 143 | `DK-5-hermitian-inequalities.eq-5-1` | `DK-5-hermitian-inequalities` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (5.1) as reconstructed in the distributable TeX. |
| 144 | `DK-5-hermitian-inequalities.eq-5-2` | `DK-5-hermitian-inequalities` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (5.2) as reconstructed in the distributable TeX. |
| 145 | `DK-5.2-thm.hilbert-unbounded-hypotheses` | `DK-5.2-thm` | `counted_result_hypothesis` | `DK-5.2-thm` | Theorem 5.2 gives the Hilbert-space unbounded Sylvester setup with separated spectra and domain/core hypotheses. |
| 146 | `DK-5.2-thm.hilbert-unbounded-conclusion` | `DK-5.2-thm` | `counted_result_statement` | `DK-5.2-thm` | The corresponding delta\|\|X\|\| lower bound holds in the stated UI/ideal norm scope. |
| 147 | `DK-5.1-lem.strong-cutoff-convergence` | `DK-5.1-lem` | `counted_result_statement` | `DK-5.1-lem` | The spectral-cutoff approximants converge strongly in the manner stated and support the unbounded proof. |
| 148 | `DK-6.1-lem.ordered-sylvester-forward` | `DK-6.1-lem` | `counted_result_statement` | `DK-6.1-lem` | The ordered spectral separation implies the stated Sylvester/UI-norm lower bound. |
| 149 | `DK-6.1-lem.ordered-sylvester-converse` | `DK-6.1-lem` | `counted_result_statement` | `DK-6.1-lem` | The source includes the converse characterization used in the single-angle proof. |
| 150 | `DK-6.2-lem.pinching-contraction` | `DK-6.2-lem` | `counted_result_statement` | `DK-6.2-lem` | The reflection/pinching operation contracts every unitary-invariant norm in the stated setup. |
| 151 | `DK-6.1-prop.sine-proof-residual-identity` | `DK-6.1-prop` | `proof_detail_not_in_printed_statement` | — | The symmetric sine proof rewrites the relevant off-diagonal block as the Sylvester residual identity. |
| 152 | `DK-6.1-prop.symmetric-sine-theorem` | `DK-6.1-prop` | `counted_result_statement` | `DK-6.1-prop` | Proposition 6.1 gives the symmetric sine-theta conclusion under two-sided spectral placement. |
| 153 | `DK-6.1-prop.source-counterexample-need-two-sided` | `DK-6.1-prop` | `remark_or_example_not_result` | — | The source exhibits the failure of the ambient/symmetric conclusion when the needed two-sided placement is dropped. |
| 154 | `DK-6.1-prop.eq-6-1` | `DK-6.1-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.1) as reconstructed in the distributable TeX. |
| 155 | `DK-6.1-thm.generalized-sine-hypotheses` | `DK-6.1-thm` | `counted_result_hypothesis` | `DK-6.1-thm` | The generalized sine theorem allows nonisometric E0 with E0*E0 >= epsilon^2 and the stated spectral separation. |
| 156 | `DK-6.1-thm.generalized-sine-conclusion` | `DK-6.1-thm` | `counted_result_statement` | `DK-6.1-thm` | delta epsilon \|\|sin Theta0\|\| <= \|\|R\|\|. |
| 157 | `DK-6.1-thm.unequal-dimension-scope` | `DK-6.1-thm` | `counted_result_scope` | `DK-6.1-thm` | The generalized theorem allows unequal-dimensional comparison subspaces as stated. |
| 158 | `DK-6.2-thm.second-generalized-sine` | `DK-6.2-thm` | `counted_result_statement` | `DK-6.2-thm` | The second generalized sine theorem gives the Hilbert--Schmidt estimate under pairwise spectral separation. |
| 159 | `DK-6.2-thm.rank-corrected-operator-consequence` | `DK-6.2-thm` | `post_result_consequence_not_in_printed_statement` | — | The stated rank-corrected operator-norm consequence follows. |
| 160 | `DK-6.3-thm.tangent-setup-identities` | `DK-6.3-thm` | `proof_or_derivation_not_result` | — | Equations (6.2)--(6.6) provide the block identities used in the generalized tangent proof. |
| 161 | `DK-6.3-thm.tangent-proof-temporary-boundedness` | `DK-6.3-thm` | `proof_or_derivation_not_result` | — | The Section 6 tangent proof temporarily supposes that all operators are bounded and that S_0 is compact, and defers the removal of both restrictions to the Appendix to Section 6. |
| 162 | `DK-6.3-thm.ambient-wholeSpace-assembly` | `DK-6.3-thm` | `proof_or_derivation_not_result` | — | The ambient conclusion is assembled from the directed one: tan Theta has the two-corner block form built from J_0, tan Theta_0 and tan Theta_1, the two corners have equal unitarily invariant norms through J_0, and Lemmas 6.1 and 6.2 then give delta \|\|tan Theta\|\| <= \|\|H\|\|. |
| 163 | `DK-6.3-thm.example6-1` | `DK-6.3-thm` | `remark_or_example_not_result` | — | Example 6.1 gives the explicit 2x2 counterexample showing one-sided placement is essential for the tangent conclusion. |
| 164 | `DK-6.3-thm.generalized-tangent-theorem` | `DK-6.3-thm` | `counted_result_statement` | `DK-6.3-thm` | Theorem 6.3 gives the generalized tangent residual bound with its exact source hypotheses. |
| 165 | `DK-6.3-thm.eq-6-2` | `DK-6.3-thm` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.2) as reconstructed in the distributable TeX. |
| 166 | `DK-6.3-thm.eq-6-3` | `DK-6.3-thm` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.3) as reconstructed in the distributable TeX. |
| 167 | `DK-6.3-thm.eq-6-4` | `DK-6.3-thm` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.4) as reconstructed in the distributable TeX. |
| 168 | `DK-6.3-thm.eq-6-5` | `DK-6.3-thm` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.5) as reconstructed in the distributable TeX. |
| 169 | `DK-6.3-thm.eq-6-6` | `DK-6.3-thm` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.6) as reconstructed in the distributable TeX. |
| 170 | `DK-6-appendix.unbounded-sine-extension` | `DK-6-appendix` | `expository_commentary_not_result` | — | The sine theorem extends to unbounded operators via bounded residual/common-domain hypotheses. |
| 171 | `DK-6-appendix.unbounded-tangent-extension` | `DK-6-appendix` | `counted_result_scope` | `S2-tan-theta` | The Appendix states the tan theta theorem in the general ordered case A0 <= alpha and Lambda1 >= alpha + delta and explicitly allows both A0 and Lambda1 to be unbounded, while the residual used by the norm estimate remains bounded. |
| 172 | `DK-6-appendix.appendix-approximation-chain` | `DK-6-appendix` | `proof_or_derivation_not_result` | — | Equations (6.7)--(6.11) form the approximation chain controlling singular directions and passing to all UI norms. |
| 173 | `DK-6-appendix.appendix-all-ui-limit` | `DK-6-appendix` | `proof_or_derivation_not_result` | — | The epsilon-to-zero argument completes the bound-norm case and then all UI norms. |
| 174 | `DK-6-appendix.eq-6-7` | `DK-6-appendix` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.7) as reconstructed in the distributable TeX. |
| 175 | `DK-6-appendix.eq-6-8` | `DK-6-appendix` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.8) as reconstructed in the distributable TeX. |
| 176 | `DK-6-appendix.eq-6-9` | `DK-6-appendix` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.9) as reconstructed in the distributable TeX. |
| 177 | `DK-6-appendix.eq-6-10` | `DK-6-appendix` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.10) as reconstructed in the distributable TeX. |
| 178 | `DK-6-appendix.eq-6-11` | `DK-6-appendix` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.11) as reconstructed in the distributable TeX. |
| 179 | `DK-6.3-lem.approximation-number-leakage` | `DK-6.3-lem` | `counted_result_statement` | `DK-6.3-lem` | Lemma 6.3 controls the approximation/singular-number leakage used in the Appendix, including the stated finite and real forms. |
| 180 | `DK-7-sin2-proof.reflection-setup` | `DK-7-sin2-proof` | `proof_or_derivation_not_result` | — | The reflection construction converts the double-angle geometry into a single-angle comparison. |
| 181 | `DK-7-sin2-proof.ambient-sin2` | `DK-7-sin2-proof` | `restatement_of_counted_result` | — | The Section 7 proof derives the ambient sin2Theta perturbation estimate. |
| 182 | `DK-7-sin2-proof.directed-sin2` | `DK-7-sin2-proof` | `restatement_of_counted_result` | — | It separately derives the directed sin2Theta0 residual estimate. |
| 183 | `DK-7-sin2-proof.factor-one-directed-residual-refinement` | `DK-7-sin2-proof` | `proof_or_derivation_not_result` | — | The directed block residual estimate has the source factor-one intermediate bound before the headline factor 2 form. |
| 184 | `DK-7-sin2-proof.swap-asymmetry` | `DK-7-sin2-proof` | `expository_commentary_not_result` | — | The source records the asymmetry involved in swapping the two operators/subspaces in the residual form. |
| 185 | `DK-7-sin2-proof.eq-7-1` | `DK-7-sin2-proof` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (7.1) as reconstructed in the distributable TeX. |
| 186 | `DK-7-sin2-proof.eq-7-2` | `DK-7-sin2-proof` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (7.2) as reconstructed in the distributable TeX. |
| 187 | `DK-7-sin2-proof.eq-7-3` | `DK-7-sin2-proof` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (7.3) as reconstructed in the distributable TeX. |
| 188 | `DK-7-sin2-proof.eq-7-4` | `DK-7-sin2-proof` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (7.4) as reconstructed in the distributable TeX. |
| 189 | `DK-7-sin2-proof.eq-7-5` | `DK-7-sin2-proof` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (7.5) as reconstructed in the distributable TeX. |
| 190 | `DK-7-tan2-proof.tan2-block-identity` | `DK-7-tan2-proof` | `proof_or_derivation_not_result` | — | Equation (7.6) gives the decisive tangent double-angle block identity. |
| 191 | `DK-7-tan2-proof.cos2-pole-exclusion` | `DK-7-tan2-proof` | `proof_or_derivation_not_result` | — | The singular-vector argument proves the relevant cos(2 theta_j) factors do not vanish from the source hypotheses. |
| 192 | `DK-7-tan2-proof.ambient-tan2` | `DK-7-tan2-proof` | `restatement_of_counted_result` | — | The proof yields the ambient tan2Theta perturbation estimate. |
| 193 | `DK-7-tan2-proof.directed-tan2` | `DK-7-tan2-proof` | `restatement_of_counted_result` | — | The proof yields the directed tan2Theta0 residual estimate. |
| 194 | `DK-7-tan2-proof.eq-7-6` | `DK-7-tan2-proof` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (7.6) as reconstructed in the distributable TeX. |
| 195 | `DK-8.1-thm.branch-problem` | `DK-8.1-thm` | `pre_result_motivation_not_result` | — | Small double-angle trigonometric quantities alone do not select angles near zero; the chosen reducing subspace matters. |
| 196 | `DK-8.1-thm.acute-iff-spectral-placement` | `DK-8.1-thm` | `counted_result_statement` | `DK-8.1-thm` | Theta<=pi/4 iff the chosen perturbed reducing blocks lie on the corresponding sides of the gap. |
| 197 | `DK-8.1-thm.existence-correct-q` | `DK-8.1-thm` | `counted_result_statement` | `DK-8.1-thm` | A reducing spectral projector Q with the required placement exists and is unique in the stated sense. |
| 198 | `DK-8.1-thm.part-i-compression` | `DK-8.1-thm` | `counted_result_statement` | `DK-8.1-thm` | The upper/lower block compression inequalities of part (i). |
| 199 | `DK-8.1-thm.part-ii-eigenvalue` | `DK-8.1-thm` | `counted_result_statement` | `DK-8.1-thm` | The finite-dimensional eigenvalue displacement inequalities of part (ii), with natural infinite-dimensional extensions. |
| 200 | `DK-8.1-thm.part-iii-gauge` | `DK-8.1-thm` | `counted_result_statement` | `DK-8.1-thm` | The symmetric-gauge majorization inequalities of part (iii). |
| 201 | `DK-8.1-thm.exclude-pi-over-four` | `DK-8.1-thm` | `proof_or_derivation_not_result` | — | Equations (8.1)--(8.2) exclude theta=pi/4 and then theta>pi/4 under the selected placement. |
| 202 | `DK-8.1-thm.spectral-repulsion-interpretation` | `DK-8.1-thm` | `post_result_interpretation_not_result` | — | Strong off-diagonal eigenvector rotation forces definite eigenvalue displacement as described. |
| 203 | `DK-8.1-thm.eq-8-1` | `DK-8.1-thm` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (8.1) as reconstructed in the distributable TeX. |
| 204 | `DK-8.1-thm.eq-8-2` | `DK-8.1-thm` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (8.2) as reconstructed in the distributable TeX. |
| 205 | `DK-8.2-thm.smallness-alternative` | `DK-8.2-thm` | `counted_result_hypothesis` | `DK-8.2-thm` | The theorem assumes either \|\|H\|\|_1<delta/2 or \|\|R\|\|_1<delta/2 plus the stated A0 interval. |
| 206 | `DK-8.2-thm.double-angle-bound-retained` | `DK-8.2-thm` | `counted_result_statement` | `DK-8.2-thm` | The corresponding sin2 double-angle estimate remains valid. |
| 207 | `DK-8.2-thm.acute-branch-conclusion` | `DK-8.2-thm` | `counted_result_statement` | `DK-8.2-thm` | Theta<pi/4. |
| 208 | `DK-8.2-thm.homotopy-proof` | `DK-8.2-thm` | `proof_or_derivation_not_result` | — | The perturbation proof uses the continuous spectral-projector homotopy and the displayed arcsine bound. |
| 209 | `DK-8.2-thm.residual-reduction` | `DK-8.2-thm` | `proof_or_derivation_not_result` | — | The residual form is reduced by changing the complementary perturbation block while preserving the residual/spectral data. |
| 210 | `DK-8.2-thm.sin2-unequal-dimension-extension` | `DK-8.2-thm` | `post_result_scope_remark_not_in_printed_statement` | — | The source states a sin2 extension to unequal comparison dimensions. |
| 211 | `DK-8.2-thm.no-tan2-unequal-dimension-extension-known` | `DK-8.2-thm` | `historical_knowledge_state` | — | No analogous tan2 extension was known. |
| 212 | `DK-9-model.real-l2-model` | `DK-9-model` | `definition_not_result` | — | The numerical model is real L2(0,1) with the free-end fourth-derivative self-adjoint closure and multiplication perturbation epsilon t. |
| 213 | `DK-9-model.perturbed-eigenproblem` | `DK-9-model` | `definition_not_result` | — | The displayed fourth-order perturbed boundary-value eigenproblem. |
| 214 | `DK-9-model.unperturbed-strict-eigenvalue-order` | `DK-9-model` | `section9_worked_example_not_result` | — | The source orders alpha1=0=alpha2<alpha3<alpha4<... with multiplicity. |
| 215 | `DK-9-model.positive-root-equation` | `DK-9-model` | `section9_worked_example_not_result` | — | For k>2, alpha_k are the positive roots of cos(alpha_k^(1/4)) cosh(alpha_k^(1/4))=1. |
| 216 | `DK-9-model.positive-spectrum-over-500` | `DK-9-model` | `section9_worked_example_not_result` | — | All positive alpha_k exceed 500. |
| 217 | `DK-9-model.zero-eigenfunctions` | `DK-9-model` | `section9_worked_example_not_result` | — | The displayed w1,w2 are orthonormal linear eigenfunctions for the zero eigenvalue. |
| 218 | `DK-9-model.lambda3-lower-bound` | `DK-9-model` | `section9_worked_example_not_result` | — | H>=0 implies lambda3>=alpha3>500. |
| 219 | `DK-9-model.initial-residual-formula` | `DK-9-model` | `section9_worked_example_not_result` | — | For A0=0, R=HE0 with the displayed residual functions r_k. |
| 220 | `DK-9-model.residual-gram` | `DK-9-model` | `section9_worked_example_not_result` | — | The displayed 2x2 R*R matrix. |
| 221 | `DK-9-model.residual-gram-eigenvalues` | `DK-9-model` | `section9_worked_example_not_result` | — | R*R has eigenvalues epsilon^2(11+-sqrt76)/30. |
| 222 | `DK-9.1-9.4.sin-bound-comparison` | `DK-9.1-9.4` | `section9_worked_example_not_result` | — | The paper notes (9.1) is sharper than the easy sin2 bound (9.2). |
| 223 | `DK-9.1-9.4.kyfan-two-term-scope` | `DK-9.1-9.4` | `section9_worked_example_not_result` | — | Equations (9.3)--(9.4) use the two-term Ky Fan norm to estimate both principal angles simultaneously. |
| 224 | `DK-9.1-9.4.eq-9-1` | `DK-9.1-9.4` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.1) as reconstructed in the distributable TeX. |
| 225 | `DK-9.1-9.4.eq-9-2` | `DK-9.1-9.4` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.2) as reconstructed in the distributable TeX. |
| 226 | `DK-9.1-9.4.eq-9-3` | `DK-9.1-9.4` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.3) as reconstructed in the distributable TeX. |
| 227 | `DK-9.1-9.4.eq-9-4` | `DK-9.1-9.4` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.4) as reconstructed in the distributable TeX. |
| 228 | `DK-9.5-9.7.rayleigh-ritz-matrix` | `DK-9.5-9.7` | `section9_worked_example_not_result` | — | The displayed Rayleigh--Ritz matrix is E0*(A+H)E0. |
| 229 | `DK-9.5-9.7.refined-residual-gram` | `DK-9.5-9.7` | `section9_worked_example_not_result` | — | The displayed refined residual Gram matrix and its one/two-term norm equal epsilon/sqrt15. |
| 230 | `DK-9.5-9.7.tangent-gap` | `DK-9.5-9.7` | `section9_worked_example_not_result` | — | The tangent gap may be taken as 500-0.7887 epsilon. |
| 231 | `DK-9.5-9.7.kyfan-tan-bound` | `DK-9.5-9.7` | `section9_worked_example_not_result` | — | The same RHS as (9.6) bounds tan theta1+tan theta2 in the two-term Ky Fan norm. |
| 232 | `DK-9.5-9.7.offdiagonal-complement-choice` | `DK-9.5-9.7` | `section9_worked_example_not_result` | — | For tan2 the complementary block is chosen as E1*(A+H)E1>500 to obtain an off-diagonal comparison. |
| 233 | `DK-9.5-9.7.kyfan-tan2-bound` | `DK-9.5-9.7` | `section9_worked_example_not_result` | — | The same RHS as (9.7) bounds tan2theta1+tan2theta2 in the two-term Ky Fan norm. |
| 234 | `DK-9.5-9.7.eq-9-5` | `DK-9.5-9.7` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.5) as reconstructed in the distributable TeX. |
| 235 | `DK-9.5-9.7.eq-9-6` | `DK-9.5-9.7` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.6) as reconstructed in the distributable TeX. |
| 236 | `DK-9.5-9.7.eq-9-7` | `DK-9.5-9.7` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.7) as reconstructed in the distributable TeX. |
| 237 | `DK-9.8.weinberger-sine-square` | `DK-9.8` | `external_result_not_dk_result` | — | Weinberger method gives the displayed sine-square estimate from Ritz upper/lower bounds and the 500 separation. |
| 238 | `DK-9.8.lehmann-best-lower-bounds` | `DK-9.8` | `external_result_not_dk_result` | — | The best lower bounds deducible from the stated 2+1 data are the two lower eigenvalues of the displayed 3x3 matrix. |
| 239 | `DK-9.8.lower-bound-asymptotic` | `DK-9.8` | `external_result_not_dk_result` | — | The source records the strict inequality and O(epsilon^4) asymptotic for alpha_hat-alpha_check. |
| 240 | `DK-9.8.angle-meaning-distinction` | `DK-9.8` | `section9_worked_example_not_result` | — | phi_k are individual trial-vector-to-subspace angles whereas theta1 is the largest subspace angle. |
| 241 | `DK-9.8.sine-square-sum-identity` | `DK-9.8` | `section9_worked_example_not_result` | — | sin^2 phi1+sin^2 phi2 = sin^2 theta1+sin^2 theta2. |
| 242 | `DK-9.8.direct-one-vector-sharper-bounds` | `DK-9.8` | `section9_worked_example_not_result` | — | Theorem 6.3 applied to each trial vector gives the displayed sharper tan phi_k bounds. |
| 243 | `DK-9.8.methods-complementary` | `DK-9.8` | `section9_worked_example_not_result` | — | The source concludes the two methods are complementary rather than one supplanting the other. |
| 244 | `DK-9.8.eq-9-8` | `DK-9.8` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.8) as reconstructed in the distributable TeX. |
| 245 | `DK-9-infinite-residual-counterexample.l2-geometric-vector-example` | `DK-9-infinite-residual-counterexample` | `section9_worked_example_not_result` | — | The geometric sequence e and diagonal operator give a trial vector just outside the operator domain. |
| 246 | `DK-9-infinite-residual-counterexample.arbitrarily-small-domain-repair` | `DK-9-infinite-residual-counterexample` | `section9_worked_example_not_result` | — | The source asserts an arbitrarily small modification repairs the domain defect. |
| 247 | `DK-9-infinite-residual-counterexample.rayleigh-quotient` | `DK-9-infinite-residual-counterexample` | `section9_worked_example_not_result` | — | The formal Rayleigh quotient is 1+mu. |
| 248 | `DK-9-infinite-residual-counterexample.residual-infinite` | `DK-9-infinite-residual-counterexample` | `section9_worked_example_not_result` | — | The residual has infinite norm so the paper residual theorems give no estimate. |
| 249 | `DK-9-infinite-residual-counterexample.weinberger-still-applies` | `DK-9-infinite-residual-counterexample` | `section9_worked_example_not_result` | — | Independent lower eigenvalue bounds still allow the displayed Weinberger estimate. |
| 250 | `DK-9-infinite-residual-counterexample.best-lower-bound-result` | `DK-9-infinite-residual-counterexample` | `section9_worked_example_not_result` | — | At the best lower bounds the true sin theta=mu satisfies mu<=mu/sqrt(1-mu). |
| 251 | `DK-9.9-9.11.angle-factorization` | `DK-9.9-9.11` | `section9_worked_example_not_result` | — | cos omega_k=cos eta_k cos psi_k and omega_k^2<=psi_k^2+eta_k^2. |
| 252 | `DK-9.9-9.11.schur-correction-bound` | `DK-9.9-9.11` | `section9_worked_example_not_result` | — | The Schur correction is bounded by the displayed off-diagonal 2x2 matrix and operator inequalities. |
| 253 | `DK-9.9-9.11.tan2-psi-bound` | `DK-9.9-9.11` | `section9_worked_example_not_result` | — | The tan2 theorem yields the displayed bound for psi_k. |
| 254 | `DK-9.9-9.11.acute-psi-selection` | `DK-9.9-9.11` | `section9_worked_example_not_result` | — | Theorem 8.1 selects 0<=psi_k<pi/4 and yields the stated arctan bound. |
| 255 | `DK-9.9-9.11.eta-bound` | `DK-9.9-9.11` | `section9_worked_example_not_result` | — | Equation (9.10) yields the displayed tan eta_k bound. |
| 256 | `DK-9.9-9.11.final-omega-bounds` | `DK-9.9-9.11` | `section9_worked_example_not_result` | — | Combining psi_k and eta_k yields the two final omega_k bounds. |
| 257 | `DK-9.9-9.11.best-possible-3x3-claim` | `DK-9.9-9.11` | `deferred_unproved_claim` | — | The source says the best possible bound from the stated data is the coordinate/eigenvector angle of the 3x3 comparison matrix. |
| 258 | `DK-9.9-9.11.best-possible-proof-deferred` | `DK-9.9-9.11` | `deferred_unproved_claim` | — | Proof of that best-possible assertion is deferred to the unresolved three-way-subspace Question 10.2. |
| 259 | `DK-9.9-9.11.eq-9-9` | `DK-9.9-9.11` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.9) as reconstructed in the distributable TeX. |
| 260 | `DK-9.9-9.11.eq-9-10` | `DK-9.9-9.11` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.10) as reconstructed in the distributable TeX. |
| 261 | `DK-9.9-9.11.eq-9-11` | `DK-9.9-9.11` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.11) as reconstructed in the distributable TeX. |
| 262 | `DK-10.1.question` | `DK-10.1` | `open_question` | — | With only pairwise spectral distance delta, how sharply can Theta0 be bounded in terms of R? |
| 263 | `DK-10.2.three-way-setup` | `DK-10.2` | `definition_not_result` | — | Three-way orthogonal decompositions are encoded by the 3x3 block matrix E_i*F_j. |
| 264 | `DK-10.2.question` | `DK-10.2` | `open_question` | — | Can nearby reducing three-way decompositions be estimated through off-diagonal blocks analogously to the two-way theory? |
| 265 | `DK-10.3.question` | `DK-10.3` | `open_question` | — | Find best possible bounds combining eigenvalue and eigenvector changes. |
| 266 | `DK-10.4.spectral-functional-calculus` | `DK-10.4` | `definition_not_result` | — | The source recalls f(A) from the spectral resolution of self-adjoint A. |
| 267 | `DK-10.4.step-function-specialization` | `DK-10.4` | `section10_motivation_not_result` | — | For the gap step function under tan2 hypotheses, f(A)=P, f(A+H)=Q, f(A0)=I. |
| 268 | `DK-10.4.ambient-functional-change` | `DK-10.4` | `section10_motivation_not_result` | — | \|\|f(A+H)-f(A)\|\|=\|\|Q-P\|\|=\|\|sin Theta\|\|. |
| 269 | `DK-10.4.ambient-tan2-bound` | `DK-10.4` | `restatement_of_counted_result` | — | delta\|\|tan 2Theta\|\|<=2\|\|H\|\|. |
| 270 | `DK-10.4.directed-functional-change` | `DK-10.4` | `section10_motivation_not_result` | — | \|\|(f(A+H)-f(A))E0\|\|=\|\|Qperp E0\|\|=\|\|sin Theta0\|\|. |
| 271 | `DK-10.4.directed-tan2-bound` | `DK-10.4` | `restatement_of_counted_result` | — | delta\|\|tan 2Theta0\|\|<=2\|\|R\|\|. |
| 272 | `DK-10.4.question` | `DK-10.4` | `open_question` | — | Seek analogous perturbation bounds for more general functions f. |

# Final independent conclusion

- **All 272 source-fidelity atoms reviewed for omission/classification:** yes / no
- **All 29 counted DK-established results reviewed against their exact printed boundaries:** yes / no
- **29 currently terminal results independently reconfirmed:** yes / no
- **0 currently nonterminal/pending results resolved by this audit:** yes / no
- **Any excluded fidelity atom that actually belongs to a counted result statement:** yes / no
- **Any Davis--Kahan-established named/headline result missing from the 29-result inventory:** yes / no
- **Any non-established/open/deferred material incorrectly included in the denominator:** yes / no
- **Every nonlocal source-semantics dependency adjudicated (paper-faithful / illicit strengthening / uncertain):** yes / no
- **Any Lean statement carrying a hypothesis the printed source does not impose, that the packet did NOT disclose:** yes / no
- **Compiler certificate clean and complete:** yes / no
- **Is the repository's explicitly limited claim of 100% result-level Davis--Kahan 1970 formalization justified?** yes / no / uncertain

## Findings requiring action

1. _none recorded yet_
