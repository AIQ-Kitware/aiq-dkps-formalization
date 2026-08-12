# Davis--Kahan 1970 independent statement audit packet

This packet is organized one source claim at a time. The TeX passages come directly from the checked-in transformative, source-order reconstruction `DavisKahan1970_part_III.tex`; they are the repository's distributable semantic audit specification. The census status is a claim to audit, not evidence of semantic fidelity.

Compiler evidence, source status, and hostile semantic certification are intentionally separate. A compiler certificate establishes that registered declarations elaborate against `DavisKahan.All`; the maintained `completion_certification` records whether the current passage has already survived an adversarial semantic review, and the auditor must independently confirm or overturn that judgement.

- Statement map: `dev/davis-kahan-1970-statement-map.json`
- Distributable source specification: `prose/distilled_literature/DavisKahan1970_part_III.tex`
- Census: `dev/davis-kahan-1970-full-source-census.json`
- Registered rows: **49**
- Mathematical completion obligations: **46**
- Compiler certificate: **not supplied**. The theorem-type boxes below are placeholders; do not infer compilation from this static packet.

## Verdict vocabulary

Use one of: **PASS exact**, **PASS refuted**, **FAIL scope**, **FAIL conclusion**, **FAIL missing clause**, **FAIL source specification**, or **UNCERTAIN**.

At the end, separately list any mathematical claim found in the distributable source specification that is not represented by a row in the statement map.

## 1. S1-block-residual — Two reducing decompositions and the residual

- **Source anchor:** Section 1, equations (1.1)–(1.8)
- **Source kind:** `construction`
- **Completion obligation:** `true`
- **Census claim:** `partial_or_wrapper_missing` / `proved_in_build`
- **Hostile completion certification:** `reopened_math`
- **Source-specification passage SHA-256:** `fe0395b4f9940b40576035b37c919996ecae46afc37cd384d4c0ad4851992699`

### Registered distributable source-specification passage

~~~~tex
Let $\Hsp$ be a separable Hilbert space, real or complex; finite dimensionality is not assumed.  In the main bounded setting $A=A^*$ and $A+H=(A+H)^*$ are bounded.  The paper also allows self-adjoint unbounded $A$ when the later domain conditions are met.

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

### Semantic audit clauses

- **`S1-block-residual.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Equation1_8`, `TauCeti.DavisKahan1970.equation1_8_eq_perturbation_comp`, `TauCeti.DavisKahan1970.equation1_8_norm_sq_eq_diagonal_add_offDiagonal`, `TauCeti.DavisKahan1970.equation1_8_norm_offDiagonal_le`

### Known hostile-review holes

- **`missing_source_facing_statement`:** The registered TeX includes the standard residual-to-eigenvalue consequence: ordered eigenvalues lambda_j with sum_j (alpha_j-lambda_j)^2 <= ||R||_sq^2 and |alpha_j-lambda_j| <= ||R||_1. The hostile review found no source-facing Lean declaration for these displayed conclusions.
- **`audit_mapping`:** `equation1_8_residual_norm_minimized_by_rayleighQuotient` now proves the printed Rayleigh--Ritz minimization statement but is not registered as primary evidence for this row.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The registered TeX includes the standard residual-to-eigenvalue consequence: ordered eigenvalues lambda_j with sum_j (alpha_j-lambda_j)^2 <= ||R||_sq^2 and |alpha_j-lambda_j| <= ||R||_1. The hostile review found no source-facing Lean declaration for these displayed conclusions. `equation1_8_residual_norm_minimized_by_rayleighQuotient` now proves the printed Rayleigh--Ritz minimization statement but is not registered as primary evidence for this row.

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

## 2. S1-ui-norms — Unitary-invariant norms, angle operators, and direct-rotation setup

- **Source anchor:** Section 1, equations (1.9)–(1.18)
- **Source kind:** `framework`
- **Completion obligation:** `true`
- **Census claim:** `partial_or_wrapper_missing` / `proved_in_build`
- **Hostile completion certification:** `reopened_math`
- **Source-specification passage SHA-256:** `c64c6651719e212086fce5c8b32caaea014ec323b5438335d8e3d3aba8f7ba9f`

### Registered distributable source-specification passage

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
The singular values of $S_0$ are $\sin\theta_k$, where $\theta_k$ are the spectral/singular-angle data of $\Theta_0$; the nonzero angle data of $\Theta$ occur twice, once from each side.  In every unitary-invariant norm,
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

### Semantic audit clauses

- **`S1-ui-norms.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm`, `TauCeti.DavisKahan.ExactSinTheta.paperKyFanNorm`, `TauCeti.DavisKahan1970.equation1_12`, `TauCeti.DavisKahan1970.equation1_13_compressions`, `TauCeti.DavisKahan1970.equation1_13_reSum`

### Known hostile-review holes

- **`math`:** PDF re-audit restored the cosine-law identity after (1.14). The remaining hostile issue is mathematical/scope: the distributable source asserts U = exp(J Theta) = cos Theta + J sin Theta in general Hilbert-space scope, while the explicit exponential theorem located by the audit is finite-dimensional.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: PDF re-audit restored the cosine-law identity after (1.14). The remaining hostile issue is mathematical/scope: the distributable source asserts U = exp(J Theta) = cos Theta + J sin Theta in general Hilbert-space scope, while the explicit exponential theorem located by the audit is finite-dimensional.

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
- **Hostile completion certification:** `accepted`
- **Source-specification passage SHA-256:** `8e5e36e64c718f1cdb002dd3c5a191c8919fa22bad64020bdbf8f22adb6a3f72`

### Registered distributable source-specification passage

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
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `c85f8a2839187dd9ae4d020608816821c3b1f30e401eb5e52d4cbce093e82b3c`

### Registered distributable source-specification passage

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

### Semantic audit clauses

- **`S2-tan-theta.directed`:** Directed conclusion: delta * ||tan Theta_0|| <= ||R||.
  - Review declarations: `TauCeti.DavisKahanTheory.partIII_tanTheta_ritzResidual_uiNorm`
- **`S2-tan-theta.ambient`:** Ambient conclusion: delta * ||tan Theta|| <= ||H||, with the ambient angle rather than Theta_0.
  - Review declarations: `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm`, `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_real`

### Known hostile-review holes

- **`audit_mapping`:** The mapped real ambient declaration accepts an explicit transversality premise. A source-hypotheses-only real theorem (`tanTheta_wholeSpace_paperUINorm_real_of_crossedDefectsEquivalent`) exists, so this is evidence-selection debt rather than missing mathematics.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The mapped real ambient declaration accepts an explicit transversality premise. A source-hypotheses-only real theorem (`tanTheta_wholeSpace_paperUINorm_real_of_crossedDefectsEquivalent`) exists, so this is evidence-selection debt rather than missing mathematics.

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

Source location candidates: `DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:210`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent`

Source location candidates: `Challenge/DavisKahan1970/Conformance.lean:320`, `DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:1275`

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
- `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_real` — DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:210
- `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real_infinite` — DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:457
- `TauCeti.DavisKahan1970.theorem6_3_all_kyFan_core_infiniteTrial_real` — DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:189
- `TauCeti.DavisKahan1970.theorem63DirectedSineBlockReal` — DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:54
- `TauCeti.DavisKahan1970.theorem63ResidualReal` — DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:60
- `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real` — DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:418
- `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent` — Challenge/DavisKahan1970/Conformance.lean:320, DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:1275
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
- **Hostile completion certification:** `accepted`
- **Source-specification passage SHA-256:** `7da711fdbd912b64b5aa6f2efc5c4255bcbe796831a18b99c92712024b81c70b`

### Registered distributable source-specification passage

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

### Semantic audit clauses

- **`S2-sin-two-theta.directed`:** Directed conclusion: delta * ||sin(2 Theta_0)|| <= 2 ||R||.
  - Review declarations: `TauCeti.DavisKahanTheory.partIII_sinTwoTheta_uiNorm`
- **`S2-sin-two-theta.ambient`:** Ambient conclusion: delta * ||sin(2 Theta)|| <= 2 ||H||.
  - Review declarations: `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm`, `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm_real`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahanTheory.partIII_sinTwoTheta_uiNorm`

Source location candidates: `Challenge/DavisKahan1970/Conformance.lean:135`, `DavisKahan/Sources/DavisKahan1970/PartIII.lean:150`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm`

Source location candidates: `Challenge/DavisKahan1970/Conformance.lean:390`, `DavisKahan/Sources/DavisKahan1970/SinTwoThetaWholeSpace.lean:723`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:252`

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

- `TauCeti.DavisKahanTheory.partIII_sinTwoTheta_uiNorm` — Challenge/DavisKahan1970/Conformance.lean:135, DavisKahan/Sources/DavisKahan1970/PartIII.lean:150
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
- `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm` — Challenge/DavisKahan1970/Conformance.lean:390, DavisKahan/Sources/DavisKahan1970/SinTwoThetaWholeSpace.lean:723
- `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm_real` — DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:252
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
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Hostile completion certification:** `accepted`
- **Source-specification passage SHA-256:** `5c5b96c1cc563a42d13b8b4e06989c19ff82ec8ed6958f3da78d67dc9b2b7830`

### Registered distributable source-specification passage

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

### Semantic audit clauses

- **`S2-tan-two-theta.hypotheses`:** Printed source hypotheses only: ordered spectral gap between A_0 and A_1 plus H_0 = H_1 = 0; no independent pole-exclusion or perturbed-Q-block placement hypothesis. The exact directed and ambient wrappers derive pole exclusion internally from these hypotheses.
  - Review declarations: `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_exact`, `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_real_exact`, `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_exact`, `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real_exact`
- **`S2-tan-two-theta.directed`:** Directed conclusion: delta * ||tan(2 Theta_0)|| <= 2 ||R|| for every source unitarily invariant norm. The complex source-facing wrapper upgrades the branch-free all-Ky-Fan directed-corner estimate to an arbitrary PaperUnitaryInvariantNorm and derives pole exclusion from the printed spectral hypotheses; the real exact wrapper transports the same statement through the canonical complexification convention already used for the paper's real directed angle while descending the residual norm to the real block.
  - Review declarations: `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_exact`, `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_real_exact`, `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_branchFree`, `TauCeti.DavisKahan1970.paperTanTwoDirectedCornerR`
- **`S2-tan-two-theta.ambient`:** Ambient conclusion: delta * ||tan(2 Theta)|| <= 2 ||H|| for every source unitarily invariant norm, from only the printed hypotheses. Exact source-facing complex and real wrappers derive the pole exclusion internally and the modulus bridge identifies the branch-free positive representative with the literal signed functional-calculus tan(2 Theta) at the level seen by source UI norms.
  - Review declarations: `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_exact`, `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real_exact`, `TauCeti.DavisKahan1970.paperAbsTanTwoAngleOperatorC_eq_modulus_paperTanTwoAngleOperatorC`

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_exact`

Source location candidates: `Challenge/DavisKahan1970/Conformance.lean:441`, `DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean:1160`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_real_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:362`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_exact`

Source location candidates: `Challenge/DavisKahan1970/Conformance.lean:531`, `DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean:1297`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:433`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahanTheory.partIII_tanTwoTheta_opNorm` — Challenge/DavisKahan1970/Conformance.lean:154, DavisKahan/Sources/DavisKahan1970/PartIII.lean:163
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
- `TauCeti.DavisKahan1970.tanTwoTheta_branchFree_paperUINorm_arbitrarySubspace` — Challenge/DavisKahan1970/Conformance.lean:411, DavisKahan/Sources/DavisKahan1970/TanTwoThetaBranchFree.lean:140
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
- `TauCeti.DavisKahan1970.paperTanTwoAngleOperatorC_eq_modulus_blockRepresentative` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:922
- `TauCeti.DavisKahan1970.paperTanTwoBlockRepresentative_lowerBlock` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:1119
- `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_all_kyFan` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:1290
- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_all_kyFan` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:1498
- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:1567
- `TauCeti.DavisKahanExt.paperTanTwoAngleOperatorR` — DavisKahan/Geometry/Angle/PaperOperatorAngleReal.lean:132
- `TauCeti.DavisKahanExt.complexify_paperTanTwoAngleOperatorR` — DavisKahan/Geometry/Angle/PaperOperatorAngleReal.lean:172
- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real` — DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:304
- `TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorC` — DavisKahan/Geometry/Angle/PaperTanAngle.lean:188
- `TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorC_nonneg` — DavisKahan/Geometry/Angle/PaperTanAngle.lean:201
- `TauCeti.DavisKahanExt.paperAbsTanTwoAngleOperatorC_eq_paperTanTwoAngleOperatorC` — DavisKahan/Geometry/Angle/PaperTanAngle.lean:209
- `TauCeti.DavisKahan1970.isUnit_one_sub_two_mul_paperProjectorDifference_sq_of_cos_two_ne_zero` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:405
- `TauCeti.DavisKahan1970.paperAbsTanTwo_sq_mul_cos_two_sq` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:453
- `TauCeti.DavisKahan1970.paperAbsTanTwoAngleOperatorC_eq_modulus_blockRepresentative` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:875
- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_all_kyFan_of_corner` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:1424
- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_of_corner` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:1531
- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_all_kyFan_branchFree` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean:1107
- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_branchFree` — Challenge/DavisKahan1970/Conformance.lean:511, DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean:1126
- `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_all_kyFan_branchFree` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean:1008
- `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_branchFree` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean:1043
- `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_exact` — Challenge/DavisKahan1970/Conformance.lean:441, DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean:1160
- `TauCeti.DavisKahan1970.paperTanTwoDirectedCornerR` — DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:176
- `TauCeti.DavisKahan1970.paperProjectionBlock_complexifySubmodule_real` — DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:187
- `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_real_exact` — DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:362
- `TauCeti.DavisKahan1970.paperAbsTanTwoAngleOperatorC_eq_modulus_paperTanTwoAngleOperatorC` — DavisKahan/Sources/DavisKahan1970/TanTwoThetaWholeSpace.lean:572
- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_exact` — Challenge/DavisKahan1970/Conformance.lean:531, DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean:1297
- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real_exact` — DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:433

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
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `fb0eaba8db2c7f46d5005c12d734b0dad4f4ad83097696e71a3954e68ffb8efb`

### Registered distributable source-specification passage

~~~~tex
The constants in all four theorem families are asserted to be best possible.  Two-dimensional examples attain the constants, and orthogonal direct sums of such examples can be arranged so that equality occurs simultaneously for all unitary-invariant norms.  When the perturbation depends linearly on a small parameter $\varepsilon$, the four estimates have the same first-order asymptotic behavior as $\varepsilon\to0$.
~~~~

### Semantic audit clauses

- **`S2-sharpness.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahanTheory.tanTheta_model_sourceSharpness`, `TauCeti.DavisKahanTheory.tanTwoTheta_model_sourceSharpness`, `TauCeti.DavisKahanTheory.sinTheta_constant_optimal`, `TauCeti.DavisKahanTheory.sinTwoTheta_constant_optimal`, `TauCeti.DavisKahanTheory.single_double_sine_tangent_ratios_tendsto_one`, `TauCeti.DavisKahanTheory.sinTheta_model_equality`

### Known hostile-review holes

- **`audit_atomization`:** The hashed passage asserts optimal constants, two-dimensional equality models, direct-sum simultaneous equality for all unitary-invariant norms, and first-order sharpness. Existing sharpness machinery is richer than the current review mapping, but these separable claims are not individually certified.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The hashed passage asserts optimal constants, two-dimensional equality models, direct-sum simultaneous equality for all unitary-invariant norms, and first-order sharpness. Existing sharpness machinery is richer than the current review mapping, but these separable claims are not individually certified.

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
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `7f098b2419b68b1002016fbc6983ccd57639127da6c28456751248a9c33cf43a`

### Registered distributable source-specification passage

~~~~tex
The paper states the four main results for infinite as well as finite dimensional separable Hilbert spaces and for arbitrary unitary-invariant norms.  The main exposition begins with bounded Hermitian $A$ and $A+H$, but the results are also intended for unbounded self-adjoint $A$ when $\operatorname{dom}(H)$ contains $\operatorname{dom}(A)$ and the expressions used in the estimates are meaningful.  Useful unbounded conclusions require the pertinent perturbation or residual to extend boundedly.  The spectral intervals in the gap hypotheses may be half-infinite, and the remaining spectra may be unbounded.  The additional analytic work for these cases is concentrated in Theorem~5.2 and the Appendix to Section~6.
~~~~

### Semantic audit clauses

- **`S2-unbounded-scope.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing_real`, `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_of_reducing_real`, `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_real`, `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_real`, `TauCeti.DavisKahan1970.theorem6_3_all_kyFan_core_infiniteData_real`, `TauCeti.DavisKahan1970.canonical_generalizedSinTheta`

### Known hostile-review holes

- **`audit_atomization`:** The passage asserts the full infinite-dimensional/unbounded/arbitrary-UI-norm scope for all four headline theorem families. The current evidence is a sample of endpoints rather than an explicit clause-by-clause four-family scope certificate.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The passage asserts the full infinite-dimensional/unbounded/arbitrary-UI-norm scope for all four headline theorem families. The current evidence is a sample of endpoints rather than an explicit clause-by-clause four-family scope certificate.

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

- **Source anchor:** Section 3 setup, equations (3.1)--(3.4), and Definition 3.1
- **Source kind:** `definition`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `a20649b8dd41ae1561494af20da1e2ea6ada223a3c5b2c4156bd2a795fdfd092`

### Registered distributable source-specification passage

~~~~tex
Section~3 ignores $A$ and $A+H$ and studies the two projectors $P=E_0E_0^*$ and $Q=F_0F_0^*$.  All block representations continue to use the $E_0\oplus E_1$ decomposition.  Thus
\begin{equation}
 Q\sim
 \begin{pmatrix}
 E_0^*QE_0&E_0^*QE_1\\
 E_1^*QE_0&E_1^*QE_1
 \end{pmatrix}.
 \tag{3.1}
\end{equation}
For a unitary
\[
 V\sim\begin{pmatrix}C_0&-S_1\\S_0&C_1\end{pmatrix}
\]
carrying $P\Hsp$ onto $Q\Hsp$, unitarity is equivalently expressed by
\begin{equation}
 \begin{pmatrix}
 C_0^*C_0+S_0^*S_0&-C_0^*S_1+S_0^*C_1\\
 -S_1^*C_0+C_1^*S_0&S_1^*S_1+C_1^*C_1
 \end{pmatrix}
 =\begin{pmatrix}I&0\\0&I\end{pmatrix},
 \tag{3.2}
\end{equation}
\begin{equation}
 \begin{pmatrix}
 C_0C_0^*+S_1S_1^*&C_0S_0^*-S_1C_1^*\\
 S_0C_0^*-C_1S_1^*&S_0S_0^*+C_1C_1^*
 \end{pmatrix}
 =\begin{pmatrix}I&0\\0&I\end{pmatrix}.
 \tag{3.3}
\end{equation}
Consequently $S_0$ and $S_1$ have the same nonzero singular values, except that unequal nullities of $C_0$ and $C_0^*$ can contribute initial strings of singular values equal to $1$ on one side.

A unitary solution of $VP=QV$ is a \emph{direct rotation} from $P\Hsp$ to $Q\Hsp$ when
\[
 C_0\ge0,\qquad C_1\ge0,\qquad S_1=S_0^*.
\]
The source reserves $U$ for direct rotations.  In the positive-diagonal case, equations (3.2)--(3.3) give
\begin{equation}
 C_0S_1=S_0^*C_1,
 \qquad
 C_0S_0^*=S_1C_1,
 \tag{3.4}
\end{equation}
which are used in the existence and uniqueness analysis.
~~~~

### Semantic audit clauses

- **`DK-3.1-def.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.complex_directRotation`, `TauCeti.DavisKahan1970.real_directRotation`, `TauCeti.DavisKahan1970.real_directRotation_orthogonal`, `TauCeti.DavisKahan1970.real_directRotation_intertwines`, `TauCeti.DavisKahan1970.real_directRotation_diagonalBlock`, `TauCeti.DavisKahan1970.real_directRotation_complementaryDiagonalBlock`

### Known hostile-review holes

- **`audit_atomization`:** The block contains equations (3.1)-(3.4), unitarity block identities, singular-value/nullity assertions, and the direct-rotation definition. The current generic `.whole` clause does not certify those assertions individually.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The block contains equations (3.1)-(3.4), unitarity block identities, singular-value/nullity assertions, and the direct-rotation definition. The current generic `.whole` clause does not certify those assertions individually.

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
- **Hostile completion certification:** `accepted`
- **Source-specification passage SHA-256:** `62638f6ec5fe84cc6ddad8a423f99d5b024c0f6ff2e1aa7a37f3d9604a77b609`

### Registered distributable source-specification passage

~~~~tex
The pair $P\Hsp,Q\Hsp$ is in the \emph{acute case} exactly when both crossing intersections vanish:
\[
 P\Hsp\cap Q^\perp\Hsp=\{0\},
 \qquad
 P^\perp\Hsp\cap Q\Hsp=\{0\}.
\]
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
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `ff945cb6247987becf0eec9e3c5fd945ba2df2d2b8756cea6df2c7ebd00213d4`

### Registered distributable source-specification passage

~~~~tex
In the acute case, a direct rotation exists and is unique.  Moreover positivity of the diagonal blocks, $C_0,C_1\ge0$, already characterizes it among unitaries carrying $P\Hsp$ onto $Q\Hsp$: the polar-decomposition relations force the off-diagonal condition $S_1=S_0^*$ because the relevant kernels vanish in the acute case.
~~~~

### Semantic audit clauses

- **`DK-3.1-prop.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.complex_directRotation`, `TauCeti.DavisKahan1970.complex_directRotation_unique`, `TauCeti.DavisKahan1970.complex_directRotation_diagonalBlock`, `TauCeti.DavisKahan1970.complex_directRotation_complementaryDiagonalBlock`, `TauCeti.DavisKahan1970.complex_directRotation_reflectionConjugate`, `TauCeti.DavisKahan1970.complex_directRotation_of_diagonalBlocks`

### Known hostile-review holes

- **`audit_mapping`:** Primary evidence is complex-centric even though the paper ambient convention is real or complex and real counterparts exist elsewhere in the census. Register exact real evidence explicitly.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: Primary evidence is complex-centric even though the paper ambient convention is real or complex and real counterparts exist elsewhere in the census. Register exact real evidence explicitly.

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
- **Census claim:** `partial_or_wrapper_missing` / `proved_in_build`
- **Hostile completion certification:** `reopened_math`
- **Source-specification passage SHA-256:** `3824155c8b919c0b61e9eb7bdc7b822214fbb6d6abfa95f7e7eb5eac2a73c09a`

### Registered distributable source-specification passage

~~~~tex
Outside the acute case a direct rotation exists iff the two crossing subspaces have the same dimension:
\begin{equation}
 \dim(P\Hsp\cap Q^\perp\Hsp)
 =\dim(P^\perp\Hsp\cap Q\Hsp).
 \tag{3.5}
\end{equation}
When it exists it need not be unique.  On the two crossing subspaces a direct rotation satisfies $U^2x=-x$.  The source also gives an infinite-dimensional bilateral-shift example showing that the equal-dimension conditions (1.5) for $P,Q$ do not by themselves imply (3.5).
~~~~

### Semantic audit clauses

- **`DK-3.2-prop.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_exists_iff_crossedDefectsEquivalent`, `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_parameterized_nonuniqueness`, `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_exists_iff_crossedDefectsEquivalent_real`

### Known hostile-review holes

- **`missing_source_facing_statement`:** The source passage says that on the two crossing subspaces every direct rotation satisfies U^2 x = -x. The hostile review did not find an exported source-facing theorem with that statement, although related reflection-product ingredients exist.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The source passage says that on the two crossing subspaces every direct rotation satisfies U^2 x = -x. The hostile review did not find an exported source-facing theorem with that statement, although related reflection-product ingredients exist.

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
- **Census claim:** `partial_or_wrapper_missing` / `proved_in_build`
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `dbc77fc4c71873dbd8c706d68f5bb4ea28064a4d930ccb58c91c2640ab7bf382`

### Registered distributable source-specification passage

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

### Semantic audit clauses

- **`DK-3.3-prop.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.complex_directRotation_sq`, `TauCeti.DavisKahan1970.complex_directRotation_hermitianPart`, `TauCeti.DavisKahan1970.complex_directRotation_principal_of_sq`, `TauCeti.DavisKahan1970.real_directRotation_sq`, `TauCeti.DavisKahan1970.real_directRotation_hermitianPart`, `TauCeti.DavisKahan1970.real_directRotation_principal_of_sq`

### Known hostile-review holes

- **`mapping`:** PDF re-audit restored source equation (3.7) exactly in the distributable TeX. The source-specification defect is closed; the row remains reopened until the new atomic equation (3.7) and the other Proposition 3.3 atoms are explicitly bound to exact Lean evidence.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: PDF re-audit restored source equation (3.7) exactly in the distributable TeX. The source-specification defect is closed; the row remains reopened until the new atomic equation (3.7) and the other Proposition 3.3 atoms are explicitly bound to exact Lean evidence.

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
- **Census claim:** `compiled_specialization` / `proved_in_build`
- **Hostile completion certification:** `reopened_math`
- **Source-specification passage SHA-256:** `a4914037fecd9b2f6193105f137f3a59d160e47ca70747bb4a6c430477038990`

### Registered distributable source-specification passage

~~~~tex
Under the same direct-rotation setup, if
\[
 C_0^2\ge\tfrac12
\]
(equivalently, the relevant principal angles do not exceed $\pi/4$), then $U^2$ is itself the direct rotation carrying $Q_-\Hsp$ onto $Q\Hsp$.
~~~~

### Semantic audit clauses

- **`DK-3.4-prop.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan.Frontier.Section3.proposition3_4_source_full`, `TauCeti.DavisKahan.Frontier.Section3.proposition3_4_source_eq_directRotation`

### Known hostile-review holes

- **`scope_gap`:** `proposition3_4_source_full` is explicitly complex-valued. The paper does not restrict Proposition 3.4 to the complex scalar field; an exact real source-facing counterpart was not located.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: `proposition3_4_source_full` is explicitly complex-valued. The paper does not restrict Proposition 3.4 to the complex scalar field; an exact real source-facing counterpart was not located.

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
- **Hostile completion certification:** `accepted`
- **Source-specification passage SHA-256:** `c596c36a00cab2889d9af204a420d6746d77273cc66e9a3268dc91891902987f`

### Registered distributable source-specification passage

~~~~tex
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
- **Hostile completion certification:** `accepted`
- **Source-specification passage SHA-256:** `2661dd05c08e61c06c54ce50c66032413a3c958bb7cda1b28638548253e30d2c`

### Registered distributable source-specification passage

~~~~tex
Under the hypotheses of Theorem~3.1, if $PQ^\perp P$ is compact, the complete invariants reduce to the eigenvalues of $\Theta_0,\Theta_1$, counted with multiplicity.  The eigenvalues of $\Theta_0$ may be any sequence
\[
 \pi/2\ge\theta_1\ge\theta_2\ge\cdots\to0,
\]
together with a possible eigenvalue $0$; $\Theta_1$ has the same nonzero eigenvalues and may differ only in the multiplicity of $0$.
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
- **Census claim:** `partial_or_wrapper_missing` / `proved_in_build`
- **Hostile completion certification:** `reopened_math`
- **Source-specification passage SHA-256:** `bdabc4530ed8ad8040dfe34d4a1071b2b52d3563d3e0e5bb9de9868287999a4e`

### Registered distributable source-specification passage

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

### Semantic audit clauses

- **`DK-3.5-prop.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.proposition3_5_directRotation_resolution`, `TauCeti.DavisKahan1970.proposition3_5_commutations`, `TauCeti.DavisKahan1970.proposition3_5_eigenvector_angle`, `TauCeti.DavisKahan1970.proposition3_5_angleEigenspace_eq_fixedCosineSubspace`, `TauCeti.DavisKahan1970.proposition3_5_angleEigenspace_uniqueMaximal`, `TauCeti.DavisKahan1970.proposition3_5_angleOperator`

### Known hostile-review holes

- **`scope_gap`:** The registered passage includes the Hilbert-space identity U = exp(J Theta). The source-facing arbitrary-dimensional Proposition 3.5 surface exposes U = cos Theta + J sin Theta; the explicit exponential theorem located by the review is finite-dimensional.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The registered passage includes the Hilbert-space identity U = exp(J Theta). The source-facing arbitrary-dimensional Proposition 3.5 surface exposes U = cos Theta + J sin Theta; the explicit exponential theorem located by the review is finite-dimensional.

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
- **Hostile completion certification:** `accepted`
- **Source-specification passage SHA-256:** `6ef3d66483655d6bf428a2422d4d26494455fe9cba09939d61a2092809e68a9d`

### Registered distributable source-specification passage

~~~~tex
Interchanging the roles of $P$ and $Q$ leaves the angle operator $\Theta$ unchanged and replaces $J$ by $-J$.
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

- **Source anchor:** Section 4 setup, Proposition 4.1, and equations (4.1)--(4.2)
- **Source kind:** `proposition`
- **Completion obligation:** `true`
- **Census claim:** `partial_or_wrapper_missing` / `proved_in_build`
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `2b3c6a4dc471284a2f9e4f7e4f091d30fd00d0c04ef03648ee469d6e9e110cb3`

### Registered distributable source-specification passage

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

### Semantic audit clauses

- **`DK-4.1-prop.vector`:** First printed formulation: an orthonormal principal-vector family v_k in P H with angle(v_k, V v_k) >= theta_k.
  - Review declarations: `TauCeti.DavisKahan1970.Proposition4_1_compact_orthonormalVectors`, `TauCeti.DavisKahan1970.Proposition4_1_compact_orthonormalVectors_real`
- **`DK-4.1-prop.singular`:** Equivalent singular-value/approximation-number minimality formulation, including the direct-rotation value 2 sin(theta_k/2).
  - Review declarations: `TauCeti.DavisKahan1970.Proposition4_1_compact_orthonormalVectors`, `TauCeti.DavisKahan1970.Proposition4_1_compact_orthonormalVectors_real`, `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute`, `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_real`, `TauCeti.DavisKahan1970.Proposition4_1_directRotationValues`

### Known hostile-review holes

- **`mapping`:** PDF re-audit restored equations (4.1) and (4.2) explicitly in the distributable TeX. The source-specification defect is closed; the row remains reopened until the minimax and pointwise-angle atoms and the headline proposition are explicitly bound to exact Lean evidence.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: PDF re-audit restored equations (4.1) and (4.2) explicitly in the distributable TeX. The source-specification defect is closed; the row remains reopened until the minimax and pointwise-angle atoms and the headline proposition are explicitly bound to exact Lean evidence.

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
- **Hostile completion certification:** `accepted`
- **Source-specification passage SHA-256:** `73cd6caf9a976a811e4836d656d566a66b0f57c7504ff38365d6891b3d75b9ba`

### Registered distributable source-specification passage

~~~~tex
For every unitary-invariant norm,
\[
 \norm{(1-V)P}
\]
is minimized among unitaries carrying $P\Hsp$ onto $Q\Hsp$ by the direct rotation $V=U$.
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
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `a1d36230f960f5b48427a6c4fce26c28327cc9fdff714575e4261c76ae92c4f4`

### Registered distributable source-specification passage

~~~~tex
For every unitary $V$ carrying $P\Hsp$ onto $Q\Hsp$ and every orthonormal basis $\{v_k\}$ of $P\Hsp$,
\[
 \sum_{k=1}^{\infty}\sin^2\angle(v_k,Vv_k)
 \ge
 \sum_{k=1}^{\infty}\sin^2\theta_k,
\]
with the inequality also valid when the right-hand side is infinite.  The proof identifies the lower bound with $\operatorname{tr}(S_0^*S_0)$.
~~~~

### Semantic audit clauses

- **`DK-4.2-prop.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Proposition4_2_infiniteDimensional`, `TauCeti.DavisKahan1970.tsum_displacementAngleSineSqR_ge_tsum_sq_sin_principalAngleSequence`

### Known hostile-review holes

- **`audit_atomization`:** The main inequality appears formalized, but the source block also records the trace/basis identification used in the proof. The terminal row does not separately bind that preserved mathematical assertion to Lean evidence.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The main inequality appears formalized, but the source block also records the trace/basis identification used in the proof. The terminal row does not separately bind that preserved mathematical assertion to Lean evidence.

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
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `efb61fbf15adb18ac47572bb82096f44ac2bd356072eaa15cd006cec8cc14dac`

### Registered distributable source-specification passage

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

### Semantic audit clauses

- **`DK-4.3-prop.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Proposition4_3_infiniteDimensional_idealGauge`

### Known hostile-review holes

- **`audit_mapping`:** Broader nonacute and real source theorems exist, but the primary row evidence is narrower and the hashed block contains equations (4.3)-(4.6) plus the precise UI-norm limitation. Rebind/atomize the complete source scope.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: Broader nonacute and real source theorems exist, but the primary row evidence is narrower and the hashed block contains equations (4.3)-(4.6) plus the precise UI-norm limitation. Rebind/atomize the complete source scope.

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

## 23. DK-4.4-prop — Full-displacement counterexamples and Proposition 4.4 as printed

- **Source anchor:** Examples 4.1–4.2 and Proposition 4.4
- **Source kind:** `proposition`
- **Completion obligation:** `true`
- **Census claim:** `refuted_as_transcribed` / `proved_in_build`
- **Hostile completion certification:** `accepted`
- **Source-specification passage SHA-256:** `1896dfda86994261bd007a6aeaf1fcd46b1b47e60a197caa7313cc5025ac1194`

### Registered distributable source-specification passage

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
- `TauCeti.DavisKahanTheory.directRotation_fullDisplacement_qnorm` — DavisKahan/FiniteDimensional/DirectRotation/QNorm.lean:69

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
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `38590318e770b1eddea8bb6e6a45126b57c9652588f5e1c6991078f3dd8a6c4a`

### Registered distributable source-specification passage

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

### Semantic audit clauses

- **`DK-5.1-thm.bounded`:** Printed bounded Banach-space theorem with a genuine inverse A^{-1}, its norm bound, an arbitrary compatible cross-operator norm, AX-XB=C, and delta ||X|| <= ||C||.
  - Review declarations: `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_exact`
- **`DK-5.1-thm.interchange`:** Printed prose remark interchanging the roles/hypotheses of A and B.
  - Review declarations: `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_interchanged_exact`
- **`DK-5.1-thm.unboundedA`:** Printed prose extension allowing densely-defined unbounded A while B and X remain bounded.
  - Review declarations: `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_unboundedA`

### Known hostile-review holes

- **`audit_mapping`:** The source block includes the Banach-space inverse-norm form, A/B interchange, and unbounded-left extension. The repository contains strong infrastructure and literal wrappers, but the audit row does not atomically show that every printed clause is represented at real/complex source scope.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The source block includes the Banach-space inverse-norm form, A/B interchange, and unbounded-left extension. The repository contains strong infrastructure and literal wrappers, but the audit row does not atomically show that every printed clause is represented at real/complex source scope.

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
- **Census claim:** `partial_or_wrapper_missing` / `proved_in_build`
- **Hostile completion certification:** `reopened_math`
- **Source-specification passage SHA-256:** `da41db53882bd87b7aba9f8e3b827b46a08f6e6ac0d2e6638d6251d93c20cb5f`

### Registered distributable source-specification passage

~~~~tex
For Hermitian matrices $A,B$ (possibly of different dimensions) with pairwise spectral distance at least $\delta>0$, and $C=AX-XB$, diagonalization gives
\begin{equation}
 \norm{C}_{\mathrm{sq}}\ge\delta\norm{X}_{\mathrm{sq}}.
 \tag{5.1}
\end{equation}
The corresponding operator-norm inequality with constant $1$ can fail.  From (5.1) one still obtains
\begin{equation}
 \norm{C}_1\sqrt{\operatorname{rank}C}\ge\delta\norm{X}_1.
 \tag{5.2}
\end{equation}
The source says (5.2) is not best possible unless $\operatorname{rank}C\le1$, and asks whether the rank factor can be replaced by a universal constant.  Constant $1$ is ruled out by
\[
 X=\begin{pmatrix}3&-3\\-3&1\end{pmatrix},\quad
 A=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
 B=\begin{pmatrix}0&0\\0&2\end{pmatrix},\quad \delta=1,
\]
for which
\[
 \delta\norm{X}_1=2+\sqrt{10}>3\sqrt2=\norm{AX-XB}_1.
\]
~~~~

### Semantic audit clauses

- **`DK-5-hermitian-inequalities.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan.ExactSinTheta.paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap`, `TauCeti.DavisKahan.ExactSinTheta.paperOperatorNorm_sylvester_le_of_pairwiseSpectrumGap`

### Known hostile-review holes

- **`missing_source_facing_statement`:** The TeX states that (5.2) is not best possible unless rank C <= 1. The repository formalizes (5.1), the rank-corrected estimate, and a counterexample showing constant 1 is too small, but the hostile review found no source-facing theorem for this stronger qualitative assertion.
- **`mixed_disposition`:** The same block asks whether the rank factor can be replaced by a universal constant. That open question should be atomically dispositioned instead of being swallowed by a terminal `.whole` clause.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The TeX states that (5.2) is not best possible unless rank C <= 1. The repository formalizes (5.1), the rank-corrected estimate, and a counterexample showing constant 1 is too small, but the hostile review found no source-facing theorem for this stronger qualitative assertion. The same block asks whether the rank factor can be replaced by a universal constant. That open question should be atomically dispositioned instead of being swallowed by a terminal `.whole` clause.

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
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `2078bb97672c50ca247554b198c575e381bd776725924f1333057a2a10fc3d8c`

### Registered distributable source-specification passage

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

### Semantic audit clauses

- **`DK-5.2-thm.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Theorem5_2`, `TauCeti.DavisKahan1970.unbounded_sylvester_intervalExterior_uiNorm_genuineSpectrum`

### Known hostile-review holes

- **`audit_mapping`:** The theorem appears available in both scalar fields, but primary evidence is not explicitly bound clause-by-clause to the paper's full real/complex source scope.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The theorem appears available in both scalar fields, but primary evidence is not explicitly bound clause-by-clause to the paper's full real/complex source scope.

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
- **Hostile completion certification:** `accepted`
- **Source-specification passage SHA-256:** `4154e65f1eb46629c33da85de5866a2751ce9b5e21d9fa3956d2d6d0e677ecbd`

### Registered distributable source-specification passage

~~~~tex
If orthogonal projectors $\Omega(\tau)$ converge strongly to the identity and $\kappa_\nu,\kappa_\nu(\tau)$ are the $\nu$th singular values of $K$ and $K\Omega(\tau)$, respectively, then
\[
 \kappa_\nu(\tau)\longrightarrow\kappa_\nu.
\]
This cutoff lemma lets finite spectral truncations recover the Ky Fan data required in the unbounded arguments.
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
- **Hostile completion certification:** `accepted`
- **Source-specification passage SHA-256:** `3fcdb9152000100900fc421874565b2defe8ccb6cc2a8574154d146c509eb2d5`

### Registered distributable source-specification passage

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
- **Hostile completion certification:** `accepted`
- **Source-specification passage SHA-256:** `fefd468fd43df7f2d9ecb643c21a78aa0f8471b3b3909472925d347e6aa26f63`

### Registered distributable source-specification passage

~~~~tex
For orthogonal projectors $\Omega,\Upsilon$ and every unitary-invariant norm,
\[
 \boxed{\norm{\Omega K\Upsilon+\Omega^\perp K\Upsilon^\perp}\le\norm{K}.}
\]
The proof is the reflection/pinching contraction obtained by averaging $K$ with suitable unitary reflections.
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

## 30. DK-6.1-prop — Sine proof, ambient limitation, and symmetric sine theorem

- **Source anchor:** Section 6 sine proof and Proposition 6.1
- **Source kind:** `proposition`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `ec802eefcfa341b4268ff3fd35bdb06d38211ec9cf5c72138d53e1ffdf5d11ce`

### Registered distributable source-specification passage

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

### Semantic audit clauses

- **`DK-6.1-prop.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Proposition6_1`, `TauCeti.DavisKahan1970.Proposition6_1_real`

### Known hostile-review holes

- **`audit_mapping`:** The source block contains the Sylvester identity (6.1), Proposition 6.1, and an explicit 2x2 counterexample showing the ambient one-sided sine conclusion fails. The counterexample exists elsewhere but is not registered as evidence for this row.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The source block contains the Sylvester identity (6.1), Proposition 6.1, and an explicit 2x2 counterexample showing the ambient one-sided sine conclusion fails. The counterexample exists elsewhere but is not registered as evidence for this row.

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
- **Hostile completion certification:** `accepted`
- **Source-specification passage SHA-256:** `13e2036a72aaec0c5094f6014d3bfe1933167f1a43cf79f77716d5d7bf9726c7`

### Registered distributable source-specification passage

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
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `3d339a183924f39cbfd71c81f3745c69442b26a631b3a25921093e05277bb58d`

### Registered distributable source-specification passage

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

### Semantic audit clauses

- **`DK-6.2-thm.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Theorem6_2`, `TauCeti.DavisKahan1970.Theorem6_2_real`, `TauCeti.DavisKahan1970.Theorem6_2_real_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_2_real_commonCore`

### Known hostile-review holes

- **`audit_mapping`:** The source passage contains both the Hilbert--Schmidt theorem and its rank-corrected operator-norm consequence. Exact rank-consequence declarations exist but are not mapped into the row's semantic audit clauses.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The source passage contains both the Hilbert--Schmidt theorem and its rank-corrected operator-norm consequence. Exact rank-consequence declarations exist but are not mapped into the row's semantic audit clauses.

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

## 33. DK-6.3-thm — Tangent proof machinery, Example 6.1, and generalized tangent theorem

- **Source anchor:** Section 6 equations (6.2)–(6.6), Example 6.1, and Theorem 6.3
- **Source kind:** `theorem`
- **Completion obligation:** `true`
- **Census claim:** `partial_or_wrapper_missing` / `proved_in_build`
- **Hostile completion certification:** `reopened_math`
- **Source-specification passage SHA-256:** `ca0097fc54e1567d7129b6da2a912399a2cb516b3ba5ddc306bf4ab65b746505`

### Registered distributable source-specification passage

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
so the relevant cosines are positive and Ky Fan/Fan dominance gives the tangent theorem.  The source then gives Example~6.1 showing the one-sided placement of $\Lambda_1$ is essential: a finite matrix example has $\delta=1$ and tangent quantity $1$ while the residual is only $1/\sqrt2$ if spectral mass is allowed on the wrong side.

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

### Semantic audit clauses

- **`DK-6.3-thm.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Theorem6_3`, `TauCeti.DavisKahan1970.theorem6_3_all_kyFan_core_infiniteTrial_real`, `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm`, `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real`

### Known hostile-review holes

- **`missing_source_facing_statement`:** The generalized tangent theorem itself appears covered, but the same hashed passage preserves Example 6.1: delta=1, tangent quantity 1, residual 1/sqrt(2) when spectral mass lies on the wrong side. The hostile review did not find an exact source-facing formalization of that explicit counterexample.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The generalized tangent theorem itself appears covered, but the same hashed passage preserves Example 6.1: delta=1, tangent quantity 1, residual 1/sqrt(2) when spectral mass lies on the wrong side. The hostile review did not find an exact source-facing formalization of that explicit counterexample.

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Theorem6_3`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanTheta.lean:90`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.theorem6_3_all_kyFan_core_infiniteTrial_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:189`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm`

Source location candidates: `Challenge/DavisKahan1970/Conformance.lean:274`, `DavisKahan/Sources/DavisKahan1970/Directed.lean:73`

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
- `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm` — Challenge/DavisKahan1970/Conformance.lean:274, DavisKahan/Sources/DavisKahan1970/Directed.lean:73
- `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_spectral` — Challenge/DavisKahan1970/Conformance.lean:297, DavisKahan/Sources/DavisKahan1970/Directed.lean:122

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
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `c5bacffe42fb3c4e8e6bba5a6b28fc34f51bd04ec368afb41d9fee5e9de689aa`

### Registered distributable source-specification passage

~~~~tex
For the sine theorem, one of $A_0,\Lambda_1$ may be unbounded.  More generally, one spectrum may lie in an interval while the other remains at distance at least $\delta$ from it.  For a finite interval Theorem~5.1 suffices.  For a half-infinite interval such as $(-\infty,\alpha]$, no useful conclusion follows unless the residual is bounded: the source assumes $(A+H)E_0$ and $E_0A_0$ share a dense domain on which (1.8) defines a bounded $R$, extends $R$ continuously, and then applies Theorem~5.2.  Proposition~6.1 and Theorem~6.1 admit the analogous relaxation.

The tangent theorem requires both spectral truncation and noncompact-angle approximation.  For fixed $\nu$ and $\varepsilon>0$, choose a rank-$\nu$ projector $\Upsilon$ so that the singular angles $\phi_k$ of $S_0\Upsilon$ satisfy
\begin{equation}
 \sum_{k=1}^{\nu}\tan\phi_k
 >\sum_{k=1}^{\nu}\tan\theta_k-\varepsilon,
 \tag{6.7}
\end{equation}
\begin{equation}
 \sum_{k=1}^{\nu}\sin^2\phi_k
 >\sum_{k=1}^{\nu}\sin^2\theta_k-\varepsilon^2.
 \tag{6.8}
\end{equation}
Using a spectral cutoff $\Omega(\tau)$ of $A_0$, a refined choice can be made with
\begin{equation}
 \sum_{k=1}^{\nu}\sin^2\phi_k
 >\sum_{k=1}^{\nu}\sin^2\psi_k-\eta^2,
 \tag{6.9}
\end{equation}
where $\psi_k$ are the singular angles of $S_0\Omega(\tau)$.  With corresponding left/right rank-$\nu$ projectors $\Gamma,\Upsilon$, the truncated block equation is
\begin{equation}
 -\Gamma C_1B\Upsilon
 +\Gamma S_0\bigl(\Omega(\tau)A_0\Omega(\tau)\bigr)\Upsilon
 =(\Gamma\Lambda_1\Gamma)\Gamma S_0\Upsilon.
 \tag{6.10}
\end{equation}
The leakage term $F$ from inserting $\Upsilon+\Upsilon^\perp$ is controlled by Lemma~6.3, and the scalar compression gives
\begin{equation}
 y_{1k}^*C_1Bx_{0k}+y_{1k}^*Fx_{0k}
 \ge\delta\sin\phi_k.
 \tag{6.11}
\end{equation}
The source then lets the approximation error tend to zero, first obtaining the operator-norm tangent estimate and a uniform positive lower bound for the relevant cosines, then orthonormalizing the almost-orthonormal vectors to recover every Ky Fan norm and hence every unitary-invariant norm.  The same method is stated to extend Theorem~6.3 to unbounded operators.
~~~~

### Semantic audit clauses

- **`DK-6-appendix.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Theorem6_1_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_1_commonCore`, `TauCeti.DavisKahan1970.Theorem6_1_real_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_1_real_commonCore`, `TauCeti.DavisKahan1970.Theorem6_2_real_commonDomain`, `TauCeti.DavisKahan1970.Theorem6_2_real_commonCore`

### Known hostile-review holes

- **`audit_atomization`:** The TeX explicitly preserves equations (6.7)-(6.11) and the limiting proof chain. The row maps endpoint/common-domain machinery and historically treats parts of the chain as documentation fidelity; under statement-level 100% coverage, every preserved mathematical equation needs explicit evidence/disposition.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The TeX explicitly preserves equations (6.7)-(6.11) and the limiting proof chain. The row maps endpoint/common-domain machinery and historically treats parts of the chain as documentation fidelity; under statement-level 100% coverage, every preserved mathematical equation needs explicit evidence/disposition.

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
- **Hostile completion certification:** `accepted`
- **Source-specification passage SHA-256:** `6709c9fbf240ea7fc10d68b73cd0c746c59536127a66d13108ba14d114d52a45`

### Registered distributable source-specification passage

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
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `67854d13100c18b09c60f5af6e85a937281d1653a691c7f24357da4964f82cf2`

### Registered distributable source-specification passage

~~~~tex
Let $X=P-P^\perp$ and $Q_-=XQX$.  Conjugating by $X$ reverses the off-diagonal block of $H$:
\begin{equation}
 A+XHX\sim\begin{pmatrix}A_0+H_0&-B^*\\-B&A_1+H_1\end{pmatrix}.
 \tag{7.1}
\end{equation}
The direct-rotation identities give the reflected diagonalization
\begin{equation}
 \begin{pmatrix}A_0+H_0&-B^*\\-B&A_1+H_1\end{pmatrix}
 \begin{pmatrix}C_0&S_0^*\\-S_0&C_1\end{pmatrix}
 =
 \begin{pmatrix}C_0&S_0^*\\-S_0&C_1\end{pmatrix}
 \begin{pmatrix}\Lambda_0&0\\0&\Lambda_1\end{pmatrix}.
 \tag{7.2}
\end{equation}
Combining it with the original diagonalization yields
\begin{equation}
 (A+H)U^2=U^2(A+XHX).
 \tag{7.3}
\end{equation}
Moreover the block form of $U^2$ contains $\cos(2\Theta_j)$ and $\sin(2\Theta_j)$:
\begin{equation}
 U^2\sim
 \begin{pmatrix}
 \cos2\Theta_0&-J_0^*\sin2\Theta_1\\
 J_0\sin2\Theta_0&\cos2\Theta_1
 \end{pmatrix}.
 \tag{7.4}
\end{equation}
Applying the symmetric sine estimate to $A+H$ and $A+XHX$ yields
\begin{equation}
 \boxed{\delta\norm{\sin2\Theta}\le\norm{H-XHX}\le2\norm{H}.}
 \tag{7.5}
\end{equation}
On the directed block, Lemma~6.1 converts the first inequality to the stronger source derivation
\[
 \boxed{\delta\norm{\sin2\Theta_0}\le\norm{B}\le\norm{R}.}
\]
The paper also notes that the ambient estimate may be obtained from corresponding gaps in $A$ by swapping $A$ and $A+H$, but the residual inference is asymmetric.  Its counterexample
\[
 A\sim\begin{pmatrix}0&0\\0&\delta\end{pmatrix},
 \qquad
 H\sim\begin{pmatrix}0&1\\1&-\delta\end{pmatrix}
\]
has $2\norm{R}=2$ while $\delta\norm{\sin2\Theta_0}=\delta$, which can be arbitrarily large under the wrong swap direction.
~~~~

### Semantic audit clauses

- **`DK-7-sin2-proof.reflection`:** Reflection/symmetric-perturbation identities (7.1)-(7.4), including the doubled-angle overlap representation.
  - Review declarations: `TauCeti.DavisKahan1970.sinTwoTheta_mirrorDefect_eq_perturbationDefect`, `TauCeti.DavisKahan1970.sinTwoTheta_reflectedOverlap_norm`
- **`DK-7-sin2-proof.ambient`:** Ambient estimate (7.5): delta ||sin 2 Theta|| <= ||H-XHX|| <= 2 ||H||.
  - Review declarations: `TauCeti.DavisKahan1970.sinTwoTheta_mirrorDefect_le_two_mul`, `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative`
- **`DK-7-sin2-proof.directed`:** Sharper directed residual conclusion: delta ||sin 2 Theta_0|| <= ||B|| <= ||R||, without the ambient factor two.
  - Review declarations: `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative`

### Known hostile-review holes

- **`audit_atomization`:** The block contains equations (7.1)-(7.5), reflected diagonalization, the factor-one directed residual refinement, swap asymmetry, and a counterexample. The current clauses do not explicitly account for every separable identity/assertion.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The block contains equations (7.1)-(7.5), reflected diagonalization, the factor-one directed residual refinement, swap asymmetry, and a counterexample. The current clauses do not explicitly account for every separable identity/assertion.

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
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `59db32e78184895941dce6d1068875d12f24818a0c86b7a02a9f452d2324f226`

### Registered distributable source-specification passage

~~~~tex
Under the printed hypotheses
\[
 H_0=H_1=0,
 \qquad A_0\le\alpha,
 \qquad A_1\ge\alpha+\delta,
\]
the relation $F_0^*(A+H)F_1=0$ yields
\begin{equation}
 -C_0B^*C_1+S_0^*BS_0^*
 =S_0^*A_1C_1-C_0A_0S_0^*.
 \tag{7.6}
\end{equation}
For paired singular vectors of $S_0$, the scalar consequence is
\[
 \pm2\cos(2\theta_j)\,\Re(y_j^*Bx_j)
 \ge\delta\sin(2\theta_j).
\]
Hence $\cos(2\theta_j)\ne0$ is a \emph{conclusion of the argument}, not an additional theorem hypothesis.  Choosing the sign appropriately gives
\[
 2\Re(y_j^*Bx_j)\ge\delta|\tan(2\theta_j)|.
\]
Summing through Ky Fan's variational principle and using Fan dominance yields
\[
 \boxed{\delta\norm{\tan(2\Theta_0)}\le2\norm{R}}.
\]
Lemma~6.1 supplies the corresponding whole-space estimate, recovering the ambient conclusion of the Section~2 $\tan2\theta$ theorem from only the printed hypotheses.
~~~~

### Semantic audit clauses

- **`DK-7-tan2-proof.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.tanTwoTheta_uiNorm`, `TauCeti.DavisKahan1970.tanTwoTheta_kyFan`, `TauCeti.DavisKahan1970.tanTwoTheta_sharp_opNorm`, `TauCeti.DavisKahan1970.tanTwoTheta_spectral_repulsion`

### Known hostile-review holes

- **`audit_atomization`:** The exact directed/ambient tan(2 Theta) endpoints are now closed. The proof block still contains equation (7.6), scalar singular-vector inequality, pole exclusion as a conclusion, Fan-dominance steps, and both endpoints under one coarse audit clause; atomize these for static semantic certification.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The exact directed/ambient tan(2 Theta) endpoints are now closed. The proof block still contains equation (7.6), scalar singular-vector inequality, pole exclusion as a conclusion, Fan-dominance steps, and both endpoints under one coarse audit clause; atomize these for static semantic certification.

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
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `ca616396d0bee7b303c7da3ad0904053b80ad6da1a13a172bbec402be84f7c57`

### Registered distributable source-specification passage

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

### Semantic audit clauses

- **`DK-8.1-thm.branch`:** Theta <= pi/4 iff the selected Lambda blocks lie on the prescribed sides of alpha, together with existence of a reducing projector Q having those properties.
  - Review declarations: `TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch`, `TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_spectrumIn`
- **`DK-8.1-thm.i`:** Part (i): operator compression/sandwich inequality for A_1-alpha and C_1(Lambda_1-alpha)C_1, and the analogous lower block.
  - Review declarations: `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_source`
- **`DK-8.1-thm.ii`:** Part (ii): finite-dimensional eigenvalue inequalities and their natural infinite-dimensional approximation-number extensions.
  - Review declarations: `TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_source`
- **`DK-8.1-thm.iii`:** Part (iii): symmetric-gauge/weak-majorization inequalities with principal-cosine weights, plus the analogous lower-block relation.
  - Review declarations: `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_source`, `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_source`

### Known hostile-review holes

- **`audit_mapping`:** The theorem is usefully split into branch/(i)/(ii)/(iii), but primary evidence remains complex-centric while real counterparts exist. Bind each source conclusion explicitly in both source scalar fields.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The theorem is usefully split into branch/(i)/(ii)/(iii), but primary evidence remains complex-centric while real counterparts exist. Bind each source conclusion explicitly in both source scalar fields.

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

## 39. DK-8.2-thm — Smallness selects the acute branch and closing extension remark

- **Source anchor:** Theorem 8.2 and final Section 8 extension remark
- **Source kind:** `theorem`
- **Completion obligation:** `true`
- **Census claim:** `compiled_exact` / `proved_in_build`
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `8af6a38667dbf398e65e1b4460763ab627b559607ac519214c35402797c1b48e`

### Registered distributable source-specification passage

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

### Semantic audit clauses

- **`DK-8.2-thm.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_paperUINorm`, `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_real_paperUINorm`, `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_source_paperUINorm`, `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_directed`

### Known hostile-review holes

- **`audit_atomization`:** A single `.whole` clause covers two alternative half-gap hypotheses, branch selection, homotopy, perturbation and residual forms, unequal-dimensional extension, and the source statement that no analogous tan(2 Theta) extension is known. These need atomic evidence/dispositions.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: A single `.whole` clause covers two alternative half-gap hypotheses, branch selection, homotopy, perturbation and residual forms, unequal-dimensional extension, and the source statement that no analogous tan(2 Theta) extension is known. These need atomic evidence/dispositions.

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
- **Census claim:** `partial_or_wrapper_missing` / `proved_in_build`
- **Hostile completion certification:** `reopened_math`
- **Source-specification passage SHA-256:** `21ee160b940f7d4e04ca80a58a01e674c0e812dd3cc50a27ecc607b60fa22498`

### Registered distributable source-specification passage

~~~~tex
Take the real Hilbert space $L^2(0,1)$ with inner product $u^*v=\int_0^1u(t)v(t)\,dt$.  The unperturbed operator is the self-adjoint closure of the fourth derivative with free-end boundary conditions
\[
 u''(0)=u'''(0)=u''(1)=u'''(1)=0,
\]
and $H$ is multiplication by $\varepsilon t$, with $0<\varepsilon<100$.  Thus the perturbed eigenproblem is
\[
 u^{(4)}+\varepsilon t u=\lambda u
\]
with the same boundary conditions.  The source orders the unperturbed eigenvalues, with multiplicity, as
\[
 \alpha_1=0=\alpha_2<\alpha_3<\alpha_4<\cdots,
\]
and for $k>2$ identifies $\alpha_k$ as the positive roots of the free-beam equation
\[
 \cos(\alpha_k^{1/4})\cosh(\alpha_k^{1/4})=1
\]
and satisfy $\alpha_k>500$.  The source chooses the explicit orthonormal zero-eigenfunctions
\[
 w_k(t)=\frac{1+(-1)^k\sqrt3(2t-1)}{\sqrt2},
 \qquad k=1,2,
\]
sets $e_k=w_k$, and takes $E_0=(e_1\ e_2):\mathbb R^2\to L^2(0,1)$.

Since $H\ge0$, the third perturbed eigenvalue satisfies $\lambda_3\ge\alpha_3>500$.  With the initial comparison $A_0=0$, the residual is $R=HE_0=(r_1\ r_2)$ with
\[
 r_k(t)=\varepsilon t e_k(t)
 =\frac{\varepsilon t\bigl(1+(-1)^k\sqrt3(2t-1)\bigr)}{\sqrt2}.
\]
Its Gram matrix is
\[
 R^*R=\frac{\varepsilon^2}{30}
 \begin{pmatrix}
 11-\sqrt{75}&-1\\-1&11+\sqrt{75}
 \end{pmatrix},
\]
whose eigenvalues are
\[
 \frac{\varepsilon^2}{30}(11\pm\sqrt{76}).
\]
These data drive the first sine estimates.
~~~~

### Semantic audit clauses

- **`DK-9-model.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Section9.real_freeBeam_operator_source`, `TauCeti.DavisKahan1970.Section9.real_freeBeam_spectrum_source`, `TauCeti.DavisKahan1970.Section9.real_freeBeam_zero_mode_source`, `TauCeti.DavisKahan1970.Section9.real_freeBeam_finiteData_source`, `TauCeti.DavisKahan1970.Section9.real_freeBeam_trial_and_perturbation_source`, `TauCeti.DavisKahan1970.Section9.real_freeBeam_positive_spectrum_source`

### Known hostile-review holes

- **`math`:** PDF re-audit resolves the source-reading ambiguity: the paper prints alpha_1 = 0 = alpha_2 < alpha_3 < alpha_4 < ... and the distributable TeX now preserves that strict ordering. The source-specification defect is closed; the formalization must now justify that source scope, including the positive-eigenvalue multiplicity/simplicity content, rather than weaken the statement.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: PDF re-audit resolves the source-reading ambiguity: the paper prints alpha_1 = 0 = alpha_2 < alpha_3 < alpha_4 < ... and the distributable TeX now preserves that strict ordering. The source-specification defect is closed; the formalization must now justify that source scope, including the positive-eigenvalue multiplicity/simplicity content, rather than weaken the statement.

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Section9.real_freeBeam_operator_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:44`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.real_freeBeam_spectrum_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:54`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.real_freeBeam_zero_mode_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:120`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.real_freeBeam_finiteData_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:129`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.real_freeBeam_trial_and_perturbation_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:135`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.real_freeBeam_positive_spectrum_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:99`

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
- `TauCeti.DavisKahan.FreeBeam.Model.nonneg_of_beamOperator_eigen` — DavisKahan/SpectralTheory/FormMethod/BeamClassicalReal.lean:1396, DavisKahan/SpectralTheory/FormMethod/BeamSpectrum.lean:747
- `TauCeti.DavisKahan.FreeBeam.Model.exists_eigenvector_of_mem_realSpectrum_beamOperator` — DavisKahan/SpectralTheory/FormMethod/BeamSpectrum.lean:917, DavisKahan/SpectralTheory/FormMethod/BeamSpectrumReal.lean:125
- `TauCeti.DavisKahan.FreeBeam.Model.zero_mem_realSpectrum_beamOperator` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:309, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:237
- `TauCeti.DavisKahan.FreeBeam.Model.realSpectrum_beamOperator_eq_insert_zero` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:327, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:249
- `TauCeti.DavisKahan.FreeBeam.Model.finite_realSpectrum_beamOperator_inter_Iic` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:343, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:263
- `TauCeti.DavisKahan.FreeBeam.Model.nonempty_orderIso_nat_beamEigenvalues` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:358, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:273
- `TauCeti.DavisKahan.FreeBeam.Model.exists_strictMono_range_eq_beamEigenvalues` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:367, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:278
- `TauCeti.DavisKahan1970.Section9.real_freeBeam_operator_source` — DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:44
- `TauCeti.DavisKahan1970.Section9.real_freeBeam_spectrum_source` — DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:54
- `TauCeti.DavisKahan1970.Section9.real_freeBeam_zero_mode_source` — DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:120
- `TauCeti.DavisKahan1970.Section9.real_freeBeam_finiteData_source` — DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:129
- `TauCeti.DavisKahan1970.Section9.real_freeBeam_trial_and_perturbation_source` — DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:135
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
- `TauCeti.DavisKahan.FreeBeam.Model.Real.exists_characteristic_of_eigen` — DavisKahan/SpectralTheory/FormMethod/BeamClassicalReal.lean:1343, DavisKahan/SpectralTheory/FormMethod/BeamSpectrum.lean:490
- `TauCeti.DavisKahan.FreeBeam.Model.Real.realSpectrum_beamOperator_subset` — DavisKahan/SpectralTheory/FormMethod/BeamSpectrum.lean:1041, DavisKahan/SpectralTheory/FormMethod/BeamSpectrumReal.lean:238
- `TauCeti.DavisKahan.FreeBeam.Model.Real.beamEigenvalues` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:163, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:115
- `TauCeti.DavisKahan.FreeBeam.Model.Real.exists_strictMono_range_eq_beamEigenvalues` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:367, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:278
- `TauCeti.DavisKahan.FreeBeam.Model.Real.five_hundred_lt_of_mem_beamEigenvalues` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:168, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:139
- `TauCeti.DavisKahan.FreeBeam.Model.Real.not_finiteDimensional_beamL2` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequence.lean:80, DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:32
- `TauCeti.DavisKahan.FreeBeam.Model.Real.beamFiniteDataCertificate` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:1067, DavisKahan/SpectralTheory/FormMethod/BeamSection9Real.lean:33
- `TauCeti.DavisKahan.FreeBeam.Model.Real.beamTrial_le_domain` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:106, DavisKahan/SpectralTheory/FormMethod/BeamTrialReal.lean:67
- `TauCeti.DavisKahan.FreeBeam.Model.Real.beamOperator_apply_trial` — DavisKahan/SpectralTheory/FormMethod/BeamSection9.lean:112, DavisKahan/SpectralTheory/FormMethod/BeamTrialReal.lean:73
- `TauCeti.DavisKahan.FreeBeam.Classical.characteristic_iff_exists_nontrivial_freeBoundary` — DavisKahan/Sources/DavisKahan1970/Section9/FreeBeamCharacteristicConverse.lean:190
- `TauCeti.DavisKahan.FreeBeam.Classical.exists_nontrivial_freeBoundary_of_characteristic` — DavisKahan/Sources/DavisKahan1970/Section9/FreeBeamCharacteristicConverse.lean:176
- `TauCeti.DavisKahan1970.Section9.real_freeBeam_positive_spectrum_source` — DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:99
- `TauCeti.DavisKahan1970.Section9.real_freeBeam_trial_le_domain` — DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:107
- `TauCeti.DavisKahan1970.Section9.real_freeBeam_operator_apply_trial` — DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean:113
- `TauCeti.DavisKahan.FreeBeam.Model.Real.beamEigenvalues_eq_characteristicFourthPowers` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:128
- `TauCeti.DavisKahan.FreeBeam.Model.Real.pow_four_mem_beamEigenvalues_of_characteristic` — DavisKahan/SpectralTheory/FormMethod/BeamEigenvalueSequenceReal.lean:121
- `TauCeti.DavisKahan.FreeBeam.Model.Real.exists_eigenpair_of_characteristic` — DavisKahan/SpectralTheory/FormMethod/BeamClassicalReal.lean:1107
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
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `57ea978cfdbd641bfe2c257f686d449a42baa10cfba67fa9d593be8ca2ab9bf9`

### Registered distributable source-specification passage

~~~~tex
With gap $\delta=500$, the operator-norm $\sin\theta$ theorem gives
\begin{equation}
 \sin\theta_1<0.001622\,\varepsilon.
 \tag{9.1}
\end{equation}
The $\sin2\theta$ theorem gives
\begin{equation}
 \sin2\theta_1<0.004\,\varepsilon.
 \tag{9.2}
\end{equation}
Using the two-term Ky Fan norm gives the simultaneous subspace estimates
\begin{equation}
 \sin\theta_1+\sin\theta_2<0.00218\,\varepsilon,
 \tag{9.3}
\end{equation}
\begin{equation}
 \sin2\theta_1+\sin2\theta_2<0.008\,\varepsilon.
 \tag{9.4}
\end{equation}
~~~~

### Semantic audit clauses

- **`DK-9.1-9.4.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Section9.equation_9_1`, `TauCeti.DavisKahan1970.Section9.equation_9_2`, `TauCeti.DavisKahan1970.Section9.equation_9_3`, `TauCeti.DavisKahan1970.Section9.equation_9_4`

### Known hostile-review holes

- **`audit_mapping`:** The primary mapped `equation_9_*` declarations are largely arithmetic wrappers conditional on analytic bounds. Genuine unconditional beam-model sine/sin(2 Theta) theorems exist elsewhere and should be the source evidence for the actual Section 9 conclusions.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The primary mapped `equation_9_*` declarations are largely arithmetic wrappers conditional on analytic bounds. Genuine unconditional beam-model sine/sin(2 Theta) theorems exist elsewhere and should be the source evidence for the actual Section 9 conclusions.

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
- **Hostile completion certification:** `reopened_mapping`
- **Source-specification passage SHA-256:** `dfcd77c495e43593fcd6cd52f5719eacdda94902526d1117ca61dba086500774`

### Registered distributable source-specification passage

~~~~tex
Refine the comparison by taking the Rayleigh--Ritz matrix
\[
 \widehat A_0=E_0^*(A+H)E_0
 =\frac{\varepsilon}{2}\operatorname{diag}(1-1/\sqrt3,\ 1+1/\sqrt3),
\]
with residual $\widehat R=(A+H)E_0-E_0\widehat A_0$.  Then
\[
 \widehat R^*\widehat R
 =\frac{\varepsilon^2}{30}\begin{pmatrix}1&-1\\-1&1\end{pmatrix},
 \qquad
 \norm{\widehat R}_1=\norm{\widehat R}_2=\frac{\varepsilon}{\sqrt{15}}.
\]
The Ritz eigenvalues are
\begin{equation}
 \widehat\alpha_k
 =\frac{\varepsilon}{2}\left(1+\frac{(-1)^k}{\sqrt3}\right).
 \tag{9.5}
\end{equation}
Thus $\widehat A_0<0.7887\varepsilon$ and the tangent gap may be taken as $500-0.7887\varepsilon$.  The operator-norm tangent estimate is
\begin{equation}
 \tan\theta_1
 <\frac{0.0005164\varepsilon}{1-0.0015774\varepsilon},
 \tag{9.6}
\end{equation}
with the same right-hand side for $\tan\theta_1+\tan\theta_2$ in the two-term Ky Fan norm.

For the double-angle theorem replace the complementary comparison block by $\widehat A_1=E_1^*(A+H)E_1>500$.  Then
\begin{equation}
 \tan2\theta_1
 <\frac{0.0010328\varepsilon}{1-0.0015774\varepsilon},
 \tag{9.7}
\end{equation}
again with the same right-hand side for $\tan2\theta_1+\tan2\theta_2$ in the two-term Ky Fan norm.
~~~~

### Semantic audit clauses

- **`DK-9.5-9.7.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Section9.equation_9_5_low`, `TauCeti.DavisKahan1970.Section9.equation_9_5_high`, `TauCeti.DavisKahan1970.Section9.equation_9_6`, `TauCeti.DavisKahan1970.Section9.equation_9_7`

### Known hostile-review holes

- **`audit_mapping`:** The current primary mapping emphasizes numerical wrappers rather than the genuine beam tangent/double-tangent theorems that discharge the analytic hypotheses. Rebind the row to the unconditional source-facing model results.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The current primary mapping emphasizes numerical wrappers rather than the genuine beam tangent/double-tangent theorems that discharge the analytic hypotheses. Rebind the row to the unconditional source-facing model results.

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
- **Census claim:** `partial_or_wrapper_missing` / `proved_in_build`
- **Hostile completion certification:** `reopened_math`
- **Source-specification passage SHA-256:** `d07f312692410096396040b41f2fa512775f63b3dd9d52d4b81490409d68368d`

### Registered distributable source-specification passage

~~~~tex
Weinberger's method combines Rayleigh--Ritz upper bounds $\widehat\alpha_k$, lower bounds $\check\alpha_k$, and the separation $\widehat\alpha_2<500<\lambda_3$ to obtain, for the angle $\phi_k$ from the trial vector $e_k$ to the exact two-dimensional eigenspace,
\[
 \sin^2\phi_k\le
 \frac{\widehat\alpha_k-\check\alpha_k}{500-\check\alpha_k}.
\]
The best lower bounds from the available $2+1$ block information are the two lower eigenvalues of
\[
 \begin{pmatrix}
 \widehat\alpha_1&0&\varepsilon/\sqrt{30}\\
 0&\widehat\alpha_2&\varepsilon/\sqrt{30}\\
 \varepsilon/\sqrt{30}&\varepsilon/\sqrt{30}&500
 \end{pmatrix}.
\]
The source further records, for the small parameter range under discussion,
\[
 \frac{\varepsilon^2/30}{500-\widehat\alpha_k}
 >\widehat\alpha_k-\check\alpha_k
 =\frac{\varepsilon^2/30}{500-\widehat\alpha_k}-O(\varepsilon^4).
\]
For $0<\varepsilon<100$ this gives
\begin{equation}
 \tan\phi_1<\frac{0.0005164\varepsilon}{1-0.0004227\varepsilon},
 \qquad
 \tan\phi_2<\frac{0.0005164\varepsilon}{1-0.0015774\varepsilon}.
 \tag{9.8}
\end{equation}
The paper stresses that $\phi_k$ and the largest subspace angle $\theta_1$ answer different questions, although
\[
 \sin^2\phi_1+\sin^2\phi_2=\sin^2\theta_1+\sin^2\theta_2.
\]
Applying Theorem~6.3 directly to each one-dimensional trial vector instead gives the sharper bounds
\[
 \tan\phi_1<\frac{0.0003652\varepsilon}{1-0.0004227\varepsilon},
 \qquad
 \tan\phi_2<\frac{0.0003652\varepsilon}{1-0.0015774\varepsilon}.
\]
The source presents the methods as complementary rather than as one dominating the other.
~~~~

### Semantic audit clauses

- **`DK-9.8.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Section9.equation_9_8_lower`, `TauCeti.DavisKahan1970.Section9.equation_9_8_upper`

### Known hostile-review holes

- **`math`:** PDF re-audit restored the lower-bound comparison and O(epsilon^4) asymptotic preceding (9.8). The source-specification defect is closed. Remaining obligations are mathematical: the Weinberger sine-square statement, Lehmann best-lower-bound assertion, restored asymptotic, and the final (9.8) conclusions each require an honest formal disposition.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: PDF re-audit restored the lower-bound comparison and O(epsilon^4) asymptotic preceding (9.8). The source-specification defect is closed. Remaining obligations are mathematical: the Weinberger sine-square statement, Lehmann best-lower-bound assertion, restored asymptotic, and the final (9.8) conclusions each require an honest formal disposition.

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.Section9.equation_9_8_lower`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/WeinbergerComparison.lean:140`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section9.equation_9_8_upper`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section9/WeinbergerComparison.lean:153`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.Section9.ArrowheadThreeByThree` — DavisKahan/Sources/DavisKahan1970/Section9/WeinbergerComparison.lean:34
- `TauCeti.DavisKahan1970.Section9.tangent_sq_le_of_weinberger_sine_sq` — DavisKahan/Sources/DavisKahan1970/Section9/WeinbergerComparison.lean:88
- `TauCeti.DavisKahan1970.Section9.equation_9_8_lower` — DavisKahan/Sources/DavisKahan1970/Section9/WeinbergerComparison.lean:140
- `TauCeti.DavisKahan1970.Section9.equation_9_8_upper` — DavisKahan/Sources/DavisKahan1970/Section9/WeinbergerComparison.lean:153
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
- **Census claim:** `partial_or_wrapper_missing` / `proved_in_build`
- **Hostile completion certification:** `reopened_math`
- **Source-specification passage SHA-256:** `2b28098ba69b0cd83e5755b950b4a4eda9cc7e80f3a2a6d95d46921271d8c91f`

### Registered distributable source-specification passage

~~~~tex
For small $\mu$ take
\[
 e=(1,\mu,\mu^2,\ldots)^*\in\ell_2,
 \qquad
 A+H=\operatorname{diag}(1,\mu^{-1},\mu^{-2},\ldots).
\]
As written, $e$ is just outside the domain because $(A+H)e=(1,1,1,\ldots)^*$; the source notes that an arbitrarily small modification fixes this domain defect.  Formally the Rayleigh quotient is
\[
 \widehat\alpha=\frac{e^*(A+H)e}{e^*e}=1+\mu,
\]
but the residual has infinite norm, so the paper's residual theorems give no estimate.  If independent lower eigenvalue bounds are known, Weinberger's method still yields
\[
 \sin^2\theta\le
 \frac{1+\mu-\check\alpha_1}{\check\alpha_2-\check\alpha_1},
\]
and at the best lower bounds, for the true $\theta=\arcsin\mu$,
\[
 \mu=\sin\theta\le\frac{\mu}{\sqrt{1-\mu}}.
\]
~~~~

### Semantic audit clauses

- **`DK-9-infinite-residual-counterexample.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Section9.rawDiagonalImage_eq_one`, `TauCeti.DavisKahan1970.Section9.rawDiagonalImage_partial_energy`, `TauCeti.DavisKahan1970.Section9.truncatedDiagonalImage_energy`, `TauCeti.DavisKahan1970.Section9.diagonalOperator`, `TauCeti.DavisKahan1970.Section9.geometricTrial_notMem_diagonalDomain`, `TauCeti.DavisKahan1970.Section9.geometricTrial_form_summable`

### Known hostile-review holes

- **`missing_source_facing_statement`:** The source says an arbitrarily small modification repairs the domain defect. Lean proves finite truncations lie in the operator domain and agree on every fixed prefix, but the hostile review did not find a norm-convergence/arbitrarily-small-perturbation theorem for those truncations.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The source says an arbitrarily small modification repairs the domain defect. Lean proves finite truncations lie in the operator domain and agree on every fixed prefix, but the hostile review did not find a norm-convergence/arbitrarily-small-perturbation theorem for those truncations.

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
- **Hostile completion certification:** `mixed_disposition`
- **Source-specification passage SHA-256:** `0f9c97c3405ebbf348de1e40df437d08c8f1e129a0038987c7ed12e45061413f`

### Registered distributable source-specification passage

~~~~tex
Let $f_k$ be the exact eigenvectors and $g_k$ the closest unit vectors in the trial plane.  Define $\eta_k$ by $P f_k=(\cos\eta_k)g_k$, let $\psi_k$ be the angle from $g_k$ to the trial vector $e_k$, and let $\omega_k$ be the angle from $e_k$ to $f_k$.  Then
\[
 \cos\omega_k=\cos\eta_k\cos\psi_k,
 \qquad
 \omega_k^2\le\psi_k^2+\eta_k^2.
\]
With coordinates $e_k\sim(u_k,0)^T$ and $f_k\sim(x_k,y_k)^T$, the eigenproblem is
\begin{equation}
 \begin{pmatrix}\widehat A_0&B^*\\B&\widehat A_1\end{pmatrix}
 \begin{pmatrix}x_k\\y_k\end{pmatrix}
 =\lambda_k\begin{pmatrix}x_k\\y_k\end{pmatrix}.
 \tag{9.9}
\end{equation}
Since $\widehat A_1>500>\lambda_k$,
\begin{equation}
 y_k=(\lambda_k-\widehat A_1)^{-1}Bx_k,
 \tag{9.10}
\end{equation}
and the two-dimensional Schur-complement eigenproblem is
\begin{equation}
 [\widehat A_0+B^*(\lambda_k-\widehat A_1)^{-1}B]x_k=\lambda_kx_k.
 \tag{9.11}
\end{equation}
The correction can be bounded by an off-diagonal matrix
\[
 \widehat H=\frac{\varepsilon^2}{30\gamma_k}
 \begin{pmatrix}0&1\\1&0\end{pmatrix},
 \qquad \gamma_k>500-\lambda_k,
\]
with
\[
 0\le\frac{\varepsilon^2}{30\gamma_k}I-\widehat H
 =B^*(\widehat A_1-\lambda_k)^{-1}B
 \le\frac{B^*B}{500-\lambda_k}.
\]
The $\tan2\theta$ theorem gives
\[
 (\widehat\alpha_2-\widehat\alpha_1)\tan2\psi_k
 \le2\norm{\widehat H}_1
 <\frac{\varepsilon^2}{15(500-\lambda_k)}.
\]
Theorem~8.1 selects $0\le\psi_k<\pi/4$, hence
\[
 2\psi_k<\arctan\frac{\varepsilon}{\sqrt{75}(500-\widehat\alpha_k)}.
\]
Equation (9.10) gives
\[
 \tan\eta_k
 <\frac{\varepsilon}{\sqrt{15}(500-\widehat\alpha_k)}.
\]
Combining the two angles yields
\[
 \omega_1<\frac{0.00053\varepsilon}{1-0.00043\varepsilon},
 \qquad
 \omega_2<\frac{0.00053\varepsilon}{1-0.0016\varepsilon}.
\]
Finally, the source says the best possible bound obtainable from the stated data is the angle between the $k$th coordinate vector and the $k$th eigenvector of the $3\times3$ comparison matrix used above, but proving that assertion is deferred to the unresolved three-way-subspace Question~10.2.
~~~~

### Semantic audit clauses

- **`DK-9.9-9.11.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: `TauCeti.DavisKahan1970.Section9.block_eigenproblem_iff`, `TauCeti.DavisKahan1970.Section9.schur_complement_reduction`, `TauCeti.DavisKahan1970.Section9.individual_angle_le_exact_envelope`, `TauCeti.DavisKahan1970.Section9.final_lower_individual_angle_bound`

### Known hostile-review holes

- **`mixed_disposition`:** The numerical/Schur-complement conclusions appear formalized, but the block ends with a source assertion that the 3x3 comparison angle is the best possible bound obtainable from the stated data while explicitly deferring its proof to unresolved Question 10.2. Record that assertion separately as source-asserted/unproved rather than counting the entire block as exact.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: The numerical/Schur-complement conclusions appear formalized, but the block ends with a source assertion that the 3x3 comparison angle is the best possible bound obtainable from the stated data while explicitly deferring its proof to unresolved Question 10.2. Record that assertion separately as source-asserted/unproved rather than counting the entire block as exact.

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
- **Hostile completion certification:** `not_applicable`
- **Source-specification passage SHA-256:** `31b6c36c9e33fb0d82afcfe7223d42b7558d1ba307b0b7823a2ff1e8ac23c764`

### Registered distributable source-specification passage

~~~~tex
If $\spec(A_0)$ and $\spec(\Lambda_1)$ are known only to have pairwise distance at least $\delta$, how sharply can $\Theta_0$ be bounded in terms of the residual $R$?  The paper points back to the limitations discussed after Theorem~5.1 and Theorem~6.2.
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
- **Hostile completion certification:** `not_applicable`
- **Source-specification passage SHA-256:** `b86da1d92d84b2592690213b7f007b3a770bd42fe09dccca2c21756a36cd7dab`

### Registered distributable source-specification passage

~~~~tex
For three-way orthogonal decompositions represented by isometries $E_0,E_1,E_2$ and $F_0,F_1,F_2$ with
\[
 \sum_{j=0}^2E_jE_j^*=I,
 \qquad
 \sum_{j=0}^2F_jF_j^*=I,
\]
the relative position is encoded by the $3\times3$ block matrix $(E_i^*F_j)_{i,j=0}^2$.  The question asks whether, when these decompositions arise from reducing subspaces of two nearby operators, the off-diagonal blocks admit estimates analogous to the two-way estimates developed in the paper.
~~~~

### Semantic audit clauses

- **`DK-10.2.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: *(none; inspect the row mapping/source context)*

### Primary Lean declarations for semantic review

No primary Lean declaration is registered for this row. If it is a completion obligation, this is itself a blocking audit defect.

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
- **Hostile completion certification:** `not_applicable`
- **Source-specification passage SHA-256:** `4354f4d04ae31bb397e07edd9f6dc6d99d9b2edddc6fd44b0bcc6509a9d442cf`

### Registered distributable source-specification passage

~~~~tex
Find best possible inequalities involving eigenvalue changes and eigenvector changes simultaneously, extending the Section~8 observations that relate spectral displacement to rotation.
~~~~

### Semantic audit clauses

- **`DK-10.3.whole`:** Audit the complete registered source passage as one semantic unit; split further if the independent reviewer finds separable mathematical clauses.
  - Review declarations: *(none; inspect the row mapping/source context)*

### Primary Lean declarations for semantic review

No primary Lean declaration is registered for this row. If it is a completion obligation, this is itself a blocking audit defect.

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

- **Source anchor:** Question 10.4, including ambient and directed functional-calculus specializations
- **Source kind:** `mixed_open_question`
- **Completion obligation:** `true`
- **Census claim:** `partial_or_wrapper_missing` / `proved_in_build`
- **Hostile completion certification:** `mixed_disposition`
- **Source-specification passage SHA-256:** `cb03063c7dac9729bde9e1594aca09f614de292828a9f3770c28061743fb3792`

### Registered distributable source-specification passage

~~~~tex
For a self-adjoint spectral resolution
\[
 A=\int_{-\infty}^{\infty}\lambda\,d\Omega(\lambda),
 \qquad
 f(A)=\int_{-\infty}^{\infty}f(\lambda)\,d\Omega(\lambda),
\]
the question asks for perturbation bounds on $f(A+H)-f(A)$ in terms of $H$ for useful classes of real functions $f$.

The paper's model case takes a step function with $f(\xi)=1$ on $\xi\le\alpha$ and $f(\xi)=0$ on $\xi\ge\alpha+\delta$.  Under the $\tan2\theta$ hypotheses,
\[
 f(A)=P,\qquad f(A+H)=Q,\qquad f(A_0)=I.
\]
Thus the ambient functional-calculus change is exactly the subspace sine:
\[
 \norm{f(A+H)-f(A)}=\norm{Q-P}=\norm{\sin\Theta},
\]
with
\[
 \boxed{\delta\norm{\tan2\Theta}\le2\norm H}.
\]
The directed action on the trial subspace is likewise
\[
 \begin{aligned}
 \norm{(f(A+H)-f(A))E_0}
 &=\norm{f(A+H)E_0-E_0f(A_0)}\\
 &=\norm{Q^\perp E_0}=\norm{\sin\Theta_0},
 \end{aligned}
\]
with the residual estimate
\[
 \boxed{\delta\norm{\tan2\Theta_0}\le2\norm R}.
\]
Question~10.4 asks for analogous bounds for more general $f$.
~~~~

### Semantic audit clauses

- **`DK-10.4.step-function-identities`:** Established model-case identities: f(A)=P, f(A+H)=Q, f(A0)=I and the projector/sine identities. These remain a completion obligation and currently have no exact registered source-facing declarations.
  - Review declarations: *(none; inspect the row mapping/source context)*
- **`DK-10.4.ambient-tan2`:** Established ambient model-case bound delta * ||tan(2 Theta)|| <= 2 ||H||.
  - Review declarations: `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_exact`, `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real_exact`
- **`DK-10.4.directed-tan2`:** Established directed model-case bound delta * ||tan(2 Theta_0)|| <= 2 ||R||.
  - Review declarations: `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_exact`, `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_real_exact`
- **`DK-10.4.open-general-f`:** Genuinely open source question: analogous perturbation bounds for useful broader classes of real functions f. This clause is not proof debt.
  - Review declarations: *(none; inspect the row mapping/source context)*

### Known hostile-review holes

- **`mixed_disposition`:** Question 10.4 is not a pure open-question block. Before the general-f question it states established step-function identities f(A)=P, f(A+H)=Q, f(A0)=I, the projector/sine identities, and the ambient/directed tan(2 Theta) bounds. The tan(2 Theta) bounds now have exact complex/real wrappers, but the functional-calculus identities are not atomically registered.
- **`checker_loophole`:** The previous checker exempted every DK-10.* row by identifier. This let established mathematics inside the Question 10.4 block escape the completion count. The row is now a mixed completion obligation until established clauses are explicitly covered and the final question separately marked open.

> **Audit warning:** HOSTILE RE-AUDIT REOPENED: Question 10.4 is not a pure open-question block. Before the general-f question it states established step-function identities f(A)=P, f(A+H)=Q, f(A0)=I, the projector/sine identities, and the ambient/directed tan(2 Theta) bounds. The tan(2 Theta) bounds now have exact complex/real wrappers, but the functional-calculus identities are not atomically registered. The previous checker exempted every DK-10.* row by identifier. This let established mathematics inside the Question 10.4 block escape the completion count. The row is now a mixed completion obligation until established clauses are explicitly covered and the final question separately marked open.

### Primary Lean declarations for semantic review

#### `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_exact`

Source location candidates: `Challenge/DavisKahan1970/Conformance.lean:531`, `DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean:1297`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:433`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_exact`

Source location candidates: `Challenge/DavisKahan1970/Conformance.lean:441`, `DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean:1160`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_real_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:362`

Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*

<details>
<summary>Full census declaration mapping for this row</summary>

When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.

- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_exact` — Challenge/DavisKahan1970/Conformance.lean:531, DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean:1297
- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real_exact` — DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:433
- `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_exact` — Challenge/DavisKahan1970/Conformance.lean:441, DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean:1160
- `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_real_exact` — DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:362

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

- **46 explicit mathematical completion obligations reviewed:** yes / no
- **13 currently hostile-certified exact obligations independently reconfirmed:** yes / no
- **1 currently hostile-certified refuted obligations independently reconfirmed:** yes / no
- **32 currently reopened completion obligations resolved by this audit:** yes / no
- **Reopened rows at packet generation:** `S1-block-residual` (reopened_math), `S1-ui-norms` (reopened_math), `S2-tan-theta` (reopened_mapping), `S2-sharpness` (reopened_mapping), `S2-unbounded-scope` (reopened_mapping), `DK-3.1-def` (reopened_mapping), `DK-3.1-prop` (reopened_mapping), `DK-3.2-prop` (reopened_math), `DK-3.3-prop` (reopened_mapping), `DK-3.4-prop` (reopened_math), `DK-3.5-prop` (reopened_math), `DK-4.1-prop` (reopened_mapping), `DK-4.2-prop` (reopened_mapping), `DK-4.3-prop` (reopened_mapping), `DK-5.1-thm` (reopened_mapping), `DK-5-hermitian-inequalities` (reopened_math), `DK-5.2-thm` (reopened_mapping), `DK-6.1-prop` (reopened_mapping), `DK-6.2-thm` (reopened_mapping), `DK-6.3-thm` (reopened_math), `DK-6-appendix` (reopened_mapping), `DK-7-sin2-proof` (reopened_mapping), `DK-7-tan2-proof` (reopened_mapping), `DK-8.1-thm` (reopened_mapping), `DK-8.2-thm` (reopened_mapping), `DK-9-model` (reopened_math), `DK-9.1-9.4` (reopened_mapping), `DK-9.5-9.7` (reopened_mapping), `DK-9.8` (reopened_math), `DK-9-infinite-residual-counterexample` (reopened_math), `DK-9.9-9.11` (mixed_disposition), `DK-10.4` (mixed_disposition)
- **Any unregistered mathematical claims found:** yes / no
- **Compiler certificate clean and complete:** yes / no
- **Is the repository's claim of 100% theorem-statement-level Davis--Kahan 1970 coverage justified?** yes / no / uncertain

## Findings requiring action

1. _none recorded yet_
