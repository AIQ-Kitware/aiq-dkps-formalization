# Davis--Kahan 1970 result-only semantic review — 2026-08-12

## Purpose

This is the maintained human-readable semantic review for the **29-result formalization denominator**. It is deliberately result-level: proof equations, examples, historical comparisons, Section 10 questions, and theorem-adjacent material remain visible in the source-fidelity inventory but do not become separate completion obligations.

A hostile reviewer should use this report together with `prose/distilled_literature/DavisKahan1970_part_III.tex`, `dev/davis-kahan-1970-source-atom-inventory.json`, and the compiler-checkable `DavisKahan/Sources/DavisKahan1970/Audits/ResultSemanticSurface.lean`. A result is marked accepted only when the checked-in Lean declarations expose every counted source hypothesis, conclusion, and scalar/dimension/norm scope.

## Current state

- Counted DK-established results: **29**
- Printed-result boundaries reviewed: **29/29**
- Semantically terminal: **26/29**
- Genuine remaining result-scope gaps: **3**
- Pending results re-audited in the current sweep: **17**
- False-positive pending statuses closed across the result-only sweep: **12**
- Latest-main baseline for this promotion: `9f1c3000e6d12cc013426bef07e3be107b7d5177`. That baseline already contains the compiler-verified full unbounded tan-2Theta closure at 25/29; this promotion adds only the real nonacute Proposition 3.3 source surface and advances the denominator to 26/29.

## All 29 counted results

### 1. `S2-sin-theta` — Single-angle sine theorem

**Verdict:** PASS exact. Re-audited in this sweep.

**Counted source atoms:** `S2-sin-theta.ui-norm-scope`, `S2-sin-theta.gap-hypothesis`, `S2-sin-theta.directed-conclusion`, `S2-unbounded-scope.infinite-dimensional-scope`, `S2-unbounded-scope.arbitrary-ui-scope`, `S2-unbounded-scope.unbounded-selfadjoint-scope`, `S2-unbounded-scope.bounded-residual-needed`, `S2-unbounded-scope.half-infinite-gap-intervals`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.sinTheta`
- `TauCeti.DavisKahan1970.sinTheta_real_exactPaper`
- `TauCeti.DavisKahan1970.generalizedSinTheta`
- `TauCeti.DavisKahan1970.generalizedSinTheta_real_exactPaper`

**Semantic review:**

Accepted result-only semantic review 2026-08-12. `sinTheta` is the complex source-shaped unbounded form-bounded isometric theorem and `sinTheta_real_exactPaper` exposes the real paper UI-norm surface; the generalized complex/real endpoints record the same unbounded closed-operator engine with the source lower-frame formulation. Together they cover the printed interval/exterior gap, arbitrary unitary-invariant norm, real/complex, infinite-dimensional, and unbounded-self-adjoint scope with bounded residual. No proof-only Section 1/6 material is used as part of the counted result.

### 2. `S2-tan-theta` — Single-angle tangent theorem

**Verdict:** OPEN — genuine result-scope theorem surface remains. Re-audited in this sweep.

**Counted source atoms:** `S2-sin-theta.ui-norm-scope`, `S2-tan-theta.ordered-gap-hypothesis`, `S2-tan-theta.rayleigh-ritz-hypothesis`, `S2-tan-theta.directed-conclusion`, `S2-tan-theta.ambient-conclusion`, `S2-unbounded-scope.infinite-dimensional-scope`, `S2-unbounded-scope.arbitrary-ui-scope`, `S2-unbounded-scope.unbounded-selfadjoint-scope`, `S2-unbounded-scope.bounded-residual-needed`, `S2-unbounded-scope.half-infinite-gap-intervals`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahanTheory.partIII_tanTheta_ritzResidual_uiNorm`
- `TauCeti.DavisKahan.Section2.theorem6_3_perturbation_infiniteTrial`
- `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm`
- `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_real`
- `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent`

**Semantic review:**

Result-only audit 2026-08-12: bounded directed and bounded ambient source theorems are present over complex and real Hilbert spaces, and the unbounded directed residual theorem is present over both scalar fields. The remaining source-scope gap is the *ambient unbounded* conclusion `delta * N(tan Theta) <= N(H)` for arbitrary paper UI norm under the printed hypotheses. No existing source-facing theorem was located that combines unbounded self-adjoint ambient scope with the sharp factor-one perturbation conclusion. Keep this result nonterminal until that theorem/wrapper exists and is registered.

**Structured remaining gap:**

- Category: `missing_unbounded_ambient_source_surface`
- Missing surface: Unbounded self-adjoint ambient perturbation theorem delta * N(tan Theta) <= N(H) for every paper unitary-invariant norm under the printed Section 2 ordered-gap/Rayleigh-Ritz hypotheses.
- Next action: Prove/register an unbounded ambient PaperUI source wrapper with the sharp factor-one perturbation conclusion; then re-run hostile semantic review.
- Strongest current evidence:
  - `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent`
  - `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists`
  - `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_real`

### 3. `S2-sin-two-theta` — Double-angle sine theorem

**Verdict:** PASS exact. Re-audited in this sweep.

**Counted source atoms:** `S2-sin-theta.ui-norm-scope`, `S2-sin-two-theta.gap-hypothesis`, `S2-sin-two-theta.directed-conclusion`, `S2-sin-two-theta.ambient-conclusion`, `S2-unbounded-scope.infinite-dimensional-scope`, `S2-unbounded-scope.arbitrary-ui-scope`, `S2-unbounded-scope.unbounded-selfadjoint-scope`, `S2-unbounded-scope.bounded-residual-needed`, `S2-unbounded-scope.half-infinite-gap-intervals`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm`
- `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm_real`
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative`
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative`
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative_real`
- `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative_real`

**Semantic review:**

Accepted result-only semantic review 2026-08-12. The bounded whole-space PaperUI wrappers give the ambient perturbation conclusion over complex and real Hilbert spaces. The four unbounded representative theorems give both ambient and directed-residual `sin 2Theta` conclusions over complex and real scalars for every paper unitary-invariant norm, with the source factor 2 and without finite-dimensional restrictions. This covers the counted Section 2 theorem at its shared unbounded scope.

### 4. `S2-tan-two-theta` — Double-angle tangent theorem

**Verdict:** PASS exact. Closed at the full advertised unbounded source scope in this promotion.

**Counted source atoms:** `S2-sin-theta.ui-norm-scope`, `S2-tan-two-theta.ordered-gap-hypothesis`, `S2-tan-two-theta.strong-offdiagonal-hypothesis`, `S2-tan-two-theta.no-extra-pole-hypothesis`, `S2-tan-two-theta.directed-conclusion`, `S2-tan-two-theta.ambient-conclusion`, `S2-unbounded-scope.infinite-dimensional-scope`, `S2-unbounded-scope.arbitrary-ui-scope`, `S2-unbounded-scope.unbounded-selfadjoint-scope`, `S2-unbounded-scope.bounded-residual-needed`, `S2-unbounded-scope.half-infinite-gap-intervals`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_exact`
- `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_real_exact`
- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_exact`
- `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real_exact`
- `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_directedResidual_paperUINorm_exact`
- `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_directedResidual_paperUINorm_real_exact`
- `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_ambient_paperUINorm_exact`
- `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_ambient_paperUINorm_real_exact`

**Semantic review:**

Accepted result-only semantic review 2026-08-12. The bounded exact wrappers already give both printed conclusions over real and complex Hilbert spaces for every `PaperUnitaryInvariantNorm`, deriving pole exclusion internally from the source hypotheses. The new unbounded wrappers close the shared Section 2 scope explicitly: the directed complex theorem uses the canonical spectral-cutoff/Ky-Fan/Fan-dominance engine; the complex ambient theorem assembles its two complementary reflection-tangent corners with skew-adjoint symmetry and Davis--Kahan Lemma 6.1; and the real directed and ambient wrappers descend these statements through the repository's exact complexification layer. The resulting theorems are arbitrary-dimensional, allow the source's unbounded self-adjoint `A` with bounded residual/perturbation data, retain the sharp factor two, and add no quarter-angle premise, explicit pole certificate, compactness/finite-dimensionality condition, or perturbed-Q spectral placement. The user reported the self-contained implementation compiling successfully on the `7cc049b4` base before this census promotion.

### 5. `DK-3.1-prop` — Acute direct rotation existence and uniqueness

**Verdict:** PASS exact. Previously terminal; retained and re-exposed on the compiler audit surface.

**Counted source atoms:** `DK-3.1-prop.existence`, `DK-3.1-prop.uniqueness`, `DK-3.1-prop.positive-diagonal-characterization`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.proposition3_1_source`

**Semantic review:**

Accepted result-only semantic review 2026-08-12. The exact generic RCLike wrapper `proposition3_1_source` uses the paper's printed `TauCeti.IsAcute` hypothesis, works in arbitrary dimension over real or complex Hilbert spaces, proves the Definition 3.1 crossed-block identity for the canonical direct rotation, and states that positivity of the two diagonal blocks alone characterizes it among unitary intertwiners. It assumes neither `IsUniformlyAcute`, equation (3.8), nor standing dimension assumption (1.5).

### 6. `DK-3.2-prop` — Nonacute existence criterion

**Verdict:** PASS exact. Re-audited in this sweep.

**Counted source atoms:** `DK-3.2-prop.existence-iff-crossing-dimensions`, `DK-3.2-prop.nonuniqueness`, `DK-3.2-prop.eq-3-5`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_exists_iff_crossedDefectsEquivalent`
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_not_unique`
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_exists_iff_crossedDefectsEquivalent_real`
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_not_unique_real`

**Semantic review:**

Accepted result-only semantic review 2026-08-12. The generic Section 3 source surface states existence of a paper direct rotation iff the two crossed defect spaces are equivalent and separately proves nonuniqueness whenever the pair is nonacute. The explicit real aliases expose the same two printed clauses over `ℝ`; the generic theorem covers `ℂ` and arbitrary Hilbert dimension. The crossing-subspace square identity and bilateral-shift example are adjacent source material and are not part of the counted Proposition 3.2 boundary.

### 7. `DK-3.3-prop` — Principal square-root characterization

**Verdict:** PASS exact.

**Counted source atoms:** `DK-3.3-prop.principal-square-root`, `DK-3.3-prop.square-root-converse`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.proposition3_3_complex_forward_source`
- `TauCeti.DavisKahan1970.proposition3_3_complex_converse_source`
- `TauCeti.DavisKahan1970.proposition3_3_real_forward_source`
- `TauCeti.DavisKahan1970.proposition3_3_real_converse_source`

**Semantic review:**

Accepted result-only semantic review 2026-08-12. The full nonacute complex forward/converse characterization was already proved in `DavisKahan.Frontier.Section3`. The source-facing complex wrappers expose exactly those printed clauses. The real forward/converse wrappers transport the same arbitrary-dimensional nonacute statement through canonical real complexification: the principal branch is defined by the spectrum of the complexification, crossed-defect transport is coordinatewise, and unitarity/intertwining/positive diagonal blocks/crossed blocks descend through the established complexification API. No `IsUniformlyAcute`, finite-dimensional, separability, compactness, or extra branch hypothesis is added. Equations (3.6)--(3.8) and reflection conjugacy remain adjacent fidelity/proof material outside the counted proposition boundary.

### 8. `DK-3.4-prop` — Square as a direct rotation

**Verdict:** OPEN — genuine result-scope theorem surface remains. Re-audited in this sweep.

**Counted source atoms:** `DK-3.4-prop.u-square-direct-rotation`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_4_source_full`
- `TauCeti.DavisKahan.Frontier.Section3.proposition3_4_source_eq_directRotation`

**Semantic review:**

Result-only audit 2026-08-12: `proposition3_4_source_full` and its equality-to-direct-rotation companion give the complete printed Proposition 3.4 over complex Hilbert spaces at the nonacute source scope. No real full-scope counterpart was located. The exact remaining task is the `R`-scalar theorem that under the printed `C0^2 >= 1/2` condition, `U^2` is the direct rotation from `Q_-` to `Q`, without replacing the source hypotheses by uniform acuteness.

**Structured remaining gap:**

- Category: `missing_real_full_scope_source_surface`
- Missing surface: Real-Hilbert-space full nonacute Proposition 3.4: under the printed C0^2 >= 1/2 condition, U^2 is the direct rotation from Q_- to Q.
- Next action: Transport/generalize the full nonacute Proposition 3.4 argument to real scalars without strengthening the source hypotheses.
- Strongest current evidence:
  - `TauCeti.DavisKahan.Frontier.Section3.proposition3_4_source_full`
  - `TauCeti.DavisKahan.Frontier.Section3.proposition3_4_source_eq_directRotation`

### 9. `DK-3.1-thm` — Classification of pairs of subspaces

**Verdict:** PASS exact. Previously terminal; retained and re-exposed on the compiler audit surface.

**Counted source atoms:** `DK-3.1-thm.complete-invariant`, `DK-3.1-thm.converse-angle-data`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan.Frontier.Section3.theorem3_1_spectralMultiplicity_classification`
- `TauCeti.DavisKahan.Frontier.Section3.theorem3_1_realization`
- `TauCeti.DavisKahan.Frontier.Section3.theorem3_1_spectralMultiplicity_classification_real`

**Semantic review:**

Accepted by the hostile audit at the stated-result level.

### 10. `DK-3.1-cor` — Compact classification by angle eigenvalues

**Verdict:** PASS exact. Previously terminal; retained and re-exposed on the compiler audit surface.

**Counted source atoms:** `DK-3.1-cor.compact-complete-invariants`, `DK-3.1-cor.allowed-angle-sequence`, `DK-3.1-cor.theta1-match`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_compact_defectBlock_angleList_classification`
- `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_compact_classification_real`
- `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_realization`

**Semantic review:**

Accepted by the hostile audit at the stated-result level.

### 11. `DK-3.5-prop` — Angle commutation and eigenspace geometry

**Verdict:** PASS exact. Re-audited in this sweep.

**Counted source atoms:** `DK-3.5-prop.commutation`, `DK-3.5-prop.eigenvector-rotation-angle`, `DK-3.5-prop.acute-maximal-characterization`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.proposition3_5_commutations`
- `TauCeti.DavisKahan1970.proposition3_5_eigenvector_angle`
- `TauCeti.DavisKahan1970.proposition3_5_angleEigenspace_eq_fixedCosineSubspace`
- `TauCeti.DavisKahan1970.proposition3_5_angleEigenspace_uniqueMaximal`

**Semantic review:**

Accepted result-only semantic review 2026-08-12. These `RCLike`-generic Proposition 3.5 source theorems expose exactly the counted statement: commutation of the angle operator with the source operators, the rotation angle on an angle eigenvector, and the maximal reducing eigenspace characterization in the acute case. They work over real or complex Hilbert spaces in arbitrary dimension. The preceding exponential and cosine-square representations are explicitly outside the Proposition 3.5 result boundary and therefore do not block this result.

### 12. `DK-3.2-cor` — Reversal symmetry

**Verdict:** PASS exact. Previously terminal; retained and re-exposed on the compiler audit surface.

**Counted source atoms:** `DK-3.2-cor.swap-invariance`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.corollary3_2_source`
- `TauCeti.DavisKahan1970.corollary3_2_paperQuarterTurn_symm`
- `TauCeti.DavisKahan1970.corollary3_2_nonacute_directRotation_resolution`
- `TauCeti.DavisKahan1970.complex_directRotation_reversal`
- `TauCeti.DavisKahan1970.real_directRotation_reversal`
- `TauCeti.DavisKahan.Frontier.Section3.corollary3_2_reversal_source_form`

**Semantic review:**

Accepted by the hostile audit at the stated-result level.

### 13. `DK-4.1-prop` — Pointwise and singular-value extremality of the direct rotation

**Verdict:** OPEN — genuine result-scope theorem surface remains. Re-audited in this sweep.

**Counted source atoms:** `DK-4.1-prop.orthonormal-angle-lower-bounds`, `DK-4.1-prop.singular-value-minimality`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.Proposition4_1_compact_orthonormalVectors`
- `TauCeti.DavisKahan1970.Proposition4_1_compact_orthonormalVectors_real`
- `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute`
- `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_real`
- `TauCeti.DavisKahan1970.Proposition4_1_directRotationValues`

**Semantic review:**

Result-only audit 2026-08-12: the arbitrary-dimensional compact complex/real theorems already prove the orthonormal-vector angle lower bounds and approximation-number minimality for the direct rotation. The remaining counted clause is the paper's *closed-form minimum value* `2 sin(theta_k/2)` at the same infinite compact scope. `Proposition4_1_directRotationValues` supplies that identity in finite dimension, but no hostile-reviewable infinite compact theorem identifying the approximation-number sequence with the principal chord sequence was located.

**Structured remaining gap:**

- Category: `missing_infinite_compact_closed_form_value`
- Missing surface: At the arbitrary-dimensional compact source scope, identify the direct-rotation displacement approximation-number sequence with the closed form 2 sin(theta_k/2), not only prove extremal minimality.
- Next action: Prove/register the infinite compact approximation-number identity for the direct rotation in terms of the principal chord sequence, over real and complex scalars.
- Strongest current evidence:
  - `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute`
  - `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_real`
  - `TauCeti.DavisKahan1970.Proposition4_1_directRotationValues`

### 14. `DK-4.1-cor` — UI-norm minimality of direct rotation displacement

**Verdict:** PASS exact. Previously terminal; retained and re-exposed on the compiler audit surface.

**Counted source atoms:** `DK-4.1-cor.ui-minimality-on-p`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.Corollary4_1_compact_nonacute`
- `TauCeti.DavisKahan1970.Corollary4_1_compact_nonacute_real`
- `TauCeti.DavisKahan1970.Corollary4_1_infiniteDimensional_nonacute`

**Semantic review:**

Accepted by the hostile audit at the stated-result level.

### 15. `DK-4.2-prop` — Basis-angle square-sum extremality

**Verdict:** PASS exact. Re-audited in this sweep.

**Counted source atoms:** `DK-4.2-prop.basis-sine-square-lower-bound`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.Proposition4_2_infiniteDimensional`
- `TauCeti.DavisKahan1970.tsum_displacementAngleSineSqR_ge_tsum_sq_sin_principalAngleSequence`

**Semantic review:**

Accepted result-only semantic review 2026-08-12. `Proposition4_2_infiniteDimensional` proves the paper's infinite-series basis-angle lower bound over `ℂ`, including the divergent right-hand side through the extended summation formulation; the real theorem gives the literal `ℝ` counterpart. The trace identification used in the source proof is proof-only material and is not part of the counted proposition statement.

### 16. `DK-4.3-prop` — Squared displacement UI-norm minimality

**Verdict:** PASS exact. Re-audited in this sweep.

**Counted source atoms:** `DK-4.3-prop.squared-displacement-global-minimum`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.Proposition4_3_compact_nonacute_idealGauge`
- `TauCeti.DavisKahan1970.Proposition4_3_compact_nonacute_real_idealGauge`

**Semantic review:**

Accepted result-only semantic review 2026-08-12. The compact nonacute complex and real wrappers state Proposition 4.3 at the paper's inherited matched-defect scope and show that the direct rotation minimizes every Ky-Fan-dominant unitary-invariant ideal gauge of the squared full displacement `(1-W*) (1-W)`. The underlying proof is dimension-free; the compact premise is kept in the wrapper solely to match the source setting. Equations (4.3)-(4.6) and the later warning about unsquared displacement are outside the counted proposition boundary.

### 17. `DK-4.4-prop` — Full-displacement counterexamples and Proposition 4.4 as printed

**Verdict:** PASS refuted + repair. Previously terminal; retained and re-exposed on the compiler audit surface.

**Counted source atoms:** `DK-4.4-prop.printed-proposition4-4`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahanTheory.DavisKahanProposition4_4_Finite`
- `TauCeti.DavisKahanTheory.not_davisKahanProposition4_4_Finite`
- `TauCeti.DavisKahanTheory.shortRotation_fullDisplacement_refuted`

**Repair evidence:**
- `TauCeti.DavisKahanTheory.directRotation_fullDisplacement_qnorm`

**Semantic review:**

Accepted by the hostile audit at the stated-result level.

### 18. `DK-5.1-thm` — Banach-space Sylvester lower bound

**Verdict:** PASS exact. Re-audited in this sweep.

**Counted source atoms:** `DK-5.1-thm.banach-hypotheses`, `DK-5.1-thm.sylvester-lower-bound`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_uiNorm`
- `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_exact`
- audit specialization: `TauCeti.DavisKahan1970.Audits.theorem5_1_scalarGeneric_sourceAudit`

**Semantic review:**

Accepted result-only semantic review 2026-08-12, after correcting the scalar-scope overclaim in `ce0f435`. The selected `banach_sylvester_lower_bound_uiNorm` is the scalar-generic reusable theorem (arbitrary nontrivially normed field), so it covers the paper's real/complex Banach-space scope; it assumes only the left-inverse half of the printed two-sided inverse hypothesis and is therefore stronger on hypotheses. `banach_sylvester_lower_bound_exact` remains the literal complex source-shape witness. To make the specialization itself compiler-visible, the maintained audit surface defines `theorem5_1_scalarGeneric_sourceAudit`, which restores both printed inverse equations over a generic scalar field and forwards to the scalar-generic theorem. The A/B interchange and one-sided unbounded remarks follow the theorem and are intentionally outside this counted result boundary.

### 19. `DK-5.2-thm` — Semibounded self-adjoint Sylvester theorem

**Verdict:** PASS exact. Re-audited in this sweep.

**Counted source atoms:** `DK-5.2-thm.hilbert-unbounded-hypotheses`, `DK-5.2-thm.hilbert-unbounded-conclusion`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.Theorem5_2`
- `TauCeti.DavisKahan.ExactSinTheta.davisKahan1970_sylvester_real`

**Semantic review:**

Accepted result-only semantic review 2026-08-12. `Theorem5_2` gives the paper's unbounded complex self-adjoint ordered-spectrum Sylvester inequality for an arbitrary unitary-invariant ideal family, with the exact closed-operator equation and source constant. `davisKahan1970_sylvester_real` supplies the real unbounded counterpart under the more general `FormBoundedSylvesterGap`; that predicate has a `leftAboveRightBelow` constructor whose hypotheses are exactly `A ≥ c + δ` and `B ≤ c`. The compiler audit theorem `theorem5_2_real_ordered_sourceAudit` performs that specialization explicitly, so a reviewer need not infer it from prose. Thus the real and complex printed Hilbert-space theorem is covered without a finite-dimensional restriction.

### 20. `DK-5.1-lem` — Strong-cutoff convergence of singular values

**Verdict:** PASS exact. Previously terminal; retained and re-exposed on the compiler audit surface.

**Counted source atoms:** `DK-5.1-lem.strong-cutoff-convergence`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.Lemma5_1`

**Semantic review:**

Accepted by the hostile audit at the stated-result level.

### 21. `DK-6.1-lem` — Direct-sum UI-norm comparison and converse

**Verdict:** PASS exact. Previously terminal; retained and re-exposed on the compiler audit surface.

**Counted source atoms:** `DK-6.1-lem.ordered-sylvester-forward`, `DK-6.1-lem.ordered-sylvester-converse`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.lemma6_1`
- `TauCeti.DavisKahan1970.lemma6_1_converse`

**Semantic review:**

Accepted by the hostile audit at the stated-result level.

### 22. `DK-6.2-lem` — Reflection-pinch contraction

**Verdict:** PASS exact. Previously terminal; retained and re-exposed on the compiler audit surface.

**Counted source atoms:** `DK-6.2-lem.pinching-contraction`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.lemma6_2`

**Semantic review:**

Accepted by the hostile audit at the stated-result level.

### 23. `DK-6.1-prop` — Sine proof, ambient limitation, and symmetric sine theorem

**Verdict:** PASS exact. Re-audited in this sweep.

**Counted source atoms:** `DK-6.1-prop.symmetric-sine-theorem`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.Proposition6_1`
- `TauCeti.DavisKahan1970.Proposition6_1_real`

**Semantic review:**

Accepted result-only semantic review 2026-08-12. The complex and real Proposition 6.1 aliases are direct source-facing PaperUI theorems for the two-sided spectral-placement hypothesis and the ambient sine bound `delta * N(sin Theta) <= N(H)` for every paper unitary-invariant norm. The Sylvester identity (6.1) and the source counterexample explaining why one-sided placement is insufficient are outside the counted proposition statement.

### 24. `DK-6.1-thm` — Generalized sine theorem

**Verdict:** PASS exact. Previously terminal; retained and re-exposed on the compiler audit surface.

**Counted source atoms:** `DK-6.1-thm.generalized-sine-hypotheses`, `DK-6.1-thm.generalized-sine-conclusion`, `DK-6.1-thm.unequal-dimension-scope`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.Theorem6_1`
- `TauCeti.DavisKahan1970.Theorem6_1_real`
- `TauCeti.DavisKahan1970.Theorem6_1_real_commonDomain`
- `TauCeti.DavisKahan1970.Theorem6_1_real_commonCore`

**Semantic review:**

Accepted by the hostile audit at the stated-result level.

### 25. `DK-6.2-thm` — Pairwise-gap square-norm sine theorem

**Verdict:** PASS exact. Re-audited in this sweep.

**Counted source atoms:** `DK-6.2-thm.second-generalized-sine`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.Theorem6_2`
- `TauCeti.DavisKahan1970.Theorem6_2_real`

**Semantic review:**

Accepted result-only semantic review 2026-08-12. The complex and real Theorem 6.2 wrappers state the pairwise-gap Hilbert-Schmidt sine inequality with the source lower-frame factor epsilon at the unbounded/common-domain source scope. The rank-corrected operator-norm consequence is an immediate post-theorem consequence in the source and is explicitly outside the 29-result denominator.

### 26. `DK-6.3-thm` — Tangent proof machinery, Example 6.1, and generalized tangent theorem

**Verdict:** PASS exact. Re-audited in this sweep.

**Counted source atoms:** `DK-6.3-thm.generalized-tangent-theorem`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists`
- `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_real`
- `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_spectral`
- `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real_spectral`

**Semantic review:**

Accepted result-only semantic review 2026-08-12. The unbounded infinite-trial complex and real theorems construct the directed tangent representative and prove the sharp source residual bound for every unitary-invariant ideal gauge at arbitrary trial dimension. The spectral PaperUI wrappers expose the same theorem in the paper's bounded/source notation. Equations (6.2)-(6.6) and Example 6.1 are proof/example material and are not part of the counted Theorem 6.3 statement.

### 27. `DK-6.3-lem` — Finite-rank near-maximizer leakage estimate

**Verdict:** PASS exact. Previously terminal; retained and re-exposed on the compiler audit surface.

**Counted source atoms:** `DK-6.3-lem.approximation-number-leakage`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan.Frontier.Section6Appendix.lemma6_3_approximationNumber_leakage`
- `TauCeti.DavisKahan.Frontier.Section6Appendix.lemma6_3_singularValue_leakage`
- `TauCeti.DavisKahan.Frontier.Section6Appendix.lemma6_3_approximationNumber_leakage_real`

**Semantic review:**

Accepted by the hostile audit at the stated-result level.

### 28. `DK-8.1-thm` — Branch selection and spectral repulsion

**Verdict:** PASS exact. Previously terminal; retained and re-exposed on the compiler audit surface.

**Counted source atoms:** `DK-8.1-thm.acute-iff-spectral-placement`, `DK-8.1-thm.existence-correct-q`, `DK-8.1-thm.part-i-compression`, `DK-8.1-thm.part-ii-eigenvalue`, `DK-8.1-thm.part-iii-gauge`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch`
- `TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_spectrumIn`
- `TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch_real`
- `TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_spectrumIn_real`
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_source`
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_source`
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_real`
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_real`
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_source`
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_source`
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_real`
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_real`
- `TauCeti.DavisKahan1970.Section8.approximationNumber_eq_eigenvalues_of_isPositive`
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_source`
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev_source`
- `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_real`
- `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev_real`

**Semantic review:**

Result-only hostile review accepted 2026-08-12. The compiled source surface covers every counted Theorem 8.1 clause under the printed hypotheses: branch existence and the closed-quarter-angle iff; part (i) on both blocks; part (ii) in dimension-free approximation-number form with the compiled positive-operator eigenvalue dictionary and real counterparts; and part (iii) for every symmetric gauge in the printed finite-dimensional scope, including increasing-index-order wrappers, over both complex and real Hilbert spaces. The previously recorded blocker was stale evidence selection, not missing mathematics.

### 29. `DK-8.2-thm` — Smallness selects the acute branch

**Verdict:** PASS exact. Re-audited in this sweep.

**Counted source atoms:** `DK-8.2-thm.smallness-alternative`, `DK-8.2-thm.double-angle-bound-retained`, `DK-8.2-thm.acute-branch-conclusion`.

**Selected source-facing Lean declarations:**
- `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_directed`
- `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_paperUINorm`
- `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_source_paperUINorm`
- `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_directed_real`
- `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_real_paperUINorm`
- `TauCeti.DavisKahan.Frontier.Section8.theorem8_2_sinTwoTheta_residual_source_real_paperUINorm`

**Semantic review:**

Accepted result-only semantic review 2026-08-12. The Section 8 source surface exposes both printed half-gap alternatives: perturbation-small and residual-small. The complex and real branch theorems select the acute branch (`Theta < pi/4`), and the PaperUI perturbation/residual theorems retain the corresponding `sin 2Theta` estimate with no constant loss. The proof homotopy, unequal-dimension extension remark, and comment about a tangent extension are adjacent material outside the counted Theorem 8.2 boundary.

## Four remaining mathematical targets

- **`S2-tan-theta` — Single-angle tangent theorem:** Unbounded self-adjoint ambient perturbation theorem delta * N(tan Theta) <= N(H) for every paper unitary-invariant norm under the printed Section 2 ordered-gap/Rayleigh-Ritz hypotheses.
- **`DK-3.3-prop` — Principal square-root characterization:** Real-Hilbert-space full nonacute principal-square-root forward/converse characterization at the printed matched-crossed-defect scope.
- **`DK-3.4-prop` — Square as a direct rotation:** Real-Hilbert-space full nonacute Proposition 3.4: under the printed C0^2 >= 1/2 condition, U^2 is the direct rotation from Q_- to Q.
- **`DK-4.1-prop` — Pointwise and singular-value extremality of the direct rotation:** At the arbitrary-dimensional compact source scope, identify the direct-rotation displacement approximation-number sequence with the closed form 2 sin(theta_k/2), not only prove extremal minimality.

## Reviewer reproduction

Compile the single theorem surface containing all selected declarations and the strongest evidence for the four red results:

```bash
lake env lean DavisKahan/Sources/DavisKahan1970/Audits/ResultSemanticSurface.lean
```

Validate the result ledger and source boundary:

```bash
python3 scripts/check_davis_kahan_1970_result_inventory.py
python3 scripts/check_davis_kahan_1970_statement_map.py
```

The hard 100% gate is intentionally red until the four structured gaps are removed:

```bash
python3 scripts/check_davis_kahan_1970_statement_map.py --require-terminal
```
