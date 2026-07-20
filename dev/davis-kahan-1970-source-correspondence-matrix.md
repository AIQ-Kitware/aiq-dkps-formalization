# Davis–Kahan 1970 §6 source correspondence matrix

Every row names a declaration that compiles and whose `#print axioms` reports
exactly `propext, Classical.choice, Quot.sound`.  That is checked mechanically
by `scripts/audit_full_paper_sine_theta.py`, which elaborates
`DavisKahan/Sources/DavisKahan1970/Audits/FullPaperSineTheta.lean` and requires
an exact axiom-set match for all 43 targets, one report per target, and no
other output.  The matrix below is the human-readable face of that audit; if
the two ever disagree, the audit is authoritative.

Source-facing names live in `ForMathlib.DavisKahan1970`.  "Target" is the
implementation declaration the source name aliases.

## Shared hypothesis packages

Most rows quantify over a data record rather than a long hypothesis list, so
the records are given once here.

`PaperTheorem61Data` (complex `E F G H`):

| field | meaning |
| --- | --- |
| `data : UnboundedSinThetaData ℂ E F G` | ambient `A`, trial block `A₀`, complement block `Λ₁`, trial map `X`, frame `F₁`, residual |
| `ambient_selfAdjoint`, `trial_selfAdjoint`, `complement_selfAdjoint` | all three closed operators are self-adjoint |
| `exact_decomposition : OrthogonalExactDecomposition exactMap data.F₁` | `exactMap` and `F₁` split the ambient space orthogonally |
| `gap_pos : 0 < gap` | the separation is strictly positive |
| `lowerFrame : LowerFrameBound data.X frameLowerBound`, `frameLowerBound_pos` | the trial map is bounded below |
| `spectral_gap : UnboundedSylvesterGap data.A₀ data.Λ₁ gap` | interval/exterior **or** either ordered half-line orientation |

`PaperTheorem62Data` is identical except that `spectral_gap` is replaced by
`spectral_distance : GenuinePairwiseSpectrumGap data.A₀ data.Λ₁ gap` — the
weaker pairwise-distance hypothesis, which is what makes Theorem 6.2 a
strictly stronger statement in the square norm.

`PaperCommonDomainTheorem61Data` and `PaperCommonCoreTheorem61Data` carry the
same fields over `PaperCommonDomainSinThetaData` / `PaperCommonCoreSinThetaData`
respectively, and each supplies a `PaperTheorem61Data` by construction, so the
appendix forms are specializations rather than parallel proofs.

## Norms

| paper item | source name | target |
| --- | --- | --- |
| unitarily invariant norms ↔ symmetric norming functions | `unitaryInvariantNorm_equiv_symmetricNormingFunction` | `PaperSymmetricNormingFunction.paperNormEquiv` |
| the class is nonempty | `unitaryInvariantNorm_nonempty` | `paperUnitaryInvariantNorm_nonempty` |

## Angle objects

| paper item | source name | target |
| --- | --- | --- |
| directed cosine equals the modulus | `directedCosAngle_eq_modulus` | `paperSourceDirectedCosC_eq` |
| directed sine equals the sine modulus | `directedSinAngle_eq_modulus` | `paperSourceDirectedSinC_eq_paperSineModulusC` |
| directed sine has the sine block's singular values | `directedSinAngle_singularValues` | `paperSourceDirectedSin_same_paperSineBlock` |
| directed angle is `arcsin` of the sine modulus | `directedAngle_eq_arcsin_sineModulus` | `paperSourceDirectedAngleC_eq_arcsin_sineModulus` |
| the same over ℝ | `directedAngle_real_eq_arcsin_sineModulus` | `paperSourceDirectedAngleR_eq_arcsin_sineModulus` |
| real directed sine / cosine | `directedSinAngle_real`, `directedCosAngle_real` | `paperSourceDirectedSinR`, `paperSourceDirectedCosR` |
| full sine matches the projection difference | `fullSinAngle_singularValues_projectionDifference` | `paperSourceFullSin_same_projectionDifference` |
| and agrees in every unitarily invariant norm | `fullSinAngle_norm_projectionDifference` | `paperSourceFullSin_mem_iff_and_gauge_eq` |

## Lemmas 6.1 and 6.2

| paper item | source name | target |
| --- | --- | --- |
| Lemma 6.1, every unitarily invariant norm | `lemma6_1` | `paperLemma61_every_unitarilyInvariantNorm` |
| Lemma 6.2, diagonal pair gauge bound | `lemma6_2` | `paperDiagonalPair_paperGauge_le` |

## Theorem 6.1

Conclusion: membership of the directed sine block in the ideal, and
`gap * ‖sin Θ‖ ≤ ‖residual‖` in **every** unitarily invariant norm
(`_across` = across the whole norm family, not one fixed gauge).

| paper item | source name | target |
| --- | --- | --- |
| Theorem 6.1, complex | `Theorem6_1` | `PaperTheorem61Data.result_every_unitarilyInvariantNorm_across` |
| Theorem 6.1, real | `Theorem6_1_real` | `PaperRealTheorem61Data.result_every_unitarilyInvariantNorm_across` |
| isometric-trial form, complex | `sinTheta_exactPaper` | `PaperIsometricTheoremData.result_every_unitarilyInvariantNorm_across` |
| isometric-trial form, real | `sinTheta_real_exactPaper` | `PaperRealIsometricTheoremData.result_every_unitarilyInvariantNorm_across` |
| generalized (lower-frame) form, complex | `generalizedSinTheta_exactPaper` | `PaperTheorem61Data.result_every_unitarilyInvariantNorm_across` |
| generalized (lower-frame) form, real | `generalizedSinTheta_real_exactPaper` | `PaperRealTheorem61Data.result_every_unitarilyInvariantNorm_across` |

## Proposition 6.1

Hypotheses differ from Theorem 6.1: two **bounded** symmetric operators `A`,
`B`, reducing subspaces `U` for `A` and `V` for `B`, and *two* gap conditions,
`U → Vᗮ` and `V → Uᗮ`.  The two-sided hypothesis is what the counterexample
rows below show cannot be weakened to a single gap.

| paper item | source name | target |
| --- | --- | --- |
| Proposition 6.1 | `Proposition6_1` | `PaperSymmetricSinThetaProblem.result_every_unitarilyInvariantNorm` |

## Theorem 6.2

| paper item | source name | target |
| --- | --- | --- |
| Theorem 6.2, complex | `Theorem6_2` | `PaperTheorem62Data.result_across` |
| Theorem 6.2, real | `Theorem6_2_real` | `PaperRealTheorem62Data.result_across` |
| printed finite-rank operator-norm consequence, complex | `Theorem6_2_boundNorm_of_finiteRank` | `PaperTheorem62Data.operatorNorm_result_across_of_rank_le` |
| the same over ℝ | `Theorem6_2_real_boundNorm_of_finiteRank` | `PaperRealTheorem62Data.operatorNorm_result_across_of_rank_le` |

## Appendix: common-domain and common-core forms

| paper item | source name | target |
| --- | --- | --- |
| Theorem 6.1, common domain, complex | `Theorem6_1_commonDomain` | `PaperCommonDomainTheorem61Data.result_every_unitarilyInvariantNorm_across` |
| Theorem 6.1, common domain, real | `Theorem6_1_real_commonDomain` | `PaperRealCommonDomainTheorem61Data.result_every_unitarilyInvariantNorm_across` |
| Theorem 6.2, common domain, complex | `Theorem6_2_commonDomain` | `PaperCommonDomainTheorem62Data.result_across` |
| Theorem 6.2, common domain, real | `Theorem6_2_real_commonDomain` | `PaperRealCommonDomainTheorem62Data.result_across` |
| the core residual extends to the whole domain | `commonCoreResidual_extends_to_domain` | `PaperCommonCoreResidualData.extends_to_domain` |
| Theorem 6.1, common core, complex | `Theorem6_1_commonCore` | `PaperCommonCoreTheorem61Data.result_every_unitarilyInvariantNorm_across` |
| Theorem 6.1, common core, real | `Theorem6_1_real_commonCore` | `PaperRealCommonCoreTheorem61Data.result_every_unitarilyInvariantNorm_across` |
| Theorem 6.2, common core, complex | `Theorem6_2_commonCore` | `PaperCommonCoreTheorem62Data.result_across` |
| Theorem 6.2, common core, real | `Theorem6_2_real_commonCore` | `PaperRealCommonCoreTheorem62Data.result_across` |

## Equality, optimality, and the one-gap counterexample

| paper item | source name | target |
| --- | --- | --- |
| the bound is attained (planar case), every norm | `Theorem6_1_equality_every_norm` | `paperTheorem61_planar_equality_every_norm` |
| constant one cannot be improved | `sineTheta_constant_one_optimal` | `paperSinTheta_constant_one_optimal` |
| counterexample: sine block, square norm | `oneGap_counterexample_sine_squareNorm` | `paperCounterexample_sine_square_norm` |
| counterexample: perturbation, square norm | `oneGap_counterexample_perturbation_squareNorm` | `paperCounterexample_perturbation_square_norm` |
| one gap does **not** suffice for Proposition 6.1 | `oneGap_does_not_imply_Proposition6_1` | `paperOneGap_does_not_imply_symmetric_square_estimate` |

## Finite multiplicity

These five are stated directly in
`DavisKahan/Sources/DavisKahan1970/SineTheta/FiniteMultiplicity.lean` rather
than aliased.  The model is explicit: a finite-multiplicity source with an
injectivity witness, no ideal-membership hypothesis, and no collapse to scalar
homogeneity.

| paper item | source name |
| --- | --- |
| residual identity | `finiteMultiplicity_residual_identity` |
| directed sine identity | `finiteMultiplicity_directedSine_identity` |
| the complement map lies in the ideal | `finiteMultiplicityComplementMap_mem` |
| Theorem 6.1 equality in every norm | `Theorem6_1_finiteMultiplicity_equality_every_norm` |
| the sine block is injective | `finiteMultiplicitySineBlock_injective` |

## Audit selection note

The 43-target executable audit covers the principal endpoints above, not every
theorem-valued alias exported by `FullSineTheta.lean`.  In particular, the
converse direction of Lemma 6.1 is proved as `lemma6_1_converse` but is not yet
printed as a separate audit target.  The same is true of several finite-Ky-Fan
forms, source-norm law aliases, and common-domain finite-rank corollaries.
Expanding or generating the target list is acceptance hardening, not a missing
mathematical step in Theorems 6.1 or 6.2.

## What is *not* claimed

The audit covers the 43 endpoints above.  It does not cover:

- the scalar-generic isometric theorem `IsometricSinThetaProblem.result`, which
  still routes through the legacy unbounded engine; the paper surface uses the
  complex and real routes instead, both of which are proved.  See
  `DavisKahan/Experimental/InfiniteDimensional/SinTheta/Canonical.lean`;
- the generic spectral cutoff and bounded truncation API in
  `DavisKahan/Experimental/InfiniteDimensional/Core/UnboundedSpectral.lean`,
  which remains an open API test bed.  Nothing in production depends on it: the
  production interval/exterior estimate comes from the vendored Spectra
  calculus;
- the 111 Part III manuscript aliases in `DavisKahan/Experimental/PartIII.lean`,
  of which 78 report `sorryAx` and 33 are proved but not yet extracted from
  files that carry unrelated obligations;

The former `PaperHilbertSchmidtSylvester` draft is no longer an open item.  Its
three intended public square-norm Sylvester declarations are restored in
`DavisKahan/Sources/DavisKahan1970/Sylvester/PaperHilbertSchmidt.lean` through
the completed defect-first pairwise-gap proof.  The unrealized joint-PVM
construction is documented separately in
`dev/paper-hilbert-schmidt-history-recovery-2026-07-20.md` and is not claimed as
an additional proof.
