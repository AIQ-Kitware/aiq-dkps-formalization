# Table 4: comparison with Lean statements

Audited 2 November 2026. The target is
[`appendix_result_summaries.tex`](appendix_result_summaries.tex), included as
subsection C.1. This checks the table's mathematical summaries against Lean;
it does not replace the original-paper correspondence reviews.

The starting declaration list is the `canonical_evidence` of each of the
29 results in the
[result inventory](../../dev/davis-kahan-1970-formalization-result-inventory.json).
The comparison read all 78 registered statements, then inspected definitions
and supporting results where the table uses a different representation or an
extension. The source tree was inspected at repository revision `00fcbf9ff`
with the manuscript edits in the working tree. No Lean source was changed.

## Corrections made

- **Norm and domain conventions:** made ideal membership explicit for displayed
  norm values, specified exhaustive orthogonal exact frames and domain-preserving
  reducing projections, and distinguished general trial operators from reference
  blocks. The finite interval gap includes `beta <= alpha`.
- **Ambient tangent:** made bounded definedness explicit. In Lean,
  `HasDefinedAmbientTangent` is the projection-gap condition `< 1`.
  The directed Ritz theorem supplies its own tangent representative; it does
  not take this ambient condition as a hypothesis.
- **Double-angle sine:** included the common-domain hypothesis of the registered
  theorem. The double-angle tangent row now names the bounded perturbation.
- **Classification:** stated the actual invariant in the Lean classification:
  the four elementary intersection dimensions and generic-angle spectral
  multiplicity, followed by the separate realization assertion.
- **Eigenvectors and restricted displacement:** required `x != 0` in the angle
  formula and limited the orthonormal-vector assertion to positive principal
  angles. The singular-value comparison still holds at every index, including
  zero padding. Reversal also sends the chosen rotation to its adjoint.
- **Banach Sylvester extension:** included closedness and dense domain for the
  unbounded coefficient; the other coefficient, solution, and right side are
  bounded. Those are the binders of the existing unbounded supporting theorem.
- **Symmetric sine:** retained the unbounded extension using the common-domain
  presentation theorem. The inventory's primary printed-gap witnesses alone
  are bounded-operator statements. Added common domain and bounded difference
  to the row rather than treating those witnesses as unbounded theorems.
- **Rank-dependent statements:** restricted the operator-norm consequence of
  the pairwise-gap theorem to finite-rank residuals. The leakage lemma is stated
  with `n >= 1` and ranks at most `n`, matching its Lean statement.
- **Spectral selection:** named the bounded perturbation and matched crossed
  defects used by the prescribed-target branch theorems. Compression inequalities
  are read in direct-rotation-aligned coordinates as quadratic-form inequalities
  for unbounded operators. Eigenvalue
  and symmetric-gauge repulsion assertions are explicitly finite-dimensional.

## Row-by-row evidence

Names in this table are in `TauCeti.DavisKahan1970` unless a different namespace
is written. A grouped real/complex family means both scalar branches were read.
The inventory supplies the full names of the registered witnesses.

| Table row | Lean evidence inspected | Result of comparison |
| --- | --- | --- |
| `S2-sin-theta` | [`SineTheta/Presentation.lean`](../../DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean), `sinTheta_unbounded_formGap_whereDefinedUIN_rclike`; `IsTrialResidual`, `IsExactSpectralDecomposition`; [`Sylvester/Gap.lean`](../../DavisKahan/Sylvester/Gap.lean), `FormBoundedSylvesterGap` | Directed sine estimate. Isometry, residual/domain identity, exact complementary decomposition, positive gap, and norm membership belong to the shared conventions. The gap has finite interval/exterior and both ordered half-line constructors. |
| `S2-tan-theta` | [`TanThetaDirectedUnbounded.lean`](../../DavisKahan/Sources/DavisKahan1970/TanThetaDirectedUnbounded.lean), `tanTheta_directed_unboundedRitz_normalizedUIN_complex/real`; [`TanThetaUnboundedAmbient.lean`](../../DavisKahan/Sources/DavisKahan1970/TanThetaUnboundedAmbient.lean) and its real sibling, `tanTheta_ambient_unboundedRitz_definedTangent_normalizedUIN_complex/real` | Both displayed bounds, with bounded ambient tangent for the ambient clause. The Ritz data identify the actual compression and bounded residual; the complementary subspace reduces the ambient operator. |
| `S2-sin-two-theta` | [`SinTwoThetaCommonDomain.lean`](../../DavisKahan/Sources/DavisKahan1970/SinTwoThetaCommonDomain.lean), `sinTwoTheta_commonDomain_whereDefinedUIN_rclike` | The two conjuncts give the directed residual and ambient perturbation estimates. Added common domain; the ambient clause uses a bounded symmetric perturbation. |
| `S2-tan-two-theta` | [`TanTwoThetaUnboundedAmbientExact.lean`](../../DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedAmbientExact.lean) and [`TanTwoThetaUnboundedExactReal.lean`](../../DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedExactReal.lean), ambient and directed normalized-UIN families | Ordered form gap, bounded odd perturbation, and reducing target. The proofs supply exclusion of tangent poles. The real directed endpoint reads both operands on the complexification; its supporting symmetric-norming theorem and singular-value transport explain this representation. No additional pole assumption was inserted. |
| `DK-3.1-prop` | [`SeparableSourceScope.lean`](../../DavisKahan/Sources/DavisKahan1970/SeparableSourceScope.lean), `proposition3_1_separable` | Vanishing crossed defects give the direct rotation and its uniqueness from positive diagonal blocks. Uniform projection gap `< 1` is not substituted for this hypothesis. |
| `DK-3.2-prop` | Same file, `proposition3_2_exists_iff_crossedDefectsEquivalent_separable`, `proposition3_2_not_unique_separable`; principal-root identity below | Existence iff crossed defects are isometrically equivalent; on separable Hilbert spaces this is equality of Hilbert dimensions. Nonacute matched defects give distinct rotations. The square is `-I` on crossed defects by the reflection-product identity. |
| `DK-3.3-prop` | Same file, real/complex forward and converse witnesses; [`Section3PrincipalSquareRoot.lean`](../../DavisKahan/Sources/DavisKahan1970/Section3PrincipalSquareRoot.lean), principal-root predicates | Forward square identity and right-half-plane spectrum; converse additionally maps one crossed defect onto the other. The real spectrum assertion is interpreted after complexification. |
| `DK-3.4-prop` | `proposition3_4_full_complex_separable`, `proposition3_4_full_real_separable` in `SeparableSourceScope.lean` | The source cosine-square lower bound is the quadratic condition `norm x ^ 2 / 2 <= norm (Q x) ^ 2` on the source subspace. Squaring gives a direct rotation from the reflected target to the target. |
| `DK-3.1-thm` | [`Section3Classification.lean`](../../DavisKahan/Sources/DavisKahan1970/Section3Classification.lean), real/complex `theorem3_1_spectralMultiplicity_classification_sourceAngle_*`; [`Section3Theorem31Realization.lean`](../../DavisKahan/Sources/DavisKahan1970/Section3Theorem31Realization.lean), real/complex `theorem3_1_realization_sourceExact_*` | Classification compares four trivial dimensions plus the generic-angle invariant. Realization takes self-adjoint angle operators with spectrum in `[0, pi/2]`, spectral multiplicity agreement away from zero, and matching total Hilbert dimension. |
| `DK-3.1-cor` | `corollary3_1_compact_defectBlock_sourceAngleList_classification_separable`; [`Section3Corollary31.lean`](../../DavisKahan/Sources/DavisKahan1970/Section3Corollary31.lean), `corollary3_1_realization_zeroMultiplicity_sourceScope` | Compact defect block gives angle-list classification together with elementary dimensions. The realization theorem permits separate source/complement zero multiplicities. |
| `DK-3.5-prop` | Three `proposition3_5_*_separable` witnesses in `SeparableSourceScope.lean` | Commutation, nonzero eigenvector angle formula, and acute-case maximal reducing eigenspace characterization. Added the missing nonzero-vector restriction. |
| `DK-3.2-cor` | `corollary3_2_separable` in the same file | Swapping the subspaces preserves the angle, negates the quarter-turn, and takes the corresponding rotation to its adjoint. |
| `DK-4.1-prop` | [`Section4DirectRotationSource.lean`](../../DavisKahan/Sources/DavisKahan1970/Section4DirectRotationSource.lean), real/complex `proposition4_1_directRotation_sourceExact_*` | Source direct rotation, compact directed sine block, and unitary intertwiner. Positive-angle indices support the orthonormal vectors; the displacement singular-value formula and comparison quantify over all indices. |
| `DK-4.1-cor` | Same file, real/complex `corollary4_1_directRotation_sourceExact_*` | Competitor restricted-displacement membership gives membership for the direct rotation and the stated norm comparison. |
| `DK-4.2-prop` | `proposition4_2_compact_nonacute_separable`, `proposition4_2_compact_nonacute_real_separable` | Compact angle data, matched crossed defects, arbitrary Hilbert basis, and unitary transporter; extended nonnegative sums retain infinite values. |
| `DK-4.3-prop` | `Section4DirectRotationSource.lean`, real/complex `proposition4_3_directRotation_sourceExact_*` | The compared operator is `(1 - star W) * (1 - W)`, exactly the table's `D(W)`. The formal predicate is `IsSourceDirectRotation`, whose positive diagonal blocks match the table's geometric definition. |
| `DK-4.4-prop` | [`Section4.lean`](../../DavisKahan/Sources/DavisKahan1970/Section4.lean), alias `proposition4_4_refuted`; [`ShortRotationCounterexample.lean`](../../DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean); [`QNorm.lean`](../../DavisKahan/FiniteDimensional/DirectRotation/QNorm.lean), `directRotation_fullDisplacement_qnorm` | The registered result is a negation of the real finite-dimensional printed assertion. The table reports refutation, points to the concrete counterexample, and keeps the finite-dimensional Q-norm repair separate. |
| `DK-5.1-thm` | [`Section5BanachSylvester.lean`](../../DavisKahan/Sources/DavisKahan1970/Section5BanachSylvester.lean), `theorem5_1_banach_sylvester_banachScope`, `theorem5_1_banach_sylvester_interchanged_exact`, `theorem5_1_banach_sylvester_unboundedA` | Compatible cross-map norm, nonnegative radius, positive gap, inverse identities and inverse bound. The unbounded sibling requires a closed densely defined partial map and bounded everywhere left inverse. |
| `DK-5.2-thm` | [`SymmetricNormingFanDominance.lean`](../../DavisKahan/Sources/DavisKahan1970/SymmetricNormingFanDominance.lean), real/complex `theorem5_2_sourceExact_*` | Oppositely semibounded self-adjoint partial maps and `LinearPMap.SylvesterEquation`, including domain mapping, give ideal membership and the norm estimate. |
| `DK-5.1-lem` | [`Section5.lean`](../../DavisKahan/Sources/DavisKahan1970/Section5.lean), `lemma5_1_complex/real` | Strong convergence of orthogonal projections gives convergence of every fixed approximation number for arbitrary bounded `K`; compactness is not required. |
| `DK-6.1-lem` | [`Section6SourceScope.lean`](../../DavisKahan/Sources/DavisKahan1970/Section6SourceScope.lean), four real/complex forward/converse source-operator witnesses | Both corner comparisons quantify over every normalized UIN. The converse needs equisingular corners separately for each of `K` and `L`, as the table says. |
| `DK-6.2-lem` | Same file, `lemma6_2_separable`; definition `diagonalPair` | Two orthogonal projections, bounded `K` in the norm ideal, and the stated two-sided diagonal pinch. |
| `DK-6.1-prop` | Same file, real/complex `proposition6_1_printedGap_sourceExact_*`; [`Proposition61.lean`](../../DavisKahan/Sources/DavisKahan1970/Proposition61.lean), `proposition6_1_commonDomain_presentation_rclike` | Primary witnesses are bounded; the supporting common-domain theorem supplies literal ambient sine for unbounded self-adjoint coefficients with bounded difference and the two form gaps. The second gap is written with slots reversed in Lean; the table's interval/exterior relation is symmetric. |
| `DK-6.1-thm` | `Section6SourceScope.lean`, real/complex printed-gap witnesses; [`Section6SourceNormClass.lean`](../../DavisKahan/Sources/DavisKahan1970/Section6SourceNormClass.lean), `theorem6_1_sourceExact_complex/real` | Lower frame bound, residual equation without isometry, exhaustive exact decomposition, and arbitrary equisingular sine representative. The supporting form-gap endpoints cover ordered half-lines as well as the finite interval/exterior case. |
| `DK-6.2-thm` | `Section6SourceScope.lean`, real/complex `theorem6_2_vacuity_sourceExact_*`; [`SineTheta/Theorem62.lean`](../../DavisKahan/Sources/DavisKahan1970/SineTheta/Theorem62.lean), `TauCeti.DavisKahan.ExactSinTheta.Theorem62Data.operatorNorm_result_of_rank_le` and real-data sibling | Pairwise spectral distance gives the Hilbert--Schmidt bound, with infinity allowed by the registered extended-norm endpoint. The operator-norm corollary separately assumes a finite natural rank bound on the residual. |
| `DK-6.3-thm` | `TanThetaDirectedUnbounded.lean`, `tanTheta_directed_unboundedRitz_normalizedUIN_complex/real` | Isometric Ritz data, reducing complement, ordered form gap, and bounded residual in the ideal. The output includes strict directed-sine approximation bounds and a tangent representative with the stated norm estimate. |
| `DK-6.3-lem` | `Section6SourceScope.lean`, `lemma6_3_leakage_separable_complex/real`; [`Section6AppendixLeakage.lean`](../../DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakage.lean), `approximationEnergy` | Bounded `K`, positive integer rank bound, positive tolerance, invariance of the selected image, and finite sum of squared approximation numbers. Conclusion is the strict operator-norm leakage bound. |
| `DK-8.1-thm` | [`Section8/Theorem81SourceUnbounded.lean`](../../DavisKahan/Sources/DavisKahan1970/Section8/Theorem81SourceUnbounded.lean), branch-existence, maximal-angle equivalence and compression witnesses; [`Theorem81BlockEigenvalue.lean`](../../DavisKahan/Sources/DavisKahan1970/Section8/Theorem81BlockEigenvalue.lean), eight real/complex eigenvalue/gauge witnesses | Bounded off-diagonal perturbation and ordered reference gap. The prescribed-target equivalence takes matched crossed defects. Compression conclusions are quadratic-form bounds on domains. All eight eigenvalue/gauge witnesses have an explicit finite-dimensional instance. |
| `DK-8.2-thm` | [`Section8/Theorem82UnboundedPath.lean`](../../DavisKahan/Sources/DavisKahan1970/Section8/Theorem82UnboundedPath.lean), real/complex branch witnesses; [`Theorem82SourceUnbounded.lean`](../../DavisKahan/Sources/DavisKahan1970/Section8/Theorem82SourceUnbounded.lean), four real/complex perturbation/residual witnesses | Bounded self-adjoint perturbation, reducing subspaces, exact perturbed interval/exterior placement, expanded reference interval, matched crossed defects and the respective strict smallness condition. Both versions give the full acute-branch conclusion; their norm bounds are ambient and directed respectively. |

## Verification

`lake build DavisKahan.All` completed successfully on the inspected source tree.
After that build, a temporary Lean file importing `DavisKahan.All` applied
`#check @...` to all 78 registered declarations and nine supporting declarations;
`lake env lean /tmp/DkpsTable4Audit.lean` exited successfully. The additional
declarations cover the unbounded/interchanged Banach estimate, common-domain
symmetric sine, full-gap lower-frame bounds, real/complex finite-rank
operator-norm corollaries, Q-norm repair, and the real directed double-angle
tangent's symmetric-norming presentation.

`make -C papers/dk_formalization_journal paper` passed with no warnings,
undefined references, or overfull boxes. The detailed table retains the same
29 distinct IDs in the same order as Table 3. It now spans pages 29--32,
including its shared conventions. `git diff --check` also passed.

This is a manual comparison document. It adds no checker, CI gate, or new
mathematical obligation. The table summarizes main conclusions; it does not
reproduce every conjunct of every source result.
