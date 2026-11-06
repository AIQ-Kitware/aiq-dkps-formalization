# YWS lecture: mathematical and formal correspondence

The main result is Yu, Wang, and Samworth, *A Useful Variant of the Davis–Kahan
Theorem for Statisticians*, Biometrika 102 (2015), 315–323,
[DOI](https://doi.org/10.1093/biomet/asv008), with a
[2014 preprint](https://arxiv.org/abs/1405.0680). Repository references and their
source reviews are treated as validated. This lecture is about the mathematics,
not a new theorem or a complete reading of every passage of the article.

## Scope and notation

For the rectangular section, the selected indices satisfy 1 <= r <= s <= rank(B),
as in the source. The gap is corrected to use the ambient Gram spectrum.

The core states and proves both conclusions of Theorem 2 for real symmetric
matrices. It explains the mixed-gap motivation from Theorem 1, then gives the
Gram-matrix reduction for the corrected ambient-spectrum version of Theorem 3.
The sharpness constructions, the source's double-angle warning, and its survey
of statistical applications are not individually developed here.

| Lecture | Paper / source reconstruction | Meaning |
| --- | --- | --- |
| A, A-hat, H | Sigma, Sigma-hat, E | Population matrix, estimated matrix, perturbation. |
| g | Delta | Exact positive population exterior boundary gap. |
| V, V-hat | V, V-hat | Orthonormal eigenframes at matching ordered positions. |
| V-perp, Lambda-one | V-one, Lambda-one | Complementary population eigenframe and its eigenvalue block. |
| X | V-one transpose V-hat | Unwanted estimated-frame coordinates. |
| R | V-hat Lambda minus Sigma V-hat | Population-eigenvalue residual used in this proof. It is different from the zero sample eigen-equation residual. |
| N | min(sqrt(d) operator norm(E), Frobenius norm(E)) | Common numerator before the factor two. |
| B, B-hat, D | A, A-hat, D in Theorem 3 | Rectangular matrices and their perturbation. |
| g_sv | Delta_sv | Corrected exterior gap in the squared singular values, including the Gram matrix's zero eigenvalues. |

Paper indices start at one; Lean source-facing indices start at zero. The
lecture explains proper blocks first; missing boundary gaps are omitted, and
the full-space case has zero sine error and exact alignment. The two theorems
used in `facts.lean` retain the source's full endpoint encoding through
`SourcePopulationGap`, rather than asserting an arbitrary gap parameter.

## Scene anchors

| Scenes | Source claim / argument | Lean evidence |
| --- | --- | --- |
| YsSetup, YsMotivation, YsMixedExample | Theorem 1 motivation and published diagonal example; ordered positions 2..4, population gap 10, mixed interval gap 0. | `Symmetric/MixedGap.lean`; `section1_weylRecovery_fails` and source census. |
| YsGap, YsGeometry | Exterior boundary gap, principal angles, unwanted-component Frobenius identity. | `Symmetric/Theorem2.lean`: `IsEigenvectorBlock`, `PopulationBoundaryGap`, `SourcePopulationGap`; `Symmetric/AngleIdentity.lean`. |
| YsTheorem | Theorem 2, both conclusions. | `theorem2_sinTheta`, `theorem2_alignedFrame`. |
| YsResidual through YsFrobeniusUpper | Source proof residual identity, compression, Weyl and Hoffman–Wielandt estimates. | `Core/Residual.lean`; `Core/Statistics.lean`; source reconstruction proof equations YWS-4 and YWS-5. |
| YsBlocks through YsCombine | Population spectral coordinates, entrywise squared Frobenius lower estimate, residual sandwich. | `Core/Residual.lean`, `Core/Statistics.lean`, source reconstruction YWS-6 and YWS-7. The lecture uses an entrywise proof instead of introducing vec/Kronecker notation. |
| YsAlignment, YsAlignmentProof | SVD alignment and cos(theta) >= cos(theta)^2 on the principal-angle range; source YWS-8. | `Core/Procrustes.lean`; `theorem2_alignedFrame` produces a matrix in `Matrix.orthogonalGroup`. |
| YsRotationExample | Two-dimensional rotated eigensystem illustration, with exact residual and perturbation norms. | `Symmetric/PlanarSharpness.lean` is related source evidence; the lecture uses its own tested illustrative model and does not claim to reproduce every sharpness parameter convention. |
| YsRectangular, YsRectangularGap | Corrected Theorem 3 through the full Gram spectrum. | `Rectangular/SourceTheorem3.lean`, `Rectangular/SingularBlock.lean`, `Rectangular/RankBoundary.lean`; printed rank-boundary refutation is separate from the corrected theorem. |
| YsFacts, YsLean, YsLeanAligned | Checked applications of both paper-facing Theorem 2 conclusions. | Local `facts.lean` imports `YuWangSamworth2015.Symmetric.Theorem2`. No desired inequality is assumed in the companion context. |
| YsComputation | Optional experimental workflow; principal-angle and orthogonal-alignment identities. | Computational illustration, not a verified executable eigensolver or a sample-only population-gap certificate. |

## Lean companion aliases

All context is included in `facts.lean`: symmetry, block indices and dimension,
ordered eigenframes, positive exact source gap. The rendered cards show the
applications after this context. The compact names are **notations**, not
additional hypotheses or approximate substitutes:

- `noise` expands to the minimum of dimension-scaled operator and Frobenius norms.
- `sinError` expands to `Submodule.sinThetaFrobenius` of the supplied frame spans.
- `alignedError O` expands to the square root of the sum of squared column
  differences of V-hat O and the supplied V.

The mathematical card before the Lean cards repeats the symbolic inequalities.
The code cards disclose their assumptions and point to this complete context.
No library proof is copied or replaced by a slide-specific axiom.

## Source boundary worth retaining

The printed Theorem 3 assigns an infinity convention at a rank-based index.
The repository records a counterexample and the repair: retain all zero
Gram eigenvalues through the ambient dimension and place the missing-boundary
convention beyond that ambient spectrum. The rectangular slide explicitly
labels its statement as corrected. This is a known source disposition, not an
unresolved validation request. The main symmetric Theorem 2 needs no such repair.

## Files to consult

- [Source reconstruction](../../../prose/distilled_literature/YuWangSamworth2015_statistical_davis_kahan.tex)
- [Source census](../../../dev/yu-wang-samworth-2015-full-source-census.md)
- [Paper-facing Theorem 2](../../../YuWangSamworth2015/YuWangSamworth2015/Symmetric/Theorem2.lean)
- [Population residual proof](../../../YuWangSamworth2015/YuWangSamworth2015/Core/Residual.lean)
- [Statistics and theorem engine](../../../YuWangSamworth2015/YuWangSamworth2015/Core/Statistics.lean)
- [Alignment](../../../YuWangSamworth2015/YuWangSamworth2015/Core/Procrustes.lean)
- [Printed rank-boundary disposition](../../../YuWangSamworth2015/YuWangSamworth2015/Rectangular/RankBoundary.lean)
