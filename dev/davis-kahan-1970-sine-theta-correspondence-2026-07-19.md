# Davis--Kahan 1970 sine-theta correspondence matrix

Date: 2026-07-19
Base commit: `d9eeaa37c205b37177c03f456f44b7355bf0925f`

This table is the review contract for claiming literal coverage of the
sine-theta material in the paper.  The compiler-accepted general theorem at the
base commit is preserved unchanged.  Everything marked **compiler-pending** is
new in the exact-paper layer and must be accepted before making the stronger
claim.

| Paper item | Literal requirement | Lean declaration | Status |
|---|---|---|---|
| Section 1 norm | One normalized unitarily invariant norm, coherently across dimensions | `PaperUnitaryInvariantNorm` | compiler-pending |
| Symmetric-gauge equivalence | Every paper norm corresponds to one coherent symmetric norming function and conversely | `PaperSymmetricNormingFunction.paperNormEquiv` | compiler-pending; high API risk |
| Compatibility | `N(VKW) <= N(K)` for contractions | `PaperUnitaryInvariantNorm.gauge_comp_le_of_contractions` | compiler-pending |
| Ky Fan theorem | All finite Ky Fan inequalities imply every paper norm inequality | `mul_gauge_le_of_all_mul_kyFan_le` | compiler-pending |
| Directed cosine | Positive modulus of the overlap block | `paperCosineModulusC` | compiler-pending |
| Directed angle | `Theta_0 = arccos |P_V|_U` | `paperSourceDirectedAngleC` | compiler-pending |
| Literal directed sine | Functional-calculus sine of the angle | `paperSourceDirectedSinC` | compiler-pending |
| Sine/block identity | Literal sine has the cross block's complete singular data | `paperSourceDirectedSin_same_paperSineBlock` | compiler-pending |
| Full angle | Direct sum of the two directed angles | `paperSourceFullAngleC`, `paperSourceFullAngleR` | compiler-pending |
| Full sine | Same singular data as `P-Q` | `paperSourceFullSin_same_projectionDifference` | compiler-pending |
| Real angle | Canonical complexification of real projection geometry | `paperSourceDirectedAngleR`, `paperSourceFullAngleR` | compiler-pending |
| Lemma 6.1 | Sharp block coupling and converse | `paperLemma61_every_unitarilyInvariantNorm`, `paperLemma61_converse` | compiler-pending |
| Lemma 6.2 | Reflection-pinch contraction | `paperDiagonalPair_paperGauge_le` | compiler-pending |
| Original sine theorem | Isometric, arbitrary paper norm, arbitrary representative | `PaperIsometricTheoremData.result_every_unitarilyInvariantNorm_across` | compiler-pending; depends on accepted theorem |
| Proposition 6.1 | Two directional gaps imply full symmetric sine estimate | `PaperSymmetricSinThetaProblem.result_every_unitarilyInvariantNorm` | compiler-pending |
| Theorem 6.1 | Lower frame, unequal dimensions, arbitrary paper norm and representative | `PaperTheorem61Data.result_every_unitarilyInvariantNorm_across` | compiler-pending; depends on accepted theorem |
| Theorem 6.1 real | Same statement over real Hilbert spaces | `PaperRealTheorem61Data.result_every_unitarilyInvariantNorm_across` | compiler-pending |
| Theorem 6.2 | Pairwise spectral distance, square norm, constant one | `PaperTheorem62Data.result_across` | compiler-pending; deepest new analysis |
| Theorem 6.2 real | Exact complexification of square-norm theorem | `PaperRealTheorem62Data.result_across` | compiler-pending |
| Finite-rank fallback | Bound norm times square root of residual rank | `operatorNorm_result_of_rank_le` | compiler-pending |
| Unbounded appendix | Equality of the two product domains and bounded extension of the residual | `HasPaperCommonDomain`, `PaperCommonDomainTheorem61Data`, `PaperCommonDomainTheorem62Data` | compiler-pending |
| Common-domain representatives | Arbitrary coordinate realization of `sin Theta_0` | `result_every_unitarilyInvariantNorm_across`, `result_across` in the common-domain namespaces | compiler-pending |
| Sharpness | Equality for every normalized norm in a planar model | `paperTheorem61_planar_equality_every_norm` | compiler-pending |
| Optimal constant | No constant below one works universally | `paperSinTheta_constant_one_optimal` | compiler-pending |
| Finite multiplicity | Orthogonal sums retain simultaneous equality | no complete declaration yet; `paperFiniteDimensional_scalar_homogeneity` is only a supporting identity | open |
| Pre-Proposition counterexample | One directional gap does not imply the symmetric square estimate | `paperOneGap_does_not_imply_symmetric_square_estimate` | compiler-pending |

## Already accepted dependency

The new Theorem 6.1 and original-sine wrappers reduce every finite Ky Fan
inequality to the compiler-accepted complex and real general sine-theta chain at
this base.  That accepted chain is not modified by this layer.

## Largest remaining mathematical implementation

Theorem 6.2 needs the rectangular Hilbert--Schmidt Plancherel theorem for the
closed Sylvester operator.  The proof manuscript fixes the intended
construction: identify Hilbert--Schmidt operators with a Hilbert tensor
product, represent left and right multiplication by strongly commuting
self-adjoint operators, use their joint spectral measure, and estimate the
multiplier `lambda-alpha` pointwise.  The current Lean leaf names the required
construction explicitly; its supporting tensor/operator package does not yet
exist in the vendored Spectra API and is the highest-priority compiler-agent
implementation task.
