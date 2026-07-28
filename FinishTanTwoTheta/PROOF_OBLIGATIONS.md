# Proof obligations and repair order

The public statements should not be weakened. Repair in dependency order.

## 1. Minimal fully symmetric completion

`exists_finiteRank_gaugeApproximation_of_kyFan_dominated`

Prove that weak submajorization by an operator in the gauge closure of finite
rank preserves that closure. The maximal/Fatou gauge inequality is already
proved by `PaperUnitaryInvariantNorm.mul_gauge_le_of_all_mul_kyFan_le`. The new
part is order continuity of the minimal completion, using finite truncations,
the additive approximation-number inequality, and finite weak majorization.

## 2. PVM spectral-band selection

`exists_gramSpectralBandModel`

Partition the finitely many relevant approximation-number levels into narrow
positive Gram bands. Use the existing threshold min--max theorem to obtain the
required dimensions, select finite subspaces from disjoint PVM ranges, and
diagonalize each finite compression. Band width gives the Gram residual.

## 3. Approximation-number spectral mapping

`exists_rank_le_norm_doubleAngleTangent_sub_lt`

For `u > a_n(X)`, prove the Gram projection of `(u^2, infinity)` has rank at
most `n`; otherwise the existing linear-independent min--max theorem
contradicts `u > a_n(X)`. Compose the tangent operator with that projection.
The complementary PVM range has norm bounded by `2u/(1-u^2)`.

`doubleAngleTangent_approximationNumber_le`

Use an approximate singular family of length `n+1`, the explicit tangent-action
stability estimate, and the existing linear-independent min--max lower bound.

## 4. Bounded sharp theorem

`stableSingularPair_doubleAngleTangent_le` is written explicitly. Compiler
repairs should preserve the paired coefficient; replacing it by an operator
norm loses the Ky Fan theorem.

`sharp_transformed_prefix` must keep the stability constant independent of the
chosen epsilon before taking the epsilon limit.

## 5. Unbounded graph-norm selection

`exists_unboundedApproximateLeadingSingularFamily`

This is not a bounded specialization. Approximate the finite ambient singular
family simultaneously in the graph norms of `A0` and `A1`. Reduction of the
selected graph supplies the complementary/adjoint domain compatibility. Use a
finite orthonormal correction with tolerance below the strict singular-value
margins.

`unboundedStableSingularPair_doubleAngleTangent_le` is explicit. Its diagonal
errors use `||A1 e0||` and symmetry to replace `<A0 x,e1>` by `<x,A0 e1>`;
there must be no factors `||A0||` or `||A1||`.

## Guards

- Do not add `sorry`, `admit`, or axioms.
- Do not replace local hard theorems with assumptions or structure fields.
- Do not reintroduce the cosine-denominator surrogate theorem.
- Do not restrict the ambient Hilbert spaces to finite dimension.
- Do not assume compactness of the angular operator.
- Do not use exact singular-vector attainment for an arbitrary bounded operator.
- Do not apply the bounded Riccati estimate to unbounded diagonal blocks.
