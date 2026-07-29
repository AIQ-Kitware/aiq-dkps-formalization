# Proof obligations and repair order

The public statements should not be weakened. Repair in dependency order.

## 1. Raw finite-rank closure density

The standard `.minimal` branch is now represented by the fully symmetric
envelope `MinimalFullySymmetricMem`.  Its Fan-dominance theorem is explicit and
contains no automation.

The remaining identification theorem is

```lean
MinimalFullySymmetricMem N A -> FiniteRankGaugeClosure N A
```

The converse is immediate.  Proving this implication identifies the envelope
with the literal gauge closure of finite-rank operators.  It requires the
infinite sequence compactness/diagonal passage and the operator truncation
bridge; it must not be hidden in `aesop`, an assumption, or a structure field.

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

## Status of obligation 5 (recorded 2026-07-29)

`exists_unboundedApproximateLeadingSingularFamily` **was never proved.** Its
body ended in an `aesop` that does not discharge the goal. It is the only thing
keeping `lake build FinishTanTwoTheta` from being green; the other fourteen
failures the lane started with were tactic and coercion repairs and are fixed.

The sketched proof in its docstring — bounded spectral-band family, density of
the domains, finite Gram--Schmidt — **cannot work**. Density and Gram--Schmidt
control `‖·‖` and say nothing about `‖A₀ ·‖`, which is exactly what the two
`_apply_norm` clauses demand.

Work since then has closed a lot of ground and eliminated three routes:

* **Proved and axiom-clean**, in `DavisKahan/Riccati/UnboundedAdjointRiccati.lean`:
  the adjoint Riccati equation from the unused half of `ReducesSubspace`; the
  bounded commutator `A₀X†X - X†XA₀ = G` with `‖G‖ ≤ 2(‖B₀₁‖+‖B₁₀‖)`; entire
  functions of `X†X` preserving `dom A₀`; the resolvent `(1 - X†X)⁻¹` doing the
  same; `tan 2Theta` transporting the domains; and the pointwise Sylvester
  identity. Also `abs_doubleAngleTangent_sub_le` in `FunctionalCalculus/`.
* **Refuted.** The remaining step needed `Ran E_T(J) ∩ dom A₀` dense in
  `Ran E_T(J)`. That is false: on `L²(ℝ)` take `K` a fat Cantor set, `f` smooth
  and bounded with `f'` bounded and `f⁻¹({c}) = K`, `T = M_f`, `A = -|D|`. All
  hypotheses hold — `[A,T]` is bounded by Calderón — yet `Ran E_T(J) = L²(K)`
  is infinite-dimensional while `L²(K) ∩ H¹ = {0}`.

**Therefore the sharp constant is an open research question, not a
formalization task.** It is *not* refuted — the counterexample uses only
"`[A,T]` bounded", whereas the real setting ties `T = X†X` to `A₀, A₁, B₀₁` by
two equations — but no route through approximate singular vectors is known to
reach it, and three have now been eliminated at the same point: nothing in the
hypotheses couples the spectral decomposition of `A₀` to that of `X†X`.

What *is* provable today is the **Sylvester defect form**

```
d · kyFan_k(tan 2Theta) ≤ 2 · kyFan_k(B₀₁) + 2 · kyFan_k(R''DR),
D = 2XB₀₁X - XX*B₁₀ - B₁₀X*X
```

which is strictly stronger than the cosine-denominator surrogate this library
was created to beat, and weaker than the sharp statement below. **Whether to
present it as this library's headline result is a human decision**, because
doing so contradicts the first guard. It has not been taken. Full reasoning,
including two further dead ends and the exact remaining steps, is in
[`../dev/finishtantwotheta-completion-lane.md`](../dev/finishtantwotheta-completion-lane.md).

## Guards

- Do not add `sorry`, `admit`, or axioms.
- Do not replace local hard theorems with assumptions or structure fields.
- Do not reintroduce the cosine-denominator surrogate theorem.
- Do not restrict the ambient Hilbert spaces to finite dimension.
- Do not assume compactness of the angular operator.
- Do not use exact singular-vector attainment for an arbitrary bounded operator.
- Do not apply the bounded Riccati estimate to unbounded diagonal blocks.

