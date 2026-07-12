/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 High
-/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite means and centered scatter operators

This file scaffolds the deterministic online covariance identities needed by Perfect Quench
and useful independently of singular-value theory. It is deliberately not imported by
`ForMathlib.lean` while signatures and proofs are being audited.

The primary theorem is the exact add-one scatter identity

`S(z ++ [y]) = S(z) + n/(n+1) • ((y - mean z) ⊗ (y - mean z))`.

Löwner monotonicity, trace growth, and eigenvalue-floor preservation should be short
corollaries of this equality. A later weighted/two-sample merge theorem should generalize the
same algebra, but the unweighted add-one theorem is the first contribution-sized unit.
-/

namespace ForMathlib

open Module
open scoped BigOperators

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Arithmetic mean of a `Fin n` family. At `n = 0`, Mathlib's total inverse convention makes
this zero.
-/
noncomputable def finiteMean {n : ℕ} (z : Fin n → E) : E :=
  ((n : 𝕜)⁻¹) • ∑ i, z i

/-- Append one point to a `Fin n` family, placing the new point at the final index. -/
noncomputable def appendFin {n : ℕ} (z : Fin n → E) (y : E) : Fin (n + 1) → E :=
  Fin.lastCases y z

/-- Unnormalized centered scatter operator
`∑ i, (zᵢ - mean z) ⊗ (zᵢ - mean z)`.

The rank-one convention is chosen so its quadratic form is
`∑ i, ‖⟪zᵢ - mean z, x⟫‖²`.
-/
noncomputable def centeredScatter {n : ℕ} (z : Fin n → E) : E →ₗ[𝕜] E :=
  ∑ i, (InnerProductSpace.rankOne 𝕜
    (z i - finiteMean z) (z i - finiteMean z)).toLinearMap

/-- The centered residuals sum to zero.

Proof strategy: unfold `finiteMean`, distribute the finite sum, use
`Finset.sum_const`, and cancel `(n : 𝕜)⁻¹ * n`. Split `n = 0` before invoking a nonzero cast.
This lemma is the simplification engine for every scatter update.
-/
theorem sum_sub_finiteMean_eq_zero {n : ℕ} (z : Fin n → E) :
    ∑ i, (z i - finiteMean z) = 0 := by
  sorry

/-- Mean after appending one point.

For `n + 1` nonzero by construction, the formula is
`mean(z ++ [y]) = (n/(n+1)) • mean z + (1/(n+1)) • y`.

Proof strategy: expand the sum over `Fin (n+1)` with `Fin.sum_univ_succ` or the matching
`lastCases` lemma, unfold `finiteMean`, and normalize field casts. Keep the formula in a form
that makes subtracting the old mean straightforward.
-/
theorem finiteMean_append {n : ℕ} (z : Fin n → E) (y : E) :
    finiteMean (appendFin z y) =
      (((n : ℝ) / (n + 1) : ℝ) : 𝕜) • finiteMean z +
        (((1 : ℝ) / (n + 1) : ℝ) : 𝕜) • y := by
  sorry

/-- Exact add-one centered-scatter identity.

Mathematical statement:

`S_{n+1} = S_n + n/(n+1) • (y - mean_n) ⊗ (y - mean_n)`.

Executable proof strategy:

1. Set `δ = y - finiteMean z` and rewrite the new mean with `finiteMean_append`.
2. For each old point, express its new centered residual as
   `(z i - finiteMean z) - (1/(n+1)) • δ`.
3. Express the new point residual as `(n/(n+1)) • δ`.
4. Expand every rank-one term using bilinearity in both vector arguments.
5. Sum the cross terms and eliminate them with `sum_sub_finiteMean_eq_zero`.
6. Normalize the remaining scalar coefficient to `n/(n+1)` by `field_simp`/`ring` after
   proving `(n + 1 : 𝕜) ≠ 0`.

Do not prove only a quadratic-form inequality: retaining the exact operator equality gives
trace, determinant, and merge-formula corollaries for free.
-/
theorem centeredScatter_append {n : ℕ} (z : Fin n → E) (y : E) :
    centeredScatter (appendFin z y) = centeredScatter z +
      (((n : ℝ) / (n + 1) : ℝ) : 𝕜) •
        (InnerProductSpace.rankOne 𝕜
          (y - finiteMean z) (y - finiteMean z)).toLinearMap := by
  sorry

/-- Centered scatter is positive. -/
theorem centeredScatter_isPositive {n : ℕ} (z : Fin n → E) :
    (centeredScatter z).IsPositive := by
  sorry

/-- Appending a point can only increase unnormalized centered scatter in Löwner order.

Proof strategy: rewrite with `centeredScatter_append`; prove the scalar coefficient
nonnegative; prove the rank-one self-operator positive; conclude with
`LinearMap.nonneg_iff_isPositive` and ordered-add-monoid simplification.
-/
theorem centeredScatter_le_append {n : ℕ} (z : Fin n → E) (y : E) :
    centeredScatter z ≤ centeredScatter (appendFin z y) := by
  sorry

/-- Quadratic-form version of the add-one identity.

This is the direct adapter needed by Perfect Quench. It should be proved by applying
`congrArg (fun T => RCLike.re (inner 𝕜 (T x) x))` to `centeredScatter_append`, not by
repeating the finite-sum expansion.
-/
theorem re_inner_centeredScatter_append {n : ℕ}
    (z : Fin n → E) (y x : E) :
    RCLike.re (inner 𝕜 (centeredScatter (appendFin z y) x) x) =
      RCLike.re (inner 𝕜 (centeredScatter z x) x) +
        (n : ℝ) / (n + 1) * ‖inner 𝕜 (y - finiteMean z) x‖ ^ 2 := by
  sorry

/-! ## Planned two-sample merge theorem

After the add-one API is stable, add the canonical two-sample identity

`S(x ⊔ y) = S(x) + S(y) + m*n/(m+n) • (mean x - mean y) ⊗ (mean x - mean y)`.

Do not freeze its Lean signature until the project chooses the canonical finite-family
concatenation/reindexing API (`Fin (m+n)`, `Fin m ⊕ Fin n`, or a general `Fintype` family).
The proof should perform one residual expansion around the pooled mean rather than iterate
`centeredScatter_append`; that route generalizes directly to weighted samples and exposes the
rank-one positive correction.
-/

end ForMathlib
