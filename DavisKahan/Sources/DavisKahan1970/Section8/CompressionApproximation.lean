/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-!
# The compression sandwich bound behind Theorem 8.1(ii)

Printed Theorem 8.1(ii) compares the ordered eigenvalues of `A₁` with those of
`Λ₁` through the factor `‖C₁‖²`.  Part (i) supplies the operator inequality

  `A₁ - α ≤ C₁ (Λ₁ - α) C₁`,

so what part (ii) additionally needs is that a *cosine sandwich* cannot increase
the `k`-th singular value by more than `‖C₁‖²`:

  `aₙ(C⋆ M C) ≤ ‖C‖² · aₙ(M)`.

This is that estimate.

## Why approximation numbers rather than `singularValues`

The obvious route is `singularValues_comp_le` / `singularValues_comp_le'` in
`ForTauCeti/Analysis/InnerProductSpace/KyFan.lean`.  It does not work here, and
the reason is worth recording so it is not re-attempted: the right-factor lemma
`singularValues_comp_le'` is stated only for the *square* case `X C : E →ₗ[𝕜] E`,
and its proof routes through `singularValues_adjoint`, which is likewise square
only.  In Theorem 8.1(ii) the sandwich is genuinely cross-space -- `C₁` maps the
old complement `Pᗮ` to the new one `Qᗮ` -- so neither applies.

`ContinuousLinearMap.approximationNumber` has both one-sided bounds without any
squareness assumption, and they are already used cross-space elsewhere (see
`ForTauCeti/Analysis/OperatorIdeal/Family/SymmetricGauge.lean`, which chains them
over `L ∘L A ∘L R`).  They are also `ContinuousLinearMap`-native, which is the
form the whole Section 8 development is written in, so no transfer to `LinearMap`
is needed either.

In finite dimensions the approximation numbers of an operator are its singular
values, so this is the printed statement's factor and not a weaker surrogate.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open scoped InnerProductSpace

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The cosine-sandwich bound.**  Conjugating by a bounded map multiplies every
approximation number by at most `‖C‖²`.

This is the estimate Theorem 8.1(ii) needs on top of part (i), and it is exactly
the printed factor: the paper's `‖C₁‖₁²` is the squared *bound* norm. -/
theorem approximationNumber_adjoint_sandwich_le
    (M : F →L[ℂ] F) (C : E →L[ℂ] F) (n : ℕ) :
    (ContinuousLinearMap.adjoint C ∘L M ∘L C).approximationNumber n ≤
      ‖C‖ ^ 2 * M.approximationNumber n := by
  have hleft :
      (ContinuousLinearMap.adjoint C ∘L M ∘L C).approximationNumber n ≤
        ‖ContinuousLinearMap.adjoint C‖ * (M ∘L C).approximationNumber n :=
    ContinuousLinearMap.approximationNumber_comp_le_norm_mul
      (ContinuousLinearMap.adjoint C) (M ∘L C) n
  have hright : (M ∘L C).approximationNumber n ≤ M.approximationNumber n * ‖C‖ :=
    ContinuousLinearMap.approximationNumber_comp_le_mul_norm M C n
  have hadj : ‖ContinuousLinearMap.adjoint C‖ = ‖C‖ :=
    ContinuousLinearMap.adjoint.norm_map C
  calc (ContinuousLinearMap.adjoint C ∘L M ∘L C).approximationNumber n
      ≤ ‖ContinuousLinearMap.adjoint C‖ * (M ∘L C).approximationNumber n := hleft
    _ ≤ ‖ContinuousLinearMap.adjoint C‖ * (M.approximationNumber n * ‖C‖) := by
        gcongr
    _ = ‖C‖ ^ 2 * M.approximationNumber n := by rw [hadj]; ring

/-- The sandwich bound for a self-adjoint conjugator, the shape Theorem 8.1(ii)
instantiates: `C₁` there is a compression of an orthogonal projection. -/
theorem approximationNumber_sandwich_le_of_isSelfAdjoint
    {C : E →L[ℂ] E} (hC : IsSelfAdjoint C) (M : E →L[ℂ] E) (n : ℕ) :
    (C ∘L M ∘L C).approximationNumber n ≤ ‖C‖ ^ 2 * M.approximationNumber n := by
  have h := approximationNumber_adjoint_sandwich_le M C n
  rwa [ContinuousLinearMap.isSelfAdjoint_iff'.mp hC] at h

end Section8
end DavisKahan1970
end TauCeti
