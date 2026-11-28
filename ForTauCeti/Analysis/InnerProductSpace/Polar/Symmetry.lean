/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Polar.PartialIsometry

/-!
# Symmetries and skew-adjoint completion of the accepted polar factor

For a skew-adjoint endomorphism it is skew-adjoint and becomes an
actual unitary on adjoining identity on the original kernel. The
construction uses the accepted factor-through-modulus representation.
-/

public section

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- A skew-adjoint polar phase, completed by identity on its kernel,
is an actual unitary in arbitrary Hilbert dimension over either field. -/
theorem polarFactor_add_ker_starProjection_mem_unitary_of_adjoint_eq_neg
    (A : E →L[𝕜] E) (hA : A.adjoint = -A) :
    A.polarFactor + A.ker.starProjection ∈ unitary (E →L[𝕜] E) := by
  let F := A.polarFactor
  let Q := A.ker.starProjection
  let P := A.kerᗮ.starProjection
  have hF : star F = -F := adjoint_polarFactor_eq_neg_of_adjoint_eq_neg hA
  have hQ : IsStarProjection Q := isStarProjection_starProjection
  have hFQ : F * Q = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    exact A.polarFactor_apply_of_mem_ker (A.ker.starProjection_apply_mem x)
  have hQF : Q * F = 0 := by
    have h := congrArg star hFQ
    rw [star_mul, hF, hQ.isSelfAdjoint.star_eq, mul_neg, star_zero] at h
    exact neg_eq_zero.mp h
  have hFF : F * F = -P := by
    have h := A.star_polarFactor_mul_polarFactor
    change star F * F = P at h
    rw [hF, neg_mul] at h
    exact neg_eq_iff_eq_neg.mp h
  have hPQ : P + Q = 1 := by
    dsimp only [P, Q]
    rw [Submodule.starProjection_orthogonal', sub_add_cancel]
  have hstar : star (F + Q) = -F + Q := by rw [star_add, hF, hQ.isSelfAdjoint.star_eq]
  change F + Q ∈ unitary (E →L[𝕜] E)
  apply Unitary.mem_iff.mpr
  constructor <;> rw [hstar]
  · simp only [add_mul, mul_add, neg_mul, hFF, hFQ, hQF,
      hQ.isIdempotentElem.eq, neg_zero, neg_neg, zero_add, add_zero]
    exact hPQ
  · simp only [add_mul, mul_add, mul_neg, hFF, hFQ, hQF,
      hQ.isIdempotentElem.eq, neg_neg, zero_add, add_zero]
    exact hPQ

end ContinuousLinearMap
