/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI GPT-5.6 Sol
-/
module

public import TauCeti.Analysis.InnerProductSpace.Polar.Bounded

/-!
# Additional identities for the canonical bounded polar factor

The factor, its support projections, norm preservation, kernel/range,
factorization, adjoint law and uniqueness come from TauCeti's bounded polar API.
This donor retains commutant preservation, negation and the skew-adjoint square
identities used by the source's direct-rotation construction.

The former range-extension construction is preserved in history at
`e4637c3919ae:ForTauCeti/Analysis/InnerProductSpace/Polar/PartialIsometry.lean`.
Original Kitware authorship and Apache-2.0 attribution are retained above.
-/

public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- An operator commuting with both `M` and its modulus commutes with its polar factor. -/
theorem commute_polarFactor_of_commute {A M : E →L[𝕜] E}
    (hAM : Commute A M) (hAmod : Commute A M.modulus) : Commute A M.polarFactor := by
  let V := A ∘L M.polarFactor - M.polarFactor ∘L A
  have hcomp : V ∘L M.modulus = 0 := by
    calc
      V ∘L M.modulus = A ∘L (M.polarFactor ∘L M.modulus) -
          M.polarFactor ∘L (A ∘L M.modulus) := by
        simp only [V, sub_comp, comp_assoc]
      _ = A ∘L M - M.polarFactor ∘L (M.modulus ∘L A) := by
        rw [M.polarFactor_comp_modulus, show A ∘L M.modulus = M.modulus ∘L A from hAmod.eq]
      _ = A ∘L M - M ∘L A := by rw [← comp_assoc, M.polarFactor_comp_modulus]
      _ = 0 := sub_eq_zero.mpr hAM.eq
  have hker : ∀ y ∈ M.modulus.rangeᗮ, V y = 0 := by
    intro y hy
    rw [M.orthogonal_range_modulus] at hy
    have hAy : A y ∈ M.ker := by
      change M (A y) = 0
      have h := congrArg (fun T : E →L[𝕜] E => T y) hAM.eq
      change A (M y) = M (A y) at h
      rw [show M y = 0 from hy, map_zero] at h
      exact h.symm
    simp only [V, sub_apply, comp_apply, M.polarFactor_apply_of_mem_ker hy,
      map_zero, M.polarFactor_apply_of_mem_ker hAy, sub_self]
  have hV := eq_factorThru (T := (0 : E →L[𝕜] E)) (A := M.modulus) hcomp hker
  have hzero := eq_factorThru (T := (0 : E →L[𝕜] E)) (A := M.modulus)
    (V := 0) (by simp) (by simp)
  exact sub_eq_zero.mp (hV.trans hzero.symm)

/-- Negating an operator negates its canonical polar factor. -/
@[simp]
theorem polarFactor_neg (M : E →L[𝕜] F) : (-M).polarFactor = -M.polarFactor := by
  symm
  apply (-M).eq_polarFactor
  · rw [modulus_neg]
    ext x
    simp only [comp_apply, neg_apply, M.polarFactor_modulus_apply]
  · intro x hx
    change -(M x) = 0 at hx
    change -(M.polarFactor x) = 0
    rw [M.polarFactor_apply_of_mem_ker (show x ∈ M.ker from neg_eq_zero.mp hx), neg_zero]

/-- The polar factor of a skew-adjoint operator is skew-adjoint. -/
theorem adjoint_polarFactor_eq_neg_of_adjoint_eq_neg {M : E →L[𝕜] E}
    (hM : M.adjoint = -M) : M.polarFactor.adjoint = -M.polarFactor := by
  rw [← M.polarFactor_adjoint, hM, polarFactor_neg]

/-- The polar factor of a skew-adjoint operator squares to minus its support projection. -/
theorem polarFactor_comp_self_eq_neg_starProjection_of_adjoint_eq_neg {M : E →L[𝕜] E}
    (hM : M.adjoint = -M) :
    M.polarFactor ∘L M.polarFactor = -M.kerᗮ.starProjection := by
  have h := M.adjoint_polarFactor_comp_polarFactor
  rw [adjoint_polarFactor_eq_neg_of_adjoint_eq_neg hM, neg_comp] at h
  exact neg_eq_iff_eq_neg.mp h

/-- On the support of a skew-adjoint operator, its polar factor squares to negation. -/
theorem polarFactor_apply_polarFactor_apply_of_mem_of_adjoint_eq_neg {M : E →L[𝕜] E}
    (hM : M.adjoint = -M) {x : E} (hx : x ∈ M.kerᗮ) :
    M.polarFactor (M.polarFactor x) = -x := by
  have h := congrArg (fun T : E →L[𝕜] E => T x)
    (polarFactor_comp_self_eq_neg_starProjection_of_adjoint_eq_neg hM)
  simpa only [comp_apply, neg_apply, Submodule.starProjection_eq_self_iff.mpr hx] using h

end ContinuousLinearMap
