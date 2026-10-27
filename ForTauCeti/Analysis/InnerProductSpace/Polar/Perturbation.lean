/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Modulus
public import TauCeti.Analysis.InnerProductSpace.Sylvester
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# A dimension-free perturbation bound for unitary polar factors

The classical polar-factor perturbation argument is a Sylvester bound
for the relative unitary. Actual factorizations and quadratic-form
lower bounds suffice, in either scalar field and arbitrary Hilbert
dimension. No finite-dimensional singular-value decomposition is used.

The matrix estimate is classical; see R.-C. Li, *New perturbation bounds
for the unitary polar factor*, SIAM J. Matrix Anal. Appl. 16 (1995),
327--332. This module supplies the Hilbert-space API used downstream.
-/

public section

noncomputable section

namespace ContinuousLinearMap

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The positive factor in an actual unitary factorization is the
accepted operator modulus, in arbitrary Hilbert dimension. -/
theorem IsPositive.eq_modulus_of_unitary_factorization
    {T H : E →L[𝕜] E} (hH : H.IsPositive) (U : E ≃ₗᵢ[𝕜] E)
    (hT : T = (U : E →L[𝕜] E) * H) : H = T.modulus := by
  apply eq_modulus_iff.mpr
  refine ⟨hH, ?_⟩
  rw [hT]
  change H ∘L H = ((U : E →L[𝕜] E) ∘L H).adjoint ∘L ((U : E →L[𝕜] E) ∘L H)
  rw [adjoint_comp, U.adjoint_eq_symm, hH.isSelfAdjoint.adjoint_eq]
  apply ContinuousLinearMap.ext
  intro x
  change H (H x) = H (U.symm (U (H x)))
  rw [U.symm_apply_apply]

/-- Positive coercivity identifies the actual unitary factor with
Tau Ceti's canonical factor through the modulus. No new polar-factor
definition, finite-dimensional assumption or inverse is needed. -/
theorem eq_factorThru_modulus_of_unitary_factorization_of_coercive
    (T H : E →L[𝕜] E) (U : E ≃ₗᵢ[𝕜] E) (hT : T = (U : E →L[𝕜] E) * H)
    (hH : H.IsPositive) (a : ℝ) (ha : 0 < a)
    (hcoerc : ∀ x, a * ‖x‖ ^ 2 ≤ RCLike.re ⟪H x, x⟫_𝕜) :
    (U : E →L[𝕜] E) = T.factorThru T.modulus := by
  have hmod := hH.eq_modulus_of_unitary_factorization U hT
  apply eq_factorThru_of_isStarNormal
    (fun x => (T.norm_modulus_apply x).symm) T.isPositive_modulus.isSelfAdjoint.isStarNormal
  · rw [← hmod]
    exact hT.symm
  · intro x hx
    have hTx : T x = 0 := hx
    have hHx : H x = 0 := by
      apply U.injective
      change ((U : E →L[𝕜] E) * H) x = U 0
      rw [← hT, hTx, map_zero]
    have h := hcoerc x
    rw [hHx, inner_zero_left, map_zero] at h
    have hsq : ‖x‖ ^ 2 ≤ 0 := by nlinarith
    have hnorm : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
    rw [norm_eq_zero.mp hnorm, map_zero]

/-- Classical polar perturbation bound from the actual positive factors.
The lower bounds may be unequal. No compactness or dimension hypothesis
is imposed, and positive factors may have infinite rank. -/
theorem add_mul_norm_sub_unitary_le_two_mul_norm_sub
    (X Y H K : E →L[𝕜] E) (U V : E ≃ₗᵢ[𝕜] E)
    (hX : X = (U : E →L[𝕜] E) * H) (hY : Y = (V : E →L[𝕜] E) * K)
    (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) (a b : ℝ)
    (ha : ∀ x, a * ‖x‖ ^ 2 ≤ RCLike.re ⟪H x, x⟫_𝕜)
    (hb : ∀ x, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪K x, x⟫_𝕜) :
    (a + b) * ‖(U : E →L[𝕜] E) - (V : E →L[𝕜] E)‖ ≤ 2 * ‖X - Y‖ := by
  let Q := V.trans U.symm
  let F := (U.symm : E →L[𝕜] E) * (X - Y)
  have hQ : (Q : E →L[𝕜] E) = (U.symm : E →L[𝕜] E) * (V : E →L[𝕜] E) := rfl
  have hUU : (U.symm : E →L[𝕜] E) * (U : E →L[𝕜] E) = 1 := by
    ext x
    exact U.symm_apply_apply x
  have hQQ : star (Q : E →L[𝕜] E) * (Q : E →L[𝕜] E) = 1 := by
    rw [show star (Q : E →L[𝕜] E) = (Q.symm : E →L[𝕜] E) from Q.adjoint_eq_symm]
    ext x
    exact Q.symm_apply_apply x
  have hF : F = H - (Q : E →L[𝕜] E) * K := by
    dsimp only [F]
    rw [hX, hY, mul_sub, ← mul_assoc, hUU, one_mul, hQ, mul_assoc]
  have hres : H * (1 - (Q : E →L[𝕜] E)) + (1 - (Q : E →L[𝕜] E)) * K =
      F - star F * (Q : E →L[𝕜] E) := by
    rw [hF, star_sub, star_mul, hH.star_eq, hK.star_eq]
    simp only [sub_mul, mul_sub, mul_one, one_mul, mul_assoc, hQQ]
    noncomm_ring
  have hnorm : ‖1 - (Q : E →L[𝕜] E)‖ = ‖(U : E →L[𝕜] E) - (V : E →L[𝕜] E)‖ := by
    have hprod : (U : E →L[𝕜] E) * (1 - (Q : E →L[𝕜] E)) =
        (U : E →L[𝕜] E) - (V : E →L[𝕜] E) := by
      apply ContinuousLinearMap.ext
      intro x
      change U (x - U.symm (V x)) = U x - V x
      rw [map_sub, U.apply_symm_apply]
    rw [← hprod, opNorm_linearIsometryEquiv_mul]
  have hbound := add_mul_norm_le_norm_comp_add_comp ha hb (1 - (Q : E →L[𝕜] E))
  change (a + b) * ‖1 - (Q : E →L[𝕜] E)‖ ≤
    ‖H * (1 - (Q : E →L[𝕜] E)) + (1 - (Q : E →L[𝕜] E)) * K‖ at hbound
  rw [hnorm, hres] at hbound
  calc
    _ ≤ ‖F - star F * (Q : E →L[𝕜] E)‖ := hbound
    _ ≤ ‖F‖ + ‖star F * (Q : E →L[𝕜] E)‖ := norm_sub_le _ _
    _ = 2 * ‖X - Y‖ := by
      rw [opNorm_mul_linearIsometryEquiv, norm_star]
      dsimp only [F]
      rw [opNorm_linearIsometryEquiv_mul]
      ring

end ContinuousLinearMap
