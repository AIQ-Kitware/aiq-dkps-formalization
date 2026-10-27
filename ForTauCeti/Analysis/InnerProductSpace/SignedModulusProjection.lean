/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import TauCeti.Analysis.InnerProductSpace.Polar.Bounded
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The unique supported sign projection of a self-adjoint modulus root

A self-adjoint operator A of positive modulus S is exactly
`A = (2P - 1) S`, where P is an orthogonal projection commuting with S
and vanishing on its kernel. The support condition removes precisely
the irrelevant zero-angle freedom. No compactness is required.

## Provenance

Classical spectral sign geometry, implemented for the DKPS optimizer
classification using the accepted polar factor. New local proof code;
no historical priority or accepted roadmap ownership is asserted.
-/

public section

noncomputable section

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Every commuting orthogonal sign splitting gives a self-adjoint root
of the prescribed positive modulus. -/
theorem isSelfAdjoint_modulus_signed_projection
    (S P : E →L[𝕜] E) (hS : S.IsPositive) (hP : IsStarProjection P)
    (hcomm : Commute P S) :
    IsSelfAdjoint (((2 : 𝕜) • P - 1) * S) ∧
      (((2 : 𝕜) • P - 1) * S).modulus = S := by
  let U := (2 : 𝕜) • P - 1
  have hU : IsSelfAdjoint U := by
    change star ((2 : 𝕜) • P - 1) = (2 : 𝕜) • P - 1
    simp only [star_sub, star_smul, star_ofNat, hP.isSelfAdjoint.star_eq, star_one]
  have hUsq : U * U = 1 := by
    dsimp only [U]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, hP.isIdempotentElem.eq]
    module
  have hUS : Commute U S :=
    (hcomm.smul_left (2 : 𝕜)).sub_left (Commute.one_left S)
  have hself : IsSelfAdjoint (U * S) := by
    change star (U * S) = U * S
    rw [star_mul, hU.star_eq, hS.isSelfAdjoint.star_eq, hUS.eq]
  refine ⟨hself, ?_⟩
  apply Eq.symm
  apply ContinuousLinearMap.eq_modulus_iff.mpr
  refine ⟨hS, ?_⟩
  change S * S = star (U * S) * (U * S)
  rw [star_mul, hU.star_eq, hS.isSelfAdjoint.star_eq]
  calc
    _ = S * (U * U) * S := by rw [hUsq, mul_one]
    _ = _ := by simp only [mul_assoc]

/-- **Exact supported sign-projection classification.** Every self-adjoint
root of a positive modulus has one unique commuting orthogonal sign
projection. The projection vanishes on the entire modulus kernel. -/
theorem exists_unique_supported_sign_projection
    (S A : E →L[𝕜] E) (hS : S.IsPositive)
    (hA : IsSelfAdjoint A) (hmod : A.modulus = S) :
    ∃! P : E →L[𝕜] E, IsStarProjection P ∧ Commute P S ∧
      P * S.ker.starProjection = 0 ∧ A = ((2 : 𝕜) • P - 1) * S := by
  let H := A.polarFactor
  let Q := S.ker.starProjection
  let R := S.kerᗮ.starProjection
  have hker : A.ker = S.ker := by rw [← A.ker_modulus, hmod]
  have hH : IsSelfAdjoint H := by
    have h := A.polarFactor_adjoint
    change (star A).polarFactor = star H at h
    rw [hA.star_eq] at h
    exact h.symm
  have hR : IsSelfAdjoint R := isSelfAdjoint_starProjection S.kerᗮ
  have hQ : IsSelfAdjoint Q := isSelfAdjoint_starProjection S.ker
  have hRq : R = 1 - Q := Submodule.starProjection_orthogonal' S.ker
  have hHsq : H * H = R := by
    have h := A.adjoint_polarFactor_comp_polarFactor
    change star H * H = A.kerᗮ.starProjection at h
    simpa only [hH.star_eq, hker] using h
  have hHQ : H * Q = 0 := by
    ext x
    apply A.polarFactor_apply_of_mem_ker
    rw [hker]
    exact S.ker.starProjection_apply_mem x
  have hHR : H * R = H := by rw [hRq, mul_sub, mul_one, hHQ, sub_zero]
  have hRH : R * H = H := by
    have h := congrArg star hHR
    simpa only [star_mul, hH.star_eq, hR.star_eq] using h
  have hSQ : S * Q = 0 := by ext x; exact S.ker.starProjection_apply_mem x
  have hQS : Q * S = 0 := by
    have h := congrArg star hSQ
    simpa only [star_mul, hQ.star_eq, hS.isSelfAdjoint.star_eq, star_zero] using h
  have hRS : R * S = S := by rw [hRq, sub_mul, one_mul, hQS, sub_zero]
  have hSR : S * R = S := by rw [hRq, mul_sub, mul_one, hSQ, sub_zero]
  have hHS : H * S = A := by
    rw [← hmod]
    exact A.polarFactor_comp_modulus
  have hSH : S * H = A := by
    have h := congrArg star hHS
    simpa only [star_mul, hH.star_eq, hS.isSelfAdjoint.star_eq, hA.star_eq] using h
  let P := (1 / 2 : 𝕜) • (R + H)
  have hP : IsStarProjection P := by
    constructor
    · change P * P = P
      dsimp only [P]
      simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add,
        hRH, hHR, hHsq, show R * R = R from isStarProjection_starProjection.isIdempotentElem.eq]
      module
    · change star ((1 / 2 : 𝕜) • (R + H)) = (1 / 2 : 𝕜) • (R + H)
      simp only [star_smul, star_div₀, star_one, star_ofNat, star_add, hR.star_eq, hH.star_eq]
  have hPS : Commute P S := by
    change P * S = S * P
    dsimp only [P]
    simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hRS, hSR, hHS, hSH]
  have hRQ : R * Q = 0 := by
    rw [hRq, sub_mul, one_mul, isStarProjection_starProjection.isIdempotentElem.eq, sub_self]
  have hPQ : P * Q = 0 := by
    dsimp only [P]
    rw [smul_mul_assoc, add_mul, hRQ, hHQ, add_zero, smul_zero]
  have hform : A = ((2 : 𝕜) • P - 1) * S := by
    rw [sub_mul, smul_mul_assoc, one_mul]
    change A = (2 : 𝕜) • (((1 / 2 : 𝕜) • (R + H)) * S) - S
    rw [smul_mul_assoc, add_mul, hRS, hHS]
    module
  refine ⟨P, ⟨hP, hPS, hPQ, hform⟩, ?_⟩
  rintro P' ⟨_, _, hP'Q, hP'form⟩
  have hfactor : ((2 : 𝕜) • P' - R) * S = A := by
    rw [sub_mul, smul_mul_assoc, hRS]
    rw [hP'form, sub_mul, smul_mul_assoc, one_mul]
  have hzero : ∀ x ∈ A.ker, ((2 : 𝕜) • P' - R) x = 0 := by
    intro x hx
    have hxS : x ∈ S.ker := hker ▸ hx
    have hQx : Q x = x := Submodule.starProjection_eq_self_iff.mpr hxS
    have hP'x : P' x = 0 := by
      have h := congrArg (fun B : E →L[𝕜] E => B x) hP'Q
      change P' (Q x) = 0 at h
      rwa [hQx] at h
    have hRx : R x = 0 := by rw [hRq]; change x - Q x = 0; rw [hQx, sub_self]
    change (2 : 𝕜) • P' x - R x = 0
    rw [hP'x, hRx, smul_zero, sub_zero]
  have hphase : (2 : 𝕜) • P' - R = H := by
    apply ContinuousLinearMap.eq_polarFactor
    · change ((2 : 𝕜) • P' - R) * A.modulus = A
      rwa [hmod]
    · exact hzero
  dsimp only [P]
  rw [← hphase]
  module

end TauCeti
