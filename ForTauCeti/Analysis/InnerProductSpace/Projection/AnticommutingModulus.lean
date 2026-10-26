/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import TauCeti.Analysis.InnerProductSpace.Reflection
public import TauCeti.Analysis.InnerProductSpace.Modulus

/-!
# Reflection-odd self-adjoint operators have projection-even modulus

Conjugation by a source reflection reverses an odd self-adjoint operator,
so its square and modulus commute with the source projection. This is
the algebraic input for finite reducing spectral sectors in constrained
transport stationarity. Both scalar fields and arbitrary dimension apply.
-/

public section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- A self-adjoint operator reversed by the source reflection has
modulus commuting with the source projection. -/
theorem commute_starProjection_modulus_of_reflection_conjugate_eq_neg
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (G : E →L[𝕜] E) (hG : IsSelfAdjoint G)
    (hodd : ((2 : 𝕜) • K.starProjection - 1) * G *
      ((2 : 𝕜) • K.starProjection - 1) = -G) :
    Commute K.starProjection G.modulus := by
  let J := (2 : 𝕜) • K.starProjection - 1
  have hJJ : J * J = 1 := by
    have hJ : J = (K.reflection : E →L[𝕜] E) := by
      simpa only [J, two_smul] using (Submodule.coe_reflection K).symm
    rw [hJ]
    ext x
    exact K.reflection_reflection x
  have hJG : J * G = -(G * J) := by
    calc
      _ = (J * G) * (J * J) := by rw [hJJ, mul_one]
      _ = (J * G * J) * J := (mul_assoc _ _ _).symm
      _ = -G * J := by rw [show J * G * J = -G from hodd]
      _ = _ := neg_mul _ _
  have hJsq : Commute J (G * G) := by
    rw [commute_iff_eq]
    calc
      _ = (J * G) * G := (mul_assoc _ _ _).symm
      _ = -(G * J) * G := by rw [hJG]
      _ = -(G * (J * G)) := by rw [neg_mul, mul_assoc]
      _ = -(G * (-(G * J))) := by rw [hJG]
      _ = G * (G * J) := by rw [mul_neg, neg_neg]
      _ = _ := (mul_assoc _ _ _).symm
  have hPsq : Commute K.starProjection (G * G) := by
    rw [commute_iff_eq]
    have h := hJsq.eq
    dsimp only [J] at h
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] at h
    have hhalf := congrArg (fun A : E →L[𝕜] E => ((2 : 𝕜)⁻¹) • A) (sub_left_inj.mp h)
    simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : 𝕜) ≠ 0), one_smul] using hhalf
  apply ContinuousLinearMap.commute_modulus_of_commute
  change Commute K.starProjection (star G * G)
  rw [hG.star_eq]
  exact hPsq

end Submodule
