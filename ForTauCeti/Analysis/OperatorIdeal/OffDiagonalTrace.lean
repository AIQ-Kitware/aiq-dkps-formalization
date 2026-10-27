/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.OrthogonalAdditivity
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Adjoint
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Modulus

/-!
# Exact native Schatten cost of self-adjoint off-diagonal operators

For a self-adjoint operator interchanging the two sectors of an
orthogonal projection, either off-diagonal block has half the total
Schatten power. The modulus has two orthogonal reducing blocks, whose
costs agree by adjoint invariance. All costs may be infinite, and no
compactness, separability or finite-dimensionality is assumed.
-/

public section

noncomputable section

namespace ContinuousLinearMap

open scoped ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- A self-adjoint off-diagonal operator has twice the native Schatten
power of either block. Modulus splitting proves exact additivity even
when the ambient operator is noncompact or the cost is infinite. -/
theorem gauge_schatten_rpow_eq_twice_of_selfAdjoint_offDiagonal
    (p : ℝ) (hp : 1 ≤ p) (A P : E →L[𝕜] E)
    (hA : IsSelfAdjoint A) (hP : IsStarProjection P)
    (hAP : A * P = (1 - P) * A) :
    (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge A ^ p =
      2 * (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge (A * P) ^ p := by
  let Φ := TauCeti.OperatorIdealFamily.schatten 𝕜 p hp
  let S := A.modulus
  have hPA : P * A = A * (1 - P) := by
    have h := congrArg star hAP
    simpa only [star_mul, hP.isSelfAdjoint.star_eq, hA.star_eq, star_sub, star_one] using h
  have hPS : Commute P S := by
    apply commute_modulus_of_commute
    change Commute P (star A * A)
    rw [hA.star_eq, commute_iff_eq]
    calc
      _ = (P * A) * A := (mul_assoc _ _ _).symm
      _ = (A * (1 - P)) * A := by rw [hPA]
      _ = A * ((1 - P) * A) := mul_assoc _ _ _
      _ = A * (A * P) := by rw [← hAP]
      _ = _ := (mul_assoc _ _ _).symm
  have hPQ : P * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hP.isIdempotentElem.eq, sub_self]
  have hS : IsSelfAdjoint S := A.isSelfAdjoint_modulus
  have hSP : IsSelfAdjoint (S * P) := by
    change star (S * P) = S * P
    rw [star_mul, hS.star_eq, hP.isSelfAdjoint.star_eq, hPS.eq]
  have hSQ : IsSelfAdjoint (S * (1 - P)) := by
    change star (S * (1 - P)) = S * (1 - P)
    rw [star_mul, star_sub, star_one, hP.isSelfAdjoint.star_eq, hS.star_eq]
    exact ((Commute.one_left S).sub_left hPS).eq
  have hzero : (S * P) * (S * (1 - P)) = 0 := by
    calc
      _ = S * (P * S) * (1 - P) := by simp only [mul_assoc]
      _ = S * (S * P) * (1 - P) := by rw [hPS.eq]
      _ = (S * S) * (P * (1 - P)) := by simp only [mul_assoc]
      _ = 0 := by rw [hPQ, mul_zero]
  have hgauge (B : E →L[𝕜] E) : Φ.gauge (S * B) = Φ.gauge (A * B) := by
    have hσ : (S * B).singularValue = (A * B).singularValue := by
      funext j
      exact singularValue_eq_of_forall_norm_apply_eq (fun x => A.norm_modulus_apply (B x)) j
    simp only [Φ, TauCeti.OperatorIdealFamily.gauge_schatten, hσ]
  have hsame : Φ.gauge (A * (1 - P)) = Φ.gauge (A * P) := by
    have hσ : (A * (1 - P)).singularValue = (A * P).singularValue := by
      funext j
      have h := singularValue_adjoint (A * P) j
      change (star (A * P)).singularValue j = _ at h
      rwa [star_mul, hP.isSelfAdjoint.star_eq, hA.star_eq, hPA] at h
    simp only [Φ, TauCeti.OperatorIdealFamily.gauge_schatten, hσ]
  have hsum : S * P + S * (1 - P) = S := by rw [← mul_add]; simp
  have h := gauge_schatten_rpow_add_of_selfAdjoint_mul_eq_zero p hp
    (S * P) (S * (1 - P)) hSP hSQ hzero
  rw [hsum, hgauge P, hgauge (1 - P), hsame, ← two_mul] at h
  simpa only [Φ, S, TauCeti.OperatorIdealFamily.gauge_schatten, singularValue_modulus] using h

end ContinuousLinearMap
