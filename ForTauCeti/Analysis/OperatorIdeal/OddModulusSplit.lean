/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.OrthogonalAdditivity
public import ForTauCeti.Analysis.InnerProductSpace.ModulusConjugation
public import ForTauCeti.Analysis.OperatorIdeal.Family.UnitaryTransport

/-!
# Exact modulus splitting of a unitary-odd self-adjoint operator

If unitary conjugation negates a self-adjoint operator, its two modulus
splits have equal native Schatten cost and orthogonal supports. Their
positive powers add exactly. At exponent one either split has the full
nuclear cost of the original operator, including infinite values.
-/

public section

noncomputable section

namespace ContinuousLinearMap

open scoped ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Equal-cost orthogonal modulus splits for an operator negated by
unitary conjugation. No compactness or finite-cost assumption is needed. -/
theorem gauge_schatten_rpow_modulus_add_of_unitary_odd
    (p : ℝ) (hp : 1 ≤ p) (A : E →L[𝕜] E) (hA : IsSelfAdjoint A)
    (J : E ≃ₗᵢ[𝕜] E) (hodd : J.conjStarAlgEquiv A = -A) :
    (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge ((2 : 𝕜) • A) ^ p =
      2 * (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge (A.modulus + A) ^ p := by
  let Φ := TauCeti.OperatorIdealFamily.schatten 𝕜 p hp
  let S := A.modulus
  have hS : IsSelfAdjoint S := A.isSelfAdjoint_modulus
  have hSS : S * S = A * A := by
    change A.modulus ∘L A.modulus = A ∘L A
    rw [A.modulus_comp_modulus, hA.adjoint_eq]
  have hAS : Commute A S := by
    apply commute_modulus_of_commute
    rw [hA.adjoint_eq]
    exact (Commute.refl A).mul_right (Commute.refl A)
  have hzero : (S + A) * (S - A) = 0 := by
    calc
      _ = S * S - A * A := by noncomm_ring [hAS.eq]
      _ = 0 := by rw [hSS, sub_self]
  have hgram : J.conjStarAlgEquiv (A.adjoint ∘L A) = (-A).adjoint ∘L (-A) := by
    change J.conjStarAlgEquiv (star A * A) = star (-A) * (-A)
    rw [map_mul, map_star, hodd]
  have hSj : J.conjStarAlgEquiv S = S := by
    have h := conjStarAlgEquiv_modulus J hgram
    rw [modulus_neg] at h
    exact h
  have hconj (T : E →L[𝕜] E) : Φ.gauge (J.conjStarAlgEquiv T) = Φ.gauge T := by
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply,
      Φ.gauge_comp_linearIsometryEquiv_left, Φ.gauge_comp_linearIsometryEquiv_right]
  have hsame : Φ.gauge (S - A) = Φ.gauge (S + A) := by
    have h := hconj (S + A)
    rw [map_add, hSj, hodd, ← sub_eq_add_neg] at h
    exact h
  have hmod : Φ.gauge S = Φ.gauge A := by
    simp only [Φ, S, TauCeti.OperatorIdealFamily.gauge_schatten, singularValue_modulus]
  have hscaled : Φ.gauge ((2 : 𝕜) • S) = Φ.gauge ((2 : 𝕜) • A) := by
    rw [Φ.gauge_smul, Φ.gauge_smul, hmod]
  have hsum : (S + A) + (S - A) = (2 : 𝕜) • S := by
    rw [two_smul]
    abel
  have h := gauge_schatten_rpow_add_of_selfAdjoint_mul_eq_zero p hp
    (S + A) (S - A) (hS.add hA) (hS.sub hA) hzero
  rw [hsum, hscaled, hsame, ← two_mul] at h
  exact h

/-- The nuclear cost of either modulus split is exactly the nuclear
cost of a self-adjoint operator negated by unitary conjugation. -/
theorem gauge_nuclear_modulus_add_of_unitary_odd
    (A : E →L[𝕜] E) (hA : IsSelfAdjoint A)
    (J : E ≃ₗᵢ[𝕜] E) (hodd : J.conjStarAlgEquiv A = -A) :
    (TauCeti.OperatorIdealFamily.schatten 𝕜 1 (by norm_num)).gauge (A.modulus + A) =
      (TauCeti.OperatorIdealFamily.schatten 𝕜 1 (by norm_num)).gauge A := by
  have h := gauge_schatten_rpow_modulus_add_of_unitary_odd 1 (by norm_num) A hA J hodd
  rw [ENNReal.rpow_one, ENNReal.rpow_one, TauCeti.OperatorIdealFamily.gauge_smul,
    ← ofReal_norm, RCLike.norm_two, ENNReal.ofReal_ofNat] at h
  exact ((ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp h).symm

end ContinuousLinearMap
