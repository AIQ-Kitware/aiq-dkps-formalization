/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenFiniteRankAttainment

/-!
# Nuclear transport in arbitrary complex Hilbert dimension

At exponent one the ambient phase sum is twice the nuclear gauge of the
directed sine map `(I-P_L) P_K`. This bounds every ambient unitary
transport. A finite-rank feasible reference gives a finite-rank attainer
and the exact unrestricted minimum, even for infinite-rank subspaces.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The full ambient nuclear angle sum is twice the nuclear directed
sine gauge. Infinite values are included without a summability assumption. -/
theorem phaseMinimum_one_sum_eq_twice_nuclear_sine
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    (∑' j, ENNReal.ofReal (phaseMinimum 1
      (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ)))) =
        2 * (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge (K.sinThetaMap L) := by
  have hterm (j : ℕ) : ENNReal.ofReal (phaseMinimum 1
      (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) =
        2 * ((K.sinThetaMap L).singularValue j : ℝ≥0∞) := by
    have hs0 : 0 ≤ ((K.sinThetaMap L).singularValue j : ℝ) := NNReal.coe_nonneg _
    have hs1 : ((K.sinThetaMap L).singularValue j : ℝ) ≤ 1 := by
      calc
        _ ≤ ‖K.sinThetaMap L‖ := by
          exact_mod_cast (K.sinThetaMap L).singularValue_le_nnnorm j
        _ ≤ 1 := K.norm_sinThetaMap_le_one L
    rw [phaseMinimum_one _ (Real.arcsin_nonneg.mpr hs0) (Real.arcsin_le_pi_div_two _),
      Real.sin_arcsin (by linarith) hs1,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left, OperatorIdealFamily.gauge_schatten]
  simp only [ENNReal.rpow_one, one_div_one]

/-- Every complex unitary subspace transport has nuclear displacement
at least twice the nuclear directed sine gauge, in arbitrary dimension. -/
theorem twice_nuclear_sine_le_transport
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L) :
    2 * (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge (K.sinThetaMap L) ≤
      (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge (1 - (U : E →L[ℂ] E)) := by
  have h := sine_phaseMinimum_sum_le_schatten_transport (1 : ℝ≥0∞) ENNReal.one_ne_top
    (by norm_num) (by norm_num) K L U hmap
  simp only [ENNReal.toReal_one, ENNReal.rpow_one] at h
  rwa [phaseMinimum_one_sum_eq_twice_nuclear_sine] at h

/-- **Exact unrestricted nuclear transport minimum for a finite-rank
pair in Hilbert space.** The value is twice the nuclear directed sine
gauge and has a finite-rank ambient unitary attainer. -/
theorem exists_unitary_minimizing_nuclear_transport_of_finite_rank_reference
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (R : E ≃ₗᵢ[ℂ] E) (hRmap : K.map R.toLinearMap = L)
    (n : ℕ) (hR : (1 - R.toLinearMap).rank ≤ n) :
    ∃ U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L ∧
      (∃ m : ℕ, (1 - U.toLinearMap).rank ≤ m) ∧
      (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge (1 - (U : E →L[ℂ] E)) =
        2 * (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge (K.sinThetaMap L) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge (1 - (U : E →L[ℂ] E)) ≤
          (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge (1 - (T : E →L[ℂ] E)) := by
  obtain ⟨U, hmap, hrank, hcost, hmin⟩ :=
    exists_unitary_minimizing_schatten_transport_of_finite_rank_reference
      (1 : ℝ≥0∞) ENNReal.one_ne_top (by norm_num) (by norm_num) K L R hRmap n hR
  simp only [ENNReal.toReal_one, ENNReal.rpow_one] at hcost hmin
  rw [phaseMinimum_one_sum_eq_twice_nuclear_sine] at hcost
  exact ⟨U, hmap, hrank, hcost, hmin⟩

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
