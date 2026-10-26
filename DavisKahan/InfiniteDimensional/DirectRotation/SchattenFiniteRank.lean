/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenGlobalAttainment
public import ForTauCeti.Analysis.InnerProductSpace.Projection.FiniteTransport
public import ForTauCeti.Analysis.InnerProductSpace.SchattenTransportDensity

/-!
# Exact Schatten transport lower bounds for finite-rank pairs in Hilbert space

The spectral angle cost is intrinsic to the ambient directed sine map.
First restrict a finite-rank competitor to its finite reducing support.
Then exact-fiber Schatten density extends the same lower bound to every
ambient unitary, given one feasible finite-rank reference transporter.
The ambient complex Hilbert space may be infinite and nonseparable.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The intrinsic ambient angle cost is a lower bound for every
finite-rank complex unitary transporter, without a prescribed block form. -/
theorem sine_phaseMinimum_sum_le_schatten_finite_rank_transport
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (n : ℕ) (hU : (1 - U.toLinearMap).rank ≤ n) :
    (∑' j, ENNReal.ofReal (phaseMinimum p.toReal
      (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ)))) ≤
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
          (1 - (U : E →L[ℂ] E)) ^ p.toReal := by
  obtain ⟨M, hM, _, V, _, hlocal, hK, hL, heq, hdisp⟩ :=
    K.exists_finite_transport_section L ⊥ U hmap n hU
  let : FiniteDimensional ℂ M := hM
  let K₀ := K.comap M.subtype
  let L₀ := L.comap M.subtype
  rw [Submodule.tsum_sine_penalty_eq_principalAngle_sum_of_finite_core K L M hK hL heq
    (fun t => ENNReal.ofReal (phaseMinimum p.toReal t))
    (by rw [phaseMinimum_zero_angle p.toReal hp1.le, ENNReal.ofReal_zero]),
    hdisp, OperatorIdealFamily.gauge_orthogonal_extension,
    OperatorIdealFamily.gauge_schatten_rpow_eq_ofReal_finite p hp]
  have hnonneg (i : Fin (Module.finrank ℂ K₀)) :
      0 ≤ phaseMinimum p.toReal (K₀.principalAngles L₀ i) :=
    phaseMinimum_nonneg _ _ hp1.le
      ⟨K₀.principalAngles_nonneg L₀ i, K₀.principalAngles_le_pi_div_two L₀ i⟩
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hnonneg i)]
  apply ENNReal.ofReal_le_ofReal
  have h := sum_phaseMinimum_le_schatten_transport_complex p hp hp1 hp2 K₀ L₀
    (Unitary.linearIsometryEquiv.symm V)
    (by simpa only [MulEquiv.apply_symm_apply] using hlocal)
  exact h

/-- **Unrestricted Hilbert-space lower bound for a finite-rank pair.**
If one finite-rank perturbation of identity transports `K` to `L`, the
intrinsic angle cost bounds every ambient complex unitary competitor,
including competitors with infinite Schatten cost. -/
theorem sine_phaseMinimum_sum_le_schatten_transport_of_finite_rank_reference
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (R : E ≃ₗᵢ[ℂ] E) (hRmap : K.map R.toLinearMap = L)
    (n : ℕ) (hR : (1 - R.toLinearMap).rank ≤ n)
    (U : E ≃ₗᵢ[ℂ] E) (hUmap : K.map U.toLinearMap = L) :
    (∑' j, ENNReal.ofReal (phaseMinimum p.toReal
      (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ)))) ≤
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
          (1 - (U : E →L[ℂ] E)) ^ p.toReal := by
  let Φ := OperatorIdealFamily.schatten ℂ p.toReal hp1.le
  let C := ∑' j, ENNReal.ofReal (phaseMinimum p.toReal
    (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ)))
  have hp0 : 0 < p.toReal := zero_lt_one.trans hp1
  have hroot : C ^ (1 / p.toReal) ≤ Φ.gauge ((U : E →L[ℂ] E) - 1) := by
    apply (schatten_transport_lower_bound_iff_finite_rank p.toReal hp1.le
      K.starProjection L.starProjection R n hR
      ((K.map_eq_iff_conjugate_starProjection L R).mp hRmap) _).mpr ?_ U
        ((K.map_eq_iff_conjugate_starProjection L U).mp hUmap)
    intro V hVP ⟨m, hm⟩
    apply (ENNReal.rpow_le_rpow_iff hp0).mp
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one,
      ← neg_sub 1 (V : E →L[ℂ] E), Φ.gauge_neg]
    exact sine_phaseMinimum_sum_le_schatten_finite_rank_transport p hp hp1 hp2 K L V
      ((K.map_eq_iff_conjugate_starProjection L V).mpr hVP) m hm
  have hpow := ENNReal.rpow_le_rpow hroot hp0.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one,
    ← neg_sub 1 (U : E →L[ℂ] E), Φ.gauge_neg] at hpow
  exact hpow

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
