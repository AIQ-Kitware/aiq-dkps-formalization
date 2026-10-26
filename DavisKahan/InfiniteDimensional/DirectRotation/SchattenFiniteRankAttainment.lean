/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenFiniteRank
public import ForTauCeti.Analysis.InnerProductSpace.Projection.ExtendTransport

/-!
# Attaining the exact Schatten value for finite-rank Hilbert-space pairs

Extend a finite-section phase optimizer by identity. Its actual accepted
Schatten power is the intrinsic ambient directed-sine penalty. Combined
with the unrestricted lower bound this closes the finite-rank pair case
in arbitrary complex Hilbert dimension.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- For every finite `p>=1`, independent principal phases on one finite
section attain the intrinsic ambient phase cost by a finite-rank unitary.
Global minimality is a separate statement requiring the corresponding
unrestricted lower bound. -/
theorem exists_finite_rank_transport_attaining_sine_phaseMinimum_sum
    (p : ℝ) (hp : 1 ≤ p)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (R : E ≃ₗᵢ[ℂ] E) (hRmap : K.map R.toLinearMap = L)
    (n : ℕ) (hR : (1 - R.toLinearMap).rank ≤ n) :
    ∃ U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L ∧
      (∃ m : ℕ, (1 - U.toLinearMap).rank ≤ m) ∧
      (OperatorIdealFamily.schatten ℂ p hp).gauge (1 - (U : E →L[ℂ] E)) ^ p =
        ∑' j, ENNReal.ofReal (phaseMinimum p
          (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) := by
  obtain ⟨M, hM, _, V, _, hlocal, hK, hL, heq, _⟩ :=
    K.exists_finite_transport_section L ⊥ R hRmap n hR
  let : FiniteDimensional ℂ M := hM
  let K₀ := K.comap M.subtype
  let L₀ := L.comap M.subtype
  have hdim : Module.finrank ℂ K₀ = Module.finrank ℂ L₀ := by
    have h := V.toLinearEquiv.finrank_map_eq K₀
    rw [hlocal] at h
    exact h.symm
  let q := ENNReal.ofReal p
  have hqreal : q.toReal = p := ENNReal.toReal_ofReal (by linarith)
  let : Fact (1 ≤ q) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  obtain ⟨W, hWmap, hWcost⟩ :=
    exists_unitary_attaining_schatten_principalAngles_complex q ENNReal.ofReal_ne_top K₀ L₀ hdim
  obtain ⟨U, hUmap, _, _, hdisp⟩ :=
    K.exists_transport_extension_by_identity L M hK hL heq W hWmap
  refine ⟨U, hUmap, ⟨Module.finrank ℂ M, ?_⟩, ?_⟩
  · have hlin : 1 - U.toLinearMap =
        ((M.subtypeL ∘L (1 - (W : M →L[ℂ] M))) ∘L M.orthogonalProjectionOnto).toLinearMap := by
      change (1 - (U : E →L[ℂ] E)).toLinearMap = _
      rw [hdisp, ContinuousLinearMap.comp_assoc]
    rw [hlin, ContinuousLinearMap.toLinearMap_comp]
    exact (LinearMap.rank_comp_le_left _ _).trans (by
      simpa only [Module.finrank_eq_rank] using
        LinearMap.rank_le_domain (M.subtypeL ∘L (1 - (W : M →L[ℂ] M))).toLinearMap)
  · have hfinite := OperatorIdealFamily.gauge_schatten_rpow_eq_ofReal_finite
      q ENNReal.ofReal_ne_top (1 - (W : M →L[ℂ] M))
    simp only [hqreal] at hfinite hWcost
    have hlinW : (1 - (W : M →L[ℂ] M)).toLinearMap = LinearMap.id - W.toLinearMap := by
      ext x
      rfl
    rw [hlinW] at hfinite
    rw [hdisp, OperatorIdealFamily.gauge_orthogonal_extension, hfinite, hWcost,
      Submodule.tsum_sine_penalty_eq_principalAngle_sum_of_finite_core K L M hK hL heq
        (fun t => ENNReal.ofReal (phaseMinimum p t))
        (by rw [phaseMinimum_zero_angle p hp, ENNReal.ofReal_zero])]
    apply ENNReal.ofReal_sum_of_nonneg
    intro i _
    exact phaseMinimum_nonneg _ _ hp
      ⟨K₀.principalAngles_nonneg L₀ i, K₀.principalAngles_le_pi_div_two L₀ i⟩

/-- **Exact unrestricted Schatten minimum for finite-rank pairs in
Hilbert space.** A finite-rank attainer achieves the ambient angle sum
and minimizes over all complex unitary competitors, of any displacement
rank or Schatten cost. The subspaces may have infinite rank and corank. -/
theorem exists_unitary_minimizing_schatten_transport_of_finite_rank_reference
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (R : E ≃ₗᵢ[ℂ] E) (hRmap : K.map R.toLinearMap = L)
    (n : ℕ) (hR : (1 - R.toLinearMap).rank ≤ n) :
    ∃ U : E ≃ₗᵢ[ℂ] E, K.map U.toLinearMap = L ∧
      (∃ m : ℕ, (1 - U.toLinearMap).rank ≤ m) ∧
      (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
          (1 - (U : E →L[ℂ] E)) ^ p.toReal =
        (∑' j, ENNReal.ofReal (phaseMinimum p.toReal
          (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ)))) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (U : E →L[ℂ] E)) ≤
          (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge (1 - (T : E →L[ℂ] E)) := by
  obtain ⟨U, hmap, hfinite, hcost⟩ :=
    exists_finite_rank_transport_attaining_sine_phaseMinimum_sum p.toReal hp1.le K L R hRmap n hR
  refine ⟨U, hmap, hfinite, hcost, fun T hT => ?_⟩
  apply (ENNReal.rpow_le_rpow_iff (zero_lt_one.trans hp1)).mp
  rw [hcost]
  exact sine_phaseMinimum_sum_le_schatten_transport_of_finite_rank_reference
    p hp hp1 hp2 K L R hRmap n hR T hT

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
