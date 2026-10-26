/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenGlobalAttainment
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenOptimalPhase
public import ForTauCeti.Analysis.InnerProductSpace.SchattenExponentContinuity

/-!
# The unrestricted complex nuclear transport endpoint

Positive-exponent continuity passes the unrestricted Schatten lower
bound to exponent one, including zero singular values. The existing
all-exponent phase construction attains its sine spectral sum. No
differentiability of the nuclear norm is used.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set Filter
open scoped ENNReal Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Every ambient complex unitary transport dominates the nuclear sine
sum, including zero, repeated and right principal angles. -/
theorem sum_sine_le_nuclear_transport_complex
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L)
    (T : E ≃ₗᵢ[ℂ] E) (hmap : K.map T.toLinearMap = L) :
    (∑ i : Fin (Module.finrank ℂ K), 2 * Real.sin (K.principalAngles L i)) ≤
      UnitarilyInvariantSeminorm.schatten ℂ E E 1 (LinearMap.id - T.toLinearMap) := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  let A : E →L[ℂ] E := 1 - (T : E →L[ℂ] E)
  have hf : ContinuousOn
      (fun q => ∑ i : Fin (Module.finrank ℂ K), phaseMinimum q (K.principalAngles L i))
      (Ioi 0) := by
    apply continuousOn_finsetSum
    intro i _
    exact continuousOn_phaseMinimum_exponent _
  have hg : ContinuousOn (fun q => singularValuePowerSum q A) (Ioi 0) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous_singularValuePowerSum_positive.comp (continuous_id.prodMk continuous_const)
  have hevent : ∀ᶠ q in 𝓝[>] (1 : ℝ),
      (∑ i : Fin (Module.finrank ℂ K), phaseMinimum q (K.principalAngles L i)) ≤
        singularValuePowerSum q A := by
    filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with q hq
    let p := ENNReal.ofReal q
    have hp : p.toReal = q := ENNReal.toReal_ofReal (by linarith [hq.1])
    have : Fact (1 ≤ p) := ⟨ENNReal.one_le_ofReal.mpr hq.1.le⟩
    obtain ⟨_, _, _, hbound⟩ := exists_unitary_minimizing_schatten_transport_principalAngles_complex
      p ENNReal.ofReal_ne_top (by rw [hp]; exact hq.1) (by rw [hp]; exact hq.2) K L hKL
    have h := hbound T hmap
    change (∑ i : Fin (Module.finrank ℂ K), phaseMinimum p.toReal (K.principalAngles L i)) ≤
      UnitarilyInvariantSeminorm.schatten ℂ E E p A.toLinearMap ^ p.toReal at h
    rw [← singularValuePowerSum_eq_schatten_rpow p ENNReal.ofReal_ne_top, hp] at h
    exact h
  have hf1 := (hf 1 (by norm_num)).continuousAt
    (isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi 0 by norm_num))
  have hg1 := (hg 1 (by norm_num)).continuousAt
    (isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi 0 by norm_num))
  have hle := le_of_tendsto_of_tendsto
    (hf1.tendsto.mono_left nhdsWithin_le_nhds)
    (hg1.tendsto.mono_left nhdsWithin_le_nhds) hevent
  simp_rw [phaseMinimum_one _ (K.principalAngles_nonneg L _)
    (K.principalAngles_le_pi_div_two L _)] at hle
  have hvalue := singularValuePowerSum_eq_schatten_rpow (1 : ℝ≥0∞)
    ENNReal.one_ne_top A
  simp only [ENNReal.toReal_one, Real.rpow_one] at hvalue
  exact hle.trans_eq hvalue

/-- The exact unrestricted complex nuclear minimum is twice the sum of
the principal-angle sines, with an actual ambient unitary attainer and
comparison against every complex unitary transporter. -/
theorem exists_unitary_minimizing_nuclear_transport_principalAngles_complex
    (K L : Submodule ℂ E) (hKL : Module.finrank ℂ K = Module.finrank ℂ L) :
    ∃ W : E ≃ₗᵢ[ℂ] E, K.map W.toLinearMap = L ∧
      UnitarilyInvariantSeminorm.schatten ℂ E E 1 (LinearMap.id - W.toLinearMap) =
        (∑ i : Fin (Module.finrank ℂ K), 2 * Real.sin (K.principalAngles L i)) ∧
      ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
        (∑ i : Fin (Module.finrank ℂ K), 2 * Real.sin (K.principalAngles L i)) ≤
          UnitarilyInvariantSeminorm.schatten ℂ E E 1 (LinearMap.id - T.toLinearMap) := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨W, hmap, hcost⟩ := exists_unitary_attaining_schatten_principalAngles_complex
    1 ENNReal.one_ne_top K L hKL
  simp only [ENNReal.toReal_one, Real.rpow_one] at hcost
  simp_rw [phaseMinimum_one _ (K.principalAngles_nonneg L _)
    (K.principalAngles_le_pi_div_two L _)] at hcost
  exact ⟨W, hmap, hcost, fun T hT => sum_sine_le_nuclear_transport_complex K L hKL T hT⟩

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
