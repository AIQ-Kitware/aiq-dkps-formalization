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

The classical projection-distance inequality gives the unrestricted nuclear
lower bound directly, including zero singular values. The existing
all-exponent phase construction attains its sine spectral sum. No
differentiability or limiting optimization theorem is needed for the bound.
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
  simpa only [Finset.mul_sum, UnitarilyInvariantSeminorm.schatten_one] using
    ComplexTraceOptimality.two_mul_sum_sin_principalAngles_le_nuclear_transport K L hKL T hmap

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
