/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenNuclearEndpoint
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenCorrectionClassification

/-!
# Exact nuclear rounding to a subspace-preserving unitary

The nearest unitary preserving a prescribed subspace has nuclear distance
twice the sum of the sines between the image subspace and the prescribed
one. This is an attained minimum over all ambient unitary corrections.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ENNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Exact nuclear rounding of a complex unitary to the full subgroup
preserving a prescribed subspace. The correction is attained and the
distance is computed from the accepted image-to-source principal angles. -/
theorem exists_nearest_nuclear_subspace_preserving_unitary_complex
    (K : Submodule ℂ E) (A : E ≃ₗᵢ[ℂ] E) :
    let L := K.map A.toLinearMap
    ∃ V : E ≃ₗᵢ[ℂ] E, K.map V.toLinearMap = K ∧
      UnitarilyInvariantSeminorm.schatten ℂ E E 1 (A.toLinearMap - V.toLinearMap) =
        (∑ i : Fin (Module.finrank ℂ L), 2 * Real.sin (L.principalAngles K i)) ∧
      ∀ W : E ≃ₗᵢ[ℂ] E, K.map W.toLinearMap = K →
        UnitarilyInvariantSeminorm.schatten ℂ E E 1 (A.toLinearMap - V.toLinearMap) ≤
          UnitarilyInvariantSeminorm.schatten ℂ E E 1 (A.toLinearMap - W.toLinearMap) := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  let L := K.map A.toLinearMap
  obtain ⟨T, hT, hcost, hmin⟩ :=
    exists_unitary_minimizing_nuclear_transport_principalAngles_complex
      L K (A.toLinearEquiv.finrank_map_eq K)
  let V := A.trans T
  have hmapV : K.map V.toLinearMap = K := by
    change K.map (T.toLinearMap ∘ₗ A.toLinearMap) = K
    rw [Submodule.map_comp]
    exact hT
  have heq : A.symm.trans V = T := by ext x; simp [V]
  have hdist : UnitarilyInvariantSeminorm.schatten ℂ E E 1
      (A.toLinearMap - V.toLinearMap) =
        UnitarilyInvariantSeminorm.schatten ℂ E E 1 (LinearMap.id - T.toLinearMap) := by
    have hfac : A.toLinearMap - V.toLinearMap =
        (LinearMap.id - (A.symm.trans V).toLinearMap) ∘ₗ A.toLinearMap := by
      ext x
      change A x - V x = A x - V (A.symm (A x))
      rw [A.symm_apply_apply]
    rw [hfac]
    calc
      _ = UnitarilyInvariantSeminorm.schatten ℂ E E 1
          (LinearMap.id - (A.symm.trans V).toLinearMap) :=
            (UnitarilyInvariantSeminorm.schatten ℂ E E 1).map_comp_linearIsometryEquiv A _
      _ = _ := by rw [heq]
  refine ⟨V, hmapV, hdist.trans hcost, ?_⟩
  apply (schatten_correction_isMin_iff_transport_power_isMin_complex
    1 (by norm_num) K A V).mpr
  intro S hS
  simp only [ENNReal.toReal_one, Real.rpow_one]
  rw [heq, hcost]
  exact hmin S hS

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
