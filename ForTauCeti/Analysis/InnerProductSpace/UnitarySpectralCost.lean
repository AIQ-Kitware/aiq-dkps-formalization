/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockSchatten
public import ForTauCeti.Analysis.InnerProductSpace.SchattenTransportRestriction

/-!
# Literal finite spectral displacement costs

On a finite normal operator, the CFC trace of a radial displacement symbol
is exactly the corresponding sum over the displacement singular values.
Unitary coordinates preserve this sum and orthogonal unitary blocks add.
No regularity or convexity of the penalty is needed in finite dimension.

These are classical spectral-theorem ingredients, generalized from the
existing `SchattenSpectralCalculus` and `SmoothedBlockCost` calculations.
They connect actual spectral costs to the already generic feasible paired
variation theorem; they do not assert optimization or historical novelty.
-/

public section

noncomputable section

namespace TauCeti

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]

/-- The literal finite CFC spectral trace of a radial displacement penalty. -/
@[expose] def normalDisplacementSpectralCost (rho : ℝ → ℝ) (U : E →L[ℂ] E) : ℝ :=
  (LinearMap.trace ℂ E (cfc (fun z => (rho ‖z - 1‖ : ℂ)) U).toLinearMap).re

/-- The normal spectral trace is exactly the displacement singular-value
sum, including all zero singular values and zero-dimensional spaces. -/
theorem normalDisplacementSpectralCost_eq_sum_singularValues
    (rho : ℝ → ℝ) (U : E →L[ℂ] E) [IsStarNormal U] :
    normalDisplacementSpectralCost rho U =
      ∑ i : Fin (Module.finrank ℂ E), rho ((LinearMap.id - U.toLinearMap).singularValues i) := by
  let := ContinuousLinearMap.isStarNormal_toLinearMap U
  obtain ⟨b, mu, hmu⟩ :=
    LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal U.toLinearMap
      (ι := Fin (Module.finrank ℂ E)) (by simp)
  have hA (i : Fin (Module.finrank ℂ E)) :
      ((LinearMap.id : E →ₗ[ℂ] E) - U.toLinearMap) (b i) = (1 - mu i) • b i := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply, hmu, sub_smul, one_smul]
  rw [normalDisplacementSpectralCost,
    ContinuousLinearMap.re_trace_cfc_eq_sum (fun z => rho ‖z - 1‖) U b mu hmu,
    sum_singularValues_eq_sum_norm_eigenvalues b _ _ hA rho]
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_sub_rev]

/-- Unitary changes of coordinates preserve arbitrary finite displacement
spectral costs. This is a classical spectral invariance statement. -/
theorem normalDisplacementSpectralCost_conj
    (rho : ℝ → ℝ) (e : E ≃ₗᵢ[ℂ] F) (U : unitary (E →L[ℂ] E)) :
    normalDisplacementSpectralCost rho (e.conjStarAlgEquiv (U : E →L[ℂ] E)) =
      normalDisplacementSpectralCost rho (U : E →L[ℂ] E) := by
  let V := e.symm.trans ((Unitary.linearIsometryEquiv U).trans e)
  have hV : (V : F →L[ℂ] F) = e.conjStarAlgEquiv (U : E →L[ℂ] E) := by ext x; rfl
  let : IsStarNormal (V : F →L[ℂ] F) :=
    isStarNormal_of_mem_unitary (Unitary.linearIsometryEquiv.symm V).property
  let := isStarNormal_of_mem_unitary U.property
  have hconj : LinearMap.id - (e.conjStarAlgEquiv (U : E →L[ℂ] E)).toLinearMap =
      (e : E →ₗ[ℂ] F) ∘ₗ (LinearMap.id - (U : E →L[ℂ] E).toLinearMap) ∘ₗ
        (e.symm : F →ₗ[ℂ] E) := by
    ext x
    change x - e ((U : E →L[ℂ] E) (e.symm x)) =
      e (e.symm x - (U : E →L[ℂ] E) (e.symm x))
    rw [map_sub, e.apply_symm_apply]
  rw [← hV, normalDisplacementSpectralCost_eq_sum_singularValues,
    normalDisplacementSpectralCost_eq_sum_singularValues, hV, hconj,
    LinearMap.singularValues_linearIsometryEquiv_comp,
    LinearMap.singularValues_comp_linearIsometryEquiv, ← e.toLinearEquiv.finrank_eq]

/-- Orthogonal unitary blocks contribute additively to every finite
spectral displacement cost. The penalty need not vanish at zero. -/
theorem normalDisplacementSpectralCost_withLpProdMap
    (rho : ℝ → ℝ) (U : unitary (E →L[ℂ] E)) (V : unitary (F →L[ℂ] F)) :
    normalDisplacementSpectralCost rho
      ((U : E →L[ℂ] E).withLpProdMap 2 (V : F →L[ℂ] F)) =
        normalDisplacementSpectralCost rho (U : E →L[ℂ] E) +
          normalDisplacementSpectralCost rho (V : F →L[ℂ] F) := by
  let := isStarNormal_of_mem_unitary U.property
  let := isStarNormal_of_mem_unitary V.property
  let := isStarNormal_of_mem_unitary
    (ContinuousLinearMap.withLpProdMap_mem_unitary U.property V.property)
  have hblock : LinearMap.id -
      ((U : E →L[ℂ] E).withLpProdMap 2 (V : F →L[ℂ] F)).toLinearMap =
      ((LinearMap.id - (U : E →L[ℂ] E).toLinearMap).prodMap
        (LinearMap.id - (V : F →L[ℂ] F).toLinearMap)).withLpMap 2 := by
    rw [ContinuousLinearMap.coe_withLpProdMap]
    ext x
    apply WithLp.ofLp_injective 2
    rfl
  rw [normalDisplacementSpectralCost_eq_sum_singularValues,
    normalDisplacementSpectralCost_eq_sum_singularValues,
    normalDisplacementSpectralCost_eq_sum_singularValues, hblock]
  exact sum_singularValues_prodMap_withLpMap _ _ rho

end TauCeti
