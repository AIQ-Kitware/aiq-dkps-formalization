/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerScalarMinimum
public import DavisKahan.FiniteDimensional.DirectRotation.ComplexTracePrincipalAngles
public import ForTauCeti.Analysis.InnerProductSpace.UnitarySpectralCost

/-!
# The common reflection-sector comparison

A reflection's displacement singular values are zero and two. Its family
cost is therefore a multiple of its nuclear displacement. The classical
projection-distance bound and convexity of the augmented norm power bound
the scalar principal-angle minima by that cost. This is a common argument
for the family, independent of the older global Schatten optimization proof.
-/

public section
noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The exact spectral cost of a reflection, including zero smoothing. -/
theorem displacementCost_of_isSelfAdjoint (p tau : ℝ) (htau : 0 ≤ tau)
    (W : E ≃ₗᵢ[ℂ] E) (hW : IsSelfAdjoint (W : E →L[ℂ] E)) :
    displacementCost p tau (W : E →L[ℂ] E) =
      (penalty p tau 2 / 2) * UnitarilyInvariantSeminorm.nuclear ℂ E E
        (LinearMap.id - W.toLinearMap) := by
  exact normalDisplacementSpectralCost_of_isSelfAdjoint (penalty p tau)
    (penalty_zero p tau htau) (Unitary.linearIsometryEquiv.symm W) hW

/-- The complete gradient-kernel reflection sector dominates the scalar
principal-angle minimum sum. No classification of its optimizers is needed. -/
theorem sum_phaseMinimum_le_selfAdjoint_transport
    (p tau : ℝ) (hp : 1 ≤ p) (htau : 0 ≤ tau)
    (K L : Submodule ℂ E) (W : E ≃ₗᵢ[ℂ] E)
    (hW : IsSelfAdjoint (W : E →L[ℂ] E)) (hmap : K.map W.toLinearMap = L) :
    (∑ i : Fin (Module.finrank ℂ K), phaseMinimum p tau (K.principalAngles L i)) ≤
      displacementCost p tau (W : E →L[ℂ] E) := by
  have hKL : Module.finrank ℂ K = Module.finrank ℂ L := by
    rw [← hmap]
    exact (W.toLinearEquiv.finrank_map_eq K).symm
  have hbound := ComplexTraceOptimality.two_mul_sum_sin_principalAngles_le_nuclear_transport
    K L hKL W hmap
  have hnonneg := penalty_nonneg p tau 2 (by linarith) htau
  calc
    _ ≤ penalty p tau 2 *
        ∑ i : Fin (Module.finrank ℂ K), Real.sin (K.principalAngles L i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => phaseMinimum_le_penalty_two_mul_sin p tau _ hp htau
        ⟨K.principalAngles_nonneg L i, K.principalAngles_le_pi_div_two L i⟩
    _ ≤ (penalty p tau 2 / 2) * UnitarilyInvariantSeminorm.nuclear ℂ E E
        (LinearMap.id - W.toLinearMap) := by
      have h := mul_le_mul_of_nonneg_left hbound (div_nonneg hnonneg (by norm_num : (0:ℝ) ≤ 2))
      nlinarith
    _ = _ := (displacementCost_of_isSelfAdjoint p tau htau W hW).symm

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport
