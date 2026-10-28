/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerBoundary
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerAngleContinuity
public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerIdealFinite
public import DavisKahan.InfiniteDimensional.DirectRotation.SmoothedPowerFeasibility
public import ForTauCeti.Analysis.InnerProductSpace.Projection.SpectralTransportLimit
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenConvergence

/-!
# The common unrestricted spectral transport lower bound in Hilbert space

The finite family value theorem lifts through the reusable moving-target
spectral transport principle. Positive smoothing gives Hilbert--Schmidt
compactness; zero smoothing gives native Schatten compactness. No
separability, finite rank, defect balance or competitor plane hypothesis
is imposed. The bound includes divergent extended costs and is separate
from attainment and classification of optimizers.
-/

public section
noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPowerTransport

open FiniteDimensional.SmoothedPowerTransport
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Unrestricted Hilbert-space lower bound for the full closed family.**
The intrinsic directed-sine angle sum bounds every ambient complex unitary
transport cost, including nuclear/quadratic boundaries and infinite costs. -/
theorem angle_minimum_sum_le_transport (p tau : ℝ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (htau : 0 ≤ tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L) :
    (∑' j, ENNReal.ofReal (phaseMinimum p tau
      (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ)))) ≤
        (1 - (U : E →L[ℂ] E)).smoothedPowerCost p tau := by
  let f := fun s : ℝ≥0 => ENNReal.ofReal ((tau ^ 2 + (s : ℝ) ^ 2) ^ (p / 2) - tau ^ p)
  let m := fun t : ℝ => ENNReal.ofReal (phaseMinimum p tau t)
  have hm : ContinuousOn m (Set.Icc 0 (Real.pi / 2)) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((continuousOn_phaseMinimum_angle p tau (by linarith)).mono (fun _ h => h.1))
  apply tsum_angle_penalty_le_displacement_of_finite_transport_bound f
    (monotone_smoothedPower_scalar p tau (by linarith)) m
    (by simp only [m, phaseMinimum_zero p tau htau, ENNReal.ofReal_zero]) hm ?_ ?_ K L U hmap
  · intro V hfinite
    change (1 - (V : E →L[ℂ] E)).smoothedPowerCost p tau ≠ ∞ at hfinite
    have hcompact := ContinuousLinearMap.isCompactOperator_of_smoothedPowerCost_ne_top
      p tau hp hp2 htau (1 - (V : E →L[ℂ] E)) hfinite
    rw [← neg_sub 1 (V : E →L[ℂ] E)]
    exact hcompact.neg
  · intro M hM K₀ L₀ V hVmap
    have hdim : Module.finrank ℂ K₀ = Module.finrank ℂ L₀ := by
      rw [← hVmap]
      exact (V.toLinearEquiv.finrank_map_eq K₀).symm
    have hnonneg (i : Fin (Module.finrank ℂ K₀)) : 0 ≤ phaseMinimum p tau (K₀.principalAngles L₀ i) :=
      phaseMinimum_nonneg p tau _ (by linarith) htau (K₀.principalAngles_nonneg L₀ i)
    change (∑ i : Fin (Module.finrank ℂ K₀),
      ENNReal.ofReal (phaseMinimum p tau (K₀.principalAngles L₀ i))) ≤
        (1 - (V : M →L[ℂ] M)).smoothedPowerCost p tau
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hnonneg i),
      smoothedPowerCost_displacement_eq_ofReal p tau (by linarith) htau]
    apply ENNReal.ofReal_le_ofReal
    obtain ⟨_, _, _, hmin⟩ :=
      exists_unitary_minimizing_transport_principalAngles_of_nonneg p tau hp hp2 htau K₀ L₀ hdim
    exact hmin V hVmap

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPowerTransport
