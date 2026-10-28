/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedPowerScalarMinimum
public import ForTauCeti.Analysis.InnerProductSpace.UnitarySpectralCost
public import ForTauCeti.Analysis.OperatorIdeal.SmoothedPower

/-!
# Exact finite agreement of the common spectral cost

The extended singular-value cost on a finite unitary displacement is the
nonnegative real CFC trace already optimized by the ambient family theorem.
This classical spectral identity fixes the objective across the Hilbert lift.
-/

public section
noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The finite CFC trace and the extended displacement cost agree exactly,
including all zero singular values and zero-smoothing boundaries. -/
theorem smoothedPowerCost_displacement_eq_ofReal (p tau : ℝ) (hp : 0 ≤ p) (htau : 0 ≤ tau)
    (U : E ≃ₗᵢ[ℂ] E) :
    (1 - (U : E →L[ℂ] E)).smoothedPowerCost p tau =
      ENNReal.ofReal (displacementCost p tau (U : E →L[ℂ] E)) := by
  let : IsStarNormal (U : E →L[ℂ] E) :=
    isStarNormal_of_mem_unitary (Unitary.linearIsometryEquiv.symm U).property
  rw [ContinuousLinearMap.smoothedPowerCost_eq_ofReal_sum p tau hp htau]
  change ENNReal.ofReal (∑ i : Fin (Module.finrank ℂ E),
      penalty p tau (((1 - (U : E →L[ℂ] E)).toLinearMap).singularValues i)) =
    ENNReal.ofReal (normalDisplacementSpectralCost (penalty p tau) (U : E →L[ℂ] E))
  rw [normalDisplacementSpectralCost_eq_sum_singularValues]
  rfl

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPowerTransport
