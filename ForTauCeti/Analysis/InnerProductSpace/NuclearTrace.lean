/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.KyFan
public import Mathlib.Analysis.InnerProductSpace.Trace
public import ForTauCeti.Analysis.InnerProductSpace.SchattenSpectralCalculus

/-!
# Nuclear norm support by unitary trace pairings

The accepted Ky Fan maximum principle bounds the absolute trace by the
nuclear norm. Unitary invariance then gives a support inequality for every
unitary trace pairing. These are classical consequences of Ky Fan duality.
-/

public section

noncomputable section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The absolute trace is bounded by the sum of singular values. -/
theorem norm_trace_le_nuclear (A : E →ₗ[𝕜] E) :
    ‖LinearMap.trace 𝕜 E A‖ ≤ UnitarilyInvariantSeminorm.nuclear 𝕜 E E A := by
  let b := stdOrthonormalBasis 𝕜 E
  rw [LinearMap.trace_eq_sum_inner _ b]
  calc
    _ ≤ A.kyFanSum (Module.finrank 𝕜 E) := by
      simpa using A.norm_sum_inner_le_kyFanSum b.orthonormal b.orthonormal
    _ = _ := A.kyFanSum_eq_nuclear (LinearMap.finrank_range_le A)

/-- Every isometric change of source coordinates defines a unitary trace
support functional for the nuclear norm. -/
theorem re_trace_isometry_comp_le_nuclear (U : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] E) :
    RCLike.re (LinearMap.trace 𝕜 E (U.toLinearMap ∘ₗ A)) ≤
      UnitarilyInvariantSeminorm.nuclear 𝕜 E E A := by
  calc
    _ ≤ ‖LinearMap.trace 𝕜 E (U.toLinearMap ∘ₗ A)‖ := RCLike.re_le_norm _
    _ ≤ UnitarilyInvariantSeminorm.nuclear 𝕜 E E (U.toLinearMap ∘ₗ A) :=
      norm_trace_le_nuclear _
    _ = _ := (UnitarilyInvariantSeminorm.nuclear 𝕜 E E).map_linearIsometryEquiv_comp U A

/-- A complete orthonormal family gives a real nuclear-norm support bound. -/
theorem re_sum_inner_le_nuclear {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 E) (A : E →ₗ[𝕜] E)
    (u : ι → E) (hu : Orthonormal 𝕜 u) :
    (∑ i, RCLike.re ⟪u i, A (b i)⟫_𝕜) ≤
      UnitarilyInvariantSeminorm.nuclear 𝕜 E E A := by
  calc
    _ = RCLike.re (∑ i, ⟪u i, A (b i)⟫_𝕜) := (map_sum _ _ _).symm
    _ ≤ ‖∑ i, ⟪u i, A (b i)⟫_𝕜‖ := RCLike.re_le_norm _
    _ ≤ A.kyFanSum (Fintype.card ι) := A.norm_sum_inner_le_kyFanSum hu b.orthonormal
    _ = _ := A.kyFanSum_eq_nuclear (by
      rw [← Module.finrank_eq_card_basis b.toBasis]
      exact LinearMap.finrank_range_le A)

/-- The nuclear norm of a diagonalizable normal map is the sum of the
absolute eigenvalues, in any finite orthonormal eigenbasis. -/
theorem nuclear_eq_sum_norm_eigenvalues {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 E) (A : E →ₗ[𝕜] E) (mu : ι → 𝕜)
    (hA : ∀ i, A (b i) = mu i • b i) :
    UnitarilyInvariantSeminorm.nuclear 𝕜 E E A = ∑ i, ‖mu i‖ := by
  simpa only [ENNReal.toReal_one, Real.rpow_one, UnitarilyInvariantSeminorm.schatten_one] using
    schatten_rpow_eq_sum_norm_eigenvalues b A mu hA 1 ENNReal.one_ne_top

end TauCeti
