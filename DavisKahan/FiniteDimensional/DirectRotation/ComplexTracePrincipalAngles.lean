/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.ComplexPhaseTrace
public import ForTauCeti.Analysis.InnerProductSpace.Projection.TraceSine
public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle

/-!
# The principal-angle formula for the global complex trace optimum

The full projector-difference trace norm equals the sum of the two directed
principal-sine traces.  For equal-dimensional subspaces those traces agree,
so every principal angle contributes twice.  Composing this formula with the
unconditional nonacute phase minimizer gives the complete explicit optimum.
-/

public section

namespace TauCeti
namespace DavisKahan.FiniteDimensional
namespace ComplexTraceOptimality

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- The full ambient trace norm of a directed sine map is the sum of the
sines of the principal angles indexed by the dimension of its source. -/
theorem kyFanSum_directedSine_eq_sum_sin_principalAngles
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    ((U.sinThetaMap V).toLinearMap).kyFanSum (finrank ℂ H) =
      ∑ j : Fin (finrank ℂ U), Real.sin (Submodule.principalAngles U V (j : ℕ)) := by
  let A : U →ₗ[ℂ] H := (U.sinThetaMap V).toLinearMap ∘ₗ U.subtype
  have hσ : A.singularValues = ((U.sinThetaMap V).toLinearMap).singularValues := by
    rw [show A = (U.sinThetaMap V).toLinearMap ∘ₗ U.subtype from rfl,
      singularValues_sinThetaMap_comp_subtype, Submodule.principalSines_def]
  have hrank : finrank ℂ U ≤ finrank ℂ H := Submodule.finrank_le U
  calc
    ((U.sinThetaMap V).toLinearMap).kyFanSum (finrank ℂ H) =
        A.kyFanSum (finrank ℂ H) := by
          simp only [LinearMap.kyFanSum_def, ← Fin.sum_univ_eq_sum_range, ← hσ]
    _ = A.kyFanSum (finrank ℂ U) :=
      ((A.kyFanSum_eq_nuclear ((LinearMap.finrank_range_le A).trans hrank)).trans
        (A.kyFanSum_eq_nuclear (LinearMap.finrank_range_le A)).symm)
    _ = ∑ j : Fin (finrank ℂ U), Real.sin (Submodule.principalAngles U V (j : ℕ)) := by
      rw [LinearMap.kyFanSum_def, ← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      rw [Submodule.sin_principalAngles U V, Submodule.principalSines_def]
      exact congrArg (fun s : ℕ →₀ ℝ => s (j : ℕ)) hσ

/-- **Exact trace norm of the projector difference.** Every equal-dimensional
finite complex pair has a doubled directed-principal-sine spectrum *in trace*,
including right angles; no acuteness hypothesis is required. -/
theorem kyFanSum_projectionDifference_eq_two_sum_sin_principalAngles
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hUV : finrank ℂ U = finrank ℂ V) :
    (projection U - projection V).kyFanSum (finrank ℂ H) =
      2 * ∑ j : Fin (finrank ℂ U), Real.sin (Submodule.principalAngles U V (j : ℕ)) := by
  have hswap : ((V.sinThetaMap U).toLinearMap).kyFanSum (finrank ℂ H) =
      ((U.sinThetaMap V).toLinearMap).kyFanSum (finrank ℂ H) := by
    simp only [LinearMap.kyFanSum_def, ← Fin.sum_univ_eq_sum_range]
    have hσ : ((V.sinThetaMap U).toLinearMap).singularValues =
        ((U.sinThetaMap V).toLinearMap).singularValues := by
      simpa only [Submodule.principalSines_def] using
        (Submodule.principalSines_comm U V hUV).symm
    rw [hσ]
  rw [kyFanSum_projectionDifference_eq_directed_sines U V, hswap,
    kyFanSum_directedSine_eq_sum_sin_principalAngles U V]
  ring

/-- The classical nuclear projection-distance bound in the accepted
principal-angle coordinates. This uses the direct UI-norm inequality,
without taking a limit of Schatten transport optima. -/
theorem two_mul_sum_sin_principalAngles_le_nuclear_transport
    (K L : Submodule ℂ H) (hKL : finrank ℂ K = finrank ℂ L) (W : H ≃ₗᵢ[ℂ] H)
    (hmap : K.map W.toLinearMap = L) :
    2 * (∑ i : Fin (finrank ℂ K), Real.sin (K.principalAngles L i)) ≤
      UnitarilyInvariantSeminorm.nuclear ℂ H H (LinearMap.id - W.toLinearMap) := by
  have htrace := kyFanSum_projectionDifference_eq_two_sum_sin_principalAngles K L hKL
  have hfull (A : H →ₗ[ℂ] H) : A.kyFanSum (finrank ℂ H) =
      UnitarilyInvariantSeminorm.nuclear ℂ H H A :=
    A.kyFanSum_eq_nuclear (LinearMap.finrank_range_le A)
  rw [hfull] at htrace
  rw [← htrace]
  exact projectionDifference_uiNorm_le_displacement
    (UnitarilyInvariantSeminorm.nuclear ℂ H H) K L W hmap

/-- **Complete unconditional complex trace optimum**, including the classical
principal-angle sum and an explicitly attained global minimum. -/
theorem exists_global_complex_trace_minimizer_with_principalAngles
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hUV : finrank ℂ U = finrank ℂ V) :
    ∃ W : H ≃ₗᵢ[ℂ] H,
      U.map W.toLinearMap = V ∧
      (LinearMap.id - W.toLinearMap).kyFanSum (finrank ℂ H) =
        (projection U - projection V).kyFanSum (finrank ℂ H) ∧
      (LinearMap.id - W.toLinearMap).kyFanSum (finrank ℂ H) =
        2 * ∑ j : Fin (finrank ℂ U), Real.sin (Submodule.principalAngles U V (j : ℕ)) ∧
      ∀ Z : H ≃ₗᵢ[ℂ] H, U.map Z.toLinearMap = V →
        (LinearMap.id - W.toLinearMap).kyFanSum (finrank ℂ H) ≤
          (LinearMap.id - Z.toLinearMap).kyFanSum (finrank ℂ H) := by
  obtain ⟨W, hmap, htrace, hmin⟩ :=
    exists_global_complex_trace_minimizer U V hUV
  refine ⟨W, hmap, htrace, ?_, hmin⟩
  calc
    (LinearMap.id - W.toLinearMap).kyFanSum (finrank ℂ H) =
        (projection U - projection V).kyFanSum (finrank ℂ H) := htrace
    _ = 2 * ∑ j : Fin (finrank ℂ U),
        Real.sin (Submodule.principalAngles U V (j : ℕ)) :=
      kyFanSum_projectionDifference_eq_two_sum_sin_principalAngles U V hUV

end ComplexTraceOptimality
end DavisKahan.FiniteDimensional
end TauCeti
