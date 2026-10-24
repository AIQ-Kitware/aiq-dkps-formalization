/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.ComplexPhaseTrace
import ForTauCeti.Analysis.InnerProductSpace.Projection.TraceSine

/-!
# The principal-angle formula for the global complex trace optimum

The full projector-difference trace norm equals the sum of the two directed
principal-sine traces.  For equal-dimensional subspaces those traces agree,
so every principal angle contributes twice.  Composing this formula with the
unconditional nonacute phase minimizer gives the complete explicit optimum.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional
namespace ComplexTraceOptimality

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- The sine of each finite-dimensional principal angle is its directed
principal singular value, including zero and right-angle endpoints. -/
theorem sin_principalAngles_eq_principalSines
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (i : ℕ) :
    Real.sin (principalAngles U V i) = principalSines U V i := by
  rw [principalAngles, Finsupp.mapRange_apply]
  have hnonneg : 0 ≤ principalSines U V i :=
    (sinThetaMap U V).singularValues_nonneg i
  have hle : principalSines U V i ≤ 1 := by
    by_cases hi : i < finrank ℂ H
    · have hcontr : ∀ x : H, ‖sinThetaMap U V x‖ ≤ ‖x‖ := by
        intro x
        change ‖Vᗮ.starProjection (U.starProjection x)‖ ≤ ‖x‖
        exact (Vᗮ.norm_starProjection_apply_le _).trans
          (U.norm_starProjection_apply_le x)
      exact singularValues_le_one_of_contraction hcontr rfl ⟨i, hi⟩
    · have hzero : principalSines U V i = 0 :=
        (sinThetaMap U V).singularValues_of_finrank_le (Nat.le_of_not_gt hi)
      rw [hzero]
      norm_num
  exact Real.sin_arcsin (by linarith) hle

/-- The full ambient trace norm of a directed sine map is the sum of the
sines of the principal angles indexed by the dimension of its source. -/
theorem kyFanSum_directedSine_eq_sum_sin_principalAngles
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    kyFanSum (finrank ℂ H) (sinThetaMap U V) =
      ∑ j : Fin (finrank ℂ U), Real.sin (principalAngles U V (j : ℕ)) := by
  let A : U →ₗ[ℂ] H := sinThetaMap U V ∘ₗ U.subtype
  have hσ : A.singularValues = (sinThetaMap U V).singularValues := by
    rw [show A = sinThetaMap U V ∘ₗ U.subtype from rfl,
      singularValues_sinThetaMap_comp_subtype]
    rfl
  have hrank : finrank ℂ U ≤ finrank ℂ H := Submodule.finrank_le U
  calc
    kyFanSum (finrank ℂ H) (sinThetaMap U V) =
        kyFanSum (finrank ℂ H) A := by
          simp only [kyFanSum_eq_sum_fin, ← hσ]
    _ = kyFanSum (finrank ℂ U) A :=
      kyFanSum_eq_of_finrank_le hrank A
    _ = ∑ j : Fin (finrank ℂ U), Real.sin (principalAngles U V (j : ℕ)) := by
      rw [kyFanSum_eq_sum_fin]
      apply Finset.sum_congr rfl
      intro j _
      rw [sin_principalAngles_eq_principalSines U V]
      exact congrArg (fun s : ℕ →₀ ℝ => s (j : ℕ)) hσ

/-- **Exact trace norm of the projector difference.** Every equal-dimensional
finite complex pair has a doubled directed-principal-sine spectrum *in trace*,
including right angles; no acuteness hypothesis is required. -/
theorem kyFanSum_projectionDifference_eq_two_sum_sin_principalAngles
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hUV : finrank ℂ U = finrank ℂ V) :
    kyFanSum (finrank ℂ H) (projection U - projection V) =
      2 * ∑ j : Fin (finrank ℂ U), Real.sin (principalAngles U V (j : ℕ)) := by
  have hswap : kyFanSum (finrank ℂ H) (sinThetaMap V U) =
      kyFanSum (finrank ℂ H) (sinThetaMap U V) := by
    simp only [kyFanSum_eq_sum_fin]
    have hσ : (sinThetaMap V U).singularValues =
        (sinThetaMap U V).singularValues := by
      exact (principalSines_comm U V hUV).symm
    rw [hσ]
  rw [kyFanSum_projectionDifference_eq_directed_sines U V, hswap,
    kyFanSum_directedSine_eq_sum_sin_principalAngles U V]
  ring

/-- **Complete unconditional complex trace optimum**, including the classical
principal-angle sum and an explicitly attained global minimum. -/
theorem exists_global_complex_trace_minimizer_with_principalAngles
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hUV : finrank ℂ U = finrank ℂ V) :
    ∃ W : H ≃ₗᵢ[ℂ] H,
      U.map W.toLinearMap = V ∧
      kyFanSum (finrank ℂ H) (LinearMap.id - W.toLinearMap) =
        kyFanSum (finrank ℂ H) (projection U - projection V) ∧
      kyFanSum (finrank ℂ H) (LinearMap.id - W.toLinearMap) =
        2 * ∑ j : Fin (finrank ℂ U), Real.sin (principalAngles U V (j : ℕ)) ∧
      ∀ Z : H ≃ₗᵢ[ℂ] H, U.map Z.toLinearMap = V →
        kyFanSum (finrank ℂ H) (LinearMap.id - W.toLinearMap) ≤
          kyFanSum (finrank ℂ H) (LinearMap.id - Z.toLinearMap) := by
  obtain ⟨W, hmap, htrace, hmin⟩ :=
    exists_global_complex_trace_minimizer U V hUV
  refine ⟨W, hmap, htrace, ?_, hmin⟩
  calc
    kyFanSum (finrank ℂ H) (LinearMap.id - W.toLinearMap) =
        kyFanSum (finrank ℂ H) (projection U - projection V) := htrace
    _ = 2 * ∑ j : Fin (finrank ℂ U),
        Real.sin (principalAngles U V (j : ℕ)) :=
      kyFanSum_projectionDifference_eq_two_sum_sin_principalAngles U V hUV

end ComplexTraceOptimality
end DavisKahan.FiniteDimensional
end TauCeti
