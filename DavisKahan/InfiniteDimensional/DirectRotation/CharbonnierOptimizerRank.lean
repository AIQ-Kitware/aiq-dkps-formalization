/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.CharbonnierOptimizerClassification

/-!
# A critical finite-rank certificate for every Hilbert Charbonnier optimizer

All global optimizers differ from every completed direct rotation only
on the finite strictly supercritical sine sector. Its dimension is
bounded by the squared Hilbert--Schmidt projection gap divided by
the squared critical sine. Critical and zero-angle spaces require no update.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition

open FiniteDimensional.SmoothedPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Every optimizer has the critical finite-rank budget.** The same
intrinsic sector controls all optimizers and every defect completion,
rather than only a specially constructed attaining transporter. -/
theorem charbonnier_minimizer_has_critical_rank_budget_complex
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
      (K.starProjection - L.starProjection) ≠ ∞)
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L)
    (hmin : ∀ T : E ≃ₗᵢ[ℂ] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[ℂ] E)).charbonnierCost tau ≤
        (1 - (T : E →L[ℂ] E)).charbonnierCost tau) :
    let c := Real.sin (smoothedCriticalAngle tau)
    let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
    ((nonacuteDirectRotation K L J).toLinearMap - U.toLinearMap).rank ≤
        Module.finrank ℂ M ∧
      (Module.finrank ℂ M : ℝ≥0∞) * ENNReal.ofReal c ^ (2 : ℝ) ≤
        (OperatorIdealFamily.schatten ℂ 2 (by norm_num)).gauge
          (K.starProjection - L.starProjection) ^ (2 : ℝ) := by
  let c := Real.sin (smoothedCriticalAngle tau)
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  have hangle := smoothedCriticalAngle_mem tau hτ
  have hc : 0 < c := Real.sin_pos_of_pos_of_lt_pi hangle.1
    (by linarith [hangle.2, Real.pi_pos])
  have hc1 : c < 1 := by
    have h := Real.strictMonoOn_sin
      ⟨by linarith [hangle.1, Real.pi_pos], hangle.2.le⟩
      ⟨by linarith [Real.pi_pos], le_rfl⟩ hangle.2
    simpa only [Real.sin_pi_div_two] using h
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top
    2 (by norm_num) (K.starProjection - L.starProjection) hD
  let : FiniteDimensional ℂ M := (finite_sine_spectral_cutoff K L hcompact c hc).1
  obtain ⟨T, hTmap, _, _, hTfinite, _, _⟩ :=
    exists_charbonnier_minimizer_by_finite_correction tau hτ K L J hD c hc hc1 le_rfl
  have hfinite := ne_top_of_le_ne_top hTfinite (hmin T hTmap)
  have htail := apply_eq_nonacuteDirectRotation_on_inactive_tail_of_charbonnier_minimal_complex
    tau hτ K L J hD c hc hc1 le_rfl U hmap hfinite hmin
  refine ⟨?_, finrank_sine_spectral_cutoff_mul_rpow_le_schatten_projection_sub 2 (by norm_num)
    K L hcompact c hc⟩
  let A : E →L[ℂ] E := nonacuteDirectRotation K L J - (U : E →L[ℂ] E)
  have hsupport : A = A ∘L M.starProjection := by
    apply ContinuousLinearMap.ext
    intro x
    change nonacuteDirectRotation K L J x - U x =
      nonacuteDirectRotation K L J (M.starProjection x) - U (M.starProjection x)
    calc
      _ = nonacuteDirectRotation K L J (M.starProjection x + Mᗮ.starProjection x) -
          U (M.starProjection x + Mᗮ.starProjection x) := by
        rw [M.starProjection_add_starProjection_orthogonal]
      _ = _ := by
        rw [map_add, map_add, htail _ (Mᗮ.starProjection_apply_mem x)]
        abel
  change A.rank ≤ Module.finrank ℂ M
  rw [hsupport]
  exact A.rank_comp_starProjection_le (by rw [Module.finrank_eq_rank])

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition
