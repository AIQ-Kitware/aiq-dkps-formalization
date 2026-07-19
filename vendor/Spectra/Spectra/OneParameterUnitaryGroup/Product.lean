/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Spectra.OneParameterUnitaryGroup.Basic

/-!
# Products of strongly commuting one-parameter unitary groups

The pointwise product of two commuting strongly continuous unitary groups is
again a strongly continuous unitary group.  The only analytic point is strong
continuity with both the operator and vector varying; it follows by adding and
subtracting `U(t) (V(t0) x)` and using norm preservation.
-/

open InnerProductSpace Complex Filter Topology
open scoped InnerProductSpace

namespace Spectra.OneParameterUnitaryGroup

noncomputable section

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A unitary family may be applied to a convergent family of vectors while
the parameter varies.  Strong convergence on each fixed vector and norm
preservation are enough; no operator-norm continuity is required. -/
theorem tendsto_apply_unitary_family
    {α : Type*} {l : Filter α} {t : α → ℝ} {t₀ : ℝ}
    (W : ℝ → H →L[ℂ] H)
    (hW : ∀ s x, ‖W s x‖ = ‖x‖)
    (hWstrong : ∀ x, Continuous fun s => W s x)
    {x : α → H} {x₀ : H}
    (ht : Tendsto t l (𝓝 t₀)) (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun a => W (t a) (x a)) l (𝓝 (W t₀ x₀)) := by
  have hvanish : Tendsto (fun a => W (t a) (x a - x₀)) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [hW] using (hx.sub_const x₀).norm
  have hfixed : Tendsto (fun a => W (t a) x₀ - W t₀ x₀) l (𝓝 0) := by
    exact (((hWstrong x₀).tendsto t₀).comp ht).sub_const (W t₀ x₀)
  have hadd := hvanish.add hfixed
  convert hadd using 1
  · funext a
    rw [map_sub]
    abel
  · simp

theorem continuous_apply_unitary_family
    (W : ℝ → H →L[ℂ] H)
    (hW : ∀ t x, ‖W t x‖ = ‖x‖)
    (hWstrong : ∀ x, Continuous fun t => W t x)
    {x : ℝ → H} (hx : Continuous x) :
    Continuous fun t => W t (x t) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hvanish : Tendsto (fun t => W t (x t - x t₀)) (𝓝 t₀) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [hW] using
      ((hx.continuousAt.sub continuousAt_const).norm)
  have hfixed : Tendsto (fun t => W t (x t₀) - W t₀ (x t₀))
      (𝓝 t₀) (𝓝 0) := by
    simpa using (hWstrong (x t₀)).continuousAt.sub_const (W t₀ (x t₀))
  have hadd := hvanish.add hfixed
  convert hadd using 1
  · funext t
    rw [map_sub]
    abel
  · simp

/-- The pointwise product of two strongly commuting unitary groups. -/
noncomputable def mul (U V : OneParameterUnitaryGroup (H := H))
    (hcomm : ∀ s t : ℝ, Commute (U.U s) (V.U t)) :
    OneParameterUnitaryGroup (H := H) where
  U t := U.U t * V.U t
  unitary t x y := by
    simp only [ContinuousLinearMap.mul_apply]
    rw [U.unitary t, V.unitary t]
  group_law s t := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply]
    have hc := (hcomm t s).eq
    have hcx := DFunLike.congr_fun hc (V.U t x)
    rw [U.group_law, V.group_law]
    simp only [ContinuousLinearMap.comp_apply]
    simpa only [ContinuousLinearMap.mul_apply] using congrArg (U.U s) hcx
  identity := by
    rw [U.identity, V.identity]
    ext x
    simp
  strong_continuous x := by
    apply continuous_apply_unitary_family (fun t => U.U t)
      (fun t y => U.norm_preserving t y) U.strong_continuous
    exact V.strong_continuous x

@[simp]
theorem mul_apply (U V : OneParameterUnitaryGroup (H := H))
    (hcomm : ∀ s t : ℝ, Commute (U.U s) (V.U t))
    (t : ℝ) (x : H) :
    mul U V hcomm |>.U t x = U.U t (V.U t x) :=
  rfl

end
end Spectra.OneParameterUnitaryGroup
