/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.Charbonnier
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# The zero-smoothing limit of the Charbonnier trace

The extended spectral cost is jointly lower semicontinuous in the
smoothing scale and the operator-norm topology. Along every nonnegative
scale tending to zero it converges to the native nuclear gauge, even
when that gauge is infinite. No trace-class domination is required.
-/

public section

noncomputable section

namespace ContinuousLinearMap

open Filter
open scoped ENNReal Topology

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Joint lower semicontinuity includes zero smoothing and infinite
values, with the operator variable in its norm topology. -/
theorem lowerSemicontinuous_charbonnierCost :
    LowerSemicontinuous (fun A : ℝ × (E →L[𝕜] F) => A.2.charbonnierCost A.1) := by
  apply lowerSemicontinuous_tsum
  intro n
  have hsv : Continuous (fun A : ℝ × (E →L[𝕜] F) => (A.2.singularValue n : ℝ)) :=
    NNReal.continuous_coe.comp ((continuous_singularValue n).comp continuous_snd)
  exact (ENNReal.continuous_ofReal.comp
    ((Real.continuous_sqrt.comp ((continuous_fst.pow 2).add (hsv.pow 2))).sub
      continuous_fst)).lowerSemicontinuous

/-- At zero smoothing the renormalized spectral trace is exactly the
accepted nuclear gauge, including a divergent trace. -/
theorem charbonnierCost_zero (T : E →L[𝕜] F) :
    T.charbonnierCost 0 = (TauCeti.OperatorIdealFamily.schatten 𝕜 1 (by norm_num)).gauge T := by
  simp [charbonnierCost, TauCeti.OperatorIdealFamily.gauge_schatten,
    Real.sqrt_sq (NNReal.coe_nonneg _)]

/-- Every nonnegative smoothing scale decreases the nuclear spectral
cost. This bound is valid without nuclear membership. -/
theorem charbonnierCost_le_nuclear (tau : ℝ) (hτ : 0 ≤ tau) (T : E →L[𝕜] F) :
    T.charbonnierCost tau ≤ (TauCeti.OperatorIdealFamily.schatten 𝕜 1 (by norm_num)).gauge T := by
  rw [← T.charbonnierCost_zero]
  unfold charbonnierCost
  apply ENNReal.tsum_le_tsum
  intro n
  apply ENNReal.ofReal_le_ofReal
  rw [zero_pow (by decide : 2 ≠ 0), zero_add, Real.sqrt_sq (NNReal.coe_nonneg _), sub_zero]
  have hs : 0 ≤ (T.singularValue n : ℝ) := NNReal.coe_nonneg _
  have hr := Real.sq_sqrt (show 0 ≤ tau ^ 2 + (T.singularValue n : ℝ) ^ 2 by positivity)
  have hr0 := Real.sqrt_nonneg (tau ^ 2 + (T.singularValue n : ℝ) ^ 2)
  nlinarith [mul_nonneg hτ hs]

/-- **Zero-smoothing limit in arbitrary Hilbert dimension.** The
Charbonnier costs converge to the nuclear gauge along every eventually
nonnegative scale tending to zero. Infinite nuclear values are allowed,
so the result also detects divergence outside the trace-class ideal. -/
theorem tendsto_charbonnierCost_zero
    (T : E →L[𝕜] F) {α : Type*} {l : Filter α} {tau : α → ℝ}
    (hτ : Tendsto tau l (𝓝 0)) (hpos : ∀ᶠ a in l, 0 ≤ tau a) :
    Tendsto (fun a => T.charbonnierCost (tau a)) l
      (𝓝 ((TauCeti.OperatorIdealFamily.schatten 𝕜 1 (by norm_num)).gauge T)) := by
  rw [← T.charbonnierCost_zero]
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact (hτ.prodMk_nhds tendsto_const_nhds).eventually
      (lowerSemicontinuous_charbonnierCost (0, T) a ha)
  · intro a ha
    filter_upwards [hpos] with b hb
    exact (T.charbonnierCost_le_nuclear (tau b) hb).trans_lt (by
      rwa [T.charbonnierCost_zero] at ha)

end ContinuousLinearMap
