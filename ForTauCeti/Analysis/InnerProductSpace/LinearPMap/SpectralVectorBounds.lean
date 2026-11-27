/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralMeasure

/-!
# Vector-local form bounds from a half-line spectral condition

A domain vector killed by a spectral projection lies in the complementary
spectral range. The native range estimates then give the form bounds used in
the min–max arguments.

The original vector-local estimates were developed in
`ApproximationNumber/GramSpectralRank.lean` and later moved here.
-/

public section

namespace TauCeti
namespace LinearPMap

open scoped InnerProductSpace
open Set

section LocalHalfLine

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

private theorem mem_range_proj_compl_of_apply_eq_zero
    {S : Set ℝ} (hS : MeasurableSet S) {x : H}
    (hx : specProjection hA S hS x = 0) :
    x ∈ ((A.spectralPVM hA).proj Sᶜ hS.compl).range := by
  refine ⟨x, ?_⟩
  change (A.spectralPVM hA).proj Sᶜ hS.compl x = x
  rw [(A.spectralPVM hA).proj_compl S hS, _root_.sub_apply, ContinuousLinearMap.id_apply,
    ← specProjection_def, hx, sub_zero]

/-- **Vector-local lower energy bound.** If a domain vector has no spectral
component in `(-∞, c]`, its quadratic form is at least `c ‖x‖²`. -/
theorem le_re_inner_of_specProjection_Iic_apply_eq_zero {c : ℝ} (x : A.domain)
    (hz : specProjection hA (Set.Iic c) measurableSet_Iic (x : H) = 0) :
    c * ‖(x : H)‖ ^ 2 ≤ (⟪A x, (x : H)⟫_ℂ).re := by
  exact hA.mul_norm_sq_le_re_inner_of_mem_range_spectralPVM_proj measurableSet_Iic.compl
    (fun _ hs => le_of_lt (lt_of_not_ge hs)) (mem_range_proj_compl_of_apply_eq_zero hA _ hz)

/-- **Vector-local upper energy bound.** If a domain vector has no spectral
component in `[c, ∞)`, its quadratic form is at most `c ‖x‖²`. -/
theorem re_inner_le_of_specProjection_Ici_apply_eq_zero {c : ℝ} (x : A.domain)
    (hz : specProjection hA (Set.Ici c) measurableSet_Ici (x : H) = 0) :
    (⟪A x, (x : H)⟫_ℂ).re ≤ c * ‖(x : H)‖ ^ 2 := by
  exact hA.re_inner_le_mul_norm_sq_of_mem_range_spectralPVM_proj measurableSet_Ici.compl
    (fun _ hs => le_of_lt (lt_of_not_ge hs)) (mem_range_proj_compl_of_apply_eq_zero hA _ hz)

end LocalHalfLine

end LinearPMap
end TauCeti
