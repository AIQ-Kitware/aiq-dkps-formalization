/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SinTheta.SpectralBridge
import DavisKahan.Sylvester.Bounded
import DavisKahan.Experimental.InfiniteDimensional.Core.Unbounded

/-!
# Open obligations of the bounded spectral bridge

The definitions now live in `DavisKahan.SinTheta.SpectralBridge`; the four
estimates below remain unresolved.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Spectral inclusion in an interval gives the centered operator-norm bound. -/
theorem norm_sub_midpoint_le_of_spectrumIn_Icc
    {A : E →L[𝕜] E} (hA : A.IsSymmetric)
    {β α : ℝ} (hβα : β ≤ α)
    (hσ : SpectrumInRealSet A (Set.Icc β α)) :
    ‖A - (((β + α) / 2 : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E‖
      ≤ (α - β) / 2 := by
  sorry

/-- Exterior spectral inclusion makes the centered operator invertible. -/
theorem centered_isUnit_of_spectrumOutside
    {A : E →L[𝕜] E} (hA : A.IsSymmetric)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hσ : SpectrumInRealSet A {x | x ≤ β - δ ∨ α + δ ≤ x}) :
    ∃ hInv : BoundedInverseData
      (A - (((β + α) / 2 : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E),
      ‖hInv.inv‖ ≤ ((α - β) / 2 + δ)⁻¹ := by
  sorry

/-- The bounded spectral theorem supplies centered norm/inverse data. -/
noncomputable def centeredIntervalExteriorWitness_of_gap
    {A : E →L[𝕜] E} {B : F →L[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B β α δ) :
    CenteredIntervalExteriorWitness A B β α δ := by
  sorry

/-- Interval/exterior Sylvester estimate in every rectangular ideal family. -/
theorem sylvester_mem_and_gauge_le_of_intervalExteriorGap
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : E →L[𝕜] E} {B : F →L[𝕜] F}
    {X C : F →L[𝕜] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : IntervalExteriorGap A B β α δ)
    (hEq : A ∘L X - X ∘L B = C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge C := by
  sorry
end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
