/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.Bounded

/-!
# Bounded spectral bridge for interval/exterior separation

This module isolates the affine shift that converts the paper's spectral
hypotheses into the norm and inverse bounds required by Theorem 5.1.  The real
and complex spectral implementations should eventually share this interface.
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

/-- Real spectrum supplied by the eventual bounded self-adjoint spectral bridge. -/
noncomputable def boundedRealSpectrum (A : E →L[𝕜] E) : Set ℝ := by
  sorry

/-- The real spectrum is contained in a set. -/
def SpectrumInRealSet (A : E →L[𝕜] E) (s : Set ℝ) : Prop :=
  boundedRealSpectrum A ⊆ s

/-- The two blocks satisfy the interval/exterior configuration in either orientation. -/
def IntervalExteriorGap
    (A : E →L[𝕜] E) (B : F →L[𝕜] F)
    (β α δ : ℝ) : Prop :=
  (SpectrumInRealSet A (Set.Icc β α) ∧
    SpectrumInRealSet B {x | x ≤ β - δ ∨ α + δ ≤ x}) ∨
  (SpectrumInRealSet B (Set.Icc β α) ∧
    SpectrumInRealSet A {x | x ≤ β - δ ∨ α + δ ≤ x})

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

/-- Centered norm/inverse data in either interval/exterior orientation. -/
inductive CenteredIntervalExteriorWitness
    (A : E →L[𝕜] E) (B : F →L[𝕜] F)
    (β α δ : ℝ) : Type (max u v) where
  | intervalOnLeft
      (hA : ‖A - (((β + α) / 2 : ℝ) : 𝕜) •
        ContinuousLinearMap.id 𝕜 E‖ ≤ (α - β) / 2)
      (hB : BoundedInverseData
        (B - (((β + α) / 2 : ℝ) : 𝕜) •
          ContinuousLinearMap.id 𝕜 F))
      (hBnorm : ‖hB.inv‖ ≤ ((α - β) / 2 + δ)⁻¹)
  | intervalOnRight
      (hB : ‖B - (((β + α) / 2 : ℝ) : 𝕜) •
        ContinuousLinearMap.id 𝕜 F‖ ≤ (α - β) / 2)
      (hA : BoundedInverseData
        (A - (((β + α) / 2 : ℝ) : 𝕜) •
          ContinuousLinearMap.id 𝕜 E))
      (hAnorm : ‖hA.inv‖ ≤ ((α - β) / 2 + δ)⁻¹)

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
