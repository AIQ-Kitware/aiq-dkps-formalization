/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.Unbounded

/-!
# Replaceable ordered two-unbounded Sylvester engine

The full genuine-spectrum sine-theta theorem has only two unfinished analytic
branches after interval/exterior separation is discharged: the two ordered
half-line configurations.  This leaf packages those branches behind one small
record.

Downstream genuine-spectrum and sine-theta statements depend only on
`canonicalGenuineOrderedSylvesterEngine`.  The current value is the compatibility
implementation through the original cutoff development.  A direct Spectra
implementation can replace that single definition without changing any final
theorem statement.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

universe v

/-- The two ordered orientations of the fully unbounded ideal-gauge Sylvester
estimate. -/
structure GenuineOrderedSylvesterEngine : Prop where
  lowerUpper :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
      (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
      {A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
      {B : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
      (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
      {X C : F →L[ℂ] E} {c δ : ℝ}
      (hδ : 0 < δ)
      (hAc : SemiboundedBelow A (c + δ))
      (hBc : SemiboundedAbove B c)
      (hEq : HasClosedSylvesterEquation A B X C)
      (hC : N.toRectangularSymmetricIdealFamily.Mem C),
      N.toRectangularSymmetricIdealFamily.Mem X ∧
        δ * N.toRectangularSymmetricIdealFamily.gauge X ≤
          N.toRectangularSymmetricIdealFamily.gauge C
  upperLower :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
      (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
      {A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
      {B : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
      (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
      {X C : F →L[ℂ] E} {c δ : ℝ}
      (hδ : 0 < δ)
      (hAc : SemiboundedAbove A c)
      (hBc : SemiboundedBelow B (c + δ))
      (hEq : HasClosedSylvesterEquation A B X C)
      (hC : N.toRectangularSymmetricIdealFamily.Mem C),
      N.toRectangularSymmetricIdealFamily.Mem X ∧
        δ * N.toRectangularSymmetricIdealFamily.gauge X ≤
          N.toRectangularSymmetricIdealFamily.gauge C

/-- Compatibility proof for the lower-left/upper-right ordered branch. -/
theorem legacyGenuineOrderedSylvesterEngine_lowerUpper
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    {A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[ℂ] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : SemiboundedBelow A (c + δ))
    (hBc : SemiboundedAbove B c)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.toRectangularSymmetricIdealFamily.Mem C) :
    N.toRectangularSymmetricIdealFamily.Mem X ∧
      δ * N.toRectangularSymmetricIdealFamily.gauge X ≤
        N.toRectangularSymmetricIdealFamily.gauge C := by
  exact unbounded_sylvester_mem_and_gauge_le_viaKyFan
    (N := N) (A := A) (B := B) (X := X) (C := C) (c := c) (δ := δ)
    hA hB hδ hAc hBc hEq hC

/-- Compatibility proof for the upper-left/lower-right ordered branch. -/
theorem legacyGenuineOrderedSylvesterEngine_upperLower
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ))
    {A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[ℂ] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : SemiboundedAbove A c)
    (hBc : SemiboundedBelow B (c + δ))
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.toRectangularSymmetricIdealFamily.Mem C) :
    N.toRectangularSymmetricIdealFamily.Mem X ∧
      δ * N.toRectangularSymmetricIdealFamily.gauge X ≤
        N.toRectangularSymmetricIdealFamily.gauge C := by
  exact unbounded_sylvester_mem_and_gauge_le_swapped_viaKyFan
    (N := N) (A := A) (B := B) (X := X) (C := C) (c := c) (δ := δ)
    hA hB hδ hAc hBc hEq hC

/-- Compatibility implementation using the existing finite-cutoff Ky Fan
proof. -/
noncomputable def legacyGenuineOrderedSylvesterEngine :
    GenuineOrderedSylvesterEngine where
  lowerUpper := legacyGenuineOrderedSylvesterEngine_lowerUpper
  upperLower := legacyGenuineOrderedSylvesterEngine_upperLower

/-- The single switch consumed by the genuine-spectrum capstone.  Replace this
value with the direct Spectra engine once its cutoff and truncation proof is
complete. -/
noncomputable def canonicalGenuineOrderedSylvesterEngine :
    GenuineOrderedSylvesterEngine :=
  legacyGenuineOrderedSylvesterEngine

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
