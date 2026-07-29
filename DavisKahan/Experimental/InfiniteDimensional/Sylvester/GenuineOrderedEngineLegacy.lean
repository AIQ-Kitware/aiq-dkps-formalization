/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sylvester.Unbounded.OrderedEngine
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.Unbounded

/-!
# Legacy genuine ordered Sylvester engine

Compatibility implementation of the ordered-engine contract through the
original spectral-cutoff development.  The canonical engine does not import
or use this leaf.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

universe v

/-- Compatibility proof for the lower-left/upper-right ordered branch. -/
theorem legacyGenuineOrderedSylvesterEngine_lowerUpper
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[ℂ] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : SemiboundedBelow A (c + δ))
    (hBc : SemiboundedAbove B c)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧
      δ * N.gauge X ≤
        N.gauge C := by
  exact unbounded_sylvester_mem_and_gauge_le_viaKyFan
    (N := N) (A := A) (B := B) (X := X) (C := C) (c := c) (δ := δ)
    hA hB hδ hAc hBc hEq hC

/-- Compatibility proof for the upper-left/lower-right ordered branch. -/
theorem legacyGenuineOrderedSylvesterEngine_upperLower
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[ℂ] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : SemiboundedAbove A c)
    (hBc : SemiboundedBelow B (c + δ))
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧
      δ * N.gauge X ≤
        N.gauge C := by
  exact unbounded_sylvester_mem_and_gauge_le_swapped_viaKyFan
    (N := N) (A := A) (B := B) (X := X) (C := C) (c := c) (δ := δ)
    hA hB hδ hAc hBc hEq hC

/-- Compatibility implementation using the existing finite-cutoff Ky Fan
proof. -/
noncomputable def legacyGenuineOrderedSylvesterEngine :
    GenuineOrderedSylvesterEngine where
  lowerUpper := legacyGenuineOrderedSylvesterEngine_lowerUpper
  upperLower := legacyGenuineOrderedSylvesterEngine_upperLower


end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti