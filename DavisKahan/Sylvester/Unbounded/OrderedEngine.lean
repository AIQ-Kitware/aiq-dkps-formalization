/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sylvester.CutoffInterface
import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-!
# Replaceable ordered two-unbounded Sylvester engine

The two ordered half-line configurations are packaged behind one small record.
This leaf contains only the record and its source-facing contract, so a direct
implementation need not import the legacy unbounded Sylvester theorem.  The
compatibility implementation remains isolated in `GenuineOrderedEngineLegacy`.
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

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
