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

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

universe v

/-- The two ordered orientations of the fully unbounded ideal-gauge Sylvester
estimate.

The hypothesis binders are `_`-prefixed because they are proof-valued and the
conclusion `N.Mem X ∧ δ * N.gauge X ≤ N.gauge C` cannot mention them; the names
are kept for documentation rather than dropped to `_`. -/
structure GenuineOrderedSylvesterEngine : Prop where
  lowerUpper :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
      (N : KyFanDominantIdealFamily (𝕜 := ℂ))
      {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
      {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
      (_hA : A.IsSelfAdjoint) (_hB : B.IsSelfAdjoint)
      {X C : F →L[ℂ] E} {c δ : ℝ}
      (_hδ : 0 < δ)
      (_hAc : SemiboundedBelow A (c + δ))
      (_hBc : SemiboundedAbove B c)
      (_hEq : HasClosedSylvesterEquation A B X C)
      (_hC : N.Mem C),
      N.Mem X ∧
        δ * N.gauge X ≤
          N.gauge C
  upperLower :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
      (N : KyFanDominantIdealFamily (𝕜 := ℂ))
      {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)}
      {B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)}
      (_hA : A.IsSelfAdjoint) (_hB : B.IsSelfAdjoint)
      {X C : F →L[ℂ] E} {c δ : ℝ}
      (_hδ : 0 < δ)
      (_hAc : SemiboundedAbove A c)
      (_hBc : SemiboundedBelow B (c + δ))
      (_hEq : HasClosedSylvesterEquation A B X C)
      (_hC : N.Mem C),
      N.Mem X ∧
        δ * N.gauge X ≤
          N.gauge C

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti