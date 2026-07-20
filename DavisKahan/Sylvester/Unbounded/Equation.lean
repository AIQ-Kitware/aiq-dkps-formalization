/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sylvester.ClosedSylvesterEquation

/-!
# The one-unbounded Sylvester equation

This is not a second equation model.  It is the closed Sylvester equation of
`DavisKahan.Sylvester.ClosedSylvesterEquation` with the right block embedded as
a full-domain closed operator, so every lemma about the closed equation applies
verbatim.
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

/-- Equation with one unbounded left block and one bounded right block.

This is not a second equation model: it is the closed Sylvester equation with
the right block embedded as a full-domain closed operator. -/
abbrev HasUnboundedBoundedSylvesterEquation
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (B : F →L[𝕜] F) (X C : F →L[𝕜] E) : Prop :=
  HasClosedSylvesterEquation A
    (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded B) X C

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
