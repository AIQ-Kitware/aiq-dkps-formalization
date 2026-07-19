/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperFullAngle
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperCosineAngleReal

/-!
# Literal full angle for real subspaces

The full real angle is the direct sum of the two source-directed angles after
canonical complexification, exactly paralleling the complex source definition.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace
open Foundation RealComplexification

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Literal full real operator angle on complexified coordinates. -/
noncomputable def paperSourceFullAngleR
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :=
  paperSourceFullAngleC (complexifySubmodule U) (complexifySubmodule V)

/-- Literal sine of the full real operator angle. -/
noncomputable def paperSourceFullSinR
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :=
  paperSourceFullSinC (complexifySubmodule U) (complexifySubmodule V)

end

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
