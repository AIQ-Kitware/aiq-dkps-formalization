/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SinTheta.Canonical
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Unbounded

/-!
# Scalar-generic isometric theorem through the legacy engine

The problem records and the complex and real routes are complete and live in
`DavisKahan.SinTheta.Canonical`.  The scalar-generic shape below is stated
through the legacy unbounded Sylvester engine, whose generic spectral cutoff is
still an open obligation.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

section GenericIsometric

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

namespace IsometricSinThetaProblem

/-- Scalar-generic historical isometric theorem shape.  The manuscript
surface selects the direct complex proof, while `RealCanonical` supplies the
parallel real proof. -/
theorem result
    [HasApproximationNumberStrongCutoff.{u, v, 0} 𝕜]
    [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜]
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    (P : IsometricSinThetaProblem (𝕜 := 𝕜) (E := E) (F := F)
      (G := G) (H := H) N) :
    N.toRectangularSymmetricIdealFamily.Mem
        ((ContinuousLinearMap.id 𝕜 E -
          P.exactMap ∘L P.exactMap.adjoint) ∘L P.data.X) ∧
      P.gap * N.toRectangularSymmetricIdealFamily.gauge
          ((ContinuousLinearMap.id 𝕜 E -
            P.exactMap ∘L P.exactMap.adjoint) ∘L P.data.X)
        ≤ N.toRectangularSymmetricIdealFamily.gauge P.data.residual :=
  sinTheta_unbounded_exact
    N P.data P.exactMap P.ambient_selfAdjoint P.trial_selfAdjoint
      P.complement_selfAdjoint P.trial_isometry P.exact_decomposition
      P.gap_pos P.spectral_gap P.residual_mem

end IsometricSinThetaProblem

end GenericIsometric

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
