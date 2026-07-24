/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Scratch.SharedFoundations.Residual.TrialResidual
import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-!
# Source-faithful hard seams for Davis--Kahan 1970, Theorem 6.3

The paper's generalized tangent theorem is directed.  Its strict dimension
hypothesis does not make the lower-dimensional trial subspace acute with the
larger exact subspace.  Instead the paper defines the sine data from the cross
block `E₀⋆ F₁` (equivalently the projection of the trial space into the
orthogonal complement of the exact space) and defines `tan Θ₀` by the same
singular-value list after applying tangent.

This file records the correct infinite-dimensional proof boundary:

* `directedSineBlock` is the source cross block in intrinsic subspace form;
* `HasDirectedTangentApproximationNumbers` records the required directed
  tangent singular-value data without assuming symmetric acuteness;
* `theorem6_3_ideal_of_kyFan_core` closes the arbitrary ideal-gauge conclusion
  once the source's finite Ky Fan inequalities have been proved.

The missing hard theorem is therefore the Ky Fan core, including the source's
finite-rank approximation/limiting argument.  It is not an implication from an
abstract dimension embedding to `IsAcute`.
-/

open scoped InnerProductSpace BigOperators
open ForMathlib.DavisKahan.Experimental.ExactSinTheta

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Scratch
namespace Section6

universe u

variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The directed sine block from the trial subspace `Z` toward the exact
subspace `V`.  It is the intrinsic version of `F₁⋆ E₀`; its adjoint has the
paper's displayed orientation `E₀⋆ F₁`, and the two have the same singular
values. -/
noncomputable def directedSineBlock
    (Z V : Submodule ℂ E) [Z.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] : Z →L[ℂ] E :=
  Vᗮ.starProjection ∘L Z.subtypeL

/-- Approximation-number formulation of the paper's phrase that `tan Θ₀` has
singular values `tan θ_j`, where `sin θ_j` are the singular values of the
directed cross block.  The strict inequality excludes the tangent pole; proving
it is part of the source theorem, not an input derived from symmetric
acuteness. -/
def HasDirectedTangentApproximationNumbers
    (Z V : Submodule ℂ E) [Z.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (tanTheta0 : Z →L[ℂ] E) : Prop :=
  (∀ n, approximationSingularValue n (directedSineBlock Z V) < 1) ∧
    ∀ n, approximationSingularValue n tanTheta0 =
      Real.tan
        (Real.arcsin
          (approximationSingularValue n (directedSineBlock Z V)))

/-- The source-facing Ky Fan core that remains to be proved.  This is separated
as a proposition so the frontier can track the substantive geometric/analytic
step independently of the already-available Fan-dominance promotion. -/
def Theorem63KyFanCore
    (delta : ℝ) (tanTheta0 residual : E →L[ℂ] F) : Prop :=
  ∀ k, delta * kyFanApproximationGauge k tanTheta0 ≤
    kyFanApproximationGauge k residual

/-- Once the source's Ky Fan inequalities are available, the arbitrary
unitarily invariant ideal conclusion is immediate from the existing
Fan-dominance bridge. -/
theorem theorem6_3_ideal_of_kyFan_core
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    {delta : ℝ} (hdelta : 0 < delta)
    {tanTheta0 residual : E →L[ℂ] F}
    (hResidual : N.toRectangularSymmetricIdealFamily.Mem residual)
    (hcore : Theorem63KyFanCore delta tanTheta0 residual) :
    N.toRectangularSymmetricIdealFamily.Mem tanTheta0 ∧
      delta * N.toRectangularSymmetricIdealFamily.gauge tanTheta0 ≤
        N.toRectangularSymmetricIdealFamily.gauge residual :=
  mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    N hdelta hResidual hcore

end Section6
end Scratch
end Experimental
end DavisKahan
end ForMathlib
