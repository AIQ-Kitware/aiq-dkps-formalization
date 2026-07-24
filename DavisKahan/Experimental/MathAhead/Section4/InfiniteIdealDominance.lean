/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-!
# Approximation-number dominance for Section 4

The infinite-dimensional form of Davis--Kahan Corollary 4.1 does not follow
from the bare rectangular ideal interface alone.  Its proof uses the stronger
Fan-dominance principle: domination of every finite Ky Fan approximation gauge
implies ideal membership and gauge domination.

This module isolates the exact bridge.  Once Proposition 4.1 is available as a
pointwise approximation-number inequality, the corrected Corollary 4.1 is a
short consequence of `KyFanDominantIdealFamily`.
-/

open scoped InnerProductSpace BigOperators

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace Section4

open ExactSinTheta

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Pointwise domination of approximation singular values implies domination
of every finite Ky Fan approximation gauge. -/
theorem kyFanApproximationGauge_le_of_approximationSingularValue_le
    {A B : E →L[𝕜] F}
    (h : ∀ n, approximationSingularValue n A ≤
      approximationSingularValue n B) (k : ℕ) :
    kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B := by
  unfold kyFanApproximationGauge
  exact Finset.sum_le_sum fun n hn => h n

/-- Correct infinite-dimensional ideal-dominance bridge for Corollary 4.1.
The stronger family contains precisely the missing monotonicity principle. -/
theorem mem_and_gauge_le_of_approximationSingularValue_le
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {A B : E →L[𝕜] F}
    (hB : N.toRectangularSymmetricIdealFamily.Mem B)
    (h : ∀ n, approximationSingularValue n A ≤
      approximationSingularValue n B) :
    N.toRectangularSymmetricIdealFamily.Mem A ∧
      N.toRectangularSymmetricIdealFamily.gauge A ≤
        N.toRectangularSymmetricIdealFamily.gauge B := by
  apply mem_and_gauge_le_of_all_kyFanApproximationGauge_le N hB
  intro k
  exact kyFanApproximationGauge_le_of_approximationSingularValue_le h k

/-- A reusable certificate containing exactly the mathematical output of
Proposition 4.1 for a pair of rectangular operators. -/
structure RestrictedDisplacementApproximationDominance
    (A B : E →L[𝕜] F) : Prop where
  approximation_le : ∀ n,
    approximationSingularValue n A ≤ approximationSingularValue n B

/-- Corollary 4.1 follows formally from a Proposition 4.1 certificate for every
Fan-dominant ideal family. -/
theorem restrictedDisplacement_idealGauge_le
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {A B : E →L[𝕜] F}
    (D : RestrictedDisplacementApproximationDominance A B)
    (hB : N.toRectangularSymmetricIdealFamily.Mem B) :
    N.toRectangularSymmetricIdealFamily.Mem A ∧
      N.toRectangularSymmetricIdealFamily.gauge A ≤
        N.toRectangularSymmetricIdealFamily.gauge B :=
  mem_and_gauge_le_of_approximationSingularValue_le N hB D.approximation_le

/-- The operator-norm specialization of the dominance bridge. -/
theorem restrictedDisplacement_opNorm_le
    {A B : E →L[𝕜] F}
    (D : RestrictedDisplacementApproximationDominance A B) :
    ‖A‖ ≤ ‖B‖ := by
  simpa only [approximationSingularValue_zero] using D.approximation_le 0

/-- Every fixed positive Ky Fan gauge is a direct specialization. -/
theorem restrictedDisplacement_kyFan_le
    [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜]
    {A B : E →L[𝕜] F}
    (D : RestrictedDisplacementApproximationDominance A B)
    (k : ℕ) :
    kyFanApproximationGauge k A ≤ kyFanApproximationGauge k B :=
  kyFanApproximationGauge_le_of_approximationSingularValue_le
    D.approximation_le k

end Section4
end MathAhead
end Experimental
end DavisKahan
end ForMathlib
