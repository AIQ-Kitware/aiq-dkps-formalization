/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Frontier.Section3
import DavisKahan.OperatorIdeal.UnitarilyInvariant.RectangularFamily

/-!
# Section 4 frontier: valid extremal properties of the direct rotation

The published Proposition 4.4 is excluded: the repository contains a compiled
counterexample.  This module states infinite-dimensional forms of the valid
Propositions 4.1--4.3 using approximation numbers, finite orthonormal-family
partial sums, and rectangular ideal gauges.
-/

open scoped InnerProductSpace BigOperators

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Frontier
namespace Section4

-- `SpectraBridge` is `ForMathlib.DavisKahan.Experimental.SpectraBridge`, so it
-- can only be opened once those namespaces are entered
open SpectraBridge
open ExactSinTheta

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- Davis--Kahan 1970, Proposition 4.1: every approximation number of the
restricted displacement is minimized by the direct rotation. -/
theorem proposition4_1_restrictedDisplacement_approximationNumbers
    (hacute : IsAcute U V) (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * projection U = projection V * W)
    (n : ℕ) :
    -- spelled out rather than by dot notation: the projection coercion makes
    -- `.approximationNumber` on the following line resolve against `H`
    ContinuousLinearMap.approximationNumber
        ((1 - spectraDirectRotation U V hacute) ∘L projection U) n ≤
      ContinuousLinearMap.approximationNumber
        ((1 - W) ∘L projection U) n := by
  sorry

/-- Davis--Kahan 1970, Corollary 4.1 at rectangular ideal-gauge scope. -/
theorem corollary4_1_restrictedDisplacement_idealGauge
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    (hacute : IsAcute U V) (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * projection U = projection V * W)
    (hWmem : N.Mem ((1 - W) ∘L projection U)) :
    N.Mem ((1 - spectraDirectRotation U V hacute) ∘L projection U) ∧
      N.gauge ((1 - spectraDirectRotation U V hacute) ∘L projection U) ≤
        N.gauge ((1 - W) ∘L projection U) := by
  sorry

/-- Squared sine cost of one unit source vector under a unitary competitor. -/
noncomputable def basisAngleSquareCost (W : H →L[ℂ] H) (x : H) : ℝ :=
  1 - (RCLike.re ⟪x, W x⟫_ℂ) ^ 2

/-- Davis--Kahan 1970, Proposition 4.2: every finite partial sum along an
orthonormal source family is bounded below by the corresponding direct-rotation
principal-angle energy. -/
theorem proposition4_2_basisAngleSquareSum
    {ι : Type*} (s : Finset ι) (v : ι → H)
    (hv : Orthonormal ℂ v)
    (hvU : ∀ i, v i ∈ U)
    (hacute : IsAcute U V) (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * projection U = projection V * W) :
    ∑ i ∈ s, basisAngleSquareCost W (v i) ≥
      ∑ i ∈ s,
        basisAngleSquareCost (spectraDirectRotation U V hacute) (v i) := by
  sorry

/-- Davis--Kahan 1970, Proposition 4.3: every approximation number of the
squared full displacement is minimized by the direct rotation. -/
theorem proposition4_3_squaredDisplacement_approximationNumbers
    (hacute : IsAcute U V) (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * projection U = projection V * W)
    (n : ℕ) :
    ((1 - star (spectraDirectRotation U V hacute)) *
        (1 - spectraDirectRotation U V hacute)).approximationNumber n ≤
      ((1 - star W) * (1 - W)).approximationNumber n := by
  sorry

end Section4
end Frontier
end Experimental
end DavisKahan
end ForMathlib
