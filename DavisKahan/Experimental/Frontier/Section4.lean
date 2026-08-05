/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Frontier.Section3
import DavisKahan.OperatorIdeal.UnitarilyInvariant.RectangularFamily
-- promoted infinite-dimensional Proposition 4.1 approximation-number majorization
-- and the Fan-dominant ideal bridge for Corollary 4.1.  This module depends only
-- on source-facing analysis, never on this frontier file, so the edge is acyclic.
import DavisKahan.Experimental.MathAhead.Section4.InfiniteProposition41
-- production Proposition 4.2 (`Sources/DavisKahan1970/Section4BasisAngleEnergy`),
-- which this file's statement is grounded on by `:=`.  Production never imports
-- the frontier, so the edge is acyclic.
import DavisKahan.Sources.DavisKahan1970.Section4BasisAngleEnergy

/-!
# Section 4 frontier: valid extremal properties of the direct rotation

The published Proposition 4.4 is excluded: the repository contains a compiled
counterexample.  This module states infinite-dimensional forms of the valid
Propositions 4.1--4.3 using approximation numbers, finite orthonormal-family
partial sums, and rectangular ideal gauges.
-/

open scoped InnerProductSpace BigOperators

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace Frontier
namespace Section4

-- `` is `TauCeti.DavisKahan.Experimental`, so it
-- can only be opened once those namespaces are entered
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
        ((1 - W) ∘L projection U) n :=
  MathAhead.Section4.proposition4_1_restrictedDisplacement_approximationNumbers_scratch
    U V hacute W hWunitary hWmap n

/-- Davis--Kahan 1970, Corollary 4.1 at Fan-dominant ideal-gauge scope.

The bare `RectangularSymmetricIdealFamily` interface does not supply the
monotonicity principle "domination of every finite Ky Fan approximation gauge
implies ideal membership and gauge domination" that the infinite-dimensional
statement genuinely needs; the honest hypothesis is a `KyFanDominantIdealFamily`,
whose membership and gauge are read off through `toRectangularSymmetricIdealFamily`. -/
theorem corollary4_1_restrictedDisplacement_idealGauge
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (hacute : IsAcute U V) (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * projection U = projection V * W)
    (hWmem : N.Mem ((1 - W) ∘L projection U)) :
    N.Mem
        ((1 - spectraDirectRotation U V hacute) ∘L projection U) ∧
      N.gauge
          ((1 - spectraDirectRotation U V hacute) ∘L projection U) ≤
        N.gauge ((1 - W) ∘L projection U) :=
  MathAhead.Section4.restrictedDisplacement_idealGauge_le N
    (MathAhead.Section4.infinite_restrictedDisplacementDominance
      U V hacute W hWunitary hWmap)
    hWmem

/-- Squared sine cost of one unit source vector under a unitary competitor. -/
noncomputable def basisAngleSquareCost (W : H →L[ℂ] H) (x : H) : ℝ :=
  1 - (RCLike.re ⟪x, W x⟫_ℂ) ^ 2

/-! ### Proposition 4.2, and a transcription defect in its earlier form

**This statement used to quantify over an arbitrary `Finset` of an arbitrary
orthonormal family in `U`, and in that form it is FALSE.**  Recorded here with
the argument, because the earlier form was audited as "sound" and it is not, and
because the singleton instance is the natural thing to attack first.

Take `ι := Unit`, so the sum has one term.  The claim becomes
`(re ⟪x, D x⟫)² ≥ (re ⟪x, W x⟫)²` for a single unit `x ∈ U`.  Now:

* `re ⟪x, D x⟫ = ⟪C x, x⟫` with `C = |S|` the positive Halmos cosine
  (`re_inner_spectraDirectRotation_eq_absoluteValue`);
* for unit `x ∈ U`, `‖C x‖ = ‖P_V x‖`, because
  `C² = 1 - (P_U - P_V)²` and `(P_U - P_V) x = x - P_V x` has square norm
  `1 - ‖P_V x‖²`;
* any admissible `W` sends `x` into `V` with `‖W x‖ = 1`, so
  `re ⟪x, W x⟫ = re ⟪P_V x, W x⟫ ≤ ‖P_V x‖`, **with equality** for the `W`
  determined by `W x = P_V x / ‖P_V x‖` — which exists whenever `U` and `V` have
  equal finite dimension, since any unit vector of `U` maps to any unit vector of
  `V` under some isometry, and `Uᗮ → Vᗮ` may be chosen freely;
* Cauchy--Schwarz gives `⟪C x, x⟫ ≤ ‖C x‖` **strictly** unless `x` is an
  eigenvector of `C`.

So *every* unit `x ∈ U` that is not a principal vector refutes the singleton
case.  Concretely, in `ℂ⁴` with principal angles `0` and `π/3` (acute, since
`sin(π/3) < 1`) and `x = (e₁ + e₂)/√2`: `⟪C x, x⟫ = 3/4` while
`‖P_V x‖ = √(5/8) ≈ 0.7906`, so the competitor's cost `1 - 5/8 = 3/8` is
*smaller* than the direct rotation's `1 - 9/16 = 7/16`.

The defect is a missing hypothesis, not a wrong theorem: the source quantifies
over an orthonormal **basis** of `U`, and the inequality is a statement about the
total energy, which no proper subfamily inherits.  Summing the same `ℂ⁴` example
over the full basis `{(e₁±e₂)/√2}` restores it: `1.025 < 1.125`.

### A SECOND defect in the same statement, found 2026-08-05

Adding the basis hypothesis was necessary and **not sufficient**.  The form

```
∑ᵢ cost W bᵢ  ≥  ∑ᵢ cost D bᵢ      -- the SAME basis on both sides
```

is still false, because the right-hand side is not the paper's.  The paper's
right-hand side is the sum of squared *principal* sines, which is
basis-independent; `∑ᵢ cost D bᵢ` is not — it is minimised at the principal
basis and strictly larger elsewhere, since `re ⟪bᵢ, D bᵢ⟫ = ⟪C bᵢ, bᵢ⟫` falls
strictly below `‖C bᵢ‖` off the eigenvectors of `C`.

Counterexample, in `ℝ⁴` (so also in `ℂ⁴`).  Take `U = span(e₁, e₂)` and `V` at
principal angles `0` and `arccos (1/10)`; the pair is acute, since
`‖P_U − P_V‖ = √(1 − 1/100) < 1`.  Rotate the basis of `U` by `0.2` radians.
Then

* the direct rotation costs `1.051417`;
* an explicit admissible competitor — an orthogonal `4 × 4` matrix `W` with
  `W P_U = P_V W`, obtained as the maximiser of `∑ᵢ (re ⟪bᵢ, W bᵢ⟫)²` over the
  admissible class, a rank-one pencil computation — costs `1.028237`;
* the principal-sine sum, which is what Proposition 4.2 actually bounds by, is
  `0.99`, and both numbers exceed it.

So the statement below is written against the paper's basis-free right-hand
side `∑ᵢ (1 − ‖C bᵢ‖²) = dim U − tr((C|_U)²)`, and it is proved.  The direct
rotation attains it on a principal basis — that is
`proposition4_2_attained_on_principal_vector` — which is the sense in which it
is the minimiser.

It is finite-index; the infinite-dimensional form additionally needs the
summability convention that `DK-4.2-prop` records as open. -/
theorem proposition4_2_basisAngleSquareSum
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ U)
    (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * projection U = projection V * W) :
    ∑ i, basisAngleSquareCost W ((b i : H)) ≥
      ∑ i, (1 - ‖spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)
        ((b i : H))‖ ^ 2) :=
  MathAhead.Section4.sum_displacementAngleSineSq_ge U V b W hWunitary hWmap

/-- **Proposition 4.2, infinite-dimensional form.**

The summability convention `DK-4.2-prop` recorded as open turns out to have
nothing to settle: with the paper's basis-free right-hand side the estimate is
termwise, so it needs neither completeness nor orthogonality of the family, and
taking the sums in `ℝ≥0∞` makes them unconditionally defined.  The index type is
arbitrary. -/
theorem proposition4_2_basisAngleSquareSum_infinite
    {ι : Type*} (b : ι → H) (hb : ∀ i, b i ∈ U) (hbnorm : ∀ i, ‖b i‖ = 1)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * projection U = projection V * W) :
    ∑' i, ENNReal.ofReal (1 - ‖spectraOperatorAbsoluteValue
        (spectraCanonicalIntertwiner U V) (b i)‖ ^ 2) ≤
      ∑' i, ENNReal.ofReal (basisAngleSquareCost W (b i)) :=
  MathAhead.Section4.tsum_displacementAngleSineSq_ge_of_mem U V W hWunitary
    hWmap b hb hbnorm

/-- The bound of `proposition4_2_basisAngleSquareSum` is attained by the direct
rotation at a principal vector, so it is the true minimum and the direct
rotation is a minimiser. -/
theorem proposition4_2_attained_on_principal_vector
    (hacute : IsAcute U V) {x : H} {μ : ℝ} (hμ : 0 ≤ μ) (hxnorm : ‖x‖ = 1)
    (hCx : spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V) x =
      (μ : ℂ) • x) :
    basisAngleSquareCost (spectraDirectRotation U V hacute) x =
      1 - ‖spectraOperatorAbsoluteValue
        (spectraCanonicalIntertwiner U V) x‖ ^ 2 :=
  MathAhead.Section4.displacementAngleSineSq_directRotation_eq_of_smul U V
    hacute hμ hxnorm hCx

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
end TauCeti