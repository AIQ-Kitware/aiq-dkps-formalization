/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Frontier.Section3
import DavisKahan.OperatorIdeal.UnitarilyInvariant.RectangularFamily
-- promoted infinite-dimensional Proposition 4.1 approximation-number majorization
-- and the Fan-dominant ideal bridge for Corollary 4.1.  This module depends only
-- on source-facing analysis, never on this frontier file, so the edge is acyclic.
import DavisKahan.MathAhead.Section4.InfiniteProposition41
-- infinite-dimensional Proposition 4.3 by pinching and orthogonal block sums.  Same
-- acyclicity argument as the line above: it depends only on source-facing analysis.
import DavisKahan.MathAhead.Section4.InfiniteProposition43
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

/-! ### Proposition 4.3, and a third refuted transcription

**This statement used to assert that every *individual* approximation number of
the squared full displacement is minimised by the direct rotation, and in that
form it is FALSE.**  Recorded here with the counterexample, because it is the
obvious reading of the printed proposition and because the repository already
contains the configuration that kills it.

Proposition 4.3 is about a *unitarily invariant norm* of `(1−V*)(1−V)`.  For a
Ky Fan norm that is a partial sum `∑_{n<k} aₙ`, so pointwise domination of the
`aₙ` would imply it — and would also imply Proposition 4.4, which the repository
**refutes** (`shortRotation_fullDisplacement_refuted`, census row DK-4.4-prop).
So pointwise domination cannot hold, and the refuting configuration is the same
equal-angle multiplicity mixing.

Explicitly, in `ℝ⁴` take `U = span(e₁, e₂)` and `V` at principal angles
`π/4, π/4` — acute, since `‖P_U − P_V‖ = sin(π/4) < 1`.  Let `W` carry `U` onto
`V` by a quarter turn in the `V`-frame and `Uᗮ` onto `Vᗮ` by the identity; it is
orthogonal and satisfies `W P_U = P_V W`.  Then

* `aₙ(1 − D) = (0.765367, 0.765367, 0.765367, 0.765367)` — four equal values
  `2 sin(π/8)`, one per principal direction;
* `aₙ(1 − W) = (1.586707, 1.586707, 0.261052, 0.261052)`;

so at `n = 2` the competitor is **strictly smaller**, and squaring preserves
that: `aₙ((1−D)*(1−D))` is `0.585786` at `n = 2` against the competitor's
`0.068148`.

Proposition 4.3 itself is untouched: its Ky Fan sums of *squares* are
`(0.586, 1.172, 1.757, 2.343)` for the direct rotation against
`(2.518, 5.035, 5.103, 5.172)` for the competitor, dominated at every `k`.  Sums
of squares and sums behave differently, which is exactly why 4.3 survives while
4.4 does not.

The statement below is therefore at Ky Fan level, which is what a unitarily
invariant norm sees.  **It is proved**, in
`MathAhead/Section4/InfiniteProposition43.lean`.  The finite-dimensional proof
(`directRotation_displacementSquare_uiNorm`) diagonalizes and applies
Fan--Hoffman to the pinched competitor; that route does not survive to infinite
dimensions, where `2 − 2C` need not be compact and has no eigenvalue list.  The
replacement chains

```
kyFan_k(2 − 2C) = kyFan_k(D's block sum) ≤ kyFan_k(W's block sum)
                = kyFan_k(pinch((1−W)†(1−W))) ≤ kyFan_k((1−W)†(1−W)),
```

reading the pinch through the isometry `H ≃ₗᵢ WithLp 2 (U × Uᗮ)`, feeding the
middle step with Proposition 4.1 on `U` and on `Uᗮ`, and closing with the
Fan--Hoffman pinching contraction.  Two facts carry it: the complementary pair
has the *same* direct rotation, and `aₙ(X†X) = aₙ(X)²` — which is also exactly
why 4.3 survives while 4.4 does not, since sums of squares are dominated at
every `k` and sums are not. -/
theorem proposition4_3_squaredDisplacement_kyFan
    (hacute : IsAcute U V) (W : H →L[ℂ] H)
    (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * projection U = projection V * W)
    (k : ℕ) :
    kyFanApproximationGauge k
        ((1 - star (spectraDirectRotation U V hacute)) *
          (1 - spectraDirectRotation U V hacute)) ≤
      kyFanApproximationGauge k ((1 - star W) * (1 - W)) :=
  MathAhead.Section4.proposition4_3_squaredDisplacement_kyFan_scratch U V hacute W
    hWunitary hWmap k

end Section4
end Frontier
end Experimental
end DavisKahan
end TauCeti