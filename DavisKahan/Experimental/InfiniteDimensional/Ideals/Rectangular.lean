/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.OperatorIdeal.UnitarilyInvariant.RectangularFamily
import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-!
# Open obligations of the rectangular ideal families

The family structure and its proved theory now live in
`DavisKahan.OperatorIdeal.UnitarilyInvariant.RectangularFamily`.  The concrete
Hilbert-Schmidt, trace-class, and Schatten families remain unresolved
and stay here.  The Ky Fan family reuses the proved approximation-number package.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

namespace RectangularSymmetricIdealFamily

variable {𝕜 : Type u} [RCLike 𝕜]

/-- Compact operators equipped with the ordinary operator norm.

The adjoint-invariance field is Schauder's theorem for Hilbert-space
adjoints, which the pinned Mathlib does not yet provide; that single field
remains an open obligation. -/
noncomputable def compactOperatorNorm :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) :=
  -- Open obligation: the compact-operator family is complete save for adjoint
  -- invariance (Schauder's theorem, absent from pinned Mathlib) and the
  -- ideal/composition norm names; handed to the mathematics agent.
  sorry

/-- Hilbert--Schmidt operators as a coherent rectangular family.

**Status corrected 2026-07-29 — most of this is now done, and the one missing
piece is much smaller than the paragraph below used to claim.**

The family itself **exists and is `RCLike`-general**:
`TauCeti.hilbertSchmidtIdealFamily` in
`ForTauCeti/Analysis/OperatorIdeal/Family/HilbertSchmidt.lean` supplies
membership, the gauge, adjoint invariance and the ideal bounds.

What blocks filling this slot is a **single** obligation: `toRectangular`
requires `[N.toOperatorIdealFamily.IsComplete]`, and that instance does not
exist for the Hilbert--Schmidt family.  Substituting the staged family fails
with `failed to synthesize (hilbertSchmidtIdealFamily 𝕜).IsComplete`.

That obligation will **not** fall out the way `kyFan`'s did.  `kyFanIdealFamily`
gets completeness from the two-sided comparison `‖A‖ ≤ ∑_{n<k} aₙ(A) ≤ k ‖A‖` —
that is, because the Ky Fan gauge is *equivalent to the operator norm*.  The
Hilbert--Schmidt gauge is not, so the diagonal argument really is needed.

Original note, retained for the construction route it describes: membership by
summability of `‖A eᵢ‖²` over a Hilbert basis (basis independence via Parseval),
the gauge as the square root of that sum, adjoint invariance by the double-sum
symmetry, ideal control by termwise operator-norm bounds, and completeness by a
diagonal argument. -/
noncomputable def hilbertSchmidt :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) :=
  -- Open obligation (separate analytic campaign): the rectangular
  -- Hilbert-Schmidt family over RCLike scalars; handed to the mathematics agent.
  sorry

/-- Trace-class operators as a coherent rectangular family.

**Status corrected 2026-07-30.**  The sentence this docstring used to end
with — "the required rectangular trace-class theory over `RCLike` scalars is
not yet available in this development" — is no longer true as written.
`TauCeti.traceClassIdealFamily` exists, in
`ForTauCeti/Analysis/OperatorIdeal/Family/TraceClass.lean`, with the gauge
`nuclearENorm`, adjoint invariance, and the ideal bounds all supplied.

**Status corrected again 2026-07-31: the first of the two remaining gaps is
closed.**  `traceClassIdealFamily` is now
`(𝕜 : Type) [RCLike 𝕜] [HasMinMaxLowerBoundEverywhere.{0, v} 𝕜] :
SymmetricOperatorIdealFamily.{0, v} 𝕜`, with instances of that class for both
`ℝ` and `ℂ`, so it fits an `RCLike`-general slot.  What made it `ℂ`-only was
never `nuclearENorm`, which never mentions the field; it was the Ky Fan
triangle inequality one layer down, and that now holds over any field with a
min--max lower bound.

One thing is still missing:

* `toRectangular` wants `[N.toOperatorIdealFamily.IsComplete]`, and as with
  `hilbertSchmidt` above that instance does not exist — and for the same
  reason, since the trace norm is not equivalent to the operator norm, so the
  `kyFan` route to completeness does not transfer.  Note that `hilbertSchmidt`'s
  half of this *was* proved on 2026-07-31; the trace-class half is open, and its
  gauge is a supremum of Ky Fan gauges rather than a `tsum`, so the Fatou input
  is not the same one.

Construction route, retained: define the trace gauge through the singular-value
sequence (equivalently `tr |A|`), with adjoint invariance from the shared
singular values of `A` and `A⋆`, ideal control from singular-value
domination, and completeness against the operator-norm limit. -/
noncomputable def traceClass :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) :=
  -- Open obligation (separate analytic campaign): the rectangular trace-class
  -- family over RCLike scalars; handed to the mathematics agent.
  sorry

/-- Schatten `p` operators as a coherent rectangular family.

**Status corrected 2026-07-30**, though less than for `traceClass` above.
`ForTauCeti/Analysis/InnerProductSpace/SchattenNorm.lean` supplies the Schatten
`p` gauge over general `RCLike` scalars, as a
`RectangularUnitarilyInvariantNorm`, with the triangle inequality already
factored exactly the way the route below describes — Ky Fan subadditivity plus
`ℓᵖ` monotonicity under weak majorization.  What it does **not** supply is the
infinite-dimensional case: it is stated for finite-dimensional `E` and `F` and
indexes by `min (finrank E) (finrank F)`.

So the remaining work is the extension from a finite-dimensional
unitarily-invariant norm to an operator ideal, not the Schatten theory itself.

Construction route, retained: apply the `ℓᵖ` gauge to the approximation-number
sequence; the triangle inequality is the Tomić--Weyl weak-majorization
argument, and completeness follows from Fatou against the operator-norm
limit. -/
noncomputable def schatten (p : ℝ) (hp : 1 ≤ p) :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) :=
  -- Open obligation (separate analytic campaign): the rectangular Schatten-p
  -- family over RCLike scalars; handed to the mathematics agent.
  sorry

/-- Ky Fan `k` gauges, with positive `k`, obtained from the already-proved
approximation-number family. -/
noncomputable def kyFan [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
    (k : ℕ) (hk : 0 < k) :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) :=
  (KyFanDominantIdealFamily.kyFan (𝕜 := 𝕜) k hk).toRectangularSymmetricIdealFamily

end RectangularSymmetricIdealFamily
end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti