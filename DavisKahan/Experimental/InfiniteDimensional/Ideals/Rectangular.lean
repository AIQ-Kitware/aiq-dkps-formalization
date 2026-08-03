/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.OperatorIdeal.UnitarilyInvariant.RectangularFamily
import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric
import ForTauCeti.Analysis.OperatorIdeal.Family.HilbertSchmidt
import ForTauCeti.Analysis.OperatorIdeal.Family.Schatten

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

**The Schauder obligation is discharged** (2026-08-02).  This docstring used to say
the adjoint-invariance field was blocked on "Schauder's theorem for Hilbert-space
adjoints, which the pinned Mathlib does not yet provide".  It is now proved, as
`ContinuousLinearMap.isCompactOperator_adjoint` in
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Adjoint.lean`, and cheaply:
compactness on a complete Hilbert target *is* the vanishing of the approximation
numbers, and those are adjoint-invariant, so the two operators have the same
sequence.

What is left is not mathematics.  `RectangularSymmetricIdealFamily` is the legacy
record that `RECT-DELETE` is retiring, and this row is one of its remaining
catalogue slots; filling in a dozen fields of a type slated for deletion is work
that the deletion would immediately discard.  When a canonical compact-operator
family is wanted, build it against the current `SymmetricOperatorIdealFamily` and
take `adjoint_mem` from the theorem above. -/
noncomputable def compactOperatorNorm :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) :=
  sorry

/-- Hilbert--Schmidt operators as a coherent rectangular family.

**Closed 2026-07-31.**  This is `TauCeti.hilbertSchmidtIdealFamily` read through
`toRectangular`, and no mathematics is restated here.

The history is worth one paragraph, because the docstring was right and stayed
right while the obstacle moved.  On 2026-07-29 it was corrected from *"the
required theory is not yet available"* to a **single** named obligation:
`toRectangular` wants `[N.toOperatorIdealFamily.IsComplete]` and the
Hilbert--Schmidt family had no such instance.  It also predicted that the
obligation would not fall out the way `kyFan`'s did -- `kyFanIdealFamily` gets
completeness from `‖A‖ ≤ ∑_{n<k} aₙ(A) ≤ k ‖A‖`, i.e. from the gauge being
*equivalent* to the operator norm, which the Hilbert--Schmidt gauge is not.

That prediction held exactly.  `isComplete_hilbertSchmidtIdealFamily` is proved
by lower semicontinuity of the gauge along pointwise convergence on a basis,
which is Fatou against the counting measure -- a genuinely different argument,
as the docstring said it would have to be. -/
noncomputable def hilbertSchmidt :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) :=
  (TauCeti.hilbertSchmidtIdealFamily.{u, v} 𝕜).toRectangular

/-- Trace-class operators as a coherent rectangular family.

**Closed 2026-07-31.**  This is `TauCeti.traceClassIdealFamily` read through
`toRectangular`; no mathematics is restated here.

Both of the obligations this docstring named on 2026-07-30 are discharged, and
they turned out to be one obligation apart rather than two of a kind.  The
`RCLike` generalisation was never about `nuclearENorm`, which does not mention
the scalar field: it was the Ky Fan triangle inequality one layer below, and
that now holds over any field with a min--max lower bound.  Completeness is
lower semicontinuity of the gauge, which follows from each approximation number
being `1`-Lipschitz in the operator norm together with Fatou for `tsum`.

The construction route this docstring used to recommend -- the trace gauge
through the singular-value sequence -- is what `nuclearENorm` is, so the route
was right and only the estimate of what remained was wrong. -/
noncomputable def traceClass [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) :=
  (TauCeti.traceClassIdealFamily.{u, v} 𝕜).toRectangular

/-- Schatten `p` operators as a coherent rectangular family.

**Closed 2026-07-31.**  This is `TauCeti.schattenIdealFamily` read through
`toRectangular`.

The 2026-07-30 note said the missing piece was *"the extension from a
finite-dimensional unitarily-invariant norm to an operator ideal"*, and that is
exactly what was built -- but not the way that note expected.  It anticipated a
weak-majorization theory for infinite sequences, which does not exist in this
repository and was not written: the finite `Fin n` theory is applied to each
truncation of the approximation-number sequence, and the `tsum` is the supremum
of those truncations.

Completeness is the trace-class argument with the exponent carried through. -/
noncomputable def schatten [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
    {p : ℝ} (hp : 1 ≤ p) :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) :=
  (TauCeti.schattenIdealFamily.{u, v} 𝕜 hp).toRectangular

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