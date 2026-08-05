/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric
import DavisKahan.Sylvester.Unbounded.OrderedEngineDirect

/-!
# Davis--Kahan 1970, Section 5: the cutoff lemma and the ordered Sylvester theorem

Source-numbered names for Section 5.  Both results are already compiled, in a form more
general than the paper's; this file supplies the paper's numbering so the facade can cite
them, and records in each docstring exactly *how* the compiled statement is more general,
so nothing is silently overstated.

Theorem 5.2 is a hard prerequisite for the Section 2 unbounded-scope claim, which names it
as one of its two halves.
-/

namespace TauCeti
namespace DavisKahan1970

/-- **Davis--Kahan 1970, Lemma 5.1.**  If a net of orthogonal projections converges
strongly to the identity, then each approximation singular value of `K ∘ P i` converges to
the corresponding one of `K`.

Stronger than the printed lemma in two ways, both deliberate: the index is an arbitrary
filtered net rather than a sequence, and the scalar field is generic rather than complex
(the strong-cutoff hypothesis is carried as the class
`HasApproximationNumberStrongCutoff`).  The paper's statement is the specialization to a
sequence over `ℂ`. -/
alias Lemma5_1 :=
  DavisKahan.Experimental.ExactSinTheta.approximationSingularValue_comp_strongProjection_tendsto

/-- **Davis--Kahan 1970, Theorem 5.2.**  For self-adjoint closed operators with the
source's ordering `A ≥ c + δ > c ≥ B`, a bounded solution of the Sylvester equation
`A X = X B + R` satisfies the sharp inequality `δ · N(X) ≤ N(R)` in every Fan-dominant
unitarily invariant ideal gauge, and `X` lies in the ideal whenever `R` does.

The ordering is the paper's: `SemiboundedBelow A (c + δ)` and `SemiboundedAbove B c`.  The
constant `δ` is sharp.  More general than the printed theorem in the scalar-ideal axis --
the conclusion is for an arbitrary `KyFanDominantIdealFamily`, not just a fixed unitarily
invariant norm -- and the operators are unbounded closed self-adjoint rather than bounded.

This is the *ordered* branch.  The interval/exterior separation hypothesis is a different
theorem, `unbounded_sylvester_intervalExterior_uiNorm_genuineSpectrum`; do not substitute
one for the other. -/
alias Theorem5_2 :=
  DavisKahan.Experimental.ExactSinTheta.directOrderedSylvesterEngine_lowerUpper

end DavisKahan1970
end TauCeti
