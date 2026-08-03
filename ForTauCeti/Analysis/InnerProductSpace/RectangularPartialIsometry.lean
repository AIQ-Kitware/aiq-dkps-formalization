/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti, roadmap topic `HilbertSpaceOperatorFoundations`.  Mathlib is
not the destination (`ForTauCeti/README.md`); on the closed Mathlib track this
would have gone to `Mathlib/Analysis/InnerProductSpace/`, beside the polar
decomposition.

Formalized by Claude Opus 5 (claude-opus-5[1m]).
-/
import ForTauCeti.Analysis.InnerProductSpace.PartialIsometry

/-!
# Partial isometries between different spaces

`ForTauCeti.Analysis.InnerProductSpace.PartialIsometry` defines a partial isometry
algebraically, as `u * star u * u = u` in a `Monoid` with `StarMul`.  That is the right
definition when it applies, and it makes `IsPartialIsometry.star_star` and the
initial-projection identity fall out of star-monoid algebra.

**It does not apply to a map between different spaces.**  `u : E →ₗ[𝕜] F` has no `star`
and lives in no monoid: `star u` would be an `F →ₗ[𝕜] E`, and there is no
multiplication carrying both.  The rectangular case has to be written with `adjoint`
and `∘ₗ` directly, which is what this file does:

* `LinearMap.IsPartialIsometry` — `u ∘ₗ u.adjoint ∘ₗ u = u`, for `u : E →ₗ[𝕜] F`;
* `LinearMap.isPartialIsometry_iff_starMul` — on endomorphisms the two agree, so
  nothing is forked and every star-monoid lemma remains available;
* `LinearMap.IsPartialIsometry.adjoint` — the class is closed under adjoint, the
  rectangular counterpart of `IsPartialIsometry.star_star`.

**Why the agreement theorem matters more than it looks.**  Two predicates of the same
name, one general and one carrier-specific, is exactly the shape that produces a
library where half the lemmas apply to a given operator and nobody can tell which
half.  `isPartialIsometry_iff_starMul` is what keeps that from happening: on `E →ₗ[𝕜] E`
the two are interchangeable, so the rectangular definition is a *generalization* rather
than a competitor.  The proof is the associativity difference and nothing else --
`u * star u * u` brackets to the left and `u ∘ₗ u.adjoint ∘ₗ u` to the right.

The polar decomposition is the consumer: `M = W |M|` with `W` a partial isometry needs
exactly this predicate when `M` is rectangular, since `W` maps `E` to `F`.
-/

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **Partial isometry between possibly different spaces**: `u ∘ₗ u.adjoint ∘ₗ u = u`.

This is the Moore--Penrose-style identity that the algebraic `u * star u * u = u`
becomes when source and target differ and no single carrier holds both `u` and its
adjoint. -/
def IsPartialIsometry (u : E →ₗ[𝕜] F) : Prop :=
  u ∘ₗ u.adjoint ∘ₗ u = u

/-- On endomorphisms the carrier-specific and star-monoid predicates agree.

The only content is bracketing: `_root_.IsPartialIsometry` reads `u * star u * u = u`,
which is `(u * star u) * u = u`, while `LinearMap.IsPartialIsometry` reads
`u ∘ₗ (u.adjoint ∘ₗ u) = u`.  `star_eq_adjoint` identifies the involutions and
`Module.End.mul_eq_comp` the products. -/
theorem isPartialIsometry_iff_starMul {u : E →ₗ[𝕜] E} :
    u.IsPartialIsometry ↔ _root_.IsPartialIsometry u := by
  simp only [LinearMap.IsPartialIsometry, _root_.IsPartialIsometry, star_eq_adjoint,
    Module.End.mul_eq_comp, LinearMap.comp_assoc]

/-- Partial isometries are closed under adjoint, in the rectangular setting.

The rectangular counterpart of `IsPartialIsometry.star_star`, and it cannot be obtained
from that lemma: `u.adjoint` lives in `F →ₗ[𝕜] E`, a different space from `u`.  Taking
adjoints through `u ∘ₗ u.adjoint ∘ₗ u = u` reverses the composition and
`LinearMap.adjoint_adjoint` collapses the double adjoint, which lands exactly on the
statement. -/
theorem IsPartialIsometry.adjoint {u : E →ₗ[𝕜] F} (hu : u.IsPartialIsometry) :
    u.adjoint.IsPartialIsometry := by
  have h := congrArg LinearMap.adjoint hu
  unfold LinearMap.IsPartialIsometry
  simpa only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint, LinearMap.comp_assoc] using h

end LinearMap
