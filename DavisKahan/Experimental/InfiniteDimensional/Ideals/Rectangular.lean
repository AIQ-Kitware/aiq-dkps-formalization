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

namespace ForMathlib
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

Construction route: define membership by summability of `‖A e i‖ ^ 2` over a
Hilbert basis (basis independence via Parseval), the gauge as the square root
of that sum, adjoint invariance by the double-sum symmetry, ideal control by
termwise operator-norm bounds, and completeness by a diagonal argument.  The
required rectangular Hilbert--Schmidt theory over `RCLike` scalars is not yet
available in this development, the pinned Mathlib, or the pinned Spectra
checkout (Spectra's trace-class development is `ℂ`-only and square). -/
noncomputable def hilbertSchmidt :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) :=
  -- Open obligation (separate analytic campaign): the rectangular
  -- Hilbert-Schmidt family over RCLike scalars; handed to the mathematics agent.
  sorry

/-- Trace-class operators as a coherent rectangular family.

Construction route: define the trace gauge through the singular-value
sequence (equivalently `tr |A|`), with adjoint invariance from the shared
singular values of `A` and `A⋆`, ideal control from singular-value
domination, and completeness against the operator-norm limit.  The required
rectangular trace-class theory over `RCLike` scalars is not yet available in
this development, the pinned Mathlib, or the pinned Spectra checkout. -/
noncomputable def traceClass :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) :=
  -- Open obligation (separate analytic campaign): the rectangular trace-class
  -- family over RCLike scalars; handed to the mathematics agent.
  sorry

/-- Schatten `p` operators as a coherent rectangular family.

Construction route: apply the `ℓᵖ` gauge to the approximation-number
sequence; the triangle inequality is the Tomić--Weyl weak-majorization
argument, and completeness follows from Fatou against the operator-norm
limit.  The required Schatten theory is not yet available in this
development, the pinned Mathlib, or the pinned Spectra checkout. -/
noncomputable def schatten (p : ℝ) (hp : 1 ≤ p) :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) :=
  -- Open obligation (separate analytic campaign): the rectangular Schatten-p
  -- family over RCLike scalars; handed to the mathematics agent.
  sorry

/-- Ky Fan `k` gauges, with positive `k`, obtained from the already-proved
approximation-number family. -/
noncomputable def kyFan [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜]
    (k : ℕ) (hk : 0 < k) :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) :=
  (KyFanDominantIdealFamily.kyFan (𝕜 := 𝕜) k hk).toRectangularSymmetricIdealFamily

end RectangularSymmetricIdealFamily
end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
