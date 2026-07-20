/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Experimental.InfiniteDimensional.DirectRotation
import DavisKahan.SpectralTheory.ClosedOperator.Basic

/-!
# Open obligations of the closed-operator interface

The proved part of the interface now lives in
`DavisKahan.SpectralTheory.ClosedOperator.Basic`.  This module retains only the
declarations that are still unresolved, so that the admission closure stays
confined here.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace
open Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

namespace ClosedOperator

/-- Adjoint of a densely defined closed operator.  The implementation should
be reconciled with mathlib's partial-linear-map adjoint API.

Construction route: define the domain as vectors `y` for which
`x ↦ ⟪A x, y⟫` is ambient-norm bounded on the dense domain, use Riesz
representation for the representing vector, and prove the resulting graph is
closed. -/
noncomputable def adjoint
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) :
    ClosedOperator (𝕜 := 𝕜) (E := E) := by
  sorry

/-- Sum with a relatively bounded operator on the same domain.

The relative-bound hypotheses are part of the constructor because an arbitrary
linear perturbation on `A.domain` need not have closed graph. -/
noncomputable def addRelative
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (V : A.domain →ₗ[𝕜] E) {a b : ℝ}
    (ha : 0 ≤ a) (hb0 : 0 ≤ b)
    (hrel : RelativelyBounded A V a b) (hb : b < 1) :
    ClosedOperator (𝕜 := 𝕜) (E := E) := by
  sorry

/-- Unbounded spectral projection. -/
noncomputable def spectralProjection
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (s : Set ℝ) : E →L[𝕜] E := by
  sorry

/-- Kato--Rellich theorem for bounded perturbations.

Lean proof route for a weaker agent:

1. Show the bounded sum has the same dense domain and closed graph as `A` by graph-norm equivalence.
2. Prove symmetry using `hA` and `hV`.
3. Apply bounded Kato--Rellich, or factor the nonreal resolvent and use a Neumann series for sufficiently large imaginary part.
4. Use the adjoint/resolvent characterization to prove equality with the Hilbert-space adjoint.


Ext-agent signature audit (GPT 5.6 High): Correct Kato--Rellich bounded-perturbation
target. It depends on the genuine adjoint equality, not maximal symmetry.

Preferred dependency route: Reconcile `ClosedOperator` with a genuine partial-operator
adjoint/resolvent API before attempting Kato--Rellich or unbounded spectral projection
arguments.
-/
theorem isSelfAdjoint_addBounded
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (V : E →L[𝕜] E)
    (hV : IsSelfAdjointOperator V) :
    (A.addBounded V).IsSelfAdjoint := by
  sorry

/-- Kato--Rellich theorem for relatively bounded perturbations with relative
bound below one.

Proof strategy: equip the common domain with the graph norm of `A`.  Relative
boundedness with coefficient below one makes the perturbed graph norm
equivalent to the original graph norm, so `A+B` is closed.  Prove surjectivity
of `A+B-z` for one nonreal `z` by factoring

`A+B-z = (I + B(A-z)⁻¹)(A-z)`

and applying a Neumann series after choosing `|Im z|` large enough.  Symmetry
plus surjectivity at `z` and `conj z` yields self-adjointness.  Reconcile the
local `ClosedOperator` structure with mathlib's partial-map adjoint API before
attempting this proof.

Lean proof route for a weaker agent:

1. Use `ha`, `hb0`, `hrel`, and `hb<1` to prove equivalence of the graph norms of `A` and `A+V`.
2. Deduce closedness and density of the perturbed operator and use `hV` for symmetry.
3. Choose a nonreal spectral parameter with small `V(A-z)⁻¹` norm and invert by Neumann series.
4. Use the standard resolvent criterion for self-adjointness.


Ext-agent signature audit (GPT 5.6 High): Correct after `addRelative` was made to carry
nonnegative relative-bound parameters and a bound below one. The symmetry hypothesis on
`V` remains essential.

Preferred dependency route: Reconcile `ClosedOperator` with a genuine partial-operator
adjoint/resolvent API before attempting Kato--Rellich or unbounded spectral projection
arguments.
-/
theorem isSelfAdjoint_of_relativelyBounded
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (V : A.domain →ₗ[𝕜] E)
    (hV : ∀ x y : A.domain,
      ⟪V x, (y : E)⟫_𝕜 = ⟪(x : E), V y⟫_𝕜)
    {a b : ℝ} (ha : 0 ≤ a) (hb0 : 0 ≤ b)
    (hrel : RelativelyBounded A V a b) (hb : b < 1) :
    (A.addRelative V ha hb0 hrel hb).IsSelfAdjoint := by
  sorry

/-- Unbounded-operator `sin Θ` theorem with bounded difference.

Lean proof route for a weaker agent:

1. Use the unbounded spectral theorem to form the two spectral projections.
2. Derive the weak Sylvester equation between their ranges on `dom A`; the bounded perturbation supplies the residual.
3. Apply the unbounded general separated-spectrum Sylvester estimate in both directions using `hsepAB,hsepBA`.
4. Recombine the directed bounds and retain the universal `π/2` constant. Add a separate interval/exterior corollary for constant one.


Ext-agent signature audit (GPT 5.6 High): Corrected to the generic `π/2` constant for
arbitrary separated spectral sets. Both mixed gaps are still needed for the full
projection difference; a later interval/exterior theorem should recover constant one.

Preferred dependency route: Reconcile `ClosedOperator` with a genuine partial-operator
adjoint/resolvent API before attempting Kato--Rellich or unbounded spectral projection
arguments.
-/
theorem sinTheta_unbounded_boundedPerturbation
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (V : E →L[𝕜] E)
    (hV : IsSelfAdjointOperator V) (s t : Set ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    {d : ℝ} (hd : 0 < d)
    (hsepAB : SpectralSetsSeparated A (A.addBounded V) s tᶜ d)
    (hsepBA : SpectralSetsSeparated (A.addBounded V) A t sᶜ d) :
    d * ‖A.spectralProjection s - (A.addBounded V).spectralProjection t‖ ≤
      (Real.pi / 2) * ‖V‖ := by
  sorry
end ClosedOperator
end DavisKahanExt
end ForMathlib
