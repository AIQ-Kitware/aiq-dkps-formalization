/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Qwen 3.8
-/
module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Self-adjoint idempotents are contractions

A bounded endomorphism of a Hilbert space that is both idempotent and
self-adjoint in the C⋆-algebra `E →L[𝕜] E` is an orthogonal projection, and
orthogonal projections are nonexpansive.  This module records that standard
fact at its natural scalar generality (`RCLike 𝕜`).

The proof is pointwise and uses only the defining identities of the adjoint:

    ‖A x‖² = re⟪x, A x⟫ ≤ ‖x‖ ‖A x‖,

which forces `‖A x‖ ≤ ‖x‖` whenever `A x ≠ 0` and is trivial otherwise.  No
closed-range or orthogonal-complement machinery is involved, so the estimate
is cheap to appear inside downstream proof terms.

## Main results

* `ContinuousLinearMap.norm_selfAdjoint_idempotent_le_one`:
  `IsSelfAdjoint A` and `A * A = A` imply `‖A‖ ≤ 1`.

## Where it is used

Not currently used by any consumer in this repository; it is kept as a
reusable canonical fact of the C⋆-algebra `E →L[𝕜] E`.

The nearest consumer, the Davis--Kahan source-directed sine modulus
(`DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean`), does
bound `‖(1 − F₀ F₀*) E₀‖` for isometric coordinate maps, but it proves the
complementary factor by a pointwise Pythagorean argument on the residual
`a − F₀ (F₀* a)` rather than by reducing `1 − F₀ F₀*` to a self-adjoint
idempotent; the Pythagorean route references the adjoint through a single
identity, which keeps downstream proof terms lighter than the idempotent
route would.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: none.  The estimate first appeared inline in
  `DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean`
  (`norm_sourceDirectedSineModulus_le_one`), proved there through the
  closed-range submodule machinery of the complementary projection
  `V = range F₀`.
* Extraction class: **extracted and generalized** — the consumer bound is a
  specific complementary projection; this theorem is the operator-algebraic
  fact beneath it, stated for an arbitrary self-adjoint idempotent.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti`.
-/

public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **A self-adjoint idempotent is a contraction.**

If `A : E →L[𝕜] E` satisfies `A * A = A` and `A = A*`, then `A` is an
orthogonal projection and `‖A‖ ≤ 1`.  The proof is the standard pointwise
inner-product argument; it uses no closed-range or orthogonal-complement
machinery, which is what makes it cheap enough to appear inside downstream
kernel proof terms. -/
theorem norm_selfAdjoint_idempotent_le_one (A : E →L[𝕜] E)
    (hA : IsSelfAdjoint A) (hA2 : IsIdempotentElem A) : ‖A‖ ≤ 1 := by
  refine A.opNorm_le_bound zero_le_one fun x => ?_
  by_cases hax : ‖A x‖ = 0
  · rw [hax]
    simp
  · have hP : A ∘L A = A := by
      change IsIdempotentElem A
      exact hA2
    have hadj : A.adjoint = A := by
      change IsSelfAdjoint A
      exact hA
    have hsq : ‖A x‖ ^ 2 = RCLike.re (⟪x, A x⟫_𝕜) := by
      rw [norm_sq_eq_re_inner (𝕜 := 𝕜) (A x), ← A.adjoint_inner_right x (A x), hadj,
          ← comp_apply, hP]
    have h1' : ‖A x‖ * ‖A x‖ ≤ ‖A x‖ * ‖x‖ := by
      rw [mul_comm (‖A x‖) (‖x‖), ← pow_two, hsq]
      exact re_inner_le_norm x (A x)
    have hapos : 0 < ‖A x‖ := by
      rw [norm_pos_iff]
      intro h0
      exact hax (by rw [h0, norm_zero])
    simpa using le_of_mul_le_mul_left h1' hapos

end ContinuousLinearMap

end
