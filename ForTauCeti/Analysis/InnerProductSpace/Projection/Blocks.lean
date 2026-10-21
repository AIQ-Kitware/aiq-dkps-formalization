/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.ReducingSubspace
public import TauCeti.Analysis.InnerProductSpace.Projection.Block

/-!
# Projection blocks and reflections

General `RCLike` block decomposition relative to an orthogonally complemented
subspace.  This module is independent of the Davis--Kahan theory.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForMathlib` at Davis--Kahan commit
  `df036cd`; the canonical diagonal and off-diagonal block operators have since
  been upstreamed to `TauCeti.Analysis.InnerProductSpace.Projection.Block`.
* Extraction class: **partially upstreamed** — this module now contains only
  donor-specific consequences and the reflection-operator adapter; it uses
  Tau Ceti's canonical `diagBlock` and `offDiagBlock` definitions.
* Original authors / copyright: Jon Crall, GPT 5.6 High; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti` (enforced by `scripts/check_dependency_layers.py`).
-/

public section


open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Submodule

/-- **Equal subspaces have the same orthogonal projection.**

`HasOrthogonalProjection` is a `Prop` class, so once the subspaces are identified
the two instance arguments coincide by proof irrelevance.  This is needed
wherever a spectral development names one subspace two ways -- the range selected
by a complement set and the orthogonal complement of the range, say -- because
`rw` on the subspace itself produces an ill-typed motive: `starProjection` takes
an instance derived from the subspace being rewritten. -/
theorem starProjection_congr {p q : Submodule 𝕜 E}
    [p.HasOrthogonalProjection] [q.HasOrthogonalProjection] (h : p = q) :
    p.starProjection = q.starProjection := by
  subst h; rfl

/-- Pointwise form of `Submodule.starProjection_congr`, for rewriting under an
application. -/
theorem starProjection_congr_apply {p q : Submodule 𝕜 E}
    [p.HasOrthogonalProjection] [q.HasOrthogonalProjection] (h : p = q) (x : E) :
    p.starProjection x = q.starProjection x := by
  rw [starProjection_congr h]

/-- Reflection through an orthogonally complemented subspace. -/
noncomputable def reflectionOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : E →L[𝕜] E :=
  U.reflection.toLinearIsometry.toContinuousLinearMap

/-- The operator has vanishing diagonal blocks relative to `U`. -/
def IsOffDiagonal (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) : Prop := U.diagBlock A = 0

/-- The off-diagonal part as the diagonal-part defect. -/
theorem offDiagBlock_eq_sub_diagBlock (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) : U.offDiagBlock A = A - U.diagBlock A := by
  have h := U.diagBlock_add_offDiagBlock A
  calc
    U.offDiagBlock A = (U.diagBlock A + U.offDiagBlock A) - U.diagBlock A := by abel
    _ = A - U.diagBlock A := by rw [h]

/-- Pointwise form of the diagonal part. -/
theorem diagBlock_apply (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) (x : E) :
    U.diagBlock A x =
      U.starProjection (A (U.starProjection x)) +
        Uᗮ.starProjection (A (Uᗮ.starProjection x)) := by
  rw [Submodule.diagBlock_def]
  simp only [add_apply, ContinuousLinearMap.comp_apply]

/-- Pointwise form of the off-diagonal part. -/
theorem offDiagBlock_apply (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) (x : E) :
    U.offDiagBlock A x = A x - U.diagBlock A x := by
  rw [offDiagBlock_eq_sub_diagBlock]
  simp only [sub_apply]

/-- Pointwise formula for reflection. -/
@[simp]
theorem reflectionOperator_apply (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (x : E) :
    U.reflectionOperator x = (2 : 𝕜) • U.starProjection x - x := by
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change U.reflection x = (2 : 𝕜) • U.starProjection x - x
  rw [Submodule.reflection_apply, ← Nat.cast_smul_eq_nsmul 𝕜]
  norm_num

/-- **Reflection fixes the subspace it reflects through.**

The pointwise formula gives `2 • P x - x`, which is `x` exactly on `U`.  Stated
separately because the useful form is the fixed-point one: a compression whose
input is restricted to `U` does not see the reflection at all. -/
theorem reflectionOperator_apply_of_mem (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] {x : E} (hx : x ∈ U) :
    U.reflectionOperator x = x := by
  change U.reflection x = x
  exact Submodule.reflection_mem_subspace_eq_self hx

/-- The bundled reflection operator is Mathlib's `Submodule.reflection`.  Stated
because `reflectionOperator` is not exposed across module boundaries, so a
consumer that needs the `LinearIsometryEquiv` -- to feed a naturality theorem
that quantifies over unitaries, say -- cannot see that the two agree. -/
theorem reflectionOperator_apply_eq_reflection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (x : E) :
    U.reflectionOperator x = U.reflection x := by
  change U.reflection x = U.reflection x
  rfl

/-- Reflection is involutive. -/
theorem reflectionOperator_involutive (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    U.reflectionOperator ∘L U.reflectionOperator =
      ContinuousLinearMap.id 𝕜 E := by
  ext x
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change U.reflection (U.reflection x) = x
  exact U.reflection_reflection x

/-- **The reflection in operator form**: `J_U = 2 P_U - I`.

The pointwise formula `reflectionOperator_apply` is what `simp` uses, but the
two-projection algebra needs the operator identity, so that products of two
reflections can be expanded by ring normalisation rather than by chasing
vectors. -/
theorem reflectionOperator_eq_two_smul_sub_id (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    U.reflectionOperator =
      (2 : 𝕜) • U.starProjection - ContinuousLinearMap.id 𝕜 E := by
  ext x
  simp

/-- Reflection preserves norms. -/
theorem reflectionOperator_norm_map (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (x : E) :
    ‖U.reflectionOperator x‖ = ‖x‖ := by
  -- names the application so the norm bound applies to it directly.
  change ‖U.reflection x‖ = ‖x‖
  exact U.reflection.norm_map x

/-- Reflection is onto. -/
theorem reflectionOperator_surjective (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : Function.Surjective U.reflectionOperator := by
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change Function.Surjective U.reflection
  exact U.reflection.surjective

/-- Reflection has operator norm at most one. -/
theorem norm_reflectionOperator_le_one (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : ‖U.reflectionOperator‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  -- names the application so the norm bound applies to it directly.
  change ‖U.reflection x‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using le_of_eq (U.reflection.norm_map x)

/-- A reducing operator commutes with the corresponding reflection. -/
theorem reflectionOperator_comm_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : A.Reduces U) :
    U.reflectionOperator ∘L A = A ∘L U.reflectionOperator := by
  ext x
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change U.reflectionOperator (A x) = A (U.reflectionOperator x)
  rw [reflectionOperator_apply, reflectionOperator_apply,
    ContinuousLinearMap.starProjection_apply_comm_of_reduces A U hU,
    map_sub, map_smul]

/-- Complementary projection as `I-P`, pointwise. -/
@[simp]
theorem starProjection_orthogonal_apply (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (x : E) :
    Uᗮ.starProjection x = x - U.starProjection x := by
  rw [Submodule.starProjection_orthogonal]
  simp

/-! ### Numerical range of a block-diagonal operator

An operator that commutes with the reflection is determined block by block, and
so is its numerical range: the quadratic form splits as a *sum* over `U` and
`Uᗮ` with no cross term.  Consequently a sign condition tested separately on the
two summands propagates to the whole space.  This is the mechanism by which
"the diagonal blocks are positive" upgrades to "the numerical range is
nonnegative"; it is what the two-projection literature uses to characterise the
direct rotation among unitary square roots of the reflection product, and it is
about projections only. -/

/-- **The quadratic form of the diagonal pinch splits along `U ⊕ Uᗮ`.**

`⟪(P A P + P' A P') x, x⟫ = ⟪A (P x), P x⟫ + ⟪A (P' x), P' x⟫`, each pinch term
read off on its own summand.  No hypothesis on `A`: the pinch is *defined* to
discard the cross terms, and this identity says what survives. -/
theorem inner_diagBlock_apply_self (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (A : E →L[𝕜] E) (x : E) :
    ⟪U.diagBlock A x, x⟫_𝕜 =
      ⟪A (U.starProjection x), U.starProjection x⟫_𝕜 +
        ⟪A (Uᗮ.starProjection x), Uᗮ.starProjection x⟫_𝕜 := by
  simp only [Submodule.diagBlock_def, add_apply, ContinuousLinearMap.comp_apply,
    inner_add_left, inner_starProjection_left_eq_right]

/-- **Commuting with the reflection is the same as being block diagonal.**

`J A J = A` forces `A` to equal its own diagonal pinch.  Immediate from
`two_smul_diagBlock`, which says
`2 (P A P + P' A P') = A + J A J`. -/
theorem diagBlock_eq_self_of_reflectionConjugate (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] {A : E →L[𝕜] E}
    (hA : (U.reflection : E →L[𝕜] E) ∘L A ∘L (U.reflection : E →L[𝕜] E) = A) :
    U.diagBlock A = A := by
  let J : E →L[𝕜] E := U.reflection
  have hJ : J * J = 1 := by
    ext x
    change U.reflection (U.reflection x) = x
    exact U.reflection_reflection x
  have hA' : J * A * J = A := by
    change U.reflection ∘L A ∘L U.reflection = A
    exact hA
  have hcomm : Commute J A := by
    rw [commute_iff_eq]
    calc
      J * A = J * A * (J * J) := by rw [hJ, mul_one]
      _ = (J * A * J) * J := by noncomm_ring
      _ = A * J := by rw [hA']
  apply U.diagBlock_eq_self_iff.mpr
  exact U.commute_reflection_iff.mp (by simpa only [J] using hcomm)

/-- **A block-diagonal operator with nonnegative blocks has nonnegative
numerical range.**

The hypotheses only constrain `A` on `U` and on `Uᗮ` separately, which for a
general operator says nothing about a mixed vector; commuting with the
reflection is exactly what removes the cross term. -/
theorem re_inner_apply_self_nonneg_of_reflectionConjugate (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] {A : E →L[𝕜] E}
    (hA : U.reflectionOperator ∘L A ∘L U.reflectionOperator = A)
    (hU : ∀ x ∈ U, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUperp : ∀ x ∈ Uᗮ, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜) (x : E) :
    0 ≤ RCLike.re ⟪A x, x⟫_𝕜 := by
  have hdiag := diagBlock_eq_self_of_reflectionConjugate U hA
  have hsplit := inner_diagBlock_apply_self U A x
  rw [hdiag] at hsplit
  rw [hsplit, map_add]
  exact add_nonneg (hU _ (U.starProjection_apply_mem x))
    (hUperp _ (Uᗮ.starProjection_apply_mem x))

end Submodule

