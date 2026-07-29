/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.OperatorModulus
public import ForTauCeti.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.Normed.Ring.Units

/-!
# The polar isometry of a bounded-below operator

For a bounded operator `M : E →L[ℂ] F` between complex Hilbert spaces whose
modulus `|M| = (M⋆ M)^(1/2)` is invertible, the **polar isometry**

    `M.polarIsometry = M ∘ |M|⁻¹`

is a genuine isometry `E → F` and satisfies the polar identity
`M.polarIsometry ∘L |M| = M`.  (Invertibility of `|M|` says exactly that `M` is
bounded below, i.e. that `M` is injective with closed range.  Without it, the
polar factor is only a *partial* isometry; the definition below then evaluates
to the junk value `0`, in the style of `Ring.inverse`.)

The point of isolating this object is quantitative.  From the polar identity,

    `M x - M.polarIsometry x = M.polarIsometry (|M| x - x)`,

so the isometry property turns the distance from `M` to the isometry
`M.polarIsometry` into the *scalar* problem of estimating `‖|M| - 1‖`.  That in
turn is bounded by `‖M⋆ M - 1‖` through the continuous functional calculus and
the elementary square-root contraction `|√μ - 1| ≤ |μ - 1|`
(`TauCeti.Real.abs_sqrt_sub_one_le_abs_sub_one`).  The resulting estimate

    `‖M - M.polarIsometry‖ ≤ ‖M⋆ M - 1‖`

is sharp: an operator whose Gram operator is `δ`-close to the identity is
`δ`-close to an isometry, with no loss in the constant and with no
finite-dimensionality assumption.

## Main results

* `ContinuousLinearMap.polarIsometry`: the canonical isometric polar factor;
* `ContinuousLinearMap.polarIsometry_comp_modulus`: the polar identity
  `W ∘L |M| = M`;
* `ContinuousLinearMap.norm_polarIsometry_apply`: `W` is an isometry;
* `ContinuousLinearMap.norm_modulus_sub_one_le`: the square-root contraction
  `‖|M| - 1‖ ≤ ‖M⋆ M - 1‖`, valid for *every* `M`;
* `ContinuousLinearMap.norm_sub_polarIsometry_le`: the sharp near-isometry
  estimate `‖M - W‖ ≤ ‖M⋆ M - 1‖`;
* `ContinuousLinearMap.polarLinearIsometry` and
  `ContinuousLinearMap.polarLinearIsometryEquiv`: the bundled forms, the latter
  under an explicit surjectivity hypothesis.

## Design notes

The definition is *total*: `polarIsometry M = M ∘L Ring.inverse |M|`, which is
`0` when `|M|` is not invertible.  Every theorem that uses the isometry property
carries `IsUnit M.modulus` explicitly, exactly as `Ring.inverse` lemmas carry
`IsUnit`.  This keeps `polarIsometry` a plain function of `M` — so it rewrites,
`simp`s, and composes — instead of a proof-dependent bundled object.

The general polar decomposition — with a *partial* isometry, defined for every
`M` and with no invertibility hypothesis — now exists, as
`ContinuousLinearMap.polarPartial` in
`ForTauCeti/Analysis/InnerProductSpace/PolarPartialIsometry.lean`; its
`polarPartial_comp_modulus` is the unconditional form of the identity below.

The reconciliation is **proved**:
`ContinuousLinearMap.polarPartial_eq_comp_ringInverse_modulus` says
`polarPartial M = M ∘L Ring.inverse M.modulus` whenever `|M|` is a unit, which
is `polarIsometry M` by definition.  So the two constructions agree exactly
where this one is meaningful, and this module is a specialisation rather than a
rival.

What is *not* done, and is deliberately left as its own lane: retiring this
definition outright.  That is more than a deletion, because the module also
carries results with nothing to do with polar decomposition — the two
criteria for `|M|` to be a unit, and the operator inequality
`‖|M| - 1‖ ≤ ‖M⋆M - 1‖` — which would have to be rehoused first.  The
bounded-below case is separated out here because it needs no
polar-decomposition theory at all: `Ring.inverse` plus the pointwise isometry
`‖|M| x‖ = ‖M x‖` suffice.

Complex scalars are required because Mathlib registers the continuous functional
calculus on Hilbert-space operators only over `ℂ`; see
`ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean`.

## References

* N. J. Higham, *Functions of Matrices: Theory and Computation*, SIAM, 2008,
  Ch. 8 (the unitary polar factor as the nearest isometry).

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **new**.  Written for the Tau Ceti signature-polish backlog
  (`dev/tauceti-signature-polish-todo.md` §8.2), which asked for the canonical
  polar factor behind the existential near-isometry statement in
  `ForTauCeti/Analysis/InnerProductSpace/NearIsometry.lean`.
* Spectra influence: **none** — this module imports only Mathlib and the
  Tau Ceti operator-modulus staging module.
-/

@[expose] public section

namespace ContinuousLinearMap

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The **polar isometry** `M ∘ |M|⁻¹` of an operator between complex Hilbert
spaces.

When the modulus `|M|` is invertible — equivalently, when `M` is bounded below —
this is an isometry `E → F` with `M.polarIsometry ∘L |M| = M`, the isometric
factor of the polar decomposition of `M`.  Otherwise `Ring.inverse` returns `0`
and so does this definition; every result below therefore carries the hypothesis
`IsUnit M.modulus`. -/
noncomputable def polarIsometry (M : E →L[ℂ] F) : E →L[ℂ] F :=
  M ∘L Ring.inverse M.modulus

theorem polarIsometry_apply (M : E →L[ℂ] F) (x : E) :
    M.polarIsometry x = M (Ring.inverse M.modulus x) := rfl

/-- The modulus of `M` is invertible exactly when the Gram operator `M⋆ M` is.

Both directions are the elementary fact that a self-commuting square is a unit
iff its root is: `|M| * |M| = M⋆ M` by `ContinuousLinearMap.modulus_mul_self`. -/
theorem isUnit_modulus_iff (M : E →L[ℂ] F) :
    IsUnit M.modulus ↔ IsUnit (M.adjoint ∘L M) := by
  rw [← M.modulus_mul_self, (Commute.refl M.modulus).isUnit_mul_iff, and_self]

/-- A Gram operator within distance `< 1` of the identity is invertible, hence so
is the modulus: an operator that is a near-isometry is bounded below. -/
theorem isUnit_modulus_of_norm_adjoint_comp_self_sub_one_lt_one {M : E →L[ℂ] F}
    (h : ‖M.adjoint ∘L M - 1‖ < 1) : IsUnit M.modulus := by
  rw [M.isUnit_modulus_iff]
  rw [show M.adjoint ∘L M = 1 - -(M.adjoint ∘L M - 1) by abel]
  exact isUnit_one_sub_of_norm_lt_one (by rwa [norm_neg])

section IsUnitModulus

variable {M : E →L[ℂ] F} (hM : IsUnit M.modulus)
include hM

/-- The **polar identity**: `M` factors as its polar isometry composed with its
modulus. -/
theorem polarIsometry_comp_modulus : M.polarIsometry ∘L M.modulus = M := by
  rw [polarIsometry, comp_assoc, ← mul_def, Ring.inverse_mul_cancel _ hM, one_def, comp_id]

theorem polarIsometry_modulus_apply (x : E) : M.polarIsometry (M.modulus x) = M x := by
  rw [← comp_apply, polarIsometry_comp_modulus hM]

/-- The polar isometry is a pointwise isometry.

Composing the pointwise identity `‖|M| y‖ = ‖M y‖`
(`ContinuousLinearMap.norm_modulus_apply`) with `y = |M|⁻¹ x` turns the
right-hand side into `‖M.polarIsometry x‖` and the left-hand side into
`‖x‖`. -/
@[simp]
theorem norm_polarIsometry_apply (x : E) : ‖M.polarIsometry x‖ = ‖x‖ := by
  rw [polarIsometry_apply, ← M.norm_modulus_apply, ← comp_apply, ← mul_def,
    Ring.mul_inverse_cancel _ hM, one_apply_eq_self]

theorem isometry_polarIsometry : Isometry M.polarIsometry :=
  AddMonoidHomClass.isometry_of_norm _ fun x => norm_polarIsometry_apply hM x

theorem polarIsometry_injective : Function.Injective M.polarIsometry :=
  (isometry_polarIsometry hM).injective

/-- **The near-isometry estimate, sharp form.**  The distance from `M` to its
polar isometry is controlled by the distance from the modulus to the identity.

This is an equality in disguise: `M x - M.polarIsometry x` is the image under the
isometry `M.polarIsometry` of `|M| x - x`, so the two sides even agree
pointwise before taking operator norms. -/
theorem norm_sub_polarIsometry_apply_eq (x : E) :
    ‖M x - M.polarIsometry x‖ = ‖M.modulus x - x‖ := by
  rw [← polarIsometry_modulus_apply hM x, ← map_sub, norm_polarIsometry_apply hM]

theorem norm_sub_polarIsometry_apply_le_norm_modulus_sub_one (x : E) :
    ‖M x - M.polarIsometry x‖ ≤ ‖M.modulus - 1‖ * ‖x‖ := by
  rw [norm_sub_polarIsometry_apply_eq hM x,
    show M.modulus x - x = (M.modulus - 1) x by simp]
  exact le_opNorm _ x

end IsUnitModulus

/-- **The square-root contraction.**  The modulus is at least as close to the
identity as the Gram operator is.  No hypothesis on `M`: for a non-invertible
modulus the statement is still true (and still proved by the calculus below).

Through the continuous functional calculus on the nonnegative operator
`a = M⋆ M`, both sides are `cfc` of a scalar function, and the estimate reduces
to `|√t - 1| ≤ |t - 1|` on the (nonnegative) spectrum of `a`. -/
theorem norm_modulus_sub_one_le (M : E →L[ℂ] F) :
    ‖M.modulus - 1‖ ≤ ‖M.adjoint ∘L M - 1‖ := by
  set a : E →L[ℂ] E := M.adjoint ∘L M with ha_def
  have ha : 0 ≤ a := M.adjoint_comp_self_nonneg
  have hsa : IsSelfAdjoint a := .of_nonneg ha
  -- Both sides are values of the continuous functional calculus at `a`.
  have hshift : cfc (fun s : ℝ => s - 1) a = a - 1 := by
    rw [cfc_sub (fun s : ℝ => s) (fun _ : ℝ => (1 : ℝ)) a, cfc_id' ℝ a, cfc_const_one ℝ a]
  have hmod : cfc (fun s : ℝ => Real.sqrt s - 1) a = M.modulus - 1 := by
    rw [cfc_sub Real.sqrt (fun _ : ℝ => (1 : ℝ)) a, cfc_const_one ℝ a, modulus,
      CFC.sqrt_eq_real_sqrt a ha, cfcₙ_eq_cfc]
  rw [← hmod, ← hshift]
  refine norm_cfc_le (norm_nonneg _) fun t ht => ?_
  have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg ha ht
  calc ‖Real.sqrt t - 1‖ = |Real.sqrt t - 1| := Real.norm_eq_abs _
    _ ≤ |t - 1| := TauCeti.Real.abs_sqrt_sub_one_le_abs_sub_one ht0
    _ = ‖t - 1‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖cfc (fun s : ℝ => s - 1) a‖ := norm_apply_le_norm_cfc (fun s : ℝ => s - 1) a ht

/-- **The near-isometry estimate.**  If the Gram operator `M⋆ M` is within `δ` of
the identity, then `M` is within `δ` of the isometry `M.polarIsometry`.

The constant is sharp and there is no dimension or surjectivity hypothesis: the
only assumption is that `M` is bounded below, which for `‖M⋆ M - 1‖ < 1` is
automatic (`isUnit_modulus_of_norm_adjoint_comp_self_sub_one_lt_one`). -/
theorem norm_sub_polarIsometry_apply_le {M : E →L[ℂ] F} (hM : IsUnit M.modulus) (x : E) :
    ‖M x - M.polarIsometry x‖ ≤ ‖M.adjoint ∘L M - 1‖ * ‖x‖ :=
  (norm_sub_polarIsometry_apply_le_norm_modulus_sub_one hM x).trans
    (mul_le_mul_of_nonneg_right M.norm_modulus_sub_one_le (norm_nonneg x))

/-- The operator-norm form of the near-isometry estimate. -/
theorem norm_sub_polarIsometry_le {M : E →L[ℂ] F} (hM : IsUnit M.modulus) :
    ‖M - M.polarIsometry‖ ≤ ‖M.adjoint ∘L M - 1‖ :=
  opNorm_le_bound _ (norm_nonneg _) fun x => by
    simpa using norm_sub_polarIsometry_apply_le hM x

/-- The polar isometry of a bounded-below operator, bundled as a
`LinearIsometry`. -/
@[simps! apply]
noncomputable def polarLinearIsometry {M : E →L[ℂ] F} (hM : IsUnit M.modulus) : E →ₗᵢ[ℂ] F where
  toLinearMap := M.polarIsometry
  norm_map' := norm_polarIsometry_apply hM

/-- The polar isometry of a bounded-below operator with dense range, bundled as a
`LinearIsometryEquiv`.

Surjectivity is where a genuine hypothesis is needed and it is stated
explicitly: `M.polarIsometry` is surjective as soon as `M` is (its range is that
of `M`, since `|M|` is invertible), and in the finite-dimensional case with
`finrank ℂ E = finrank ℂ F` it follows from injectivity. -/
@[simps! apply]
noncomputable def polarLinearIsometryEquiv {M : E →L[ℂ] F} (hM : IsUnit M.modulus)
    (hsurj : Function.Surjective M.polarIsometry) : E ≃ₗᵢ[ℂ] F :=
  .ofSurjective (polarLinearIsometry hM) hsurj

theorem surjective_polarIsometry_of_surjective {M : E →L[ℂ] F} (hM : IsUnit M.modulus)
    (hsurj : Function.Surjective M) : Function.Surjective M.polarIsometry := by
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨M.modulus x, by rw [polarIsometry_modulus_apply hM, hx]⟩

end ContinuousLinearMap

end
