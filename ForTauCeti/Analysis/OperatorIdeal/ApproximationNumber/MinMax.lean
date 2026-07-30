/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import ForTauCeti.Analysis.InnerProductSpace.CourantFischer

/-!
# Min--max lower bounds for approximation numbers

This module proves the infinite-dimensional lower half of the
Courant--Fischer characterization for approximation numbers. A uniform lower
modulus on an `(n+1)`-dimensional test subspace forces the `n`th approximation
number to be at least that modulus.

The other half — every strict lower bound for `aₙ(T)` is realized as such a
modulus — is
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean`.

## Namespace note

These declarations extend the existing Mathlib namespace `ContinuousLinearMap`
rather than living under `TauCeti`, so that dot notation resolves and the names
match the eventual Mathlib upstreaming target. Lean field projection binds
`T.foo` only to the literal `ContinuousLinearMap.foo` and does not consult the
enclosing `TauCeti` namespace. This is a deliberate API choice, flagged for Tau
Ceti maintainer review.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module:
  `ForMathlib/Analysis/Normed/Operator/ApproximationNumberMinMax.lean`
  at Davis--Kahan commit `fc38eb48b9b49f2e1d87fe0c7022dc5e262820a7`.
* Original declarations:
  `ContinuousLinearMap.le_approximationNumber_of_finrank_lt` and
  `ContinuousLinearMap.le_approximationNumber_of_linearIndependent`.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking;
  Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Extraction class: **copied**, converted to the Tau Ceti module system.
  Declaration names are unchanged (they already extend the canonical Mathlib
  namespace).  No mathematical change.
* Spectra influence: **none** — this module imports only Mathlib and the
  sibling `Basic` and `CourantFischer` staging modules.
-/

public section

namespace ContinuousLinearMap

open Module (finrank)
open scoped InnerProductSpace

noncomputable section

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]

section InfiniteDimensionalMinMaxLower

variable {E₁ : Type v} {F₁ : Type w}
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]

/-- **Courant--Fischer lower bound for approximation numbers.**  If `T` is
bounded below by `c` on a test subspace of rank greater than `n`, then the `n`th
approximation number is at least `c`.

The hypothesis is stated on `Module.rank`, not `finrank`, and the bound is
homogeneous rather than restricted to unit vectors.  Both matter:

* rank rather than dimension means the test subspace need not be
  finite-dimensional, so there is no `[FiniteDimensional 𝕜 V]` instance to
  supply — an infinite-dimensional `V` satisfies `n < Module.rank 𝕜 V` for every
  `n`.  The proof never uses more than "`V` is too big to be killed by a rank
  `≤ n` map";
* the homogeneous bound `c * ‖x‖ ≤ ‖T x‖` says something at `x = 0` and scales,
  where a unit-vector premise does neither.  `le_approximationNumber_of_finrank_lt`
  below converts from the unit-vector form, which needs no sign hypothesis on
  `c`.

Unlike the finite-dimensional Eckart--Young identification, the ambient source
and target spaces need not be finite-dimensional either.

The converse is
`ContinuousLinearMap.exists_linearIndependent_lowerBound_of_lt_approximationNumber`
in `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean`, so
the characterization is complete; an earlier version of this docstring said only
this half held unconditionally in infinite dimensions, which was a statement
about the then-available proof, not about the mathematics. -/
theorem le_approximationNumber_of_lt_rank
    (T : E₁ →L[𝕜] F₁) (n : ℕ) (V : Submodule 𝕜 E₁) {c : ℝ}
    (hVrank : (n : Cardinal) < Module.rank 𝕜 V)
    (hV : ∀ x : V, c * ‖(x : E₁)‖ ≤ ‖T (x : E₁)‖) :
    c ≤ T.approximationNumber n := by
  refine T.le_approximationNumber_iff.mpr ?_
  intro R hR
  let RV : V →L[𝕜] F₁ := R.comp V.subtypeL
  have hRVrank : RV.rank ≤ (n : Cardinal) := by
    calc
      RV.rank ≤ R.rank := by
        change LinearMap.rank
            (R.toLinearMap.comp V.subtypeL.toLinearMap) ≤ R.rank
        exact LinearMap.rank_comp_le_left V.subtypeL.toLinearMap R.toLinearMap
      _ ≤ (n : Cardinal) := hR
  have hker : RV.ker ≠ ⊥ := by
    intro hkerbot
    -- The rank-nullity identity compares the rank of the range, which lives in
    -- the codomain universe, with the rank of the domain.  Those universes are
    -- independent, so argue through injectivity and `Cardinal.lift` instead: an
    -- injective map identifies the domain with its range.
    have hinj : Function.Injective RV.toLinearMap :=
      LinearMap.ker_eq_bot.mp hkerbot
    have hequiv :
        Cardinal.lift.{w} (Module.rank 𝕜 V) =
          Cardinal.lift.{v}
            (Module.rank 𝕜 (LinearMap.range RV.toLinearMap)) :=
      (LinearEquiv.ofInjective RV.toLinearMap hinj).lift_rank_eq
    have hbad : Module.rank 𝕜 V ≤ (n : Cardinal) := by
      refine Cardinal.lift_le_natCast.mp ?_
      calc
        Cardinal.lift.{w} (Module.rank 𝕜 V)
            = Cardinal.lift.{v} (LinearMap.rank RV.toLinearMap) := hequiv
        _ ≤ Cardinal.lift.{v} ((n : ℕ) : Cardinal) := Cardinal.lift_le.mpr hRVrank
        _ = ((n : ℕ) : Cardinal) := Cardinal.lift_natCast n
    exact absurd hbad (not_le.mpr hVrank)
  obtain ⟨z, hzker, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hzNorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  let x : V := ((‖z‖⁻¹ : ℝ) : 𝕜) • z
  have hxker : x ∈ RV.ker := RV.ker.smul_mem _ hzker
  have hxNorm : ‖(x : E₁)‖ = 1 := by
    simp only [x, Submodule.coe_smul, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm]
    exact inv_mul_cancel₀ hzNorm
  have hRx : R (x : E₁) = 0 := by
    change RV x = 0
    exact LinearMap.mem_ker.mp hxker
  calc
    c = c * ‖(x : E₁)‖ := by rw [hxNorm, mul_one]
    _ ≤ ‖T (x : E₁)‖ := hV x
    _ = ‖(T - R) (x : E₁)‖ := by rw [sub_apply, hRx, sub_zero]
    _ ≤ ‖T - R‖ * ‖(x : E₁)‖ := (T - R).le_opNNNorm (x : E₁)
    _ = ‖T - R‖ := by rw [hxNorm, mul_one]

/-- Finite-dimensional form of `le_approximationNumber_of_lt_rank`, with the
unit-vector premise the classical statement uses.

Nothing is assumed about the sign of `c`: at `x = 0` the homogeneous bound reads
`c * 0 ≤ 0`, and elsewhere it follows by rescaling to a unit vector. -/
theorem le_approximationNumber_of_finrank_lt
    (T : E₁ →L[𝕜] F₁) (n : ℕ) (V : Submodule 𝕜 E₁)
    [FiniteDimensional 𝕜 V] {c : ℝ} (hVdim : n < finrank 𝕜 V)
    (hV : ∀ x : V, ‖(x : E₁)‖ = 1 → c ≤ ‖T (x : E₁)‖) :
    c ≤ T.approximationNumber n := by
  refine le_approximationNumber_of_lt_rank T n V ?_ ?_
  · rw [← Module.finrank_eq_rank' 𝕜 V]
    exact_mod_cast hVdim
  · intro x
    rcases eq_or_ne (x : E₁) 0 with hx | hx
    · simp [hx]
    · -- Rescale `x` to the unit sphere of `V` and use homogeneity of both sides.
      have hxn : ‖(x : E₁)‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      set y : V := ((‖(x : E₁)‖⁻¹ : ℝ) : 𝕜) • x with hy
      have hyNorm : ‖(y : E₁)‖ = 1 := by
        simp only [hy, Submodule.coe_smul, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm]
        exact inv_mul_cancel₀ hxn
      have hTy : ‖T (y : E₁)‖ = ‖(x : E₁)‖⁻¹ * ‖T (x : E₁)‖ := by
        simp [hy, norm_smul]
      have hstep := hV y hyNorm
      rw [hTy] at hstep
      calc c * ‖(x : E₁)‖
          ≤ (‖(x : E₁)‖⁻¹ * ‖T (x : E₁)‖) * ‖(x : E₁)‖ :=
            mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
        _ = ‖T (x : E₁)‖ := by field_simp

/-- Family form of `le_approximationNumber_of_finrank_lt`: a linearly independent
family of `n + 1` vectors determines the required test subspace.

This is not a forgetful wrapper — it is how every downstream consumer in this
repository applies the bound, since a spanning family is what the perturbation
arguments produce. -/
theorem le_approximationNumber_of_linearIndependent
    (T : E₁ →L[𝕜] F₁) (n : ℕ) (v : Fin (n + 1) → E₁)
    (hv : LinearIndependent 𝕜 v) {c : ℝ}
    (hV : ∀ x ∈ Submodule.span 𝕜 (Set.range v),
      ‖x‖ = 1 → c ≤ ‖T x‖) :
    c ≤ T.approximationNumber n := by
  let V : Submodule 𝕜 E₁ := Submodule.span 𝕜 (Set.range v)
  let b : Module.Basis (Fin (n + 1)) 𝕜 V := Module.Basis.span hv
  letI : FiniteDimensional 𝕜 V := b.finiteDimensional_of_finite
  have hVdim : n < finrank 𝕜 V := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
    exact Nat.lt_succ_self n
  refine le_approximationNumber_of_finrank_lt T n V hVdim ?_
  intro x hx
  exact hV (x : E₁) x.2 hx

/-! ### The orthogonal-tail upper bound

Roadmap topic T09 §B4 asks for the intrinsic equality
`aₙ(T) = ⨅ {‖T ∘L (Vᗮ).starProjection‖ : finrank V ≤ n}`.  This is the `≤` half:
every subspace of dimension at most `n` supplies an admissible approximation, so
the approximation number is below every orthogonal tail. -/

/-- **Every orthogonal tail bounds the approximation number.**  Compressing away a
subspace `V` of dimension at most `n` leaves an admissible rank-`≤ n`
approximation, so `aₙ(T) ≤ ‖T ∘L (Vᗮ).starProjection‖`.

This is the easy half of the orthogonal-tail formula (T09 §B4); the reverse
inequality — that the infimum over such `V` is *attained down to* `aₙ(T)` — is not
proved here.  The subspace lies in the **source**, and the dimension bound is
`finrank V ≤ n` under the zero-based indexing this development uses. -/
theorem approximationNumber_le_norm_comp_starProjection_orthogonal
    (T : E₁ →L[𝕜] F₁) (n : ℕ) (V : Submodule 𝕜 E₁)
    [V.HasOrthogonalProjection] [Vᗮ.HasOrthogonalProjection]
    [FiniteDimensional 𝕜 V] (hV : finrank 𝕜 V ≤ n) :
    T.approximationNumber n ≤ ‖T ∘L Vᗮ.starProjection‖ := by
  have hrangeeq :
      LinearMap.range ((T ∘L V.starProjection) : E₁ →ₗ[𝕜] F₁) =
        Submodule.map (T : E₁ →ₗ[𝕜] F₁) V := by
    change LinearMap.range ((T : E₁ →ₗ[𝕜] F₁).comp
        ((V.starProjection : E₁ →ₗ[𝕜] E₁))) = _
    rw [LinearMap.range_comp, Submodule.range_starProjection]
  haveI : FiniteDimensional 𝕜 (Submodule.map (T : E₁ →ₗ[𝕜] F₁) V) := inferInstance
  have hrank : (T ∘L V.starProjection).rank ≤ (n : Cardinal) := by
    rw [LinearMap.rank, hrangeeq,
      ← Module.finrank_eq_rank' 𝕜 (Submodule.map (T : E₁ →ₗ[𝕜] F₁) V)]
    exact_mod_cast le_trans (Submodule.finrank_map_le _ _) hV
  have hsub : T - T ∘L V.starProjection = T ∘L Vᗮ.starProjection := by
    ext x
    have hsplit : x - V.starProjection x = Vᗮ.starProjection x := by
      rw [V.starProjection_orthogonal']
      simp
    have hval : (T - T ∘L V.starProjection) x = T (x - V.starProjection x) := by
      simp [map_sub]
    rw [hval, hsplit]
    rfl
  calc T.approximationNumber n ≤ ‖T - T ∘L V.starProjection‖ :=
        T.approximationNumber_le_norm_sub hrank
    _ = ‖T ∘L Vᗮ.starProjection‖ := by rw [hsub]

end InfiniteDimensionalMinMaxLower

end

end ContinuousLinearMap

end
