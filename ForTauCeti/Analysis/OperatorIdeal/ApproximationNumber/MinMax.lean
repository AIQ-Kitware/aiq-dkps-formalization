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
  `ContinuousLinearMap.lowerBound_le_approximationNumber_of_finrank` and
  `ContinuousLinearMap.lowerBound_le_approximationNumber_of_linearIndependent`.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking;
  Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Extraction class: **copied**, converted to the Tau Ceti module system.
  Declaration names are unchanged (they already extend the canonical Mathlib
  namespace).  No mathematical change.
* Spectra influence: **none** — this module imports only Mathlib and the
  sibling `Basic` and `CourantFischer` staging modules.
-/

@[expose] public section

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

/-- Courant--Fischer lower bound for approximation numbers. If an
`(n+1)`-dimensional test subspace has lower modulus at least `c`, then the
`n`th approximation number is at least `c`.

Unlike the finite-dimensional Eckart--Young theorem above, the ambient source
and target spaces need not be finite-dimensional. -/
theorem lowerBound_le_approximationNumber_of_finrank
    (T : E₁ →L[𝕜] F₁) (n : ℕ) (V : Submodule 𝕜 E₁)
    [FiniteDimensional 𝕜 V]
    (hVdim : finrank 𝕜 V = n + 1) (c : ℝ)
    (hV : ∀ x : V, ‖x‖ = 1 → c ≤ ‖T (x : E₁)‖) :
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
    -- now independent, so argue through injectivity and `Cardinal.lift`
    -- instead: an injective map identifies the domain with its range.
    have hinj : Function.Injective RV.toLinearMap :=
      LinearMap.ker_eq_bot.mp hkerbot
    have hequiv :
        Cardinal.lift.{w} (Module.rank 𝕜 V) =
          Cardinal.lift.{v}
            (Module.rank 𝕜 (LinearMap.range RV.toLinearMap)) :=
      (LinearEquiv.ofInjective RV.toLinearMap hinj).lift_rank_eq
    have hVrank : Module.rank 𝕜 V = ((n + 1 : ℕ) : Cardinal) := by
      calc
        Module.rank 𝕜 V = (finrank 𝕜 V : Cardinal) :=
          (Module.finrank_eq_rank' 𝕜 V).symm
        _ = ((n + 1 : ℕ) : Cardinal) := by rw [hVdim]
    have hbad : ((n + 1 : ℕ) : Cardinal.{max v w}) ≤ ((n : ℕ) : Cardinal) := by
      calc
        ((n + 1 : ℕ) : Cardinal.{max v w})
            = Cardinal.lift.{w} (Module.rank 𝕜 V) := by
          rw [hVrank, Cardinal.lift_natCast]
        _ = Cardinal.lift.{v} (LinearMap.rank RV.toLinearMap) := hequiv
        _ ≤ Cardinal.lift.{v} ((n : ℕ) : Cardinal) :=
          Cardinal.lift_le.mpr hRVrank
        _ = ((n : ℕ) : Cardinal) := Cardinal.lift_natCast n
    have hbad' : n + 1 ≤ n := by exact_mod_cast hbad
    omega
  obtain ⟨z, hzker, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hzNorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  let x : V := ((‖z‖⁻¹ : ℝ) : 𝕜) • z
  have hxker : x ∈ RV.ker := RV.ker.smul_mem _ hzker
  have hxNorm : ‖x‖ = 1 := by
    simp only [x, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm]
    exact inv_mul_cancel₀ hzNorm
  have hRx : R (x : E₁) = 0 := by
    change RV x = 0
    exact LinearMap.mem_ker.mp hxker
  calc
    c ≤ ‖T (x : E₁)‖ := hV x hxNorm
    _ = ‖(T - R) (x : E₁)‖ := by rw [sub_apply, hRx, sub_zero]
    _ ≤ ‖T - R‖ * ‖(x : E₁)‖ := (T - R).le_opNNNorm (x : E₁)
    _ = ‖T - R‖ := by
      have hxNN : ‖(x : E₁)‖ = 1 := by
        exact hxNorm
      rw [hxNN, mul_one]

/-- Family form of `lowerBound_le_approximationNumber_of_finrank`. A linearly
independent family of `n+1` vectors determines the required test subspace. -/
theorem lowerBound_le_approximationNumber_of_linearIndependent
    (T : E₁ →L[𝕜] F₁) (n : ℕ) (v : Fin (n + 1) → E₁)
    (hv : LinearIndependent 𝕜 v) (c : ℝ)
    (hV : ∀ x ∈ Submodule.span 𝕜 (Set.range v),
      ‖x‖ = 1 → c ≤ ‖T x‖) :
    c ≤ T.approximationNumber n := by
  let V : Submodule 𝕜 E₁ := Submodule.span 𝕜 (Set.range v)
  let b : Module.Basis (Fin (n + 1)) 𝕜 V := Module.Basis.span hv
  letI : FiniteDimensional 𝕜 V := b.finiteDimensional_of_finite
  have hVdim : finrank 𝕜 V = n + 1 := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  apply lowerBound_le_approximationNumber_of_finrank T n V hVdim c
  intro x hx
  exact hV (x : E₁) x.2 hx

end InfiniteDimensionalMinMaxLower

end

end ContinuousLinearMap

end
