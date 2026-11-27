/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Intertwining
public import TauCeti.Analysis.Normed.Operator.Banach

/-!
# Intertwining and the real continuous functional calculus

One-sided inverses of the shifted partial operators suffice for the
resolvent comparison. For bounded self-adjoint operators over an arbitrary
`RCLike` field, realification and Tau Ceti's continuous calculus intertwining
give the real calculus comparison and its eigenvector specialization.

The original DKPS development replaced the corresponding Spectra
intertwining route. The contribution census records which parts are now
provided by the accepted Tau Ceti API.
-/

public section

open scoped InnerProductSpace

namespace TauCeti
namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **An intertwiner intertwines the resolvents.**

If `X` carries `B` to `A` — `A (X y) = X (B y)` on `dom B` — and `z` is a
resolvent point of both, then `X R_B = R_A X`.

Only the two defining properties of a resolvent are used: that `R_A` inverts
`z • I - A` on the domain, and that `R_B` lands in `dom B` and inverts
`z • I - B` there.  Neither self-adjointness nor closedness is needed. -/
theorem resolvent_intertwines
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {X : F →L[𝕜] E} {z : 𝕜}
    {RA : E →L[𝕜] E} {RB : F →L[𝕜] F}
    (hRA : ∀ ψ : A.domain, RA (z • (ψ : E) - A ψ) = (ψ : E))
    (hRB : ∀ φ : F, ∃ h : RB φ ∈ B.domain, z • RB φ - B ⟨RB φ, h⟩ = φ)
    (hmaps : ∀ y : B.domain, X (y : F) ∈ A.domain)
    (hint : ∀ y : B.domain, A ⟨X (y : F), hmaps y⟩ = X (B y)) :
    X ∘L RB = RA ∘L X := by
  refine ContinuousLinearMap.ext fun φ => ?_
  obtain ⟨hmem, hBinv⟩ := hRB φ
  -- Push `X` through `z • RB φ - B ⟨RB φ⟩ = φ` and rewrite with the
  -- intertwining relation, turning it into a statement about `A`.
  have hXpush : z • X (RB φ) - A ⟨X (RB φ), hmaps ⟨RB φ, hmem⟩⟩ = X φ := by
    have := congrArg X hBinv
    rw [map_sub, map_smul] at this
    rw [hint ⟨RB φ, hmem⟩]
    exact this
  -- `RA` inverts `A - z` at that domain vector, which is exactly the claim.
  have := hRA ⟨X (RB φ), hmaps ⟨RB φ, hmem⟩⟩
  rw [hXpush] at this
  simpa using this.symm

section SelfAdjoint

variable [CompleteSpace E] [CompleteSpace F]

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
  ContinuousLinearMap.instStarOrderedRingRCLike

/-- A rectangular intertwiner of self-adjoint operators intertwines their real continuous
functional calculi. Continuous symbols are required on the union of the two real spectra. -/
theorem cfc_intertwines_selfAdjoint
    {u : E →L[𝕜] E} {v : F →L[𝕜] F} (hu : IsSelfAdjoint u) (hv : IsSelfAdjoint v)
    {X : F →L[𝕜] E}
    (hint : X ∘L v = u ∘L X) {f : ℝ → ℝ}
    (hf : ContinuousOn f (_root_.spectrum ℝ u ∪ _root_.spectrum ℝ v)) :
    X ∘L cfc f v = cfc f u ∘L X := by
  let : Algebra ℝ (E →L[𝕜] E) := ContinuousLinearMap.realAlgebra
  let : Algebra ℝ (F →L[𝕜] F) := ContinuousLinearMap.realAlgebra
  have hcu := ContinuousLinearMap.restrictScalars_cfc f u
  have hcv := ContinuousLinearMap.restrictScalars_cfc f v
  let := InnerProductSpace.rclikeToReal 𝕜 E
  let := InnerProductSpace.rclikeToReal 𝕜 F
  have hU := ContinuousLinearMap.isSelfAdjoint_restrictScalars_iff.mpr hu
  have hV := ContinuousLinearMap.isSelfAdjoint_restrictScalars_iff.mpr hv
  have hcomp : X.restrictScalars ℝ ∘L v.restrictScalars ℝ =
      u.restrictScalars ℝ ∘L X.restrictScalars ℝ :=
    congrArg (ContinuousLinearMap.restrictScalars ℝ) hint
  have hstar : X.restrictScalars ℝ ∘L star (v.restrictScalars ℝ) =
      star (u.restrictScalars ℝ) ∘L X.restrictScalars ℝ := by
    rw [hU.star_eq, hV.star_eq]
    exact hcomp
  have hfu : ContinuousOn f (_root_.spectrum ℝ (u.restrictScalars ℝ)) := by
    rw [ContinuousLinearMap.spectrum_restrictScalars]
    exact hf.mono Set.subset_union_left
  have hfv : ContinuousOn f (_root_.spectrum ℝ (v.restrictScalars ℝ)) := by
    rw [ContinuousLinearMap.spectrum_restrictScalars]
    exact hf.mono Set.subset_union_right
  have h := (X.restrictScalars ℝ).comp_cfc_eq_cfc_comp hcomp hstar f hfv hfu hV hU
  rw [← hcv, ← hcu] at h
  exact ContinuousLinearMap.ext fun x => DFunLike.congr_fun h x

/-- **Continuous functional calculus acts pointwise on a genuine eigenvector.**

If a bounded self-adjoint operator satisfies `u x = λ x` with `x ≠ 0`, then
`f(u) x = f(λ) x` for every continuous real symbol `f`.  The proof is
infinite-dimensional: the normalized rank-one projection onto `𝕜 x`
intertwines `u` with the scalar operator `λ I`, so
`cfc_intertwines_selfAdjoint` transports the scalar functional calculus.

This is the bounded `RCLike` analogue of the finite-dimensional eigenbasis
calculus lemma, and is deliberately independent of any compactness or pure
point spectrum assumption. -/
theorem cfc_apply_of_apply_eq_real_smul
    {u : E →L[𝕜] E} (hu : IsSelfAdjoint u) {x : E} (hx0 : x ≠ 0)
    {lam : ℝ} (hx : u x = ((lam : ℝ) : 𝕜) • x)
    (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f u x = ((f lam : ℝ) : 𝕜) • x := by
  let alpha : 𝕜 := (inner 𝕜 x x)⁻¹
  let X : E →L[𝕜] E := alpha • InnerProductSpace.rankOne 𝕜 x x
  let v : E →L[𝕜] E := algebraMap ℝ (E →L[𝕜] E) lam
  have hinner : inner 𝕜 x x ≠ 0 := by
    intro hzero
    exact hx0 (inner_self_eq_zero.mp hzero)
  have hXx : X x = x := by
    simp only [X, smul_apply, InnerProductSpace.rankOne_apply, smul_smul]
    rw [show alpha * inner 𝕜 x x = 1 from inv_mul_cancel₀ hinner]
    exact one_smul 𝕜 x
  have hv_eq : v = ((lam : ℝ) : 𝕜) • (1 : E →L[𝕜] E) := by
    dsimp [v]
    rw [Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_smul 𝕜]
  have hv_apply (y : E) : v y = ((lam : ℝ) : 𝕜) • y := by
    rw [hv_eq, smul_apply, one_apply_eq_self]
  have hvsa : IsSelfAdjoint v := by
    dsimp [v]
    exact cfc_predicate_algebraMap lam
  have hint : X ∘L v = u ∘L X := by
    ext y
    simp only [ContinuousLinearMap.comp_apply, hv_apply, X, smul_apply,
      InnerProductSpace.rankOne_apply, map_smul, hx, smul_smul]
    rw [mul_comm (((lam : ℝ) : 𝕜)) (alpha * inner 𝕜 x y)]
  have hinter := cfc_intertwines_selfAdjoint hu hvsa hint hf.continuousOn
  have hcfv : cfc f v = algebraMap ℝ (E →L[𝕜] E) (f lam) := by
    dsimp [v]
    rw [cfc_algebraMap]
  have hfv_eq : algebraMap ℝ (E →L[𝕜] E) (f lam) =
      ((f lam : ℝ) : 𝕜) • (1 : E →L[𝕜] E) := by
    rw [Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_smul 𝕜]
  have happ := congrArg (fun T : E →L[𝕜] E => T x) hinter
  simp only [ContinuousLinearMap.comp_apply, hcfv, hfv_eq, smul_apply,
    one_apply_eq_self, map_smul, hXx] at happ
  exact happ.symm

end SelfAdjoint

end LinearPMap
end TauCeti
