/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
module

public import TauCeti.Analysis.InnerProductSpace.Symmetric.FunctionalCalculus
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import TauCeti.Analysis.InnerProductSpace.Positive.SquareRoot

/-!
# Spectral transfer for the accepted finite symmetric calculus

The construction and core algebra, positivity, norm, eigenvector and intertwining
laws are supplied by `LinearMap.IsSymmetric.cfc`. This donor retains coordinate
vanishing, transfer between scalar symbols, and extraction of a preimage eigenvalue
from an eigenvector of a function of the operator. It also retains the short
dependent congruence lemma for changing the underlying operator.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.SelfAdjointFunctionalCalculus`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `caa0966`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, GPT-5.6 Thinking; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The calculus depends only on the operator, not on the symmetry witness.
The operator occurs solely inside that witness's type, so a plain rewrite
cannot reach it; this is the bridge that lets callers replace it. -/
theorem cfc_congr_operator {T S : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (h : T = S) (f : ℝ → ℝ) :
    LinearMap.IsSymmetric.cfc hT f = LinearMap.IsSymmetric.cfc hS f := by
  subst h
  rfl

/-- **An eigenvector of `f(T)` is blind to the eigenvalues `f` does not send to
its eigenvalue.**

If `f(T) x = lam • x`, then `x` has no component along an eigenvector of `T`
whose eigenvalue `f` moves away from `lam`.  This is the one computation behind
both transfer lemmas below, and it is `LinearMap.IsSymmetric.isSymmetric_cfc`
applied to the pair `(f(T) (b i), f(T) x)`. -/
theorem repr_eq_zero_of_calculus_apply_eq_smul
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (f : ℝ → ℝ)
    {x : E} {lam : ℝ}
    (hx : LinearMap.IsSymmetric.cfc hT f x = ((lam : ℝ) : 𝕜) • x)
    {i : Fin (finrank 𝕜 E)} (hi : f (hT.eigenvalues rfl i) ≠ lam) :
    (hT.eigenvectorBasis rfl).repr x i = 0 := by
  set b := hT.eigenvectorBasis rfl with hb
  have hS := LinearMap.IsSymmetric.isSymmetric_cfc hT f
  rw [b.repr_apply_apply]
  have heig : LinearMap.IsSymmetric.cfc hT f (b i) =
      ((f (hT.eigenvalues rfl i) : ℝ) : 𝕜) • b i :=
    LinearMap.IsSymmetric.cfc_apply_eigenvectorBasis hT rfl f i
  have hinner :
      ((f (hT.eigenvalues rfl i) : ℝ) : 𝕜) * ⟪b i, x⟫_𝕜 =
        ((lam : ℝ) : 𝕜) * ⟪b i, x⟫_𝕜 := by
    calc
      ((f (hT.eigenvalues rfl i) : ℝ) : 𝕜) * ⟪b i, x⟫_𝕜
          = ⟪LinearMap.IsSymmetric.cfc hT f (b i), x⟫_𝕜 := by
              rw [heig, inner_smul_left, RCLike.conj_ofReal]
      _ = ⟪b i, LinearMap.IsSymmetric.cfc hT f x⟫_𝕜 := hS _ _
      _ = ((lam : ℝ) : 𝕜) * ⟪b i, x⟫_𝕜 := by
              rw [hx, inner_smul_right]
  have hscalar : (((f (hT.eigenvalues rfl i) - lam : ℝ) : 𝕜)) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (sub_ne_zero.mpr hi)
  apply (mul_eq_zero.mp ?_).resolve_left hscalar
  simpa [RCLike.ofReal_sub, sub_mul] using sub_eq_zero.mpr hinner

/-- **Transfer of an eigenvector between two symbols of the same operator.**

If `f(T)` scales `x` by `lam`, and a second symbol `g` takes the constant value
`mu` at every eigenvalue that `f` sends to `lam`, then `g(T)` scales `x` by `mu`.
Taking `f = id` recovers `LinearMap.IsSymmetric.cfc_apply_of_apply_eq_smul`.

This is what lets an eigenvector of an operator that is *defined* as a functional
calculus — an operator angle `Θ = arcsin (sin Θ)`, say — be pushed through a
different symbol without ever naming the eigenbasis. -/
theorem selfAdjointFunctionalCalculus_apply_of_calculus_apply_eq_smul
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (f g : ℝ → ℝ)
    {x : E} {lam mu : ℝ}
    (hx : LinearMap.IsSymmetric.cfc hT f x = ((lam : ℝ) : 𝕜) • x)
    (hfg : ∀ i : Fin (finrank 𝕜 E),
      f (hT.eigenvalues rfl i) = lam → g (hT.eigenvalues rfl i) = mu) :
    LinearMap.IsSymmetric.cfc hT g x = ((mu : ℝ) : 𝕜) • x := by
  classical
  let b := hT.eigenvectorBasis rfl
  rw [← b.sum_repr x, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, LinearMap.IsSymmetric.cfc_apply_eigenvectorBasis]
  by_cases hi : f (hT.eigenvalues rfl i) = lam
  · rw [hfg i hi]; exact smul_comm _ _ _
  · rw [repr_eq_zero_of_calculus_apply_eq_smul hT f hx hi]
    simp

/-- **A nonzero eigenvector of `f(T)` exhibits its eigenvalue as a value of `f`.**

Contrapositive of `repr_eq_zero_of_calculus_apply_eq_smul`: if `f` missed `lam`
at every eigenvalue of `T`, then every coordinate of `x` in the eigenbasis would
vanish.  This is what pins the *range* of an operator angle: an eigenvalue of
`arcsin (sin Θ)` is an actual arcsine, hence lies in `[-π/2, π/2]`. -/
theorem exists_eigenvalue_of_calculus_apply_eq_smul
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (f : ℝ → ℝ)
    {x : E} {lam : ℝ} (hx0 : x ≠ 0)
    (hx : LinearMap.IsSymmetric.cfc hT f x = ((lam : ℝ) : 𝕜) • x) :
    ∃ i : Fin (finrank 𝕜 E), f (hT.eigenvalues rfl i) = lam := by
  classical
  by_contra hcon
  have hmiss : ∀ i : Fin (finrank 𝕜 E), f (hT.eigenvalues rfl i) ≠ lam :=
    fun i hi => hcon ⟨i, hi⟩
  refine hx0 ?_
  set b := hT.eigenvectorBasis rfl with hb
  calc x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
    _ = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [repr_eq_zero_of_calculus_apply_eq_smul hT f hx (hmiss i), zero_smul]

end TauCeti
