/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Spectral cutoffs of a positive operator

For a positive operator `A : E →L[ℂ] E` and a level `s : ℝ` the **spectral cutoff** is the
positive part of `A - s`, and the **spectral cocutoff** is the positive part of `s - A`,
both formed with the continuous functional calculus:

```
A.spectralCutoff s = (A - s)₊,   A.spectralCocutoff s = (s - A)₊.
```

Their point is that the closed subspace `ker (A.spectralCutoff s)` splits `E` exactly the
way the spectral projection of `A` for `[0, s]` would, *without* needing a projection-valued
measure:

* on `ker (A.spectralCutoff s)`, `A` is bounded above by `s`;
* on its orthogonal complement, `A` is bounded below by `s`.

That is all the spectral theorem is used for in the min--max theorem for approximation
numbers, so with these two lemmas that theorem needs no measure theory — see
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean`.

## The two inequalities

Both come from a pointwise inequality of real functions fed to `cfc_nonneg`, so neither
needs `A` to be compact, `E` to be separable, or any spectral decomposition to exist.

For the upper bound, `t * t - s ^ 2 ≤ (t + s) * max (t - s) 0` holds for every `t ≥ 0` —
with equality when `t ≥ s` and with a negative left side otherwise.  Reading it through the
functional calculus gives `A * A ≤ s ^ 2 + (A + s) * (A - s)₊`, and the second summand
annihilates the kernel of the cutoff, leaving `‖A y‖ ^ 2 ≤ s ^ 2 * ‖y‖ ^ 2` there.

For the lower bound, `(s - t) ≤ max (s - t) 0` gives `s - A ≤ (s - A)₊`.  The cocutoff
kills the orthogonal complement of the kernel — its range lies in the kernel, because
`max (t - s) 0 * max (s - t) 0 = 0` identically, and it is self-adjoint, so it preserves the
complement as well — leaving `s * ‖y‖ ^ 2 ≤ re ⟪A y, y⟫`, and Cauchy--Schwarz finishes.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none**.  `vendor/Spectra` proves the corresponding facts through its
  projection-valued-measure and Borel functional calculus layer; the point of this module is
  that the continuous functional calculus already in Mathlib suffices.
-/

@[expose] public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The positive part `(A - s)₊` of `A - s`, formed with the continuous functional
calculus. -/
noncomputable def spectralCutoff (A : E →L[ℂ] E) (s : ℝ) : E →L[ℂ] E :=
  cfc (fun t : ℝ => max (t - s) 0) A

/-- The positive part `(s - A)₊` of `s - A`, formed with the continuous functional
calculus. -/
noncomputable def spectralCocutoff (A : E →L[ℂ] E) (s : ℝ) : E →L[ℂ] E :=
  cfc (fun t : ℝ => max (s - t) 0) A

/-- The operator identity behind the upper bound: `s ^ 2 + (A + s) (A - s)₊ - A ^ 2` is the
functional calculus of a single real function. -/
theorem cutoff_split (A : E →L[ℂ] E) (hA : 0 ≤ A) (s : ℝ) :
    (s ^ 2 : ℝ) • (1 : E →L[ℂ] E) + (A + (s : ℝ) • 1) * A.spectralCutoff s - A * A
      = cfc (fun t : ℝ => s ^ 2 + (t + s) * max (t - s) 0 - t * t) A := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  rw [spectralCutoff,
    cfc_sub (a := A) (fun t : ℝ => s ^ 2 + (t + s) * max (t - s) 0) (fun t : ℝ => t * t),
    cfc_add (a := A) (fun _ : ℝ => s ^ 2) (fun t : ℝ => (t + s) * max (t - s) 0),
    cfc_mul (fun t : ℝ => t + s) (fun t : ℝ => max (t - s) 0) A,
    cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) A,
    cfc_add (a := A) (fun t : ℝ => t) (fun _ : ℝ => s),
    cfc_const (s ^ 2) A, cfc_const s A, cfc_id' ℝ A]
  simp [Algebra.algebraMap_eq_smul_one]

/-- The operator identity behind the lower bound. -/
theorem cocutoff_split (A : E →L[ℂ] E) (hA : 0 ≤ A) (s : ℝ) :
    A.spectralCocutoff s - ((s : ℝ) • (1 : E →L[ℂ] E) - A)
      = cfc (fun t : ℝ => max (s - t) 0 - (s - t)) A := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  rw [spectralCocutoff,
    cfc_sub (a := A) (fun t : ℝ => max (s - t) 0) (fun t : ℝ => s - t),
    cfc_sub (a := A) (fun _ : ℝ => s) (fun t : ℝ => t),
    cfc_const s A, cfc_id' ℝ A]
  simp [Algebra.algebraMap_eq_smul_one]

/-- The cutoff and the cocutoff annihilate each other: the real functions defining them have
disjoint supports. -/
theorem spectralCutoff_mul_spectralCocutoff (A : E →L[ℂ] E) (hA : 0 ≤ A) (s : ℝ) :
    A.spectralCutoff s * A.spectralCocutoff s = 0 := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  rw [spectralCutoff, spectralCocutoff,
    ← cfc_mul (fun t : ℝ => max (t - s) 0) (fun t : ℝ => max (s - t) 0) A]
  have hzero : (fun t : ℝ => max (t - s) 0 * max (s - t) 0) = fun _ : ℝ => (0 : ℝ) := by
    funext t
    rcases le_or_gt t s with h | h
    · rw [max_eq_right (by linarith)]; ring
    · rw [max_eq_right (a := s - t) (by linarith)]; ring
  rw [hzero, cfc_const_zero]

/-- The complementary spectral cut-off is self-adjoint, hence an orthogonal projection. -/
theorem isSelfAdjoint_spectralCocutoff (A : E →L[ℂ] E) (hA : 0 ≤ A) (s : ℝ) :
    IsSelfAdjoint (A.spectralCocutoff s) := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  exact cfc_predicate _ A

/-- The range of the cocutoff lies in the kernel of the cutoff. -/
@[simp]
theorem spectralCutoff_spectralCocutoff_apply (A : E →L[ℂ] E) (hA : 0 ≤ A) (s : ℝ) (x : E) :
    A.spectralCutoff s (A.spectralCocutoff s x) = 0 := by
  have h := congrArg (fun B : E →L[ℂ] E => B x) (spectralCutoff_mul_spectralCocutoff A hA s)
  simpa [mul_apply_eq_comp] using h

section Auxiliary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem re_inner_mul_self {A : H →L[ℂ] H} (hsa : IsSelfAdjoint A) (y : H) :
    RCLike.re ⟪(A * A) y, y⟫_ℂ = ‖A y‖ ^ 2 := by
  have hadj : A.adjoint = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hsa.star_eq
  have hstep : ⟪(A * A) y, y⟫_ℂ = ⟪A y, A y⟫_ℂ := by
    rw [mul_apply_eq_comp, ← hadj, ContinuousLinearMap.adjoint_inner_left, hadj]
  rw [hstep, inner_self_eq_norm_sq_to_K]
  norm_cast

omit [CompleteSpace H] in
private theorem nonneg_re_inner {B : H →L[ℂ] H} (hB : 0 ≤ B) (y : H) :
    0 ≤ RCLike.re ⟪B y, y⟫_ℂ :=
  ((ContinuousLinearMap.nonneg_iff_isPositive B).mp hB).2 y

omit [CompleteSpace H] in
private theorem re_inner_real_smul_self (c : ℝ) (y : H) :
    RCLike.re ⟪c • y, y⟫_ℂ = c * ‖y‖ ^ 2 := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c y, inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

end Auxiliary

/-- **`A` is bounded above by `s` on the kernel of its `s`-cutoff.** -/
theorem norm_apply_le_of_spectralCutoff_apply_eq_zero {A : E →L[ℂ] E} (hA : 0 ≤ A) {s : ℝ}
    (hs : 0 ≤ s) {y : E} (hy : A.spectralCutoff s y = 0) : ‖A y‖ ≤ s * ‖y‖ := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hpt : ∀ t ∈ spectrum ℝ A, 0 ≤ s ^ 2 + (t + s) * max (t - s) 0 - t * t := by
    intro t ht
    have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg hA ht
    rcases le_or_gt t s with h | h
    · rw [max_eq_right (by linarith)]; nlinarith
    · rw [max_eq_left (by linarith)]; nlinarith
  have hnn : (0 : E →L[ℂ] E) ≤
      (s ^ 2 : ℝ) • (1 : E →L[ℂ] E) + (A + (s : ℝ) • 1) * A.spectralCutoff s - A * A := by
    rw [cutoff_split A hA s]
    exact cfc_nonneg hpt
  have hform := nonneg_re_inner hnn y
  have happ : ((A + (s : ℝ) • 1) * A.spectralCutoff s) y = 0 := by
    rw [mul_apply_eq_comp]
    simp [hy]
  rw [sub_apply, add_apply, happ, add_zero, smul_apply, one_apply_eq_self,
    inner_sub_left, map_sub, re_inner_mul_self hsa y,
    re_inner_real_smul_self (s ^ 2) y] at hform
  have hsq : ‖A y‖ ^ 2 ≤ (s * ‖y‖) ^ 2 := by nlinarith
  have h1 : (0 : ℝ) ≤ ‖A y‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ s * ‖y‖ := mul_nonneg hs (norm_nonneg _)
  nlinarith

/-- **`A` is bounded below by `s` on the orthogonal complement of the kernel of its
`s`-cutoff.** -/
theorem le_norm_apply_of_mem_orthogonal_ker_spectralCutoff {A : E →L[ℂ] E} (hA : 0 ≤ A)
    {s : ℝ} {y : E} (hy : y ∈ (LinearMap.ker (A.spectralCutoff s : E →ₗ[ℂ] E))ᗮ) :
    s * ‖y‖ ≤ ‖A y‖ := by
  have hsa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA
  have hco : IsSelfAdjoint (A.spectralCocutoff s) := isSelfAdjoint_spectralCocutoff A hA s
  have hcoadj : (A.spectralCocutoff s).adjoint = A.spectralCocutoff s := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hco.star_eq
  have hrange : ∀ x : E,
      A.spectralCocutoff s x ∈ LinearMap.ker (A.spectralCutoff s : E →ₗ[ℂ] E) :=
    fun x => spectralCutoff_spectralCocutoff_apply A hA s x
  have hzero : A.spectralCocutoff s y = 0 := by
    have hperp : ∀ u ∈ LinearMap.ker (A.spectralCutoff s : E →ₗ[ℂ] E), ⟪u, y⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal _ y).mp hy
    have hself : ⟪A.spectralCocutoff s y, A.spectralCocutoff s y⟫_ℂ = 0 := by
      rw [← ContinuousLinearMap.adjoint_inner_left, hcoadj]
      exact hperp _ (hrange (A.spectralCocutoff s y))
    exact inner_self_eq_zero.mp hself
  have hnn : (0 : E →L[ℂ] E) ≤ A.spectralCocutoff s - ((s : ℝ) • (1 : E →L[ℂ] E) - A) := by
    rw [cocutoff_split A hA s]
    refine cfc_nonneg fun t _ => ?_
    rcases le_or_gt (s - t) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h.le]; linarith
  have hform := nonneg_re_inner hnn y
  rw [sub_apply, sub_apply, hzero, smul_apply, one_apply_eq_self,
    inner_sub_left, inner_sub_left, map_sub, map_sub, re_inner_real_smul_self s y] at hform
  simp only [inner_zero_left, map_zero, zero_sub, neg_sub] at hform
  have hcs : RCLike.re ⟪A y, y⟫_ℂ ≤ ‖A y‖ * ‖y‖ :=
    le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  · have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hkey : s * ‖y‖ ^ 2 ≤ ‖A y‖ * ‖y‖ := by linarith
    nlinarith

end ContinuousLinearMap
