/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8

Staged for Tau Ceti, roadmap topic T19.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/PiL2.lean`
(the `ℓ¹ ≤ √card · ℓ²` bound) and `Mathlib/Analysis/Matrix/Normed.lean` (the
entrywise → `ℓ²`-operator-norm bound).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Chebyshev


/-! # `ℓ¹`–`ℓ²` and entrywise–operator norm comparisons

Two elementary norm comparisons that are absent from Mathlib (which has the
`ℓ²`-operator-norm API in `Mathlib/Analysis/CStarAlgebra/Matrix.lean` but no
bound of it by the entrywise norm):

* on `EuclideanSpace 𝕜 ι`, `∑ i, ‖x i‖ ≤ √(card ι) · ‖x‖` (Cauchy–Schwarz /
  Chebyshev);
* for an `RCLike` finite rectangular matrix with entries bounded by `ε`, the
  induced Euclidean map has `‖A x‖ ≤ √(card ι) ε √(card κ) ‖x‖`; the square
  `Fin n` specialization gives `‖A x‖ ≤ n ε ‖x‖`.

## Main results

* `EuclideanSpace.sum_norm_le_sqrt_card_mul_norm`
* `Matrix.norm_toEuclideanLin_le_of_entry_le`
* `Matrix.norm_toEuclideanLin_le_of_entry_le_fin`

The matrix estimate uses the scalar norm over any `RCLike` field. Apply the triangle
inequality in each row, then the two `l1`-to-`l2` estimates. Empty row or
column index types yield a zero action without constraining `ε`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.Matrix.EntrywiseOpNorm`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `7366186`.
* Extraction class: **moved**, then generalized for arbitrary finite rectangular
  matrices. The `EuclideanSpace` and `Matrix` namespaces match the public APIs.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

open scoped BigOperators

namespace EuclideanSpace

/--
**`ℓ¹ ≤ √card · ℓ²` on Euclidean space.** For `x : EuclideanSpace 𝕜 ι`,
`∑ i, ‖x i‖ ≤ √(card ι) · ‖x‖`.
-/
theorem sum_norm_le_sqrt_card_mul_norm {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]
    (x : EuclideanSpace 𝕜 ι) :
    ∑ i, ‖x i‖ ≤ Real.sqrt (Fintype.card ι) * ‖x‖ := by
  have hcs : (∑ i, ‖x i‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖x i‖ ^ 2 := by
    simpa [Finset.card_univ] using
      sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i => ‖x i‖)
  have hnorm : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := EuclideanSpace.norm_sq_eq x
  have hsum_nonneg : 0 ≤ ∑ i, ‖x i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hrhs_nonneg : 0 ≤ Real.sqrt (Fintype.card ι) * ‖x‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hsq : (∑ i, ‖x i‖) ^ 2 ≤ (Real.sqrt (Fintype.card ι) * ‖x‖) ^ 2 := by
    have hrw : (Real.sqrt (Fintype.card ι) * ‖x‖) ^ 2 = (Fintype.card ι : ℝ) * ‖x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (Fintype.card ι : ℝ))]
    rw [hrw, hnorm]; exact hcs
  exact (abs_le_of_sq_le_sq' hsq hrhs_nonneg).2

end EuclideanSpace

namespace Matrix

/-- If every entry of a finite rectangular matrix is bounded by `ε`, its Euclidean
action has norm at most `√(card ι) * ε * √(card κ)` times the input norm.

Both index types may be empty; in that case the action is zero, even if `ε` is negative. -/
theorem norm_toEuclideanLin_le_of_entry_le {𝕜 ι κ : Type*} [RCLike 𝕜]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    {A : Matrix ι κ 𝕜} {ε : ℝ} (hentry : ∀ i j, ‖A i j‖ ≤ ε)
    (x : EuclideanSpace 𝕜 κ) :
    ‖Matrix.toEuclideanLin A x‖ ≤
      Real.sqrt (Fintype.card ι) * ε * Real.sqrt (Fintype.card κ) * ‖x‖ := by
  classical
  by_cases hrows : Nonempty ι
  · by_cases hcols : Nonempty κ
    · obtain ⟨i₀⟩ := hrows
      obtain ⟨j₀⟩ := hcols
      have heps : 0 ≤ ε := (norm_nonneg (A i₀ j₀)).trans (hentry i₀ j₀)
      have hrow : ∀ i : ι,
          ‖(Matrix.toEuclideanLin A x) i‖ ≤
            ε * (Real.sqrt (Fintype.card κ) * ‖x‖) := by
        intro i
        have happ : (Matrix.toEuclideanLin A x) i = ∑ j : κ, A i j * x j := by
          -- `toEuclideanLin` abbreviates `toLpLin 2 2`; use its public evaluation
          -- theorem instead of reducing the `EuclideanSpace`/`WithLp` implementation.
          calc
            _ = (WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)) i :=
              congrArg (fun y : EuclideanSpace 𝕜 ι => y i)
                (Matrix.toLpLin_apply (p := 2) (q := 2) A x)
            _ = ∑ j : κ, A i j * x j := by
              simp [Matrix.mulVec, dotProduct]
        calc
          ‖(Matrix.toEuclideanLin A x) i‖ = ‖∑ j : κ, A i j * x j‖ := by rw [happ]
          _ ≤ ∑ j : κ, ‖A i j * x j‖ := norm_sum_le _ _
          _ = ∑ j : κ, ‖A i j‖ * ‖x j‖ := by simp only [norm_mul]
          _ ≤ ∑ j : κ, ε * ‖x j‖ :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_right (hentry i j) (norm_nonneg _)
          _ = ε * ∑ j : κ, ‖x j‖ := by rw [Finset.mul_sum]
          _ ≤ ε * (Real.sqrt (Fintype.card κ) * ‖x‖) := by
            exact mul_le_mul_of_nonneg_left
              (EuclideanSpace.sum_norm_le_sqrt_card_mul_norm x) heps
      have hnorm_sq : ‖Matrix.toEuclideanLin A x‖ ^ 2
          ≤ (Fintype.card ι : ℝ) *
            (ε * (Real.sqrt (Fintype.card κ) * ‖x‖)) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        calc
          ∑ i : ι, ‖(Matrix.toEuclideanLin A x) i‖ ^ 2
              ≤ ∑ _i : ι, (ε * (Real.sqrt (Fintype.card κ) * ‖x‖)) ^ 2 := by
            exact Finset.sum_le_sum fun i _ =>
              pow_le_pow_left₀ (norm_nonneg _) (hrow i) 2
          _ = (Fintype.card ι : ℝ) *
                (ε * (Real.sqrt (Fintype.card κ) * ‖x‖)) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hs : (Real.sqrt (Fintype.card ι)) ^ 2 = (Fintype.card ι : ℝ) :=
        Real.sq_sqrt (by positivity)
      have hsq_eq :
          (Real.sqrt (Fintype.card ι) * ε * Real.sqrt (Fintype.card κ) * ‖x‖) ^ 2 =
            (Fintype.card ι : ℝ) *
              (ε * (Real.sqrt (Fintype.card κ) * ‖x‖)) ^ 2 := by
        simp only [mul_pow, hs]
        ring
      have hle : ‖Matrix.toEuclideanLin A x‖ ^ 2
          ≤ (Real.sqrt (Fintype.card ι) * ε *
              Real.sqrt (Fintype.card κ) * ‖x‖) ^ 2 := by
        rw [hsq_eq]
        exact hnorm_sq
      exact (abs_le_of_sq_le_sq' hle (by positivity)).2
    · have hx : x = 0 := by
        ext j
        exact (hcols ⟨j⟩).elim
      subst x
      simp
  · have hzero : Matrix.toEuclideanLin A x = 0 := by
      ext i
      exact (hrows ⟨i⟩).elim
    have hcard : Fintype.card ι = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun i => hrows ⟨i⟩⟩
    simp [hzero, hcard]

/-- The square finite-index form of the entrywise-to-Euclidean operator bound:
`‖A x‖ ≤ n * ε * ‖x‖` when `‖A i j‖ ≤ ε`. -/
theorem norm_toEuclideanLin_le_of_entry_le_fin {𝕜 : Type*} [RCLike 𝕜]
    {n : ℕ} {A : Matrix (Fin n) (Fin n) 𝕜} {ε : ℝ}
    (hentry : ∀ i j, ‖A i j‖ ≤ ε)
    (x : EuclideanSpace 𝕜 (Fin n)) :
    ‖Matrix.toEuclideanLin A x‖ ≤ (n : ℝ) * ε * ‖x‖ := by
  have h := norm_toEuclideanLin_le_of_entry_le hentry x
  have hs : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  calc
    ‖Matrix.toEuclideanLin A x‖ ≤
        Real.sqrt (n : ℝ) * ε * Real.sqrt (n : ℝ) * ‖x‖ := by
      simpa only [Fintype.card_fin] using h
    _ = (Real.sqrt (n : ℝ)) ^ 2 * ε * ‖x‖ := by ring
    _ = (n : ℝ) * ε * ‖x‖ := by rw [hs]

end Matrix
