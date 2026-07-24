/-
Rectangular Gram-spectrum bridge for raw-response Quench.

This module connects the repository's matrix-level sorted-eigenvalue convention
(`Acharyya2025.MatrixPerturbation.sortedEigenvalues` of `configGram`) to the intrinsic
rectangular spectral theory in `ForMathlib`:

* the configuration Gram matrix acts as the Gram operator `A A†` of the analysis map of the
  configuration (`TauCeti.finiteAnalysis`);
* a quadratic floor on the configuration therefore bounds the first `d` sorted eigenvalues
  of the `n × n` Gram matrix below (`sortedEigenvalues_configGram_lower_of_quadratic_floor`);
* conversely, with `d ≤ n`, a floor on those eigenvalues recovers the quadratic floor
  (`quadratic_floor_of_sortedEigenvalues_configGram_lower`).

The two directions are the deterministic engine behind the reference-Gram spectral floor and
the target-augmentation floor in `SpectralRegularity.lean`.
-/

import DkpsQuench2026.Core.Certificates
import ForTauCeti.Analysis.InnerProductSpace.FiniteFrame
import ForTauCeti.Analysis.InnerProductSpace.CenteredScatter

set_option linter.mathlibStandardSet false

open scoped BigOperators RealInnerProductSpace InnerProductSpace Matrix
open Module (finrank)

set_option maxHeartbeats 400000
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace DkpsQuench2026

open Acharyya2024
open Acharyya2025.MathlibBridge
open Acharyya2025.MatrixPerturbation

/-- The real inner product on `Vec d` written as a coordinate sum. -/
theorem inner_vec_eq_sum {d : Nat} (x y : Vec d) :
    ⟪x, y⟫_ℝ = ∑ k, x k * y k := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- The squared linear form of a configuration row is the squared norm of the corresponding
real inner product; summed over rows, this is the frame quadratic form of the family. -/
theorem sum_sq_linearForm_eq_sum_norm_inner {n d : Nat} (z : Config n d) (x : Vec d) :
    ∑ i : Fin n, (∑ a, x a * z i a) ^ 2 = ∑ i, ‖(inner ℝ (z i) x : ℝ)‖ ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs, inner_vec_eq_sum]
  congr 1
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- The Gram matrix of a configuration acts on `EuclideanSpace ℝ (Fin n)` as the Gram
operator `A A†` of the analysis map of the configuration. -/
theorem toEuclideanLin_configGram_eq_finiteGramOperator {n d : Nat} (z : Config n d) :
    Matrix.toEuclideanLin (disMatToMatrix (configGram z)) =
      TauCeti.finiteGramOperator ℝ z := by
  apply LinearMap.ext
  intro c
  apply PiLp.ext
  intro i
  rw [TauCeti.finiteGramOperator_apply]
  show (disMatToMatrix (configGram z) *ᵥ WithLp.ofLp c) i = _
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_vec_eq_sum]
  rfl

/-- The repository's sorted eigenvalues of a configuration Gram matrix agree with the sorted
eigenvalues of the finite-family Gram operator. -/
theorem sortedEigenvalues_configGram_eq_eigenvalues_finiteGramOperator
    {n d : Nat} (z : Config n d) (i : Fin n) :
    sortedEigenvalues (configGramPosSemidef z).isHermitian i =
      (TauCeti.isSymmetric_finiteGramOperator ℝ z).eigenvalues
        finrank_euclideanSpace_fin i := by
  have hcongr := TauCeti.eigenvalues_congr'
    (toEuclideanLin_configGram_eq_finiteGramOperator z)
    (opSym (configGramPosSemidef z).isHermitian)
    (TauCeti.isSymmetric_finiteGramOperator ℝ z)
    (finrank_euclideanSpace_fin (n := n))
  exact congrFun hcongr i

/-- **Quadratic floor to Gram spectral floor.**  A quadratic floor
`α‖x‖² ≤ ∑ᵢ ⟪x, zᵢ⟫²` for the configuration bounds the first `d` sorted eigenvalues of the
`n × n` configuration Gram matrix below by `α`.  No relation between `d` and `n` is assumed:
a positive floor forces `d ≤ n` through injectivity of the analysis map. -/
theorem sortedEigenvalues_configGram_lower_of_quadratic_floor
    {n d : Nat} {z : Config n d} {α : Real}
    (hquad : ∀ x : Vec d, α * ‖x‖ ^ 2 ≤ ∑ i : Fin n, (∑ a, x a * z i a) ^ 2)
    (i : Fin n) (hi : (i : Nat) < d) :
    α ≤ sortedEigenvalues (configGramPosSemidef z).isHermitian i := by
  rw [sortedEigenvalues_configGram_eq_eigenvalues_finiteGramOperator]
  refine TauCeti.le_eigenvalues_finiteGramOperator_of_forall_le_sum_sq ℝ
    (fun x => ?_) finrank_euclideanSpace_fin i (by simpa [finrank_euclideanSpace_fin] using hi)
  rw [← sum_sq_linearForm_eq_sum_norm_inner]
  exact hquad x

/-- **Gram spectral floor to quadratic floor.**  With `d ≤ n`, a floor on the first `d`
sorted eigenvalues of the configuration Gram matrix recovers the quadratic floor for the
configuration. -/
theorem quadratic_floor_of_sortedEigenvalues_configGram_lower
    {n d : Nat} (hdn : d ≤ n) {z : Config n d} {α : Real}
    (hlow : ∀ i : Fin n, (i : Nat) < d →
      α ≤ sortedEigenvalues (configGramPosSemidef z).isHermitian i)
    (x : Vec d) :
    α * ‖x‖ ^ 2 ≤ ∑ i : Fin n, (∑ a, x a * z i a) ^ 2 := by
  rw [sum_sq_linearForm_eq_sum_norm_inner]
  refine TauCeti.sum_sq_floor_of_le_eigenvalues_finiteGramOperator ℝ
    finrank_euclideanSpace_fin (by simpa [finrank_euclideanSpace_fin] using hdn)
    (fun k hk => ?_) x
  rw [← sortedEigenvalues_configGram_eq_eigenvalues_finiteGramOperator]
  exact hlow k (by simpa [finrank_euclideanSpace_fin] using hk)

/-- The repository centroid is the `ForMathlib` finite mean. -/
theorem configCentroid_eq_finiteMean {n d : Nat} (z : Config n d) :
    configCentroid z = TauCeti.finiteMean ℝ z :=
  rfl

/-- Sorted eigenvalues depend only on the matrix, not on the Hermitian certificate. -/
theorem sortedEigenvalues_matrix_congr {n : Nat} {B₁ B₂ : SqMat n} (h : B₁ = B₂)
    (h₁ : B₁.IsHermitian) (h₂ : B₂.IsHermitian) :
    sortedEigenvalues h₁ = sortedEigenvalues h₂ := by
  subst h; rfl

/-- The augmented centered squared-projection sum dominates the reference centered
squared-projection sum: recentering after adding one point contributes the exact nonnegative
rank-one correction of the online-variance identity. -/
theorem sum_sq_centered_le_augmented {n d : Nat}
    (ψref : Fin n → Vec d) (target : Vec d) (x : Vec d) :
    ∑ i : Fin n, (∑ a, x a * centerConfig ψref i a) ^ 2 ≤
      ∑ i : Fin (n + 1),
        (∑ a, x a * centerConfig (Fin.lastCases target ψref) i a) ^ 2 := by
  have hkey : ∀ {m : Nat} (w : Config m d),
      ∑ i : Fin m, (∑ a, x a * centerConfig w i a) ^ 2 =
        RCLike.re (inner ℝ (TauCeti.centeredScatter ℝ w x) x) := by
    intro m w
    rw [TauCeti.re_inner_centeredScatter_self]
    exact sum_sq_linearForm_eq_sum_norm_inner (centerConfig w) x
  rw [hkey ψref, hkey (Fin.lastCases target ψref)]
  rw [show (Fin.lastCases target ψref : Fin (n + 1) → Vec d) =
    TauCeti.appendFin ψref target from rfl]
  rw [TauCeti.re_inner_centeredScatter_append]
  have hnn : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) *
      ‖(inner ℝ (target - TauCeti.finiteMean ℝ ψref) x : ℝ)‖ ^ 2 := by
    positivity
  linarith

end DkpsQuench2026
