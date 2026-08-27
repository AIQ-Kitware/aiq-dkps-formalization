/-
Proposition 1 of Acharyya et al. (2025): the compact-Riemannian-manifold sufficient condition.

The proposition asserts that Assumptions 1 and 2 hold as soon as every generative model is
associated with a vector on a `d`-dimensional compact Riemannian manifold in an ambient `R^q`,
whose pairwise geodesic distances are the population dissimilarities.

That hypothesis constrains the ambient space and says nothing about how the models are placed
inside it, and the conclusion is a statement about the placement: Assumption 1 asks the
population matrix to have rank `d`, and Assumption 2 asks its `d`-th eigenvalue to stay above a
positive constant.  A degenerate selection satisfies the hypothesis and violates both.

This file records that, with the degenerate selection made explicit and machine-checked.  The
source states Proposition 1 without proof.

Formalized by Claude Opus 5 (claude-opus-5[1m]).
-/
import Acharyya2024.Common
import Acharyya2025.Deterministic
import Acharyya2025.MathlibBridge
import ForTauCeti.Analysis.Matrix.SpectralFunctionMeasurable

open scoped BigOperators
open Acharyya2024 Acharyya2025.Deterministic Acharyya2025.MathlibBridge

namespace Acharyya2025.ManifoldCondition

/-- A constant model selection has vanishing population dissimilarities, hence a vanishing
doubly centred population matrix. -/
theorem classicalMDSMatrix_const_eq_zero {n q : Nat} (p : Rvec q) :
    classicalMDSMatrix (fun _ _ : Fin n => ‖p - p‖) = fun _ _ => 0 := by
  funext i j
  simp only [sub_self, norm_zero]
  simp [classicalMDSMatrix, doubleCenter, rowMean, colMean, grandMean]

/-- The matrix form of the same fact. -/
theorem disMatToMatrix_classicalMDSMatrix_const_eq_zero {n q : Nat} (p : Rvec q) :
    disMatToMatrix (classicalMDSMatrix (fun _ _ : Fin n => ‖p - p‖)) = 0 := by
  funext i j
  rw [disMatToMatrix, classicalMDSMatrix_const_eq_zero]
  rfl

/-- A Hermitian matrix that vanishes has vanishing eigenvalues. -/
theorem eigenvalues₀_eq_zero_of_eq_zero {n : Nat} {B : Matrix (Fin n) (Fin n) Real}
    (hB : B.IsHermitian) (h0 : B = 0) (k : Fin (Fintype.card (Fin n))) :
    hB.eigenvalues₀ k = 0 := by
  have hbound : ∀ i j, |B i j| ≤ (0 : Real) := by simp [h0]
  have h := TauCeti.Matrix.abs_eigenvalues₀_le_of_entry_le hB hbound k
  rw [mul_zero] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/--
**Every eigenvalue of the population matrix of a constant selection is zero.**

Associate every model with one and the same point `p`.  The pairwise population dissimilarities
are then all zero.  They are also, literally, the pairwise geodesic distances of any compact
geodesically convex set containing `p` -- a closed ball of the ambient `R^q`, for instance --
so the hypothesis of Proposition 1 is met.  The doubly centred population matrix nevertheless
vanishes identically.
-/
theorem eigenvalues₀_classicalMDSMatrix_const_eq_zero {n q : Nat} (p : Rvec q)
    (hB : (disMatToMatrix (classicalMDSMatrix (fun _ _ : Fin n => ‖p - p‖))).IsHermitian)
    (k : Fin (Fintype.card (Fin n))) :
    hB.eigenvalues₀ k = 0 :=
  eigenvalues₀_eq_zero_of_eq_zero hB (disMatToMatrix_classicalMDSMatrix_const_eq_zero p) k

/--
**Assumption 2 fails for the constant selection**: no positive constant bounds the eigenvalues
of its population matrix from below, at any stage.
-/
theorem no_eigenvalue_floor_for_const_selection {q : Nat} (p : Rvec q) :
    ¬ ∃ C₁ : Real, 0 < C₁ ∧ ∀ (n : Nat)
      (hB : (disMatToMatrix (classicalMDSMatrix (fun _ _ : Fin n => ‖p - p‖))).IsHermitian)
      (k : Fin (Fintype.card (Fin n))), C₁ ≤ hB.eigenvalues₀ k := by
  rintro ⟨C₁, hC₁, h⟩
  have hzero := disMatToMatrix_classicalMDSMatrix_const_eq_zero (n := 1) p
  have hB : (disMatToMatrix (classicalMDSMatrix (fun _ _ : Fin 1 => ‖p - p‖))).IsHermitian := by
    rw [hzero]; exact Matrix.isHermitian_zero
  have hk : Fin (Fintype.card (Fin 1)) := ⟨0, by simp⟩
  have := h 1 hB hk
  rw [eigenvalues₀_classicalMDSMatrix_const_eq_zero p hB hk] at this
  linarith

/--
**Assumption 1 fails for the constant selection**: the population matrix has rank `0`, not `d`,
for any positive embedding dimension `d`.
-/
theorem rank_classicalMDSMatrix_const_eq_zero {n q : Nat} (p : Rvec q) :
    (disMatToMatrix (classicalMDSMatrix (fun _ _ : Fin n => ‖p - p‖))).rank = 0 := by
  rw [disMatToMatrix_classicalMDSMatrix_const_eq_zero]
  exact Matrix.rank_zero

end Acharyya2025.ManifoldCondition
