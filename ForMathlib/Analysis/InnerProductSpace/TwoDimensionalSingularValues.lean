/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/

import ForMathlib.Analysis.InnerProductSpace.KyFan
import ForMathlib.Analysis.InnerProductSpace.UnitarilyInvariantNorm

/-!
# Singular values of elementary two-dimensional operators

Reusable finite-dimensional reductions for planar sharpness models.  The main
lemma compares a Gram operator with a real diagonal operator; the matrix
corollaries are the symmetric off-diagonal and one-sided rank-one blocks.
-/

namespace ForMathlib

open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The finitely supported sequence with two prescribed entries. -/
noncomputable def pairSingularValues (s0 s1 : ℝ) : ℕ →₀ ℝ :=
  Finsupp.single 0 s0 + Finsupp.single 1 s1

@[simp] theorem pairSingularValues_zero (s0 s1 : ℝ) :
    pairSingularValues s0 s1 0 = s0 := by
  simp [pairSingularValues]

@[simp] theorem pairSingularValues_one (s0 s1 : ℝ) :
    pairSingularValues s0 s1 1 = s1 := by
  simp [pairSingularValues]

@[simp] theorem pairSingularValues_of_two_le (s0 s1 : ℝ) {i : ℕ} (hi : 2 ≤ i) :
    pairSingularValues s0 s1 i = 0 := by
  simp [pairSingularValues, Finsupp.single_apply, Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hi),
    Nat.ne_of_gt (lt_of_lt_of_le Nat.one_lt_two hi)]

/-- A nonnegative decreasing diagonal on a two-dimensional inner-product space
has the expected two singular values and no others. -/
theorem singularValues_diagOp_fin_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
    (hfin : finrank 𝕜 E = 2) (b : OrthonormalBasis (Fin 2) 𝕜 E)
    {s0 s1 : ℝ} (hs0 : 0 ≤ s0) (hs1 : 0 ≤ s1) (hord : s1 ≤ s0) :
    (diagOp b ![s0, s1]).singularValues = pairSingularValues s0 s1 := by
  ext i
  have hanti : Antitone (![s0, s1] : Fin 2 → ℝ) := by
    intro a c hac
    fin_cases a <;> fin_cases c <;> simp_all
  have hnonneg : ∀ j : Fin 2, 0 ≤ (![s0, s1] : Fin 2 → ℝ) j := by
    intro j
    fin_cases j
    · simpa using hs0
    · simpa using hs1
  by_cases hi : i < 2
  · -- `fin_cases` cannot see through a `let`-bound index, so split on `i` itself
    interval_cases i
    · simpa using singularValues_diagOp (𝕜 := 𝕜) hfin b hanti hnonneg (0 : Fin 2)
    · simpa using singularValues_diagOp (𝕜 := 𝕜) hfin b hanti hnonneg (1 : Fin 2)
  · have h2 : 2 ≤ i := Nat.le_of_not_gt hi
    rw [(diagOp b ![s0, s1]).singularValues_of_finrank_le]
    · exact (pairSingularValues_of_two_le s0 s1 h2).symm
    · simpa [hfin] using h2

/-- A planar operator whose Gram operator is diagonal in an orthonormal basis
has the corresponding prescribed singular values. -/
theorem singularValues_eq_pair_of_gram_eq
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (hfin : finrank 𝕜 E = 2) (b : OrthonormalBasis (Fin 2) 𝕜 E)
    (A : E →ₗ[𝕜] F) {s0 s1 : ℝ}
    (hs0 : 0 ≤ s0) (hs1 : 0 ≤ s1) (hord : s1 ≤ s0)
    (hgram : A.adjoint ∘ₗ A = diagOp b ![s0 ^ 2, s1 ^ 2]) :
    A.singularValues = pairSingularValues s0 s1 := by
  let D : E →ₗ[𝕜] E := diagOp b ![s0, s1]
  have hDgram : D.adjoint ∘ₗ D = diagOp b ![s0 ^ 2, s1 ^ 2] := by
    dsimp [D]
    rw [adjoint_diagOp, diagOp_comp]
    congr 1
    funext i
    fin_cases i <;> simp [pow_two]
  calc
    A.singularValues = D.singularValues :=
      singularValues_eq_of_gram_eq (hgram.trans hDgram.symm)
    _ = pairSingularValues s0 s1 :=
      singularValues_diagOp_fin_two hfin b hs0 hs1 hord

/-- A symmetric planar operator whose square is `r² I` has the two singular
values `|r|, |r|`. -/
theorem singularValues_eq_abs_pair_of_isSymmetric_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
    (hfin : finrank 𝕜 E = 2) (b : OrthonormalBasis (Fin 2) 𝕜 E)
    (A : E →ₗ[𝕜] E) (r : ℝ) (hA : A.IsSymmetric)
    (hsq : A ∘ₗ A = (((r ^ 2 : ℝ) : 𝕜) • LinearMap.id)) :
    A.singularValues = pairSingularValues |r| |r| := by
  apply singularValues_eq_pair_of_gram_eq hfin b A (abs_nonneg r) (abs_nonneg r) le_rfl
  rw [hA.adjoint_eq, hsq]
  refine b.toBasis.ext fun i => ?_
  rw [OrthonormalBasis.coe_toBasis]
  -- the diagonal entry only reduces once the index is split
  fin_cases i <;>
    simp [LinearMap.smul_apply, LinearMap.id_apply, diagOp_apply_basis, sq_abs]


/-- In positive finite dimension, the operator norm is the largest singular
value. -/
theorem opNorm_eq_singularValues_zero
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (A : E →ₗ[𝕜] F) {n : ℕ} (hn : finrank 𝕜 E = n) (hn0 : 0 < n) :
    ‖A.toContinuousLinearMap‖ = A.singularValues 0 := by
  apply le_antisymm
  · refine A.toContinuousLinearMap.opNorm_le_bound
      (A.singularValues_nonneg 0) fun x => ?_
    exact norm_apply_le_singularValues_zero_mul A hn hn0 x
  · obtain ⟨x, hx, hAx⟩ := exists_norm_apply_eq_singularValues_zero A hn hn0
    rw [← hAx]
    calc
      ‖A x‖ = ‖A.toContinuousLinearMap x‖ := rfl
      _ ≤ ‖A.toContinuousLinearMap‖ * ‖x‖ :=
        A.toContinuousLinearMap.le_opNorm x
      _ = ‖A.toContinuousLinearMap‖ := by rw [hx, mul_one]

/-- The singular values of the symmetric off-diagonal planar block
`[[0,r],[r,0]]` are `|r|,|r|`. -/
theorem singularValues_offDiagonal_two_by_two (r : ℝ) :
    (Matrix.toEuclideanLin
      !![(0 : 𝕜), (r : 𝕜); (r : 𝕜), 0]).singularValues =
      pairSingularValues |r| |r| := by
  let A : EuclideanSpace 𝕜 (Fin 2) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 2) :=
    Matrix.toEuclideanLin !![(0 : 𝕜), (r : 𝕜); (r : 𝕜), 0]
  -- symmetry is exactly hermitianness of the underlying matrix
  have hsym : A.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.conjTranspose_apply, RCLike.conj_ofReal])
  have hsq : A ∘ₗ A = (((r ^ 2 : ℝ) : 𝕜) • LinearMap.id) := by
    ext x i
    fin_cases i <;>
      simp [A, Matrix.toEuclideanLin_apply, Matrix.vecHead, Matrix.vecTail] <;>
      push_cast <;> ring
  exact singularValues_eq_abs_pair_of_isSymmetric_sq
    finrank_euclideanSpace_fin (EuclideanSpace.basisFun (Fin 2) 𝕜) A r hsym hsq

/-- The singular values of the one-sided lower-left planar block
`[[0,0],[r,0]]` are `|r|,0`. -/
theorem singularValues_lowerLeft_two_by_two (r : ℝ) :
    (Matrix.toEuclideanLin
      !![(0 : 𝕜), 0; (r : 𝕜), 0]).singularValues =
      pairSingularValues |r| 0 := by
  let A : EuclideanSpace 𝕜 (Fin 2) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 2) :=
    Matrix.toEuclideanLin !![(0 : 𝕜), 0; (r : 𝕜), 0]
  -- compute the adjoint as a matrix rather than through `adjoint_inner_left`
  have hadj : A.adjoint =
      Matrix.toEuclideanLin !![(0 : 𝕜), (r : 𝕜); 0, 0] := by
    rw [show (A.adjoint) =
        (!![(0 : 𝕜), 0; (r : 𝕜), 0]).toEuclideanLin.adjoint from rfl,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply, RCLike.conj_ofReal]
  have hgram : A.adjoint ∘ₗ A =
      diagOp (EuclideanSpace.basisFun (Fin 2) 𝕜) ![|r| ^ 2, 0] := by
    rw [hadj]
    refine (EuclideanSpace.basisFun (Fin 2) 𝕜).toBasis.ext fun i => ?_
    rw [OrthonormalBasis.coe_toBasis]
    -- reduce the diagonal side first: unfolding the basis vector would stop
    -- `diagOp_apply_basis` from matching
    fin_cases i <;>
      rw [diagOp_apply_basis] <;>
      ext j <;> fin_cases j <;>
      simp [A, LinearMap.comp_apply, Matrix.toEuclideanLin_apply,
        Matrix.vecHead, Matrix.vecTail, EuclideanSpace.basisFun_apply,
        sq_abs] <;>
      push_cast <;> ring
  refine singularValues_eq_pair_of_gram_eq finrank_euclideanSpace_fin
    (EuclideanSpace.basisFun (Fin 2) 𝕜) A (abs_nonneg r) le_rfl
    (abs_nonneg r) ?_
  simpa using hgram

end ForMathlib
