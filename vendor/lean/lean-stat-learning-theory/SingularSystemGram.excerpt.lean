/-
VENDORED SOURCE EXCERPT -- NOT PART OF THE PROJECT BUILD.

Original work:
  Yuanhe Zhang, Jason D. Lee, Fanghui Liu
  `SLT/MatrixInfra/Basic.lean`
  https://github.com/YuanheZ/lean-stat-learning-theory
  commit 216e578c9576bab6b0abc3ba6c65762536768e96
  blob 8c7dd1aaeaedd6c702c28fee2845d9f66cecf219
  selected source declarations beginning at lines 164-339
  Apache License 2.0

Local change: this provenance wrapper was added and noncontiguous surrounding declarations
were omitted. The selected declaration text below is otherwise copied verbatim. It depends on
imports, namespaces, variables, and earlier declarations from the original project.
-/

/--
The right singular vectors of a matrix, chosen as an orthonormal eigenbasis of `A†A`. This is the
`v_i` basis in HDP Theorem 4.1.1.
-/
noncomputable def rightSingularVectorBasis (A : Matrix m n 𝕜) :
    OrthonormalBasis (Fin (Fintype.card n)) 𝕜 (EuclideanSpace 𝕜 n) :=
  A.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvectorBasis finrank_euclideanSpace

/--
The right singular vectors diagonalize `A†A`, with eigenvalues equal to squared singular values:
`A†A v_i = s_i^2 v_i`.
-/
theorem adjoint_comp_self_apply_rightSingularVectorBasis
    (A : Matrix m n 𝕜) (i : Fin (Fintype.card n)) :
    (LinearMap.adjoint A.toEuclideanLin ∘ₗ A.toEuclideanLin)
        (A.rightSingularVectorBasis i) =
      ((A.singularValues i ^ 2 : ℝ) : 𝕜) • A.rightSingularVectorBasis i := by
  rw [rightSingularVectorBasis]
  have h :=
    A.toEuclideanLin.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis
      finrank_euclideanSpace i
  rw [← A.sq_singularValues_fin i] at h
  exact h

/--
The left singular vector associated to a nonzero singular value, defined as `s_i⁻¹ A v_i`. For
zero singular values this definition is still total, but the main equation below is stated under
`s_i ≠ 0`.
-/
noncomputable def leftSingularVector (A : Matrix m n 𝕜) (i : Fin (Fintype.card n)) :
    EuclideanSpace 𝕜 m :=
  (((A.singularValues i : ℝ) : 𝕜)⁻¹) • A.toEuclideanLin (A.rightSingularVectorBasis i)

/-- The SVD proof relation `A v_i = s_i u_i` for nonzero singular values. -/
theorem apply_rightSingularVectorBasis_eq_smul_leftSingularVector
    (A : Matrix m n 𝕜) {i : Fin (Fintype.card n)} (hi : A.singularValues i ≠ 0) :
    A.toEuclideanLin (A.rightSingularVectorBasis i) =
      ((A.singularValues i : ℝ) : 𝕜) • A.leftSingularVector i := by
  unfold leftSingularVector
  rw [smul_smul]
  have hci : ((A.singularValues i : ℝ) : 𝕜) ≠ 0 := by
    simpa only [ne_eq, RCLike.ofReal_eq_zero] using hi
  rw [mul_inv_cancel₀ hci]
  simp

/-- Right singular vectors with zero singular value lie in the kernel of `A`. -/
theorem apply_rightSingularVectorBasis_eq_zero_of_singularValues_eq_zero
    (A : Matrix m n 𝕜) {i : Fin (Fintype.card n)} (hi : A.singularValues i = 0) :
    A.toEuclideanLin (A.rightSingularVectorBasis i) = 0 := by
  have hker :
      A.rightSingularVectorBasis i ∈
        (LinearMap.adjoint A.toEuclideanLin ∘ₗ A.toEuclideanLin).ker := by
    have hzero : A.toEuclideanLin.singularValues (i : ℕ) = 0 := by
      simpa [Matrix.singularValues] using hi
    rw [LinearMap.mem_ker]
    rw [A.adjoint_comp_self_apply_rightSingularVectorBasis i]
    simp [hzero]
  have hkerA : A.rightSingularVectorBasis i ∈ A.toEuclideanLin.ker := by
    simpa [LinearMap.ker_adjoint_comp_self] using hker
  exact LinearMap.mem_ker.mp hkerA

/--
The SVD proof relation `A v_i = s_i u_i`, with the zero singular-value case included by the
kernel lemma above.
-/
theorem apply_rightSingularVectorBasis_eq_smul_leftSingularVector'
    (A : Matrix m n 𝕜) (i : Fin (Fintype.card n)) :
    A.toEuclideanLin (A.rightSingularVectorBasis i) =
      ((A.singularValues i : ℝ) : 𝕜) • A.leftSingularVector i := by
  by_cases hi : A.singularValues i = 0
  · rw [A.apply_rightSingularVectorBasis_eq_zero_of_singularValues_eq_zero hi]
    rw [hi]
    simp
  · exact A.apply_rightSingularVectorBasis_eq_smul_leftSingularVector hi

/-- Applying `A` to a right singular vector has norm equal to the corresponding singular value. -/
theorem norm_apply_rightSingularVectorBasis
    (A : Matrix m n 𝕜) (i : Fin (Fintype.card n)) :
    ‖A.toEuclideanLin (A.rightSingularVectorBasis i)‖ = A.singularValues i := by
  refine (sq_eq_sq₀ (norm_nonneg _) (A.singularValues_nonneg i)).mp ?_
  calc
    ‖A.toEuclideanLin (A.rightSingularVectorBasis i)‖ ^ 2 =
        RCLike.re (inner 𝕜 (A.toEuclideanLin (A.rightSingularVectorBasis i))
          (A.toEuclideanLin (A.rightSingularVectorBasis i))) := by
      exact norm_sq_eq_re_inner (𝕜 := 𝕜) _
    _ = RCLike.re (inner 𝕜
          ((LinearMap.adjoint A.toEuclideanLin ∘ₗ A.toEuclideanLin)
            (A.rightSingularVectorBasis i))
          (A.rightSingularVectorBasis i)) := by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    _ = RCLike.re (inner 𝕜
          (((A.singularValues i ^ 2 : ℝ) : 𝕜) • A.rightSingularVectorBasis i)
          (A.rightSingularVectorBasis i)) := by
      rw [A.adjoint_comp_self_apply_rightSingularVectorBasis i]
    _ = A.singularValues i ^ 2 := by
      simp [inner_smul_left, OrthonormalBasis.norm_eq_one, RCLike.ofReal_pow]

/-- Nonzero left singular vectors are unit vectors. -/
theorem norm_leftSingularVector_of_singularValues_ne_zero
    (A : Matrix m n 𝕜) {i : Fin (Fintype.card n)} (hi : A.singularValues i ≠ 0) :
    ‖A.leftSingularVector i‖ = 1 := by
  unfold leftSingularVector
  rw [norm_smul]
  rw [A.norm_apply_rightSingularVectorBasis i]
  have hpos : 0 < A.singularValues i := lt_of_le_of_ne' (A.singularValues_nonneg i) hi
  rw [norm_inv, RCLike.norm_ofReal, abs_of_pos hpos]
  exact inv_mul_cancel₀ hi

/--
The left singular vectors indexed by nonzero singular values are orthonormal. Together with the
right singular-vector orthonormal basis, this records the orthonormal-family part of HDP
Theorem 4.1.1.
-/
theorem orthonormal_leftSingularVector_of_singularValues_ne_zero
    (A : Matrix m n 𝕜) :
    Orthonormal 𝕜
      (fun i : { i : Fin (Fintype.card n) // A.singularValues i ≠ 0 } =>
        A.leftSingularVector i) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i = j
  · subst j
    simp [A.norm_leftSingularVector_of_singularValues_ne_zero i.property,
      inner_self_eq_norm_sq_to_K]
  · have hne : (i : Fin (Fintype.card n)) ≠ (j : Fin (Fintype.card n)) := by
      intro hval
      exact hij (Subtype.ext hval)
    have hmap :
        inner 𝕜 (A.toEuclideanLin (A.rightSingularVectorBasis i))
            (A.toEuclideanLin (A.rightSingularVectorBasis j)) = 0 := by
      calc
        inner 𝕜 (A.toEuclideanLin (A.rightSingularVectorBasis i))
            (A.toEuclideanLin (A.rightSingularVectorBasis j)) =
            inner 𝕜 ((LinearMap.adjoint A.toEuclideanLin ∘ₗ A.toEuclideanLin)
              (A.rightSingularVectorBasis i)) (A.rightSingularVectorBasis j) := by
          rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
        _ = inner 𝕜
            (((A.singularValues i ^ 2 : ℝ) : 𝕜) • A.rightSingularVectorBasis i)
            (A.rightSingularVectorBasis j) := by
          rw [A.adjoint_comp_self_apply_rightSingularVectorBasis i]
        _ = 0 := by
          rw [inner_smul_left]
          simp [A.rightSingularVectorBasis.inner_eq_zero hne]
    rw [if_neg hij]
    unfold leftSingularVector
    rw [inner_smul_left, inner_smul_right, hmap]
    simp

/--
Operator-action form of the finite-dimensional SVD reconstruction: expanding `x` in the right
singular-vector orthonormal basis and applying `A` gives the sum of the singular-value weighted
left singular vectors.
-/
theorem toEuclideanLin_apply_eq_sum_singularValue_leftSingularVector
    (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    A.toEuclideanLin x =
      ∑ i : Fin (Fintype.card n),
        A.rightSingularVectorBasis.repr x i •
          (((A.singularValues i : ℝ) : 𝕜) • A.leftSingularVector i) := by
  calc
    A.toEuclideanLin x =
        A.toEuclideanLin
          (∑ i : Fin (Fintype.card n),
            A.rightSingularVectorBasis.repr x i • A.rightSingularVectorBasis i) := by
      rw [A.rightSingularVectorBasis.sum_repr x]
    _ = ∑ i : Fin (Fintype.card n),
          A.rightSingularVectorBasis.repr x i •
            A.toEuclideanLin (A.rightSingularVectorBasis i) := by
      simp [map_sum, map_smul]
    _ = ∑ i : Fin (Fintype.card n),
          A.rightSingularVectorBasis.repr x i •
            (((A.singularValues i : ℝ) : 𝕜) • A.leftSingularVector i) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [A.apply_rightSingularVectorBasis_eq_smul_leftSingularVector' i]
