/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SingularCharpoly
public import ForTauCeti.Analysis.InnerProductSpace.SchattenSpectralCalculus
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Spectral displacement costs from characteristic polynomials

A finite complex normal map has displacement singular values `|1-λ|`.
Their sums are computed from the full characteristic root multiset, so
algebraic multiplicities and fixed directions remain explicit. For a
real matrix, scalar extension preserves its source Gram polynomial and
hence every singular value. These classical bridges turn a real transport
quartic into its literal spectral cost without choosing eigenvectors at
coalescing phases.
-/

public section

noncomputable section

namespace TauCeti

/-- Every trace parameter in `[-2,2]` determines a conjugate reciprocal
pair on the unit circle with the stated displacement norm. Construct the
upper-half-circle point explicitly; no root separation is required at
the two endpoints. -/
theorem exists_unit_circle_pair_of_trace_mem
    (T : ℝ) (hT : T ∈ Set.Icc (-2) 2) :
    ∃ w : ℂ, w + star w = (T : ℂ) ∧ w * star w = 1 ∧
      ‖1 - w‖ = Real.sqrt (2 - T) := by
  let r := T / 2
  let s := Real.sqrt (1 - r ^ 2)
  let w : ℂ := ⟨r, s⟩
  have hr : 0 ≤ 1 - r ^ 2 := by dsimp [r]; nlinarith [hT.1, hT.2]
  have hs : s ^ 2 = 1 - r ^ 2 := Real.sq_sqrt hr
  refine ⟨w, ?_, ?_, ?_⟩
  · apply Complex.ext <;> simp [w, r]
  · apply Complex.ext <;> simp [w] <;> nlinarith [hs]
  · rw [Complex.norm_eq_sqrt_sq_add_sq]
    congr 1
    change (1 - r) ^ 2 + (0 - s) ^ 2 = 2 - T
    dsimp [r] at hs ⊢
    nlinarith [hs]

/-- A normal complex displacement cost is the sum over its characteristic
roots with algebraic multiplicities. The penalty is arbitrary and need
not vanish at zero; fixed directions are retained in both sums. -/
theorem sum_displacement_singularValues_eq_roots_of_isStarNormal
    {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [AddCommMonoid M]
    (A : E →ₗ[ℂ] E) [IsStarNormal A] (f : ℝ → M) :
    (∑ i : Fin (Module.finrank ℂ E), f ((LinearMap.id - A).singularValues i)) =
      (A.charpoly.roots.map (fun z => f ‖1 - z‖)).sum := by
  classical
  obtain ⟨b, mu, hmu⟩ :=
    LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal A
      (ι := Fin (Module.finrank ℂ E)) (by simp)
  have hdiag : A = Matrix.toLin b.toBasis b.toBasis (Matrix.diagonal mu) := by
    apply b.toBasis.ext
    intro i
    simpa [Matrix.toLin_self, Matrix.diagonal_apply] using hmu i
  have hroots : A.charpoly.roots = Finset.univ.val.map mu := by
    rw [hdiag, Matrix.charpoly_toLin, Matrix.charpoly_diagonal,
      Polynomial.roots_prod _ _ (by
        simp only [Finset.prod_ne_zero_iff]
        exact fun i _ => Polynomial.X_sub_C_ne_zero (mu i))]
    simp
  have heigen (i : Fin (Module.finrank ℂ E)) :
      (LinearMap.id - A : E →ₗ[ℂ] E) (b i) = (1 - mu i) • b i := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply, hmu, sub_smul, one_smul]
  rw [sum_singularValues_eq_sum_norm_eigenvalues b _ _ heigen f, hroots,
    Multiset.map_map]
  rfl

end TauCeti

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

/-- Entrywise scalar extension from `ℝ` to `ℂ` preserves the entire
singular-value sequence of a real matrix. Rectangular and empty matrices
are included. -/
theorem singularValues_toEuclideanLin_map_ofReal (A : Matrix m n ℝ) :
    A.toEuclideanLin.singularValues =
      (A.map Complex.ofRealHom).toEuclideanLin.singularValues := by
  classical
  apply LinearMap.singularValues_eq_complex_of_gram_charpoly_map_eq
  · simp
  · have hstar : (A.map Complex.ofRealHom).conjTranspose =
        A.transpose.map Complex.ofRealHom := by
      ext i j
      simp
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      show A.conjTranspose = A.transpose by simp,
      ← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same,
      Matrix.toLpLin_eq_toLin, Matrix.toLpLin_eq_toLin, Matrix.charpoly_toLin,
      Matrix.charpoly_toLin, hstar, ← Matrix.map_mul, Matrix.charpoly_map]

/-- The literal real displacement cost of any orthogonal matrix is obtained
from its complex characteristic roots. This retains fixed and reflection
eigenvalues and their multiplicities and requires no regularity of `f`. -/
theorem sum_displacement_singularValues_eq_complex_roots_of_orthogonal
    {M : Type*} [AddCommMonoid M] (A : Matrix n n ℝ)
    (hA : A.transpose * A = 1) (f : ℝ → M) :
    (∑ i : Fin (Fintype.card n), f ((LinearMap.id - A.toEuclideanLin).singularValues i)) =
      ((A.charpoly.map Complex.ofRealHom).roots.map (fun z => f ‖1 - z‖)).sum := by
  classical
  let B := A.map Complex.ofRealHom
  let T := B.toEuclideanLin
  have hstar : B.conjTranspose = A.transpose.map Complex.ofRealHom := by
    ext i j
    simp [B]
  have hleft : T.adjoint ∘ₗ T = LinearMap.id := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change B.conjTranspose.toEuclideanLin ∘ₗ B.toEuclideanLin = _
    rw [← Matrix.toLpLin_mul_same, hstar]
    change (A.transpose.map Complex.ofRealHom * A.map Complex.ofRealHom).toEuclideanLin = _
    rw [← Matrix.map_mul, hA]
    simp
  have hright : T ∘ₗ T.adjoint = LinearMap.id := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change B.toEuclideanLin ∘ₗ B.conjTranspose.toEuclideanLin = _
    rw [← Matrix.toLpLin_mul_same, hstar]
    change (A.map Complex.ofRealHom * A.transpose.map Complex.ofRealHom).toEuclideanLin = _
    rw [← Matrix.map_mul, mul_eq_one_comm.mp hA]
    simp
  let : IsStarNormal T := ⟨show T.adjoint ∘ₗ T = T ∘ₗ T.adjoint by rw [hleft, hright]⟩
  have hsing := singularValues_toEuclideanLin_map_ofReal (1 - A)
  have hmap : (1 - A).map Complex.ofRealHom = 1 - B := by
    ext i j
    by_cases h : i = j <;> simp [B, h]
  have hreal : (1 - A).toEuclideanLin = LinearMap.id - A.toEuclideanLin := by simp
  have hcomplex : (1 - B).toEuclideanLin = LinearMap.id - T := by simp [T]
  rw [hmap, hreal, hcomplex] at hsing
  rw [hsing]
  have hcost := TauCeti.sum_displacement_singularValues_eq_roots_of_isStarNormal T f
  rw [finrank_euclideanSpace] at hcost
  simpa only [T, B,
    toEuclideanLin_eq_toLin_orthonormal,
    charpoly_toLin, charpoly_map] using hcost

end Matrix
