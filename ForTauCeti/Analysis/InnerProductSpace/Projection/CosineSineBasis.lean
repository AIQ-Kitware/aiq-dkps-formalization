/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.ScaledOrthonormalExtension
public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Data.Matrix.Block

/-!
# Principal-angle cosine--sine bases, including both endpoints

Apply the accepted singular system to the sine embedding `L -> Kᗮ`.
Its right basis is already ordered by the accepted principal sines. The
images in `K` and `Kᗮ` have diagonal Gram matrices with cosine and sine
scales. Complete each normalized nonzero family with its original labels.
Thus zero and right angles require no inverse on a zero scale and no
separate acuteness assumption. The construction is real or complex and
includes the empty pair.
-/

public section

noncomputable section

namespace Submodule

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

private theorem inner_projection_partition (K : Submodule 𝕜 E) (x y : E) :
    ⟪K.orthogonalProjectionOnto x, K.orthogonalProjectionOnto y⟫_𝕜 +
      ⟪Kᗮ.orthogonalProjectionOnto x, Kᗮ.orthogonalProjectionOnto y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  change ⟪K.starProjection x, K.starProjection y⟫_𝕜 +
    ⟪Kᗮ.starProjection x, Kᗮ.starProjection y⟫_𝕜 = _
  rw [K.inner_starProjection_left_eq_right, Kᗮ.inner_starProjection_left_eq_right]
  rw [K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem y),
    Kᗮ.starProjection_eq_self_iff.mpr (Kᗮ.starProjection_apply_mem y)]
  rw [← inner_add_right, K.starProjection_add_starProjection_orthogonal]

/-- A balanced finite pair has cosine--sine orthonormal bases labeled by
the accepted principal angles in decreasing order. No angle is deleted:
the common, exterior and crossed-defect directions remain in the bases.
The dimension conditions say that both the source and its complement have
the target's dimension. -/
theorem exists_orthonormalBases_cos_sin_principalAngles
    (K L : Submodule 𝕜 E)
    (hKL : Module.finrank 𝕜 K = Module.finrank 𝕜 L)
    (hcomp : Module.finrank 𝕜 Kᗮ = Module.finrank 𝕜 L) :
    ∃ u : OrthonormalBasis (Fin (Module.finrank 𝕜 L)) 𝕜 K,
      ∃ v : OrthonormalBasis (Fin (Module.finrank 𝕜 L)) 𝕜 Kᗮ,
        ∃ w : OrthonormalBasis (Fin (Module.finrank 𝕜 L)) 𝕜 L,
          ∀ i, (w i : E) = ((Real.cos (K.principalAngles L i) : ℝ) : 𝕜) • (u i : E) +
            ((Real.sin (K.principalAngles L i) : ℝ) : 𝕜) • (v i : E) := by
  classical
  let A : L →ₗ[𝕜] Kᗮ := Kᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ L.subtype
  let B : L →ₗ[𝕜] K := K.orthogonalProjectionOnto.toLinearMap ∘ₗ L.subtype
  let w := A.rightSingularBasis
  have hsv : A.singularValues = K.principalSines L := by
    have h := K.principalSines_range_eq_singularValues
      (X := L.subtypeL) L.subtypeₗᵢ.isometry
    have hrange : L.subtypeL.range = L := by
      change L.subtype.range = L
      exact L.range_subtype
    have hincl : Kᗮ.subtypeₗᵢ.toLinearMap ∘ₗ A =
        (Kᗮ.starProjection ∘L L.subtypeL).toLinearMap := by
      ext x
      rfl
    rw [← LinearMap.singularValues_linearIsometry_comp Kᗮ.subtypeₗᵢ A, hincl]
    simpa only [hrange, K.principalSines_comm L hKL] using h.symm
  have hs (i : Fin (Module.finrank 𝕜 L)) :
      A.singularValues i = Real.sin (K.principalAngles L i) := by
    rw [hsv]
    exact (K.sin_principalAngles L i).symm
  have hAi (i j : Fin (Module.finrank 𝕜 L)) :
      ⟪A (w i), A (w j)⟫_𝕜 =
        if i = j then ((Real.sin (K.principalAngles L i) ^ 2 : ℝ) : 𝕜) else 0 := by
    rw [A.inner_apply_rightSingularBasis]
    rw [w.inner_eq_ite, hs]
    split_ifs <;> simp_all
  have hBi (i j : Fin (Module.finrank 𝕜 L)) :
      ⟪B (w i), B (w j)⟫_𝕜 =
        if i = j then ((Real.cos (K.principalAngles L i) ^ 2 : ℝ) : 𝕜) else 0 := by
    have hsum := inner_projection_partition K (w i) (w j)
    change ⟪B (w i), B (w j)⟫_𝕜 + ⟪A (w i), A (w j)⟫_𝕜 = ⟪w i, w j⟫_𝕜 at hsum
    rw [hAi, w.inner_eq_ite] at hsum
    by_cases hij : i = j
    · subst j
      simp only [ite_true] at hsum ⊢
      have hpy : ((Real.cos (K.principalAngles L i)^2 : ℝ) : 𝕜) +
          ((Real.sin (K.principalAngles L i)^2 : ℝ) : 𝕜) = 1 := by
        exact_mod_cast Real.cos_sq_add_sin_sq (K.principalAngles L i)
      linear_combination hsum - hpy
    · simpa only [hij, ite_false, add_zero] using hsum
  obtain ⟨u, hu⟩ := OrthonormalBasis.exists_smul_eq_of_inner_eq_ite
    (by simpa only [Fintype.card_fin] using hKL) (fun i => B (w i))
    (fun i => Real.cos (K.principalAngles L i)) hBi
  obtain ⟨v, hv⟩ := OrthonormalBasis.exists_smul_eq_of_inner_eq_ite
    (by simpa only [Fintype.card_fin] using hcomp) (fun i => A (w i))
    (fun i => Real.sin (K.principalAngles L i)) hAi
  refine ⟨u, v, w, fun i => ?_⟩
  have hKu : K.starProjection (w i) =
      ((Real.cos (K.principalAngles L i) : ℝ) : 𝕜) • (u i : E) :=
    congrArg Subtype.val (hu i)
  have hKv : Kᗮ.starProjection (w i) =
      ((Real.sin (K.principalAngles L i) : ℝ) : 𝕜) • (v i : E) :=
    congrArg Subtype.val (hv i)
  rw [← hKu, ← hKv]
  exact (K.starProjection_add_starProjection_orthogonal (w i)).symm

/-- Combine the two cosine--sine halves into a complete ambient orthonormal
basis. Its left and right halves lie in the source and its complement,
and its paired columns express a full basis of the target. -/
theorem exists_ambient_orthonormalBasis_cos_sin_principalAngles
    (K L : Submodule 𝕜 E)
    (hKL : Module.finrank 𝕜 K = Module.finrank 𝕜 L)
    (hcomp : Module.finrank 𝕜 Kᗮ = Module.finrank 𝕜 L) :
    ∃ b : OrthonormalBasis
        (Fin (Module.finrank 𝕜 L) ⊕ Fin (Module.finrank 𝕜 L)) 𝕜 E,
      ∃ w : OrthonormalBasis (Fin (Module.finrank 𝕜 L)) 𝕜 L,
        (∀ i, b (Sum.inl i) ∈ K) ∧ (∀ i, b (Sum.inr i) ∈ Kᗮ) ∧
          ∀ i, (w i : E) =
            ((Real.cos (K.principalAngles L i) : ℝ) : 𝕜) • b (Sum.inl i) +
              ((Real.sin (K.principalAngles L i) : ℝ) : 𝕜) • b (Sum.inr i) := by
  obtain ⟨u, v, w, hw⟩ := K.exists_orthonormalBases_cos_sin_principalAngles L hKL hcomp
  let b := (u.prod v).map K.orthogonalDecomposition.symm
  have hu (i) : b (Sum.inl i) = (u i : E) := by
    simp [b, OrthonormalBasis.prod_apply]
  have hv (i) : b (Sum.inr i) = (v i : E) := by
    simp [b, OrthonormalBasis.prod_apply]
  exact ⟨b, w, fun i => hu i ▸ (u i).property,
    fun i => hv i ▸ (v i).property, fun i => by rw [hu, hv]; exact hw i⟩

/-- The usual balanced ambient dimension implies the dimension hypotheses
of the complete cosine--sine basis construction. -/
theorem exists_ambient_orthonormalBasis_cos_sin_principalAngles_of_finrank_eq_twice
    (K L : Submodule 𝕜 E)
    (hKL : Module.finrank 𝕜 K = Module.finrank 𝕜 L)
    (hdim : Module.finrank 𝕜 E = 2 * Module.finrank 𝕜 L) :
    ∃ b : OrthonormalBasis
        (Fin (Module.finrank 𝕜 L) ⊕ Fin (Module.finrank 𝕜 L)) 𝕜 E,
      ∃ w : OrthonormalBasis (Fin (Module.finrank 𝕜 L)) 𝕜 L,
        (∀ i, b (Sum.inl i) ∈ K) ∧ (∀ i, b (Sum.inr i) ∈ Kᗮ) ∧
          ∀ i, (w i : E) =
            ((Real.cos (K.principalAngles L i) : ℝ) : 𝕜) • b (Sum.inl i) +
              ((Real.sin (K.principalAngles L i) : ℝ) : 𝕜) • b (Sum.inr i) := by
  apply exists_ambient_orthonormalBasis_cos_sin_principalAngles K L hKL
  have hsum := K.finrank_add_finrank_orthogonal
  omega

/-- In a complete cosine--sine basis the two actual projection matrices
have the standard source block and the cosine--sine target blocks. The
entries use the accepted principal angles, including their full zero and
right-angle multiplicities. -/
theorem exists_cosineSine_projection_matrices
    (K L : Submodule 𝕜 E)
    (hKL : Module.finrank 𝕜 K = Module.finrank 𝕜 L)
    (hdim : Module.finrank 𝕜 E = 2 * Module.finrank 𝕜 L) :
    ∃ b : OrthonormalBasis
        (Fin (Module.finrank 𝕜 L) ⊕ Fin (Module.finrank 𝕜 L)) 𝕜 E,
      LinearMap.toMatrixOrthonormal b K.starProjection.toLinearMap =
        Matrix.fromBlocks 1 0 0 0 ∧
      LinearMap.toMatrixOrthonormal b L.starProjection.toLinearMap =
        Matrix.fromBlocks
          (Matrix.diagonal (fun i : Fin (Module.finrank 𝕜 L) =>
            ((Real.cos (K.principalAngles L i)^2 : ℝ) : 𝕜)))
          (Matrix.diagonal (fun i : Fin (Module.finrank 𝕜 L) => ((Real.cos (K.principalAngles L i) *
            Real.sin (K.principalAngles L i) : ℝ) : 𝕜)))
          (Matrix.diagonal (fun i : Fin (Module.finrank 𝕜 L) => ((Real.cos (K.principalAngles L i) *
            Real.sin (K.principalAngles L i) : ℝ) : 𝕜)))
          (Matrix.diagonal (fun i : Fin (Module.finrank 𝕜 L) =>
            ((Real.sin (K.principalAngles L i)^2 : ℝ) : 𝕜))) := by
  classical
  obtain ⟨b, w, hbK, hbO, hw⟩ :=
    K.exists_ambient_orthonormalBasis_cos_sin_principalAngles_of_finrank_eq_twice L hKL hdim
  have hPK (i) : K.starProjection (b (Sum.inl i)) = b (Sum.inl i) :=
    K.starProjection_eq_self_iff.mpr (hbK i)
  have hPO (i) : K.starProjection (b (Sum.inr i)) = 0 :=
    K.starProjection_apply_eq_zero_iff.mpr (hbO i)
  have hproj (x : E) : L.starProjection x =
      ∑ i, ⟪(w i : E), x⟫_𝕜 • (w i : E) := by
    rw [w.starProjection_eq_sum_rankOne]
    simp only [sum_apply, InnerProductSpace.rankOne_apply]
  have hwl (i j) : ⟪(w i : E), b (Sum.inl j)⟫_𝕜 =
      if i = j then ((Real.cos (K.principalAngles L i) : ℝ) : 𝕜) else 0 := by
    rw [hw i]
    simp only [inner_add_left, inner_smul_left, RCLike.conj_ofReal, b.inner_eq_ite,
      Sum.inl.injEq, Sum.inr_ne_inl, ite_false, mul_zero, add_zero]
    split_ifs <;> simp_all
  have hwr (i j) : ⟪(w i : E), b (Sum.inr j)⟫_𝕜 =
      if i = j then ((Real.sin (K.principalAngles L i) : ℝ) : 𝕜) else 0 := by
    rw [hw i]
    simp only [inner_add_left, inner_smul_left, RCLike.conj_ofReal, b.inner_eq_ite,
      Sum.inr.injEq, Sum.inl_ne_inr, ite_false, mul_zero, zero_add]
    split_ifs <;> simp_all
  have hPL (j) : L.starProjection (b (Sum.inl j)) =
      ((Real.cos (K.principalAngles L j) : ℝ) : 𝕜) • (w j : E) := by
    rw [hproj]
    simp [hwl, ite_smul]
  have hPR (j) : L.starProjection (b (Sum.inr j)) =
      ((Real.sin (K.principalAngles L j) : ℝ) : 𝕜) • (w j : E) := by
    rw [hproj]
    simp [hwr, ite_smul]
  refine ⟨b, ?_, ?_⟩
  · ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [LinearMap.toMatrixOrthonormal_apply_apply, hPK, hPO,
        b.inner_eq_ite, Matrix.fromBlocks, Matrix.one_apply]
  · ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [LinearMap.toMatrixOrthonormal_apply_apply, ContinuousLinearMap.coe_coe,
        hPL, hPR, hw, inner_smul_right, inner_add_right, b.inner_eq_ite,
        Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, ite_false,
        mul_zero, zero_add, add_zero, Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl,
        Sum.elim_inr, Matrix.diagonal_apply] <;>
      split_ifs with hij <;> simp [hij, RCLike.ofReal_pow, RCLike.ofReal_mul] <;> ring

end Submodule
