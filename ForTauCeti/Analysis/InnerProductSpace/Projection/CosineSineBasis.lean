/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Projection.CosineSineFrame
public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Data.Matrix.Block

/-!
# Principal-angle cosine--sine bases, including both endpoints

Use the principal-angle frame constructed in arbitrary ambient dimension.
When source and complement have equal rank, complete its zero complementary
columns to a full complement basis with their original labels. The resulting
ambient chart uses the accepted ordered principal angles, including zero,
repeated and right angles, over either field and for the empty pair.
-/

public section

noncomputable section

namespace Submodule

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

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
  obtain ⟨u, w, v₀, hgram, hsource, hcomplement, _, _, _⟩ :=
    K.exists_cosineSine_principalAngle_frame L hKL
  let f (i : Fin (Module.finrank 𝕜 L)) := Kᗮ.orthogonalProjectionOnto (w i : E)
  have hf (i) : f i = ((Real.sin (K.principalAngles L i) : ℝ) : 𝕜) • v₀ i := by
    apply Subtype.ext
    exact hcomplement i
  have hinner (i j : Fin (Module.finrank 𝕜 L)) :
      ⟪f i, f j⟫_𝕜 =
        if i = j then ((Real.sin (K.principalAngles L i)^2 : ℝ) : 𝕜) else 0 := by
    rw [hf i, hf j, inner_smul_left, inner_smul_right, hgram]
    simp only [RCLike.conj_ofReal]
    by_cases hij : i = j
    · subst j
      by_cases hi : 0 < K.principalAngles L i
      · simp [hi, pow_two]
      · have hz : K.principalAngles L i = 0 :=
          le_antisymm (le_of_not_gt hi) (K.principalAngles_nonneg L i)
        simp [hz]
    · simp [hij]
  obtain ⟨v, hv⟩ := OrthonormalBasis.exists_smul_eq_of_inner_eq_ite
    (by simpa only [Fintype.card_fin] using hcomp) f
    (fun i => Real.sin (K.principalAngles L i)) hinner
  refine ⟨u, v, w, fun i => ?_⟩
  have hKv : Kᗮ.starProjection (w i) =
      ((Real.sin (K.principalAngles L i) : ℝ) : 𝕜) • (v i : E) :=
    congrArg Subtype.val (hv i)
  rw [← hsource, ← hKv]
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
