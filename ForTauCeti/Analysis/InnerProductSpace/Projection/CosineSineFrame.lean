/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.ScaledOrthonormalExtension
public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Principal-angle frames without a balanced ambient dimension

For equal-rank subspaces, the sine embedding of the target into the
source complement gives an accepted ordered singular system. Complete
only the cosine-scaled images into a source basis. The complementary
vectors are the actual left singular vectors: they are orthonormal at
positive angles and vanish at zero angles. Thus no artificial complement
directions are needed when the source rank exceeds half the ambient
dimension. Zero, repeated and right angles retain their original labels.
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

/-- For equal-rank subspaces, the target's sine embedding into the
source complement has exactly the accepted principal-sine sequence. -/
theorem principalSines_eq_singularValues_sineEmbedding
    (K L : Submodule 𝕜 E) (hKL : Module.finrank 𝕜 K = Module.finrank 𝕜 L) :
    K.principalSines L =
      (Kᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ L.subtype).singularValues := by
  let A := Kᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ L.subtype
  have h := K.principalSines_range_eq_singularValues (X := L.subtypeL) L.subtypeₗᵢ.isometry
  have hrange : L.subtypeL.range = L := L.range_subtype
  have hincl : Kᗮ.subtypeₗᵢ.toLinearMap ∘ₗ A =
      (Kᗮ.starProjection ∘L L.subtypeL).toLinearMap := by ext x; rfl
  rw [← LinearMap.singularValues_linearIsometry_comp Kᗮ.subtypeₗᵢ A, hincl]
  simpa only [hrange, K.principalSines_comm L hKL] using h

/-- Every equal-rank finite pair has a full source basis, a full target
basis and complementary vectors with the actual accepted principal angles.
Only positive-angle complementary vectors are unit vectors; the zero
columns vanish. There is no restriction on ambient dimension or rank. -/
theorem exists_cosineSine_principalAngle_frame
    (K L : Submodule 𝕜 E) (hKL : Module.finrank 𝕜 K = Module.finrank 𝕜 L) :
    ∃ u : OrthonormalBasis (Fin (Module.finrank 𝕜 L)) 𝕜 K,
      ∃ w : OrthonormalBasis (Fin (Module.finrank 𝕜 L)) 𝕜 L,
        ∃ v : Fin (Module.finrank 𝕜 L) → Kᗮ,
          (∀ i j, ⟪v i, v j⟫_𝕜 =
            if i = j ∧ 0 < K.principalAngles L i then 1 else 0) ∧
          (∀ i, K.starProjection (w i : E) =
            ((Real.cos (K.principalAngles L i) : ℝ) : 𝕜) • (u i : E)) ∧
          (∀ i, Kᗮ.starProjection (w i : E) =
            ((Real.sin (K.principalAngles L i) : ℝ) : 𝕜) • (v i : E)) ∧
          (∀ i, (w i : E) =
            ((Real.cos (K.principalAngles L i) : ℝ) : 𝕜) • (u i : E) +
              ((Real.sin (K.principalAngles L i) : ℝ) : 𝕜) • (v i : E)) ∧
          (∀ i, L.starProjection (u i : E) =
            ((Real.cos (K.principalAngles L i) : ℝ) : 𝕜) • (w i : E)) ∧
          ∀ i, L.starProjection (v i : E) =
            ((Real.sin (K.principalAngles L i) : ℝ) : 𝕜) • (w i : E) := by
  classical
  let A : L →ₗ[𝕜] Kᗮ := Kᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ L.subtype
  let B : L →ₗ[𝕜] K := K.orthogonalProjectionOnto.toLinearMap ∘ₗ L.subtype
  let w := A.rightSingularBasis
  have hsv : A.singularValues = K.principalSines L :=
    (K.principalSines_eq_singularValues_sineEmbedding L hKL).symm
  have hs (i : Fin (Module.finrank 𝕜 L)) :
      A.singularValues i = Real.sin (K.principalAngles L i) := by
    rw [hsv]
    exact (K.sin_principalAngles L i).symm
  have hspos (i : Fin (Module.finrank 𝕜 L)) :
      A.singularValues i ≠ 0 ↔ 0 < K.principalAngles L i := by
    rw [hs]
    constructor
    · intro hi
      exact lt_of_le_of_ne (K.principalAngles_nonneg L i) (fun hz => by simp [← hz] at hi)
    · intro hi
      exact (Real.sin_pos_of_pos_of_lt_pi hi
        ((K.principalAngles_le_pi_div_two L i).trans_lt (by linarith [Real.pi_pos]))).ne'
  have hAi (i j : Fin (Module.finrank 𝕜 L)) :
      ⟪A (w i), A (w j)⟫_𝕜 =
        if i = j then ((Real.sin (K.principalAngles L i)^2 : ℝ) : 𝕜) else 0 := by
    rw [A.inner_apply_rightSingularBasis, w.inner_eq_ite, hs]
    split_ifs <;> simp_all
  have hBi (i j : Fin (Module.finrank 𝕜 L)) :
      ⟪B (w i), B (w j)⟫_𝕜 =
        if i = j then ((Real.cos (K.principalAngles L i)^2 : ℝ) : 𝕜) else 0 := by
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
  have hsource (i) : K.starProjection (w i : E) =
      ((Real.cos (K.principalAngles L i) : ℝ) : 𝕜) • (u i : E) :=
    congrArg Subtype.val (hu i)
  have hcomplement (i) : Kᗮ.starProjection (w i : E) =
      ((Real.sin (K.principalAngles L i) : ℝ) : 𝕜) • (A.leftSingularVector i : E) := by
    have h := A.apply_rightSingularBasis i
    rw [hs] at h
    exact congrArg Subtype.val h
  let v := A.leftSingularVector
  have hgram (i j) : ⟪v i, v j⟫_𝕜 =
      if i = j ∧ 0 < K.principalAngles L i then 1 else 0 := by
    simpa only [hspos] using A.inner_leftSingularVector i j
  have hdecomp (i) : (w i : E) =
      ((Real.cos (K.principalAngles L i) : ℝ) : 𝕜) • (u i : E) +
        ((Real.sin (K.principalAngles L i) : ℝ) : 𝕜) • (v i : E) := by
    rw [← hsource, ← hcomplement]
    exact (K.starProjection_add_starProjection_orthogonal (w i)).symm
  have hproj (x : E) : L.starProjection x =
      ∑ i, ⟪(w i : E), x⟫_𝕜 • (w i : E) := by
    rw [w.starProjection_eq_sum_rankOne]
    simp only [sum_apply, InnerProductSpace.rankOne_apply]
  have huu (i j) : ⟪(u i : E), (u j : E)⟫_𝕜 = if i = j then 1 else 0 := u.inner_eq_ite i j
  have huv (i j) : ⟪(u i : E), (v j : E)⟫_𝕜 = 0 :=
    Submodule.inner_right_of_mem_orthogonal (u i).property (v j).property
  have hvu (i j) : ⟪(v i : E), (u j : E)⟫_𝕜 = 0 := inner_eq_zero_symm.mpr (huv j i)
  have hwu (i j) : ⟪(w i : E), (u j : E)⟫_𝕜 =
      if i = j then ((Real.cos (K.principalAngles L i) : ℝ) : 𝕜) else 0 := by
    rw [hdecomp, inner_add_left, inner_smul_left, inner_smul_left, huu, hvu]
    simp only [RCLike.conj_ofReal, mul_zero, add_zero]
    split_ifs <;> simp
  have hwv (i j) : ⟪(w i : E), (v j : E)⟫_𝕜 =
      if i = j then ((Real.sin (K.principalAngles L i) : ℝ) : 𝕜) else 0 := by
    rw [hdecomp, inner_add_left, inner_smul_left, inner_smul_left, huv]
    simp only [mul_zero, zero_add, RCLike.conj_ofReal]
    change ((Real.sin (K.principalAngles L i) : ℝ) : 𝕜) * ⟪v i, v j⟫_𝕜 = _
    rw [hgram]
    by_cases hij : i = j
    · subst j
      by_cases hi : 0 < K.principalAngles L i
      · simp [hi]
      · have hz : K.principalAngles L i = 0 :=
          le_antisymm (le_of_not_gt hi) (K.principalAngles_nonneg L i)
        simp [hz]
    · simp [hij]
  refine ⟨u, w, v, hgram, hsource, hcomplement, hdecomp, ?_, ?_⟩
  · intro i
    rw [hproj]
    simp [hwu, ite_smul]
  · intro i
    rw [hproj]
    simp [hwv, ite_smul]

/-- The two halves of the positive-angle frame are jointly orthonormal.
In particular every positive angle has an actual orthogonal principal
plane, including every crossed right-angle direction. -/
theorem cosineSine_principalAngle_active_orthonormal
    (K L : Submodule 𝕜 E)
    (u : OrthonormalBasis (Fin (Module.finrank 𝕜 L)) 𝕜 K)
    (v : Fin (Module.finrank 𝕜 L) → Kᗮ)
    (hgram : ∀ i j, ⟪v i, v j⟫_𝕜 =
      if i = j ∧ 0 < K.principalAngles L i then 1 else 0) :
    Orthonormal 𝕜
      (Sum.elim
        (fun i : {j : Fin (Module.finrank 𝕜 L) // 0 < K.principalAngles L j} => (u i.val : E))
        (fun i : {j : Fin (Module.finrank 𝕜 L) // 0 < K.principalAngles L j} =>
          (v i.val : E))) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · simpa only [Sum.elim_inl, Sum.inl.injEq, Subtype.ext_iff, ← K.coe_inner]
      using u.inner_eq_ite i.val j.val
  · change ⟪(u i.val : E), (v j.val : E)⟫_𝕜 = 0
    exact Submodule.inner_right_of_mem_orthogonal (u i.val).property (v j.val).property
  · change ⟪(v i.val : E), (u j.val : E)⟫_𝕜 = 0
    exact inner_eq_zero_symm.mpr
      (Submodule.inner_right_of_mem_orthogonal (u j.val).property (v i.val).property)
  · simpa only [Sum.elim_inr, Sum.inr.injEq, i.property, and_true, Subtype.ext_iff,
      ← (Kᗮ).coe_inner]
      using hgram i.val j.val

/-- Outside the span of the actual positive-angle frame, the two
orthogonal projections agree. This is the whole common summand to be
fixed when gluing matching transports, in arbitrary ambient dimension. -/
theorem starProjection_eq_on_cosineSine_active_orthogonal
    (K L : Submodule 𝕜 E)
    (u : OrthonormalBasis (Fin (Module.finrank 𝕜 L)) 𝕜 K)
    (w : OrthonormalBasis (Fin (Module.finrank 𝕜 L)) 𝕜 L)
    (v : Fin (Module.finrank 𝕜 L) → Kᗮ)
    (hdecomp : ∀ i, (w i : E) =
      ((Real.cos (K.principalAngles L i) : ℝ) : 𝕜) • (u i : E) +
        ((Real.sin (K.principalAngles L i) : ℝ) : 𝕜) • (v i : E))
    (x : E)
    (hx : x ∈ (Submodule.span 𝕜 (Set.range
      (Sum.elim
        (fun i : {j : Fin (Module.finrank 𝕜 L) // 0 < K.principalAngles L j} => (u i.val : E))
        (fun i : {j : Fin (Module.finrank 𝕜 L) // 0 < K.principalAngles L j} =>
          (v i.val : E)))))ᗮ) :
    K.starProjection x = L.starProjection x := by
  classical
  rw [u.starProjection_eq_sum_rankOne, w.starProjection_eq_sum_rankOne]
  simp only [sum_apply, InnerProductSpace.rankOne_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0 < K.principalAngles L i
  · have hu : ⟪(u i : E), x⟫_𝕜 = 0 :=
      (Submodule.mem_orthogonal _ _).mp hx _
        (Submodule.subset_span (Set.mem_range.mpr ⟨Sum.inl ⟨i, hi⟩, rfl⟩))
    have hv : ⟪(v i : E), x⟫_𝕜 = 0 :=
      (Submodule.mem_orthogonal _ _).mp hx _
        (Submodule.subset_span (Set.mem_range.mpr ⟨Sum.inr ⟨i, hi⟩, rfl⟩))
    have hw : ⟪(w i : E), x⟫_𝕜 = 0 := by
      rw [hdecomp, inner_add_left, inner_smul_left, inner_smul_left, hu, hv, mul_zero,
        mul_zero, add_zero]
    rw [hu, hw, zero_smul, zero_smul]
  · have hz : K.principalAngles L i = 0 :=
      le_antisymm (le_of_not_gt hi) (K.principalAngles_nonneg L i)
    have heq : (w i : E) = (u i : E) := by
      simpa only [hz, Real.cos_zero, Real.sin_zero, RCLike.ofReal_one, RCLike.ofReal_zero,
        one_smul, zero_smul, add_zero] using hdecomp i
    rw [heq]

/-- Conversely, a sorted cosine--sine frame computes the accepted angles
of its actual subspace pair. The complement vectors need only be an
orthonormal family. Compute the sine embedding's Gram operator in the
target basis and use the accepted sorted Gram-eigenbasis singular-value
theorem, including repeated and zero eigenvalues. -/
theorem principalAngles_eq_of_cosineSine_frame
    (K L : Submodule 𝕜 E) {n : ℕ}
    (u : OrthonormalBasis (Fin n) 𝕜 K)
    (w : OrthonormalBasis (Fin n) 𝕜 L)
    (v : Fin n → Kᗮ) (hv : Orthonormal 𝕜 v)
    (theta : Fin n → ℝ) (htheta : Antitone theta)
    (hrange : ∀ i, theta i ∈ Set.Icc 0 (Real.pi / 2))
    (hdecomp : ∀ i, (w i : E) =
      ((Real.cos (theta i) : ℝ) : 𝕜) • (u i : E) +
        ((Real.sin (theta i) : ℝ) : 𝕜) • (v i : E)) :
    ∀ i : Fin n, K.principalAngles L i = theta i := by
  classical
  have hKL : Module.finrank 𝕜 K = Module.finrank 𝕜 L := by
    rw [Module.finrank_eq_card_basis u.toBasis, Module.finrank_eq_card_basis w.toBasis]
  let A := Kᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ L.subtype
  have hA (i) : A (w i) = ((Real.sin (theta i) : ℝ) : 𝕜) • v i := by
    apply Subtype.ext
    change Kᗮ.starProjection (w i : E) = _
    rw [hdecomp, map_add, map_smul, map_smul,
      Kᗮ.starProjection_apply_eq_zero_iff.mpr
        (by simpa only [K.orthogonal_orthogonal] using (u i).property),
      Kᗮ.starProjection_eq_self_iff.mpr (v i).property, smul_zero, zero_add]
    rfl
  have hmu : Antitone (fun i => Real.sin (theta i)^2) := by
    intro i j hij
    have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi / 2) ≤ theta j by linarith [(hrange j).1, Real.pi_pos])
      (hrange i).2 (htheta hij)
    exact pow_le_pow_left₀
      (Real.sin_nonneg_of_nonneg_of_le_pi (hrange j).1
        ((hrange j).2.trans (by linarith [Real.pi_pos]))) hsin 2
  have hgram (i) : (A.adjoint ∘ₗ A) (w i) =
      ((Real.sin (theta i)^2 : ℝ) : 𝕜) • w i := by
    apply InnerProductSpace.ext_inner_right_basis w.toBasis
    intro j
    change ⟪A.adjoint (A (w i)), w j⟫_𝕜 =
      ⟪((Real.sin (theta i)^2 : ℝ) : 𝕜) • w i, w j⟫_𝕜
    rw [LinearMap.adjoint_inner_left, hA, hA, inner_smul_left, inner_smul_right,
      orthonormal_iff_ite.mp hv, inner_smul_left, w.inner_eq_ite]
    simp only [RCLike.conj_ofReal, RCLike.ofReal_pow]
    by_cases hij : i = j
    · subst j
      simp [pow_two]
    · simp [hij]
  intro i
  have hsq := A.sq_singularValues_eq_of_adjoint_comp_self_eigenbasis w hmu hgram i
  have hsin0 : 0 ≤ Real.sin (theta i) := Real.sin_nonneg_of_nonneg_of_le_pi
    (hrange i).1 ((hrange i).2.trans (by linarith [Real.pi_pos]))
  have hsv : A.singularValues i = Real.sin (theta i) :=
    (sq_eq_sq₀ (A.singularValues_nonneg i) hsin0).mp hsq
  rw [principalAngles_apply, K.principalSines_eq_singularValues_sineEmbedding L hKL, hsv]
  exact Real.arcsin_sin (by linarith [(hrange i).1, Real.pi_pos]) (hrange i).2

end Submodule
