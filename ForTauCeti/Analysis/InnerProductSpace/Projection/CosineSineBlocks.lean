/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Projection.CosineSineFrame
public import ForTauCeti.Analysis.InnerProductSpace.Projection.InvariantSubspace
public import TauCeti.LinearAlgebra.Trace.Idempotent
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Actual reducing blocks selected from a positive principal-angle frame

An injective ordered selection of `n` positive principal angles generates
a genuine `2*n` dimensional reducing subspace. Its source and target
intersections have dimension `n`, and their accepted principal angles
are exactly the selected angles, with the given labels. The ambient
dimension is arbitrary. Trace of the actual restricted projections gives
the ranks; the sorted Gram-eigenbasis theorem recovers the angles.
-/

public section

noncomputable section

namespace Submodule

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Span of the selected source and complementary frame vectors. The
definition exposes the actual generators for subsequent disjoint-orbit
orthogonality and span arguments. -/
@[expose] def cosineSineFrameBlock
    {K L : Submodule 𝕜 E} {n : ℕ}
    (u : OrthonormalBasis (Fin (Module.finrank 𝕜 L)) 𝕜 K)
    (v : Fin (Module.finrank 𝕜 L) → Kᗮ) (e : Fin n ↪ Fin (Module.finrank 𝕜 L)) :
    Submodule 𝕜 E :=
  span 𝕜 (Set.range (Sum.elim (fun i => (u (e i) : E)) (fun i => (v (e i) : E))))

private theorem finrank_eq_of_trace_starProjection
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (K : Submodule 𝕜 F) (n : ℕ)
    (htrace : LinearMap.trace 𝕜 F K.starProjection.toLinearMap = (n : 𝕜)) :
    Module.finrank 𝕜 K = n := by
  have hidem : IsIdempotentElem K.starProjection.toLinearMap := by
    change K.starProjection.toLinearMap * K.starProjection.toLinearMap =
      K.starProjection.toLinearMap
    exact congrArg ContinuousLinearMap.toLinearMap K.isIdempotentElem_starProjection.eq
  have h := LinearMap.trace_eq_finrank_range_of_isIdempotentElem hidem
  have hrange : K.starProjection.toLinearMap.range = K := K.range_starProjection
  rw [hrange, htrace] at h
  exact_mod_cast h.symm

/-- A selected collection of positive principal planes is an actual
reducing block of the original pair, with exact dimension, source/target
ranks and accepted angle labels. The selection may be empty and may
contain repeated or right principal angles. -/
theorem cosineSineFrameBlock_data
    (K L : Submodule 𝕜 E)
    (u : OrthonormalBasis (Fin (Module.finrank 𝕜 L)) 𝕜 K)
    (w : OrthonormalBasis (Fin (Module.finrank 𝕜 L)) 𝕜 L)
    (v : Fin (Module.finrank 𝕜 L) → Kᗮ)
    (hgram : ∀ i j, ⟪v i, v j⟫_𝕜 =
      if i = j ∧ 0 < K.principalAngles L i then 1 else 0)
    (hdecomp : ∀ i, (w i : E) =
      ((Real.cos (K.principalAngles L i) : ℝ) : 𝕜) • (u i : E) +
        ((Real.sin (K.principalAngles L i) : ℝ) : 𝕜) • (v i : E))
    (hLu : ∀ i, L.starProjection (u i : E) =
      ((Real.cos (K.principalAngles L i) : ℝ) : 𝕜) • (w i : E))
    (hLv : ∀ i, L.starProjection (v i : E) =
      ((Real.sin (K.principalAngles L i) : ℝ) : 𝕜) • (w i : E))
    {n : ℕ} (e : Fin n ↪ Fin (Module.finrank 𝕜 L))
    (hpos : ∀ i, 0 < K.principalAngles L (e i))
    (horder : Antitone (fun i => K.principalAngles L (e i))) :
    let W := cosineSineFrameBlock u v e
    Module.finrank 𝕜 W = 2*n ∧
      (∀ x ∈ W, K.starProjection x ∈ W) ∧
      (∀ x ∈ W, L.starProjection x ∈ W) ∧
      Module.finrank 𝕜 (K.comap W.subtype) = n ∧
      Module.finrank 𝕜 (L.comap W.subtype) = n ∧
      ∀ i : Fin n, (K.comap W.subtype).principalAngles (L.comap W.subtype) i =
        K.principalAngles L (e i) := by
  classical
  let f : Fin n ⊕ Fin n → E :=
    Sum.elim (fun i => (u (e i) : E)) (fun i => (v (e i) : E))
  let W := cosineSineFrameBlock u v e
  have hon : Orthonormal 𝕜 f := by
    rw [orthonormal_iff_ite]
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · simpa only [f, Sum.elim_inl, Sum.inl.injEq, ← K.coe_inner, e.injective.eq_iff]
        using u.inner_eq_ite (e i) (e j)
    · exact Submodule.inner_right_of_mem_orthogonal (u (e i)).property (v (e j)).property
    · exact inner_eq_zero_symm.mpr
        (Submodule.inner_right_of_mem_orthogonal (u (e j)).property (v (e i)).property)
    · simpa only [f, Sum.elim_inr, Sum.inr.injEq, ← (Kᗮ).coe_inner, hpos i,
        and_true, e.injective.eq_iff] using hgram (e i) (e j)
  let bb := Module.Basis.span hon.linearIndependent
  have hbb : Orthonormal 𝕜 (bb : Fin n ⊕ Fin n → W) := by
    rw [orthonormal_iff_ite]
    intro i j
    simpa only [bb, Module.Basis.span_apply] using
      orthonormal_iff_ite.mp (orthonormal_span hon) i j
  let b : OrthonormalBasis (Fin n ⊕ Fin n) 𝕜 W := bb.toOrthonormalBasis hbb
  have hb (j) : (b j : E) = f j := by
    change ((bb.toOrthonormalBasis hbb : _ → W) j : E) = f j
    rw [Module.Basis.coe_toOrthonormalBasis]
    exact Module.Basis.coe_span_apply _ _
  have hleft (i) : f (Sum.inl i) ∈ W := Submodule.subset_span (Set.mem_range_self _)
  have hright (i) : f (Sum.inr i) ∈ W := Submodule.subset_span (Set.mem_range_self _)
  have hw (i) : (w (e i) : E) ∈ W := by
    rw [hdecomp]
    exact W.add_mem (W.smul_mem _ (hleft i)) (W.smul_mem _ (hright i))
  have hKf (i) : K.starProjection (f (Sum.inl i)) = f (Sum.inl i) :=
    K.starProjection_eq_self_iff.mpr (u (e i)).property
  have hKv (i) : K.starProjection (f (Sum.inr i)) = 0 :=
    K.starProjection_apply_eq_zero_iff.mpr (v (e i)).property
  have hK : ∀ x ∈ W, K.starProjection x ∈ W := by
    have hle : W ≤ W.comap K.starProjection.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change K.starProjection (f i) ∈ W
      rcases i with i | i
      · rw [hKf]; exact hleft i
      · rw [hKv]; exact W.zero_mem
    exact fun _ hx => hle hx
  have hL : ∀ x ∈ W, L.starProjection x ∈ W := by
    have hle : W ≤ W.comap L.starProjection.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change L.starProjection (f i) ∈ W
      rcases i with i | i
      · change L.starProjection (u (e i) : E) ∈ W
        rw [hLu]; exact W.smul_mem _ (hw i)
      · change L.starProjection (v (e i) : E) ∈ W
        rw [hLv]; exact W.smul_mem _ (hw i)
    exact fun _ hx => hle hx
  let K₀ := K.comap W.subtype
  let L₀ := L.comap W.subtype
  have hPK (i) : K₀.starProjection (b (Sum.inl i)) = b (Sum.inl i) := by
    apply Subtype.ext
    rw [K.starProjection_comap_subtype_apply_of_invariant W hK, hb, hKf]
  have hPV (i) : K₀.starProjection (b (Sum.inr i)) = 0 := by
    apply Subtype.ext
    rw [K.starProjection_comap_subtype_apply_of_invariant W hK, hb, hKv]
    rfl
  let z (i : Fin n) : W := ⟨w (e i), hw i⟩
  have hz (i) : z i =
      ((Real.cos (K.principalAngles L (e i)) : ℝ) : 𝕜) • b (Sum.inl i) +
        ((Real.sin (K.principalAngles L (e i)) : ℝ) : 𝕜) • b (Sum.inr i) := by
    apply Subtype.ext
    simpa only [Submodule.coe_add, Submodule.coe_smul, hb, z, f,
      Sum.elim_inl, Sum.elim_inr] using hdecomp (e i)
  have hQL (i) : L₀.starProjection (b (Sum.inl i)) =
      ((Real.cos (K.principalAngles L (e i)) : ℝ) : 𝕜) • z i := by
    apply Subtype.ext
    rw [L.starProjection_comap_subtype_apply_of_invariant W hL, hb]
    exact hLu (e i)
  have hQR (i) : L₀.starProjection (b (Sum.inr i)) =
      ((Real.sin (K.principalAngles L (e i)) : ℝ) : 𝕜) • z i := by
    apply Subtype.ext
    rw [L.starProjection_comap_subtype_apply_of_invariant W hL, hb]
    exact hLv (e i)
  have hrankK : Module.finrank 𝕜 K₀ = n := by
    apply finrank_eq_of_trace_starProjection
    rw [LinearMap.trace_eq_sum_inner _ b, Fintype.sum_sum_type]
    simp [hPK, hPV]
  have hrankL : Module.finrank 𝕜 L₀ = n := by
    apply finrank_eq_of_trace_starProjection
    rw [LinearMap.trace_eq_sum_inner _ b, Fintype.sum_sum_type]
    simp only [ContinuousLinearMap.coe_coe, hQL, hQR, hz, inner_smul_right,
      inner_add_right, b.inner_eq_ite,
      Sum.inl_ne_inr, Sum.inr_ne_inl, ite_true, ite_false, mul_one, mul_zero,
      add_zero, zero_add]
    rw [← Finset.sum_add_distrib]
    simp only [← pow_two, ← RCLike.ofReal_pow, ← RCLike.ofReal_add,
      Real.cos_sq_add_sin_sq, RCLike.ofReal_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  let u₀ (i : Fin n) : K₀ := ⟨b (Sum.inl i), K₀.starProjection_eq_self_iff.mp (hPK i)⟩
  let w₀ (i : Fin n) : L₀ := ⟨z i, (w (e i)).property⟩
  let v₀ (i : Fin n) : K₀ᗮ := ⟨b (Sum.inr i), K₀.starProjection_apply_eq_zero_iff.mp (hPV i)⟩
  have hu₀ : Orthonormal 𝕜 u₀ := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [u₀, K₀.coe_inner, b.inner_eq_ite, Sum.inl.injEq]
  have hw₀ : Orthonormal 𝕜 w₀ := by
    rw [orthonormal_iff_ite]
    intro i j
    simpa only [w₀, z, L₀.coe_inner, W.coe_inner, ← L.coe_inner, e.injective.eq_iff]
      using w.inner_eq_ite (e i) (e j)
  have hv₀ : Orthonormal 𝕜 v₀ := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [v₀, (K₀ᗮ).coe_inner, b.inner_eq_ite, Sum.inr.injEq]
  let ub := OrthonormalBasis.mk hu₀
    ((hu₀.linearIndependent.span_eq_top_of_card_eq_finrank'
      (by simpa only [Fintype.card_fin] using hrankK.symm)).ge)
  let wb := OrthonormalBasis.mk hw₀
    ((hw₀.linearIndependent.span_eq_top_of_card_eq_finrank'
      (by simpa only [Fintype.card_fin] using hrankL.symm)).ge)
  refine ⟨?_, hK, hL, hrankK, hrankL, ?_⟩
  · rw [Module.finrank_eq_card_basis b.toBasis, Fintype.card_sum, Fintype.card_fin]
    omega
  · apply K₀.principalAngles_eq_of_cosineSine_frame L₀ ub wb v₀ hv₀ _ horder
      (fun i => ⟨(hpos i).le, K.principalAngles_le_pi_div_two L (e i)⟩)
    intro i
    simpa only [ub, wb, OrthonormalBasis.coe_mk, u₀, w₀, v₀] using hz i

/-- Disjoint selections of positive labels generate orthogonal actual
principal-plane blocks. No numerical separation of their angles is needed. -/
theorem orthogonalFamily_cosineSineFrameBlock
    (K L : Submodule 𝕜 E)
    (u : OrthonormalBasis (Fin (Module.finrank 𝕜 L)) 𝕜 K)
    (v : Fin (Module.finrank 𝕜 L) → Kᗮ)
    (hgram : ∀ i j, ⟪v i, v j⟫_𝕜 =
      if i = j ∧ 0 < K.principalAngles L i then 1 else 0)
    {ι : Type*} (n : ι → ℕ) (e : ∀ i, Fin (n i) ↪ Fin (Module.finrank 𝕜 L))
    (hdisjoint : ∀ i j, i ≠ j → ∀ a b, e i a ≠ e j b) :
    OrthogonalFamily 𝕜 (fun i => cosineSineFrameBlock u v (e i))
      (fun i => (cosineSineFrameBlock u v (e i)).subtypeₗᵢ) := by
  classical
  apply OrthogonalFamily.of_pairwise
  intro i j hij
  apply Submodule.isOrtho_span.mpr
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rcases a with a | a <;> rcases b with b | b
  · simp only [Sum.elim_inl, ← K.coe_inner, u.inner_eq_ite,
      ite_eq_right (hdisjoint i j hij a b)]
  · exact Submodule.inner_right_of_mem_orthogonal (u (e i a)).property (v (e j b)).property
  · exact inner_eq_zero_symm.mpr
      (Submodule.inner_right_of_mem_orthogonal (u (e j b)).property (v (e i a)).property)
  · simp only [Sum.elim_inr, ← (Kᗮ).coe_inner, hgram, hdisjoint i j hij a b,
      false_and, ite_false]

/-- A covering selection of positive labels exhausts precisely the
active cosine--sine space. The orthogonal complement is the entire common
summand, regardless of the ambient dimension or the number of zero angles. -/
theorem iSup_cosineSineFrameBlock_eq_active
    (K L : Submodule 𝕜 E)
    (u : OrthonormalBasis (Fin (Module.finrank 𝕜 L)) 𝕜 K)
    (v : Fin (Module.finrank 𝕜 L) → Kᗮ)
    {ι : Type*} (n : ι → ℕ) (e : ∀ i, Fin (n i) ↪ Fin (Module.finrank 𝕜 L))
    (hpos : ∀ i a, 0 < K.principalAngles L (e i a))
    (hcover : ∀ j : Fin (Module.finrank 𝕜 L), 0 < K.principalAngles L j →
      ∃ i a, e i a = j) :
    (⨆ i, cosineSineFrameBlock u v (e i)) =
      span 𝕜 (Set.range (Sum.elim
        (fun i : {j : Fin (Module.finrank 𝕜 L) // 0 < K.principalAngles L j} => (u i.val : E))
        (fun i : {j : Fin (Module.finrank 𝕜 L) // 0 < K.principalAngles L j} =>
          (v i.val : E)))) := by
  apply le_antisymm
  · apply iSup_le
    intro i
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    apply Submodule.subset_span
    rcases a with a | a
    · exact ⟨Sum.inl ⟨e i a, hpos i a⟩, rfl⟩
    · exact ⟨Sum.inr ⟨e i a, hpos i a⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    rcases a with a | a
    · obtain ⟨i, b, hb⟩ := hcover a.val a.property
      apply (le_iSup (fun i => cosineSineFrameBlock u v (e i)) i)
      apply Submodule.subset_span
      exact ⟨Sum.inl b, by simp only [Sum.elim_inl, hb]⟩
    · obtain ⟨i, b, hb⟩ := hcover a.val a.property
      apply (le_iSup (fun i => cosineSineFrameBlock u v (e i)) i)
      apply Submodule.subset_span
      exact ⟨Sum.inr b, by simp only [Sum.elim_inr, hb]⟩

end Submodule
