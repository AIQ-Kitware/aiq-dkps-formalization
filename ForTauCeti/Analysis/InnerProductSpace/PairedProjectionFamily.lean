/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.AnticommutingInvolution
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Independent projection parameters on conjugate unitary eigenspaces

A reversing involution pairs conjugate eigenspaces of a unitary. Select
distinct unit-circle eigenvalues with no conjugate coincidences. Arbitrary
orthogonal projections on their eigenspaces extend jointly and uniquely
to a commuting ambient projection supported on the selected paired sum.
-/

public section

noncomputable section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E]

omit [FiniteDimensional 𝕜 E] in
/-- Restricting an orthogonal projection to a complete invariant subspace
gives an orthogonal projection on that subspace. -/
theorem _root_.IsStarProjection.restrict_invariant
    {P : E →L[𝕜] E} (hP : IsStarProjection P)
    (N : Submodule 𝕜 E) [CompleteSpace N] (hN : ∀ x ∈ N, P x ∈ N) :
    IsStarProjection (P.restrict hN : N →L[𝕜] N) := by
  constructor
  · ext x
    exact congrArg (fun A : E →L[𝕜] E => A x) hP.isIdempotentElem
  · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    exact hP.isSelfAdjoint.isSymmetric.restrict_invariant hN

/-- Compatible orthogonal projections supported on selected conjugate
unitary eigenspace pairs. -/
@[expose] def unitaryPairedProjectionSpace
    (U : unitary (E →L[𝕜] E)) (J : E ≃ₗᵢ[𝕜] E) (mu : ι → 𝕜) : Set (E →L[𝕜] E) :=
  let N := fun i => Module.End.eigenspace (U : E →L[𝕜] E).toLinearMap (mu i)
  {P | IsStarProjection P ∧ Commute P (U : E →L[𝕜] E) ∧
    (∀ x, P (J x) = J (P x)) ∧ ∀ x, P x ∈ ⨆ i, N i ⊔ (N i).map J.toLinearMap}

/-- Projection parameters on distinct, nonconjugate unitary eigenspaces
extend jointly and uniquely to a compatible ambient projection supported
on their reflected sum. The eigenspaces are the actual ambient ones;
empty eigenspaces and an empty index set are allowed. -/
theorem exists_unique_unitary_paired_projection_family
    (U : unitary (E →L[𝕜] E)) (J : E ≃ₗᵢ[𝕜] E) (hJ : Function.Involutive J)
    (hrev : ∀ x, (U : E →L[𝕜] E) (J x) = J (star (U : E →L[𝕜] E) x))
    (mu : ι → 𝕜) (hmu : ∀ i, ‖mu i‖ = 1) (hinj : Function.Injective mu)
    (hconj : ∀ i j, mu i ≠ star (mu j))
    (Q : ∀ i, Module.End.eigenspace (U : E →L[𝕜] E).toLinearMap (mu i) →L[𝕜]
      Module.End.eigenspace (U : E →L[𝕜] E).toLinearMap (mu i))
    (hQ : ∀ i, IsStarProjection (Q i)) :
    let N := fun i => Module.End.eigenspace (U : E →L[𝕜] E).toLinearMap (mu i)
    let S := ⨆ i, N i ⊔ (N i).map J.toLinearMap
    ∃! P : E →L[𝕜] E, IsStarProjection P ∧ Commute P (U : E →L[𝕜] E) ∧
      (∀ x, P (J x) = J (P x)) ∧
      (∀ i (x : N i), P x = (Q i x : E)) ∧ ∀ x, P x ∈ S := by
  classical
  let N := fun i => Module.End.eigenspace (U : E →L[𝕜] E).toLinearMap (mu i)
  let M := fun i => (Q i).range.map (N i).subtype
  let S := ⨆ i, N i ⊔ (N i).map J.toLinearMap
  let A := ⨆ i, M i ⊔ (M i).map J.toLinearMap
  let R := Unitary.linearIsometryEquiv U
  have hMN (i) : M i ≤ N i := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hRx (i) (x : N i) : R x = mu i • (x : E) :=
    Module.End.mem_eigenspace_iff.mp x.property
  have hRJx (i) (x : N i) : R (J x) = star (mu i) • J x := by
    change (U : E →L[𝕜] E) (J x) = _
    rw [hrev, unitary_star_apply_of_apply_eq_smul U (mu i) (hmu i) x (hRx i x), map_smul]
  have hAsub : A ≤ S := iSup_mono fun i =>
    sup_le_sup (hMN i) (Submodule.map_mono (hMN i))
  have hRA : A.map R.toLinearMap ≤ A := by
    rw [Submodule.map_iSup]
    refine iSup_le fun i => ?_
    rw [Submodule.map_sup]
    refine sup_le ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      change R y ∈ A
      rw [hRx i ⟨y, hMN i hy⟩]
      exact A.smul_mem _ ((le_iSup (fun i => M i ⊔ (M i).map J.toLinearMap) i)
        (Submodule.mem_sup_left hy))
    · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      change R (J z) ∈ A
      rw [hRJx i ⟨z, hMN i hz⟩]
      exact A.smul_mem _ ((le_iSup (fun i => M i ⊔ (M i).map J.toLinearMap) i)
        (Submodule.mem_sup_right (Submodule.mem_map_of_mem hz)))
  have hJA : A.map J.toLinearMap ≤ A := by
    rw [Submodule.map_iSup]
    refine iSup_le fun i => ?_
    rw [Submodule.map_sup]
    refine sup_le ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      exact (le_iSup (fun i => M i ⊔ (M i).map J.toLinearMap) i)
        (Submodule.mem_sup_right (Submodule.mem_map_of_mem hy))
    · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      change J (J z) ∈ A
      rw [hJ]
      exact (le_iSup (fun i => M i ⊔ (M i).map J.toLinearMap) i)
        (Submodule.mem_sup_left hz)
  have hcomm (V : E ≃ₗᵢ[𝕜] E) (hV : A.map V.toLinearMap ≤ A) (x : E) :
      A.starProjection (V x) = V (A.starProjection x) := by
    have hmap : A.map V.toLinearMap = A :=
      Submodule.eq_of_le_of_finrank_eq hV (V.toLinearEquiv.finrank_map_eq A)
    have h := V.toLinearIsometry.map_starProjection A x
    change V (A.starProjection x) = (A.map V.toLinearMap).starProjection (V x) at h
    simpa only [hmap] using h.symm
  have hPN (i) (x : N i) : A.starProjection x = (Q i x : E) := by
    apply A.eq_starProjection_of_mem_of_inner_eq_zero
    · exact (le_iSup (fun i => M i ⊔ (M i).map J.toLinearMap) i)
        (Submodule.mem_sup_left (Submodule.mem_map_of_mem (show Q i x ∈ (Q i).range from ⟨x, rfl⟩)))
    · intro y hy
      refine Submodule.iSup_induction
        (motive := fun z : E => ⟪(x : E) - (Q i x : E), z⟫_𝕜 = 0) _ hy ?_ ?_ ?_
      · intro j z hz
        rcases Submodule.mem_sup.mp hz with ⟨u, ⟨u₀, hu₀, rfl⟩, v,
          ⟨w, ⟨w₀, hw₀, rfl⟩, rfl⟩, rfl⟩
        rw [inner_add_right]
        have hfirst : ⟪(x : E) - (Q i x : E), (u₀ : E)⟫_𝕜 = 0 := by
          by_cases hji : j = i
          · subst j
            change ⟪x - Q i x, u₀⟫_𝕜 = 0
            obtain ⟨_, heq⟩ := isStarProjection_iff_eq_starProjection_range.mp (hQ i)
            rw [show Q i x = (Q i).range.starProjection x from
              congrArg (fun B : N i →L[𝕜] N i => B x) heq]
            exact (Q i).range.starProjection_inner_eq_zero x u₀ hu₀
          · exact unitary_eigenvectors_inner_eq_zero_of_ne U (mu i) (mu j) (hmu i)
              (fun h => hji (hinj h.symm)) (x - Q i x) u₀ (hRx i (x - Q i x)) (hRx j u₀)
        have hsecond : ⟪(x : E) - (Q i x : E), J (w₀ : E)⟫_𝕜 = 0 :=
          unitary_eigenvectors_inner_eq_zero_of_ne U (mu i) (star (mu j)) (hmu i)
            (hconj i j) (x - Q i x) (J w₀) (hRx i (x - Q i x)) (hRJx j w₀)
        change ⟪(x : E) - (Q i x : E), (u₀ : E)⟫_𝕜 +
          ⟪(x : E) - (Q i x : E), J (w₀ : E)⟫_𝕜 = 0
        rw [hfirst, hsecond, add_zero]
      · exact inner_zero_right _
      · intro a b ha hb
        rw [inner_add_right, ha, hb, add_zero]
  refine ⟨A.starProjection, ⟨isStarProjection_starProjection, ?_, hcomm J hJA,
    hPN, fun x => hAsub (A.starProjection_apply_mem x)⟩, ?_⟩
  · ext x
    exact hcomm R hRA x
  · rintro P ⟨hP, _, hPJ, hPx, hPsupp⟩
    have hagree (x : E) (hx : x ∈ S) : P x = A.starProjection x := by
      refine Submodule.iSup_induction
        (motive := fun z : E => P z = A.starProjection z) _ hx ?_ ?_ ?_
      · intro i z hz
        rcases Submodule.mem_sup.mp hz with ⟨u, hu, v, ⟨w, hw, rfl⟩, rfl⟩
        change P (u + J w) = A.starProjection (u + J w)
        rw [map_add, map_add, hPJ, hcomm J hJA,
          hPx i ⟨u, hu⟩, hPN i ⟨u, hu⟩, hPx i ⟨w, hw⟩, hPN i ⟨w, hw⟩]
      · rw [map_zero, map_zero]
      · intro a b ha hb
        rw [map_add, map_add, ha, hb]
    have hsym : IsSelfAdjoint (P - A.starProjection) :=
      hP.isSelfAdjoint.sub isStarProjection_starProjection.isSelfAdjoint
    ext x
    apply sub_eq_zero.mp
    have hmem : (P - A.starProjection) x ∈ S :=
      S.sub_mem (hPsupp x) (hAsub (A.starProjection_apply_mem x))
    have hzero : (P - A.starProjection) ((P - A.starProjection) x) = 0 :=
      sub_eq_zero.mpr (hagree _ hmem)
    have hinner := hsym.isSymmetric ((P - A.starProjection) x) x
    change inner 𝕜 ((P - A.starProjection) ((P - A.starProjection) x)) x =
      inner 𝕜 ((P - A.starProjection) x) ((P - A.starProjection) x) at hinner
    rw [hzero, inner_zero_left] at hinner
    exact inner_self_eq_zero.mp hinner.symm

/-- The compatible projection space is the product of the unrestricted
orthogonal-projection spaces on one eigenspace from each selected pair.
Both directions act by actual restriction and extension. -/
theorem exists_unitary_paired_projection_equiv
    (U : unitary (E →L[𝕜] E)) (J : E ≃ₗᵢ[𝕜] E) (hJ : Function.Involutive J)
    (hrev : ∀ x, (U : E →L[𝕜] E) (J x) = J (star (U : E →L[𝕜] E) x))
    (mu : ι → 𝕜) (hmu : ∀ i, ‖mu i‖ = 1) (hinj : Function.Injective mu)
    (hconj : ∀ i j, mu i ≠ star (mu j)) :
    let N := fun i => Module.End.eigenspace (U : E →L[𝕜] E).toLinearMap (mu i)
    ∃ e : (∀ i, {Q : N i →L[𝕜] N i // IsStarProjection Q}) ≃
        unitaryPairedProjectionSpace U J mu,
      ∀ Q i (x : N i), (e Q).val x = ((Q i).val x : E) := by
  classical
  let N := fun i => Module.End.eigenspace (U : E →L[𝕜] E).toLinearMap (mu i)
  let Params := ∀ i, {Q : N i →L[𝕜] N i // IsStarProjection Q}
  let Space := unitaryPairedProjectionSpace U J mu
  have hatt (Q : Params) : ∃ P : Space, ∀ i (x : N i), P.val x = ((Q i).val x : E) := by
    obtain ⟨P, ⟨hP, hPU, hPJ, hPx, hPsupp⟩, _⟩ :=
      exists_unique_unitary_paired_projection_family U J hJ hrev mu hmu hinj hconj
        (fun i => (Q i).val) (fun i => (Q i).property)
    exact ⟨⟨P, hP, hPU, hPJ, hPsupp⟩, hPx⟩
  let f : Params → Space := fun Q => (hatt Q).choose
  have hf (Q) : ∀ i (x : N i), (f Q).val x = ((Q i).val x : E) := (hatt Q).choose_spec
  have hinjective : Function.Injective f := by
    intro Q Q' heq
    funext i
    apply Subtype.ext
    ext x
    exact (hf Q i x).symm.trans
      ((congrArg (fun P : Space => P.val (x : E)) heq).trans (hf Q' i x))
  have hsurjective : Function.Surjective f := by
    intro P
    have hN (i) : ∀ x ∈ N i, P.val x ∈ N i := by
      intro x hx
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      change (U : E →L[𝕜] E) (P.val x) = mu i • P.val x
      change (U : E →L[𝕜] E) x = mu i • x at hx
      calc
        _ = P.val ((U : E →L[𝕜] E) x) :=
          (congrArg (fun A : E →L[𝕜] E => A x) P.property.2.1.eq).symm
        _ = _ := by rw [hx, map_smul]
    let Q : Params := fun i =>
      ⟨P.val.restrict (hN i), P.property.1.restrict_invariant (N i) (hN i)⟩
    obtain ⟨P₀, _, huni⟩ :=
      exists_unique_unitary_paired_projection_family U J hJ hrev mu hmu hinj hconj
        (fun i => (Q i).val) (fun i => (Q i).property)
    have hfeq := huni (f Q).val
      ⟨(f Q).property.1, (f Q).property.2.1, (f Q).property.2.2.1,
        hf Q, (f Q).property.2.2.2⟩
    have hPeq := huni P.val
      ⟨P.property.1, P.property.2.1, P.property.2.2.1,
        fun i x => rfl, P.property.2.2.2⟩
    exact ⟨Q, Subtype.ext (hfeq.trans hPeq.symm)⟩
  exact ⟨Equiv.ofBijective f ⟨hinjective, hsurjective⟩, hf⟩

end TauCeti
