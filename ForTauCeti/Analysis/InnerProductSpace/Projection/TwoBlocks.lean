/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.JointEigenbasis
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Algebra.GroupWithZero.Idempotent
public import Mathlib.Tactic.NoncommRing

/-!
# Common orthogonal blocks of two projections

Two orthogonal projections on a finite real or complex Hilbert space have
common invariant blocks of dimension at most two. The proof chooses a
joint eigenvector of the first projection and the diagonal compression of
the second. That vector and its image under the second projection generate
a common invariant line or plane. Orthogonal complement induction completes
the decomposition.

This classical finite two-projection lemma supplies the zero-gradient
reflection case in real transport optimization. The existing joint
orthonormal eigenbasis consumes Mathlib's joint-eigenspace decomposition.
-/

public section

noncomputable section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E]

/-- Every nonzero common invariant subspace of two orthogonal projections
contains a nonzero common invariant line or plane. -/
theorem exists_small_invariant_submodule_of_two_projections
    (P Q : E →L[𝕜] E) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (S : Submodule 𝕜 E) (hS : S ≠ ⊥)
    (hPS : ∀ x ∈ S, P x ∈ S) (hQS : ∀ x ∈ S, Q x ∈ S) :
    ∃ K : Submodule 𝕜 E, K ≤ S ∧ K ≠ ⊥ ∧ Module.finrank 𝕜 K ≤ 2 ∧
      (∀ x ∈ K, P x ∈ K) ∧ (∀ x ∈ K, Q x ∈ K) := by
  classical
  let R := 1 - P
  let T := P * (Q * P) + R * (Q * R)
  have hPP : P * P = P := hP.isIdempotentElem.eq
  have hQQ (x : E) : Q (Q x) = Q x :=
    congrArg (fun A : E →L[𝕜] E => A x) hQ.isIdempotentElem.eq
  have hPR : P * R = 0 := hP.mul_one_sub_self
  have hRP : R * P = 0 := hP.one_sub_mul_self
  have hTsym : T.toLinearMap.IsSymmetric := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    change star T = T
    dsimp only [T, R]
    simp only [star_add, star_mul, star_sub, star_one,
      hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq]
    noncomm_ring
  have hPT : Commute P T := by
    change P * T = T * P
    calc
      P * T = (P * P) * (Q * P) + (P * R) * (Q * R) := by
        dsimp [T]
        noncomm_ring
      _ = P * (Q * P) := by rw [hPP, hPR, zero_mul, add_zero]
      _ = P * (Q * (P * P)) + R * (Q * (R * P)) := by
        rw [hPP, hRP, mul_zero, mul_zero, add_zero]
      _ = T * P := by
        dsimp [T]
        noncomm_ring
  have hRS (x : E) (hx : x ∈ S) : R x ∈ S := S.sub_mem hx (hPS x hx)
  have hTS : ∀ x ∈ S, T x ∈ S := by
    intro x hx
    exact S.add_mem (hPS _ (hQS _ (hPS x hx))) (hRS _ (hQS _ (hRS x hx)))
  have hPT' : Commute (P.toLinearMap.restrict hPS) (T.toLinearMap.restrict hTS) := by
    ext x
    change P (T x) = T (P x)
    exact congrArg (fun A : E →L[𝕜] E => A x) hPT.eq
  obtain ⟨b, mu, nu, hmu, hnu⟩ :=
    (hP.isSelfAdjoint.isSymmetric.restrict_invariant hPS).exists_joint_orthonormalBasis
      (hTsym.restrict_invariant hTS) hPT'
  let : Nontrivial S := (Submodule.nontrivial_iff_ne_bot).mpr hS
  let i : Fin (Module.finrank 𝕜 S) := ⟨0, Module.finrank_pos⟩
  let x : E := b i
  have hx0 : x ≠ 0 := by
    intro h
    exact b.orthonormal.ne_zero i (Subtype.ext h)
  have hxS : x ∈ S := (b i).property
  have hPx : P x = mu i • x := congrArg Subtype.val (hmu i)
  have hTx : T x = nu i • x := congrArg Subtype.val (hnu i)
  have hmidem : IsIdempotentElem (mu i) := by
    apply smul_left_injective 𝕜 hx0
    have h := congrArg (fun A : E →L[𝕜] E => A x) hPP
    change P (P x) = P x at h
    rwa [hPx, map_smul, hPx, smul_smul] at h
  let K := Submodule.span 𝕜 ({x, Q x} : Set E)
  have hxK : x ∈ K := Submodule.subset_span (by simp)
  have hQxK : Q x ∈ K := Submodule.subset_span (by simp)
  have hPxK : P x ∈ K := by rw [hPx]; exact K.smul_mem _ hxK
  have hPQxK : P (Q x) ∈ K := by
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hmidem with hm | hm
    · have hPx0 : P x = 0 := by simpa only [hm, zero_smul] using hPx
      have hTxx : Q x - P (Q x) = nu i • x := by
        simpa only [T, R, add_apply, mul_apply_eq_comp,
          sub_apply, one_apply_eq_self,
          hPx0, map_zero, sub_zero, zero_add] using hTx
      have hPQx : P (Q x) = Q x - nu i • x := by
        linear_combination (norm := module) -hTxx
      rw [hPQx]
      exact K.sub_mem hQxK (K.smul_mem _ hxK)
    · have hPx1 : P x = x := by simpa only [hm, one_smul] using hPx
      have hPQx : P (Q x) = nu i • x := by
        simpa only [T, R, add_apply, mul_apply_eq_comp,
          sub_apply, one_apply_eq_self,
          hPx1, sub_self, map_zero, sub_zero, add_zero] using hTx
      rw [hPQx]
      exact K.smul_mem _ hxK
  refine ⟨K, ?_, ?_, ?_, ?_, ?_⟩
  · apply Submodule.span_le.mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hxS
    · rw [Set.mem_singleton_iff.mp hz]
      exact hQS x hxS
  · intro hzero
    rw [hzero] at hxK
    exact hx0 hxK
  · have h := finrank_span_le_card ({x, Q x} : Set E) (R := 𝕜)
    simp only [Set.toFinset_insert, Set.toFinset_singleton] at h
    exact h.trans Finset.card_le_two
  · intro z hz
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
    rw [map_add, map_smul, map_smul]
    exact K.add_mem (K.smul_mem _ hPxK) (K.smul_mem _ hPQxK)
  · intro z hz
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
    rw [map_add, map_smul, map_smul, hQQ]
    exact K.add_mem (K.smul_mem _ hQxK) (K.smul_mem _ hQxK)

/-- Two orthogonal projections admit a complete orthogonal decomposition
into nonzero common invariant subspaces of dimension at most two. -/
theorem exists_orthogonal_blocks_of_two_projections
    (P Q : E →L[𝕜] E) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    ∃ F : Finset (Submodule 𝕜 E),
      (∀ K ∈ F, K ≠ ⊥ ∧ Module.finrank 𝕜 K ≤ 2 ∧
        (∀ x ∈ K, P x ∈ K) ∧ (∀ x ∈ K, Q x ∈ K)) ∧
      (F : Set (Submodule 𝕜 E)).Pairwise Submodule.IsOrtho ∧ F.sup id = ⊤ := by
  classical
  have aux : ∀ n : ℕ, ∀ S : Submodule 𝕜 E, Module.finrank 𝕜 S = n →
      (∀ x ∈ S, P x ∈ S) → (∀ x ∈ S, Q x ∈ S) →
      ∃ F : Finset (Submodule 𝕜 E),
        (∀ K ∈ F, K ≤ S ∧ K ≠ ⊥ ∧ Module.finrank 𝕜 K ≤ 2 ∧
          (∀ x ∈ K, P x ∈ K) ∧ (∀ x ∈ K, Q x ∈ K)) ∧
        (F : Set (Submodule 𝕜 E)).Pairwise Submodule.IsOrtho ∧ F.sup id = S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hdim hPS hQS
      by_cases hS : S = ⊥
      · subst S
        exact ⟨∅, by simp, by simp, by simp⟩
      obtain ⟨K, hKS, hK0, hKdim, hPK, hQK⟩ :=
        exists_small_invariant_submodule_of_two_projections P Q hP hQ S hS hPS hQS
      let L := Kᗮ ⊓ S
      have hPL : ∀ x ∈ L, P x ∈ L := by
        intro x hx
        refine ⟨?_, hPS x hx.2⟩
        apply (K.mem_orthogonal (P x)).mpr
        intro y hy
        exact (hP.isSelfAdjoint.isSymmetric y x).symm.trans
          ((K.mem_orthogonal x).mp hx.1 _ (hPK y hy))
      have hQL : ∀ x ∈ L, Q x ∈ L := by
        intro x hx
        refine ⟨?_, hQS x hx.2⟩
        apply (K.mem_orthogonal (Q x)).mpr
        intro y hy
        exact (hQ.isSelfAdjoint.isSymmetric y x).symm.trans
          ((K.mem_orthogonal x).mp hx.1 _ (hQK y hy))
      have hdrop : Module.finrank 𝕜 L < n := by
        let : Nontrivial K := (Submodule.nontrivial_iff_ne_bot).mpr hK0
        have hpos : 0 < Module.finrank 𝕜 K := Module.finrank_pos
        have hsum := Submodule.finrank_add_inf_finrank_orthogonal hKS
        change Module.finrank 𝕜 K + Module.finrank 𝕜 L = Module.finrank 𝕜 S at hsum
        omega
      obtain ⟨F, hF, hpair, hspan⟩ := ih _ hdrop L rfl hPL hQL
      refine ⟨insert K F, ?_, ?_, ?_⟩
      · intro T hT
        rcases Finset.mem_insert.mp hT with rfl | hT
        · exact ⟨hKS, hK0, hKdim, hPK, hQK⟩
        · have h := hF T hT
          exact ⟨h.1.trans inf_le_right, h.2⟩
      · intro T hT V hV hTV
        rcases Finset.mem_insert.mp hT with hTK | hTF
        · subst T
          rcases Finset.mem_insert.mp hV with hVK | hVF
          · exact (hTV hVK.symm).elim
          · exact Submodule.IsOrtho.symm ((hF V hVF).1.trans inf_le_left)
        · rcases Finset.mem_insert.mp hV with hVK | hVF
          · subst V
            exact (hF T hTF).1.trans inf_le_left
          · exact hpair hTF hVF hTV
      · rw [Finset.sup_insert, id_eq, hspan]
        exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hKS
  obtain ⟨F, hF, hpair, hspan⟩ := aux _ ⊤ rfl (by simp) (by simp)
  exact ⟨F, fun K hK => (hF K hK).2, hpair, hspan⟩

end TauCeti
