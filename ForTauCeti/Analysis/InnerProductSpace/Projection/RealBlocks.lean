/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Real invariant blocks of the components of a Hermitian projection

Writing a complex Hermitian projection as `X + iY` gives a real symmetric
`X`, a real skew-symmetric `Y`, and the relations `X² - Y² = X` and
`XY + YX = Y`. A real eigenvector of `X` generates a common invariant
line or an orthonormal two-dimensional block with explicit coefficients.
This is the elementary block step in the classical real orthogonal normal
form, used in the real transport matching theorem.
-/

public section

noncomputable section

namespace TauCeti

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A unit eigenvector of the symmetric component determines the squared
norm of its image under the skew component. -/
theorem norm_sq_skew_apply_of_projection_relations
    (X Y : Module.End ℝ E)
    (hY : ∀ x y, ⟪Y x, y⟫_ℝ = -⟪x, Y y⟫_ℝ)
    (hquad : X * X - Y * Y = X) (lam : ℝ) (x : E)
    (hXx : X x = lam • x) (hx : ‖x‖ = 1) :
    ‖Y x‖ ^ 2 = lam * (1 - lam) := by
  have hq := congrArg (fun A : Module.End ℝ E => A x) hquad
  change X (X x) - Y (Y x) = X x at hq
  rw [hXx, map_smul, hXx, smul_smul] at hq
  have hYY : Y (Y x) = (lam ^ 2 - lam) • x := by
    linear_combination (norm := module) -hq
  have h := hY x (Y x)
  rw [real_inner_self_eq_norm_sq, hYY, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hx] at h
  nlinarith

/-- The components of a Hermitian projection on a nonzero finite real
Hilbert space have a common invariant line or an explicit orthonormal
two-dimensional block. No choice of complex coordinates is required. -/
theorem exists_real_projection_line_or_plane [FiniteDimensional ℝ E] [Nontrivial E]
    (X Y : Module.End ℝ E) (hX : X.IsSymmetric)
    (hY : ∀ x y, ⟪Y x, y⟫_ℝ = -⟪x, Y y⟫_ℝ)
    (hquad : X * X - Y * Y = X) (hanti : X * Y + Y * X = Y) :
    ∃ x : E, ‖x‖ = 1 ∧
      ((X x = 0 ∧ Y x = 0) ∨ (X x = x ∧ Y x = 0) ∨
        ∃ lam ∈ Set.Ioo (0 : ℝ) 1, ∃ y : E,
          ‖y‖ = 1 ∧ ⟪x, y⟫_ℝ = 0 ∧
          X x = lam • x ∧ X y = (1 - lam) • y ∧
          Y x = Real.sqrt (lam * (1 - lam)) • y ∧
          Y y = -Real.sqrt (lam * (1 - lam)) • x) := by
  let b := hX.eigenvectorBasis rfl
  let i : Fin (Module.finrank ℝ E) := ⟨0, Module.finrank_pos⟩
  let x := b i
  let lam := hX.eigenvalues rfl i
  have hx : ‖x‖ = 1 := b.norm_eq_one i
  have hXx : X x = lam • x := hX.apply_eigenvectorBasis rfl i
  have hnorm := norm_sq_skew_apply_of_projection_relations X Y hY hquad lam x hXx hx
  refine ⟨x, hx, ?_⟩
  by_cases hy0 : Y x = 0
  · have hf : lam * (1 - lam) = 0 := by simpa [hy0] using hnorm.symm
    rcases mul_eq_zero.mp hf with hl | hl
    · exact Or.inl ⟨by simpa [hl] using hXx, hy0⟩
    · have hl1 : lam = 1 := by linarith
      exact Or.inr (Or.inl ⟨by simpa [hl1] using hXx, hy0⟩)
  · have hpos : 0 < lam * (1 - lam) := by
      rw [← hnorm]
      exact sq_pos_of_pos (norm_pos_iff.mpr hy0)
    have hl0 : 0 < lam := by nlinarith
    have hl1 : lam < 1 := by nlinarith
    let r := Real.sqrt (lam * (1 - lam))
    have hr : 0 < r := Real.sqrt_pos.mpr hpos
    have hrr : r ^ 2 = lam * (1 - lam) := Real.sq_sqrt hpos.le
    have hrnorm : r = ‖Y x‖ := by
      rw [show r = Real.sqrt (lam * (1 - lam)) from rfl,
        ← hnorm, Real.sqrt_sq (norm_nonneg _)]
    let y := r⁻¹ • Y x
    have hy : ‖y‖ = 1 := by
      change ‖r⁻¹ • Y x‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
        ← hrnorm, inv_mul_cancel₀ hr.ne']
    have hinner : ⟪x, Y x⟫_ℝ = 0 := by
      have h := hY x x
      linarith [real_inner_comm (Y x) x]
    have hxy : ⟪x, y⟫_ℝ = 0 := by
      change ⟪x, r⁻¹ • Y x⟫_ℝ = 0
      rw [real_inner_smul_right, hinner, mul_zero]
    have hXY : X (Y x) = (1 - lam) • Y x := by
      have h := congrArg (fun A : Module.End ℝ E => A x) hanti
      change X (Y x) + Y (X x) = Y x at h
      rw [hXx, map_smul] at h
      rw [sub_smul, one_smul]
      exact eq_sub_of_add_eq h
    have hYY : Y (Y x) = (lam ^ 2 - lam) • x := by
      have h := congrArg (fun A : Module.End ℝ E => A x) hquad
      change X (X x) - Y (Y x) = X x at h
      rw [hXx, map_smul, hXx, smul_smul] at h
      linear_combination (norm := module) -h
    have hXy : X y = (1 - lam) • y := by
      change X (r⁻¹ • Y x) = (1 - lam) • (r⁻¹ • Y x)
      rw [map_smul, hXY, smul_comm]
    have hYx : Y x = r • y := by
      change Y x = r • (r⁻¹ • Y x)
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hcoeff : r⁻¹ * (lam ^ 2 - lam) = -r := by
      field_simp
      nlinarith [hrr]
    have hYy : Y y = -r • x := by
      change Y (r⁻¹ • Y x) = -r • x
      rw [map_smul, hYY, smul_smul, hcoeff]
    exact Or.inr (Or.inr ⟨lam, ⟨hl0, hl1⟩, y, hy, hxy, hXx, hXy, hYx, hYy⟩)

/-- Every nonzero finite common invariant subspace contains a nonzero
common invariant line or plane. This form is convenient for successive
orthogonal decomposition and does not need skew-symmetry of `Y`. -/
theorem exists_small_invariant_submodule_of_projection_relations
    (X Y : Module.End ℝ E) (hX : X.IsSymmetric)
    (hquad : X * X - Y * Y = X) (hanti : X * Y + Y * X = Y)
    (S : Submodule ℝ E) [FiniteDimensional ℝ S] (hS : S ≠ ⊥)
    (hXS : ∀ x ∈ S, X x ∈ S) (hYS : ∀ x ∈ S, Y x ∈ S) :
    ∃ K : Submodule ℝ E, K ≤ S ∧ K ≠ ⊥ ∧ Module.finrank ℝ K ≤ 2 ∧
      (∀ x ∈ K, X x ∈ K) ∧ (∀ x ∈ K, Y x ∈ K) := by
  classical
  let : Nontrivial S := (Submodule.nontrivial_iff_ne_bot).mpr hS
  let hs := hX.restrict_invariant hXS
  let b := hs.eigenvectorBasis rfl
  let i : Fin (Module.finrank ℝ S) := ⟨0, Module.finrank_pos⟩
  let x : E := b i
  let lam := hs.eigenvalues rfl i
  have hXx : X x = lam • x := congrArg Subtype.val (hs.apply_eigenvectorBasis rfl i)
  have hx0 : x ≠ 0 := by
    intro h
    apply b.orthonormal.ne_zero i
    exact Subtype.ext h
  have hXY : X (Y x) = (1 - lam) • Y x := by
    have h := congrArg (fun A : Module.End ℝ E => A x) hanti
    change X (Y x) + Y (X x) = Y x at h
    rw [hXx, map_smul] at h
    rw [sub_smul, one_smul]
    exact eq_sub_of_add_eq h
  have hYY : Y (Y x) = (lam ^ 2 - lam) • x := by
    have h := congrArg (fun A : Module.End ℝ E => A x) hquad
    change X (X x) - Y (Y x) = X x at h
    rw [hXx, map_smul, hXx, smul_smul] at h
    linear_combination (norm := module) -h
  let K := Submodule.span ℝ ({x, Y x} : Set E)
  have hxK : x ∈ K := Submodule.subset_span (by simp)
  have hYxK : Y x ∈ K := Submodule.subset_span (by simp)
  have hKS : K ≤ S := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact (b i).property
    · have hz' : z = Y x := Set.mem_singleton_iff.mp hz
      rw [hz']
      exact hYS x (b i).property
  have hK0 : K ≠ ⊥ := by
    intro h
    rw [h] at hxK
    exact hx0 hxK
  have hdim : Module.finrank ℝ K ≤ 2 := by
    have h := finrank_span_le_card ({x, Y x} : Set E) (R := ℝ)
    simp only [Set.toFinset_insert, Set.toFinset_singleton] at h
    exact h.trans Finset.card_le_two
  refine ⟨K, hKS, hK0, hdim, ?_, ?_⟩
  · intro z hz
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
    rw [map_add, map_smul, map_smul, hXx, hXY]
    exact K.add_mem (K.smul_mem _ (K.smul_mem _ hxK))
      (K.smul_mem _ (K.smul_mem _ hYxK))
  · intro z hz
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
    rw [map_add, map_smul, map_smul, hYY]
    exact K.add_mem (K.smul_mem _ hYxK) (K.smul_mem _ (K.smul_mem _ hxK))

/-- The real symmetric and skew components of a complex Hermitian
projection admit a complete orthogonal decomposition into common
invariant subspaces of real dimension at most two. -/
theorem exists_orthogonal_real_projection_blocks [FiniteDimensional ℝ E]
    (X Y : Module.End ℝ E) (hX : X.IsSymmetric)
    (hY : ∀ x y, ⟪Y x, y⟫_ℝ = -⟪x, Y y⟫_ℝ)
    (hquad : X * X - Y * Y = X) (hanti : X * Y + Y * X = Y) :
    ∃ F : Finset (Submodule ℝ E),
      (∀ K ∈ F, K ≠ ⊥ ∧ Module.finrank ℝ K ≤ 2 ∧
        (∀ x ∈ K, X x ∈ K) ∧ (∀ x ∈ K, Y x ∈ K)) ∧
      (F : Set (Submodule ℝ E)).Pairwise Submodule.IsOrtho ∧ F.sup id = ⊤ := by
  classical
  have aux : ∀ n : ℕ, ∀ S : Submodule ℝ E, Module.finrank ℝ S = n →
      (∀ x ∈ S, X x ∈ S) → (∀ x ∈ S, Y x ∈ S) →
      ∃ F : Finset (Submodule ℝ E),
        (∀ K ∈ F, K ≤ S ∧ K ≠ ⊥ ∧ Module.finrank ℝ K ≤ 2 ∧
          (∀ x ∈ K, X x ∈ K) ∧ (∀ x ∈ K, Y x ∈ K)) ∧
        (F : Set (Submodule ℝ E)).Pairwise Submodule.IsOrtho ∧ F.sup id = S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hdim hXS hYS
      by_cases hS : S = ⊥
      · subst S
        exact ⟨∅, by simp, by simp, by simp⟩
      obtain ⟨K, hKS, hK0, hKdim, hXK, hYK⟩ :=
        exists_small_invariant_submodule_of_projection_relations X Y hX hquad hanti
          S hS hXS hYS
      let L := Kᗮ ⊓ S
      have hXL : ∀ x ∈ L, X x ∈ L := by
        intro x hx
        refine ⟨?_, hXS x hx.2⟩
        apply (K.mem_orthogonal (X x)).mpr
        intro y hy
        rw [← hX y x]
        exact (K.mem_orthogonal x).mp hx.1 _ (hXK y hy)
      have hYL : ∀ x ∈ L, Y x ∈ L := by
        intro x hx
        refine ⟨?_, hYS x hx.2⟩
        apply (K.mem_orthogonal (Y x)).mpr
        intro y hy
        have hz := (K.mem_orthogonal x).mp hx.1 _ (hYK y hy)
        linarith [hY y x]
      have hdrop : Module.finrank ℝ L < n := by
        let : Nontrivial K := (Submodule.nontrivial_iff_ne_bot).mpr hK0
        have hpos : 0 < Module.finrank ℝ K := Module.finrank_pos
        have hsum := Submodule.finrank_add_inf_finrank_orthogonal hKS
        change Module.finrank ℝ K + Module.finrank ℝ L = Module.finrank ℝ S at hsum
        omega
      obtain ⟨F, hF, hpair, hspan⟩ := ih _ hdrop L rfl hXL hYL
      refine ⟨insert K F, ?_, ?_, ?_⟩
      · intro T hT
        rcases Finset.mem_insert.mp hT with rfl | hT
        · exact ⟨hKS, hK0, hKdim, hXK, hYK⟩
        · have h := hF T hT
          exact ⟨h.1.trans inf_le_right, h.2⟩
      · intro T hT U hU hTU
        rcases Finset.mem_insert.mp hT with hTK | hTF
        · subst T
          rcases Finset.mem_insert.mp hU with hUK | hUF
          · exact (hTU hUK.symm).elim
          · exact Submodule.IsOrtho.symm ((hF U hUF).1.trans inf_le_left)
        · rcases Finset.mem_insert.mp hU with hUK | hUF
          · subst U
            exact (hF T hTF).1.trans inf_le_left
          · exact hpair hTF hUF hTU
      · rw [Finset.sup_insert, id_eq, hspan]
        exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hKS
  obtain ⟨F, hF, hpair, hspan⟩ := aux _ ⊤ rfl (by simp) (by simp)
  exact ⟨F, fun K hK => (hF K hK).2, hpair, hspan⟩

end TauCeti
