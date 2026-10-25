/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.SpectralTheory.Complexification.SubmoduleEquiv
import ForTauCeti.Analysis.InnerProductSpace.Complexification.FiniteDimensional
import ForTauCeti.Analysis.InnerProductSpace.Complexification.RealPoints

/-!
# Descending conjugation-invariant spectral blocks to the real space

A complex submodule of the established Hilbert complexification is the
complexification of its real preimage precisely when it is stable under
coordinate conjugation. Dimension, invariance and orthogonality descend.
These are the representation bridges needed to turn the positive-gradient
construction into actual real transport blocks.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real preimage of a complex subspace under the established real inclusion. -/
def realSubmodule (M : Submodule ℂ (RealComplexification E)) : Submodule ℝ E :=
  (M.restrictScalars ℝ).comap ofReal.toLinearMap

/-- Membership in the descended real space is literal membership of the real copy. -/
@[simp]
theorem mem_realSubmodule (M : Submodule ℂ (RealComplexification E)) (x : E) :
    x ∈ realSubmodule M ↔ ofReal x ∈ M := Iff.rfl

/-- Taking the real preimage recovers the original real subspace. -/
@[simp]
theorem realSubmodule_complexifySubmodule (N : Submodule ℝ E) :
    realSubmodule (complexifySubmodule N) = N := by
  ext x
  exact ofReal_mem_complexifySubmodule_iff N x

private theorem complexifySubmodule_mono {N T : Submodule ℝ E} (h : N ≤ T) :
    complexifySubmodule N ≤ complexifySubmodule T := by
  intro z hz
  rw [mem_complexifySubmodule] at hz ⊢
  exact ⟨h hz.1, h hz.2⟩

private theorem ofReal_re_eq_half_add_conjugation (z : RealComplexification E) :
    ofReal (re z) = (1 / 2 : ℂ) • (z + conjugation z) := by
  apply RealComplexification.ext <;> simp
  module

/-- A vector fixed by coordinate conjugation is its actual real copy. -/
theorem ofReal_re_of_conjugation_fixed (z : RealComplexification E)
    (hz : conjugation z = z) : ofReal (re z) = z := by
  rw [ofReal_re_eq_half_add_conjugation, hz]
  module

section RealPointsDescent

variable (M : Submodule ℂ (RealComplexification E))

local instance : InnerProductSpace ℝ M := InnerProductSpace.rclikeToReal ℂ M

/-- Fixed vectors of an actual restricted coordinate conjugation identify
isometrically with the original ambient real preimage. -/
def realPointsDescentEquiv (C : M ≃ₗᵢ⋆[ℂ] M)
    (hC : ∀ z : M, (C z : RealComplexification E) = conjugation z) :
    realPoints C.toLinearEquiv.toLinearMap ≃ₗᵢ[ℝ] realSubmodule M := by
  have hreal (z : realPoints C.toLinearEquiv.toLinearMap) :
      ofReal (re ((z : M) : RealComplexification E)) = (z : M) := by
    apply ofReal_re_of_conjugation_fixed
    have h := congrArg (fun w : M => (w : RealComplexification E))
      (mem_realPoints.mp z.property)
    exact (hC z).symm.trans h
  exact
    { toFun := fun z => ⟨re ((z : M) : RealComplexification E), by
        rw [mem_realSubmodule, hreal]
        exact (z : M).property⟩
      invFun := fun x => ⟨⟨ofReal (x : E), (mem_realSubmodule M x).mp x.property⟩, by
        rw [mem_realPoints]
        apply Subtype.ext
        exact (hC ⟨ofReal (x : E), (mem_realSubmodule M x).mp x.property⟩).trans
          (conjugation_ofReal (x : E))⟩
      left_inv := by
        intro z
        apply Subtype.ext
        apply Subtype.ext
        exact hreal z
      right_inv := by
        intro x
        apply Subtype.ext
        exact re_ofReal (x : E)
      map_add' := by
        intro x y
        apply Subtype.ext
        exact re_add _ _
      map_smul' := by
        intro r z
        apply Subtype.ext
        change re ((r : ℂ) • ((z : M) : RealComplexification E)) =
          r • re ((z : M) : RealComplexification E)
        simp only [re_complex_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]
      norm_map' := by
        intro z
        change ‖re ((z : M) : RealComplexification E)‖ = ‖z‖
        have h := congrArg norm (hreal z)
        simpa only [ofReal.norm_map, Submodule.norm_coe] using h }

/-- The real descent equivalence reads the actual ambient real coordinate. -/
@[simp]
theorem realPointsDescentEquiv_apply (C : M ≃ₗᵢ⋆[ℂ] M)
    (hC : ∀ z : M, (C z : RealComplexification E) = conjugation z)
    (z : realPoints C.toLinearEquiv.toLinearMap) :
    (realPointsDescentEquiv M C hC z : E) = re ((z : M) : RealComplexification E) := by
  unfold realPointsDescentEquiv
  rfl

end RealPointsDescent

/-- A conjugation-stable submodule contains the real and imaginary
coordinate copies of each of its vectors. -/
theorem ofReal_parts_mem_of_conjugation_invariant
    (M : Submodule ℂ (RealComplexification E))
    (hM : ∀ z ∈ M, conjugation z ∈ M) (z : RealComplexification E) (hz : z ∈ M) :
    ofReal (re z) ∈ M ∧ ofReal (im z) ∈ M := by
  have hre (w : RealComplexification E) (hw : w ∈ M) : ofReal (re w) ∈ M := by
    rw [ofReal_re_eq_half_add_conjugation]
    exact M.smul_mem _ (M.add_mem hw (hM w hw))
  refine ⟨hre z hz, ?_⟩
  simpa using hre (-Complex.I • z) (M.smul_mem _ hz)

/-- Conjugation-stable complex subspaces descend exactly to the real space. -/
theorem complexify_realSubmodule
    (M : Submodule ℂ (RealComplexification E))
    (hM : ∀ z ∈ M, conjugation z ∈ M) :
    complexifySubmodule (realSubmodule M) = M := by
  ext z
  constructor
  · intro hz
    rw [mem_complexifySubmodule] at hz
    rw [eq_ofReal_add_I_smul_ofReal z]
    exact M.add_mem hz.1 (M.smul_mem _ hz.2)
  · intro hz
    rw [mem_complexifySubmodule]
    exact ofReal_parts_mem_of_conjugation_invariant M hM z hz

/-- Descent preserves nontriviality for conjugation-stable subspaces. -/
theorem realSubmodule_eq_bot_iff
    (M : Submodule ℂ (RealComplexification E))
    (hM : ∀ z ∈ M, conjugation z ∈ M) :
    realSubmodule M = ⊥ ↔ M = ⊥ := by
  constructor
  · intro hzero
    apply bot_unique
    intro z hz
    obtain ⟨hr, hi⟩ := ofReal_parts_mem_of_conjugation_invariant M hM z hz
    have hr0 : re z = 0 := by
      have h : re z ∈ realSubmodule M := hr
      simpa only [hzero, Submodule.mem_bot] using h
    have hi0 : im z = 0 := by
      have h : im z ∈ realSubmodule M := hi
      simpa only [hzero, Submodule.mem_bot] using h
    rw [Submodule.mem_bot]
    apply RealComplexification.ext <;> simp [hr0, hi0]
  · rintro rfl
    apply bot_unique
    intro x hx
    change ofReal x ∈ (⊥ : Submodule ℂ (RealComplexification E)) at hx
    rw [Submodule.mem_bot] at hx ⊢
    exact ofReal.injective (by simpa using hx)

/-- The real dimension of a descended block is its original complex dimension. -/
theorem finrank_realSubmodule [FiniteDimensional ℝ E]
    (M : Submodule ℂ (RealComplexification E))
    (hM : ∀ z ∈ M, conjugation z ∈ M) :
    Module.finrank ℝ (realSubmodule M) = Module.finrank ℂ M := by
  calc
    Module.finrank ℝ (realSubmodule M) =
        Module.finrank ℂ (RealComplexification (realSubmodule M)) := finrank_complex.symm
    _ = Module.finrank ℂ (complexifySubmodule (realSubmodule M)) :=
      (complexifySubmoduleEquiv (realSubmodule M)).toLinearEquiv.finrank_eq
    _ = _ := congrArg (fun S : Submodule ℂ (RealComplexification E) => Module.finrank ℂ S)
      (complexify_realSubmodule M hM)

/-- Invariance under an actual real operator descends from its complexification. -/
theorem realSubmodule_invariant
    (M : Submodule ℂ (RealComplexification E)) (T : E →L[ℝ] E)
    (hT : ∀ z ∈ M, complexify T z ∈ M) :
    ∀ x ∈ realSubmodule M, T x ∈ realSubmodule M := by
  intro x hx
  have h := hT (ofReal x) hx
  change ofReal (T x) ∈ M
  simpa only [complexify_ofReal] using h

/-- Orthogonal complex blocks descend to orthogonal real blocks. -/
theorem realSubmodule_isOrtho
    (M N : Submodule ℂ (RealComplexification E)) (hMN : M.IsOrtho N) :
    (realSubmodule M).IsOrtho (realSubmodule N) := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro x hx y hy
  have h := hMN.inner_eq hx hy
  change ⟪ofReal x, ofReal y⟫_ℂ = 0 at h
  rw [inner_ofReal] at h
  exact_mod_cast h

/-- Doubling a subspace by source reflection produces a real, source-preserving
invariant block whenever the original subspace is stable under source
reflection followed by conjugation. -/
theorem doubled_block_invariant
    (R : RealComplexification E ≃ₗᵢ[ℂ] RealComplexification E)
    (hR : Function.Involutive R)
    (hRC : ∀ z, R (conjugation z) = conjugation (R z))
    (U : RealComplexification E →L[ℂ] RealComplexification E)
    (hUC : ∀ z, U (conjugation z) = conjugation (U z))
    (S : Submodule ℂ (RealComplexification E))
    (hSJ : ∀ z ∈ S, R (conjugation z) ∈ S)
    (hUS : ∀ z ∈ S, U z ∈ S) :
    let M := S ⊔ S.map R.toLinearMap
    (∀ z ∈ M, R z ∈ M) ∧
      (∀ z ∈ M, conjugation z ∈ M) ∧ (∀ z ∈ M, U z ∈ M) := by
  let M := S ⊔ S.map R.toLinearMap
  have hCS (z : RealComplexification E) (hz : z ∈ S) :
      conjugation z ∈ S.map R.toLinearMap :=
    ⟨R (conjugation z), hSJ z hz, hR (conjugation z)⟩
  have hCRS (z : RealComplexification E) (hz : z ∈ S) :
      conjugation (R z) ∈ S := by
    rw [← hRC]
    exact hSJ z hz
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, _, ⟨y, hy, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hz
    change R (x + R y) ∈ M
    rw [map_add, hR]
    exact M.add_mem ((show S.map R.toLinearMap ≤ M from le_sup_right)
      (Submodule.mem_map_of_mem hx)) ((show S ≤ M from le_sup_left) hy)
  · intro z hz
    obtain ⟨x, hx, _, ⟨y, hy, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hz
    change conjugation (x + R y) ∈ M
    rw [map_add]
    exact M.add_mem ((show S.map R.toLinearMap ≤ M from le_sup_right) (hCS x hx))
      ((show S ≤ M from le_sup_left) (hCRS y hy))
  · intro z hz
    obtain ⟨x, hx, _, ⟨y, hy, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hz
    change U (x + R y) ∈ M
    rw [map_add]
    apply M.add_mem ((show S ≤ M from le_sup_left) (hUS x hx))
    have hyJ := hSJ y hy
    have heq : R y = conjugation (R (conjugation y)) := by
      rw [hRC, conjugation_involutive]
    rw [heq, hUC]
    exact (show S.map R.toLinearMap ≤ M from le_sup_right) (hCS _ (hUS _ hyJ))

/-- Orthogonality survives doubling when the original family and its
reflected copy lie in mutually orthogonal spectral spaces. -/
theorem doubled_blocks_isOrtho
    (R : RealComplexification E ≃ₗᵢ[ℂ] RealComplexification E)
    (L S T : Submodule ℂ (RealComplexification E))
    (hL : L.IsOrtho (L.map R.toLinearMap))
    (hS : S ≤ L) (hT : T ≤ L) (hST : S.IsOrtho T) :
    (S ⊔ S.map R.toLinearMap).IsOrtho (T ⊔ T.map R.toLinearMap) := by
  rw [Submodule.isOrtho_sup_left, Submodule.isOrtho_sup_right,
    Submodule.isOrtho_sup_right]
  exact ⟨⟨hST, hL.mono hS (Submodule.map_mono hT)⟩,
    ⟨hL.symm.mono (Submodule.map_mono hS) hT, hST.map R.toLinearIsometry⟩⟩

/-- A positive-level block of complex dimension at most two lifts to an
actual real invariant block of dimension at most four. The source reflection
and the actual real transporter preserve that block. -/
theorem exists_small_real_doubled_block [FiniteDimensional ℝ E]
    (R : RealComplexification E ≃ₗᵢ[ℂ] RealComplexification E)
    (hR : Function.Involutive R)
    (hRC : ∀ z, R (conjugation z) = conjugation (R z))
    (U : RealComplexification E →L[ℂ] RealComplexification E)
    (hUC : ∀ z, U (conjugation z) = conjugation (U z))
    (S : Submodule ℂ (RealComplexification E)) (hS0 : S ≠ ⊥)
    (hdim : Module.finrank ℂ S ≤ 2)
    (hSJ : ∀ z ∈ S, R (conjugation z) ∈ S)
    (hUS : ∀ z ∈ S, U z ∈ S) :
    ∃ N : Submodule ℝ E,
      complexifySubmodule N = S ⊔ S.map R.toLinearMap ∧
      N ≠ ⊥ ∧ Module.finrank ℝ N ≤ 4 ∧
      (∀ x ∈ N, realify U x ∈ N) ∧
      (∀ x ∈ N, realify (R : RealComplexification E →L[ℂ] RealComplexification E) x ∈ N) := by
  let M := S ⊔ S.map R.toLinearMap
  obtain ⟨hRM, hCM, hUM⟩ := doubled_block_invariant R hR hRC U hUC S hSJ hUS
  let N := realSubmodule M
  refine ⟨N, complexify_realSubmodule M hCM, ?_, ?_, ?_, ?_⟩
  · intro hN
    have hM : M = ⊥ := (realSubmodule_eq_bot_iff M hCM).mp hN
    apply hS0
    exact le_bot_iff.mp (hM ▸ (show S ≤ M from le_sup_left))
  · rw [show Module.finrank ℝ N = Module.finrank ℂ M from finrank_realSubmodule M hCM]
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq S (S.map R.toLinearMap)
    rw [R.toLinearEquiv.finrank_map_eq S] at hsum
    change Module.finrank ℂ M + _ = _ at hsum
    omega
  · apply realSubmodule_invariant M (realify U)
    rwa [complexify_realify hUC]
  · apply realSubmodule_invariant M
      (realify (R : RealComplexification E →L[ℂ] RealComplexification E))
    rw [complexify_realify hRC]
    exact hRM

/-- A complete orthogonal family on one half of a reflection-paired spectral
level descends to a complete family of actual real invariant blocks. Every
descended member retains its original complex half, so subsequent exact
rank certificates refer to the same actual block family. -/
theorem exists_orthogonal_real_doubled_blocks [FiniteDimensional ℝ E]
    (R : RealComplexification E ≃ₗᵢ[ℂ] RealComplexification E)
    (hR : Function.Involutive R)
    (hRC : ∀ z, R (conjugation z) = conjugation (R z))
    (U : RealComplexification E →L[ℂ] RealComplexification E)
    (hUC : ∀ z, U (conjugation z) = conjugation (U z))
    (L : Submodule ℂ (RealComplexification E))
    (hL : L.IsOrtho (L.map R.toLinearMap))
    (F : Finset (Submodule ℂ (RealComplexification E)))
    (hF : ∀ S ∈ F, S ≠ ⊥ ∧ Module.finrank ℂ S ≤ 2 ∧
      (∀ z ∈ S, R (conjugation z) ∈ S) ∧ (∀ z ∈ S, U z ∈ S))
    (hpair : (F : Set (Submodule ℂ (RealComplexification E))).Pairwise Submodule.IsOrtho)
    (hspan : F.sup id = L) :
    ∃ G : Finset (Submodule ℝ E),
      (∀ N ∈ G, N ≠ ⊥ ∧ Module.finrank ℝ N ≤ 4 ∧
        (∀ x ∈ N, realify U x ∈ N) ∧
        (∀ x ∈ N, realify (R : RealComplexification E →L[ℂ] RealComplexification E) x ∈ N)) ∧
      (G : Set (Submodule ℝ E)).Pairwise Submodule.IsOrtho ∧
      complexifySubmodule (G.sup id) = L ⊔ L.map R.toLinearMap ∧
      (∀ N ∈ G, ∃ S ∈ F,
        complexifySubmodule N = S ⊔ S.map R.toLinearMap) := by
  classical
  let f := fun S : Submodule ℂ (RealComplexification E) =>
    realSubmodule (S ⊔ S.map R.toLinearMap)
  have hCS (S) (hS : S ∈ F) :
      complexifySubmodule (f S) = S ⊔ S.map R.toLinearMap :=
    complexify_realSubmodule _
      (doubled_block_invariant R hR hRC U hUC S (hF S hS).2.2.1 (hF S hS).2.2.2).2.1
  let G := F.image f
  have hleL (S) (hS : S ∈ F) : S ≤ L := by
    rw [← hspan]
    exact Finset.le_sup (f := id) hS
  have hf (S) (hS : S ∈ F) : f S ∈ G := Finset.mem_image.mpr ⟨S, hS, rfl⟩
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro N hN
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hN
    obtain ⟨hS0, hdim, hSJ, hUS⟩ := hF S hS
    obtain ⟨N, hN, hN0, hdimN, hUN, hRN⟩ :=
      exists_small_real_doubled_block R hR hRC U hUC S hS0 hdim hSJ hUS
    have heq : N = f S := by
      have h := congrArg realSubmodule hN
      simpa only [realSubmodule_complexifySubmodule] using h
    exact heq ▸ ⟨hN0, hdimN, hUN, hRN⟩
  · intro N hN T hT hNT
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hN
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hT
    exact realSubmodule_isOrtho _ _ (doubled_blocks_isOrtho R L S V hL
      (hleL S hS) (hleL V hV) (hpair hS hV (fun h => hNT (congrArg f h))))
  · let T := G.sup id
    have hST (S) (hS : S ∈ F) : S ⊔ S.map R.toLinearMap ≤ complexifySubmodule T := by
      rw [← hCS S hS]
      exact complexifySubmodule_mono (Finset.le_sup (f := id) (hf S hS))
    have hLT : L ≤ complexifySubmodule T := by
      rw [← hspan]
      apply Finset.sup_le
      intro S hS
      exact le_trans le_sup_left (hST S hS)
    have hRLT : L.map R.toLinearMap ≤ complexifySubmodule T := by
      have hLc : L ≤ (complexifySubmodule T).comap R.toLinearMap := by
        rw [← hspan]
        apply Finset.sup_le
        intro S hS x hx
        exact hST S hS ((show S.map R.toLinearMap ≤ S ⊔ S.map R.toLinearMap from
          le_sup_right) (Submodule.mem_map_of_mem hx))
      rintro z ⟨x, hx, rfl⟩
      exact hLc hx
    apply le_antisymm
    · have hT : T ≤ realSubmodule (L ⊔ L.map R.toLinearMap) := by
        apply Finset.sup_le
        intro N hN
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hN
        intro x hx
        exact (sup_le_sup (hleL S hS) (Submodule.map_mono (hleL S hS))) hx
      intro z hz
      have hp := (mem_complexifySubmodule.mp hz)
      rw [eq_ofReal_add_I_smul_ofReal z]
      exact (L ⊔ L.map R.toLinearMap).add_mem (hT hp.1)
        ((L ⊔ L.map R.toLinearMap).smul_mem _ (hT hp.2))
    · exact sup_le hLT hRLT
  · intro N hN
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hN
    exact ⟨S, hS, hCS S hS⟩

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
