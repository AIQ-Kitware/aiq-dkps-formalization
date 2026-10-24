/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.SpectralTheory.Complexification.SubmoduleEquiv
import ForTauCeti.Analysis.InnerProductSpace.Complexification.FiniteDimensional
import ForTauCeti.Analysis.InnerProductSpace.Complexification.RealPoints
import ForTauCeti.Analysis.InnerProductSpace.Projection.ComplexRealBlocks

/-!
# Real blocks of two-phase operators

On a positive real stationary-gradient level the transport has at most two
complex phases. Its Hermitian spectral projection, expressed in the fixed
real coordinates of source reflection, therefore gives a complete common
invariant decomposition into complex blocks of dimension at most two,
or real blocks of dimension at most four.

This file certifies the two-phase algebraic reduction. The derivation of
these hypotheses from real transport stationarity and the final matching
minimum are separate steps.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem invariant_complexifySubmodule_of_parts
    (A : RealComplexification E →L[ℂ] RealComplexification E) (K : Submodule ℝ E)
    (hX : ∀ x ∈ K, realPartOperator A x ∈ K)
    (hY : ∀ x ∈ K, imaginaryPartOperator A x ∈ K) :
    ∀ z ∈ complexifySubmodule K, A z ∈ complexifySubmodule K := by
  intro z hz
  rw [mem_complexifySubmodule] at hz ⊢
  rw [re_apply_eq_parts, im_apply_eq_parts]
  exact ⟨K.sub_mem (hX _ hz.1) (hY _ hz.2),
    K.add_mem (hY _ hz.1) (hX _ hz.2)⟩

private theorem isOrtho_complexifySubmodule
    (K L : Submodule ℝ E) (hKL : K.IsOrtho L) :
    (complexifySubmodule K).IsOrtho (complexifySubmodule L) := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro z hz w hw
  rw [mem_complexifySubmodule] at hz hw
  apply Complex.ext <;>
    simp [inner_apply, hKL.inner_eq hz.1 hw.1, hKL.inner_eq hz.2 hw.2,
      hKL.inner_eq hz.1 hw.2, hKL.inner_eq hz.2 hw.1]

private theorem sup_complexifySubmodule_eq_top
    (F : Finset (Submodule ℝ E)) (hF : F.sup id = ⊤) :
    F.sup (fun K => complexifySubmodule K) = ⊤ := by
  classical
  let S := F.sup (fun K => complexifySubmodule K)
  let T := (S.restrictScalars ℝ).comap ofReal.toLinearMap
  have hle : F.sup id ≤ T := by
    apply Finset.sup_le
    intro K hK x hx
    have hKS : complexifySubmodule K ≤ S := Finset.le_sup hK
    exact hKS ((ofReal_mem_complexifySubmodule_iff K x).mpr hx)
  have hof (x : E) : ofReal x ∈ S := by
    rw [hF] at hle
    exact hle (Submodule.mem_top)
  apply top_unique
  intro z _
  rw [eq_ofReal_add_I_smul_ofReal z]
  exact S.add_mem (hof _) (S.smul_mem _ (hof _))

/-- A two-phase operator and coordinate conjugation have a complete common
orthogonal invariant decomposition into blocks of real dimension at most four.
The blocks come from actual Hermitian spectral projection data. -/
theorem exists_orthogonal_small_real_blocks_of_two_phase
    [FiniteDimensional ℝ E]
    (A V : RealComplexification E →L[ℂ] RealComplexification E)
    (hA : IsStarProjection A) (a b : ℂ) (hV : V = a • 1 + b • A) :
    ∃ F : Finset (Submodule ℝ E),
      (∀ K ∈ F, K ≠ ⊥ ∧ Module.finrank ℝ K ≤ 2 ∧
        Module.finrank ℂ (complexifySubmodule K) ≤ 2 ∧
        Module.finrank ℝ (complexifySubmodule K) ≤ 4 ∧
        (∀ z ∈ complexifySubmodule K, V z ∈ complexifySubmodule K) ∧
        (∀ z ∈ complexifySubmodule K, conjugation z ∈ complexifySubmodule K)) ∧
      (F : Set (Submodule ℝ E)).Pairwise
        (fun K L => (complexifySubmodule K).IsOrtho (complexifySubmodule L)) ∧
      F.sup (fun K => complexifySubmodule K) = ⊤ := by
  obtain ⟨F, hF, hpair, hspan⟩ :=
    exists_orthogonal_real_blocks_of_isStarProjection A hA
  refine ⟨F, ?_, ?_, sup_complexifySubmodule_eq_top F hspan⟩
  · intro K hK
    obtain ⟨hK0, hdim, hX, hY⟩ := hF K hK
    have hdimC : Module.finrank ℂ (complexifySubmodule K) = Module.finrank ℝ K := by
      rw [← (complexifySubmoduleEquiv K).toLinearEquiv.finrank_eq, finrank_complex]
    have hdimR := Module.finrank_mul_finrank ℝ ℂ (complexifySubmodule K)
    rw [Complex.finrank_real_complex, hdimC] at hdimR
    refine ⟨hK0, hdim, hdimC ▸ hdim, by omega, ?_, ?_⟩
    · intro z hz
      rw [hV]
      change a • z + b • A z ∈ complexifySubmodule K
      exact (complexifySubmodule K).add_mem ((complexifySubmodule K).smul_mem _ hz)
        ((complexifySubmodule K).smul_mem _
          (invariant_complexifySubmodule_of_parts A K hX hY z hz))
    · intro z hz
      exact (conjugation_mem_complexifySubmodule_iff K z).mpr hz
  · intro K hK L hL hKL
    exact isOrtho_complexifySubmodule K L (hpair hK hL hKL)

section AbstractConjugation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

/-- Two-phase operators on an abstract complex Hilbert space admit complete
orthogonal invariant blocks of complex dimension at most two, simultaneously
invariant under any specified isometric conjugation. Thus each is a real
block of dimension at most four in the stationary transport problem. -/
theorem exists_orthogonal_blocks_of_two_phase_and_conjugation
    (J : H →ₛₗ[starRingEnd ℂ] H) (hJ : Isometry J)
    (hinv : Function.Involutive J)
    (A V : H →L[ℂ] H) (hA : IsStarProjection A)
    (a b : ℂ) (hV : V = a • 1 + b • A) :
    ∃ G : Finset (Submodule ℂ H),
      (∀ K ∈ G, K ≠ ⊥ ∧ Module.finrank ℂ K ≤ 2 ∧
        Module.finrank ℝ K ≤ 4 ∧
        (∀ x ∈ K, V x ∈ K) ∧ (∀ x ∈ K, J x ∈ K)) ∧
      (G : Set (Submodule ℂ H)).Pairwise Submodule.IsOrtho ∧ G.sup id = ⊤ := by
  classical
  let e := realPointsComplexificationEquiv J hJ hinv
  let A' := e.symm.conjStarAlgEquiv A
  let V' := e.symm.conjStarAlgEquiv V
  have hA' : IsStarProjection A' := hA.map e.symm.conjStarAlgEquiv
  have hV' : V' = a • 1 + b • A' := by
    simpa only [map_add, map_smul, map_one] using
      congrArg e.symm.conjStarAlgEquiv hV
  obtain ⟨F, hF, hpair, hspan⟩ :=
    exists_orthogonal_small_real_blocks_of_two_phase A' V' hA' a b hV'
  let f := fun K : Submodule ℝ (realPoints J) =>
    (complexifySubmodule K).map e.toLinearMap
  let G := F.image f
  refine ⟨G, ?_, ?_, ?_⟩
  · intro K hK
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨hL0, hdim, hdimC, _, hVL, hJL⟩ := hF L hL
    have hmapdim : Module.finrank ℂ (f L) =
        Module.finrank ℂ (complexifySubmodule L) := e.toLinearEquiv.finrank_map_eq _
    have hdimR := Module.finrank_mul_finrank ℝ ℂ (f L)
    rw [Complex.finrank_real_complex, hmapdim] at hdimR
    refine ⟨?_, hmapdim ▸ hdimC, by omega, ?_, ?_⟩
    · intro hz
      have hzero : Module.finrank ℂ (complexifySubmodule L) = 0 := by
        rw [← hmapdim, hz]
        exact finrank_bot ℂ H
      rw [← (complexifySubmoduleEquiv L).toLinearEquiv.finrank_eq] at hzero
      exact hL0 (Submodule.finrank_eq_zero.mp
        ((finrank_complex (E := L)).symm.trans hzero))
    · rintro x ⟨z, hz, rfl⟩
      refine ⟨V' z, hVL z hz, ?_⟩
      simp [V', LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
    · rintro x ⟨z, hz, rfl⟩
      refine ⟨conjugation z, hJL z hz, ?_⟩
      exact (realPointsComplexificationEquiv_conjugation J hJ hinv z).symm
  · intro K hK L hL hKL
    obtain ⟨K', hK', rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨L', hL', rfl⟩ := Finset.mem_image.mp hL
    exact (hpair hK' hL' (fun h => hKL (congrArg f h))).map e.toLinearIsometry
  · let S := G.sup id
    have hle : F.sup (fun K => complexifySubmodule K) ≤ S.comap e.toLinearMap := by
      apply Finset.sup_le
      intro K hK z hz
      have hmem : f K ∈ G := Finset.mem_image.mpr ⟨K, hK, rfl⟩
      have hKS : f K ≤ S := Finset.le_sup (f := id) hmem
      exact hKS ⟨z, hz, rfl⟩
    rw [hspan] at hle
    apply top_unique
    intro x _
    have hz : e.symm x ∈ S.comap e.toLinearMap := hle Submodule.mem_top
    change e (e.symm x) ∈ S at hz
    rwa [e.apply_symm_apply] at hz

end AbstractConjugation

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
