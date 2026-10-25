/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.RealBlockDescent
import ForTauCeti.LinearAlgebra.InvolutionDoubledBlock

/-!
# Exact ranks of the real reflection-paired spectral blocks

A doubled block from a disjoint positive spectral half has twice the
original complex dimension. Each signed real reflection space occupies
exactly half the block. In particular source-reflection doubling gives
the exact source ranks needed to apply the one- and two-angle transport
minima. A dimension upper bound alone would not establish this balance.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Signed real eigenspaces are exactly the real preimages of the complex
eigenspaces of an operator commuting with coordinate conjugation. -/
theorem realSubmodule_eigenspace
    (T : RealComplexification E →L[ℂ] RealComplexification E)
    (hT : ∀ z, T (conjugation z) = conjugation (T z)) (e : ℝ) :
    realSubmodule (Module.End.eigenspace T.toLinearMap (e : ℂ)) =
      Module.End.eigenspace (realify T).toLinearMap e := by
  ext x
  change (ofReal x ∈ Module.End.eigenspace T.toLinearMap (e : ℂ)) ↔ _
  rw [Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff]
  have hreal : T (ofReal x) = ofReal (realify T x) := by
    calc
      _ = complexify (realify T) (ofReal x) :=
        congrArg (fun A : RealComplexification E →L[ℂ] RealComplexification E =>
          A (ofReal x)) (complexify_realify hT).symm
      _ = _ := complexify_ofReal _ _
  have hsmul : ofReal (e • x) = (e : ℂ) • ofReal x := by
    simpa only [coe_real_smul] using ofReal.map_smul e x
  change T (ofReal x) = (e : ℂ) • ofReal x ↔ realify T x = e • x
  rw [hreal, ← hsmul, ofReal.injective.eq_iff]

/-- A conjugation-compatible doubled block has exact ambient and signed
reflection ranks. The original half need not be an eigenspace of any
operator, only disjoint from its reflection. -/
theorem finrank_real_doubled_block [FiniteDimensional ℝ E]
    (R : RealComplexification E ≃ₗᵢ[ℂ] RealComplexification E)
    (hR : Function.Involutive R)
    (hRC : ∀ z, R (conjugation z) = conjugation (R z))
    (S : Submodule ℂ (RealComplexification E))
    (hS : Disjoint S (S.map R.toLinearMap))
    (hSJ : ∀ z ∈ S, R (conjugation z) ∈ S) :
    let N := realSubmodule (S ⊔ S.map R.toLinearMap)
    Module.finrank ℝ N = 2 * Module.finrank ℂ S ∧
      ∀ e : ℝ, e ^ 2 = 1 →
        Module.finrank ℝ ↥(N ⊓ Module.End.eigenspace
          (realify (R : RealComplexification E →L[ℂ] RealComplexification E)).toLinearMap e) =
            Module.finrank ℂ S := by
  let M := S ⊔ S.map R.toLinearMap
  have hCM : ∀ z ∈ M, conjugation z ∈ M :=
    (doubled_block_invariant R hR hRC 1 (fun _ => rfl) S hSJ (fun _ hz => hz)).2.1
  constructor
  · rw [finrank_realSubmodule M hCM]
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq S (S.map R.toLinearMap)
    rw [hS.eq_bot, finrank_bot, R.toLinearEquiv.finrank_map_eq S] at hsum
    change Module.finrank ℂ M + 0 = _ at hsum
    omega
  · intro e he
    let T := Module.End.eigenspace R.toLinearMap (e : ℂ)
    have hCT : ∀ z ∈ T, conjugation z ∈ T := by
      intro z hz
      rw [Module.End.mem_eigenspace_iff] at hz ⊢
      change R z = (e : ℂ) • z at hz
      change R (conjugation z) = (e : ℂ) • conjugation z
      rw [hRC, hz, conjugation_complex_smul, Complex.conj_ofReal]
    have hCMT : ∀ z ∈ M ⊓ T, conjugation z ∈ M ⊓ T :=
      fun z hz => ⟨hCM z hz.1, hCT z hz.2⟩
    have hdescent : realSubmodule (M ⊓ T) =
        realSubmodule M ⊓ Module.End.eigenspace
          (realify (R : RealComplexification E →L[ℂ] RealComplexification E)).toLinearMap e := by
      change realSubmodule M ⊓ realSubmodule T = _
      congr 1
      exact realSubmodule_eigenspace
        (R : RealComplexification E →L[ℂ] RealComplexification E) hRC e
    rw [← hdescent, finrank_realSubmodule (M ⊓ T) hCMT]
    exact finrank_doubled_inf_eigenspace R.toLinearEquiv hR S hS (e : ℂ)
      (by exact_mod_cast he)

/-- Source-reflection doubling has exactly half its real dimension in the
source. For original half-dimension one or two these are precisely the
balanced one- and two-angle real transport blocks. -/
theorem finrank_real_source_doubled_block [FiniteDimensional ℝ E]
    (K S : Submodule ℂ (RealComplexification E))
    (hRC : ∀ z, K.reflection (conjugation z) = conjugation (K.reflection z))
    (hS : S.IsOrtho (S.map K.reflection.toLinearMap))
    (hSJ : ∀ z ∈ S, K.reflection (conjugation z) ∈ S) :
    let N := realSubmodule (S ⊔ S.map K.reflection.toLinearMap)
    Module.finrank ℝ N = 2 * Module.finrank ℂ S ∧
      Module.finrank ℝ ↥(N ⊓ realSubmodule K) = Module.finrank ℂ S := by
  obtain ⟨hdim, hsign⟩ := finrank_real_doubled_block K.reflection
    K.reflection_involutive hRC S hS.disjoint hSJ
  have heig : Module.End.eigenspace
      (realify (K.reflection : RealComplexification E →L[ℂ] RealComplexification E)).toLinearMap
      (1 : ℝ) = realSubmodule K := by
    rw [← realSubmodule_eigenspace
      (K.reflection : RealComplexification E →L[ℂ] RealComplexification E) hRC 1]
    congr 1
    ext z
    rw [Module.End.mem_eigenspace_iff]
    change K.reflection z = (1 : ℂ) • z ↔ z ∈ K
    rw [one_smul]
    exact K.reflection_eq_self_iff z
  refine ⟨hdim, ?_⟩
  have hfixed := hsign 1 (by norm_num)
  change Module.finrank ℝ ↥(realSubmodule (S ⊔ S.map K.reflection.toLinearMap) ⊓
    Module.End.eigenspace (realify
      (K.reflection : RealComplexification E →L[ℂ] RealComplexification E)).toLinearMap 1) =
        Module.finrank ℂ S at hfixed
  rwa [heig] at hfixed

/-- The actual small invariant real block also has the exact balanced source
rank. Its dimension bound is supplemented by source data, with no supplied
principal-angle coordinates or nondegeneracy assumption on the restriction. -/
theorem exists_small_real_source_balanced_block [FiniteDimensional ℝ E]
    (K S : Submodule ℂ (RealComplexification E))
    (hRC : ∀ z, K.reflection (conjugation z) = conjugation (K.reflection z))
    (U : RealComplexification E →L[ℂ] RealComplexification E)
    (hUC : ∀ z, U (conjugation z) = conjugation (U z))
    (hS0 : S ≠ ⊥) (hdim : Module.finrank ℂ S ≤ 2)
    (hS : S.IsOrtho (S.map K.reflection.toLinearMap))
    (hSJ : ∀ z ∈ S, K.reflection (conjugation z) ∈ S)
    (hUS : ∀ z ∈ S, U z ∈ S) :
    ∃ N : Submodule ℝ E,
      complexifySubmodule N = S ⊔ S.map K.reflection.toLinearMap ∧
      N ≠ ⊥ ∧ Module.finrank ℝ N ≤ 4 ∧
      (∀ x ∈ N, realify U x ∈ N) ∧
      (∀ x ∈ N, realify
        (K.reflection : RealComplexification E →L[ℂ] RealComplexification E) x ∈ N) ∧
      Module.finrank ℝ N = 2 * Module.finrank ℂ S ∧
      Module.finrank ℝ ↥(N ⊓ realSubmodule K) = Module.finrank ℂ S := by
  obtain ⟨N, hN, hN0, hNdim, hUN, hRN⟩ := exists_small_real_doubled_block
    K.reflection K.reflection_involutive hRC U hUC S hS0 hdim hSJ hUS
  have hreal : N = realSubmodule (S ⊔ S.map K.reflection.toLinearMap) := by
    have h := congrArg realSubmodule hN
    simpa only [realSubmodule_complexifySubmodule] using h
  have hrank := finrank_real_source_doubled_block K S hRC hS hSJ
  rw [← hreal] at hrank
  exact ⟨N, hN, hN0, hNdim, hUN, hRN, hrank⟩

/-- A complete reflection-paired level descends to a complete orthogonal
family of actual real blocks with exact source ranks. Every member is
either a two-dimensional rank-one problem or a four-dimensional rank-two
problem, including degenerate restricted principal angles. -/
theorem exists_orthogonal_real_source_balanced_blocks [FiniteDimensional ℝ E]
    (K : Submodule ℂ (RealComplexification E))
    (hRC : ∀ z, K.reflection (conjugation z) = conjugation (K.reflection z))
    (U : RealComplexification E →L[ℂ] RealComplexification E)
    (hUC : ∀ z, U (conjugation z) = conjugation (U z))
    (L : Submodule ℂ (RealComplexification E))
    (hL : L.IsOrtho (L.map K.reflection.toLinearMap))
    (F : Finset (Submodule ℂ (RealComplexification E)))
    (hF : ∀ S ∈ F, S ≠ ⊥ ∧ Module.finrank ℂ S ≤ 2 ∧
      (∀ z ∈ S, K.reflection (conjugation z) ∈ S) ∧ (∀ z ∈ S, U z ∈ S))
    (hpair : (F : Set (Submodule ℂ (RealComplexification E))).Pairwise Submodule.IsOrtho)
    (hspan : F.sup id = L) :
    ∃ H : Finset (Submodule ℝ E),
      (∀ N ∈ H, N ≠ ⊥ ∧ Module.finrank ℝ N ≤ 4 ∧
        (∀ x ∈ N, realify U x ∈ N) ∧
        (∀ x ∈ N, realify
          (K.reflection : RealComplexification E →L[ℂ] RealComplexification E) x ∈ N) ∧
        ((Module.finrank ℝ N = 2 ∧ Module.finrank ℝ ↥(N ⊓ realSubmodule K) = 1) ∨
          (Module.finrank ℝ N = 4 ∧ Module.finrank ℝ ↥(N ⊓ realSubmodule K) = 2))) ∧
      (H : Set (Submodule ℝ E)).Pairwise Submodule.IsOrtho ∧
      complexifySubmodule (H.sup id) = L ⊔ L.map K.reflection.toLinearMap := by
  obtain ⟨H, hH, horth, hcover, horigin⟩ := exists_orthogonal_real_doubled_blocks
    K.reflection K.reflection_involutive hRC U hUC L hL F hF hpair hspan
  refine ⟨H, ?_, horth, hcover⟩
  intro N hN
  obtain ⟨hN0, hNdim, hUN, hRN⟩ := hH N hN
  obtain ⟨S, hS, hNS⟩ := horigin N hN
  have hSL : S ≤ L := by
    rw [← hspan]
    exact Finset.le_sup (f := id) hS
  have hSS : S.IsOrtho (S.map K.reflection.toLinearMap) :=
    hL.mono hSL (Submodule.map_mono hSL)
  have hreal : N = realSubmodule (S ⊔ S.map K.reflection.toLinearMap) := by
    have h := congrArg realSubmodule hNS
    simpa only [realSubmodule_complexifySubmodule] using h
  have hrank := finrank_real_source_doubled_block K S hRC hSS (hF S hS).2.2.1
  rw [← hreal] at hrank
  have hpos : 0 < Module.finrank ℂ S := by
    have hn : Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr (hF S hS).1
    exact Module.finrank_pos
  have hsmall := (hF S hS).2.1
  refine ⟨hN0, hNdim, hUN, hRN, ?_⟩
  rcases (by omega : Module.finrank ℂ S = 1 ∨ Module.finrank ℂ S = 2) with h1 | h2
  · left
    constructor <;> omega
  · right
    constructor <;> omega

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
