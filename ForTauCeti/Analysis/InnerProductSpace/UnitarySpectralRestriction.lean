/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SpectralTrace
public import ForTauCeti.Analysis.InnerProductSpace.FiniteUnitaryRestriction
public import ForTauCeti.Analysis.CStarAlgebra.TwoPointSpectrum

/-!
# Spectral level restrictions of finite unitary operators

A finite invariant subspace on which a functional calculus is scalar has
unitary spectrum in the corresponding scalar level set. A two-point level
set therefore gives an actual two-phase orthogonal-projection restriction.

This classical spectral-theorem argument is adapted from the existing
`SmoothedGradientBlocks` proof, with the symbol and level made explicit.
No optimization or historical novelty is asserted.
-/

public section

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

set_option maxHeartbeats 600000 in
-- Elaborating the restricted eigenspectrum and scalar CFC action crosses nested subspace carriers.
/-- An actual unitary restriction has two phases whenever its scalar CFC
level has at most two unit-circle preimages. Repeated roots and empty
subspaces are allowed. -/
theorem exists_two_phase_restriction_of_cfc_level
    (f : ℂ → ℂ) (c a b : ℂ) (U : unitary (E →L[ℂ] E)) (N : Submodule ℂ E)
    (hinv : ∀ x ∈ N, (U : E →L[ℂ] E) x ∈ N)
    (hlevel : ∀ x ∈ N, cfc f (U : E →L[ℂ] E) x = c • x)
    (hroots : ∀ z : ℂ, ‖z‖ = 1 → f z = c → z = a ∨ z = b) :
    ∃ (V : N ≃ₗᵢ[ℂ] N) (P : N →L[ℂ] N),
      IsStarProjection P ∧ (∀ x : N, (V x : E) = (U : E →L[ℂ] E) x) ∧
      (V : N →L[ℂ] N) = a • 1 + (b - a) • P := by
  obtain ⟨V, hV, _, _⟩ :=
    (Unitary.linearIsometryEquiv U).exists_restriction_of_finite_invariant N hinv
  let : IsStarNormal (V : N →L[ℂ] N) :=
    isStarNormal_of_mem_unitary (Unitary.linearIsometryEquiv.symm V).property
  let := isStarNormal_of_mem_unitary U.property
  have hs : spectrum ℂ (V : N →L[ℂ] N) ⊆ {a, b} := by
    intro mu hmu
    rw [_root_.ContinuousLinearMap.spectrum_eq] at hmu
    obtain ⟨x, hx⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.2 hmu).exists_hasEigenvector
    have hx0 : (x : E) ≠ 0 := fun h => hx.2 (Subtype.ext h)
    have hxU : (U : E →L[ℂ] E) (x : E) = mu • (x : E) :=
      (hV x).symm.trans (congrArg (fun y : N => (y : E)) hx.apply_eq_smul)
    have hnorm : ‖mu‖ = 1 := by
      have h := _root_.ContinuousLinearMap.norm_map_of_mem_unitary U.2 (x : E)
      rw [hxU, norm_smul] at h
      exact mul_right_cancel₀ (norm_ne_zero_iff.2 hx0) (by simpa using h)
    have hsymbol := ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal f hxU
    rw [hlevel x x.2] at hsymbol
    have hscalar : f mu = c := (smul_left_injective ℂ hx0 hsymbol).symm
    exact hroots mu hnorm hscalar
  obtain ⟨P, hP, hrepr⟩ := exists_isStarProjection_eq_affine_of_spectrum_subset_pair
    (V : N →L[ℂ] N) a b hs
  exact ⟨V, P, hP, hV, hrepr⟩

end TauCeti
