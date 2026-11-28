/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/

module

public import DavisKahan.Specialized.FreeBeam.BeamClassicalReal
public import ForTauCeti.Analysis.InnerProductSpace.CompactSelfAdjointClassification
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Tactic

/-!
# Spectrum of the real free-beam realization

This file runs the compact-resolvent/Fredholm argument directly on the real Section 9 model.
It proves that every real spectral point is an eigenvalue, classifies the positive spectrum by
the free-beam characteristic equation, and obtains the source gap `{0} ∪ (500, ∞)`.
-/

public section

open scoped InnerProductSpace ENNReal
open MeasureTheory TauCeti


namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model
namespace Real

noncomputable section

/-! ## Compact variational resolvent -/

/-- The variational resolvent is the embedding composed with its adjoint. -/
theorem beamResolvent_eq :
    beamCoerciveFormData.resolvent =
      beamEmbed.comp (ContinuousLinearMap.adjoint beamEmbed) :=
  Scalar.beamResolvent_eq (𝕜 := ℝ)

/-- The real variational resolvent is compact. -/
theorem isCompactOperator_beamResolvent :
    IsCompactOperator beamCoerciveFormData.resolvent :=
  beamCoerciveFormData.isCompactOperator_resolvent isCompactOperator_beamEmbed

/-- Invert a nonzero resolvent eigenvalue into a beam-operator eigenvalue. -/
theorem exists_beamOperator_apply_of_beamResolvent_smul {mu : ℝ} (hmu : mu ≠ 0)
    {u : BeamL2} (huv : beamCoerciveFormData.resolvent u = mu • u) :
    ∃ h : u ∈ beamOperator.domain,
      beamOperator ⟨u, h⟩ = (mu⁻¹ - 1) • u := by
  have hRmu : beamCoerciveFormData.resolvent (mu⁻¹ • u) = u := by
    rw [map_smul, huv, smul_smul, inv_mul_cancel₀ hmu, one_smul]
  obtain ⟨humem, hB⟩ := beamShiftedFormData.exists_beamOperator_apply_of_resolvent_eq hRmu
  exact ⟨humem, hB.trans (by rw [sub_smul, one_smul])⟩

/-- A fixed vector of the resolvent is an affine zero mode. -/
theorem exists_affine_of_beamResolvent_eq_self {u : BeamL2}
    (huv : beamCoerciveFormData.resolvent u = u) :
    ∃ a b : ℝ, u = affineLp a b := by
  obtain ⟨humem, hbeam⟩ :=
    exists_beamOperator_apply_of_beamResolvent_smul (mu := 1) one_ne_zero
      (by simpa using huv)
  refine exists_affine_of_beamOperator_eq_zero (x := ⟨u, humem⟩) ?_
  rw [hbeam, inv_one, sub_self, zero_smul]

/-- Nonzero real eigenvalues of the variational resolvent are either the affine value `1` or
`(1 + beta^4)⁻¹` for a positive free-beam characteristic root. -/
theorem beamResolvent_eigenvalue_classify {mu : ℝ} (hmu : mu ≠ 0)
    {u : BeamL2} (hu0 : u ≠ 0)
    (huv : beamCoerciveFormData.resolvent u = mu • u) :
    mu = 1 ∨ ∃ beta : ℝ, 0 < beta ∧ characteristic beta = 0 ∧
      mu = (1 + beta ^ 4)⁻¹ := by
  obtain ⟨humem, hbeam⟩ := exists_beamOperator_apply_of_beamResolvent_smul hmu huv
  set nu : ℝ := mu⁻¹ - 1 with hnu
  have hnu_nonneg : 0 ≤ nu := by
    apply nonneg_of_beamOperator_eigen (x := ⟨u, humem⟩) hu0
    simpa [nu] using hbeam
  rcases eq_or_lt_of_le hnu_nonneg with hzero | hpos
  · left
    have h1 : mu⁻¹ = 1 := by
      rw [hnu] at hzero
      linarith
    exact inv_eq_one.mp h1
  · right
    have heig : beamOperator ⟨u, humem⟩ = nu • u := by
      simpa [nu] using hbeam
    obtain ⟨beta, hβ, hchar, hnueq⟩ :=
      exists_characteristic_of_eigen hpos (x := ⟨u, humem⟩) hu0 heig
    refine ⟨beta, hβ, hchar, ?_⟩
    have hmuinv : mu⁻¹ = 1 + beta ^ 4 := by
      rw [hnu] at hnueq
      linarith
    rw [← hmuinv, inv_inv]

/-! ## Fredholm bridge -/

/-- Every real spectral point of the free beam is an eigenvalue. The spectral
parameter of the shifted operator is `lam + 1`, and the compact variational
resolvent has the corresponding eigenvalue `(lam + 1)⁻¹`. -/
theorem exists_eigenvector_of_mem_realSpectrum_beamOperator {lam : ℝ}
    (hlam : lam ∈ _root_.LinearPMap.realSpectrum beamOperator) :
    ∃ x : beamOperator.domain, (x : BeamL2) ≠ 0 ∧
      beamOperator x = lam • (x : BeamL2) := by
  let R := beamCoerciveFormData.resolvent
  have hinj : Function.Injective R := beamCoerciveFormData.resolvent_injective
  let c : ℝ := lam + 1
  have hshift : c ∈ (R.toLinearMap.toPMap ⊤).inverse.spectrum := by
    have h := _root_.LinearPMap.mem_realSpectrum_iff.mp hlam
    change lam ∈ beamShiftedFormData.beamOperator.spectrum at h
    rw [beamShiftedFormData.beamOperator_eq_subScalar, _root_.LinearPMap.mem_spectrum_iff,
      TauCeti.LinearPMap.mem_resolventSet_subScalar_iff] at h
    change lam + 1 ∉ beamCoerciveFormData.associatedOperator.resolventSet at h
    rw [beamCoerciveFormData.associatedOperator_eq_inverse] at h
    exact (_root_.LinearPMap.mem_spectrum_iff _ _).mpr h
  have hc : c ≠ 0 := by
    intro h0
    rw [h0] at hshift
    exact (_root_.LinearPMap.mem_spectrum_iff _ _).mp hshift
      (R.zero_mem_resolventSet_inverse_toPMap_top hinj)
  have hev := (R.mem_spectrum_inverse_toPMap_top_iff_hasEigenvalue hinj
    isCompactOperator_beamResolvent hc).mp hshift
  obtain ⟨v, hvmem, hv0⟩ := hev.exists_hasEigenvector
  have hveq : R v = c⁻¹ • v := by
    simpa only [Module.End.mem_genEigenspace_one, ContinuousLinearMap.coe_coe] using hvmem
  obtain ⟨hvdom, hbeam⟩ := exists_beamOperator_apply_of_beamResolvent_smul (inv_ne_zero hc) hveq
  refine ⟨⟨v, hvdom⟩, hv0, ?_⟩
  simpa only [inv_inv, c, add_sub_cancel_right] using hbeam

/-- The real spectrum consists only of zero and characteristic fourth powers. -/
theorem realSpectrum_beamOperator_subset :
    _root_.LinearPMap.realSpectrum beamOperator ⊆
      {0} ∪ {lam : ℝ | ∃ beta : ℝ,
        0 < beta ∧ characteristic beta = 0 ∧ lam = beta ^ 4} := by
  intro lam hlam
  obtain ⟨x, hx0, heig⟩ := exists_eigenvector_of_mem_realSpectrum_beamOperator hlam
  rcases eq_or_lt_of_le (nonneg_of_beamOperator_eigen hx0 heig) with h0 | hpos
  · exact Or.inl (Set.mem_singleton_iff.mpr h0.symm)
  · exact Or.inr (exists_characteristic_of_eigen hpos hx0 heig)

/-- Source spectral gap: every nonzero spectral point of the real free beam exceeds `500`. -/
theorem realSpectrum_beamOperator_subset_gap :
    _root_.LinearPMap.realSpectrum beamOperator ⊆ ({0} : Set ℝ) ∪ Set.Ioi 500 := by
  intro lam hlam
  rcases realSpectrum_beamOperator_subset hlam with h0 | ⟨beta, hβ, hchar, hlameq⟩
  · exact Or.inl h0
  · refine Or.inr ?_
    rw [Set.mem_Ioi, hlameq]
    exact Classical.five_hundred_lt_pow_four_of_characteristic_eq_zero hβ hchar

end

end Real
end Model
end FreeBeam
end DavisKahan
end TauCeti
