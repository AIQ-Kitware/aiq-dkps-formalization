/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Interop.Spectra.BoundedSelfAdjointSpectralProjection
import DavisKahan.Interop.Spectra.BoundedFromSpectrum
import DavisKahan.Interop.Spectra.RealSpectrumBridge
import Spectra.SpectralTheory.Calculus.Bounded
import Spectra.SpectralTheory.Calculus.PMapBounded
import Spectra.SpectralTheory.Calculus.SquareBridge
import Spectra.SpectralTheory.SeparatedIntertwiner
import Spectra.Modular.Cocycle.ModularSqrtSquare
import Spectra.Modular.Tomita.BoundedPicture
import Spectra.QuantumMechanics.BornRule.Observable

/-!
# Bounded Borel calculus for bounded self-adjoint operators

Vendored Spectra already contains the required real-line bounded Borel
functional calculus.  For a self-adjoint operator `T`,
`Spectra.QuantumMechanics.SpectralTheory.spectralCalculus
(genToGroup T.selfAdjoint)` integrates every globally bounded measurable symbol
against the canonical real spectral measure.

The only missing layer for the Sylvester finite-step argument is a bridge from a
bounded continuous linear map to that calculus, together with the fact that
symbols need only be bounded on the actual spectrum.  We obtain the latter by
zero-extending the symbol off the spectrum.  The bounded-on-spectrum hypothesis
is explicit: measurability alone does not imply boundedness, even on a compact
set.
-/

namespace TauCeti
namespace DavisKahanExt

open MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators
open Spectra
open Spectra.Borel
open Spectra.YosidaHille
open Spectra.QuantumMechanics.BornRule.Observable
open Spectra.QuantumMechanics.SpectralTheory
open DavisKahan.Experimental.SpectraBridge

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The Spectra one-parameter group attached to a bounded self-adjoint map. -/
noncomputable def boundedSelfAdjointGroup
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) :
    OneParameterUnitaryGroup (H := H) :=
  genToGroup (boundedSelfAdjointOperator A hA).selfAdjoint

/-- Complex-valued globally bounded Borel calculus of a bounded self-adjoint
map.  This is a direct wrapper around Spectra's production calculus. -/
noncomputable def boundedSelfAdjointBorelCalculusC
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (f : ℝ → ℂ) (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ x : ℝ, ‖f x‖ ≤ C) : H →L[ℂ] H :=
  spectralCalculus (boundedSelfAdjointGroup A hA) f hf hfb

/-- Application of the bridged full-domain self-adjoint pmap is the original map. -/
theorem boundedSelfAdjointOperator_toLinearPMap_apply
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) (y : H)
    (hy : y ∈ (boundedSelfAdjointOperator A hA).toLinearPMap.domain) :
    (boundedSelfAdjointOperator A hA).toLinearPMap ⟨y, hy⟩ = A y := rfl

/-- The Spectra resolvent set of the bridged full-domain realization is exactly the
invertibility locus of `A - z` in the bounded operator algebra. -/
theorem mem_resolventSet_toLinearPMap_iff
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) (z : ℂ) :
    z ∈ Spectra.Resolvent.resolventSet (boundedSelfAdjointOperator A hA).toLinearPMap ↔
      IsUnit (A - z • (1 : H →L[ℂ] H)) := by
  constructor
  · rintro ⟨R, hleft, hright⟩
    refine ⟨⟨A - z • (1 : H →L[ℂ] H), R, ?_, ?_⟩, rfl⟩
    · apply ContinuousLinearMap.ext
      intro φ
      obtain ⟨h, hφ⟩ := hright φ
      exact hφ
    · apply ContinuousLinearMap.ext
      intro x
      exact hleft ⟨x, Submodule.mem_top⟩
  · rintro ⟨u, hu⟩
    have hval : (u : H →L[ℂ] H) = A - z • (1 : H →L[ℂ] H) := hu
    refine ⟨↑u⁻¹, ?_, ?_⟩
    · intro ψ
      have hinv : (↑u⁻¹ : H →L[ℂ] H) * (A - z • (1 : H →L[ℂ] H)) = 1 := by
        rw [← hval]; exact u.inv_mul
      exact ContinuousLinearMap.ext_iff.mp hinv (ψ : H)
    · intro φ
      refine ⟨Submodule.mem_top, ?_⟩
      have hinv : (A - z • (1 : H →L[ℂ] H)) * (↑u⁻¹ : H →L[ℂ] H) = 1 := by
        rw [← hval]; exact u.mul_inv
      exact ContinuousLinearMap.ext_iff.mp hinv φ

/-- The real spectrum of the bounded map agrees with the Spectra spectrum of
its full-domain self-adjoint realization. -/
theorem realSpectrum_eq_boundedSelfAdjoint_spectrum
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) :
    realSpectrum A =
      Spectra.Resolvent.spectrum (boundedSelfAdjointOperator A hA).toLinearPMap := by
  ext r
  show (r : ℂ) ∈ spectrum ℂ A ↔ (r : ℂ) ∉ Spectra.Resolvent.resolventSet _
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one,
    ← IsUnit.neg_iff, neg_sub, mem_resolventSet_toLinearPMap_iff A hA (r : ℂ)]

/-- The real spectrum of a bounded self-adjoint operator is closed. -/
theorem isClosed_realSpectrum_boundedSelfAdjoint
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) :
    IsClosed (realSpectrum A) := by
  rw [realSpectrum_eq_boundedSelfAdjoint_spectrum A hA]
  exact isClosed_spectrum_of_isSelfAdjoint (boundedSelfAdjointOperator A hA)

/-- The real spectrum is measurable. -/
theorem measurableSet_realSpectrum_boundedSelfAdjoint
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) :
    MeasurableSet (realSpectrum A) :=
  (isClosed_realSpectrum_boundedSelfAdjoint A hA).measurableSet

/-- Restrict a real symbol to the actual spectrum and coerce it to `ℂ`. -/
noncomputable def spectrumRestrictedSymbol
    (A : H →L[ℂ] H) (f : ℝ → ℝ) : ℝ → ℂ :=
  Set.indicator (realSpectrum A) fun x => (f x : ℂ)

/-- Measurability of the spectrum-restricted symbol. -/
theorem measurable_spectrumRestrictedSymbol
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (f : ℝ → ℝ) (hf : Measurable f) :
    Measurable (spectrumRestrictedSymbol A f) := by
  exact Complex.measurable_ofReal.comp hf |>.indicator
    (measurableSet_realSpectrum_boundedSelfAdjoint A hA)

/-- A spectral bound becomes a global bound after zero extension. -/
theorem bounded_spectrumRestrictedSymbol
    (A : H →L[ℂ] H) (f : ℝ → ℝ)
    (hf : BoundedOnSpectrum A f) :
    ∃ C : ℝ, ∀ x : ℝ, ‖spectrumRestrictedSymbol A f x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := hf
  refine ⟨C, fun x => ?_⟩
  by_cases hx : x ∈ realSpectrum A
  · rw [spectrumRestrictedSymbol, Set.indicator_of_mem hx, Complex.norm_real,
      Real.norm_eq_abs]
    exact hC x hx
  · rw [spectrumRestrictedSymbol, Set.indicator_of_notMem hx, norm_zero]
    exact hC0

/-- Real-valued bounded-on-spectrum Borel calculus.  The explicit boundedness
hypothesis is mathematically necessary. -/
noncomputable def boundedSelfAdjointBorelCalculus
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (f : ℝ → ℝ) (hf : Measurable f) (hfb : BoundedOnSpectrum A f) :
    H →L[ℂ] H :=
  boundedSelfAdjointBorelCalculusC A hA
    (spectrumRestrictedSymbol A f)
    (measurable_spectrumRestrictedSymbol A hA f hf)
    (bounded_spectrumRestrictedSymbol A f hfb)

/-- The complex calculus of an indicator is the canonical spectral projection. -/
theorem boundedSelfAdjointBorelCalculusC_indicator
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    boundedSelfAdjointBorelCalculusC A hA
      (Set.indicator s fun _ => (1 : ℂ))
      (measurable_const.indicator hs)
      (indicator_one_bdd s) =
      boundedSelfAdjointSpectralProjection A hA s hs := by
  rfl

/-- The spectral measure of every vector is supported on the real spectrum. -/
theorem boundedSelfAdjoint_borelMeasure_support
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) (x : H) :
    (borelMeasure (boundedSelfAdjointGroup A hA) x).support ⊆ realSpectrum A := by
  rw [realSpectrum_eq_boundedSelfAdjoint_spectrum A hA]
  exact bornMeasure_support_subset_spectrum (boundedSelfAdjointOperator A hA) x

/-- Symbols agreeing on the real spectrum have the same bounded calculus. -/
theorem boundedSelfAdjointBorelCalculusC_congr_on_spectrum
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    {f g : ℝ → ℂ}
    (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hg : Measurable g) (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C)
    (hfg : ∀ x ∈ realSpectrum A, f x = g x) :
    boundedSelfAdjointBorelCalculusC A hA f hf hfb =
      boundedSelfAdjointBorelCalculusC A hA g hg hgb := by
  unfold boundedSelfAdjointBorelCalculusC
  apply spectralCalculus_congr_ae_forall
  intro x
  have hsupp := boundedSelfAdjoint_borelMeasure_support A hA x
  filter_upwards [Measure.support_mem_ae (μ := borelMeasure (boundedSelfAdjointGroup A hA) x)] with l hl
  exact hfg l (hsupp hl)

/-- Operator norm is bounded by a global pointwise symbol bound. -/
theorem norm_boundedSelfAdjointBorelCalculusC_le
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (f : ℝ → ℂ) (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    ‖boundedSelfAdjointBorelCalculusC A hA f hf hfb‖ ≤ C := by
  exact norm_spectralCalculus_le (boundedSelfAdjointGroup A hA) f hf hfb hC

/-- A spectrum-only pointwise bound controls a calculus difference. -/
theorem boundedSelfAdjointBorelCalculusC_norm_sub_le
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    {f g : ℝ → ℂ}
    (hf : Measurable f) (hfb : ∃ Cf : ℝ, ∀ x, ‖f x‖ ≤ Cf)
    (hg : Measurable g) (hgb : ∃ Cg : ℝ, ∀ x, ‖g x‖ ≤ Cg)
    {C : ℝ} (hC0 : 0 ≤ C)
    (h : ∀ x ∈ realSpectrum A, ‖f x - g x‖ ≤ C) :
    ‖boundedSelfAdjointBorelCalculusC A hA f hf hfb -
      boundedSelfAdjointBorelCalculusC A hA g hg hgb‖ ≤ C := by
  set q : ℝ → ℂ := Set.indicator (realSpectrum A) fun x => f x - g x with hq
  have hqm : Measurable q :=
    (hf.sub hg).indicator (measurableSet_realSpectrum_boundedSelfAdjoint A hA)
  have hqb : ∃ D : ℝ, ∀ x, ‖q x‖ ≤ D := by
    obtain ⟨Cf, hCf⟩ := hfb
    obtain ⟨Cg, hCg⟩ := hgb
    refine ⟨Cf + Cg, fun x => ?_⟩
    by_cases hx : x ∈ realSpectrum A
    · rw [hq, Set.indicator_of_mem hx]
      exact (norm_sub_le _ _).trans (add_le_add (hCf x) (hCg x))
    · rw [hq, Set.indicator_of_notMem hx, norm_zero]
      have hCf0 : 0 ≤ Cf := le_trans (norm_nonneg (f x)) (hCf x)
      have hCg0 : 0 ≤ Cg := le_trans (norm_nonneg (g x)) (hCg x)
      linarith
  have hqC : ∀ x, ‖q x‖ ≤ C := by
    intro x
    by_cases hx : x ∈ realSpectrum A
    · rw [hq, Set.indicator_of_mem hx]
      exact h x hx
    · rw [hq, Set.indicator_of_notMem hx, norm_zero]
      exact hC0
  have hsub : boundedSelfAdjointBorelCalculusC A hA f hf hfb -
      boundedSelfAdjointBorelCalculusC A hA g hg hgb =
      boundedSelfAdjointBorelCalculusC A hA q hqm hqb := by
    unfold boundedSelfAdjointBorelCalculusC
    rw [← spectralCalculus_sub (boundedSelfAdjointGroup A hA)
      f g hf hfb hg hgb (hf.sub hg) (bounded_sub hfb hgb)]
    apply spectralCalculus_congr_ae_forall
    intro x
    have hsupp := boundedSelfAdjoint_borelMeasure_support A hA x
    filter_upwards [Measure.support_mem_ae (μ := borelMeasure (boundedSelfAdjointGroup A hA) x)] with l hl
    rw [hq, Set.indicator_of_mem (hsupp hl)]
  rw [hsub]
  exact norm_boundedSelfAdjointBorelCalculusC_le A hA q hqm hqb hqC

/-- A globally bounded cut-off of the identity symbol. -/
noncomputable def boundedIdentitySymbol (A : H →L[ℂ] H) : ℝ → ℂ :=
  Set.indicator (Set.Icc (-‖A‖) ‖A‖) fun x => (x : ℂ)

/-- The cut-off identity symbol is measurable. -/
theorem measurable_boundedIdentitySymbol (A : H →L[ℂ] H) :
    Measurable (boundedIdentitySymbol A) := by
  exact Complex.measurable_ofReal.indicator measurableSet_Icc

/-- The cut-off identity symbol is globally bounded by `‖A‖`. -/
theorem bounded_boundedIdentitySymbol (A : H →L[ℂ] H) :
    ∃ C : ℝ, ∀ x, ‖boundedIdentitySymbol A x‖ ≤ C := by
  refine ⟨‖A‖, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (-‖A‖) ‖A‖
  · rw [boundedIdentitySymbol, Set.indicator_of_mem hx, Complex.norm_real,
      Real.norm_eq_abs]
    exact abs_le.mpr hx
  · rw [boundedIdentitySymbol, Set.indicator_of_notMem hx, norm_zero]
    exact norm_nonneg A

/-- Every real spectral value of a bounded operator lies in the norm interval. -/
theorem realSpectrum_subset_norm_Icc [Nontrivial H]
    (A : H →L[ℂ] H) : realSpectrum A ⊆ Set.Icc (-‖A‖) ‖A‖ := by
  intro x hx
  change (x : ℂ) ∈ spectrum ℂ A at hx
  have hnorm : ‖(x : ℂ)‖ ≤ ‖A‖ := spectrum.norm_le_norm_of_mem hx
  have habs : |x| ≤ ‖A‖ := by simpa using hnorm
  exact abs_le.mp habs

/-- The cut-off identity agrees with the identity on the real spectrum. -/
theorem boundedIdentitySymbol_eq [Nontrivial H]
    (A : H →L[ℂ] H) {x : ℝ} (hx : x ∈ realSpectrum A) :
    boundedIdentitySymbol A x = (x : ℂ) := by
  rw [boundedIdentitySymbol, Set.indicator_of_mem (realSpectrum_subset_norm_Icc A hx)]

/-- The bounded calculus of the cut-off identity is the original operator. -/
theorem boundedSelfAdjointBorelCalculusC_id [Nontrivial H]
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) :
    boundedSelfAdjointBorelCalculusC A hA (boundedIdentitySymbol A)
      (measurable_boundedIdentitySymbol A)
      (bounded_boundedIdentitySymbol A) = A := by
  let T := boundedSelfAdjointOperator A hA
  let U := boundedSelfAdjointGroup A hA
  apply ContinuousLinearMap.ext
  intro x
  have hxdomT : x ∈ T.domain := by
    rw [boundedSelfAdjointOperator_domain A hA]
    exact Submodule.mem_top
  have hgen : U.generator = T.toLinearPMap := by
    simpa [U, boundedSelfAdjointGroup] using generator_genToGroup T.selfAdjoint
  have hxdomU : x ∈ U.generator.domain := by
    rw [hgen]
    exact hxdomT
  have hidmem := mem_pmapDomain_id_of_mem_generator U ⟨x, hxdomU⟩
  have hcutmem : x ∈ ProjValMeasure.pmapDomain U.toPVM (boundedIdentitySymbol A) :=
    mem_pmapDomain_of_bounded U (boundedIdentitySymbol A)
      (measurable_boundedIdentitySymbol A) (bounded_boundedIdentitySymbol A) x
  have hae : boundedIdentitySymbol A =ᵐ[borelMeasure U x] fun s => (s : ℂ) := by
    have hsupp := boundedSelfAdjoint_borelMeasure_support A hA x
    filter_upwards [Measure.support_mem_ae (μ := borelMeasure U x)] with s hs
    exact boundedIdentitySymbol_eq A (hsupp hs)
  have hcongr := pmapOfPVM_congr_ae U
    (boundedIdentitySymbol A) (fun s => (s : ℂ))
    (measurable_boundedIdentitySymbol A) Complex.measurable_ofReal
    ((ProjValMeasure.mem_pmapDomain U.toPVM).mp hcutmem)
    ((ProjValMeasure.mem_pmapDomain U.toPVM).mp hidmem) hae
  have hbounded := pmapOfPVM_apply_eq_spectralCalculus_of_bounded U
    (boundedIdentitySymbol A) (measurable_boundedIdentitySymbol A)
    (bounded_boundedIdentitySymbol A) x hcutmem
  have hid := pmapOfPVM_id_eq_generator U ⟨x, hxdomU⟩ hidmem
  have hgenA : U.generator ⟨x, hxdomU⟩ = A x := by
    have happly := (LinearPMap.ext_iff.mp hgen).2
    have hT : T.toLinearPMap ⟨x, hxdomT⟩ = A x := rfl
    exact (happly (x := x) (hf := hxdomU) (hg := hxdomT)).trans hT
  unfold boundedSelfAdjointBorelCalculusC
  change spectralCalculus U (boundedIdentitySymbol A)
      (measurable_boundedIdentitySymbol A) (bounded_boundedIdentitySymbol A) x = A x
  rw [← hbounded, hcongr, hid, hgenA]


/-- The real identity symbol is bounded on the real spectrum by the operator
norm. -/
theorem identity_boundedOnSpectrum [Nontrivial H]
    (A : H →L[ℂ] H) : BoundedOnSpectrum A (fun x => x) := by
  refine ⟨‖A‖, norm_nonneg A, fun x hx => ?_⟩
  exact abs_le.mpr (realSpectrum_subset_norm_Icc A hx)

/-- Spectrum-only sup control for the real-valued calculus. -/
theorem boundedSelfAdjointBorelCalculus_norm_sub_le
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfb : BoundedOnSpectrum A f) (hgb : BoundedOnSpectrum A g)
    {C : ℝ} (hC0 : 0 ≤ C)
    (h : ∀ x ∈ realSpectrum A, |f x - g x| ≤ C) :
    ‖boundedSelfAdjointBorelCalculus A hA f hf hfb -
      boundedSelfAdjointBorelCalculus A hA g hg hgb‖ ≤ C := by
  apply boundedSelfAdjointBorelCalculusC_norm_sub_le A hA
  · exact hC0
  · intro x hx
    simp only [spectrumRestrictedSymbol, Set.indicator_of_mem hx]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact h x hx

/-- The real Borel calculus of the identity is the original operator. -/
theorem boundedSelfAdjointBorelCalculus_id [Nontrivial H]
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A) :
    boundedSelfAdjointBorelCalculus A hA (fun x => x) measurable_id
      (identity_boundedOnSpectrum A) = A := by
  have hcongr : boundedSelfAdjointBorelCalculusC A hA
      (spectrumRestrictedSymbol A fun x => x)
      (measurable_spectrumRestrictedSymbol A hA _ measurable_id)
      (bounded_spectrumRestrictedSymbol A _ (identity_boundedOnSpectrum A)) =
      boundedSelfAdjointBorelCalculusC A hA (boundedIdentitySymbol A)
        (measurable_boundedIdentitySymbol A)
        (bounded_boundedIdentitySymbol A) := by
    apply boundedSelfAdjointBorelCalculusC_congr_on_spectrum A hA
    intro x hx
    rw [spectrumRestrictedSymbol, Set.indicator_of_mem hx,
      boundedIdentitySymbol_eq A hx]
  exact hcongr.trans (boundedSelfAdjointBorelCalculusC_id A hA)

end
end DavisKahanExt
end TauCeti