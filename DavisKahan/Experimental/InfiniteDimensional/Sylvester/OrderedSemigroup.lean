/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.FourierSemigroup
import ForMathlib.Analysis.InnerProductSpace.SpectralOrder.Complex
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Ordered-spectrum Sylvester reconstruction

For bounded self-adjoint complex operators whose spectra are ordered by a
positive gap, the Sylvester solution is the Laplace integral

`X = integral over t >= 0 of exp(-t A) C exp(t B)`.

The proof differentiates `exp(-t A) X exp(t B)`, integrates on a finite
interval, and lets the endpoint tend to infinity.  The spectral order gives
exponential decay.  This is the constant-one branch of the Sylvester theory;
it is logically different from the two-sided Fourier branch, whose universal
constant is `pi/2`.
-/

namespace ForMathlib
namespace DavisKahanExt

open MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open Spectra.YosidaHille.Approximation

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- The restriction to the full space has the original real spectrum. -/
theorem restrictedSpectrum_top_eq_realSpectrum
    (T : E →L[ℂ] E) : restrictedSpectrum T ⊤ = realSpectrum T := by
  ext r
  constructor
  · rintro ⟨hTop, hr⟩
    let e : (⊤ : Submodule ℂ E) ≃L[ℂ] E :=
      LinearIsometryEquiv.ofSurjective
        ((⊤ : Submodule ℂ E).subtypeL)
        (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
    have hsim : T.restrict hTop = e.symm.toContinuousLinearMap ∘L T ∘L
        e.toContinuousLinearMap := by
      ext x
      rfl
    have hspectrum := spectrum_eq_of_similarity hsim
    exact hspectrum ▸ hr
  · intro hr
    let hTop : InvariantFor T (⊤ : Submodule ℂ E) := by
      intro x hx
      trivial
    refine ⟨hTop, ?_⟩
    let e : (⊤ : Submodule ℂ E) ≃L[ℂ] E :=
      LinearIsometryEquiv.ofSurjective
        ((⊤ : Submodule ℂ E).subtypeL)
        (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
    have hsim : T.restrict hTop = e.symm.toContinuousLinearMap ∘L T ∘L
        e.toContinuousLinearMap := by
      ext x
      rfl
    have hspectrum := spectrum_eq_of_similarity hsim
    exact hspectrum.symm ▸ hr

/-- A common cut between two compact ordered spectra. -/
theorem exists_common_cut_of_orderedSeparation
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d) :
    ∃ c : ℝ,
      realSpectrum B ⊆ Set.Iic c ∧
      realSpectrum A ⊆ Set.Ici (c + d) := by
  have hBc : IsCompact (realSpectrum B) := realSpectrum_isCompact B hB
  have hBn : (realSpectrum B).Nonempty := realSpectrum_nonempty B
  let c := sSup (realSpectrum B)
  have hcB : realSpectrum B ⊆ Set.Iic c := by
    intro b hb
    exact le_csSup hBc.isBoundedAbove hb
  have hcA : realSpectrum A ⊆ Set.Ici (c + d) := by
    intro a ha
    have hforall : ∀ b ∈ realSpectrum B, b + d ≤ a := by
      intro b hb
      have hb' : b ∈ restrictedSpectrum B ⊤ := by
        rw [restrictedSpectrum_top_eq_realSpectrum]
        exact hb
      have ha' : a ∈ restrictedSpectrum A ⊤ := by
        rw [restrictedSpectrum_top_eq_realSpectrum]
        exact ha
      exact hsep.2.2 b hb' a ha'
    have hsup : c ≤ a - d := by
      apply csSup_le hBn
      intro b hb
      linarith [hforall b hb]
    exact by
      change c + d ≤ a
      linarith
  exact ⟨c, hcB, hcA⟩

/-- Functional-calculus formula for the bounded exponential group. -/
theorem semigroup_eq_cfc
    (T : E →L[ℂ] E) (hT : IsSelfAdjointOperator T) (t : ℝ) :
    semigroup T t = cfc (fun z : ℂ => Complex.exp (t * z)) T := by
  rw [semigroup, expBounded_eq_exp]
  exact NormedSpace.exp_eq_cfc_exp T

/-- Upper spectral bound for a self-adjoint exponential. -/
theorem norm_semigroup_le_of_spectrum_subset_Iic
    (T : E →L[ℂ] E) (hT : IsSelfAdjointOperator T)
    {c t : ℝ} (ht : 0 ≤ t)
    (hσ : realSpectrum T ⊆ Set.Iic c) :
    ‖semigroup T t‖ ≤ Real.exp (t * c) := by
  rw [semigroup_eq_cfc T hT t]
  have hnormal : IsStarNormal T :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT).isStarNormal
  calc
    ‖cfc (fun z : ℂ => Complex.exp (t * z)) T‖
        ≤ sSup ((fun z : ℂ => ‖Complex.exp (t * z)‖) '' spectrum ℂ T) :=
          cfc_norm_le_sup hnormal _
    _ ≤ Real.exp (t * c) := by
      apply csSup_le
      · exact ⟨0, by intro y hy; rcases hy with ⟨z, hz, rfl⟩; positivity⟩
      · intro y hy
        rcases hy with ⟨z, hz, rfl⟩
        obtain ⟨r, hr, rfl⟩ :=
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT).spectrumRestricts hz
        rw [Complex.norm_exp, mul_re]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hσ hr) ht)

/-- Lower spectral bound, written as decay of `exp(-t T)`. -/
theorem norm_semigroup_neg_le_of_spectrum_subset_Ici
    (T : E →L[ℂ] E) (hT : IsSelfAdjointOperator T)
    {c t : ℝ} (ht : 0 ≤ t)
    (hσ : realSpectrum T ⊆ Set.Ici c) :
    ‖semigroup (-T) t‖ ≤ Real.exp (-t * c) := by
  apply norm_semigroup_le_of_spectrum_subset_Iic (-T) hT.neg ht
  intro x hx
  have hx' : -x ∈ realSpectrum T := by
    simpa [realSpectrum, spectrum.neg] using hx
  have := hσ hx'
  change x ≤ -c
  linarith

/-- The ordered semigroup integrand has the sharp exponential majorant. -/
theorem orderedSemigroup_integrand_bound
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (C : E →L[ℂ] F) :
    ∀ t ≥ 0,
      ‖semigroup (-A) t ∘L C ∘L semigroup B t‖ ≤
        Real.exp (-d * t) * ‖C‖ := by
  obtain ⟨c, hBc, hAc⟩ :=
    exists_common_cut_of_orderedSeparation hA hB hd hsep
  intro t ht
  have hleft := norm_semigroup_neg_le_of_spectrum_subset_Ici A hA ht hAc
  have hright := norm_semigroup_le_of_spectrum_subset_Iic B hB ht hBc
  calc
    ‖semigroup (-A) t ∘L C ∘L semigroup B t‖
        ≤ ‖semigroup (-A) t‖ * ‖C‖ * ‖semigroup B t‖ :=
          ContinuousLinearMap.opNorm_comp_comp_le _ _ _
    _ ≤ Real.exp (-t * (c + d)) * ‖C‖ * Real.exp (t * c) := by
      gcongr
    _ = Real.exp (-d * t) * ‖C‖ := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Bochner integrability of the ordered semigroup formula. -/
theorem orderedSylvester_integrable
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (C : E →L[ℂ] F) :
    Integrable fun t : ℝ => Set.indicator (Set.Ici 0)
      (fun t => semigroup (-A) t ∘L C ∘L semigroup B t) t := by
  have hmeas : StronglyMeasurable fun t : ℝ =>
      semigroup (-A) t ∘L C ∘L semigroup B t := by
    exact ((continuous_expBounded (-A)).comp continuous_id).stronglyMeasurable.comp₂
      continuous_const ((continuous_expBounded B).comp continuous_id).stronglyMeasurable
  refine Integrable.mono' (integrableOn_exp_neg_mul_Ici hd |>.const_mul ‖C‖) ?_ ?_
  · exact hmeas.indicator measurableSet_Ici
  · filter_upwards [] with t
    by_cases ht : 0 ≤ t
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      exact orderedSemigroup_integrand_bound hA hB hd hsep C t ht
    · rw [Set.indicator_of_not_mem (by simpa using ht),
          Set.indicator_of_not_mem (by simpa using ht), norm_zero]

/-- Derivative of the conjugated solution orbit. -/
theorem hasDerivAt_ordered_solution_orbit
    (A : F →L[ℂ] F) (B : E →L[ℂ] E) (X C : E →L[ℂ] F)
    (hEq : A ∘L X - X ∘L B = C) (t : ℝ) :
    HasDerivAt
      (fun s => semigroup (-A) s ∘L X ∘L semigroup B s)
      (-(semigroup (-A) t ∘L C ∘L semigroup B t)) t := by
  have hleft := hasDerivAt_semigroup (-A) t
  have hright := hasDerivAt_semigroup B t
  convert (hleft.clm_comp_const X).clm_comp hright using 1
  · ext x
    simp only [ContinuousLinearMap.comp_apply, neg_apply]
    rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc]
    have hcommA : A ∘L semigroup (-A) t = semigroup (-A) t ∘L A :=
      expBounded_commutes (-A) A t (by module)
    have hcommB : B ∘L semigroup B t = semigroup B t ∘L B :=
      expBounded_commutes B B t (by rfl)
    rw [hcommA, hcommB, ← hEq]
    module

/-- Finite-interval fundamental theorem for the ordered orbit. -/
theorem ordered_orbit_sub_eq_integral
    (A : F →L[ℂ] F) (B : E →L[ℂ] E) (X C : E →L[ℂ] F)
    (hEq : A ∘L X - X ∘L B = C) {T : ℝ} (hT : 0 ≤ T) :
    X - semigroup (-A) T ∘L X ∘L semigroup B T =
      ∫ t in Set.Icc (0 : ℝ) T,
        semigroup (-A) t ∘L C ∘L semigroup B t := by
  have hderiv := fun t => hasDerivAt_ordered_solution_orbit A B X C hEq t
  have hFTC := intervalIntegral.integral_deriv_eq_sub
    (fun t _ => (hderiv t).hasDerivWithinAt)
    (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
  simpa [intervalIntegral.integral_of_le hT] using congrArg Neg.neg hFTC

/-- The conjugated endpoint tends to zero under an ordered gap. -/
theorem tendsto_ordered_solution_orbit_zero
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (X : E →L[ℂ] F) :
    Tendsto (fun t : ℝ => semigroup (-A) t ∘L X ∘L semigroup B t)
      atTop (nhds 0) := by
  refine squeeze_zero' ?_ (fun t => norm_nonneg _) ?_
  · exact tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact orderedSemigroup_integrand_bound hA hB hd hsep X t ht
  · simpa using
      (Real.tendsto_exp_atTop_nhds_zero_of_neg (neg_lt_zero.mpr hd)).const_mul ‖X‖

/-- Exact ordered-spectrum reconstruction. -/
theorem orderedSylvester_reconstruction
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    {X C : E →L[ℂ] F}
    (hEq : A ∘L X - X ∘L B = C) :
    X = ∫ t : ℝ, Set.indicator (Set.Ici 0)
      (fun t => semigroup (-A) t ∘L C ∘L semigroup B t) t := by
  have hint := orderedSylvester_integrable hA hB hd hsep C
  have hfinite := fun T (hT : 0 ≤ T) =>
    ordered_orbit_sub_eq_integral A B X C hEq hT
  have horbit := tendsto_ordered_solution_orbit_zero hA hB hd hsep X
  have htrunc : Tendsto
      (fun T : ℝ => ∫ t in Set.Icc (0 : ℝ) T,
        semigroup (-A) t ∘L C ∘L semigroup B t)
      atTop
      (nhds (∫ t : ℝ, Set.indicator (Set.Ici 0)
        (fun t => semigroup (-A) t ∘L C ∘L semigroup B t) t)) := by
    exact hint.tendsto_setIntegral_Icc_atTop
  have hleft : Tendsto
      (fun T : ℝ => X - semigroup (-A) T ∘L X ∘L semigroup B T)
      atTop (nhds X) := by
    simpa using tendsto_const_nhds.sub horbit
  filter_upwards [eventually_ge_atTop (0 : ℝ)] at hfinite
  exact tendsto_nhds_unique (hleft.congr' hfinite) htrunc

end DavisKahanExt
end ForMathlib
