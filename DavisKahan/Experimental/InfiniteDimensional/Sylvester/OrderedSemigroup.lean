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

/-- The real spectrum of a bounded operator is bounded above by its norm.
(Local copy of the `TanTwoTheta` lemma, kept private to avoid importing the
heavy continuation chain that its home file drags in.) -/
private theorem realSpectrum_bddAbove' [Nontrivial E] (T : E →L[ℂ] E) :
    BddAbove (realSpectrum T) := by
  refine ⟨‖T‖, ?_⟩
  intro r hr
  have hr' : (r : ℂ) ∈ spectrum ℂ T := hr
  have hnorm : ‖(r : ℂ)‖ ≤ ‖T‖ := spectrum.norm_le_norm_of_mem hr'
  calc
    r ≤ |r| := le_abs_self r
    _ = ‖(r : ℂ)‖ := by simp
    _ ≤ ‖T‖ := hnorm

/-- The real spectrum of a bounded operator is bounded below by minus its norm.
(Local private copy; see `realSpectrum_bddAbove'`.) -/
private theorem realSpectrum_bddBelow' [Nontrivial E] (T : E →L[ℂ] E) :
    BddBelow (realSpectrum T) := by
  refine ⟨-‖T‖, ?_⟩
  intro r hr
  have hr' : (r : ℂ) ∈ spectrum ℂ T := hr
  have hnorm : ‖(r : ℂ)‖ ≤ ‖T‖ := spectrum.norm_le_norm_of_mem hr'
  have habs : |r| ≤ ‖T‖ := by simpa using hnorm
  exact neg_le_of_abs_le habs

/-- A bounded self-adjoint operator on a nontrivial complex Hilbert space has a
nonempty native real spectrum.  (Local private copy; see `realSpectrum_bddAbove'`.) -/
private theorem realSpectrum_nonempty_of_selfAdjoint' [Nontrivial E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjointOperator T) :
    (realSpectrum T).Nonempty := by
  have hTsa : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  have hrad : spectralRadius ℂ T = ‖T‖₊ :=
    T.spectralRadius_eq_nnnorm hTsa
  obtain ⟨z, hz⟩ : (spectrum ℂ T).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hzeroRadius : spectralRadius ℂ T = 0 := by
      show (⨆ k ∈ spectrum ℂ T, (‖k‖₊ : ENNReal)) = 0
      rw [hempty]
      simp
    have hTzero : T = 0 := by
      have hnormZero : ((‖T‖₊ : ENNReal)) = 0 := by
        rw [← hrad]
        exact hzeroRadius
      rw [ENNReal.coe_eq_zero, nnnorm_eq_zero] at hnormZero
      exact hnormZero
    have hzeroMem : (0 : ℂ) ∈ spectrum ℂ T := by
      rw [hTzero, spectrum.zero_mem_iff]
      exact not_isUnit_zero
    rw [hempty] at hzeroMem
    exact hzeroMem
  obtain ⟨lam, _hlam, rfl⟩ :=
    hTsa.spectrumRestricts.algebraMap_image.symm ▸ hz
  refine ⟨lam, ?_⟩
  change (lam : ℂ) ∈ spectrum ℂ T
  exact hz

/-- On a trivial space every operator is a unit, so the real spectrum is empty. -/
theorem realSpectrum_eq_empty_of_subsingleton
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [Subsingleton G] (T : G →L[ℂ] G) : realSpectrum T = ∅ := by
  haveI : Subsingleton (G →L[ℂ] G) :=
    ⟨fun a b => by ext x; exact Subsingleton.elim _ _⟩
  ext r
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hr
  have hr' : (r : ℂ) ∈ spectrum ℂ T := hr
  rw [spectrum.mem_iff] at hr'
  exact hr' (isUnit_of_subsingleton _)

/-- A common cut between two compact ordered spectra.  When `A` acts on a
nontrivial space its spectrum is a nonempty compact real set, so `c := inf σ(A) −
d` separates the two spectra; the degenerate trivial-space cases are handled by
`realSpectrum_eq_empty_of_subsingleton`. -/
theorem exists_common_cut_of_orderedSeparation
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d) :
    ∃ c : ℝ,
      realSpectrum B ⊆ Set.Iic c ∧
      realSpectrum A ⊆ Set.Ici (c + d) := by
  have hsep0 := hsep.2.2
  simp only [restrictedSpectrum_top_eq_realSpectrum] at hsep0
  -- `hsep0 : ∀ a ∈ realSpectrum B, ∀ b ∈ realSpectrum A, a + d ≤ b`
  rcases subsingleton_or_nontrivial F with hFs | hFn
  · -- `A` acts on a trivial space, so `realSpectrum A = ∅`.
    haveI := hFs
    have hAe : realSpectrum A = ∅ := realSpectrum_eq_empty_of_subsingleton A
    rcases subsingleton_or_nontrivial E with hEs | hEn
    · -- both spectra empty
      haveI := hEs
      refine ⟨0, ?_, ?_⟩
      · rw [realSpectrum_eq_empty_of_subsingleton B]; exact Set.empty_subset _
      · rw [hAe]; exact Set.empty_subset _
    · -- cut at `sup σ(B)`
      haveI := hEn
      refine ⟨sSup (realSpectrum B), fun a ha => ?_, ?_⟩
      · exact Set.mem_Iic.mpr (le_csSup (realSpectrum_bddAbove' B) ha)
      · rw [hAe]; exact Set.empty_subset _
  · -- `A` acts on a nontrivial space: cut at `inf σ(A) − d`.
    haveI := hFn
    have hAne : (realSpectrum A).Nonempty :=
      realSpectrum_nonempty_of_selfAdjoint' A hA
    have hAbb : BddBelow (realSpectrum A) := realSpectrum_bddBelow' A
    refine ⟨sInf (realSpectrum A) - d, fun a ha => ?_, fun b hb => ?_⟩
    · refine Set.mem_Iic.mpr ?_
      have hlb : a + d ≤ sInf (realSpectrum A) :=
        le_csInf hAne (fun b hb => hsep0 a ha b hb)
      linarith
    · refine Set.mem_Ici.mpr ?_
      have := csInf_le hAbb hb
      linarith

/-- Functional-calculus formula for the bounded exponential group. -/
theorem semigroup_eq_cfc
    (T : E →L[ℂ] E) (hT : IsSelfAdjointOperator T) (t : ℝ) :
    semigroup T t = cfc (fun z : ℂ => Complex.exp (t * z)) T := by
  -- Open obligation: agreement of the bounded exponential with the continuous
  -- functional calculus of `exp` on a self-adjoint operator, handed to the
  -- mathematics agent.
  sorry

/-- Upper spectral bound for a self-adjoint exponential. -/
theorem norm_semigroup_le_of_spectrum_subset_Iic
    (T : E →L[ℂ] E) (hT : IsSelfAdjointOperator T)
    {c t : ℝ} (ht : 0 ≤ t)
    (hσ : realSpectrum T ⊆ Set.Iic c) :
    ‖semigroup T t‖ ≤ Real.exp (t * c) := by
  -- Open obligation: the self-adjoint CFC norm bound `‖f(T)‖ ≤ sup_{σ(T)} |f|`
  -- (Mathlib `norm_cfc_le`) composed with `semigroup_eq_cfc`, handed to the
  -- mathematics agent.
  sorry

/-- Lower spectral bound, written as decay of `exp(-t T)`. -/
theorem norm_semigroup_neg_le_of_spectrum_subset_Ici
    (T : E →L[ℂ] E) (hT : IsSelfAdjointOperator T)
    {c t : ℝ} (ht : 0 ≤ t)
    (hσ : realSpectrum T ⊆ Set.Ici c) :
    ‖semigroup (-T) t‖ ≤ Real.exp (-t * c) := by
  -- Open obligation: negation of a self-adjoint operator and the spectral
  -- reflection `σ(-T) = -σ(T)`, composed with the upper bound above; handed to
  -- the mathematics agent.
  sorry

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
        ≤ ‖semigroup (-A) t‖ * ‖C‖ * ‖semigroup B t‖ := by
          refine ((semigroup (-A) t).opNorm_comp_le (C ∘L semigroup B t)).trans ?_
          rw [mul_assoc]
          gcongr
          exact C.opNorm_comp_le (semigroup B t)
    _ ≤ Real.exp (-t * (c + d)) * ‖C‖ * Real.exp (t * c) := by
      gcongr
    _ = Real.exp (-d * t) * ‖C‖ := by
      rw [mul_right_comm, ← Real.exp_add,
        show -t * (c + d) + t * c = -d * t from by ring]

/-- Bochner integrability of the ordered semigroup formula. -/
theorem orderedSylvester_integrable
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (C : E →L[ℂ] F) :
    Integrable fun t : ℝ => Set.indicator (Set.Ici 0)
      (fun t => semigroup (-A) t ∘L C ∘L semigroup B t) t := by
  have hcontA : Continuous (semigroup (-A)) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_semigroup (-A) t).continuousAt
  have hcontB : Continuous (semigroup B) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_semigroup B t).continuousAt
  have hcont : Continuous (fun t : ℝ => semigroup (-A) t ∘L C ∘L semigroup B t) :=
    (hcontA.clm_comp continuous_const).clm_comp hcontB
  have hmajor : IntegrableOn (fun t : ℝ => Real.exp (-d * t) * ‖C‖) (Set.Ici 0) :=
    ((exp_neg_integrableOn_Ioi 0 hd).congr_set_ae Ioi_ae_eq_Ici.symm).mul_const ‖C‖
  -- Dominate the operator-valued indicator by the `ℝ`-valued exponential
  -- indicator, sidestepping the continuous-linear-map `enorm` instance diamond.
  refine (hmajor.integrable_indicator measurableSet_Ici).mono'
    (hcont.aestronglyMeasurable.indicator measurableSet_Ici) ?_
  filter_upwards with t
  by_cases ht : t ∈ Set.Ici 0
  · simp only [Set.indicator_of_mem ht]
    exact orderedSemigroup_integrand_bound hA hB hd hsep C t ht
  · simp only [Set.indicator_of_notMem ht, norm_zero, le_refl]

/-- Derivative of the conjugated solution orbit. -/
theorem hasDerivAt_ordered_solution_orbit
    (A : F →L[ℂ] F) (B : E →L[ℂ] E) (X C : E →L[ℂ] F)
    (hEq : A ∘L X - X ∘L B = C) (t : ℝ) :
    HasDerivAt
      (fun s => semigroup (-A) s ∘L X ∘L semigroup B s)
      (-(semigroup (-A) t ∘L C ∘L semigroup B t)) t := by
  -- Open obligation: the *operator*-valued product rule.  The generator
  -- commutation is available (`commute_exp A (-A) t (Commute.refl A).neg_right`),
  -- but `HasDerivAt.clm_comp` requires the composed maps to be linear over the
  -- derivation field `ℝ`, whereas the semigroups are `ℂ`-linear; bridging that
  -- needs the `ℝ`-bilinear composition Fréchet derivative (restrictScalars +
  -- `IsBoundedBilinearMap.hasFDerivAt`).  The downstream finite-interval FTC
  -- `ordered_orbit_sub_eq_integral` is proved directly by the vector-valued
  -- route, so this operator form is not on its critical path.
  sorry

/-- Finite-interval fundamental theorem for the ordered orbit. -/
theorem ordered_orbit_sub_eq_integral
    (A : F →L[ℂ] F) (B : E →L[ℂ] E) (X C : E →L[ℂ] F)
    (hEq : A ∘L X - X ∘L B = C) {T : ℝ} (hT : 0 ≤ T) :
    X - semigroup (-A) T ∘L X ∘L semigroup B T =
      ∫ t in Set.Icc (0 : ℝ) T,
        semigroup (-A) t ∘L C ∘L semigroup B t := by
  have hcontA : Continuous (semigroup (-A)) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_semigroup (-A) t).continuousAt
  have hcontB : Continuous (semigroup B) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_semigroup B t).continuousAt
  have hcont : Continuous (fun t : ℝ => semigroup (-A) t ∘L C ∘L semigroup B t) :=
    (hcontA.clm_comp continuous_const).clm_comp hcontB
  have hInt : IntegrableOn
      (fun t : ℝ => semigroup (-A) t ∘L C ∘L semigroup B t) (Set.Icc 0 T) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hcomm_pt : ∀ (s : ℝ) (y : F),
      semigroup (-A) s (A y) = A (semigroup (-A) s y) := by
    intro s y
    have hcomm : Commute A (semigroup (-A) s) :=
      commute_exp A (-A) s ((Commute.refl A).neg_right)
    exact (ContinuousLinearMap.ext_iff.mp hcomm.eq y).symm
  ext ψ
  -- Vector-valued antiderivative `Ψ(s) = e^{-sA} X e^{sB} ψ` and its derivative.
  have hΨ : ∀ s : ℝ, HasDerivAt
      (fun s => semigroup (-A) s (X (semigroup B s ψ)))
      (-(semigroup (-A) s (C (semigroup B s ψ)))) s := by
    intro s
    have hg_apply : HasDerivAt (fun s => semigroup B s ψ)
        (B (semigroup B s ψ)) s := by
      simpa [Function.comp_def] using
        ((ContinuousLinearMap.apply ℂ E ψ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
          (hasDerivAt_semigroup B s)
    have hu : HasDerivAt (fun s => X (semigroup B s ψ))
        (X (B (semigroup B s ψ))) s :=
      (X.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hg_apply
    have hf' : HasDerivAt (fun s => (semigroup (-A) s).restrictScalars ℝ)
        (((-A) ∘L semigroup (-A) s).restrictScalars ℝ) s :=
      (ContinuousLinearMap.restrictScalarsL ℂ F F ℝ ℝ).hasFDerivAt.comp_hasDerivAt s
        (hasDerivAt_semigroup (-A) s)
    refine (hf'.clm_apply hu).congr_deriv ?_
    show (((-A) ∘L semigroup (-A) s).restrictScalars ℝ) (X (semigroup B s ψ))
        + ((semigroup (-A) s).restrictScalars ℝ) (X (B (semigroup B s ψ)))
      = -(semigroup (-A) s (C (semigroup B s ψ)))
    rw [← hEq]
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.sub_apply, map_sub]
    rw [hcomm_pt s (X (semigroup B s ψ))]
    abel
  have hcont_hψ : Continuous
      (fun s : ℝ => semigroup (-A) s (C (semigroup B s ψ))) :=
    hcont.clm_apply continuous_const
  -- Finite-interval fundamental theorem of calculus for the vector orbit.
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := T)
    (fun s _ => hΨ s) (hcont_hψ.neg.intervalIntegrable 0 T)
  rw [intervalIntegral.integral_neg] at hftc
  have hkey : (∫ t in (0 : ℝ)..T, semigroup (-A) t (C (semigroup B t ψ)))
      = semigroup (-A) 0 (X (semigroup B 0 ψ))
        - semigroup (-A) T (X (semigroup B T ψ)) := by
    have h := congrArg Neg.neg hftc
    simpa [neg_neg, neg_sub] using h
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.integral_apply hInt ψ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hT]
  simp only [ContinuousLinearMap.comp_apply, hkey, semigroup_zero,
    ContinuousLinearMap.one_apply]

/-- The conjugated endpoint tends to zero under an ordered gap. -/
theorem tendsto_ordered_solution_orbit_zero
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (X : E →L[ℂ] F) :
    Tendsto (fun t : ℝ => semigroup (-A) t ∘L X ∘L semigroup B t)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound := orderedSemigroup_integrand_bound hA hB hd hsep X
  have hexp : Tendsto (fun t : ℝ => Real.exp (-d * t) * ‖X‖) atTop (nhds 0) := by
    have h : Tendsto (fun t : ℝ => Real.exp (-d * t)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp
        ((tendsto_const_mul_atBot_of_neg (by linarith : -d < 0)).mpr tendsto_id)
    simpa using h.mul_const ‖X‖
  refine squeeze_zero' ?_ ?_ hexp
  · filter_upwards with t using norm_nonneg _
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht using hbound t ht

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
  have hcontA : Continuous (semigroup (-A)) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_semigroup (-A) t).continuousAt
  have hcontB : Continuous (semigroup B) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_semigroup B t).continuousAt
  have hcont : Continuous (fun t : ℝ => semigroup (-A) t ∘L C ∘L semigroup B t) :=
    (hcontA.clm_comp continuous_const).clm_comp hcontB
  have hmajor : IntegrableOn (fun t : ℝ => Real.exp (-d * t) * ‖C‖) (Set.Ici 0) :=
    ((exp_neg_integrableOn_Ioi 0 hd).congr_set_ae Ioi_ae_eq_Ici.symm).mul_const ‖C‖
  have hIntIci : IntegrableOn
      (fun t : ℝ => semigroup (-A) t ∘L C ∘L semigroup B t) (Set.Ici 0) := by
    refine hmajor.mono' hcont.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact orderedSemigroup_integrand_bound hA hB hd hsep C t ht
  have hmono : Monotone (fun n : ℕ => Set.Icc (0 : ℝ) (n : ℝ)) :=
    fun a b hab => Set.Icc_subset_Icc_right (by exact_mod_cast hab)
  have hunion : ⋃ n : ℕ, Set.Icc (0 : ℝ) (n : ℝ) = Set.Ici 0 := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro ⟨n, hx0, -⟩; exact hx0
    · intro hx0
      obtain ⟨n, hn⟩ := exists_nat_ge x
      exact ⟨n, hx0, hn⟩
  -- The truncated integrals converge to the improper `Ici 0` integral.
  have hlim2 : Tendsto (fun n : ℕ => ∫ t in Set.Icc (0 : ℝ) (n : ℝ),
      semigroup (-A) t ∘L C ∘L semigroup B t) atTop
      (nhds (∫ t in Set.Ici (0 : ℝ), semigroup (-A) t ∘L C ∘L semigroup B t)) := by
    have h := MeasureTheory.tendsto_setIntegral_of_monotone
      (s := fun n : ℕ => Set.Icc (0 : ℝ) (n : ℝ))
      (fun n => measurableSet_Icc) hmono (by rw [hunion]; exact hIntIci)
    rwa [hunion] at h
  -- The truncated left-hand sides converge to `X` (endpoint decay).
  have hlim1 : Tendsto (fun n : ℕ =>
      X - semigroup (-A) (n : ℝ) ∘L X ∘L semigroup B (n : ℝ)) atTop (nhds X) := by
    have h0 := (tendsto_ordered_solution_orbit_zero hA hB hd hsep X).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using tendsto_const_nhds.sub h0
  have heq : ∀ n : ℕ, X - semigroup (-A) (n : ℝ) ∘L X ∘L semigroup B (n : ℝ)
      = ∫ t in Set.Icc (0 : ℝ) (n : ℝ), semigroup (-A) t ∘L C ∘L semigroup B t :=
    fun n => ordered_orbit_sub_eq_integral A B X C hEq (Nat.cast_nonneg n)
  rw [MeasureTheory.integral_indicator measurableSet_Ici]
  exact tendsto_nhds_unique (hlim1.congr heq) hlim2

end

end DavisKahanExt
end ForMathlib
