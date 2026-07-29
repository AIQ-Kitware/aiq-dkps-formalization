/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Mathlib.MeasureTheory.Measure.Support
import Spectra.Mathlib.CharFunBridge
import Spectra.Spaces.Tensor.HilbertSchmidtFlow
import Spectra.SpectralTheory.Algebra
import Spectra.SpectralTheory.Calculus.SpectralGapInverse

/-!
# Spectral support of the rectangular Hilbert--Schmidt Sylvester flow

For a pure Hilbert tensor `u tensor conjugate(v)`, the scalar spectral measure
of the left-minus-right flow is the pushforward of the product of the two
scalar spectral measures under `(lambda, alpha) |-> lambda - alpha`.

Consequently, pairwise separation of the scalar supports gives a spectral gap
for every pure tensor.  Pure tensors span densely and the gap spectral
projection is bounded, so the projection vanishes on the whole Hilbert tensor
space.  Thus every rectangular Hilbert--Schmidt tensor has the same vector
spectral gap.
-/

open MeasureTheory Complex Spectra
open scoped InnerProductSpace
-- The pure-tensor notation is scoped to `Spectra.HilbertTensor`, and the
-- spectral measure lives in `Spectra.Borel`; neither is reached by the above.
open scoped Spectra.HilbertTensor
open Spectra.Borel
open Spectra.Borel.SpectralMeasure

namespace Spectra.HilbertSchmidtTensor

noncomputable section

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The spectral-coordinate difference map for the Sylvester flow. -/
def spectralDifference (p : ℝ × ℝ) : ℝ := p.1 - p.2

@[fun_prop]
theorem continuous_spectralDifference : Continuous spectralDifference := by
  -- `fun_prop` does not unfold the definition on its own.
  unfold spectralDifference
  fun_prop

@[fun_prop]
theorem measurable_spectralDifference : Measurable spectralDifference :=
  continuous_spectralDifference.measurable

private theorem conj_orbit_inner
    (V : OneParameterUnitaryGroup (H := F)) (t : ℝ) (v : F) :
    ⟪Conj.toConj v, Conj.map (V.U t) (Conj.toConj v)⟫_ℂ =
      ⟪v, V.U (-t) v⟫_ℂ := by
  change ⟪V.U t v, v⟫_ℂ = ⟪v, V.U (-t) v⟫_ℂ
  rw [V.inverse_eq_adjoint]
  exact (ContinuousLinearMap.adjoint_inner_right (V.U t) v v).symm

private theorem char_difference_factor (t lam α : ℝ) :
    cexp (I * ((spectralDifference (lam, α) : ℝ) : ℂ) * (t : ℂ)) =
      cexp (I * (lam : ℂ) * (t : ℂ)) *
        cexp (I * (α : ℂ) * ((-t : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  simp only [spectralDifference]
  push_cast
  ring

/-- The pure-tensor scalar spectral measure is the difference-pushforward of
the product scalar measure. -/
theorem borelMeasure_sylvesterGroup_tmul
    (U : OneParameterUnitaryGroup (H := E))
    (V : OneParameterUnitaryGroup (H := F))
    (u : E) (v : F) :
    borelMeasure (sylvesterGroup U V) (u ⊗̂ₜ[ℂ] Conj.toConj v) =
      Measure.map spectralDifference
        ((borelMeasure U u).prod (borelMeasure V v)) := by
  let μ := borelMeasure U u
  let ν := borelMeasure V v
  haveI : IsFiniteMeasure μ := borelMeasure_isFiniteMeasure U u
  haveI : IsFiniteMeasure ν := borelMeasure_isFiniteMeasure V v
  haveI : IsFiniteMeasure (μ.prod ν) := inferInstance
  haveI : IsFiniteMeasure (Measure.map spectralDifference (μ.prod ν)) := inferInstance
  apply Spectra.Fourier.measure_ext_of_fourier
  intro t
  rw [← borelMeasure_fourier (sylvesterGroup U V)
    (u ⊗̂ₜ[ℂ] Conj.toConj v) t]
  -- State the integrand as a lambda in the target variable: built from `comp`
  -- and pointwise products it does not match the shape `integral_map` expects,
  -- and it was written in the source variable rather than the mapped one.
  have hcont : Continuous fun ω : ℝ =>
      Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ)) := by fun_prop
  rw [integral_map measurable_spectralDifference.aemeasurable
    hcont.aestronglyMeasurable]
  change
    ⟪u ⊗̂ₜ[ℂ] Conj.toConj v,
      (sylvesterGroup U V).U t (u ⊗̂ₜ[ℂ] Conj.toConj v)⟫_ℂ =
      ∫ p, cexp (I * ((spectralDifference p : ℝ) : ℂ) * (t : ℂ)) ∂(μ.prod ν)
  rw [sylvesterGroup_apply, HilbertTensor.mapL_tmul,
    HilbertTensor.inner_tmul_tmul]
  rw [show (fun p : ℝ × ℝ =>
      cexp (I * ((spectralDifference p : ℝ) : ℂ) * (t : ℂ))) =
      fun p => cexp (I * (p.1 : ℂ) * (t : ℂ)) *
        cexp (I * (p.2 : ℂ) * ((-t : ℝ) : ℂ)) by
      funext p
      exact char_difference_factor t p.1 p.2]
  -- The factorisation is higher order, so the two factors are given explicitly.
  rw [integral_prod_mul (μ := μ) (ν := ν)
    (f := fun x : ℝ => cexp (I * (x : ℂ) * (t : ℂ)))
    (g := fun y : ℝ => cexp (I * (y : ℂ) * ((-t : ℝ) : ℂ)))]
  rw [← borelMeasure_fourier U u t, ← borelMeasure_fourier V v (-t)]
  exact congrArg₂ (· * ·) rfl (conj_orbit_inner V t v)

/-- Pairwise separation of the scalar spectral supports of two groups. -/
def PairwiseScalarSupportGap
    (U : OneParameterUnitaryGroup (H := E))
    (V : OneParameterUnitaryGroup (H := F))
    (δ : ℝ) : Prop :=
  ∀ u : E, ∀ v : F,
    ∀ lam ∈ (borelMeasure U u).support,
    ∀ α ∈ (borelMeasure V v).support,
      δ ≤ |lam - α|

/-- Pairwise support separation gives the vector gap for every pure tensor. -/
theorem hasVectorSpectralGap_tmul
    (U : OneParameterUnitaryGroup (H := E))
    (V : OneParameterUnitaryGroup (H := F))
    {δ : ℝ} (hgap : PairwiseScalarSupportGap U V δ)
    (u : E) (v : F) :
    Spectra.QuantumMechanics.SpectralTheory.HasVectorSpectralGap
      (sylvesterGroup U V) (u ⊗̂ₜ[ℂ] Conj.toConj v) δ := by
  let μ := borelMeasure U u
  let ν := borelMeasure V v
  haveI : IsFiniteMeasure μ := borelMeasure_isFiniteMeasure U u
  haveI : IsFiniteMeasure ν := borelMeasure_isFiniteMeasure V v
  unfold Spectra.QuantumMechanics.SpectralTheory.HasVectorSpectralGap
  rw [borelMeasure_sylvesterGroup_tmul]
  have hprod : ∀ᵐ p ∂μ.prod ν, δ ≤ |spectralDifference p| := by
    have hmeas : MeasurableSet {p : ℝ × ℝ | δ ≤ |spectralDifference p|} :=
      measurableSet_le measurable_const
        (measurable_spectralDifference.abs)
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae hmeas]
    filter_upwards [μ.support_mem_ae] with lam hlam
    filter_upwards [ν.support_mem_ae] with α hα
    exact hgap u v lam hlam α hα
  exact (ae_map_iff measurable_spectralDifference.aemeasurable
    (measurableSet_le measurable_const measurable_abs)).2 hprod

private theorem gap_projection_tmul_eq_zero
    (U : OneParameterUnitaryGroup (H := E))
    (V : OneParameterUnitaryGroup (H := F))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hgap : PairwiseScalarSupportGap U V δ)
    (u : E) (v : F) :
    Spectra.QuantumMechanics.SpectralTheory.spectralProjection
      (sylvesterGroup U V) (Set.Ioo (-δ) δ) measurableSet_Ioo
      (u ⊗̂ₜ[ℂ] Conj.toConj v) = 0 := by
  rw [Spectra.QuantumMechanics.SpectralTheory.spectralProjection_eq_zero_iff_measure_zero]
  have hae := hasVectorSpectralGap_tmul U V hgap u v
  refine measure_mono_null ?_ (ae_iff.mp hae)
  intro s hs
  change s ∈ {s : ℝ | δ ≤ |s|}ᶜ
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  exact abs_lt.2 hs

/-- Pairwise scalar support separation opens a global gap in the
left-minus-right Hilbert--Schmidt tensor flow. -/
theorem spectralProjection_gap_eq_zero
    (U : OneParameterUnitaryGroup (H := E))
    (V : OneParameterUnitaryGroup (H := F))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hgap : PairwiseScalarSupportGap U V δ) :
    Spectra.QuantumMechanics.SpectralTheory.spectralProjection
      (sylvesterGroup U V) (Set.Ioo (-δ) δ) measurableSet_Ioo = 0 := by
  refine ContinuousLinearMap.ext fun z₀ => ?_
  refine HilbertTensor.dense_span_tmul.induction
    (P := fun t => Spectra.QuantumMechanics.SpectralTheory.spectralProjection
      (sylvesterGroup U V) (Set.Ioo (-δ) δ) measurableSet_Ioo t = 0) ?_ ?_ z₀
  · intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        rcases hz with ⟨⟨u, cv⟩, rfl⟩
        simpa using gap_projection_tmul_eq_zero U V hδ hgap
          u (Conj.ofConj cv)
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  · exact isClosed_eq
      ((Spectra.QuantumMechanics.SpectralTheory.spectralProjection
        (sylvesterGroup U V) (Set.Ioo (-δ) δ) measurableSet_Ioo).continuous)
      continuous_const

/-- Pairwise scalar support separation gives a vector spectral gap for every
Hilbert--Schmidt tensor. -/
theorem hasVectorSpectralGap
    (U : OneParameterUnitaryGroup (H := E))
    (V : OneParameterUnitaryGroup (H := F))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hgap : PairwiseScalarSupportGap U V δ)
    (z : Space E F) :
    Spectra.QuantumMechanics.SpectralTheory.HasVectorSpectralGap
      (sylvesterGroup U V) z δ := by
  have hproj := congrArg
    (fun P : Space E F →L[ℂ] Space E F => P z)
    (spectralProjection_gap_eq_zero U V hδ hgap)
  have hnull : borelMeasure (sylvesterGroup U V) z
      (Set.Ioo (-δ) δ) = 0 := by
    rw [← Spectra.QuantumMechanics.SpectralTheory.spectralProjection_eq_zero_iff_measure_zero]
    simpa using hproj
  refine ae_iff.mpr ?_
  refine measure_mono_null ?_ hnull
  intro s hs
  change s ∈ Set.Ioo (-δ) δ
  have hlt : |s| < δ := by simpa only [Set.mem_compl_iff,
    Set.mem_setOf_eq, not_le] using hs
  exact abs_lt.mp hlt

end
end Spectra.HilbertSchmidtTensor
