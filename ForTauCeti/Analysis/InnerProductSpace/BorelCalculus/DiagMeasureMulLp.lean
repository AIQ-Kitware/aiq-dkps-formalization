/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.DiagonalMeasure
public import ForTauCeti.MeasureTheory.MulLpCfc
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The scalar spectral measure of a multiplication operator

For a multiplication operator `mulLp ρ g` on `L²(ρ)` and a vector `F`, the scalar spectral
measure of `F` is the pushforward along the symbol of `|F|² · ρ`:

```text
(diagMeasure F) ∘ (spectrum ↪ ℂ)  =  g_* (|F|² · ρ).
```

## Why this is the shape to prove

Everything the uniqueness argument needs about the model is a statement about *null sets*, and
this identity converts them all into statements about `ρ`.  A vector's spectral measure is
automatically absolutely continuous with respect to the pushforward of `ρ`, and when `F` is
almost everywhere nonzero the two have exactly the same null sets -- which is what makes a
maximal vector detect the measure class of the model rather than some proper piece of it.

## The proof

Both sides are finite measures on `ℂ`, so it is enough to integrate bounded continuous test
functions (`MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure`).  On the left the
diagonal measure is characterised by `∫ f d(diagMeasure F) = re ⟪F, f(a) F⟫`, and `cfc_mulLp`
evaluates `f(a)` as multiplication by `f ∘ g`; on the right `withDensity` and `Measure.map` unfold
directly.  Both land on `∫ f (g x) * ‖F x‖² ∂ρ`.

Note that the test functions only ever meet the *continuous* functional calculus.  No Borel
calculus is needed here, even though the conclusion is a statement about arbitrary measurable
sets: the measures do that work.

## Main results

* `TauCeti.BorelCalculus.lintegral_enorm_sq_lt_top`: an `L²` vector has finite squared mass.
* `TauCeti.BorelCalculus.map_val_diagMeasure_mulLp`: **the scalar spectral measure of a
  multiplication operator.**

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

open MeasureTheory

open scoped InnerProductSpace ENNReal

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace BorelCalculus

variable {α : Type*} [MeasurableSpace α]

section Density

variable (ρ : Measure α)

/-- The squared pointwise modulus of an `L²` vector is almost everywhere measurable. -/
theorem aemeasurable_enorm_sq (F : Lp ℂ 2 ρ) :
    AEMeasurable (fun x => ‖(F : α → ℂ) x‖ₑ ^ 2) ρ :=
  ((Lp.aestronglyMeasurable F).aemeasurable.enorm).pow_const 2

/-- **An `L²` vector has finite squared mass.**  This is what makes `|F|² · ρ` a finite measure,
and hence what lets the identification of the spectral measure be tested on bounded continuous
functions. -/
theorem lintegral_enorm_sq_lt_top (F : Lp ℂ 2 ρ) :
    ∫⁻ x, ‖(F : α → ℂ) x‖ₑ ^ 2 ∂ρ < ∞ := by
  have h : eLpNorm (F : α → ℂ) 2 ρ < ∞ := (Lp.eLpNorm_ne_top F).lt_top
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)] at h
  simpa [ENNReal.rpow_natCast] using h

/-- The squared-modulus density makes a finite measure. -/
theorem isFiniteMeasure_withDensity_enorm_sq (F : Lp ℂ 2 ρ) :
    IsFiniteMeasure (ρ.withDensity fun x => ‖(F : α → ℂ) x‖ₑ ^ 2) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact lintegral_enorm_sq_lt_top ρ F

end Density

section MulLp

variable (ρ : Measure α) [SigmaFinite ρ] {g : α → ℂ} (hg : Measurable g) {C : ℝ}
variable (hgC : ∀ x, ‖g x‖ ≤ C)

include hg hgC in
/-- **The scalar spectral measure of a multiplication operator.**

The measure `diagMeasure F` of the vector `F` for the operator `mulLp ρ g`, pushed forward from
the spectrum subtype to `ℂ`, is the pushforward along the symbol of `|F|² · ρ`. -/
theorem map_val_diagMeasure_mulLp (F : Lp ℂ 2 ρ) :
    Measure.map (Subtype.val : spectrum ℂ (mulLp ρ hg hgC) → ℂ)
        (diagMeasure (isStarNormal_mulLp ρ hg hgC) F)
      = Measure.map g (ρ.withDensity fun x => ‖(F : α → ℂ) x‖ₑ ^ 2) := by
  haveI ha : IsStarNormal (mulLp ρ hg hgC) := isStarNormal_mulLp ρ hg hgC
  haveI hwd : IsFiniteMeasure (ρ.withDensity fun x => ‖(F : α → ℂ) x‖ₑ ^ 2) :=
    isFiniteMeasure_withDensity_enorm_sq ρ F
  haveI hL : IsFiniteMeasure (Measure.map (Subtype.val : spectrum ℂ (mulLp ρ hg hgC) → ℂ)
      (diagMeasure ha F)) := Measure.isFiniteMeasure_map _ _
  haveI hR : IsFiniteMeasure
      (Measure.map g (ρ.withDensity fun x => ‖(F : α → ℂ) x‖ₑ ^ 2)) :=
    Measure.isFiniteMeasure_map _ _
  refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure fun φ => ?_
  have hφc : Continuous fun z : ℂ => ((φ z : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp φ.continuous
  -- The left-hand side, through the characterisation of the diagonal measure.
  have hleft : ∫ w : spectrum ℂ (mulLp ρ hg hgC), φ (w : ℂ) ∂(diagMeasure ha F)
      = (⟪F, cfc (fun z : ℂ => ((φ z : ℝ) : ℂ)) (mulLp ρ hg hgC) F⟫_ℂ).re := by
    have hG := integral_diagMeasure_ofReal ha F
      (⟨fun w : spectrum ℂ (mulLp ρ hg hgC) => φ (w : ℂ),
        φ.continuous.comp continuous_subtype_val⟩ :
        C(spectrum ℂ (mulLp ρ hg hgC), ℝ))
    simp only [ContinuousMap.coe_mk] at hG
    rw [hG, cfc_apply (f := fun z : ℂ => ((φ z : ℝ) : ℂ)) (a := mulLp ρ hg hgC) ha
      hφc.continuousOn]
    exact congrArg (fun T : Lp ℂ 2 ρ →L[ℂ] Lp ℂ 2 ρ => (⟪F, T F⟫_ℂ).re)
      (congrArg (cfcHom ha) (ContinuousMap.ext fun _ => by simp))
  -- The functional calculus of a multiplication operator.
  have hcm : Measurable fun x => ((φ (g x) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp (φ.continuous.measurable.comp hg)
  have hcb : ∀ x, ‖((φ (g x) : ℝ) : ℂ)‖ ≤ ‖φ‖ := by
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact φ.norm_coe_le_norm (g x)
  have hcfc : cfc (fun z : ℂ => ((φ z : ℝ) : ℂ)) (mulLp ρ hg hgC) = mulLp ρ hcm hcb :=
    cfc_mulLp ρ hg hgC hφc.continuousOn hcm hcb (Filter.Eventually.of_forall fun _ => rfl)
  -- The inner product against a multiplication operator is a weighted integral.
  have hinner : (⟪F, mulLp ρ hcm hcb F⟫_ℂ).re
      = ∫ x, φ (g x) * ‖(F : α → ℂ) x‖ ^ 2 ∂ρ := by
    rw [MeasureTheory.L2.inner_def]
    have hcongr : ∫ x, ⟪(F : α → ℂ) x, ((mulLp ρ hcm hcb F : Lp ℂ 2 ρ) : α → ℂ) x⟫_ℂ ∂ρ
        = ∫ x, ((φ (g x) * ‖(F : α → ℂ) x‖ ^ 2 : ℝ) : ℂ) ∂ρ := by
      refine integral_congr_ae ?_
      filter_upwards [coeFn_mulLp ρ hcm hcb F] with x hx
      rw [hx, RCLike.inner_apply]
      have hz : (starRingEnd ℂ) ((F : α → ℂ) x) * ((F : α → ℂ) x)
          = ((‖(F : α → ℂ) x‖ : ℂ)) ^ 2 := RCLike.conj_mul _
      push_cast
      linear_combination ((φ (g x) : ℂ)) * hz
    rw [hcongr, integral_complex_ofReal, Complex.ofReal_re]
  -- Assemble.
  rw [integral_map measurable_subtype_coe.aemeasurable φ.continuous.aestronglyMeasurable,
    hleft, hcfc, hinner,
    integral_map hg.aemeasurable φ.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ (aemeasurable_enorm_sq ρ F)
      (Filter.Eventually.of_forall fun _ => by finiteness)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 1

end MulLp

end BorelCalculus
end TauCeti
