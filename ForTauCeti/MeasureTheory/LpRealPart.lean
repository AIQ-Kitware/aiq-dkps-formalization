/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Star

/-!
# Real and conjugate representatives of `Lᵖ` classes

These representative identities hold for every exponent. For `1 ≤ p`, TauCeti
packages the real-part equivalence as `MeasureTheory.Lp.selfAdjointLinearIsometryEquiv`.
-/

public section

open MeasureTheory

open scoped ENNReal ComplexConjugate

namespace TauCeti

variable {K : Type*} [RCLike K] {p : ℝ≥0∞} {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **A `star`-fixed `Lᵖ` class is almost everywhere real**, in the form that recovers the
class from its real part.  This is the direction that does the work: it is what lets a real
representative be chosen. -/
theorem ae_ofReal_re_eq_of_star_eq_self {F : Lp K p μ} (hF : star F = F) :
    ∀ᵐ x ∂μ, ((RCLike.re ((F : α → K) x) : ℝ) : K) = (F : α → K) x := by
  have h := Lp.coeFn_star F
  rw [hF] at h
  filter_upwards [h] with x hx
  have hconj : conj ((F : α → K) x) = (F : α → K) x := by
    simpa [Pi.star_apply, RCLike.star_def] using hx.symm
  exact RCLike.conj_eq_iff_re.mp hconj

/-- **C1: `star F = F` exactly when `F` has an almost everywhere real representative.** -/
theorem star_eq_self_iff_ae_ofReal_re_eq {F : Lp K p μ} :
    star F = F ↔ ∀ᵐ x ∂μ, ((RCLike.re ((F : α → K) x) : ℝ) : K) = (F : α → K) x := by
  refine ⟨ae_ofReal_re_eq_of_star_eq_self, fun h => ?_⟩
  refine Lp.star_eq_self_of_ae_eq_ofReal (u := fun x => RCLike.re (F x)) ?_
  filter_upwards [h] with x hx using hx.symm

/-- The `im = 0` phrasing of `star_eq_self_iff_ae_ofReal_re_eq`.  Kept separate because the
two phrasings are convenient at different call sites: this one is the cheap test, the other
carries the real representative. -/
theorem star_eq_self_iff_ae_im_eq_zero {F : Lp K p μ} :
    star F = F ↔ ∀ᵐ x ∂μ, RCLike.im ((F : α → K) x) = 0 := by
  rw [star_eq_self_iff_ae_ofReal_re_eq]
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact RCLike.conj_eq_iff_im.mp (RCLike.conj_eq_iff_re.mpr hx)
  · intro h
    filter_upwards [h] with x hx
    exact RCLike.conj_eq_iff_re.mp (RCLike.conj_eq_iff_im.mpr hx)

/-- Pointwise star is postcomposition by the real-linear conjugation map. -/
theorem star_eq_compLp (F : Lp K p μ) :
    star F = ((RCLike.conjCLE (K := K)).toContinuousLinearMap).compLp F := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star F,
    ((RCLike.conjCLE (K := K)).toContinuousLinearMap).coeFn_compLp F] with x h1 h2
  rw [h1, h2]
  simp [Pi.star_apply, RCLike.star_def]

/-- Taking the real part of a pointwise real inclusion recovers the original class. -/
theorem reCLM_compLp_ofRealCLM_compLp (f : Lp ℝ p μ) :
    (RCLike.reCLM (K := K)).compLp ((RCLike.ofRealCLM (K := K)).compLp f) = f := by
  refine Lp.ext ?_
  filter_upwards [(RCLike.reCLM (K := K)).coeFn_compLp
    ((RCLike.ofRealCLM (K := K)).compLp f), (RCLike.ofRealCLM (K := K)).coeFn_compLp f]
    with x hre hcoe
  rw [hre, hcoe]
  exact RCLike.ofReal_re (K := K) (f x)

/-- Including the real part of a conjugation-fixed class recovers the class. -/
theorem ofRealCLM_compLp_reCLM_compLp_of_star_eq_self {F : Lp K p μ} (hF : star F = F) :
    (RCLike.ofRealCLM (K := K)).compLp ((RCLike.reCLM (K := K)).compLp F) = F := by
  refine Lp.ext ?_
  filter_upwards [(RCLike.ofRealCLM (K := K)).coeFn_compLp ((RCLike.reCLM (K := K)).compLp F),
    (RCLike.reCLM (K := K)).coeFn_compLp F, ae_ofReal_re_eq_of_star_eq_self hF]
    with x hcoe hre hx
  rw [hcoe, hre]
  exact hx

end TauCeti
