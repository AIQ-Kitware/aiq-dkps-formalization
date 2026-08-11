/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.MultiplicityModel
public import ForTauCeti.MeasureTheory.LpRealPart

/-!
# When the real part of a multiplicity model is invariant

A `TauCeti.MultiplicityDatum ℂ` presents multiplication by the (truncated) spectral coordinate
on `L²` of a measure living on `ℂ × ℕ`.  The `star`-fixed part of that `L²` space is the real
`L²` space (`TauCeti.starFixedLpEquivRealLp`), so a real model can only be read off the complex
one if the model operator maps the `star`-fixed part into itself.

**It does not, in general.**  Multiplication by a symbol `w` satisfies `star (w * F) = conj w * F`
on a `star`-fixed `F`, so `w * F` is `star`-fixed exactly where `conj w = w` or `F = 0`.  The main
theorem below is the resulting **biconditional**:

`TauCeti.MultiplicityDatum.StarFixedInvariant D ↔ D.base {z | z.im ≠ 0} = 0`.

Both directions are genuine.  The forward direction is *not* vacuous: it is proved by feeding the
operator the indicator of the non-real part of the zeroth slice, which is an honest element of
`L²` because `MultiplicityDatum.base_finite` makes that set have finite measure, and which is
`star`-fixed because it is real valued.

## Why this is a hypothesis and not a field

`base_supported_real` is deliberately **not** added to `TauCeti.MultiplicityDatum`.  The datum's
one existing support field, `base_supported_level_zero`, is there because without it a datum is
not determined even in principle -- mass outside `level 0` contributes to no summand of
`measure`, so two data differing only there present the *same* operator.  Reality of the base
measure has no such character: a datum whose base charges the non-real points is perfectly well
determined and presents a perfectly good operator.  It is a property of the *operator being
self-adjoint*, not a well-formedness condition on the presentation.

Making it a field would also be an outright regression.  `TauCeti.MultiplicityDatum` has exactly
one construction site in this repository, `TauCeti.BorelCalculus.exists_hasMultiplicityModel`,
which is complex Hahn--Hellinger for an arbitrary bounded **normal** operator.  A normal operator
has complex spectrum, so that construction could not discharge such a field at all.

## Main results

* `TauCeti.MultiplicityDatum.base_eq_zero_iff_measure_fst_preimage_eq_zero`: the base measure and
  the model measure have the same null sets of spectral values.  This is where
  `base_supported_level_zero` is consumed.
* `TauCeti.star_eq_self_iff_of_coeFn_mul`: a class presented as a bounded symbol times a
  `star`-fixed class is `star`-fixed exactly where the symbol is real or the class vanishes.
* `TauCeti.MultiplicityDatum.StarFixedInvariant`: the property that the model operator preserves
  the `star`-fixed part.
* `TauCeti.MultiplicityDatum.starFixedInvariant_iff_base_im_eq_zero`: **the D1 verdict.**
* `TauCeti.MultiplicityDatum.mapsTo_starFixedSubmodule`: the submodule phrasing of the useful
  direction.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

open MeasureTheory

open scoped ENNReal ComplexConjugate

namespace TauCeti

section BaseNull

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The model measure of a set of spectral values is the sum, over the levels, of the base
measure of that set inside each level. -/
theorem MultiplicityDatum.measure_fst_preimage (D : MultiplicityDatum 𝕜) {S : Set ℂ}
    (hS : MeasurableSet S) :
    D.measure (Prod.fst ⁻¹' S) = ∑' k, D.base (S ∩ D.level k) := by
  rw [MultiplicityDatum.measure_def, sliceSum_apply _ (hS.preimage measurable_fst)]
  refine tsum_congr fun k => ?_
  have hfib : {z : ℂ | (z, k) ∈ Prod.fst ⁻¹' S} = S := rfl
  rw [hfib, Measure.restrict_apply hS]

/-- The model measure of the zeroth slice over a set of spectral values is the base measure of
that set inside `level 0` -- and so is finite, because the base measure is. -/
theorem MultiplicityDatum.measure_fst_preimage_inter_slice_zero (D : MultiplicityDatum 𝕜)
    {S : Set ℂ} (hS : MeasurableSet S) :
    D.measure (Prod.fst ⁻¹' S ∩ slice 0) = D.base (S ∩ D.level 0) := by
  rw [MultiplicityDatum.measure_def,
    sliceSum_apply _ ((hS.preimage measurable_fst).inter (measurableSet_slice 0)),
    tsum_eq_single 0 ?_]
  · have hfib : {z : ℂ | (z, (0 : ℕ)) ∈ Prod.fst ⁻¹' S ∩ slice 0} = S := by
      ext z
      simp [mem_slice]
    rw [hfib, Measure.restrict_apply hS]
  · intro m hm
    have hfib : {z : ℂ | (z, m) ∈ Prod.fst ⁻¹' S ∩ slice 0} = (∅ : Set ℂ) := by
      ext z
      simp [mem_slice, hm]
    rw [hfib, measure_empty]

/-- **The base measure and the model measure have the same null sets of spectral values.**

The `←` direction is the one with content, and it is exactly where
`MultiplicityDatum.base_supported_level_zero` is consumed: without that field the base measure
could charge `S` entirely outside `level 0`, where the model measure never looks. -/
theorem MultiplicityDatum.base_eq_zero_iff_measure_fst_preimage_eq_zero (D : MultiplicityDatum 𝕜)
    {S : Set ℂ} (hS : MeasurableSet S) :
    D.base S = 0 ↔ D.measure (Prod.fst ⁻¹' S) = 0 := by
  rw [D.measure_fst_preimage hS, ENNReal.tsum_eq_zero]
  constructor
  · exact fun h k => measure_mono_null Set.inter_subset_left h
  · intro h
    have hsub : S ⊆ (S ∩ D.level 0) ∪ (D.level 0)ᶜ := by
      intro z hz
      by_cases hz0 : z ∈ D.level 0
      · exact Or.inl ⟨hz, hz0⟩
      · exact Or.inr hz0
    exact measure_mono_null hsub (measure_union_null (h 0) D.base_supported_level_zero)

/-- A base-null set of spectral values is avoided by almost every point of the model. -/
theorem MultiplicityDatum.ae_fst_notMem (D : MultiplicityDatum 𝕜) {S : Set ℂ}
    (hS : MeasurableSet S) (h : D.base S = 0) : ∀ᵐ q ∂D.measure, q.1 ∉ S := by
  rw [ae_iff]
  have hset : {q : ℂ × ℕ | ¬ q.1 ∉ S} = Prod.fst ⁻¹' S := by
    ext q
    simp
  rw [hset]
  exact (D.base_eq_zero_iff_measure_fst_preimage_eq_zero hS).mp h

end BaseNull

section StarMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}

/-- A `star`-fixed `Lᵖ` class is almost everywhere fixed by pointwise conjugation.  This is
`ae_ofReal_re_eq_of_star_eq_self` in the phrasing multiplication arguments want. -/
theorem ae_conj_eq_self_of_star_eq_self {F : Lp ℂ p μ} (hF : star F = F) :
    ∀ᵐ x ∂μ, conj ((F : α → ℂ) x) = (F : α → ℂ) x := by
  filter_upwards [ae_ofReal_re_eq_of_star_eq_self hF] with x hx
  exact RCLike.conj_eq_iff_re.mpr hx

/-- **A class presented as a bounded symbol times a `star`-fixed class is `star`-fixed exactly
where the symbol is real or the class vanishes.**

This is the pointwise heart of the D1 verdict: `star` conjugates the symbol and leaves the
`star`-fixed factor alone, so the two products agree iff the conjugated symbol does.  It is
stated for an arbitrary `G` presented by a pointwise product so that it serves both
`mulLpField` and `MultiplicityDatum.operator`, whose bodies the module system does not
expose. -/
theorem star_eq_self_iff_of_coeFn_mul {g : α → ℂ} {F G : Lp ℂ 2 μ}
    (hG : (G : α → ℂ) =ᵐ[μ] fun x => g x * (F : α → ℂ) x) (hF : star F = F) :
    star G = G ↔ ∀ᵐ x ∂μ, conj (g x) * (F : α → ℂ) x = g x * (F : α → ℂ) x := by
  have hkey : ∀ᵐ x ∂μ, ((star G : Lp ℂ 2 μ) : α → ℂ) x = conj (g x) * (F : α → ℂ) x := by
    filter_upwards [Lp.coeFn_star G, hG, ae_conj_eq_self_of_star_eq_self hF] with x h1 h2 h3
    rw [h1, Pi.star_apply, h2, RCLike.star_def, map_mul, h3]
  constructor
  · intro h
    have hcoe : ((star G : Lp ℂ 2 μ) : α → ℂ) = (G : α → ℂ) :=
      congrArg (fun H : Lp ℂ 2 μ => (H : α → ℂ)) h
    filter_upwards [hkey, hG] with x h1 h2
    calc conj (g x) * (F : α → ℂ) x = ((star G : Lp ℂ 2 μ) : α → ℂ) x := h1.symm
      _ = (G : α → ℂ) x := congrFun hcoe x
      _ = g x * (F : α → ℂ) x := h2
  · intro h
    refine Lp.ext ?_
    filter_upwards [hkey, hG, h] with x h1 h2 h3
    calc ((star G : Lp ℂ 2 μ) : α → ℂ) x = conj (g x) * (F : α → ℂ) x := h1
      _ = g x * (F : α → ℂ) x := h3
      _ = (G : α → ℂ) x := h2.symm

/-- The `mulLpField` specialization of `star_eq_self_iff_of_coeFn_mul`. -/
theorem star_mulLpField_eq_self_iff (ρ : Measure α) {g : α → ℂ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) {F : Lp ℂ 2 ρ} (hF : star F = F) :
    star (mulLpField ρ hg hgC F) = mulLpField ρ hg hgC F ↔
      ∀ᵐ x ∂ρ, conj (g x) * (F : α → ℂ) x = g x * (F : α → ℂ) x :=
  star_eq_self_iff_of_coeFn_mul (coeFn_mulLpField ρ hg hgC F) hF

end StarMultiplication

section Coord

/-- Inside the ball, reality of the point makes the truncated coordinate real. -/
theorem conj_coordTrunc_of_im_eq_zero {R : ℝ} {z : ℂ} (hzR : ‖z‖ ≤ R) (hz : z.im = 0) :
    conj (coordTrunc R z) = coordTrunc R z := by
  rw [coordTrunc_eq_self hzR]
  exact Complex.conj_eq_iff_im.mpr hz

/-- Inside the ball, where the truncation is inert, reality of the truncated coordinate is
reality of the point. -/
theorem im_eq_zero_of_conj_coordTrunc {R : ℝ} {z : ℂ} (hzR : ‖z‖ ≤ R)
    (h : conj (coordTrunc R z) = coordTrunc R z) : z.im = 0 := by
  rw [coordTrunc_eq_self hzR] at h
  exact Complex.conj_eq_iff_im.mp h

end Coord

section StarFixedInvariance

/-- The set of non-real spectral values is measurable. -/
theorem measurableSet_im_ne_zero : MeasurableSet {z : ℂ | z.im ≠ 0} :=
  (Complex.measurable_im (measurableSet_singleton (0 : ℝ))).compl

/-- **The model operator preserves the `star`-fixed part of its `L²` space.**

Named rather than left inline because both directions of the D1 verdict quantify over it, and
because it is the hypothesis every real-model construction downstream will carry. -/
def MultiplicityDatum.StarFixedInvariant (D : MultiplicityDatum ℂ) : Prop :=
  ∀ F : Lp ℂ 2 D.measure, star F = F → star (D.operator F) = D.operator F

/-- The model operator is pointwise multiplication by the *complex* truncated coordinate; this is
`MultiplicityDatum.coeFn_operator` with the field-valued symbol specialized. -/
theorem MultiplicityDatum.coeFn_operator_complex (D : MultiplicityDatum ℂ)
    (F : Lp ℂ 2 D.measure) :
    (D.operator F : ℂ × ℕ → ℂ) =ᵐ[D.measure]
      fun q => coordTrunc D.bound q.1 * (F : ℂ × ℕ → ℂ) q := by
  simpa only [coordTruncField_complex] using D.coeFn_operator F

/-- The model operator's action on a `star`-fixed class, tested pointwise. -/
theorem MultiplicityDatum.star_operator_eq_self_iff (D : MultiplicityDatum ℂ)
    {F : Lp ℂ 2 D.measure} (hF : star F = F) :
    star (D.operator F) = D.operator F ↔
      ∀ᵐ q ∂D.measure, conj (coordTrunc D.bound q.1) * (F : ℂ × ℕ → ℂ) q
        = coordTrunc D.bound q.1 * (F : ℂ × ℕ → ℂ) q :=
  star_eq_self_iff_of_coeFn_mul (D.coeFn_operator_complex F) hF

/-- A datum carried by the real axis has `star`-invariant real part.  This is the direction the
real Hahn--Hellinger route consumes. -/
theorem MultiplicityDatum.starFixedInvariant_of_base_im_eq_zero {D : MultiplicityDatum ℂ}
    (h : D.base {z : ℂ | z.im ≠ 0} = 0) : D.StarFixedInvariant := by
  intro F hF
  rw [D.star_operator_eq_self_iff hF]
  filter_upwards [D.ae_fst_notMem measurableSet_im_ne_zero h, D.ae_norm_le_bound] with q hq hqb
  have him : (q.1 : ℂ).im = 0 := by simpa using hq
  rw [conj_coordTrunc_of_im_eq_zero hqb him]

/-- **The converse.**  If the model operator preserves the `star`-fixed part then the base measure
is carried by the real axis.

The witness is the indicator of the non-real part of the zeroth slice.  It lies in `L²` because
`MultiplicityDatum.base_finite` makes that set have finite model measure, and it is `star`-fixed
because it is real valued; feeding it to the hypothesis forces the set to be null, and
`base_eq_zero_iff_measure_fst_preimage_eq_zero` converts that back to the base measure. -/
theorem MultiplicityDatum.base_im_eq_zero_of_starFixedInvariant {D : MultiplicityDatum ℂ}
    (h : D.StarFixedInvariant) : D.base {z : ℂ | z.im ≠ 0} = 0 := by
  classical
  set S : Set ℂ := {z : ℂ | z.im ≠ 0} with hSdef
  set T : Set (ℂ × ℕ) := Prod.fst ⁻¹' S ∩ slice 0 with hTdef
  have hSm : MeasurableSet S := measurableSet_im_ne_zero
  have hTm : MeasurableSet T := (hSm.preimage measurable_fst).inter (measurableSet_slice 0)
  have hTval : D.measure T = D.base (S ∩ D.level 0) :=
    D.measure_fst_preimage_inter_slice_zero hSm
  have hTfin : D.measure T ≠ ⊤ := by
    rw [hTval]
    exact (measure_lt_top D.base _).ne
  set F : Lp ℂ 2 D.measure := indicatorConstLp 2 hTm hTfin (1 : ℂ) with hFdef
  have hFcoe : (F : ℂ × ℕ → ℂ) =ᵐ[D.measure] T.indicator fun _ => (1 : ℂ) :=
    indicatorConstLp_coeFn
  have hFstar : star F = F := by
    rw [star_eq_self_iff_ae_im_eq_zero]
    filter_upwards [hFcoe] with q hq
    rw [hq, Set.indicator_apply]
    split_ifs <;> simp
  have hmain := (D.star_operator_eq_self_iff hFstar).mp (h F hFstar)
  have hnull : ∀ᵐ q ∂D.measure, q ∉ T := by
    filter_upwards [hmain, hFcoe, D.ae_norm_le_bound] with q h1 h2 h3
    intro hqT
    have hone : (F : ℂ × ℕ → ℂ) q = 1 := by
      rw [h2, Set.indicator_of_mem hqT]
    rw [hone, mul_one, mul_one] at h1
    exact hqT.1 (im_eq_zero_of_conj_coordTrunc h3 h1)
  have hT0 : D.measure T = 0 := by
    have h' := (ae_iff (μ := D.measure) (p := fun q => q ∉ T)).mp hnull
    have hset : {q : ℂ × ℕ | ¬ q ∉ T} = T := by
      ext q
      simp
    rwa [hset] at h'
  have hbase0 : D.base (S ∩ D.level 0) = 0 := by rw [← hTval, hT0]
  have hsub : S ⊆ (S ∩ D.level 0) ∪ (D.level 0)ᶜ := by
    intro z hz
    by_cases hz0 : z ∈ D.level 0
    · exact Or.inl ⟨hz, hz0⟩
    · exact Or.inr hz0
  exact measure_mono_null hsub (measure_union_null hbase0 D.base_supported_level_zero)

/-- **D1, the verdict.**  The `star`-fixed part of the model `L²` space is invariant under the
model operator **if and only if** the base measure is carried by the real axis.

Neither direction is formal.  The `←` direction is what a real Hahn--Hellinger model needs; the
`→` direction is what says the hypothesis cannot be dropped, since a datum charging any non-real
set of positive base measure already breaks invariance. -/
theorem MultiplicityDatum.starFixedInvariant_iff_base_im_eq_zero (D : MultiplicityDatum ℂ) :
    D.StarFixedInvariant ↔ D.base {z : ℂ | z.im ≠ 0} = 0 :=
  ⟨MultiplicityDatum.base_im_eq_zero_of_starFixedInvariant,
    MultiplicityDatum.starFixedInvariant_of_base_im_eq_zero⟩

/-- The submodule phrasing: for a real-carried datum the model operator maps
`TauCeti.starFixedSubmodule` into itself, which is the form `TauCeti.starFixedLpEquivRealLp`
consumes. -/
theorem MultiplicityDatum.mapsTo_starFixedSubmodule {D : MultiplicityDatum ℂ}
    (h : D.base {z : ℂ | z.im ≠ 0} = 0) :
    ∀ F ∈ starFixedSubmodule ℂ 2 D.measure,
      D.operator F ∈ starFixedSubmodule ℂ 2 D.measure := by
  intro F hF
  rw [mem_starFixedSubmodule] at hF ⊢
  exact MultiplicityDatum.starFixedInvariant_of_base_im_eq_zero h F hF

end StarFixedInvariance

section Compression

variable {α : Type*} [MeasurableSpace α]

/-- **The real-valued multiplication operator is the compression of the complex one to the real
classes -- unconditionally.**

`RCLike.map ℂ ℝ` is `RCLike.reCLM` (`RCLike.map_to_real`), so `coordTruncField ℝ` is the real
part of `coordTrunc`; this lemma is the corresponding statement one level down, for an arbitrary
bounded symbol.  It holds with no reality hypothesis because the real part of `w * r` is
`(re w) * r` whenever `r` is real.

What it does **not** say is that the complex operator *restricts*: the compression is a
restriction exactly when `MultiplicityDatum.StarFixedInvariant` holds, which by
`MultiplicityDatum.starFixedInvariant_iff_base_im_eq_zero` is exactly reality of the base
measure. -/
theorem reLp_mulLpField_ofRealLp (ρ : Measure α) {g : α → ℂ} (hg : Measurable g) {C : ℝ}
    (hgC : ∀ x, ‖g x‖ ≤ C) (f : Lp ℝ 2 ρ) :
    reLp (mulLpField ρ hg hgC (ofRealLp f)) =
      mulLpField ρ (𝕜 := ℝ) (Complex.measurable_re.comp hg)
        (fun x => (RCLike.norm_re_le_norm (K := ℂ) (g x)).trans (hgC x)) f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_reLp (mulLpField ρ hg hgC (ofRealLp f)),
    coeFn_mulLpField ρ hg hgC (ofRealLp (K := ℂ) f),
    coeFn_ofRealLp (K := ℂ) f,
    coeFn_mulLpField ρ (𝕜 := ℝ) (Complex.measurable_re.comp hg)
      (fun x => (RCLike.norm_re_le_norm (K := ℂ) (g x)).trans (hgC x)) f] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  simp

end Compression

end TauCeti
