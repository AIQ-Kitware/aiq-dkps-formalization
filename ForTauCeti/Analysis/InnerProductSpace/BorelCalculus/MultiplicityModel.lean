/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.SeparableCyclic
public import ForTauCeti.Analysis.InnerProductSpace.HilbertSumIntertwine
public import ForTauCeti.MeasureTheory.MultiplicityLevels

/-!
# The multiplication model of a normal operator, in multiplicity normal form

**Every bounded normal operator on a separable complex Hilbert space is unitarily equivalent to
multiplication by the spectral coordinate on `L²` of a level-set family.**  That is the existence
half of Hahn--Hellinger, and it is what makes "same spectral multiplicity" a statement with
content rather than a statement about an opaque term.

The datum produced is a `TauCeti.MultiplicityDatum`: a finite measure `base` on `ℂ` supported in
a ball, together with an **antitone** sequence of measurable level sets.  Its meaning is the
usual one -- `base` carries the measure class of the operator and `k ↦ level k` is the sequence
of super-level sets of the multiplicity function -- and its `operator` is multiplication by the
spectral coordinate on the assembled `L²` space.

## The chain

1. `exists_countable_isHilbertSum_lp_diagMeasure`: `H` is the Hilbert sum of the `L²` spaces of
   the scalar spectral measures of countably many vectors, with `a` acting by coordinate
   multiplication on each.
2. `embLpEquiv`: those measures move off the `spectrum` subtype onto `ℂ`, where models of
   different operators can be compared.
3. `isHilbertSum_sliceLp`: the same family of `L²` spaces assembles into `L²` of a single measure
   on `ℂ × ℕ`, again with coordinate multiplication.
4. `operatorUnitaryEquiv_of_isHilbertSum`: two Hilbert sums of one family carry the same
   operator, so `a` *is* that multiplication operator.
5. `exists_multiplicityLevels`: the assembled measure is normalised to level-set form.

Only step 1 uses separability, and only to make the index type `ℕ` -- which the level-set
normalisation needs, since ranks count *earlier* indices.

## Main results

* `TauCeti.MultiplicityDatum`: the datum.
* `TauCeti.exists_hasMultiplicityModel`: **existence of a model.**
* `TauCeti.operatorUnitaryEquiv_of_measureEquiv`: **data agreeing up to measure class and null
  sets present unitarily equivalent operators.**

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

section Coord

/-- **The spectral coordinate, truncated outside a ball.**  Multiplication operators need a
*bounded* symbol, and the coordinate is unbounded on `ℂ`; truncating outside a ball that already
contains the spectrum changes nothing where the spectral measure lives. -/
noncomputable def coordTrunc (R : ℝ) : ℂ → ℂ := fun z => if ‖z‖ ≤ R then z else 0

/-- The truncated coordinate is measurable: it is the identity on a closed sublevel set of the
norm and zero off it. -/
theorem measurable_coordTrunc (R : ℝ) : Measurable (coordTrunc R) :=
  Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_id
    measurable_const

/-- The truncated coordinate is bounded by the truncation radius -- which is the whole point of
truncating. -/
theorem norm_coordTrunc_le {R : ℝ} (hR : 0 ≤ R) (z : ℂ) : ‖coordTrunc R z‖ ≤ R := by
  rw [coordTrunc]
  split_ifs with h
  · exact h
  · simpa using hR

/-- Inside the ball the truncation does nothing, so a model whose measure lives there multiplies
by the coordinate itself. -/
theorem coordTrunc_eq_self {R : ℝ} {z : ℂ} (h : ‖z‖ ≤ R) : coordTrunc R z = z := if_pos h

end Coord

section Datum

/-- **A multiplicity datum**: a finite measure on `ℂ` supported in a ball, together with an
antitone sequence of measurable level sets.

The measure carries the measure class; the level sets encode the cardinal-valued multiplicity
function by its super-level sets, which is what makes every hypothesis a plain `MeasurableSet`
rather than measurability of an `ℕ∞`-valued function.  The bound is part of the *presentation*,
not of the invariant: it exists only so the coordinate symbol is bounded. -/
structure MultiplicityDatum where
  /-- The base measure, carrying the measure class. -/
  base : Measure ℂ
  /-- A bound outside which the base measure vanishes. -/
  bound : ℝ
  /-- The super-level sets of the multiplicity function. -/
  level : ℕ → Set ℂ
  /-- The base measure is finite. -/
  base_finite : IsFiniteMeasure base
  /-- The bound is nonnegative. -/
  bound_nonneg : 0 ≤ bound
  /-- The base measure lives inside the ball of radius `bound`. -/
  base_supported : base {z | bound < ‖z‖} = 0
  /-- The level sets are measurable. -/
  measurableSet_level : ∀ k, MeasurableSet (level k)
  /-- The level sets decrease: this is what makes them super-level sets of a function. -/
  antitone_level : Antitone level

attribute [instance] MultiplicityDatum.base_finite

/-- The measure of the model: the slice sum of the restrictions to the level sets. -/
noncomputable def MultiplicityDatum.measure (D : MultiplicityDatum) : Measure (ℂ × ℕ) :=
  sliceSum fun k => D.base.restrict (D.level k)

/-- The model measure is σ-finite: its slices are spanning sets of finite measure, because the
base measure is finite.  This is what lets the Radon--Nikodym unitary compare two models. -/
instance MultiplicityDatum.sigmaFinite_measure (D : MultiplicityDatum) :
    SigmaFinite D.measure := by
  rw [MultiplicityDatum.measure]
  infer_instance

/-- **The model operator**: multiplication by the spectral coordinate. -/
noncomputable def MultiplicityDatum.operator (D : MultiplicityDatum) :
    Lp ℂ 2 D.measure →L[ℂ] Lp ℂ 2 D.measure :=
  mulLp D.measure ((measurable_coordTrunc D.bound).comp measurable_fst)
    (fun p => norm_coordTrunc_le D.bound_nonneg p.1)

/-- The model measure lives where the coordinate is bounded by the datum's bound. -/
theorem MultiplicityDatum.ae_norm_le_bound (D : MultiplicityDatum) :
    ∀ᵐ p ∂D.measure, ‖p.1‖ ≤ D.bound := by
  rw [ae_iff]
  have hmeas : MeasurableSet {p : ℂ × ℕ | ¬ ‖p.1‖ ≤ D.bound} :=
    (measurableSet_le (measurable_norm.comp measurable_fst) measurable_const).compl
  rw [MultiplicityDatum.measure, sliceSum_apply _ hmeas, ENNReal.tsum_eq_zero]
  intro k
  have hfib : {z : ℂ | (z, k) ∈ {p : ℂ × ℕ | ¬ ‖p.1‖ ≤ D.bound}} = {z : ℂ | D.bound < ‖z‖} := by
    refine Set.ext fun z => ?_
    simp only [Set.mem_setOf_eq, not_le]
  rw [hfib, Measure.restrict_apply (measurableSet_lt measurable_const measurable_norm)]
  exact measure_mono_null Set.inter_subset_left D.base_supported

end Datum

section Equivalence

/-- The two truncations of the coordinate agree where the model measure lives. -/
theorem operator_eq_mulLp_of_le {D : MultiplicityDatum} {R : ℝ} (hR : 0 ≤ R)
    (hle : D.bound ≤ R) :
    D.operator = mulLp D.measure ((measurable_coordTrunc R).comp measurable_fst)
      (fun p => norm_coordTrunc_le hR p.1) := by
  refine mulLp_congr_ae _ _ _ _ _ ?_
  filter_upwards [D.ae_norm_le_bound] with p hp
  rw [Function.comp_apply, Function.comp_apply, coordTrunc_eq_self hp,
    coordTrunc_eq_self (hp.trans hle)]

/-- **Data agreeing up to measure class and null sets present unitarily equivalent operators.**

The measure classes of the two model measures agree fibrewise -- restricting one base measure to
almost-equal sets gives literally the same measure, and the bases are equivalent -- so the
Radon--Nikodym unitary applies once the two coordinate symbols are truncated at a common
bound. -/
theorem operatorUnitaryEquiv_of_measureEquiv {D E : MultiplicityDatum}
    (hbase : MeasureEquiv D.base E.base)
    (hlevel : ∀ k, D.base (symmDiff (D.level k) (E.level k)) = 0) :
    OperatorUnitaryEquiv D.operator E.operator := by
  have hlev : ∀ k, (D.level k : Set ℂ) =ᵐ[D.base] (E.level k : Set ℂ) := fun k =>
    measure_symmDiff_eq_zero_iff.mp (hlevel k)
  have hfib : ∀ k, MeasureEquiv (D.base.restrict (D.level k)) (E.base.restrict (E.level k)) :=
    fun k => (measureEquiv_restrict_congr (hlev k)).trans (hbase.restrict (E.level k))
  have hmeas : MeasureEquiv D.measure E.measure := by
    rw [MultiplicityDatum.measure, MultiplicityDatum.measure]
    exact measureEquiv_sliceSum hfib
  set R : ℝ := max D.bound E.bound with hRdef
  have hR0 : 0 ≤ R := le_trans D.bound_nonneg (le_max_left _ _)
  rw [operator_eq_mulLp_of_le (D := D) hR0 (le_max_left _ _),
    operator_eq_mulLp_of_le (D := E) hR0 (le_max_right _ _)]
  exact operatorUnitaryEquiv_of_intertwines (rnDerivL2Equiv hmeas.1 hmeas.2) fun F =>
    rnDerivL2Equiv_mulLp hmeas.1 hmeas.2 ((measurable_coordTrunc R).comp measurable_fst)
      (fun p => norm_coordTrunc_le hR0 p.1) F

end Equivalence

namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

/-- Multiplication by any symbol that agrees with the coordinate on the spectrum *is* coordinate
multiplication.  Stated with the symbol arbitrary so that call sites never have to match a
truncation syntactically. -/
theorem mulLp_eq_coordMulLp (ha : IsStarNormal a) (ξ : H) {g : spectrum ℂ a → ℂ}
    (hg : Measurable g) {C : ℝ} (hgC : ∀ w, ‖g w‖ ≤ C)
    (hgeq : ∀ w : spectrum ℂ a, g w = (w : ℂ)) (F : Lp ℂ 2 (diagMeasure ha ξ)) :
    mulLp (diagMeasure ha ξ) hg hgC F = coordMulLp ha ξ F := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mulLp (diagMeasure ha ξ) hg hgC F, coeFn_coordMulLp ha ξ F] with w h1 h2
  rw [h1, h2, hgeq w]

/-- **Every bounded normal operator on a separable complex Hilbert space has a multiplicity
model.**  This is the existence half of Hahn--Hellinger. -/
theorem exists_hasMultiplicityModel [TopologicalSpace.SeparableSpace H] (ha : IsStarNormal a) :
    ∃ D : MultiplicityDatum, OperatorUnitaryEquiv a D.operator := by
  classical
  have hR0 : (0 : ℝ) ≤ ‖a‖ * ‖(1 : H →L[ℂ] H)‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hspec : ∀ w : spectrum ℂ a, ‖(w : ℂ)‖ ≤ ‖a‖ * ‖(1 : H →L[ℂ] H)‖ := by
    intro w
    have hw := spectrum.subset_closedBall_norm_mul a w.2
    simpa [Metric.mem_closedBall, dist_zero_right] using hw
  have hmeasSpec : MeasurableSet (spectrum ℂ a) := (spectrum.isCompact a).isClosed.measurableSet
  have hemb : MeasurableEmbedding ((↑) : spectrum ℂ a → ℂ) :=
    MeasurableEmbedding.subtype_coe hmeasSpec
  obtain ⟨ξ, hsum⟩ := exists_countable_isHilbertSum_lp_diagMeasure ha
  haveI hfin : ∀ n, IsFiniteMeasure (Measure.map ((↑) : spectrum ℂ a → ℂ)
      (diagMeasure ha (ξ n))) := fun n => Measure.isFiniteMeasure_map _ _
  have hsum' : IsHilbertSum ℂ
      (fun n => Lp ℂ 2 (Measure.map ((↑) : spectrum ℂ a → ℂ) (diagMeasure ha (ξ n))))
      (fun n => (cyclicIsometry ha (ξ n)).comp
        (embLpEquiv hemb (diagMeasure ha (ξ n))).toLinearIsometry) :=
    isHilbertSum_comp_linearIsometryEquiv hsum fun n => embLpEquiv hemb (diagMeasure ha (ξ n))
  have hsum2 := isHilbertSum_sliceLp
    (fun n => Measure.map ((↑) : spectrum ℂ a → ℂ) (diagMeasure ha (ξ n)))
  have hA : ∀ (n : ℕ)
      (F : Lp ℂ 2 (Measure.map ((↑) : spectrum ℂ a → ℂ) (diagMeasure ha (ξ n)))),
      a (((cyclicIsometry ha (ξ n)).comp
          (embLpEquiv hemb (diagMeasure ha (ξ n))).toLinearIsometry) F)
        = ((cyclicIsometry ha (ξ n)).comp
          (embLpEquiv hemb (diagMeasure ha (ξ n))).toLinearIsometry)
          (mulLp _ (measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖))
            (norm_coordTrunc_le hR0) F) := by
    intro n F
    have h1 : embLpEquiv hemb (diagMeasure ha (ξ n))
        (mulLp _ (measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖)) (norm_coordTrunc_le hR0) F)
        = coordMulLp ha (ξ n) (embLpEquiv hemb (diagMeasure ha (ξ n)) F) :=
      (embLpEquiv_mulLp hemb (diagMeasure ha (ξ n))
        (measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖)) (norm_coordTrunc_le hR0) F).trans
        (mulLp_eq_coordMulLp ha (ξ n) _ _ (fun w => coordTrunc_eq_self (hspec w)) _)
    change a (cyclicIsometry ha (ξ n) (embLpEquiv hemb (diagMeasure ha (ξ n)) F))
      = cyclicIsometry ha (ξ n) (embLpEquiv hemb (diagMeasure ha (ξ n)) _)
    rw [h1, cyclicIsometry_coordMulLp ha (ξ n)]
  have hB : ∀ (n : ℕ)
      (F : Lp ℂ 2 (Measure.map ((↑) : spectrum ℂ a → ℂ) (diagMeasure ha (ξ n)))),
      (mulLp _ ((measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖)).comp measurable_fst)
          (fun p => norm_coordTrunc_le hR0 p.1))
        (sliceLp (fun n => Measure.map ((↑) : spectrum ℂ a → ℂ)
          (diagMeasure ha (ξ n))) n F)
        = sliceLp (fun n => Measure.map ((↑) : spectrum ℂ a → ℂ) (diagMeasure ha (ξ n))) n
          (mulLp _ (measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖))
            (norm_coordTrunc_le hR0) F) :=
    fun n F => (sliceLp_mulLp (fun m => Measure.map ((↑) : spectrum ℂ a → ℂ)
      (diagMeasure ha (ξ m))) n (measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖))
      (norm_coordTrunc_le hR0) F).symm
  have hstep1 := operatorUnitaryEquiv_of_isHilbertSum hsum' hsum2 hA hB
  obtain ⟨ρ, D, hρfin, hDmeas, hDanti, hρsupp, hstep2⟩ :=
    exists_multiplicityLevels (fun n => Measure.map ((↑) : spectrum ℂ a → ℂ)
      (diagMeasure ha (ξ n))) (measurable_coordTrunc (‖a‖ * ‖(1 : H →L[ℂ] H)‖))
      (norm_coordTrunc_le hR0)
  refine ⟨⟨ρ, ‖a‖ * ‖(1 : H →L[ℂ] H)‖, D, hρfin, hR0, ?_, hDmeas, hDanti⟩,
    hstep1.trans hstep2⟩
  refine hρsupp _ (measurableSet_lt measurable_const measurable_norm) fun n => ?_
  rw [Measure.map_apply hemb.measurable (measurableSet_lt measurable_const measurable_norm)]
  convert measure_empty (μ := diagMeasure ha (ξ n))
  refine Set.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
  exact absurd (hspec w) (not_le.mpr hw)

end BorelCalculus

end TauCeti
