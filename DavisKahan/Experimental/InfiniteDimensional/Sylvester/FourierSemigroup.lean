/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.SpectralProjection
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.FiniteBlockReconstruction
import ForMathlib.Analysis.Fourier.HaagerupZsidoKernel
import Spectra.YosidaHille.Approximation.ExpBounded.Unitary
import Spectra.CayleyTransform.BorelCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Fourier and semigroup formulas for bounded Sylvester equations

This file supplies the analytic layer used by the infinite-dimensional
Sylvester development.  The oscillatory formula is necessarily complex: the
phase `exp (i t A)` has no same-space real-linear analogue.  Real Hilbert-space
consequences are obtained after complexification, not by assigning a fake
imaginary unit to `R`.

The reciprocal multiplier is the scaled Haagerup--Zsido kernel

`mu_d(t) = reciprocalKernel (d t)`.

With the Fourier convention used in this repository it satisfies

`integral mu_d(t) exp(i t x) dt = 1/x`,  when `d <= |x|`,

and its exact mass is `pi/(2 d)`.  The factor `pi/2` is essential; an `L1`
mass of `1/d` would assert a false general separated-spectrum estimate.

The operator reconstruction is proved by finite spectral step approximation.
Each self-adjoint operator is approximated in norm by a finite sum of its own
spectral projections, with representatives chosen from the original spectrum.
Consequently the cross-gap is preserved exactly.  The formula is first checked
block by block for the finite spectral sums and then passed to the limit by
Bochner dominated convergence.
-/

namespace ForMathlib
namespace DavisKahanExt

open MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators
open Spectra.YosidaHille.Approximation

noncomputable section

universe u v

section ScalarKernel

/-- Scaled Haagerup--Zsido reciprocal kernel. -/
def separatedSylvesterMultiplier (d : ℝ) (_hd : 0 < d) : ℝ → ℂ :=
  fun t => HaagerupZsido.reciprocalKernel (d * t)

/-- The scaled reciprocal kernel is Bochner integrable. -/
theorem integrable_separatedSylvesterMultiplier (d : ℝ) (hd : 0 < d) :
    Integrable (separatedSylvesterMultiplier d hd) := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hbase := HaagerupZsido.integrable_reciprocalKernel
  exact hbase.comp_mul_left' hd0

/-- Exact Fourier identity for the scaled reciprocal kernel. -/
theorem separatedSylvesterMultiplier_identity
    (d : ℝ) (hd : 0 < d) (a b : ℝ) (hab : d ≤ |a - b|) :
    (∫ t : ℝ, separatedSylvesterMultiplier d hd t *
      Complex.exp ((((t * (a - b) : ℝ) : ℂ) * Complex.I))) =
      (((a - b)⁻¹ : ℝ) : ℂ) := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hab0 : a - b ≠ 0 := by
    have : 0 < |a - b| := lt_of_lt_of_le hd hab
    exact abs_pos.mp this
  set x : ℝ := (a - b) / d with hxdef
  have hx : 1 ≤ |x| := by
    rw [hxdef, abs_div, abs_of_pos hd, le_div_iff₀ hd, one_mul]
    exact hab
  have hfourier := HaagerupZsido.reciprocalKernel_fourier x hx
  set g : ℝ → ℂ := fun s =>
    HaagerupZsido.reciprocalKernel s *
      Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) with hgdef
  have hchange := MeasureTheory.Measure.integral_comp_mul_left g d
  have harg : ∀ t : ℝ, d * t * x = t * (a - b) := by
    intro t; rw [hxdef]; field_simp
  have hpoint : (fun t : ℝ => g (d * t)) =
      fun t : ℝ => separatedSylvesterMultiplier d hd t *
        Complex.exp ((((t * (a - b) : ℝ) : ℂ) * Complex.I)) := by
    funext t
    simp only [hgdef, separatedSylvesterMultiplier, harg t]
  rw [← hpoint, hchange, hfourier]
  have hxc : (x : ℂ) = ((a - b : ℝ) : ℂ) / (d : ℂ) := by
    rw [hxdef]; push_cast; ring
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
  have habc : ((a - b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hab0
  rw [abs_of_pos (by positivity : (0:ℝ) < d⁻¹), Complex.real_smul, hxc]
  push_cast
  field_simp

/-- Exact `L1` mass of the scaled reciprocal kernel. -/
theorem l1_norm_separatedSylvesterMultiplier (d : ℝ) (hd : 0 < d) :
    (∫ t : ℝ, ‖separatedSylvesterMultiplier d hd t‖) =
      Real.pi / (2 * d) := by
  let g : ℝ → ℝ := fun s => ‖HaagerupZsido.reciprocalKernel s‖
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hchange := MeasureTheory.Measure.integral_comp_mul_left g d
  have hpoint : (fun t : ℝ => g (d * t)) =
      fun t : ℝ => ‖separatedSylvesterMultiplier d hd t‖ := by
    funext t
    rfl
  rw [← hpoint]
  calc
    (∫ t : ℝ, g (d * t)) = d⁻¹ * ∫ s : ℝ, g s := by
      simpa [Real.norm_eq_abs, abs_of_pos hd, one_div, smul_eq_mul] using hchange
    _ = d⁻¹ * (Real.pi / 2) := by
      rw [HaagerupZsido.integral_norm_reciprocalKernel]
    _ = Real.pi / (2 * d) := by
      field_simp [hd0]

/-- A form convenient for the final Sylvester estimate. -/
theorem mul_l1_norm_separatedSylvesterMultiplier (d : ℝ) (hd : 0 < d) :
    d * (∫ t : ℝ, ‖separatedSylvesterMultiplier d hd t‖) = Real.pi / 2 := by
  rw [l1_norm_separatedSylvesterMultiplier d hd]
  field_simp [ne_of_gt hd]

end ScalarKernel

section Exponentials

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The unitary group `exp(i t A)` of a bounded complex operator. -/
noncomputable def unitaryGroup (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  expBounded (Complex.I • A) t

/-- The real exponential semigroup `exp(t A)`. -/
noncomputable def semigroup (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  expBounded A t

@[simp] theorem unitaryGroup_zero (A : H →L[ℂ] H) :
    unitaryGroup A 0 = 1 := by
  exact expBounded_at_zero' (Complex.I • A)

@[simp] theorem semigroup_zero (A : H →L[ℂ] H) :
    semigroup A 0 = 1 := by
  exact expBounded_at_zero' A

/-- Group law for `exp(i t A)`. -/
theorem unitaryGroup_add (A : H →L[ℂ] H) (s t : ℝ) :
    unitaryGroup A (s + t) = unitaryGroup A s ∘L unitaryGroup A t := by
  exact expBounded_add_smul (Complex.I • A) s t

/-- Semigroup/group law for `exp(t A)`. -/
theorem semigroup_add (A : H →L[ℂ] H) (s t : ℝ) :
    semigroup A (s + t) = semigroup A s ∘L semigroup A t := by
  exact expBounded_add_smul A s t

/-- Self-adjoint generators give unitary exponentials. -/
theorem unitaryGroup_mem_unitary (A : H →L[ℂ] H)
    (hA : IsSelfAdjointOperator A) (t : ℝ) :
    unitaryGroup A t ∈ unitary (H →L[ℂ] H) := by
  apply expBounded_mem_unitary
  exact smul_I_skewSelfAdjoint A hA.clm_adjoint_eq

/-- The inverse of `exp(i t A)` is `exp(-i t A)`. -/
theorem unitaryGroup_neg_mul (A : H →L[ℂ] H)
    (hA : IsSelfAdjointOperator A) (t : ℝ) :
    unitaryGroup A (-t) ∘L unitaryGroup A t = 1 ∧
      unitaryGroup A t ∘L unitaryGroup A (-t) = 1 := by
  have hsum1 := unitaryGroup_add A (-t) t
  have hsum2 := unitaryGroup_add A t (-t)
  simpa using And.intro hsum1.symm hsum2.symm

/-- Every unitary group element is a contraction. -/
theorem norm_unitaryGroup_le_one (A : H →L[ℂ] H)
    (hA : IsSelfAdjointOperator A) (t : ℝ) :
    ‖unitaryGroup A t‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  rw [one_mul]
  exact le_of_eq
    (ContinuousLinearMap.norm_map_of_mem_unitary (unitaryGroup_mem_unitary A hA t) x)

/-- On a nonzero Hilbert space every unitary group element has norm one. -/
theorem norm_unitaryGroup [Nontrivial H] (A : H →L[ℂ] H)
    (hA : IsSelfAdjointOperator A) (t : ℝ) :
    ‖unitaryGroup A t‖ = 1 := by
  exact CStarRing.norm_coe_unitary
    (⟨unitaryGroup A t, unitaryGroup_mem_unitary A hA t⟩ : unitary (H →L[ℂ] H))

/-- Two-sided unitary multiplication preserves the operator norm. -/
theorem norm_unitary_left_right
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (B : E →L[ℂ] E) (hB : IsSelfAdjointOperator B)
    (t : ℝ) (C : E →L[ℂ] H) :
    ‖unitaryGroup A t ∘L C ∘L unitaryGroup B (-t)‖ = ‖C‖ := by
  let UA := unitaryGroup A t
  let UB := unitaryGroup B (-t)
  let UAinv := unitaryGroup A (-t)
  let UBinv := unitaryGroup B t
  have hforward : ‖UA ∘L C ∘L UB‖ ≤ ‖C‖ := by
    calc
      ‖UA ∘L C ∘L UB‖ ≤ ‖UA‖ * ‖C‖ * ‖UB‖ := by
        refine (UA.opNorm_comp_le (C ∘L UB)).trans ?_
        rw [mul_assoc]
        gcongr
        exact C.opNorm_comp_le UB
      _ ≤ 1 * ‖C‖ * 1 := by
        gcongr
        · exact norm_unitaryGroup_le_one A hA t
        · exact norm_unitaryGroup_le_one B hB (-t)
      _ = ‖C‖ := by ring
  have hrecover : UAinv ∘L (UA ∘L C ∘L UB) ∘L UBinv = C := by
    ext x
    simp only [ContinuousLinearMap.comp_apply]
    have hAinv := (unitaryGroup_neg_mul A hA t).1
    have hBinv := (unitaryGroup_neg_mul B hB (-t)).2
    have hBx : UB (UBinv x) = x := by
      simpa [UB, UBinv] using
        congrArg (fun T : E →L[ℂ] E => T x) hBinv
    rw [hBx]
    simpa [UA, UAinv] using
      congrArg (fun T : H →L[ℂ] H => T (C x)) hAinv
  have hbackward : ‖C‖ ≤ ‖UA ∘L C ∘L UB‖ := by
    calc
      ‖C‖ = ‖UAinv ∘L (UA ∘L C ∘L UB) ∘L UBinv‖ := by rw [hrecover]
      _ ≤ ‖UAinv‖ * ‖UA ∘L C ∘L UB‖ * ‖UBinv‖ := by
        refine (UAinv.opNorm_comp_le ((UA ∘L C ∘L UB) ∘L UBinv)).trans ?_
        rw [mul_assoc]
        gcongr
        exact (UA ∘L C ∘L UB).opNorm_comp_le UBinv
      _ ≤ 1 * ‖UA ∘L C ∘L UB‖ * 1 := by
        gcongr
        · exact norm_unitaryGroup_le_one A hA (-t)
        · exact norm_unitaryGroup_le_one B hB t
      _ = ‖UA ∘L C ∘L UB‖ := by ring
  exact le_antisymm hforward hbackward

/-- Derivative of the unitary group. -/
theorem hasDerivAt_unitaryGroup (A : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (unitaryGroup A)
      ((Complex.I • A) ∘L unitaryGroup A t) t := by
  exact expBounded_hasDerivAt (Complex.I • A) t

/-- Derivative of the real exponential group. -/
theorem hasDerivAt_semigroup (A : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (semigroup A) (A ∘L semigroup A t) t := by
  exact expBounded_hasDerivAt A t

/-- Elementary norm estimate for the real exponential. -/
theorem norm_semigroup_le_exp_norm (A : H →L[ℂ] H) (t : ℝ) :
    ‖semigroup A t‖ ≤ Real.exp (|t| * ‖A‖) := by
  exact expBounded_norm_bound A t

end Exponentials

section SpectralStepApproximation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A finite spectral resolution of a bounded self-adjoint operator.

The representatives are actual points of the original spectrum.  This is the
feature that preserves any cross-gap when two such resolutions are formed. -/
structure FiniteSpectralStep (A : H →L[ℂ] H)
    (hA : IsSelfAdjointOperator A) where
  n : ℕ
  cell : Fin n → Set ℝ
  measurable_cell : ∀ i, MeasurableSet (cell i)
  pairwise_disjoint : Set.PairwiseDisjoint Set.univ cell
  covers_spectrum : realSpectrum A ⊆ ⋃ i, cell i
  representative : Fin n → ℝ
  representative_mem : ∀ i, representative i ∈ realSpectrum A
  diameter_le : ℝ
  diameter_nonneg : 0 ≤ diameter_le
  cell_close : ∀ i, ∀ x ∈ cell i ∩ realSpectrum A,
    |x - representative i| ≤ diameter_le

/-- Operator represented by a finite spectral step. -/
noncomputable def FiniteSpectralStep.operator
    {A : H →L[ℂ] H} {hA : IsSelfAdjointOperator A}
    (S : FiniteSpectralStep A hA) : H →L[ℂ] H :=
  ∑ i, (S.representative i : ℂ) •
    boundedSelfAdjointSpectralProjection A hA (S.cell i)
      (S.measurable_cell i)

/-- The spectral cells sum to the identity on the spectrum. -/
theorem FiniteSpectralStep.sum_projection_eq_one
    {A : H →L[ℂ] H} {hA : IsSelfAdjointOperator A}
    (S : FiniteSpectralStep A hA) :
    ∑ i, boundedSelfAdjointSpectralProjection A hA (S.cell i)
      (S.measurable_cell i) = 1 :=
  (spectralProjection_finset_sum_eq_id A hA S.cell S.measurable_cell
    S.pairwise_disjoint S.covers_spectrum).trans rfl

/-- A spectral step approximates its generator in operator norm by the cell
radius. -/
theorem FiniteSpectralStep.norm_operator_sub_le
    {A : H →L[ℂ] H} {hA : IsSelfAdjointOperator A}
    (S : FiniteSpectralStep A hA) :
    ‖S.operator - A‖ ≤ S.diameter_le := by
  rcases subsingleton_or_nontrivial H with hsub | hnon
  · -- On a trivial space every operator is zero, so the estimate is `0 ≤ diam`.
    have : S.operator - A = 0 := Subsingleton.elim _ _
    rw [this, norm_zero]
    exact S.diameter_nonneg
  · haveI := hnon
    have hf := measurable_chosenFiniteStepSymbol S.cell S.measurable_cell
      S.pairwise_disjoint S.representative
    have hfb : BoundedOnSpectrum A (chosenFiniteStepSymbol S.cell S.representative) := by
      refine ⟨∑ i, |S.representative i|,
        Finset.sum_nonneg fun i _ => abs_nonneg _, fun x hx => ?_⟩
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (S.covers_spectrum hx)
      have hex : ∃ j, x ∈ S.cell j := ⟨i, hxi⟩
      rw [chosenFiniteStepSymbol, dif_pos hex]
      exact Finset.single_le_sum (fun j _ => abs_nonneg (S.representative j))
        (Finset.mem_univ _)
    have hclose : ∀ x ∈ realSpectrum A,
        |chosenFiniteStepSymbol S.cell S.representative x - x| ≤ S.diameter_le := by
      intro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (S.covers_spectrum hx)
      have hex : ∃ j, x ∈ S.cell j := ⟨i, hxi⟩
      rw [chosenFiniteStepSymbol, dif_pos hex]
      have hxj : x ∈ S.cell (Classical.choose hex) := Classical.choose_spec hex
      have hsame : Classical.choose hex = i := by
        by_contra hne
        exact Set.disjoint_left.mp
          (S.pairwise_disjoint (Set.mem_univ (Classical.choose hex))
            (Set.mem_univ i) hne) hxj hxi
      rw [hsame]
      simpa [abs_sub_comm] using S.cell_close i x ⟨hxi, hx⟩
    have hcalc : S.operator = boundedSelfAdjointBorelCalculus A hA
        (chosenFiniteStepSymbol S.cell S.representative) hf hfb := by
      rw [FiniteSpectralStep.operator]
      exact (boundedSelfAdjointBorelCalculus_eq_finset_sum_indicator A hA S.cell
        S.measurable_cell S.pairwise_disjoint S.representative S.covers_spectrum).symm
    calc
      ‖S.operator - A‖
          = ‖boundedSelfAdjointBorelCalculus A hA
                (chosenFiniteStepSymbol S.cell S.representative) hf hfb -
              boundedSelfAdjointBorelCalculus A hA (fun x => x) measurable_id
                (identity_boundedOnSpectrum A)‖ := by
            rw [hcalc, boundedSelfAdjointBorelCalculus_id A hA]
      _ ≤ S.diameter_le :=
            boundedSelfAdjointBorelCalculus_norm_sub_le A hA hf measurable_id hfb
              (identity_boundedOnSpectrum A) S.diameter_nonneg hclose

/-- Every bounded self-adjoint operator has finite spectral steps with
arbitrarily small cells and representatives in its own spectrum. -/
theorem exists_finiteSpectralStep
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : FiniteSpectralStep A hA, S.diameter_le ≤ ε := by
  classical
  rcases subsingleton_or_nontrivial H with hss | hnt
  · -- Trivial space: the spectrum is empty, so a zero-cell step suffices.
    haveI := hss
    have hempty : realSpectrum A = ∅ := by
      haveI : Subsingleton (H →L[ℂ] H) := ⟨fun a b => by ext x; exact Subsingleton.elim _ _⟩
      ext r
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hr
      have hr' : (r : ℂ) ∈ spectrum ℂ A := hr
      rw [spectrum.mem_iff] at hr'
      exact hr' (isUnit_of_subsingleton _)
    refine ⟨{
      n := 0
      cell := Fin.elim0
      measurable_cell := fun i => i.elim0
      pairwise_disjoint := fun i _ => i.elim0
      covers_spectrum := hempty.subset.trans (Set.empty_subset _)
      representative := Fin.elim0
      representative_mem := fun i => i.elim0
      diameter_le := ε
      diameter_nonneg := le_of_lt hε
      cell_close := fun i => i.elim0 }, le_refl ε⟩
  haveI := hnt
  have hε2 : (0 : ℝ) < ε / 2 := by positivity
  -- The real spectrum is compact (closed and bounded by `‖A‖`).
  have hbdd_mem : ∀ r ∈ realSpectrum A, |r| ≤ ‖A‖ := by
    intro r hr
    have hr' : (r : ℂ) ∈ spectrum ℂ A := hr
    simpa using spectrum.norm_le_norm_of_mem hr'
  have hsub : realSpectrum A ⊆ Set.Icc (-‖A‖) ‖A‖ := by
    intro r hr
    have h := abs_le.mp (hbdd_mem r hr)
    exact ⟨h.1, h.2⟩
  have hclosed : IsClosed (realSpectrum A) := by
    have hpre : realSpectrum A = Complex.ofReal ⁻¹' (spectrum ℂ A) := rfl
    rw [hpre]
    exact (spectrum.isClosed A).preimage Complex.continuous_ofReal
  have hcompact : IsCompact (realSpectrum A) :=
    Metric.isCompact_of_isClosed_isBounded hclosed
      ((Metric.isBounded_Icc _ _).subset hsub)
  -- Finite subcover by `ε/2`-balls centered in the spectrum.
  have hcover : realSpectrum A ⊆ ⋃ p ∈ realSpectrum A, Metric.ball p (ε / 2) := fun r hr =>
    Set.mem_biUnion hr (Metric.mem_ball_self hε2)
  obtain ⟨t, htsub, htfin, htcover⟩ :=
    hcompact.elim_finite_subcover_image (fun p _ => Metric.isOpen_ball) hcover
  -- Enumerate the finite net inside the spectrum.
  let htf : Finset ℝ := htfin.toFinset
  let rep : Fin htf.card → ℝ := fun i => htf.orderEmbOfFin rfl i
  have hrep_mem : ∀ i, rep i ∈ realSpectrum A := by
    intro i
    apply htsub
    rw [← htfin.mem_toFinset]
    exact htf.orderEmbOfFin_mem rfl i
  -- Ball function indexed over `ℕ` for disjointification into measurable cells.
  let f : ℕ → Set ℝ := fun k =>
    if h : k < htf.card then Metric.ball (rep ⟨k, h⟩) (ε / 2) else ∅
  have hfmeas : ∀ k, MeasurableSet (f k) := by
    intro k
    by_cases h : k < htf.card
    · simp only [f, dif_pos h]; exact Metric.isOpen_ball.measurableSet
    · simp only [f, dif_neg h]; exact MeasurableSet.empty
  have hf_i : ∀ i : Fin htf.card, f i.val = Metric.ball (rep i) (ε / 2) := by
    intro i
    simp only [f, dif_pos i.isLt, Fin.eta]
  refine ⟨{
    n := htf.card
    cell := fun i => disjointed f i.val
    measurable_cell := fun i => MeasurableSet.disjointed hfmeas i.val
    pairwise_disjoint := fun i _ j _ hij =>
      disjoint_disjointed f (Fin.val_ne_of_ne hij)
    covers_spectrum := ?_
    representative := rep
    representative_mem := hrep_mem
    diameter_le := ε
    diameter_nonneg := le_of_lt hε
    cell_close := ?_ }, le_refl ε⟩
  · -- Every spectral point lies in a ball, hence in the disjointified cell.
    intro r hr
    obtain ⟨p, hp, hrp⟩ := Set.mem_iUnion₂.mp (htcover hr)
    have hpf : p ∈ htf := htfin.mem_toFinset.mpr hp
    obtain ⟨i, hi⟩ : ∃ i : Fin htf.card, rep i = p := by
      have hmem : p ∈ Set.range (htf.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]; exact hpf
      obtain ⟨i, hi⟩ := hmem
      exact ⟨i, hi⟩
    have hrf : r ∈ f i.val := by rw [hf_i i, hi]; exact hrp
    have hru : r ∈ ⋃ k, f k := Set.mem_iUnion.mpr ⟨i.val, hrf⟩
    rw [← iUnion_disjointed (f := f)] at hru
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hru
    have hkn : k < htf.card := by
      by_contra hc
      have hfk : f k = ∅ := by simp only [f, dif_neg hc]
      have hsub' : disjointed f k ⊆ f k := disjointed_le f k
      rw [hfk] at hsub'
      exact absurd (hsub' hk) (Set.notMem_empty r)
    exact Set.mem_iUnion.mpr ⟨⟨k, hkn⟩, hk⟩
  · -- Each cell sits inside its ball, so points are within `ε/2 ≤ ε` of the rep.
    intro i x hx
    have hxf : x ∈ f i.val := disjointed_le f i.val hx.1
    rw [hf_i i, Metric.mem_ball, Real.dist_eq] at hxf
    exact le_of_lt (lt_of_lt_of_le hxf (by linarith))

/-- The restriction to the full space has the original real spectrum.  Proved by
conjugating the top-restriction through `Submodule.topContEquiv` and invoking
spectral invariance of the induced endomorphism-algebra equivalence. -/
theorem restrictedSpectrum_top_eq_realSpectrum
    (T : H →L[ℂ] H) : restrictedSpectrum T ⊤ = realSpectrum T := by
  have hInv :
      ForMathlib.DavisKahan.Experimental.Foundation.InvariantFor T (⊤ : Submodule ℂ H) :=
    fun x _ => Submodule.mem_top
  have hbridge :=
    ForMathlib.DavisKahan.Experimental.Foundation.restrictedSpectrum_eq_restrictionSpectrum
      T ⊤ hInv
  have hconj :
      (Submodule.topContEquiv : (⊤ : Submodule ℂ H) ≃L[ℂ] H).conjContinuousAlgEquiv
        (T.restrict hInv) = T := by
    ext x
    rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply]
    show ((T.restrict hInv) ((Submodule.topContEquiv :
      (⊤ : Submodule ℂ H) ≃L[ℂ] H).symm x) : H) = T x
    rw [ContinuousLinearMap.coe_restrict_apply]
    rfl
  have hspec : spectrum ℂ (T.restrict hInv) = spectrum ℂ T := by
    conv_rhs => rw [← hconj]
    exact (AlgEquiv.spectrum_eq
      ((Submodule.topContEquiv : (⊤ : Submodule ℂ H) ≃L[ℂ] H).conjContinuousAlgEquiv)
      (T.restrict hInv)).symm
  show ForMathlib.DavisKahan.Experimental.Foundation.restrictedSpectrum T ⊤ =
    ForMathlib.DavisKahan.Experimental.Foundation.realSpectrum T
  rw [hbridge]
  ext r
  simp only [ForMathlib.DavisKahan.Experimental.Foundation.realSpectrum,
    Set.mem_setOf_eq, hspec]

/-- Two finite steps whose representatives come from separated original
spectra inherit exactly the same separation. -/
theorem finiteSpectralStep_representatives_separated
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    {A : H →L[ℂ] H} {B : K →L[ℂ] K}
    {hA : IsSelfAdjointOperator A} {hB : IsSelfAdjointOperator B}
    {d : ℝ} (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (SA : FiniteSpectralStep A hA) (SB : FiniteSpectralStep B hB)
    (i : Fin SA.n) (j : Fin SB.n) :
    d ≤ |SA.representative i - SB.representative j| := by
  -- Transport `SpectraSeparated`'s clause on `restrictedSpectrum _ ⊤` to the
  -- native `realSpectrum`, where the representatives live by construction.
  have hai : SA.representative i ∈ restrictedSpectrum A ⊤ := by
    rw [restrictedSpectrum_top_eq_realSpectrum]; exact SA.representative_mem i
  have hbj : SB.representative j ∈ restrictedSpectrum B ⊤ := by
    rw [restrictedSpectrum_top_eq_realSpectrum]; exact SB.representative_mem j
  exact hsep.2.2 _ hai _ hbj

end SpectralStepApproximation

section FiniteStepReconstruction

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Finite spectral block evaluation of the unitary group. -/
theorem unitaryGroup_finiteSpectralStep
    {A : F →L[ℂ] F} {hA : IsSelfAdjointOperator A}
    (S : FiniteSpectralStep A hA) (t : ℝ) :
    unitaryGroup S.operator t =
      ∑ i, Complex.exp (((t * S.representative i : ℝ) : ℂ) * Complex.I) •
        boundedSelfAdjointSpectralProjection A hA (S.cell i)
          (S.measurable_cell i) := by
  rw [unitaryGroup, expBounded_eq_exp, smul_smul]
  exact unitaryGroup_finiteDiagonal
    (fun i => boundedSelfAdjointSpectralProjection A hA (S.cell i) (S.measurable_cell i))
    S.representative
    (fun i => (boundedSelfAdjointSpectralPVM A hA).proj_idem (S.cell i) (S.measurable_cell i))
    (spectralProjection_pairwise_orthogonal A hA S.cell S.measurable_cell S.pairwise_disjoint)
    S.sum_projection_eq_one t

/-- The reciprocal integral reconstructs a Sylvester solution for finite
spectral steps. -/
theorem finiteSpectralStep_reconstruction
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    {hA : IsSelfAdjointOperator A} {hB : IsSelfAdjointOperator B}
    {d : ℝ} (hd : 0 < d) (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (SA : FiniteSpectralStep A hA) (SB : FiniteSpectralStep B hB)
    (X : E →L[ℂ] F) :
    X = ∫ t : ℝ, separatedSylvesterMultiplier d hd t •
      (unitaryGroup SA.operator t ∘L
        (SA.operator ∘L X - X ∘L SB.operator) ∘L
        unitaryGroup SB.operator (-t)) := by
  have hUA : ∀ s : ℝ, unitaryGroup SA.operator s =
      NormedSpace.exp (((s : ℂ) * Complex.I) • SA.operator) := fun s => by
    rw [unitaryGroup, expBounded_eq_exp, smul_smul]
  have hUB : ∀ s : ℝ, unitaryGroup SB.operator s =
      NormedSpace.exp (((s : ℂ) * Complex.I) • SB.operator) := fun s => by
    rw [unitaryGroup, expBounded_eq_exp, smul_smul]
  have hSAop : SA.operator = finiteDiagonalOperator
      (fun i => boundedSelfAdjointSpectralProjection A hA (SA.cell i) (SA.measurable_cell i))
      SA.representative := rfl
  have hSBop : SB.operator = finiteDiagonalOperator
      (fun j => boundedSelfAdjointSpectralProjection B hB (SB.cell j) (SB.measurable_cell j))
      SB.representative := rfl
  simp only [hUA, hUB]
  simp only [hSAop, hSBop]
  exact finiteDiagonal_sylvester_reconstruction
    (fun i => boundedSelfAdjointSpectralProjection A hA (SA.cell i) (SA.measurable_cell i))
    (fun j => boundedSelfAdjointSpectralProjection B hB (SB.cell j) (SB.measurable_cell j))
    SA.representative SB.representative
    (fun i => (boundedSelfAdjointSpectralPVM A hA).proj_idem (SA.cell i) (SA.measurable_cell i))
    (spectralProjection_pairwise_orthogonal A hA SA.cell SA.measurable_cell SA.pairwise_disjoint)
    SA.sum_projection_eq_one
    (fun j => (boundedSelfAdjointSpectralPVM B hB).proj_idem (SB.cell j) (SB.measurable_cell j))
    (spectralProjection_pairwise_orthogonal B hB SB.cell SB.measurable_cell SB.pairwise_disjoint)
    SB.sum_projection_eq_one
    (separatedSylvesterMultiplier d hd)
    (integrable_separatedSylvesterMultiplier d hd)
    (fun i j => separatedSylvesterMultiplier_identity d hd
      (SA.representative i) (SB.representative j)
      (finiteSpectralStep_representatives_separated hsep SA SB i j))
    (fun i j => abs_pos.mp
      (lt_of_lt_of_le hd (finiteSpectralStep_representatives_separated hsep SA SB i j)))
    X

end FiniteStepReconstruction

section LimitReconstruction

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- Pointwise norm continuity of the two-sided unitary orbit in all three
operator arguments. -/
theorem tendsto_unitary_orbit
    {A : ℕ → F →L[ℂ] F} {B : ℕ → E →L[ℂ] E}
    {C : ℕ → E →L[ℂ] F} {A0 : F →L[ℂ] F} {B0 : E →L[ℂ] E}
    {C0 : E →L[ℂ] F}
    (hA : Tendsto A atTop (nhds A0))
    (hB : Tendsto B atTop (nhds B0))
    (hC : Tendsto C atTop (nhds C0)) (t : ℝ) :
    Tendsto (fun n => unitaryGroup (A n) t ∘L C n ∘L unitaryGroup (B n) (-t))
      atTop (nhds (unitaryGroup A0 t ∘L C0 ∘L unitaryGroup B0 (-t))) := by
  -- `unitaryGroup A t = exp ((t·i)·A)` is continuous in the generator `A`.
  have hUAn : Tendsto (fun n => unitaryGroup (A n) t)
      atTop (nhds (unitaryGroup A0 t)) := by
    have hgen : Tendsto (fun n => ((t : ℂ) • (Complex.I • A n)))
        atTop (nhds ((t : ℂ) • (Complex.I • A0))) :=
      (((continuous_const_smul (t : ℂ)).comp
        (continuous_const_smul Complex.I)).tendsto A0).comp hA
    simp only [unitaryGroup, expBounded_eq_exp]
    exact (NormedSpace.exp_continuous.tendsto _).comp hgen
  have hUBn : Tendsto (fun n => unitaryGroup (B n) (-t))
      atTop (nhds (unitaryGroup B0 (-t))) := by
    have hgen : Tendsto (fun n => (((-t : ℝ) : ℂ) • (Complex.I • B n)))
        atTop (nhds (((-t : ℝ) : ℂ) • (Complex.I • B0))) :=
      (((continuous_const_smul ((-t : ℝ) : ℂ)).comp
        (continuous_const_smul Complex.I)).tendsto B0).comp hB
    simp only [unitaryGroup, expBounded_eq_exp]
    exact (NormedSpace.exp_continuous.tendsto _).comp hgen
  -- Joint continuity of the two-sided composition in all three arguments.
  have hΦ : Continuous (fun p : (F →L[ℂ] F) × (E →L[ℂ] F) × (E →L[ℂ] E) =>
      p.1 ∘L p.2.1 ∘L p.2.2) :=
    continuous_fst.clm_comp
      ((continuous_fst.comp continuous_snd).clm_comp
        (continuous_snd.comp continuous_snd))
  have htriple :
      Tendsto (fun n => (unitaryGroup (A n) t, C n, unitaryGroup (B n) (-t)))
        atTop (nhds (unitaryGroup A0 t, C0, unitaryGroup B0 (-t))) :=
    hUAn.prodMk_nhds (hC.prodMk_nhds hUBn)
  exact (hΦ.tendsto _).comp htriple

/-- Exact separated-spectrum reconstruction on complex Hilbert spaces. -/
theorem separatedSylvester_reconstruction_complex
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d) (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (X C : E →L[ℂ] F)
    (hEq : A ∘L X - X ∘L B = C) :
    X = ∫ t : ℝ, separatedSylvesterMultiplier d hd t •
      (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t)) := by
  -- Open obligation: the dominated-convergence limit passing the finite
  -- spectral-step reconstruction to the general operator.  Depends on
  -- `finiteSpectralStep_reconstruction`, `exists_finiteSpectralStep`,
  -- `FiniteSpectralStep.norm_operator_sub_le`, `norm_bounded_of_tendsto`, and
  -- `FiniteSpectralStep.operator_isSelfAdjoint`, handed to the mathematics
  -- agent.  The uniform bound is `‖μ_d‖_{L¹} · ‖C‖` from the (proved)
  -- `l1_norm_separatedSylvesterMultiplier`.
  sorry

/-- The integral in the separated reconstruction is integrable. -/
theorem separatedSylvester_integrable_complex
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d) (C : E →L[ℂ] F) :
    Integrable fun t : ℝ => separatedSylvesterMultiplier d hd t •
      (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t)) := by
  have hcontA : Continuous (unitaryGroup A) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_unitaryGroup A t).continuousAt
  have hcontB : Continuous (unitaryGroup B) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_unitaryGroup B t).continuousAt
  have hUBneg : Continuous (fun t : ℝ => unitaryGroup B (-t)) :=
    hcontB.comp continuous_neg
  have horbit : Continuous
      (fun t : ℝ => unitaryGroup A t ∘L C ∘L unitaryGroup B (-t)) :=
    hcontA.clm_comp (continuous_const.clm_comp hUBneg)
  have hμ : AEStronglyMeasurable (separatedSylvesterMultiplier d hd) volume :=
    (integrable_separatedSylvesterMultiplier d hd).aestronglyMeasurable
  have hmajor : Integrable (fun t : ℝ => ‖separatedSylvesterMultiplier d hd t‖ * ‖C‖) :=
    (integrable_separatedSylvesterMultiplier d hd).norm.mul_const ‖C‖
  -- Dominate the operator-valued integrand by the integrable scalar majorant
  -- `‖μ_d(t)‖ · ‖C‖`; the orbit norm is exactly `‖C‖` by two-sided unitarity.
  refine hmajor.mono' (hμ.smul horbit.aestronglyMeasurable) ?_
  filter_upwards with t
  refine le_of_eq ?_
  rw [norm_smul, norm_unitary_left_right A hA B hB t C]


/-- The reciprocal integral is a right inverse of the Sylvester operator.

The proof uses the same finite spectral steps as the reconstruction theorem.
For each step pair the assertion is the scalar Fourier identity on every
spectral rectangle.  The step generators converge in operator norm, their
unitary orbits converge pointwise, and the reciprocal kernel supplies an
integrable dominating function. -/
theorem spectral_step_integral_right_inverse
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d) (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (C : E →L[ℂ] F) :
    A ∘L (∫ t : ℝ, separatedSylvesterMultiplier d hd t •
      (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t))) -
      (∫ t : ℝ, separatedSylvesterMultiplier d hd t •
        (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t))) ∘L B = C := by
  -- Open obligation: the right-inverse form of the reconstruction, proved by
  -- the same finite spectral-step limit (`finiteSpectralStep_reconstruction`
  -- transported to `sylvesterOperator`, `integral_finset_sylvester_blocks`,
  -- dominated convergence), handed to the mathematics agent.  The scalar
  -- premise on each spectral rectangle is `separatedSylvesterMultiplier_identity`.
  sorry


/-- Spectral-multiplier extensionality for the reciprocal kernel.

The proof is the finite-spectral-step argument above: equality is checked on
all spectral rectangles and then passed to norm limits.  The final scalar
premise is exposed so callers can localize any normalization or sign error to
the one-dimensional Fourier identity. -/
theorem spectralMultiplier_ext
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} {hd : 0 < d}
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    {C : E →L[ℂ] F}
    (hscalar : ∀ a ∈ realSpectrum A, ∀ b ∈ realSpectrum B,
      (∫ t : ℝ, separatedSylvesterMultiplier d hd t *
        Complex.exp ((((t * (a - b) : ℝ) : ℂ) * Complex.I))) =
        (((a - b)⁻¹ : ℝ) : ℂ)) :
    A ∘L (∫ t : ℝ, separatedSylvesterMultiplier d hd t •
      (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t))) -
      (∫ t : ℝ, separatedSylvesterMultiplier d hd t •
        (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t))) ∘L B = C := by
  have hcanonical : ∀ a ∈ realSpectrum A, ∀ b ∈ realSpectrum B,
      (∫ t : ℝ, separatedSylvesterMultiplier d hd t *
        Complex.exp ((((t * (a - b) : ℝ) : ℂ) * Complex.I))) =
        (((a - b)⁻¹ : ℝ) : ℂ) := by
    intro a ha b hb
    exact hscalar a ha b hb
  exact spectral_step_integral_right_inverse hA hB hd hsep C

end LimitReconstruction

end

end DavisKahanExt
end ForMathlib
