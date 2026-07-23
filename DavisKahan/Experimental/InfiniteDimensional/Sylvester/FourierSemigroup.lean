/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.SpectralProjection
import ForMathlib.Analysis.Fourier.HaagerupZsidoKernel
import Spectra.YosidaHille.Approximation.ExpBounded.Unitary
import Spectra.CayleyTransform.BorelCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Topology.MetricSpace.ProperSpace.Real

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
  simpa [separatedSylvesterMultiplier, mul_comm] using
    hbase.comp_mul_left hd0

/-- Exact Fourier identity for the scaled reciprocal kernel. -/
theorem separatedSylvesterMultiplier_identity
    (d : ℝ) (hd : 0 < d) (a b : ℝ) (hab : d ≤ |a - b|) :
    (∫ t : ℝ, separatedSylvesterMultiplier d hd t *
      Complex.exp ((((t * (a - b) : ℝ) : ℂ) * Complex.I))) =
      (((a - b)⁻¹ : ℝ) : ℂ) := by
  let x : ℝ := (a - b) / d
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hx : 1 ≤ |x| := by
    rw [x, abs_div, abs_of_pos hd]
    exact (le_div_iff₀ hd).2 hab
  have hfourier := HaagerupZsido.reciprocalKernel_fourier x hx
  let g : ℝ → ℂ := fun s =>
    HaagerupZsido.reciprocalKernel s *
      Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)
  have hgint : Integrable g := by
    refine HaagerupZsido.integrable_reciprocalKernel.norm.mul_const ?_
    intro s
    rw [Complex.norm_exp]
    simp
  have hchange := MeasureTheory.Measure.integral_comp_mul_left g d
  have hpoint : (fun t : ℝ => g (d * t)) =
      fun t : ℝ => separatedSylvesterMultiplier d hd t *
        Complex.exp ((((t * (a - b) : ℝ) : ℂ) * Complex.I)) := by
    funext t
    dsimp [g, separatedSylvesterMultiplier, x]
    congr 2
    congr 1
    push_cast
    field_simp [hd0]
    ring
  have hscale :
      (∫ t : ℝ, g (d * t)) = d⁻¹ • ∫ s : ℝ, g s := by
    simpa [Real.norm_eq_abs, abs_of_pos hd, one_div] using hchange
  rw [← hpoint, hscale, hfourier]
  have hab0 : a - b ≠ 0 := by
    have : 0 < |a - b| := lt_of_lt_of_le hd hab
    exact sub_ne_zero.mp (abs_pos.mp this)
  apply Complex.ext
  · simp [x, hd0, hab0]
    field_simp [hd0, hab0]
  · simp

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
      ring

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
  exact smul_I_skewSelfAdjoint A hA.adjoint_eq

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
  exact (unitaryGroup_mem_unitary A hA t).norm_le_one

/-- On a nonzero Hilbert space every unitary group element has norm one. -/
theorem norm_unitaryGroup [Nontrivial H] (A : H →L[ℂ] H)
    (hA : IsSelfAdjointOperator A) (t : ℝ) :
    ‖unitaryGroup A t‖ = 1 := by
  exact (unitaryGroup_mem_unitary A hA t).norm_eq_one

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
      ‖UA ∘L C ∘L UB‖ ≤ ‖UA‖ * ‖C‖ * ‖UB‖ :=
        ContinuousLinearMap.opNorm_comp_comp_le UA C UB
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
    rw [← hrecover]
    calc
      ‖UAinv ∘L (UA ∘L C ∘L UB) ∘L UBinv‖
          ≤ ‖UAinv‖ * ‖UA ∘L C ∘L UB‖ * ‖UBinv‖ :=
        ContinuousLinearMap.opNorm_comp_comp_le UAinv (UA ∘L C ∘L UB) UBinv
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
      (S.measurable_cell i) = 1 := by
  let P := boundedSelfAdjointSpectralPVM A hA
  have hdisj : Set.PairwiseDisjoint Set.univ S.cell := S.pairwise_disjoint
  have hunion : P.proj (⋃ i, S.cell i) (MeasurableSet.iUnion S.measurable_cell) = 1 := by
    have hres : realSpectrum A ⊆ ⋃ i, S.cell i := S.covers_spectrum
    rw [boundedSelfAdjointSpectralProjection, ← P.proj_univ]
    apply P.proj_congr
    exact spectralPVM_proj_congr_of_inter_spectrum_eq P
      (by ext x; simp [hres])
  rw [← hunion]
  exact P.proj_iUnion_finite S.measurable_cell hdisj

/-- A spectral step approximates its generator in operator norm by the cell
radius. -/
theorem FiniteSpectralStep.norm_operator_sub_le
    {A : H →L[ℂ] H} {hA : IsSelfAdjointOperator A}
    (S : FiniteSpectralStep A hA) :
    ‖S.operator - A‖ ≤ S.diameter_le := by
  let q : ℝ → ℝ := fun x =>
    if hx : ∃ i, x ∈ S.cell i then
      S.representative (Classical.choose hx)
    else x
  have hq_meas : Measurable q := by
    apply measurable_piecewise_finite_partition
    exact S.measurable_cell
  have hq_close : ∀ x ∈ realSpectrum A, |q x - x| ≤ S.diameter_le := by
    intro x hx
    have hcover : x ∈ ⋃ i, S.cell i := S.covers_spectrum hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hcover
    have hex : ∃ j, x ∈ S.cell j := ⟨i, hxi⟩
    rw [q, dif_pos hex]
    let j := Classical.choose hex
    have hxj := Classical.choose_spec hex
    have hsame : j = i := by
      apply S.pairwise_disjoint.elim hxi hxj
    subst j
    simpa [abs_sub_comm] using S.cell_close i x ⟨hxi, hx⟩
  have hcalc : S.operator = boundedSelfAdjointBorelCalculus A hA q hq_meas := by
    rw [FiniteSpectralStep.operator]
    exact boundedSelfAdjointBorelCalculus_eq_finset_sum_indicator
      A hA S.cell S.measurable_cell S.pairwise_disjoint
      S.representative S.covers_spectrum
  rw [hcalc, ← boundedSelfAdjointBorelCalculus_id A hA]
  exact boundedSelfAdjointBorelCalculus_norm_sub_le hq_meas measurable_id hq_close

/-- Every bounded self-adjoint operator has finite spectral steps with
arbitrarily small cells and representatives in its own spectrum. -/
theorem exists_finiteSpectralStep
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : FiniteSpectralStep A hA, S.diameter_le ≤ ε := by
  have hcompact : IsCompact (realSpectrum A) :=
    realSpectrum_isCompact A hA
  obtain ⟨centers, hcenters, hcover⟩ :=
    hcompact.exists_finset_ball_cover hε
  let active := centers.filter fun c => Metric.ball c ε ∩ realSpectrum A |>.Nonempty
  have hactive : ∀ c ∈ active, c ∈ realSpectrum A := by
    intro c hc
    obtain ⟨x, hxball, hxsigma⟩ := (Finset.mem_filter.mp hc).2
    exact choose_spectrum_point_in_ball hxsigma hxball
  let ordered : Fin active.card → ℝ := active.orderIsoFin.symm
  let cell : Fin active.card → Set ℝ := fun i =>
    Metric.ball (ordered i) ε \
      ⋃ j : Fin active.card, j < i, Metric.ball (ordered j) ε
  have hmeas : ∀ i, MeasurableSet (cell i) := by
    intro i
    exact measurableSet_ball.diff (MeasurableSet.iUnion fun j =>
      MeasurableSet.iUnion fun _ => measurableSet_ball)
  have hpair : Set.PairwiseDisjoint Set.univ cell := by
    exact pairwiseDisjoint_successiveDifference ordered
  have hcov : realSpectrum A ⊆ ⋃ i, cell i := by
    exact successiveDifference_covers_of_finset_ball_cover
      hcompact active ordered hcover
  refine ⟨{
    n := active.card
    cell := cell
    measurable_cell := hmeas
    pairwise_disjoint := hpair
    covers_spectrum := hcov
    representative := fun i => Classical.choose
      (active_ball_meets_spectrum active ordered i)
    representative_mem := fun i =>
      (Classical.choose_spec (active_ball_meets_spectrum active ordered i)).2
    diameter_le := 2 * ε
    diameter_nonneg := by positivity
    cell_close := ?_ }, by linarith⟩
  intro i x hx
  have hxball : x ∈ Metric.ball (ordered i) ε := hx.1.1
  have hrball :=
    (Classical.choose_spec (active_ball_meets_spectrum active ordered i)).1
  rw [Real.dist_eq] at hxball hrball
  exact (abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩)

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
  exact hsep _ (SA.representative_mem i) _ (SB.representative_mem j)

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
  rw [unitaryGroup, expBounded_eq_exp]
  exact exp_finset_orthogonal_idempotents
    (fun i => boundedSelfAdjointSpectralProjection A hA (S.cell i)
      (S.measurable_cell i))
    (fun i => (S.representative i : ℂ))
    (spectralProjection_pairwise_orthogonal S.pairwise_disjoint)
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
  let PA : Fin SA.n → F →L[ℂ] F := fun i =>
    boundedSelfAdjointSpectralProjection A hA (SA.cell i) (SA.measurable_cell i)
  let PB : Fin SB.n → E →L[ℂ] E := fun j =>
    boundedSelfAdjointSpectralProjection B hB (SB.cell j) (SB.measurable_cell j)
  have hblock (i : Fin SA.n) (j : Fin SB.n) :
      PA i ∘L (SA.operator ∘L X - X ∘L SB.operator) ∘L PB j =
        ((SA.representative i - SB.representative j : ℝ) : ℂ) •
          (PA i ∘L X ∘L PB j) := by
    rw [FiniteSpectralStep.operator, FiniteSpectralStep.operator]
    simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.comp_finset_sum, ContinuousLinearMap.finset_sum_comp,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
    rw [spectralProjection_select_left PA SA.pairwise_disjoint i,
      spectralProjection_select_right PB SB.pairwise_disjoint j]
    module
  have horbit (t : ℝ) :
      unitaryGroup SA.operator t ∘L
          (SA.operator ∘L X - X ∘L SB.operator) ∘L
          unitaryGroup SB.operator (-t) =
        ∑ i, ∑ j,
          Complex.exp ((((t * (SA.representative i - SB.representative j) : ℝ) : ℂ) *
            Complex.I)) •
            (((SA.representative i - SB.representative j : ℝ) : ℂ) •
              (PA i ∘L X ∘L PB j)) := by
    rw [unitaryGroup_finiteSpectralStep SA t,
      unitaryGroup_finiteSpectralStep SB (-t)]
    simp only [ContinuousLinearMap.finset_sum_comp,
      ContinuousLinearMap.comp_finset_sum, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul, hblock, smul_smul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [show (fun t => separatedSylvesterMultiplier d hd t •
      (unitaryGroup SA.operator t ∘L
        (SA.operator ∘L X - X ∘L SB.operator) ∘L
        unitaryGroup SB.operator (-t))) =
      fun t => separatedSylvesterMultiplier d hd t •
        (∑ i, ∑ j,
          Complex.exp ((((t * (SA.representative i - SB.representative j) : ℝ) : ℂ) *
            Complex.I)) •
            (((SA.representative i - SB.representative j : ℝ) : ℂ) •
              (PA i ∘L X ∘L PB j))) by funext t; rw [horbit t]]
  rw [integral_finset_sum, integral_finset_sum]
  have hscalar (i : Fin SA.n) (j : Fin SB.n) :
      (∫ t : ℝ, separatedSylvesterMultiplier d hd t *
        Complex.exp ((((t * (SA.representative i - SB.representative j) : ℝ) : ℂ) *
          Complex.I))) *
        ((SA.representative i - SB.representative j : ℝ) : ℂ) = 1 := by
    have hij := finiteSpectralStep_representatives_separated hsep SA SB i j
    rw [separatedSylvesterMultiplier_identity d hd _ _ hij]
    have hne : SA.representative i - SB.representative j ≠ 0 := by
      have : 0 < |SA.representative i - SB.representative j| :=
        lt_of_lt_of_le hd hij
      exact sub_ne_zero.mp (abs_pos.mp this)
    norm_cast
    exact inv_mul_cancel₀ hne
  calc
    (∫ t : ℝ, separatedSylvesterMultiplier d hd t •
        (∑ i, ∑ j,
          Complex.exp ((((t * (SA.representative i - SB.representative j) : ℝ) : ℂ) *
            Complex.I)) •
            (((SA.representative i - SB.representative j : ℝ) : ℂ) •
              (PA i ∘L X ∘L PB j)))) =
      ∑ i, ∑ j, PA i ∘L X ∘L PB j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [← integral_smul_const]
        simp only [smul_smul]
        rw [hscalar i j, one_smul]
    _ = (∑ i, PA i) ∘L X ∘L (∑ j, PB j) := by
      simp [ContinuousLinearMap.finset_sum_comp,
        ContinuousLinearMap.comp_finset_sum]
    _ = X := by
      rw [SA.sum_projection_eq_one, SB.sum_projection_eq_one]
      simp

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
  have hUA : Tendsto (fun n => unitaryGroup (A n) t) atTop
      (nhds (unitaryGroup A0 t)) := by
    exact tendsto_expBounded_of_tendsto hA t
  have hUB : Tendsto (fun n => unitaryGroup (B n) (-t)) atTop
      (nhds (unitaryGroup B0 (-t))) := by
    exact tendsto_expBounded_of_tendsto hB (-t)
  exact (hUA.comp hC).comp hUB

/-- Exact separated-spectrum reconstruction on complex Hilbert spaces. -/
theorem separatedSylvester_reconstruction_complex
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d) (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (X C : E →L[ℂ] F)
    (hEq : A ∘L X - X ∘L B = C) :
    X = ∫ t : ℝ, separatedSylvesterMultiplier d hd t •
      (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t)) := by
  choose SA hSA using fun n : ℕ =>
    exists_finiteSpectralStep A hA (show 0 < (n + 1 : ℝ)⁻¹ by positivity)
  choose SB hSB using fun n : ℕ =>
    exists_finiteSpectralStep B hB (show 0 < (n + 1 : ℝ)⁻¹ by positivity)
  let An : ℕ → F →L[ℂ] F := fun n => (SA n).operator
  let Bn : ℕ → E →L[ℂ] E := fun n => (SB n).operator
  let Cn : ℕ → E →L[ℂ] F := fun n => An n ∘L X - X ∘L Bn n
  have hAn : Tendsto An atTop (nhds A) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun n hn => ?_⟩
    calc
      dist (An n) A = ‖(SA n).operator - A‖ := dist_eq_norm _ _
      _ ≤ (SA n).diameter_le := (SA n).norm_operator_sub_le
      _ ≤ (n + 1 : ℝ)⁻¹ := hSA n
      _ ≤ (N + 1 : ℝ)⁻¹ := by
        exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
      _ < ε := hN
  have hBn : Tendsto Bn atTop (nhds B) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun n hn => ?_⟩
    calc
      dist (Bn n) B = ‖(SB n).operator - B‖ := dist_eq_norm _ _
      _ ≤ (SB n).diameter_le := (SB n).norm_operator_sub_le
      _ ≤ (n + 1 : ℝ)⁻¹ := hSB n
      _ ≤ (N + 1 : ℝ)⁻¹ := by
        exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
      _ < ε := hN
  have hCn : Tendsto Cn atTop (nhds C) := by
    have hleft : Tendsto (fun n => An n ∘L X) atTop (nhds (A ∘L X)) :=
      continuous_comp_right.tendsto A |>.comp hAn
    have hright : Tendsto (fun n => X ∘L Bn n) atTop (nhds (X ∘L B)) :=
      continuous_comp_left.tendsto B |>.comp hBn
    simpa [Cn, hEq] using hleft.sub hright
  have hfinite (n : ℕ) :
      X = ∫ t : ℝ, separatedSylvesterMultiplier d hd t •
        (unitaryGroup (An n) t ∘L Cn n ∘L unitaryGroup (Bn n) (-t)) := by
    exact finiteSpectralStep_reconstruction hd hsep (SA n) (SB n) X
  have hboundC : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖Cn n‖ ≤ M := by
    exact norm_bounded_of_tendsto hCn
  obtain ⟨M, hM0, hM⟩ := hboundC
  let majorant : ℝ → ℝ := fun t =>
    ‖separatedSylvesterMultiplier d hd t‖ * M
  have hmajorant : Integrable majorant := by
    exact (integrable_separatedSylvesterMultiplier d hd).norm.const_mul M
  have hpoint (t : ℝ) : Tendsto
      (fun n => separatedSylvesterMultiplier d hd t •
        (unitaryGroup (An n) t ∘L Cn n ∘L unitaryGroup (Bn n) (-t)))
      atTop
      (nhds (separatedSylvesterMultiplier d hd t •
        (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t)))) := by
    exact tendsto_const_nhds.smul (tendsto_unitary_orbit hAn hBn hCn t)
  have hdom (n : ℕ) : ∀ᵐ t : ℝ ∂volume,
      ‖separatedSylvesterMultiplier d hd t •
        (unitaryGroup (An n) t ∘L Cn n ∘L unitaryGroup (Bn n) (-t))‖ ≤
        majorant t := by
    filter_upwards [] with t
    rw [norm_smul]
    calc
      ‖separatedSylvesterMultiplier d hd t‖ *
          ‖unitaryGroup (An n) t ∘L Cn n ∘L unitaryGroup (Bn n) (-t)‖
        ≤ ‖separatedSylvesterMultiplier d hd t‖ * ‖Cn n‖ := by
          gcongr
          calc
            ‖unitaryGroup (An n) t ∘L Cn n ∘L unitaryGroup (Bn n) (-t)‖
              ≤ ‖unitaryGroup (An n) t‖ * ‖Cn n‖ * ‖unitaryGroup (Bn n) (-t)‖ :=
                ContinuousLinearMap.opNorm_comp_comp_le _ _ _
            _ ≤ 1 * ‖Cn n‖ * 1 := by
              gcongr
              · exact norm_unitaryGroup_le_one _
                  (FiniteSpectralStep.operator_isSelfAdjoint (SA n)) _
              · exact norm_unitaryGroup_le_one _
                  (FiniteSpectralStep.operator_isSelfAdjoint (SB n)) _
            _ = ‖Cn n‖ := by ring
      _ ≤ ‖separatedSylvesterMultiplier d hd t‖ * M :=
        mul_le_mul_of_nonneg_left (hM n) (norm_nonneg _)
  have hlim :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      hmajorant hdom (fun t => (hpoint t).ae)
  have : Tendsto (fun _n : ℕ => X) atTop
      (nhds (∫ t : ℝ, separatedSylvesterMultiplier d hd t •
        (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t)))) := by
    simpa only [hfinite] using hlim
  exact tendsto_nhds_unique tendsto_const_nhds this

/-- The integral in the separated reconstruction is integrable. -/
theorem separatedSylvester_integrable_complex
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d) (C : E →L[ℂ] F) :
    Integrable fun t : ℝ => separatedSylvesterMultiplier d hd t •
      (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t)) := by
  apply Integrable.mono' ((integrable_separatedSylvesterMultiplier d hd).norm.const_mul ‖C‖)
  · exact (continuous_unitary_orbit A B C).stronglyMeasurable.smul
      (measurable_separatedSylvesterMultiplier d hd).stronglyMeasurable
  · filter_upwards [] with t
    rw [norm_smul, norm_unitary_left_right A hA B hB t C]
    rfl


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
  choose SA hSA using fun n : ℕ =>
    exists_finiteSpectralStep A hA (show 0 < (n + 1 : ℝ)⁻¹ by positivity)
  choose SB hSB using fun n : ℕ =>
    exists_finiteSpectralStep B hB (show 0 < (n + 1 : ℝ)⁻¹ by positivity)
  let An : ℕ → F →L[ℂ] F := fun n => (SA n).operator
  let Bn : ℕ → E →L[ℂ] E := fun n => (SB n).operator
  let Yn : ℕ → E →L[ℂ] F := fun n =>
    ∫ t : ℝ, separatedSylvesterMultiplier d hd t •
      (unitaryGroup (An n) t ∘L C ∘L unitaryGroup (Bn n) (-t))
  let Y : E →L[ℂ] F :=
    ∫ t : ℝ, separatedSylvesterMultiplier d hd t •
      (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t))
  have hAn : Tendsto An atTop (nhds A) := by
    rw [Metric.tendsto_atTop]
    intro eps heps
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt heps
    refine ⟨N, fun n hn => ?_⟩
    calc
      dist (An n) A = ‖(SA n).operator - A‖ := dist_eq_norm _ _
      _ ≤ (SA n).diameter_le := (SA n).norm_operator_sub_le
      _ ≤ (n + 1 : ℝ)⁻¹ := hSA n
      _ ≤ (N + 1 : ℝ)⁻¹ := by
        exact inv_anti₀ (by positivity)
          (by exact_mod_cast Nat.add_le_add_right hn 1)
      _ < eps := hN
  have hBn : Tendsto Bn atTop (nhds B) := by
    rw [Metric.tendsto_atTop]
    intro eps heps
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt heps
    refine ⟨N, fun n hn => ?_⟩
    calc
      dist (Bn n) B = ‖(SB n).operator - B‖ := dist_eq_norm _ _
      _ ≤ (SB n).diameter_le := (SB n).norm_operator_sub_le
      _ ≤ (n + 1 : ℝ)⁻¹ := hSB n
      _ ≤ (N + 1 : ℝ)⁻¹ := by
        exact inv_anti₀ (by positivity)
          (by exact_mod_cast Nat.add_le_add_right hn 1)
      _ < eps := hN
  have hYn : Tendsto Yn atTop (nhds Y) := by
    have hmajor : Integrable fun t : ℝ =>
        ‖separatedSylvesterMultiplier d hd t‖ * ‖C‖ :=
      (integrable_separatedSylvesterMultiplier d hd).norm.const_mul ‖C‖
    have hdom (n : ℕ) : ∀ᵐ t : ℝ ∂volume,
        ‖separatedSylvesterMultiplier d hd t •
          (unitaryGroup (An n) t ∘L C ∘L unitaryGroup (Bn n) (-t))‖ ≤
          ‖separatedSylvesterMultiplier d hd t‖ * ‖C‖ := by
      filter_upwards [] with t
      rw [norm_smul]
      gcongr
      calc
        ‖unitaryGroup (An n) t ∘L C ∘L unitaryGroup (Bn n) (-t)‖
            ≤ ‖C‖ := by
          calc
            _ ≤ ‖unitaryGroup (An n) t‖ * ‖C‖ *
                ‖unitaryGroup (Bn n) (-t)‖ :=
              ContinuousLinearMap.opNorm_comp_comp_le _ _ _
            _ ≤ 1 * ‖C‖ * 1 := by
              gcongr
              · exact norm_unitaryGroup_le_one _
                  (FiniteSpectralStep.operator_isSelfAdjoint (SA n)) _
              · exact norm_unitaryGroup_le_one _
                  (FiniteSpectralStep.operator_isSelfAdjoint (SB n)) _
            _ = ‖C‖ := by ring
    have hpoint (t : ℝ) : Tendsto
        (fun n => separatedSylvesterMultiplier d hd t •
          (unitaryGroup (An n) t ∘L C ∘L unitaryGroup (Bn n) (-t)))
        atTop
        (nhds (separatedSylvesterMultiplier d hd t •
          (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t)))) := by
      exact tendsto_const_nhds.smul
        (tendsto_unitary_orbit hAn hBn tendsto_const_nhds t)
    simpa [Yn, Y] using
      MeasureTheory.tendsto_integral_of_dominated_convergence
        hmajor hdom (fun t => (hpoint t).ae)
  have hfinite (n : ℕ) : An n ∘L Yn n - Yn n ∘L Bn n = C := by
    let PA : Fin (SA n).n → F →L[ℂ] F := fun i =>
      boundedSelfAdjointSpectralProjection A hA ((SA n).cell i)
        ((SA n).measurable_cell i)
    let PB : Fin (SB n).n → E →L[ℂ] E := fun j =>
      boundedSelfAdjointSpectralProjection B hB ((SB n).cell j)
        ((SB n).measurable_cell j)
    have hCblocks : C = ∑ i, ∑ j, PA i ∘L C ∘L PB j := by
      calc
        C = (∑ i, PA i) ∘L C ∘L (∑ j, PB j) := by
          rw [(SA n).sum_projection_eq_one, (SB n).sum_projection_eq_one]
          simp
        _ = ∑ i, ∑ j, PA i ∘L C ∘L PB j := by
          simp [ContinuousLinearMap.finset_sum_comp,
            ContinuousLinearMap.comp_finset_sum]
    have hscalar (i : Fin (SA n).n) (j : Fin (SB n).n) :
        (((SA n).representative i - (SB n).representative j : ℝ) : ℂ) *
          (∫ t : ℝ, separatedSylvesterMultiplier d hd t *
            Complex.exp ((((t * ((SA n).representative i -
              (SB n).representative j) : ℝ) : ℂ) * Complex.I))) = 1 := by
      have hij := finiteSpectralStep_representatives_separated
        hsep (SA n) (SB n) i j
      rw [separatedSylvesterMultiplier_identity d hd _ _ hij]
      have hne : (SA n).representative i - (SB n).representative j ≠ 0 := by
        have hpos : 0 < |(SA n).representative i - (SB n).representative j| :=
          lt_of_lt_of_le hd hij
        exact sub_ne_zero.mp (abs_pos.mp hpos)
      norm_cast
      exact mul_inv_cancel₀ hne
    rw [Yn]
    rw [integral_finset_sylvester_blocks
      (SA n) (SB n) C hd hsep hscalar]
    exact hCblocks.symm
  have hdefect : Tendsto (fun n => An n ∘L Yn n - Yn n ∘L Bn n)
      atTop (nhds (A ∘L Y - Y ∘L B)) := by
    exact ((continuous_comp.tendsto (A, Y)).comp (hAn.prodMk hYn)).sub
      ((continuous_comp.tendsto (Y, B)).comp (hYn.prodMk hBn))
  have hconst : Tendsto (fun _n : ℕ => C) atTop (nhds C) := tendsto_const_nhds
  have hsame : (fun n => An n ∘L Yn n - Yn n ∘L Bn n) = fun _n : ℕ => C := by
    funext n
    exact hfinite n
  rw [hsame] at hdefect
  exact tendsto_nhds_unique hdefect hconst


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

end DavisKahanExt
end ForMathlib
