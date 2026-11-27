/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralMeasure.Construction

/-!
# The spectral measure of an unbounded self-adjoint operator: bounded sets

For bounded Borel sets, the accepted spectral-cut graph and norm laws
control the domain and action on the spectral range. This module supplies
the remaining spectral-cut and exhaustion results used by the Davis--Kahan
arguments.

The bounded-set results were split from the original spectral-measure file
on 2026-07-29. See `SpectralMeasure/Construction.lean` for the Cayley-transform
and Spectra provenance. The separate restricted-resolvent proof was retired
when the Davis--Kahan localization theorem moved to the accepted Tau Ceti
gap-resolvent API.
-/

public section

open scoped InnerProductSpace
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section BoundedSet

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

include hA in
/-- Off the Cayley singularity, `κ(w) + i = 2i/(1 - w)`. -/
theorem cayleyInv_add_I {w : _root_.spectrum ℂ (A.cayley)} (hw1 : (w : ℂ) ≠ 1) :
    ((cayleyInv A w : ℝ) : ℂ) + Complex.I = (2 * Complex.I) / (1 - (w : ℂ)) := by
  have hnorm : ‖(w : ℂ)‖ = 1 :=
    spectrum.norm_eq_one_of_unitary (hA.cayley_mem_unitary) w.property
  have hd : (1 : ℂ) - (w : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hcast : ((cayleyInv A w : ℝ) : ℂ) = Complex.I * (1 + (w : ℂ)) / (1 - (w : ℂ)) :=
    Complex.ext (by simp [cayleyInv_def])
      (by simpa using (inverseCayley_im_eq_zero hnorm hw1).symm)
  rw [hcast]
  field_simp
  ring

include hA in
/-- **The Cayley symbol and `κ + i` are reciprocal off the singularity.**

`(2i)⁻¹(1 - w)` is the value of the symbol every construction here calls `gsym`, and this
says it inverts `κ(w) + i`.  Three proofs -- two `hprod`s and one `hgae`, in this file and
in the retired `SpectralGapInverse.lean` -- each derived it inline from `cayleyInv_add_I` and
`field_simp`; it is one line of algebra and belongs beside the identity it uses. -/
theorem inv_two_I_mul_one_sub_mul_cayleyInv_add_I
    {w : _root_.spectrum ℂ (A.cayley)} (hw1 : (w : ℂ) ≠ 1) :
    (2 * Complex.I)⁻¹ * (1 - (w : ℂ)) * (((cayleyInv A w : ℝ) : ℂ) + Complex.I) = 1 := by
  have hd : (1 : ℂ) - (w : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  rw [cayleyInv_add_I hA hw1]
  field_simp

variable (B : Set ℝ) (hB : MeasurableSet B)

/-- A bounded spectral range lies inside the operator domain. -/
theorem mem_domain_of_mem_specRange_of_bounded {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M)
    {x : H} (hx : x ∈ specRange hA B hB) : x ∈ A.domain := by
  have hM : 0 ≤ max 0 M := le_max_left _ _
  have hcut := hA.mem_graph_spectralCut B hB 0 (max 0 M) hM
    (fun s hs => by simpa only [sub_zero] using (hbnd s hs).trans (le_max_right _ _)) x
  have hfix := (mem_specRange_iff hA B hB x).1 hx
  rw [specProjection_def] at hfix
  rw [hfix] at hcut
  exact _root_.LinearPMap.mem_domain_of_mem_graph hcut

/-- On a bounded spectral range, the operator differs from its center by the spectral radius. -/
theorem norm_sub_smul_le_of_mem_specRange {M c r : ℝ} (_hbnd : ∀ s ∈ B, |s| ≤ M)
    (hr : 0 ≤ r) (hcr : ∀ s ∈ B, |s - c| ≤ r) {x : H} (hx : x ∈ specRange hA B hB)
    (hmem : x ∈ A.domain) :
    ‖A ⟨x, hmem⟩ - (c : ℂ) • x‖ ≤ r * ‖x‖ := by
  have hcut := hA.mem_graph_spectralCut B hB c r hr hcr x
  have hfix := (mem_specRange_iff hA B hB x).1 hx
  rw [specProjection_def] at hfix
  rw [hfix] at hcut
  have hact := A.mem_graph_snd_inj (A.mem_graph ⟨x, hmem⟩) hcut rfl
  rw [hact, add_sub_cancel_right]
  exact (A.spectralCut hA B hB c r hr hcr).le_of_opNorm_le
    (hA.norm_spectralCut_le B hB c r hr hcr) x

/-- **The interval cutoffs converge strongly to the identity.** -/
theorem tendsto_specProjection_Icc (x : H) :
    Filter.Tendsto
      (fun τ : ℝ => specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x)
      Filter.atTop (nhds x) := by
  classical
  set hU := hA.isStarNormal_cayley with hhU
  set μ := (cfcHom hU).representationDiagMeasure x with hμ
  set κ := cayleyInv A with hκ
  set F : ℝ → _root_.spectrum ℂ (A.cayley) → ℝ :=
    fun τ => (κ ⁻¹' Set.Icc (-τ) τ).indicator (fun _ => (1 : ℝ)) with hF
  -- the diagonal masses are the indicator integrals
  have hd : ∀ τ : ℝ, (((A.spectralPVM hA).diag x) (Set.Icc (-τ) τ)).toReal
      = ∫ w, F τ w ∂μ := by
    intro τ
    have hSm : MeasurableSet (κ ⁻¹' Set.Icc (-τ) τ) :=
      measurable_cayleyInv A measurableSet_Icc
    have hdiag : ((A.spectralPVM hA).diag x) = Measure.map κ μ := by
      rw [spectralPVM_def, BorelCalculus.toProjValMeasure_diag, hμ, hκ]
    -- Left as a `rw` chain on purpose: `simp only` with this same list leaves the
    -- goal unsolved.  `integral_indicator_const` only applies once `Measure.map_apply`
    -- has put the measure in the right form, and `simp only` normalises past that shape
    -- before the integral lemma can see it.
    rw [hdiag,
      Measure.map_apply (measurable_cayleyInv A) measurableSet_Icc, hF,
      integral_indicator_const _ hSm, smul_eq_mul, mul_one,
      MeasureTheory.measureReal_def]
  -- dominated convergence
  have hlim : Filter.Tendsto (fun τ : ℝ => ∫ w, F τ w ∂μ) Filter.atTop
      (nhds (∫ _w, (1 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
      (Filter.Eventually.of_forall fun τ =>
        (measurable_const.indicator
          (measurable_cayleyInv A measurableSet_Icc)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun τ => Filter.Eventually.of_forall fun w => ?_)
      (integrable_const _)
      (Filter.Eventually.of_forall fun w => ?_)
    · by_cases hw : w ∈ κ ⁻¹' Set.Icc (-τ) τ <;> simp [hF, hw]
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.eventually_ge_atTop |κ w|] with τ hτ
      have hmem : w ∈ κ ⁻¹' Set.Icc (-τ) τ :=
        ⟨by linarith [neg_abs_le (κ w)], by linarith [le_abs_self (κ w)]⟩
      simp [hF, hmem]
  have htot : ∫ _w, (1 : ℝ) ∂μ = ‖x‖ ^ 2 := by
    rw [integral_const, smul_eq_mul, mul_one, hμ,
      StarAlgHom.representationDiagMeasure_real_univ]
  -- the squared distance is the missing mass
  have hsq : ∀ τ : ℝ,
      ‖specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x - x‖ ^ 2
        = ‖x‖ ^ 2 - (((A.spectralPVM hA).diag x) (Set.Icc (-τ) τ)).toReal := by
    intro τ
    have hnormP : ‖specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x‖ ^ 2
        = (((A.spectralPVM hA).diag x) (Set.Icc (-τ) τ)).toReal := by
      rw [specProjection_def]; exact (A.spectralPVM hA).norm_sq_proj_apply _ _ x
    have hinner : ⟪x, specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x⟫_ℂ
        = ((((A.spectralPVM hA).diag x) (Set.Icc (-τ) τ)).toReal : ℂ) := by
      rw [specProjection_def]; exact (A.spectralPVM hA).inner_proj _ _ x
    have hre : RCLike.re (⟪specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x, x⟫_ℂ)
        = (((A.spectralPVM hA).diag x) (Set.Icc (-τ) τ)).toReal := by
      rw [← inner_conj_symm, hinner]
      simp
    rw [norm_sub_sq (𝕜 := ℂ), hnormP, hre]
    ring
  -- conclude
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  have hsq' : Filter.Tendsto
      (fun τ : ℝ => ‖specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x - x‖ ^ 2)
      Filter.atTop (nhds 0) := by
    have hconv : Filter.Tendsto
        (fun τ : ℝ => ‖x‖ ^ 2 - (((A.spectralPVM hA).diag x) (Set.Icc (-τ) τ)).toReal)
        Filter.atTop (nhds (‖x‖ ^ 2 - ‖x‖ ^ 2)) := by
      refine Filter.Tendsto.sub tendsto_const_nhds ?_
      simpa only [hd, htot] using hlim
    simpa only [hsq, sub_self] using hconv
  have hfin := (Real.continuous_sqrt.tendsto 0).comp hsq'
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hfin

private noncomputable def boundedCoordinate {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) :
    BoundedBorelFunction ℝ :=
  BoundedBorelFunction.ofFunction (B.indicator fun s => (s : ℂ))
    ((by fun_prop : Measurable fun s : ℝ => (s : ℂ)).indicator hB)
    ⟨max 0 M, le_max_left _ _, fun s => by
      by_cases hs : s ∈ B
      · simpa only [Set.indicator_of_mem hs, Complex.norm_real, Real.norm_eq_abs] using
          (hbnd s hs).trans (le_max_right 0 M)
      · simp only [Set.indicator_of_notMem hs, norm_zero]; exact le_max_left _ _⟩

private theorem spectralCut_zero_integral {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) :
    A.spectralCut hA B hB 0 (max 0 M) (le_max_left _ _)
      (fun s hs => by simpa using (hbnd s hs).trans (le_max_right 0 M)) =
        (A.spectralPVM hA).integral (boundedCoordinate B hB hbnd) := by
  apply hA.spectralCut_eq_integral
  intro s
  simp [boundedCoordinate]

/-- The centered-zero spectral cut agrees with the actual operator on its projection. -/
theorem spectralCut_zero_eq_on_specProjection {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) (y : H) :
    ∃ hy : specProjection hA B hB y ∈ A.domain,
      A ⟨specProjection hA B hB y, hy⟩ =
        A.spectralCut hA B hB 0 (max 0 M) (le_max_left _ _)
          (fun s hs => by simpa using (hbnd s hs).trans (le_max_right 0 M)) y := by
  have h := hA.mem_graph_spectralCut B hB 0 (max 0 M) (le_max_left _ _)
    (fun s hs => by simpa using (hbnd s hs).trans (le_max_right 0 M)) y
  simp only [Complex.ofReal_zero, zero_smul, add_zero, ← specProjection_def] at h
  have hm := _root_.LinearPMap.mem_domain_of_mem_graph h
  exact ⟨hm, A.mem_graph_snd_inj (A.mem_graph ⟨_, hm⟩) h rfl⟩

/-- A spectral cut with real symbol is self-adjoint. -/
theorem isSelfAdjoint_spectralCut_zero {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) :
    IsSelfAdjoint (A.spectralCut hA B hB 0 (max 0 M) (le_max_left _ _)
      (fun s hs => by simpa using (hbnd s hs).trans (le_max_right 0 M))) := by
  rw [spectralCut_zero_integral hA B hB hbnd]
  have hf : star (boundedCoordinate B hB hbnd) = boundedCoordinate B hB hbnd := by
    ext s
    simp only [BoundedBorelFunction.star_apply, boundedCoordinate,
      BoundedBorelFunction.ofFunction_apply]
    by_cases hs : s ∈ B <;> simp [hs]
  change star ((A.spectralPVM hA).integral _) = _
  rw [← map_star, hf]

/-- The centered-zero cut absorbs its spectral projection. -/
theorem spectralCut_zero_mul_specProjection {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) :
    A.spectralCut hA B hB 0 (max 0 M) (le_max_left _ _)
      (fun s hs => by simpa using (hbnd s hs).trans (le_max_right 0 M)) *
        specProjection hA B hB =
      A.spectralCut hA B hB 0 (max 0 M) (le_max_left _ _)
        (fun s hs => by simpa using (hbnd s hs).trans (le_max_right 0 M)) := by
  rw [spectralCut_zero_integral hA B hB hbnd, specProjection_def, ProjValMeasure.integral_mul_proj]
  congr 1
  ext s
  simp only [BoundedBorelFunction.indicator_apply, boundedCoordinate,
    BoundedBorelFunction.ofFunction_apply]
  by_cases hs : s ∈ B <;> simp [hs]

/-- The centered-zero cut already lands in its spectral range. -/
theorem specProjection_mul_spectralCut_zero {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) :
    specProjection hA B hB *
      A.spectralCut hA B hB 0 (max 0 M) (le_max_left _ _)
        (fun s hs => by simpa using (hbnd s hs).trans (le_max_right 0 M)) =
      A.spectralCut hA B hB 0 (max 0 M) (le_max_left _ _)
        (fun s hs => by simpa using (hbnd s hs).trans (le_max_right 0 M)) := by
  rw [spectralCut_zero_integral hA B hB hbnd, specProjection_def, ProjValMeasure.proj_mul_integral]
  congr 1
  ext s
  simp only [BoundedBorelFunction.indicator_apply, boundedCoordinate,
    BoundedBorelFunction.ofFunction_apply]
  by_cases hs : s ∈ B <;> simp [hs]

end BoundedSet

end LinearPMap
end TauCeti
