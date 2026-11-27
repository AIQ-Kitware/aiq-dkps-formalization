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

variable (B : Set ℝ) (hB : MeasurableSet B)

/-- A bounded spectral range lies inside the operator domain. -/
theorem mem_domain_of_mem_specRange_of_bounded {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M)
    {x : H} (hx : x ∈ ((A.spectralPVM hA).proj B hB).range) : x ∈ A.domain := by
  have hM : 0 ≤ max 0 M := le_max_left _ _
  have hcut := hA.mem_graph_spectralCut B hB 0 (max 0 M) hM
    (fun s hs => by simpa only [sub_zero] using (hbnd s hs).trans (le_max_right _ _)) x
  have hfix := Submodule.starProjection_eq_self_iff.mpr hx
  rw [ProjValMeasure.starProjection_range_proj] at hfix
  rw [hfix] at hcut
  exact _root_.LinearPMap.mem_domain_of_mem_graph hcut

/-- On a bounded spectral range, the operator differs from its center by the spectral radius. -/
theorem norm_sub_smul_le_of_mem_specRange {M c r : ℝ} (_hbnd : ∀ s ∈ B, |s| ≤ M)
    (hr : 0 ≤ r) (hcr : ∀ s ∈ B, |s - c| ≤ r) {x : H}
    (hx : x ∈ ((A.spectralPVM hA).proj B hB).range)
    (hmem : x ∈ A.domain) :
    ‖A ⟨x, hmem⟩ - (c : ℂ) • x‖ ≤ r * ‖x‖ := by
  have hcut := hA.mem_graph_spectralCut B hB c r hr hcr x
  have hfix := Submodule.starProjection_eq_self_iff.mpr hx
  rw [ProjValMeasure.starProjection_range_proj] at hfix
  rw [hfix] at hcut
  have hact := A.mem_graph_snd_inj (A.mem_graph ⟨x, hmem⟩) hcut rfl
  rw [hact, add_sub_cancel_right]
  exact (A.spectralCut hA B hB c r hr hcr).le_of_opNorm_le
    (hA.norm_spectralCut_le B hB c r hr hcr) x

/-- **The interval cutoffs converge strongly to the identity.** -/
theorem tendsto_specProjection_Icc (x : H) :
    Filter.Tendsto
      (fun τ : ℝ => (A.spectralPVM hA).proj (Set.Icc (-τ) τ) measurableSet_Icc x)
      Filter.atTop (nhds x) := by
  exact (A.spectralPVM hA).tendsto_proj_apply (fun _ : ℝ => measurableSet_Icc) x
    (Filter.Eventually.of_forall fun s =>
      (Filter.eventually_ge_atTop |s|).mono fun τ hs => abs_le.mp hs)

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
    ∃ hy : (A.spectralPVM hA).proj B hB y ∈ A.domain,
      A ⟨(A.spectralPVM hA).proj B hB y, hy⟩ =
        A.spectralCut hA B hB 0 (max 0 M) (le_max_left _ _)
          (fun s hs => by simpa using (hbnd s hs).trans (le_max_right 0 M)) y := by
  have h := hA.mem_graph_spectralCut B hB 0 (max 0 M) (le_max_left _ _)
    (fun s hs => by simpa using (hbnd s hs).trans (le_max_right 0 M)) y
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at h
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
        (A.spectralPVM hA).proj B hB =
      A.spectralCut hA B hB 0 (max 0 M) (le_max_left _ _)
        (fun s hs => by simpa using (hbnd s hs).trans (le_max_right 0 M)) := by
  rw [spectralCut_zero_integral hA B hB hbnd, ProjValMeasure.integral_mul_proj]
  congr 1
  ext s
  simp only [BoundedBorelFunction.indicator_apply, boundedCoordinate,
    BoundedBorelFunction.ofFunction_apply]
  by_cases hs : s ∈ B <;> simp [hs]

/-- The centered-zero cut already lands in its spectral range. -/
theorem specProjection_mul_spectralCut_zero {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) :
    (A.spectralPVM hA).proj B hB *
      A.spectralCut hA B hB 0 (max 0 M) (le_max_left _ _)
        (fun s hs => by simpa using (hbnd s hs).trans (le_max_right 0 M)) =
      A.spectralCut hA B hB 0 (max 0 M) (le_max_left _ _)
        (fun s hs => by simpa using (hbnd s hs).trans (le_max_right 0 M)) := by
  rw [spectralCut_zero_integral hA B hB hbnd, ProjValMeasure.proj_mul_integral]
  congr 1
  ext s
  simp only [BoundedBorelFunction.indicator_apply, boundedCoordinate,
    BoundedBorelFunction.ofFunction_apply]
  by_cases hs : s ∈ B <;> simp [hs]

end BoundedSet

end LinearPMap
end TauCeti
