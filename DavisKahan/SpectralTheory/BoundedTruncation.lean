/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
module

public import DavisKahan.SpectralTheory.SpectralCutoff

public section

open TauCeti.DavisKahan.Sylvester

/-!
# Bounded truncations for the unbounded Sylvester argument

The truncation at radius `τ` is the Borel calculus of `λ · 1_{[-τ,τ]}` — the
bounded operator that agrees with `A` on the range of the cutoff `E_A([-τ,τ])`.

## Provenance

Until 2026-07-29 this was Spectra's `spectralCalculus` of the same symbol,
applied to the one-parameter unitary group of Stone's theorem.
The truncation uses `LinearPMap.spectralCut` at center zero. The graph law
identifies its action on the cutoff and gives the two form bounds.
The PVM integral of the native bounded Borel truncation supplies symmetry
and projection absorption.
-/

open scoped InnerProductSpace Topology
open Filter MeasureTheory

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta


universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The interval `[-τ, τ]` keeps the spectral parameter bounded by `max 0 τ`. -/
private theorem abs_sub_zero_le_radius_of_mem_Icc (τ : ℝ) :
    ∀ s ∈ Set.Icc (-τ) τ, |s - 0| ≤ max 0 τ := by
  intro s hs
  rw [sub_zero]
  exact (abs_le.mpr hs).trans (le_max_right 0 τ)

/-- The bounded truncation `A · E_A([-τ,τ])`. -/
noncomputable def spectraBoundedTruncation
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (τ : ℝ) : H →L[ℂ] H :=
  A.spectralCut hA (Set.Icc (-τ) τ) measurableSet_Icc 0 (max 0 τ)
    (le_max_left _ _) (abs_sub_zero_le_radius_of_mem_Icc τ)

private theorem norm_ofReal_le_set_eq_Icc (τ : ℝ) :
    {s : ℝ | ‖(s : ℂ)‖ ≤ τ} = Set.Icc (-τ) τ := by
  ext s
  change ‖(s : ℂ)‖ ≤ τ ↔ -τ ≤ s ∧ s ≤ τ
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]

private theorem spectraBoundedTruncation_eq_integral_truncate
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (τ : ℝ) :
    spectraBoundedTruncation A hA τ = (A.spectralPVM hA).integral
      (BoundedBorelFunction.truncate (fun s : ℝ => (s : ℂ)) Complex.measurable_ofReal τ) := by
  unfold spectraBoundedTruncation
  apply hA.spectralCut_eq_integral
  intro s
  rw [BoundedBorelFunction.truncate_apply, norm_ofReal_le_set_eq_Icc]
  simp only [sub_zero]

/-- Bounded truncations are symmetric: the symbol is real. -/
theorem spectraBoundedTruncation_isSymmetric
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (τ : ℝ) :
    (spectraBoundedTruncation A hA τ).IsSymmetric := by
  rw [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric,
    spectraBoundedTruncation_eq_integral_truncate]
  apply IsSelfAdjoint.map
  change star (BoundedBorelFunction.truncate _ _ _) = _
  have hreal : star (fun s : ℝ => (s : ℂ)) = fun s : ℝ => (s : ℂ) := by
    ext s
    simp
  simp only [BoundedBorelFunction.star_truncate, hreal]

/-- The truncation agrees with `A` on the cutoff range. -/
theorem spectraBoundedTruncation_eq_on_cutoff
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (τ : ℝ) (x : H) :
    ∃ hx : spectraSpectralCutoff A hA τ x ∈ A.domain,
      spectraBoundedTruncation A hA τ x = A ⟨spectraSpectralCutoff A hA τ x, hx⟩ := by
  have hgraph : (spectraSpectralCutoff A hA τ x, spectraBoundedTruncation A hA τ x) ∈
      A.graph := by
    simpa only [spectraSpectralCutoff, selfAdjointSpectralProjection, spectraBoundedTruncation,
      Complex.ofReal_zero, zero_smul, add_zero] using
      hA.mem_graph_spectralCut (Set.Icc (-τ) τ) measurableSet_Icc 0 (max 0 τ)
        (le_max_left _ _) (abs_sub_zero_le_radius_of_mem_Icc τ) x
  have hx := _root_.LinearPMap.mem_domain_of_mem_graph hgraph
  exact ⟨hx, A.mem_graph_snd_inj hgraph (A.mem_graph ⟨_, hx⟩) rfl⟩

/-- Bounded truncations converge strongly to `A` on its domain. -/
theorem spectraBoundedTruncation_tendsto_on_domain
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (x : A.domain) :
    Tendsto (fun τ : ℝ => spectraBoundedTruncation A hA τ (x : H)) atTop
      (𝓝 (A x)) := by
  have hval : ∀ τ : ℝ, spectraBoundedTruncation A hA τ (x : H)
      = (A.spectralPVM hA).proj (Set.Icc (-τ) τ) measurableSet_Icc
          (A x) := by
    intro τ
    obtain ⟨hx, hb⟩ := spectraBoundedTruncation_eq_on_cutoff A hA τ (x : H)
    rw [hb]
    exact ((hA.intertwines_spectralPVM_proj (Set.Icc (-τ) τ) measurableSet_Icc).apply_eq x).symm
  simp only [hval]
  exact spectraSpectralCutoff_tendsto_identity A hA (A x)

/-- A lower semibound for `A` descends to the truncations. -/
theorem spectraBoundedTruncation_lowerBound
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) {c : ℝ} (hc : TauCeti.LinearPMap.SemiboundedBelow A c) {τ : ℝ} (x : H) :
    c * ‖spectraSpectralCutoff A hA τ x‖ ^ 2 ≤
      RCLike.re ⟪spectraBoundedTruncation A hA τ x, spectraSpectralCutoff A hA τ x⟫_ℂ := by
  obtain ⟨hx, hb⟩ := spectraBoundedTruncation_eq_on_cutoff A hA τ x
  rw [hb]
  exact (TauCeti.LinearPMap.semiboundedBelow_iff _ _).mp hc
    ⟨spectraSpectralCutoff A hA τ x, hx⟩

/-- An upper semibound for `A` descends to the truncations. -/
theorem spectraBoundedTruncation_upperBound
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) {c : ℝ} (hc : TauCeti.LinearPMap.SemiboundedAbove A c) {τ : ℝ} (x : H) :
    RCLike.re ⟪spectraBoundedTruncation A hA τ x, spectraSpectralCutoff A hA τ x⟫_ℂ ≤
      c * ‖spectraSpectralCutoff A hA τ x‖ ^ 2 := by
  obtain ⟨hx, hb⟩ := spectraBoundedTruncation_eq_on_cutoff A hA τ x
  rw [hb]
  exact (TauCeti.LinearPMap.semiboundedAbove_iff _ _).mp hc
    ⟨spectraSpectralCutoff A hA τ x, hx⟩

/-- The truncation absorbs its cutoff on both sides. -/
theorem spectraBoundedTruncation_commutes_cutoff
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (τ : ℝ) :
    spectraBoundedTruncation A hA τ ∘L spectraSpectralCutoff A hA τ =
        spectraBoundedTruncation A hA τ ∧
      spectraSpectralCutoff A hA τ ∘L spectraBoundedTruncation A hA τ =
        spectraBoundedTruncation A hA τ := by
  rw [spectraBoundedTruncation_eq_integral_truncate]
  let f := BoundedBorelFunction.truncate (fun s : ℝ => (s : ℂ)) Complex.measurable_ofReal τ
  change (A.spectralPVM hA).integral f * (A.spectralPVM hA).proj _ measurableSet_Icc =
      (A.spectralPVM hA).integral f ∧
    (A.spectralPVM hA).proj _ measurableSet_Icc * (A.spectralPVM hA).integral f =
      (A.spectralPVM hA).integral f
  have hf : BoundedBorelFunction.indicator (Set.Icc (-τ) τ) measurableSet_Icc f = f := by
    simpa only [norm_ofReal_le_set_eq_Icc] using
      (BoundedBorelFunction.indicator_norm_le_truncate (fun s : ℝ => (s : ℂ))
        Complex.measurable_ofReal τ
        (hs := measurableSet_le Complex.measurable_ofReal.norm measurable_const))
  simp only [ProjValMeasure.integral_mul_proj, ProjValMeasure.proj_mul_integral, hf, and_self]

/-- The implementation of the coherent bounded truncation interface. -/
noncomputable def spectraBoundedTruncationInterface
    (A : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) :
    BoundedTruncationInterface A hA
      (spectraSpectralCutoffInterface A hA) where
  truncation := spectraBoundedTruncation A hA
  isSymmetric := spectraBoundedTruncation_isSymmetric A hA
  eq_on_cutoff := spectraBoundedTruncation_eq_on_cutoff A hA
  tendsto_on_domain := spectraBoundedTruncation_tendsto_on_domain A hA
  lowerBound := by
    intro c hLower τ _ x
    exact spectraBoundedTruncation_lowerBound A hA hLower x
  upperBound := by
    intro c hUpper τ _ x
    exact spectraBoundedTruncation_upperBound A hA hUpper x
  commutes_cutoff := spectraBoundedTruncation_commutes_cutoff A hA

end ExactSinTheta
end DavisKahan
end TauCeti
