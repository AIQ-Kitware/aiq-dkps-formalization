/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.GenuineSpectralCutoff
import Spectra.SpectralTheory.Algebra

/-!
# Direct Spectra bounded truncations for the unbounded Sylvester argument

This leaf supplies the second direct vendored-Spectra implementation required by
`GenuineBoundedTruncationInterface`.  At radius `τ`, the truncation is the bounded
functional calculus of the real symbol `λ 1_{[-τ,τ]}(λ)`.

The interface laws follow from the vendored bounded calculus and the direct cutoff
interface:

* reality of the symbol gives symmetry;
* the generator-on-a-bounded-spectral-band theorem identifies the truncation with
  the original closed operator on the cutoff range;
* generator/cutoff commutation gives convergence on the operator domain;
* the original quadratic-form bounds apply directly to cutoff vectors;
* multiplicativity of the bounded calculus gives absorption by the cutoff.
-/

open scoped InnerProductSpace Topology
open Filter

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open Spectra.OneParameterUnitaryGroup
open Spectra.YosidaHille
open Spectra.QuantumMechanics.SpectralTheory

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private noncomputable def spectraTruncationSymbol (τ : ℝ) : ℝ → ℂ :=
  fun l => (l : ℂ) * Set.indicator (Set.Icc (-τ) τ) (fun _ => (1 : ℂ)) l

private theorem spectraTruncationSymbol_measurable (τ : ℝ) :
    Measurable (spectraTruncationSymbol τ) := by
  exact id_indicator_measurable measurableSet_Icc

private theorem spectraTruncationSymbol_bdd (τ : ℝ) :
    ∃ C, ∀ l, ‖spectraTruncationSymbol τ l‖ ≤ C := by
  exact id_indicator_bdd (fun _ hl => abs_le_max_of_mem_Icc hl)

/-- The direct bounded truncation `Φ(λ 1_{[-τ,τ]}(λ))`. -/
noncomputable def spectraBoundedTruncation
    (A : ComplexClosedOperatorH (H := H))
    (hA : A.IsSelfAdjoint) (τ : ℝ) : H →L[ℂ] H :=
  spectralCalculus (genToGroup hA) (spectraTruncationSymbol τ)
    (spectraTruncationSymbol_measurable τ) (spectraTruncationSymbol_bdd τ)

/-- The direct bounded truncation is symmetric. -/
theorem spectraBoundedTruncation_isSymmetric
    (A : ComplexClosedOperatorH (H := H))
    (hA : A.IsSelfAdjoint) (τ : ℝ) :
    (spectraBoundedTruncation A hA τ).IsSymmetric := by
  apply (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
  change ContinuousLinearMap.adjoint
      (spectraBoundedTruncation A hA τ) =
    spectraBoundedTruncation A hA τ
  unfold spectraBoundedTruncation
  have hconj :
      (fun l => (starRingEnd ℂ) (spectraTruncationSymbol τ l)) =
        spectraTruncationSymbol τ := by
    funext l
    by_cases hl : l ∈ Set.Icc (-τ) τ
    · rw [spectraTruncationSymbol, Set.indicator_of_mem hl, mul_one,
        Complex.conj_ofReal]
    · rw [spectraTruncationSymbol, Set.indicator_of_notMem hl, mul_zero, map_zero]
  have hcm : Measurable fun l =>
      (starRingEnd ℂ) (spectraTruncationSymbol τ l) :=
    Complex.continuous_conj.measurable.comp
      (spectraTruncationSymbol_measurable τ)
  have hcb : ∃ C, ∀ l,
      ‖(starRingEnd ℂ) (spectraTruncationSymbol τ l)‖ ≤ C := by
    obtain ⟨C, hC⟩ := spectraTruncationSymbol_bdd τ
    exact ⟨C, fun l => by rw [RCLike.norm_conj]; exact hC l⟩
  rw [spectralCalculus_adjoint (genToGroup hA)
    (spectraTruncationSymbol τ)
    (spectraTruncationSymbol_measurable τ)
    (spectraTruncationSymbol_bdd τ) hcm hcb]
  exact spectralCalculus_congr (genToGroup hA) hconj hcm hcb
    (spectraTruncationSymbol_measurable τ)
    (spectraTruncationSymbol_bdd τ)

/-- The direct truncation agrees with the closed operator on the cutoff range. -/
theorem spectraBoundedTruncation_eq_on_cutoff
    (A : ComplexClosedOperatorH (H := H))
    (hA : A.IsSelfAdjoint) (τ : ℝ) (x : H) :
    ∃ hx : spectraSpectralCutoff A hA τ x ∈ A.domain,
      spectraBoundedTruncation A hA τ x =
        A.toLinearMap ⟨spectraSpectralCutoff A hA τ x, hx⟩ := by
  let U := genToGroup hA
  have hR : ∀ l ∈ Set.Icc (-τ) τ, |l| ≤ max |(-τ)| |τ| :=
    fun _ hl => abs_le_max_of_mem_Icc hl
  have hxU : spectralProjection U (Set.Icc (-τ) τ) measurableSet_Icc x ∈
      (generator U).domain :=
    spectralProjection_mem_generatorDomain U measurableSet_Icc hR x
  have hgen : generator U = A.toLinearPMap := generator_genToGroup hA
  have hdom : (generator U).domain = A.domain :=
    congrArg LinearPMap.domain hgen
  have hxA : spectraSpectralCutoff A hA τ x ∈ A.domain := by
    change spectralProjection U (Set.Icc (-τ) τ) measurableSet_Icc x ∈ A.domain
    exact (le_of_eq hdom) hxU
  refine ⟨hxA, ?_⟩
  have hval := generator_spectralProjection U measurableSet_Icc hR x
  have hcalc :
      spectralCalculus U (spectraTruncationSymbol τ)
          (spectraTruncationSymbol_measurable τ)
          (spectraTruncationSymbol_bdd τ) =
        spectralCalculus U
          (fun l => (l : ℂ) *
            Set.indicator (Set.Icc (-τ) τ) (fun _ => (1 : ℂ)) l)
          (id_indicator_measurable measurableSet_Icc)
          (id_indicator_bdd hR) := by
    exact spectralCalculus_congr U (by rfl)
      (spectraTruncationSymbol_measurable τ)
      (spectraTruncationSymbol_bdd τ)
      (id_indicator_measurable measurableSet_Icc)
      (id_indicator_bdd hR)
  have happly := (LinearPMap.ext_iff.mp hgen).2
  have hbridge :
      generator U
          ⟨spectralProjection U (Set.Icc (-τ) τ) measurableSet_Icc x, hxU⟩ =
        A.toLinearPMap
          ⟨spectralProjection U (Set.Icc (-τ) τ) measurableSet_Icc x, hxA⟩ :=
    happly
      (x := spectralProjection U (Set.Icc (-τ) τ) measurableSet_Icc x)
      (hf := hxU) (hg := hxA)
  change spectralCalculus U (spectraTruncationSymbol τ)
      (spectraTruncationSymbol_measurable τ)
      (spectraTruncationSymbol_bdd τ) x =
    A.toLinearPMap
      ⟨spectralProjection U (Set.Icc (-τ) τ) measurableSet_Icc x, hxA⟩
  calc
    spectralCalculus U (spectraTruncationSymbol τ)
        (spectraTruncationSymbol_measurable τ)
        (spectraTruncationSymbol_bdd τ) x =
      spectralCalculus U
          (fun l => (l : ℂ) *
            Set.indicator (Set.Icc (-τ) τ) (fun _ => (1 : ℂ)) l)
          (id_indicator_measurable measurableSet_Icc)
          (id_indicator_bdd hR) x :=
        congrArg (fun T : H →L[ℂ] H => T x) hcalc
    _ = generator U
        ⟨spectralProjection U (Set.Icc (-τ) τ) measurableSet_Icc x, hxU⟩ :=
      hval.symm
    _ = A.toLinearPMap
        ⟨spectralProjection U (Set.Icc (-τ) τ) measurableSet_Icc x, hxA⟩ := hbridge

/-- On the operator domain, direct truncation is the cutoff applied to the
operator value. -/
theorem spectraBoundedTruncation_apply_domain
    (A : ComplexClosedOperatorH (H := H))
    (hA : A.IsSelfAdjoint) (τ : ℝ) (x : A.domain) :
    spectraBoundedTruncation A hA τ (x : H) =
      spectraSpectralCutoff A hA τ (A.toLinearMap x) := by
  obtain ⟨hx, htrunc⟩ :=
    spectraBoundedTruncation_eq_on_cutoff A hA τ (x : H)
  obtain ⟨hxcomm, hcomm⟩ :=
    spectraSpectralCutoff_commutes_on_domain A hA τ x
  have hsub :
      (⟨spectraSpectralCutoff A hA τ (x : H), hx⟩ : A.domain) =
        ⟨spectraSpectralCutoff A hA τ (x : H), hxcomm⟩ :=
    Subtype.ext rfl
  calc
    spectraBoundedTruncation A hA τ (x : H) =
        A.toLinearMap ⟨spectraSpectralCutoff A hA τ (x : H), hx⟩ := htrunc
    _ = A.toLinearMap
        ⟨spectraSpectralCutoff A hA τ (x : H), hxcomm⟩ :=
      congrArg A.toLinearMap hsub
    _ = spectraSpectralCutoff A hA τ (A.toLinearMap x) := hcomm

/-- Direct truncations reconstruct the closed operator on its domain. -/
theorem spectraBoundedTruncation_tendsto_on_domain
    (A : ComplexClosedOperatorH (H := H))
    (hA : A.IsSelfAdjoint) (x : A.domain) :
    Tendsto (fun τ : ℝ => spectraBoundedTruncation A hA τ (x : H))
      atTop (𝓝 (A.toLinearMap x)) := by
  have hcut := spectraSpectralCutoff_tendsto_identity A hA (A.toLinearMap x)
  exact hcut.congr' (Filter.Eventually.of_forall fun τ =>
    (spectraBoundedTruncation_apply_domain A hA τ x).symm)

/-- A lower quadratic-form bound passes to each direct bounded truncation. -/
theorem spectraBoundedTruncation_lowerBound
    (A : ComplexClosedOperatorH (H := H))
    (hA : A.IsSelfAdjoint) {c : ℝ}
    (hLower : SemiboundedBelow A c) {τ : ℝ} (_hτ : 0 ≤ τ) (x : H) :
    c * ‖spectraSpectralCutoff A hA τ x‖ ^ 2 ≤
      RCLike.re ⟪spectraBoundedTruncation A hA τ x,
        spectraSpectralCutoff A hA τ x⟫_ℂ := by
  obtain ⟨hx, htrunc⟩ := spectraBoundedTruncation_eq_on_cutoff A hA τ x
  rw [htrunc]
  exact hLower ⟨spectraSpectralCutoff A hA τ x, hx⟩

/-- An upper quadratic-form bound passes to each direct bounded truncation. -/
theorem spectraBoundedTruncation_upperBound
    (A : ComplexClosedOperatorH (H := H))
    (hA : A.IsSelfAdjoint) {c : ℝ}
    (hUpper : SemiboundedAbove A c) {τ : ℝ} (_hτ : 0 ≤ τ) (x : H) :
    RCLike.re ⟪spectraBoundedTruncation A hA τ x,
        spectraSpectralCutoff A hA τ x⟫_ℂ ≤
      c * ‖spectraSpectralCutoff A hA τ x‖ ^ 2 := by
  obtain ⟨hx, htrunc⟩ := spectraBoundedTruncation_eq_on_cutoff A hA τ x
  rw [htrunc]
  exact hUpper ⟨spectraSpectralCutoff A hA τ x, hx⟩

private theorem spectraTruncationSymbol_mul_cutoff (τ : ℝ) :
    (fun l => spectraTruncationSymbol τ l *
      Set.indicator (Set.Icc (-τ) τ) (fun _ => (1 : ℂ)) l) =
      spectraTruncationSymbol τ := by
  funext l
  by_cases hl : l ∈ Set.Icc (-τ) τ
  · simp only [spectraTruncationSymbol, Set.indicator_of_mem hl, mul_one]
  · simp only [spectraTruncationSymbol, Set.indicator_of_notMem hl, mul_zero]

/-- Direct bounded truncation is absorbed by its cutoff projection on both
sides. -/
theorem spectraBoundedTruncation_commutes_cutoff
    (A : ComplexClosedOperatorH (H := H))
    (hA : A.IsSelfAdjoint) (τ : ℝ) :
    spectraBoundedTruncation A hA τ ∘L spectraSpectralCutoff A hA τ =
        spectraBoundedTruncation A hA τ ∧
      spectraSpectralCutoff A hA τ ∘L spectraBoundedTruncation A hA τ =
        spectraBoundedTruncation A hA τ := by
  let U := genToGroup hA
  have hcut_m : Measurable
      (fun l : ℝ => Set.indicator (Set.Icc (-τ) τ)
        (fun _ => (1 : ℂ)) l) :=
    measurable_const.indicator measurableSet_Icc
  have hcut_b : ∃ C, ∀ l : ℝ,
      ‖Set.indicator (Set.Icc (-τ) τ) (fun _ => (1 : ℂ)) l‖ ≤ C :=
    indicator_one_bdd (Set.Icc (-τ) τ)
  have hprod_m : Measurable fun l =>
      spectraTruncationSymbol τ l *
        Set.indicator (Set.Icc (-τ) τ) (fun _ => (1 : ℂ)) l :=
    (spectraTruncationSymbol_measurable τ).mul hcut_m
  have hprod_b : ∃ C, ∀ l,
      ‖spectraTruncationSymbol τ l *
        Set.indicator (Set.Icc (-τ) τ) (fun _ => (1 : ℂ)) l‖ ≤ C :=
    bounded_mul (spectraTruncationSymbol_bdd τ) hcut_b
  have hright :
      spectralCalculus U (spectraTruncationSymbol τ)
          (spectraTruncationSymbol_measurable τ)
          (spectraTruncationSymbol_bdd τ) *
        spectralCalculus U
          (fun l : ℝ => Set.indicator (Set.Icc (-τ) τ)
            (fun _ => (1 : ℂ)) l)
          hcut_m hcut_b =
      spectralCalculus U (spectraTruncationSymbol τ)
          (spectraTruncationSymbol_measurable τ)
          (spectraTruncationSymbol_bdd τ) := by
    calc
      spectralCalculus U (spectraTruncationSymbol τ)
          (spectraTruncationSymbol_measurable τ)
          (spectraTruncationSymbol_bdd τ) *
        spectralCalculus U
          (fun l : ℝ => Set.indicator (Set.Icc (-τ) τ)
            (fun _ => (1 : ℂ)) l)
          hcut_m hcut_b =
        spectralCalculus U
          (fun l => spectraTruncationSymbol τ l *
            Set.indicator (Set.Icc (-τ) τ) (fun _ => (1 : ℂ)) l)
          hprod_m hprod_b := by
            exact spectralCalculus_mul U
              (fun l : ℝ => Set.indicator (Set.Icc (-τ) τ)
                (fun _ => (1 : ℂ)) l)
              (spectraTruncationSymbol τ)
              hcut_m hcut_b
              (spectraTruncationSymbol_measurable τ)
              (spectraTruncationSymbol_bdd τ) hprod_m hprod_b
      _ = spectralCalculus U (spectraTruncationSymbol τ)
          (spectraTruncationSymbol_measurable τ)
          (spectraTruncationSymbol_bdd τ) :=
        spectralCalculus_congr U (spectraTruncationSymbol_mul_cutoff τ)
          hprod_m hprod_b
          (spectraTruncationSymbol_measurable τ)
          (spectraTruncationSymbol_bdd τ)
  have hcomm := spectralCalculus_comm U
    (fun l : ℝ => Set.indicator (Set.Icc (-τ) τ)
      (fun _ => (1 : ℂ)) l)
    (spectraTruncationSymbol τ)
    hcut_m hcut_b
    (spectraTruncationSymbol_measurable τ)
    (spectraTruncationSymbol_bdd τ)
  constructor
  · simpa only [spectraBoundedTruncation, spectraSpectralCutoff,
      spectralProjection, U, ContinuousLinearMap.mul_def] using hright
  · simpa only [spectraBoundedTruncation, spectraSpectralCutoff,
      spectralProjection, U, ContinuousLinearMap.mul_def] using
        hcomm.symm.trans hright


/-- The direct vendored-Spectra implementation of the coherent bounded
truncation interface. -/
noncomputable def spectraBoundedTruncationInterface
    (A : ComplexClosedOperatorH (H := H))
    (hA : A.IsSelfAdjoint) :
    GenuineBoundedTruncationInterface A hA
      (spectraSpectralCutoffInterface A hA) where
  truncation := spectraBoundedTruncation A hA
  isSymmetric := spectraBoundedTruncation_isSymmetric A hA
  eq_on_cutoff := spectraBoundedTruncation_eq_on_cutoff A hA
  tendsto_on_domain := spectraBoundedTruncation_tendsto_on_domain A hA
  lowerBound := by
    intro c hLower τ hτ x
    exact spectraBoundedTruncation_lowerBound A hA hLower hτ x
  upperBound := by
    intro c hUpper τ hτ x
    exact spectraBoundedTruncation_upperBound A hA hUpper hτ x
  commutes_cutoff := spectraBoundedTruncation_commutes_cutoff A hA

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
