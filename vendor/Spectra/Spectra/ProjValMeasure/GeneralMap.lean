/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Spectra.ProjValMeasure.General

/-!
# Pushforward of a general projection-valued measure to the real line

A projective measure on an arbitrary measurable outcome space can be pushed
forward along a measurable real-valued observable.  This is the bridge from a
joint PVM on `R x R` to the ordinary one-dimensional PVM of a joint symbol such
as `(lambda, alpha) |-> lambda - alpha`.
-/

open MeasureTheory Complex
open scoped InnerProductSpace

namespace Spectra
namespace ProjValMeasure'

noncomputable section

variable {K ι : Type*}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [MeasurableSpace ι]

/-- Push a general PVM forward along a measurable real-valued map. -/
noncomputable def mapToReal (P : ProjValMeasure' K ι)
    (φ : ι → ℝ) (hφ : Measurable φ) : ProjValMeasure K where
  proj B hB := P.proj (φ ⁻¹' B) (hφ hB)
  diag ξ := (P.diag ξ).map φ
  diag_finite ξ := by
    haveI := P.diag_finite ξ
    exact (P.diag ξ).isFiniteMeasure_map φ
  inner_proj B hB ξ := by
    rw [P.inner_proj (φ ⁻¹' B) (hφ hB) ξ, Measure.map_apply hφ hB]
  proj_univ := by
    show P.proj (φ ⁻¹' Set.univ) (hφ MeasurableSet.univ) =
      ContinuousLinearMap.id ℂ K
    rw [P.proj_congr Set.preimage_univ
      (hφ MeasurableSet.univ) MeasurableSet.univ]
    exact P.proj_univ
  proj_inter B₁ B₂ hB₁ hB₂ := by
    show P.proj (φ ⁻¹' B₁) (hφ hB₁) *
        P.proj (φ ⁻¹' B₂) (hφ hB₂) =
      P.proj (φ ⁻¹' (B₁ ∩ B₂)) (hφ (hB₁.inter hB₂))
    rw [P.proj_inter (φ ⁻¹' B₁) (φ ⁻¹' B₂)
      (hφ hB₁) (hφ hB₂)]
    exact P.proj_congr Set.preimage_inter.symm
      ((hφ hB₁).inter (hφ hB₂)) (hφ (hB₁.inter hB₂))

@[simp]
theorem mapToReal_proj (P : ProjValMeasure' K ι)
    (φ : ι → ℝ) (hφ : Measurable φ)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (P.mapToReal φ hφ).proj B hB =
      P.proj (φ ⁻¹' B) (hφ hB) :=
  rfl

@[simp]
theorem mapToReal_diag (P : ProjValMeasure' K ι)
    (φ : ι → ℝ) (hφ : Measurable φ) (ξ : K) :
    (P.mapToReal φ hφ).diag ξ = (P.diag ξ).map φ :=
  rfl

end
end ProjValMeasure'
end Spectra
