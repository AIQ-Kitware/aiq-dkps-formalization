/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Frontier.RieszCircle
import DavisKahan.Experimental.Frontier.CircleContour
import DavisKahan.Experimental.Sources.DavisKahan1970.Section8.All

/-!
# Section 8 frontier: branch selection and spectral repulsion

This module states the missing bridges from circle spectral projections to the
existing continuation witnesses, then states the source-level conclusions of
Theorems 8.1 and 8.2.  The declarations are intentionally separate so progress
can be measured at the analytic, geometric, and source-wrapper layers.
-/

open scoped InnerProductSpace
open Set Filter

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Frontier
namespace Section8

open DavisKahanExt
open RieszCircle

universe u v

section ContinuationBridge

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {A E : H →L[ℂ] H} {s : Set ℝ}

/-- Every point of the affine self-adjoint path is self-adjoint: the real
parameter is conjugation-fixed. -/
theorem operatorPath_isSelfAdjointOperator
    {A E : H →L[ℂ] H} (hA : IsSelfAdjointOperator A)
    (hE : IsSelfAdjointOperator E) (t : ℝ) :
    IsSelfAdjointOperator (operatorPath A E t) :=
  hA.add (hE.smul (Complex.conj_ofReal t))

/-- Circle data sufficient to construct the continuation witness used by the
existing Section 8 development.  The pencil inverse is taken through the total
`Ring.inverse`, matching the RieszCircle surface. -/
structure CircleContinuationData
    (A E : H →L[ℂ] H) (s : Set ℝ) where
  hA : IsSelfAdjointOperator A
  hE : IsSelfAdjointOperator E
  hs : MeasurableSet s
  center : ℝ
  radius : ℝ
  margin : ℝ
  margin_pos : 0 < margin
  separates : ∀ t (_ht : t ∈ Set.Icc (0 : ℝ) 1),
    CircleSeparatesRealSpectrum (operatorPath A E t)
      (operatorPath_isSelfAdjointOperator hA hE t) s center radius
  inverse_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ∀ z : ℂ, ‖z - (center : ℂ)‖ = radius →
      ‖Ring.inverse (z • (1 : H →L[ℂ] H) - operatorPath A E t)‖ ≤ margin⁻¹

/-- Every circle point lies on the sphere of the circle contour. -/
theorem circleContour_path_norm_sub_center
    (D : CircleContinuationData A E s) (x : unitInterval) :
    ‖(CircleContour.circleContour (D.center : ℂ) D.radius).path x -
        (D.center : ℂ)‖ = D.radius := by
  show ‖circleMap (D.center : ℂ) D.radius (2 * Real.pi * (x : ℝ)) -
      (D.center : ℂ)‖ = D.radius
  simpa [mem_sphere_iff_norm] using
    circleMap_mem_sphere (D.center : ℂ)
      (D.separates 0 ⟨le_rfl, zero_le_one⟩).radius_pos.le
      (2 * Real.pi * (x : ℝ))

/-- A common separating circle constructs the canonical spectral continuation
witness consumed by the Section 8 branch-selection stack.  The pathwise
separating contours are the circle contours of `CircleContour`, and the
uniform margin comes from the common resolvent bound through the
Neumann-series estimate. -/
noncomputable def spectralContinuationWitness_of_circle
    (D : CircleContinuationData A E s) :
    SpectralContinuationWitness A E s where
  contour := CircleContour.circleContour (D.center : ℂ) D.radius
  separating := fun t ht =>
    CircleContour.circleSeparatingContour (operatorPath A E t)
      (operatorPath_isSelfAdjointOperator D.hA D.hE t) D.hs
      (D.separates t ht)
  geometric_eq := fun _t _ht => rfl
  margin := D.margin
  margin_pos := D.margin_pos
  spectrum_separated := by
    intro t ht x lam hlam
    have hzc := circleContour_path_norm_sub_center D x
    have hznot : (CircleContour.circleContour (D.center : ℂ) D.radius).path x ∉
        spectrum ℂ (operatorPath A E t) :=
      (D.separates t ht).contour_resolvent _ hzc
    have hb := D.inverse_bound t ht _ hzc
    exact CircleContour.margin_le_norm_sub_of_inverse_bound
      D.margin_pos hznot hb hlam

/-- The source and target selected projections of the witness are the genuine
bounded self-adjoint spectral projections. -/
theorem spectralContinuationWitness_of_circle_endpoints
    (D : CircleContinuationData A E s) :
    (spectralContinuationWitness_of_circle
        D).sourceSelectedSpectralSubspace.starProjection =
        boundedSelfAdjointSpectralProjection A D.hA s D.hs ∧
      (spectralContinuationWitness_of_circle
          D).targetSelectedSpectralSubspace.starProjection =
        boundedSelfAdjointSpectralProjection (A + E)
          (D.hA.add D.hE) s D.hs := by
  constructor
  · exact (boundedSelfAdjointSpectralProjection_eq_starProjection
      A D.hA s D.hs).symm
  · exact (boundedSelfAdjointSpectralProjection_eq_starProjection
      (A + E) (D.hA.add D.hE) s D.hs).symm

/-- Quantitative projection variation obtained from the common-circle
resolvent bound. -/
theorem selectedBranchProjectionLipschitzConstant_of_circle
    (D : CircleContinuationData A E s) :
    selectedBranchProjectionLipschitzConstant
      (spectralContinuationWitness_of_circle D).contour E D.margin ≤
        D.radius * ‖E‖ / D.margin ^ 2 := by
  have hr : (0 : ℝ) ≤ D.radius :=
    (D.separates 0 ⟨le_rfl, zero_le_one⟩).radius_pos.le
  apply le_of_eq
  unfold selectedBranchProjectionLipschitzConstant
  have hlen : (spectralContinuationWitness_of_circle D).contour.contourLength =
      2 * Real.pi * D.radius :=
    CircleContour.circleContour_contourLength _ hr
  have hnorm : ‖rieszNormalization‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_rieszNormalization, norm_inv]
    have h2pi : ‖((2 : ℂ) * Real.pi * Complex.I)‖ = 2 * Real.pi := by
      simp [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [h2pi]
  rw [hlen, hnorm]
  have hm : (D.margin : ℝ) ≠ 0 := D.margin_pos.ne'
  field_simp

end ContinuationBridge

section DirectRotationCompression

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {A E : H →L[ℂ] H} {s : Set ℝ}

/-- Concrete direct-rotation block algebra supplies the upper compression data
used in Theorem 8.1(i). -/
noncomputable def directRotationUpperCompressionData
    (C : SpectralContinuationWitness A E s) (alpha : ℝ) :
    DavisKahan1970.Section8.UpperCompressionRepulsionData
      (fun x : C.sourceSelectedSpectralSubspaceᗮ =>
        RCLike.re ⟪(x : H), A x⟫_ℂ)
      (fun x : C.sourceSelectedSpectralSubspaceᗮ =>
        RCLike.re ⟪(x : H), (A + E) x⟫_ℂ)
      (fun x : C.sourceSelectedSpectralSubspaceᗮ =>
        RCLike.re ⟪(x : H), (A + E) x⟫_ℂ)
      id id := by
  sorry

/-- Concrete direct-rotation block algebra supplies the lower compression data
used in Theorem 8.1(i). -/
noncomputable def directRotationLowerCompressionData
    (C : SpectralContinuationWitness A E s) (alpha : ℝ) :
    DavisKahan1970.Section8.LowerCompressionRepulsionData
      (fun x : C.sourceSelectedSpectralSubspace =>
        RCLike.re ⟪(x : H), A x⟫_ℂ)
      (fun x : C.sourceSelectedSpectralSubspace =>
        RCLike.re ⟪(x : H), (A + E) x⟫_ℂ)
      (fun x : C.sourceSelectedSpectralSubspace =>
        RCLike.re ⟪(x : H), (A + E) x⟫_ℂ)
      id id := by
  sorry

/-- Davis--Kahan 1970, Theorem 8.1(i), upper compression inequality, after
instantiating the abstract block certificate by the canonical direct rotation. -/
theorem theorem8_1_upperCompressionRepulsion_of_directRotation
    (C : SpectralContinuationWitness A E s) (alpha : ℝ)
    (hbranch : DavisKahan1970.Section8.SelectedBranchConclusion C) :
    ∀ x : C.sourceSelectedSpectralSubspaceᗮ,
      RCLike.re ⟪(x : H), A x⟫_ℂ - alpha * ‖x‖ ^ 2 ≤
        RCLike.re ⟪(x : H), (A + E) x⟫_ℂ - alpha * ‖x‖ ^ 2 := by
  sorry

/-- Davis--Kahan 1970, Theorem 8.1(i), lower compression companion. -/
theorem theorem8_1_lowerCompressionRepulsion_of_directRotation
    (C : SpectralContinuationWitness A E s) (alpha : ℝ)
    (hbranch : DavisKahan1970.Section8.SelectedBranchConclusion C) :
    ∀ x : C.sourceSelectedSpectralSubspace,
      alpha * ‖x‖ ^ 2 - RCLike.re ⟪(x : H), A x⟫_ℂ ≤
        alpha * ‖x‖ ^ 2 - RCLike.re ⟪(x : H), (A + E) x⟫_ℂ := by
  sorry

end DirectRotationCompression

section SourceTheorems

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {A E : H →L[ℂ] H} {s : Set ℝ}

/-- Full source-level conclusion currently expected from Davis--Kahan Theorem
8.1.  The compression inequalities are kept explicit rather than hidden behind
an unconstrained certificate. -/
structure Theorem81SourceConclusion
    (C : SpectralContinuationWitness A E s) (a b delta : ℝ) : Prop where
  core : DavisKahan1970.Section8.Theorem81CoreConclusion C a b delta
  upper_compression :
    ∀ x : C.sourceSelectedSpectralSubspaceᗮ,
      RCLike.re ⟪(x : H), A x⟫_ℂ - a * ‖x‖ ^ 2 ≤
        RCLike.re ⟪(x : H), (A + E) x⟫_ℂ - a * ‖x‖ ^ 2
  lower_compression :
    ∀ x : C.sourceSelectedSpectralSubspace,
      b * ‖x‖ ^ 2 - RCLike.re ⟪(x : H), A x⟫_ℂ ≤
        b * ‖x‖ ^ 2 - RCLike.re ⟪(x : H), (A + E) x⟫_ℂ

/-- Davis--Kahan 1970, Theorem 8.1 assembled from a common-circle
continuation, oriented spectral placement, and direct-rotation compression
algebra. -/
theorem theorem8_1_selectedBranch_and_spectralRepulsion
    (D : CircleContinuationData A E s) {a b delta : ℝ}
    (hsmall : D.radius * ‖E‖ / D.margin ^ 2 < Real.sqrt 2 / 2)
    (hgap : a + delta ≤ b)
    (h0 : SpectrumIn (A + E)
      (spectralContinuationWitness_of_circle D).targetSelectedSpectralSubspace
      (Set.Iic a))
    (h1 : SpectrumIn (A + E)
      (spectralContinuationWitness_of_circle D).targetSelectedSpectralSubspaceᗮ
      (Set.Ici b)) :
    Theorem81SourceConclusion
      (spectralContinuationWitness_of_circle D) a b delta := by
  sorry

/-- Construct the perturbation half-gap bridge required by Theorem 8.2. -/
noncomputable def perturbationHalfGapBridge_of_sourceHypotheses
    (D : CircleContinuationData A E s) {delta : ℝ}
    (hdelta : 0 < delta) (hsmall : ‖E‖ < delta / 2) :
    DavisKahan1970.Section8.PerturbationHalfGapBridge
      (spectralContinuationWitness_of_circle D) delta := by
  sorry

/-- Construct the residual half-gap bridge by the Krein replacement argument. -/
noncomputable def residualHalfGapBridge_of_sourceHypotheses
    (D : CircleContinuationData A E s) (R : F →L[ℂ] H) {delta : ℝ}
    (hdelta : 0 < delta) (hsmall : ‖R‖ < delta / 2) :
    DavisKahan1970.Section8.ResidualHalfGapBridge
      (spectralContinuationWitness_of_circle D) R delta := by
  sorry

/-- Davis--Kahan 1970, Theorem 8.2, perturbation-smallness alternative. -/
theorem theorem8_2_perturbationHalfGap_selectedBranch
    (D : CircleContinuationData A E s) {delta : ℝ}
    (hdelta : 0 < delta) (hsmall : ‖E‖ < delta / 2) :
    DavisKahan1970.Section8.SelectedBranchConclusion
      (spectralContinuationWitness_of_circle D) := by
  sorry

/-- Davis--Kahan 1970, Theorem 8.2, residual-smallness alternative. -/
theorem theorem8_2_residualHalfGap_selectedBranch
    (D : CircleContinuationData A E s) (R : F →L[ℂ] H) {delta : ℝ}
    (hdelta : 0 < delta) (hsmall : ‖R‖ < delta / 2) :
    DavisKahan1970.Section8.SelectedBranchConclusion
      (spectralContinuationWitness_of_circle D) := by
  sorry

end SourceTheorems

end Section8
end Frontier
end Experimental
end DavisKahan
end ForMathlib
