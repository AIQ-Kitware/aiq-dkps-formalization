/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Riccati.Bounded
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.Continuation

/-!
# Off-diagonal perturbations, `tan Θ`, and `tan 2Θ`

This file follows a moving spectral component by a contour rather than by a
fixed real set.  The contour datum records the selected component at every
point of the path and is the bridge between spectral enclosure, Riesz
continuation, and the contractive Riccati branch.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Complete branch-selection data for the path `A+tH`.

The sets `component t` are labels for the spectral component enclosed by one
fixed contour.  Only `component 0` is prescribed; the endpoint set is allowed
to move with the spectrum. -/
structure ContinuedSpectralDatum (A H : E →L[𝕜] E) (s : Set ℝ) : Type _ where
  hA : IsSelfAdjointOperator A
  hH : IsSelfAdjointOperator H
  contour : ℝ → 𝕜
  component : ℝ → Set ℝ
  component_measurable : ∀ t ∈ Set.Icc (0 : ℝ) 1, MeasurableSet (component t)
  component_zero : component 0 = s
  separates : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ContourSeparatesSpectrum (operatorPath A H t) (component t) contour

/-- The endpoint subspace selected by continuation.  The definition is total:
when no branch datum exists it returns the zero subspace. -/
noncomputable def continuedSpectralSubspace (A H : E →L[𝕜] E)
    (s : Set ℝ) : Submodule 𝕜 E := by
  classical
  by_cases h : Nonempty (ContinuedSpectralDatum A H s)
  · let D := Classical.choice h
    exact LinearMap.range
      (continuedProjection A H D.contour 1).toLinearMap
  · exact ⊥

/-- The endpoint Riesz projection supplied by continuation is orthogonal. -/
theorem continuedProjection_isOrthogonalProjection
    {A H : E →L[𝕜] E} {s : Set ℝ}
    (D : ContinuedSpectralDatum A H s) :
    IsOrthogonalProjection (continuedProjection A H D.contour 1) := by
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hself : IsSelfAdjointOperator (operatorPath A H 1) := by
    simpa [operatorPath] using D.hA.add D.hH
  have heq := rieszProjection_eq_spectralProjection
    (operatorPath A H 1) hself (D.component 1)
    (D.component_measurable 1 h1) D.contour (D.separates 1 h1)
  rw [continuedProjection, heq]
  exact spectralProjection_isOrthogonalProjection _ _

noncomputable instance continuedSpectralSubspace_hasOrthogonalProjection
    (A H : E →L[𝕜] E) (s : Set ℝ) :
    (continuedSpectralSubspace A H s).HasOrthogonalProjection := by
  classical
  by_cases h : Nonempty (ContinuedSpectralDatum A H s)
  · let D := Classical.choice h
    have hp := continuedProjection_isOrthogonalProjection D
    rw [continuedSpectralSubspace, dif_pos h]
    exact hp.range_hasOrthogonalProjection
  · rw [continuedSpectralSubspace, dif_neg h]
    infer_instance

/-- Under the finite-gap off-diagonal hypothesis there is a single contour
that follows the initial spectral component for the whole path. -/
theorem exists_continuedSpectralDatum_of_offDiagonal
    {A H : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hH : IsSelfAdjointOperator H)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {d : ℝ} (hd : 0 < d)
    (hfinite : FiniteGapConfiguration A U d)
    (hsmall : ‖H‖ < Real.sqrt 2 * d) :
    Nonempty (ContinuedSpectralDatum A H (restrictedSpectrum A U)) := by
  classical
  obtain ⟨a, b, hab, hUab, hUc⟩ := hfinite
  let ρ : ℝ → ℝ := fun t =>
    Real.sqrt ((d/2)^2 + (t * ‖H‖)^2) - d/2
  have hρ : ∀ t ∈ Set.Icc (0 : ℝ) 1, 2 * ρ t < d := by
    intro t ht
    exact offDiagonal_shift_twice_lt_gap hd hsmall ht
  obtain ⟨Γ, hΓclosed, hΓrect, hΓbetween⟩ :=
    exists_rectangular_contour_between_moving_enclosures
      a b d ρ hab hρ
  let component : ℝ → Set ℝ := fun t =>
    {λ | Contour.index Γ (λ : 𝕜) = 1}
  have hmeas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      MeasurableSet (component t) := by
    intro t ht
    exact measurableSet_contour_index_eq Γ 1
  have hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContourSeparatesSpectrum (operatorPath A H t) (component t) Γ := by
    intro t ht
    have henclosure := offDiagonal_spectral_enclosure_path
      hA hH hU hoff hd hUab hUc t ht
    exact contourSeparatesSpectrum_of_enclosures
      hΓclosed hΓrect (hΓbetween t ht) henclosure
  have hzero : component 0 = restrictedSpectrum A U := by
    ext λ
    exact contour_index_initial_component_iff
      hA hU hUab hUc hΓbetween λ
  exact ⟨⟨hA, hH, Γ, component, hmeas, hzero, hsep⟩⟩

/-- Off-diagonal perturbations preserve the selected gap below the sharp
`√2 d` branch threshold. -/
theorem gap_preserved_of_offDiagonal
    {A H : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hH : IsSelfAdjointOperator H)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {d : ℝ} (hd : 0 < d)
    (hU_spec : (restrictedSpectrum A U).Nonempty)
    (hUc_spec : (restrictedSpectrum A Uᗮ).Nonempty)
    (hfinite : FiniteGapConfiguration A U d)
    (hsmall : ‖H‖ < Real.sqrt 2 * d) :
    let V := continuedSpectralSubspace A H (restrictedSpectrum A U)
    Reduces (A + H) V ∧ IsAcute U V ∧
      0 < spectralDistance (restrictedSpectrum (A + H) V)
        (restrictedSpectrum (A + H) Vᗮ) := by
  classical
  let hdatum := exists_continuedSpectralDatum_of_offDiagonal
    hA hH hU hoff hd hfinite hsmall
  let D := Classical.choice hdatum
  let V := continuedSpectralSubspace A H (restrictedSpectrum A U)
  have hVrange : V = LinearMap.range
      (continuedProjection A H D.contour 1).toLinearMap := by
    simp [V, continuedSpectralSubspace, hdatum, D]
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hendpoint : continuedProjection A H D.contour 1 =
      spectralProjection (A+H) (D.component 1) := by
    simpa [operatorPath] using continuedProjection_eq_spectralProjection
      A H hA hH (D.component 1) (D.component_measurable 1 h1)
      D.contour D.separates
  have hVred : Reduces (A+H) V := by
    rw [hVrange, hendpoint]
    exact spectralSubspace_reduces (A+H) (hA.add hH) (D.component 1)
  have hcont := continuous_continuedProjection
    A H (D.component 0) D.contour (by
      intro t ht
      simpa [D.component_zero] using D.separates t ht)
  have hacute : IsAcute U V := by
    have hP0 : continuedProjection A H D.contour 0 = projection U := by
      have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
      rw [continuedProjection_eq_spectralProjection
        A H hA hH (D.component 0) (D.component_measurable 0 h0)
        D.contour D.separates, D.component_zero]
      exact spectralProjection_restrictedSpectrum_eq_projection hA hU
    have hP1 : continuedProjection A H D.contour 1 = projection V := by
      rw [hVrange]
      exact orthogonalProjection_range_eq_self
        (continuedProjection_isOrthogonalProjection D)
    rw [IsAcute, subspaceGap, ← hP0, ← hP1]
    exact offDiagonal_continued_projection_gap_lt_one
      hA hH hU hoff hd hfinite hsmall D hcont
  have hdist : 0 < spectralDistance
      (restrictedSpectrum (A+H) V) (restrictedSpectrum (A+H) Vᗮ) := by
    obtain ⟨a, b, hab, hUa, hUc⟩ := hfinite
    have henclosure := offDiagonal_endpoint_enclosures
      hA hH hU hoff hd hfinite hsmall D hU_spec hUc_spec
    exact spectralDistance_pos_of_disjoint_closed_enclosures henclosure
  exact ⟨hVred, hacute, hdist⟩

/-- Generalized `tan 2Θ` theorem for an off-diagonal perturbation. -/
theorem tanTwoTheta_offDiagonal
    {A H : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hH : IsSelfAdjointOperator H)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces (A + H) V)
    (hoff : IsOffDiagonal U H)
    {d : ℝ} (hd : 0 < d) (hgap : OrderedInternalGap A U d)
    (hquarter : IsQuarterAcute U V) :
    ‖tanTwoAngleOperator U V hquarter‖ ≤ 2 * ‖H‖ / d := by
  classical
  obtain ⟨X, hVgraph, hXunique⟩ :=
    existsUnique_angularOperator U V hquarter.isAcute
  have hric : RiccatiEquation
      (diagonalBlock U A) (diagonalBlock Uᗮ A)
      (offDiagonalBlock U Uᗮ H) X := by
    exact riccatiEquation_of_graph_reduces
      hA hH hU hV hoff hVgraph
  have hdouble :
      sylvesterOperator (diagonalBlock Uᗮ A) (diagonalBlock U A)
        (twoAngleTransform X) =
      2 • offDiagonalBlock U Uᗮ H := by
    exact twoAngle_sylvester_identity_of_riccati hric hquarter
  have hsep := orderedInternalGap_diagonalBlocks hgap
  have hbound := norm_sylvester_le_of_ordered_spectra
    (diagonalBlock Uᗮ A) (diagonalBlock U A)
    (twoAngleTransform X) (2 • offDiagonalBlock U Uᗮ H)
    hd hsep hdouble
  have hidentify : ‖tanTwoAngleOperator U V hquarter‖ =
      ‖twoAngleTransform X‖ := by
    exact norm_tanTwoAngleOperator_graph hVgraph hquarter
  rw [hidentify]
  calc
    ‖twoAngleTransform X‖ ≤ ‖2 • offDiagonalBlock U Uᗮ H‖ / d := hbound
    _ ≤ 2 * ‖H‖ / d := by
      gcongr
      simpa [norm_smul] using
        offDiagonalBlock_norm_le (U := U) (T := H)

/-- A priori `tan Θ` theorem in the finite-gap configuration. -/
theorem aPrioriTanTheta
    {A H : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hH : IsSelfAdjointOperator H)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {d : ℝ} (hd : 0 < d)
    (hU_spec : (restrictedSpectrum A U).Nonempty)
    (hUc_spec : (restrictedSpectrum A Uᗮ).Nonempty)
    (hfinite : FiniteGapConfiguration A U d)
    (hsmall : ‖H‖ < Real.sqrt 2 * d) :
    let V := continuedSpectralSubspace A H (restrictedSpectrum A U)
    subspaceGap U V ≤ Real.sin (Real.arctan (‖H‖ / d)) := by
  classical
  let V := continuedSpectralSubspace A H (restrictedSpectrum A U)
  obtain ⟨hV, hacute, hsepV⟩ := gap_preserved_of_offDiagonal
    hA hH hU hoff hd hU_spec hUc_spec hfinite hsmall
  obtain ⟨X, hgraph, hXunique⟩ := existsUnique_angularOperator U V hacute
  have hric := riccatiEquation_of_graph_reduces
    hA hH hU hV hoff hgraph
  have hmajorant : d * ‖X‖ ≤ ‖H‖ := by
    exact riccati_contracting_branch_majorant
      hA hH hU hoff hd hfinite hsmall hric hgraph
  have hX : ‖X‖ ≤ ‖H‖ / d := by
    exact (le_div_iff₀ hd).2 hmajorant
  have hgapgraph : subspaceGap U V = ‖X‖ / Real.sqrt (1 + ‖X‖^2) :=
    subspaceGap_graphSubspace hgraph
  rw [hgapgraph, Real.sin_arctan]
  exact div_le_div_of_nonneg_right
    (monotone_x_div_sqrt_one_add_sq hX (norm_nonneg X)) (by positivity)

/-- Spectral repulsion: the two continued components move away from the
original ordered gap. -/
theorem spectral_repulsion_offDiagonal
    {A H : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hH : IsSelfAdjointOperator H)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {d : ℝ} (hd : 0 < d) (hordered : OrderedInternalGap A U d)
    (hU_spec : (restrictedSpectrum A U).Nonempty)
    (hUc_spec : (restrictedSpectrum A Uᗮ).Nonempty)
    (hfinite : FiniteGapConfiguration A U d)
    (hsmall : ‖H‖ < Real.sqrt 2 * d) :
    spectralDistance (restrictedSpectrum (A + H)
      (continuedSpectralSubspace A H (restrictedSpectrum A U)))
      (restrictedSpectrum (A + H)
        (continuedSpectralSubspace A H (restrictedSpectrum A U))ᗮ) ≥
      spectralDistance (restrictedSpectrum A U) (restrictedSpectrum A Uᗮ) := by
  classical
  let V := continuedSpectralSubspace A H (restrictedSpectrum A U)
  obtain ⟨hV, hacute, hdist⟩ := gap_preserved_of_offDiagonal
    hA hH hU hoff hd hU_spec hUc_spec hfinite hsmall
  obtain ⟨X, hgraph, hXunique⟩ := existsUnique_angularOperator U V hacute
  have hric := riccatiEquation_of_graph_reduces
    hA hH hU hV hoff hgraph
  obtain ⟨L, R, hdiag, hLorder, hRorder⟩ :=
    riccati_blockDiagonalization hA hH hU hV hoff hgraph hric
  have hleft := spectrum_mono_of_selfAdjoint_le hLorder
  have hright := spectrum_mono_of_selfAdjoint_le hRorder
  have horiented := orderedInternalGap_orient hordered
  exact spectralDistance_mono_of_oriented_enclosures
    hU_spec hUc_spec horiented hdiag hleft hright

end DavisKahanExt
end ForMathlib
