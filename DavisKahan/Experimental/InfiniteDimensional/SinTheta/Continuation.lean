/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.DoubleAngle
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.Resolvent

/-!
# Spectral projection continuation and branch selection

The analytic input is norm continuity of a Riesz projection along a path of
self-adjoint operators while a fixed contour stays in the common resolvent set.
The topological input is that nearby orthogonal projections have unitarily
equivalent ranges.  These two facts let a spectral component be followed without
silently identifying the moving component with a fixed subset of the real line.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Linear perturbation path. -/
def operatorPath (A H : E →L[𝕜] E) (t : ℝ) : E →L[𝕜] E :=
  A + (t : 𝕜) • H

/-- Continued Riesz projection selected by a fixed separating contour. -/
noncomputable def continuedProjection (A H : E →L[𝕜] E)
    (contour : ℝ → 𝕜) (t : ℝ) : E →L[𝕜] E :=
  rieszProjection (operatorPath A H t) contour

/-- A quantitative local estimate for a continued Riesz projection.

If the contour has length `L`, both resolvents are bounded by `M`, and the
operator path changes by `|t-u| ‖H‖`, the second resolvent identity gives the
stated Lipschitz bound.  This is the analytic heart of continuation. -/
theorem norm_continuedProjection_sub_le
    (A H : E →L[𝕜] E) (contour : ℝ → 𝕜)
    {t u L M : ℝ}
    (hrect : Contour.Rectifiable contour)
    (hlength : Contour.length contour ≤ L)
    (hM : ∀ r ∈ Set.uIcc t u, ∀ z ∈ Set.range contour,
      InResolventSet (operatorPath A H r) z ∧
        ‖resolventOperator (operatorPath A H r) z‖ ≤ M) :
    ‖continuedProjection A H contour t -
        continuedProjection A H contour u‖ ≤
      (L / (2 * Real.pi)) * M^2 * |t-u| * ‖H‖ := by
  classical
  unfold continuedProjection rieszProjection
  have hres : ∀ z ∈ Set.range contour,
      resolventOperator (operatorPath A H t) z -
          resolventOperator (operatorPath A H u) z =
        resolventOperator (operatorPath A H t) z ∘L
          ((u-t : ℝ) : 𝕜) • H ∘L
            resolventOperator (operatorPath A H u) z := by
    intro z hz
    rw [resolvent_perturbation_identity]
    · congr 2
      simp [operatorPath, sub_eq_add_neg]
      module
    · exact (hM t (Set.left_mem_uIcc) z hz).1
    · exact (hM u (Set.right_mem_uIcc) z hz).1
  rw [← Contour.integral_sub]
  apply le_trans (norm_smul_le _ _)
  apply le_trans (Contour.norm_integral_le_length_mul_sup hrect hlength)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  intro z hz
  rw [hres z hz]
  calc
    ‖resolventOperator (operatorPath A H t) z ∘L
        ((u-t : ℝ) : 𝕜) • H ∘L
          resolventOperator (operatorPath A H u) z‖
        ≤ M * (|u-t| * ‖H‖) * M := by
          gcongr
          · exact (hM t Set.left_mem_uIcc z hz).2
          · simp [norm_smul, abs_sub_comm]
          · exact (hM u Set.right_mem_uIcc z hz).2
    _ = M^2 * |t-u| * ‖H‖ := by
      rw [abs_sub_comm]
      ring

/-- Norm continuity of the selected projection path on the interval on which
one contour stays separating. -/
theorem continuous_continuedProjection
    (A H : E →L[𝕜] E) (s : Set ℝ) (contour : ℝ → 𝕜)
    (hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContourSeparatesSpectrum (operatorPath A H t) s contour) :
    ContinuousOn (continuedProjection A H contour) (Set.Icc (0 : ℝ) 1) := by
  classical
  intro t ht
  obtain ⟨hclosed, hrect, hres, M, hM0, hM, hinside, houtside⟩ := hsep t ht
  have hlocal : ∃ ε > 0, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |u-t| < ε → ∀ z ∈ Set.range contour,
        InResolventSet (operatorPath A H u) z ∧
          ‖resolventOperator (operatorPath A H u) z‖ ≤ 2 * max M 1 := by
    exact uniform_resolvent_neighborhood_along_linear_path
      A H contour t ht hres hrect hM
  obtain ⟨ε, hε, hlocal⟩ := hlocal
  refine continuousWithinAt_of_dist_le
    (C := (Contour.length contour / (2 * Real.pi)) *
      (2 * max M 1)^2 * ‖H‖) hε ?_
  intro u hu hut
  have hsegment : Set.uIcc t u ⊆ Set.Icc (0 : ℝ) 1 :=
    Set.uIcc_subset_Icc hu ht
  have hbound : ∀ r ∈ Set.uIcc t u, ∀ z ∈ Set.range contour,
      InResolventSet (operatorPath A H r) z ∧
        ‖resolventOperator (operatorPath A H r) z‖ ≤ 2 * max M 1 := by
    intro r hr z hz
    exact hlocal r (hsegment hr) z hz (by
      exact lt_of_le_of_lt (abs_sub_le_of_mem_uIcc hr) hut)
  simpa [dist_eq, abs_sub_comm, mul_assoc] using
    norm_continuedProjection_sub_le A H contour hrect le_rfl hbound

/-- Two orthogonal projections belong to the same norm-continuous component. -/
def SameProjectionComponent (P Q : E →L[𝕜] E) : Prop :=
  ∃ path : ℝ → E →L[𝕜] E,
    ContinuousOn path (Set.Icc (0 : ℝ) 1) ∧ path 0 = P ∧ path 1 = Q ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, IsOrthogonalProjection (path t)

/-- The continued projection remains in the component selected at `t = 0`. -/
theorem continuedProjection_same_component
    (A H : E →L[𝕜] E) (contour : ℝ → 𝕜)
    (hcontinuous : ContinuousOn (continuedProjection A H contour)
      (Set.Icc (0 : ℝ) 1))
    (hproj : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsOrthogonalProjection (continuedProjection A H contour t)) :
    SameProjectionComponent
      (continuedProjection A H contour 0)
      (continuedProjection A H contour 1) :=
  ⟨continuedProjection A H contour, hcontinuous, rfl, rfl, hproj⟩

/-- At an endpoint, a separating Riesz projection is the Borel spectral
projection selected by the contour. -/
theorem continuedProjection_eq_spectralProjection
    (A H : E →L[𝕜] E) (hA : IsSelfAdjointOperator A)
    (hH : IsSelfAdjointOperator H) (s : Set ℝ) (hs : MeasurableSet s)
    (contour : ℝ → 𝕜)
    (hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContourSeparatesSpectrum (operatorPath A H t) s contour) :
    continuedProjection A H contour 1 = spectralProjection (A + H) s := by
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hself : IsSelfAdjointOperator (operatorPath A H 1) := by
    simpa [operatorPath] using hA.add hH
  calc
    continuedProjection A H contour 1 =
        rieszProjection (operatorPath A H 1) contour := rfl
    _ = spectralProjection (operatorPath A H 1) s :=
      rieszProjection_eq_spectralProjection
        (operatorPath A H 1) hself s hs contour (hsep 1 h1)
    _ = spectralProjection (A + H) s := by simp [operatorPath]

/-- Norm-close orthogonal projections are intertwined by a canonical unitary.

The proof uses the invertible canonical intertwiner
`S = QP + (1-Q)(1-P)`.  The inequality `‖1-S‖ ≤ ‖P-Q‖ < 1` makes `S`
invertible.  Its polar factor is unitary and intertwines `P` and `Q`. -/
theorem range_equiv_of_projection_norm_lt_one
    (P Q : E →L[𝕜] E)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (hclose : ‖P - Q‖ < 1) :
    ∃ W : E →L[𝕜] E, IsUnitaryOperator W ∧ W ∘L P = Q ∘L W := by
  classical
  let S : E →L[𝕜] E := Q ∘L P + (1-Q) ∘L (1-P)
  have hSP : S ∘L P = Q ∘L S := by
    dsimp [S]
    noncomm_ring [hP.1, hQ.1]
  have hfactor : S - 1 = (Q-P) ∘L (2 • P - 1) := by
    dsimp [S]
    noncomm_ring [hP.1]
  have hreflection : IsUnitaryOperator (2 • P - 1) :=
    orthogonalProjection_reflection_unitary hP
  have hnorm : ‖1-S‖ ≤ ‖P-Q‖ := by
    rw [show 1-S = -(S-1) by abel, norm_neg, hfactor]
    calc
      ‖(Q-P) ∘L (2 • P-1)‖ ≤ ‖Q-P‖ * ‖2 • P-1‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖P-Q‖ := by
        rw [hreflection.norm_eq_one, mul_one]
        simpa [show Q-P = -(P-Q) by abel]
  let Su : (E →L[𝕜] E)ˣ := Units.oneSub (1-S) (hnorm.trans_lt hclose)
  let Aabs : E →L[𝕜] E :=
    RCLikeContinuousFunctionalCalculus.sqrt (star S ∘L S)
  have hAabs_unit : IsUnit Aabs :=
    sqrt_isUnit_of_isUnit_star_mul_self Su.isUnit
  let Au : (E →L[𝕜] E)ˣ := hAabs_unit.unit
  let W : E →L[𝕜] E := S ∘L (↑Au⁻¹ : E →L[𝕜] E)
  have hgram_comm : Commute (star S ∘L S) P := by
    rw [commute_iff_eq]
    have hstar := congrArg star hSP
    simp only [star_mul, hP.2.star_eq, hQ.2.star_eq] at hstar
    noncomm_ring [hSP, hstar]
  have habs_comm : Commute Aabs P :=
    RCLikeContinuousFunctionalCalculus.sqrt_commute hgram_comm
  have hWint : W ∘L P = Q ∘L W := by
    dsimp [W]
    rw [ContinuousLinearMap.comp_assoc, habs_comm.isUnit_inv_commute hAabs_unit,
      ← ContinuousLinearMap.comp_assoc, hSP, ContinuousLinearMap.comp_assoc]
  have hWunit : IsUnitaryOperator W := by
    dsimp [W Aabs Au]
    exact polar_factor_unitary_of_isUnit Su.isUnit
  exact ⟨W, hWunit, hWint⟩

end DavisKahanExt
end ForMathlib
