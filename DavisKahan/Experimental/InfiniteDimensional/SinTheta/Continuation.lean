/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Experimental.InfiniteDimensional.DoubleAngle
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.DirectRotationAPI
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.Resolvent

/-!
# Spectral projection continuation and branch selection

Literature writeup: local TeX, Sections 15 and 20--24.  The infinite-
dimensional tangent theorems require selecting the perturbed spectral
component by a norm-continuous path of Riesz projections.
-/


/-! ## Weak-agent execution plan: continuation

Split this module into a local analytic theorem and a global topological
argument.

Local theorem: under a fixed separating contour and a uniform resolvent bound,
prove norm continuity of the Riesz projection from the second resolvent
identity.  State a quantitative Lipschitz estimate; continuity is its
corollary.

Global theorem: for a continuous path of projections `P t`, prove rank or
component constancy.  In finite dimension use `‖P-Q‖ < 1` to construct an
isomorphism between the ranges.  In infinite dimension use the same estimate
to obtain the graph representation.  Cover the parameter interval by local
neighborhoods and use connectedness/clopen reasoning.

Keep the spectral identification separate: show the continued Riesz
projection equals the requested spectral projection only after the path
argument.  This prevents a cycle between continuity and spectral selection.
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


omit [CompleteSpace E] in
/-- Difference of two points on the affine perturbation path. -/
theorem operatorPath_sub
    (A H : E →L[𝕜] E) (t u : ℝ) :
    operatorPath A H t - operatorPath A H u =
      ((t - u : ℝ) : 𝕜) • H := by
  calc
    operatorPath A H t - operatorPath A H u =
        (t : 𝕜) • H - (u : 𝕜) • H := by
      simp only [operatorPath]
      abel
    _ = ((t : 𝕜) - (u : 𝕜)) • H := by
      rw [sub_smul]
    _ = ((t - u : ℝ) : 𝕜) • H := by
      rw [RCLike.ofReal_sub]

omit [CompleteSpace E] in
/-- Exact norm of an affine-path increment. -/
theorem norm_operatorPath_sub
    (A H : E →L[𝕜] E) (t u : ℝ) :
    ‖operatorPath A H t - operatorPath A H u‖ = ‖t - u‖ * ‖H‖ := by
  rw [operatorPath_sub, norm_smul, RCLike.norm_ofReal, Real.norm_eq_abs]

/-- Quantitative path-parameter estimate for the resolvent at one fixed
spectral parameter.  Under a uniform bound `M` at two path values, the
resolvent varies at most linearly in `|t-u|`.

This is the analytic operator estimate to be integrated along a separating
contour in the proof of `continuous_continuedProjection`. -/
theorem norm_resolventOperator_operatorPath_sub_le
    (A H : E →L[𝕜] E) (z : 𝕜) (M : ℝ) (t u : ℝ)
    (ht : InResolventSet (operatorPath A H t) z)
    (hu : InResolventSet (operatorPath A H u) z)
    (hMt : ‖resolventOperator (operatorPath A H t) z‖ ≤ M)
    (hMu : ‖resolventOperator (operatorPath A H u) z‖ ≤ M) :
    ‖resolventOperator (operatorPath A H t) z -
        resolventOperator (operatorPath A H u) z‖ ≤
      M ^ 2 * ‖H‖ * ‖t - u‖ := by
  calc
    ‖resolventOperator (operatorPath A H t) z -
        resolventOperator (operatorPath A H u) z‖ ≤
      M * ‖operatorPath A H u - operatorPath A H t‖ * M :=
        norm_resolventOperator_sub_le_of_bounds
          (operatorPath A H u) (operatorPath A H t) hu ht hMu hMt
    _ = M * (‖u - t‖ * ‖H‖) * M := by
      rw [norm_operatorPath_sub]
    _ = M ^ 2 * ‖H‖ * ‖t - u‖ := by
      rw [norm_sub_rev]
      ring

/-- Set-uniform version of the fixed-parameter resolvent estimate. -/
theorem norm_resolventOperator_operatorPath_sub_le_of_uniform_bound
    (A H : E →L[𝕜] E) (z : 𝕜) (M : ℝ) (I : Set ℝ)
    (hmem : ∀ t ∈ I, InResolventSet (operatorPath A H t) z)
    (hbound : ∀ t ∈ I,
      ‖resolventOperator (operatorPath A H t) z‖ ≤ M)
    {t u : ℝ} (ht : t ∈ I) (hu : u ∈ I) :
    ‖resolventOperator (operatorPath A H t) z -
        resolventOperator (operatorPath A H u) z‖ ≤
      M ^ 2 * ‖H‖ * ‖t - u‖ :=
  norm_resolventOperator_operatorPath_sub_le A H z M t u
    (hmem t ht) (hmem u hu) (hbound t ht) (hbound u hu)


/-! ## Complex spectral-distance specialization -/

section ComplexResolventDistance

variable {Hc : Type*} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc]
  [CompleteSpace Hc]

/-- Along a complex self-adjoint affine path, a common positive distance from
one spectral parameter to every path spectrum supplies the endpoint
resolvent-set and norm hypotheses automatically. -/
theorem norm_resolventOperator_operatorPath_sub_le_of_spectral_distance
    (A H : Hc →L[ℂ] Hc) (z : ℂ) (delta : ℝ) (hdelta : 0 < delta)
    (I : Set ℝ)
    (hself : ∀ t ∈ I, IsSelfAdjointOperator (operatorPath A H t))
    (hsep : ∀ t ∈ I, ∀ lam ∈ realSpectrum (operatorPath A H t),
      delta ≤ ‖z - (lam : ℂ)‖)
    {t u : ℝ} (ht : t ∈ I) (hu : u ∈ I) :
    ‖resolventOperator (operatorPath A H t) z -
        resolventOperator (operatorPath A H u) z‖ ≤
      delta⁻¹ ^ 2 * ‖H‖ * ‖t - u‖ := by
  obtain ⟨htmem, htbound⟩ :=
    complex_inResolventSet_and_norm_resolvent_le_inv_distance
      (operatorPath A H t) (hself t ht) z delta hdelta (hsep t ht)
  obtain ⟨humem, hubound⟩ :=
    complex_inResolventSet_and_norm_resolvent_le_inv_distance
      (operatorPath A H u) (hself u hu) z delta hdelta (hsep u hu)
  exact norm_resolventOperator_operatorPath_sub_le A H z delta⁻¹ t u
    htmem humem htbound hubound

end ComplexResolventDistance

/-- Continued spectral projection selected by a separating contour. -/
noncomputable def continuedProjection (A H : E →L[𝕜] E)
    (contour : ℝ → 𝕜) (t : ℝ) : E →L[𝕜] E :=
  rieszProjection (operatorPath A H t) contour

/-- Norm continuity of the selected projection path.

Proof strategy: fix a contour that remains uniformly inside the resolvent set.
Use the second resolvent identity to prove uniform norm continuity of
`z ↦ (z-A_t)⁻¹` in the path parameter, dominate the contour integrand by the
inverse distance to the spectrum, and pass continuity through the contour
Bochner integral.  Derive an explicit Lipschitz estimate when the contour
margin is quantitative.

Lean proof route for a weaker agent:

1. Use `norm_resolventOperator_operatorPath_sub_le_of_uniform_bound` pointwise on the contour.  The second-resolvent operator algebra and the exact affine-path increment are now fully proved.
2. Use `complex_continuousOn_resolventOperator_of_distance` for continuity in the contour parameter; the first-resolvent identity now supplies this from the same uniform spectral-distance margin.
3. Combine that continuity with a piecewise `C1` contour to obtain curve integrability and a uniform speed bound.
4. Pass the resulting Lipschitz estimate through the Bochner contour integral and assemble the pointwise statements into `ContinuousOn`.


Ext-agent signature audit (GPT 5.6 High): The corrected `ContinuousOn [0,1]` signature
asks only for separation on the path segment actually used. A global continuity theorem
remains available in the resolvent module.

Preferred dependency route: Use a uniformly separating Riesz contour on `[0,1]`,
norm-continuity of resolvents, and local equivalences of close projection ranges.
-/
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

omit [CompleteSpace E] in
/-- The continued projection remains in the component selected at `t = 0`.

Ext-agent signature audit (GPT 5.6 High): Correct after `SameProjectionComponent` was
localized to continuity on `[0,1]`; global continuity would be unnecessary
overstrengthening.
-/
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

/-- Continued Riesz projections select the spectral component born from the
initial component.

Lean proof route for a weaker agent:

1. Use `rieszProjection_eq_spectralProjection` at `t=1`, passing `hs`.
2. Verify that `operatorPath A H 1 = A+H` by `simp [operatorPath]`.
3. Specialize the uniformly separating-contour hypothesis at `1 ∈ [0,1]`.


Ext-agent signature audit (GPT 5.6 High): Correct with the explicit measurability
premise if the fixed contour encloses the same Borel spectral component throughout the
path. At `t=1`, self-adjointness follows from `hA` and `hH`.

Preferred dependency route: Use a uniformly separating Riesz contour on `[0,1]`,
norm-continuity of resolvents, and local equivalences of close projection ranges.
-/
theorem continuedProjection_eq_spectralProjection
    (A H : E →L[𝕜] E) (hA : IsSelfAdjointOperator A)
    (hH : IsSelfAdjointOperator H) (s : Set ℝ) (hs : MeasurableSet s)
    (contour : ℝ → 𝕜)
    (hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContourSeparatesSpectrum (operatorPath A H t) s contour) :
    continuedProjection A H contour 1 = spectralProjection (A + H) s := by
  have h1 : operatorPath A H 1 = A + H := by
    simp [operatorPath]
  have hA1 : IsSelfAdjointOperator (A + H) := by
    have h := hA.add hH
    rwa [← ContinuousLinearMap.toLinearMap_add] at h
  have hc := hsep 1 ⟨zero_le_one, le_refl 1⟩
  rw [h1] at hc
  unfold continuedProjection
  rw [h1]
  exact rieszProjection_eq_spectralProjection (A + H) hA1 s hs contour hc

/-! ## Close complex orthogonal projections

The direct-rotation package turns the local geometric step in spectral
continuation into a short theorem.  A projection supplied abstractly as an
idempotent symmetric continuous linear map is first identified with the
orthogonal projection onto its fixed-point subspace.  Norm closeness then says
those two fixed-point subspaces are acute, so their canonical direct rotation
is the required global unitary intertwiner.
-/

section ComplexCloseProjections

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Fixed-point subspace of a bounded operator.  For an orthogonal projection
this is its range, but the kernel presentation gives closedness and the
orthogonal-projection instance without a separate closed-range theorem. -/
private noncomputable def projectionFixedSpace
    (P : H →L[ℂ] H) : Submodule ℂ H :=
  (P - 1).ker

private noncomputable instance projectionFixedSpaceComplete
    (P : H →L[ℂ] H) : CompleteSpace (projectionFixedSpace P) :=
  (P - 1).isClosed_ker.completeSpace_coe

private noncomputable instance projectionFixedSpaceHasOrthogonalProjection
    (P : H →L[ℂ] H) :
    (projectionFixedSpace P).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

private theorem mem_projectionFixedSpace_iff
    (P : H →L[ℂ] H) (x : H) :
    x ∈ projectionFixedSpace P ↔ P x = x := by
  change (P - 1) x = 0 ↔ P x = x
  simp only [sub_apply, one_apply_eq_self, sub_eq_zero]

private theorem projection_apply_idempotent
    (P : H →L[ℂ] H) (hP : IsOrthogonalProjection P) (x : H) :
    P (P x) = P x := by
  have h := congrArg (fun T : H →L[ℂ] H => T x) hP.1
  simpa only [ContinuousLinearMap.comp_apply] using h

/-- An abstract orthogonal projection is the canonical orthogonal projection
onto its fixed-point/range subspace. -/
private theorem projection_fixedSpace_eq
    (P : H →L[ℂ] H) (hP : IsOrthogonalProjection P) :
    projection (projectionFixedSpace P) = P := by
  ext x
  apply (projectionFixedSpace P).eq_starProjection_of_mem_of_inner_eq_zero
  · rw [mem_projectionFixedSpace_iff]
    exact projection_apply_idempotent P hP x
  · intro y hy
    have hyfix : P y = y :=
      (mem_projectionFixedSpace_iff P y).mp hy
    have hsym : ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ :=
      hP.2 x y
    rw [inner_sub_left]
    calc
      ⟪x, y⟫_ℂ - ⟪P x, y⟫_ℂ = ⟪x, y⟫_ℂ - ⟪x, P y⟫_ℂ := by rw [hsym]
      _ = 0 := by rw [hyfix, sub_self]

/-- Norm-close complex orthogonal projections have unitarily equivalent ranges
and complements.  The unitary is the canonical acute direct rotation of their
fixed-point subspaces. -/
theorem range_equiv_of_projection_norm_lt_one
    (P Q : H →L[ℂ] H)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (hclose : ‖P - Q‖ < 1) :
    ∃ W : H →L[ℂ] H, IsUnitaryOperator W ∧ W ∘L P = Q ∘L W := by
  let U : Submodule ℂ H := projectionFixedSpace P
  let V : Submodule ℂ H := projectionFixedSpace Q
  have hPU : projection U = P := by
    simpa only [U] using projection_fixedSpace_eq P hP
  have hQV : projection V = Q := by
    simpa only [V] using projection_fixedSpace_eq Q hQ
  have hacute : IsAcute U V := by
    change ‖projection U - projection V‖ < 1
    rw [hPU, hQV]
    exact hclose
  let W : H →L[ℂ] H := complexDirectRotation U V hacute
  refine ⟨W, ?_, ?_⟩
  · simpa only [W] using complexDirectRotation_unitary U V hacute
  · have hintertwine := complexDirectRotation_intertwines U V hacute
    rw [hPU, hQV] at hintertwine
    simpa only [W] using hintertwine

end ComplexCloseProjections

end DavisKahanExt
end ForMathlib
