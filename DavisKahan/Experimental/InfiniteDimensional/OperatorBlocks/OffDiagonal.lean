/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.InfiniteDimensional.Riccati.Bounded
import DavisKahan.InfiniteDimensional.SinTheta.Continuation
import DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Off-diagonal perturbations, `tan Θ`, and `tan 2Θ`

Literature writeup: local TeX, Sections 21--24.  This covers gap preservation,
spectral enclosure, the generalized `tan 2Θ` theorem, and the sharp a priori
`tan Θ` theorem.
-/


/-! ## Construction plan

Construct `continuedSpectralSubspace` from a Riesz projection along the path
`A_t = A + t H`.  Prove the separating contour remains in the resolvent set
using the off-diagonal gap estimate, prove norm continuity of the projection,
and select the connected acute component beginning at the original subspace.
The finite version may use ordered eigenvalue continuity, but the bounded
version should use the resolvent/Riesz infrastructure.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Experimental.Foundation

open DavisKahan

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Spectral components born from an isolated component under an off-diagonal
perturbation. -/
noncomputable def continuedSpectralSubspace (A H : E →L[𝕜] E)
    (s : Set ℝ) : Submodule 𝕜 E := by
  classical
  by_cases h : Nonempty (ContinuedSpectralDatum A H s)
  · let D := Classical.choice h
    exact LinearMap.range
      (continuedProjection A H D.contour 1).toLinearMap
  · exact ⊥

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

/-- Off-diagonal perturbations preserve the separating gap below the sharp
`√2 d` threshold.

Proof strategy: first obtain enclosure of each perturbed spectral component
from the Schur complement or Riccati block diagonalization.  Show the two
enclosures remain disjoint under the scalar inequality `‖H‖ < sqrt 2 * d`.
Use norm-continuity of the Riesz projection along `A+tH` to rule out branch
switching, then identify the endpoint with the continued spectral subspace. 

Lean proof route for a weaker agent:

1. Use off-diagonal spectral enclosure to bound the two perturbed components on opposite sides of the original gap.
2. Check the scalar `sqrt 2` inequality leaves a positive distance between the enclosures.
3. Continue the Riesz projection along `A+tH` to select the correct component.
4. Prove reduction, acuteness, and positive endpoint spectral distance in that order.


Ext-agent signature audit (GPT 5.6 High): The nonempty block hypotheses are necessary
for the positive spectral-distance conclusion. The `√2 d` threshold belongs to
continuation/branch preservation, not to the local Riccati contraction theorem.

Preferred dependency route: Select the continued spectral branch first, prove
graph/Riccati control second, and isolate scalar threshold optimization from operator
arguments.
-/
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
    Reduces (A + H) V ∧ IsUniformlyAcute U V ∧
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
  have hacute : IsUniformlyAcute U V := by
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
    rw [IsUniformlyAcute, subspaceGap, ← hP0, ← hP1]
    exact offDiagonal_continued_projection_gap_lt_one
      hA hH hU hoff hd hfinite hsmall D hcont
  have hdist : 0 < spectralDistance
      (restrictedSpectrum (A+H) V) (restrictedSpectrum (A+H) Vᗮ) := by
    obtain ⟨a, b, hab, hUa, hUc⟩ := hfinite
    have henclosure := offDiagonal_endpoint_enclosures
      hA hH hU hoff hd hfinite hsmall D hU_spec hUc_spec
    exact spectralDistance_pos_of_disjoint_closed_enclosures henclosure
  exact ⟨hVred, hacute, hdist⟩

/-- Generalized `tan 2Θ` theorem. 

Lean proof route for a weaker agent:

1. Represent `V` as a graph over `U`; `hquarter` ensures the double-angle tangent is bounded.
2. Derive the Riccati equation from reduction of `A+H` and the off-diagonal form of `H`.
3. Apply the ordered gap to the linear Sylvester term and estimate the quadratic terms.
4. Translate the resulting bound on the angular operator to `tanTwoAngleOperator`.


Ext-agent signature audit (GPT 5.6 High): Correct only below the quarter-angle pole; the
proof argument is now passed to `tanTwoAngleOperator`, so the operator is not silently
totalized.

Preferred dependency route: Select the continued spectral branch first, prove
graph/Riccati control second, and isolate scalar threshold optimization from operator
arguments.
-/
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
    existsUnique_angularOperator U V hquarter.isUniformlyAcute
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

/-- A priori `tan Θ` theorem in the finite-gap configuration.

Proof strategy: select the continued spectral subspace and represent it as the
graph of the contractive Riccati solution `X`.  Combine spectral enclosure for
the perturbed diagonal blocks with the Riccati equation to obtain a scalar
quadratic inequality for `x = ‖X‖`.  Solve the majorant inequality on the
contractive branch and translate through

`‖P-Q‖ = x / sqrt(1+x^2)`.

The sharp `sqrt 2 * d` threshold is where the selected scalar branch ceases to
remain uniformly acute.  Keep the scalar optimization and trigonometric
identity in separate lemmas so the operator proof is mostly monotonicity. 

Lean proof route for a weaker agent:

1. Use `gap_preserved_of_offDiagonal` to obtain the continued reducing subspace and acuteness.
2. Apply `existsUnique_angularOperator` to represent that subspace as `graphSubspace U X`.
3. Derive the Riccati equation from graph invariance and use the finite-gap enclosure to obtain the scalar majorant for `‖X‖`.
4. Solve the scalar inequality on the contractive branch, then rewrite the projector gap with `tan_maximalAngle_eq_norm_angularOperator`.


Ext-agent signature audit (GPT 5.6 High): The added nonempty-spectrum hypotheses align
this theorem with `gap_preserved_of_offDiagonal`. The endpoint is the continued branch,
not an arbitrary reducing subspace of `A+H`.

Preferred dependency route: Select the continued spectral branch first, prove
graph/Riccati control second, and isolate scalar threshold optimization from operator
arguments.
-/
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

/-- Spectral repulsion: off-diagonal perturbations move the two components
away from the original gap. 

Lean proof route for a weaker agent:

1. Use the Riccati block diagonalization of the continued spectral subspace.
2. Express the effective diagonal blocks as the original blocks plus positive/negative Schur-complement corrections.
3. Apply spectral monotonicity to show the selected components move away from the original gap.
4. Convert the two enclosure inequalities into the stated spectral-distance comparison.


Ext-agent signature audit (GPT 5.6 High): Plausible only in the ordered configuration;
the explicit `OrderedInternalGap` and nonempty hypotheses are therefore essential. Prove
oriented enclosure inequalities before converting to set distance.

Preferred dependency route: Select the continued spectral branch first, prove
graph/Riccati control second, and isolate scalar threshold optimization from operator
arguments.
-/
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
end TauCeti