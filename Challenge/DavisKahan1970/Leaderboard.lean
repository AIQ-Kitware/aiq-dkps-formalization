/-
# Davis--Kahan 1970 exhibition leaderboard

This module exposes the production proofs corresponding to
`Challenge.DavisKahan1970.Conformance` and prints additional source-facing
results that make the scope and sharpness of the formalization visible.

Four comparator targets are intentionally absent from the production side.
The literal infinite-dimensional ambient `tan Theta` statement is challenged by
a source-hypothesis witness exhibiting a right-angle ambient component, which
shows that the crossed-defect condition (3.5) — introduced only in Section 3 and
standing thereafter — is a substantive qualification that the Section 2 display
does not carry.  It is a vacuity/nonvacuity witness, not a counterexample to the
counted result; the repository's reading of that printed statement is recorded
under `nonlocal_source_interpretation` for `S2-tan-theta` in
`dev/davis-kahan-1970-formalization-result-inventory.json`.  The directed residual `tan 2Theta` statement
still lacks one source-facing arbitrary-UI-norm wrapper from only the printed
hypotheses.  Finally, the newly proved ambient `tan 2Theta` inequality derives
pole exclusion internally, but its source-hypothesis pole theorem is not yet
exported as a public declaration for a signature-only semantic certificate.
The paper's unbounded extension of the directed `tan 2Theta` estimate also lacks
one arbitrary-source-UI wrapper that derives its cutoff/denominator assembly
from only the printed unbounded hypotheses.
-/
import DavisKahan.Sources.DavisKahan1970.PartIII
import DavisKahan.Sources.DavisKahan1970.FullSineTheta
import DavisKahan.Sources.DavisKahan1970.Directed
import DavisKahan.Sources.DavisKahan1970.DirectedReal
import DavisKahan.Sources.DavisKahan1970.TanThetaWholeSpace
import DavisKahan.Sources.DavisKahan1970.SinTwoThetaWholeSpace
import DavisKahan.Sources.DavisKahan1970.WholeSpaceReal
import DavisKahan.Sources.DavisKahan1970.TanTwoThetaBranchFree
import DavisKahan.Sources.DavisKahan1970.TanTwoThetaReflectionAmbient
import DavisKahan.BoundedOperator.Spectral.Complex
import DavisKahan.FiniteDimensional.DirectRotation.ShortRotationCounterexample
import DavisKahan.FiniteDimensional.Sharpness
import DavisKahan.Sources.DavisKahan1970.Section3Proposition32
import DavisKahan.Sources.DavisKahan1970.Section8.All
import DavisKahan.Sources.DavisKahan1970.Section9.All

namespace TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Comparator-facing spelling of the printed finite tangent interval hypotheses. -/
theorem partIII_tanTheta_source_uiNorm
    (N : RectangularUnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) (hrank : finrank 𝕜 F = finrank 𝕜 U)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hMspec : SpectrumIn (compression A X) ⊤ (Set.Icc β α))
    (hAspec : SpectrumIn A Uᗮ (Set.Ici (α + δ)))
    (tanTheta0 : F →ₗ[𝕜] E)
    (htan : tanTheta0.singularValues =
      principalTangents (approximateSubspace X) U) :
    δ * N tanTheta0 ≤ N (ritzResidual A X) := by
  exact davisKahan1970_tanTheta0_ritzResidual_le N hA hU X hrank hβα hδ
    ⟨hMspec, hAspec⟩ tanTheta0 htan

universe u

section ProjectorDifference

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Comparator-facing wrapper around the arbitrary-Hilbert restriction-spectrum
projector theorem. -/
theorem projectorDifference_restrictionSpectra_opNorm
    {A B : H →L[ℂ] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule ℂ H} [U.HasOrthogonalProjection]
    [W.HasOrthogonalProjection]
    (hU : A.Reduces U) (hW : B.Reduces W)
    {c g : ℝ} (hg : 0 < g)
    (hUhi : spectrum ℝ (A.restrict hU.1) ⊆ Set.Ici (c + g))
    (hUlo : spectrum ℝ (A.restrict hU.2) ⊆ Set.Iic c)
    (hWhi : spectrum ℝ (B.restrict hW.1) ⊆ Set.Ici (c + g))
    (hWlo : spectrum ℝ (B.restrict hW.2) ⊆ Set.Iic c) :
    ‖(U.starProjection - W.starProjection : H →L[ℂ] H)‖ ≤ ‖B - A‖ / g := by
  exact TauCeti.DavisKahan.Spectral.Complex.opNorm_starProjection_sub_le_of_restriction_spectra
    hA hB hU hW hg hUhi hUlo hWhi hWlo

end ProjectorDifference

/-- Comparator-facing name for the explicit refutation witness of Proposition 4.4. -/
theorem proposition4_4_counterexample :
    ∃ (U V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)))
      (hacute : IsAcute U V)
      (W : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)),
      U.map W.toLinearMap = V ∧
      principalAngles U V 0 ≤ Real.pi / 3 ∧
      kyFanSum 4 (LinearMap.id - W.toLinearMap) <
        kyFanSum 4 (LinearMap.id - (directRotation U V hacute).toLinearMap) := by
  exact shortRotation_fullDisplacement_refuted

end DavisKahanTheory
end TauCeti

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Comparator-facing direct-hypothesis wrapper around source Proposition 6.1. -/
theorem sinTheta_wholeSpace_paperUINorm
    (N : PaperUnitaryInvariantNorm)
    {A B : E →L[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {gap : ℝ} (hgap : 0 < gap)
    (hgapUV : FormBoundedSylvesterGap
      (ClosedOperator.reducingRestriction (ClosedOperator.ofBounded A) U
        (ClosedOperator.ofBounded_reducesSubspace A U hU)).toLinearPMap
      (ClosedOperator.reducingRestriction (ClosedOperator.ofBounded B) Vᗮ
        (ClosedOperator.ofBounded_reducesSubspace B V hV).orthogonal).toLinearPMap
      gap)
    (hgapVU : FormBoundedSylvesterGap
      (ClosedOperator.reducingRestriction (ClosedOperator.ofBounded B) V
        (ClosedOperator.ofBounded_reducesSubspace B V hV)).toLinearPMap
      (ClosedOperator.reducingRestriction (ClosedOperator.ofBounded A) Uᗮ
        (ClosedOperator.ofBounded_reducesSubspace A U hU).orthogonal).toLinearPMap
      gap)
    (hMem : N.Mem (B - A)) :
    N.Mem (paperSinAngleOperatorC U V) ∧
      gap * N.gauge (paperSinAngleOperatorC U V) ≤ N.gauge (B - A) := by
  let P : PaperSymmetricSinThetaProblem (E := E) :=
    { A := A
      B := B
      selfAdjoint_A := hA
      selfAdjoint_B := hB
      U := U
      V := V
      proj_U := inferInstance
      proj_V := inferInstance
      reduces_A_U := hU
      reduces_B_V := hV
      gap := gap
      gap_pos := hgap
      gap_U_to_Vperp := hgapUV
      gap_V_to_Uperp := hgapVU }
  have hsource := P.result_every_unitarilyInvariantNorm N (by
    simpa [P, PaperSymmetricSinThetaProblem.perturbation] using hMem)
  simpa [P, PaperSymmetricSinThetaProblem.perturbation] using hsource

end
end DavisKahan1970
end TauCeti

/-! ## Comparator targets that are currently proved -/

#print axioms TauCeti.DavisKahanTheory.partIII_sinTheta_residual_uiNorm
#print axioms TauCeti.DavisKahanTheory.partIII_sinTheta_uiNorm
#print axioms TauCeti.DavisKahan1970.sinTheta_wholeSpace_paperUINorm
#print axioms TauCeti.DavisKahanTheory.partIII_tanTheta_source_uiNorm
#print axioms TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm
#print axioms TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_spectral
#print axioms TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent
#print axioms TauCeti.DavisKahanTheory.partIII_sinTwoTheta_uiNorm
#print axioms TauCeti.DavisKahan1970.sinTwoTheta_directedResidual_paperUINorm
#print axioms TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm
#print axioms TauCeti.DavisKahanTheory.partIII_tanTwoTheta_opNorm
#print axioms TauCeti.DavisKahan1970.tanTwoTheta_branchFree_paperUINorm_arbitrarySubspace
#print axioms TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_branchFree
#print axioms TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_exact
#print axioms TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_exact
#print axioms TauCeti.DavisKahanTheory.projectorDifference_restrictionSpectra_opNorm
#print axioms TauCeti.DavisKahanTheory.proposition4_4_counterexample

/-!
## Additional exhibition sentinels

These are not extra comparator holes.  They make high-value parts of the 1970
formalization visible in an ordinary challenge build: the definitive generalized
sine theorem over both scalar fields, real-Hilbert counterparts of the corrected
tangent and double-angle endpoints, source sharpness/asymptotics, the bilateral-
shift separation of the paper's dimension conditions, the formal refutation of
the false printed Proposition 4.4, Section 8 branch selection, and a source-
numbered Section 9 numerical consequence.
-/

#print axioms TauCeti.DavisKahan1970.Theorem6_1
#print axioms TauCeti.DavisKahan1970.Theorem6_1_real
#print axioms TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real
#print axioms TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_real_of_crossedDefectsEquivalent
#print axioms TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm_real
#print axioms TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_real_exact
#print axioms TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real_exact
#print axioms TauCeti.DavisKahanTheory.directSum_model_all_four_equalities
#print axioms TauCeti.DavisKahanTheory.single_double_sine_tangent_ratios_tendsto_one
#print axioms TauCeti.DavisKahan1970.remark3_2_bilateralShift_separates_dimensionHypotheses
#print axioms TauCeti.DavisKahanTheory.not_davisKahanProposition4_4_Finite
#print axioms TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch
#print axioms TauCeti.DavisKahan1970.Section9.equation_9_7
