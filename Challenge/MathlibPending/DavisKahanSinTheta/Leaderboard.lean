/- # Headline Davis--Kahan sin-Theta dependency audit -/

import DavisKahan.Sources.DavisKahan1970.PartIII
import DavisKahan.Sources.DavisKahan1970.SineTheta.Symmetric

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

/-- Comparator-facing direct-hypothesis wrapper around the exact source
Proposition 6.1 implementation. -/
theorem sinTheta_wholeSpace_paperUINorm
    (N : PaperUnitaryInvariantNorm)
    {A B : E →L[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {gap : ℝ} (hgap : 0 < gap)
    (hgapUV : FormBoundedSylvesterGap
      (ClosedOperator.reducingRestriction (ClosedOperator.ofBounded A) U
        (ClosedOperator.ofBounded_reducesSubspace A U hU))
      (ClosedOperator.reducingRestriction (ClosedOperator.ofBounded B) Vᗮ
        (ClosedOperator.ofBounded_reducesSubspace B V hV).orthogonal)
      gap)
    (hgapVU : FormBoundedSylvesterGap
      (ClosedOperator.reducingRestriction (ClosedOperator.ofBounded B) V
        (ClosedOperator.ofBounded_reducesSubspace B V hV))
      (ClosedOperator.reducingRestriction (ClosedOperator.ofBounded A) Uᗮ
        (ClosedOperator.ofBounded_reducesSubspace A U hU).orthogonal)
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

#print axioms TauCeti.DavisKahanTheory.partIII_sinTheta_residual_uiNorm
#print axioms TauCeti.DavisKahanTheory.partIII_sinTheta_uiNorm
#print axioms TauCeti.DavisKahan1970.sinTheta_wholeSpace_paperUINorm
