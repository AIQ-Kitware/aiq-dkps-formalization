/- # Headline Davis--Kahan tan-Theta dependency audit -/

import DavisKahan.Sources.DavisKahan1970.PartIII
import DavisKahan.Sources.DavisKahan1970.Directed
import DavisKahan.Sources.DavisKahan1970.TanThetaWholeSpace

namespace TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Comparator-facing spelling of the printed interval hypotheses. -/
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

end DavisKahanTheory
end TauCeti

#print axioms TauCeti.DavisKahanTheory.partIII_tanTheta_source_uiNorm
#print axioms TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm
#print axioms TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent
