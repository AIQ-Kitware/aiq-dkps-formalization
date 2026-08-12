/-
# Headline Davis--Kahan tan-Theta comparators

This challenge pins the two source-facing halves of the Part III tan-Theta
headline theorem rather than the older per-vector compatibility endpoint:

* the directed Ritz-residual inequality in every rectangular unitarily
  invariant norm, with the paper's equal-dimension standing hypothesis; and
* the ambient arbitrary-Hilbert-space inequality in every source unitarily
  invariant norm, with transversality derived from the printed standing
  assumption (3.5).
-/

import DavisKahan.FiniteDimensional.Core.All
import ForTauCeti.Analysis.InnerProductSpace.Residual.Ritz
import ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantSeminorm
import DavisKahan.Geometry.Angle.PaperTanAngle
import DavisKahan.Geometry.Halmos.CrossedDefectGap
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm
import DavisKahan.TanTheta.Theorem63FiniteSource
import DavisKahan.TanTheta.Theorem63InfiniteTrial

/-!
## Comparator maintenance rule

The open proofs below are deliberate challenge placeholders.  The implementation
lives in ordinary library/source modules imported by the paired leaderboard.
The first statement deliberately spells out the interval hypotheses instead of
importing the implementation-only `TanThetaIntervalGap` packaging.
-/

namespace TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Davis--Kahan Part III directed tan-Theta Ritz-residual theorem in every
rectangular unitarily invariant norm.  Transversality is a conclusion of the
spectral hypotheses, not an extra comparator premise. -/
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
  sorry

end DavisKahanTheory
end TauCeti

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.ExactTanTheta

open scoped InnerProductSpace

noncomputable section

universe u v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {T A : E →L[ℂ] E} {U V : Submodule ℂ E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- Davis--Kahan Theorem 6.3 directed tan-Theta result on an arbitrary
complete complex Hilbert space and arbitrary complete trial subspace, for every
source unitarily invariant norm. -/
theorem tanTheta_directed_paperUINorm
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (N : PaperUnitaryInvariantNorm)
    (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (V Z : Submodule ℂ H) [V.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    [CompleteSpace Z]
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z,
      RCLike.re ⟪theorem63Compression T Z z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (hResidual : N.Mem (theorem63Residual T Z)) :
    ∃ tanTheta0 : Z →L[ℂ] H,
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 ∧
        N.Mem tanTheta0 ∧
        delta * N.gauge tanTheta0 ≤ N.gauge (theorem63Residual T Z) := by
  sorry

/-- Davis--Kahan Part III ambient tan-Theta theorem on an arbitrary complete
complex Hilbert space, for every source unitarily invariant norm.  The printed
standing assumption (3.5) supplies the transversality needed to define the
paper tangent; it is not separately assumed. -/
theorem tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent
    (N : PaperUnitaryInvariantNorm)
    (hT : T.IsSymmetric) (hA : IsSelfAdjoint A)
    (hV : T.Reduces V) (hAU : ∀ x ∈ U, A x ∈ U)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : U,
      RCLike.re ⟪theorem63Compression T U z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ)
    (h35 : DavisKahan.Frontier.CrossedDefectsEquivalent U V)
    (hMem : N.Mem (T - A)) :
    N.Mem (paperTanAngleOperatorC U V) ∧
      delta * N.gauge (paperTanAngleOperatorC U V) ≤ N.gauge (T - A) := by
  sorry

end
end DavisKahan1970
end TauCeti
