/-
# Headline Davis--Kahan sin-2Theta comparators

This challenge pins both a finite reusable UI-norm endpoint and the full
arbitrary-Hilbert-space source-UI-norm ambient statement of the Part III
sin-2Theta headline theorem.
-/

import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
import DavisKahan.BoundedOperator.Compat
import DavisKahan.Geometry.Angle.PaperDoubleAngle
import DavisKahan.DoubleAngle.UnboundedIdeal
import DavisKahan.BoundedOperator.TrialResidual
import DavisKahan.Sylvester.Spectrum
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm

/-!
## Comparator maintenance rule

The open proofs below are deliberate challenge placeholders.  The implementations
live in ordinary library/source modules imported by the paired leaderboard.
-/

namespace TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
  {T S : E →ₗ[𝕜] E}

/-- Davis--Kahan Part III finite sin-2Theta theorem in every unitarily invariant
seminorm. -/
theorem partIII_sinTwoTheta_uiNorm
    (N : UnitarilyInvariantSeminorm 𝕜 E)
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (hVinv : ∀ x ∈ V, S x ∈ V)
    {a b : ℝ} (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2) :
    N ((Uᗮ.starProjection ∘L V.starProjection ∘L U.starProjection
        : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (S - T) / (b - a) := by
  sorry

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
variable {A B : E →L[ℂ] E} {U V : Submodule ℂ E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- Davis--Kahan Part III directed residual sin-2Theta theorem on an arbitrary
complete complex Hilbert space, for every source unitarily invariant norm. -/
theorem sinTwoTheta_directedResidual_paperUINorm
    (N : PaperUnitaryInvariantNorm)
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x)
    (M : V →L[ℂ] V)
    (hMem : N.Mem (residual A V.subtypeL M)) :
    N.Mem (sinTwoThetaIdealBlock U V) ∧
      d * N.gauge (sinTwoThetaIdealBlock U V) ≤
        2 * N.gauge (residual A V.subtypeL M) := by
  sorry

/-- Davis--Kahan Part III ambient sin-2Theta theorem on an arbitrary complete
complex Hilbert space, for every source unitarily invariant norm. -/
theorem sinTwoTheta_wholeSpace_paperUINorm
    (N : PaperUnitaryInvariantNorm)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hU : Reduces A U) (hV : Reduces B V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x)
    (hMem : N.Mem (B - A)) :
    N.Mem (paperSinTwoAngleOperatorC U V) ∧
      d * N.gauge (paperSinTwoAngleOperatorC U V) ≤
        2 * N.gauge (B - A) := by
  sorry

end
end DavisKahan1970
end TauCeti
