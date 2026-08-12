/-
# Headline Davis--Kahan tan-2Theta comparators

This challenge pins both the established finite sharp operator-norm endpoint
and the strongest current arbitrary-Hilbert-space/source-UI-norm ambient
endpoint.

The latter still exposes the paper's `cos (2 theta) != 0` pole-exclusion
condition as a hypothesis.  Consequently this challenge intentionally does NOT
claim that the repository has a literal unrestricted Section 2 wrapper from
only the printed spectral/off-diagonal hypotheses.  When that final wrapper is
proved, it should replace or supplement this comparator leaf.
-/

import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
import DavisKahan.BoundedOperator.Compat
import DavisKahan.Geometry.Angle.PaperTanAngle
import DavisKahan.DoubleAngle.TanTwoThetaBranchFree
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
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Sharp finite operator-norm Davis--Kahan tan-2Theta theorem. -/
theorem partIII_tanTwoTheta_opNorm {T S : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (hVinv : ∀ x ∈ V, S x ∈ V)
    {a b ε : ℝ} (hab : a < b) (hε0 : 0 ≤ ε)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hVb : ∀ x ∈ V, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪S x, x⟫_𝕜)
    (hVa : ∀ x ∈ Vᗮ, RCLike.re ⟪S x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, ∀ y ∈ U, ⟪x, (S - T) y⟫_𝕜 = 0)
    (hHUperp : ∀ x ∈ Uᗮ, ∀ y ∈ Uᗮ, ⟪x, (S - T) y⟫_𝕜 = 0)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ ^ 2 < 1 / 2 ∧
      (b - a) * (2 * ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖
          * Real.sqrt
            (1 - ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ ^ 2))
        ≤ 2 * ε *
          (1 - 2 * ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ ^ 2) := by
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

/-- Branch-free directed/source-representative tan-2Theta theorem on an
arbitrary complete complex Hilbert space.  This theorem carries the source UI
norm and sharp factor two without a finite-dimensional trial-space hypothesis. -/
theorem tanTwoTheta_branchFree_paperUINorm_arbitrarySubspace
    {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (N : PaperUnitaryInvariantNorm)
    {A H T : E →L[ℂ] E} {U : Submodule ℂ E} [U.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (tanTwoTheta : E →L[ℂ] E) (π : ℕ ≃ ℕ)
    (htan : ∀ n, approximationSingularValue (π n) tanTwoTheta =
      DavisKahanTheory.absDoubleAngleTangent (approximationSingularValue n T))
    (hHmem : N.Mem H) :
    N.Mem tanTwoTheta ∧
      (b - a) * N.gauge tanTwoTheta ≤ 2 * N.gauge H := by
  sorry

/-- Strongest current ambient tan-2Theta theorem for every source UI norm.
This is branch-free apart from the explicit pole-exclusion premise `hcos`; that
premise must not be silently confused with the literal printed Section 2
hypothesis surface. -/
theorem tanTwoTheta_wholeSpace_paperUINorm_branchFree
    (N : PaperUnitaryInvariantNorm)
    {A H : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hcos : ∀ t ∈ spectrum ℝ (paperAngleOperatorC U V), Real.cos (2 * t) ≠ 0)
    (hHmem : N.Mem H) :
    N.Mem (paperAbsTanTwoAngleOperatorC U V) ∧
      (b - a) * N.gauge (paperAbsTanTwoAngleOperatorC U V) ≤ 2 * N.gauge H := by
  sorry

end
end DavisKahan1970
end TauCeti
