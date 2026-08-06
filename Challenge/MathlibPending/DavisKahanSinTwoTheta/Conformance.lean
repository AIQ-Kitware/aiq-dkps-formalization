/-
# Classical finite Davis--Kahan sin-2Theta theorem

A focused comparator statement for the source-faithful Part III sin-2Theta
endpoint in every unitarily invariant norm.
-/

import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm

/-!
## Comparator maintenance rule

The open proof below is a deliberate challenge placeholder. The implementation
lives in the ordinary library module imported by the paired leaderboard.
-/


namespace TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
  {T S : E →ₗ[𝕜] E}

/-- Davis--Kahan Part III sin-2Theta theorem in every unitarily invariant norm. -/
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