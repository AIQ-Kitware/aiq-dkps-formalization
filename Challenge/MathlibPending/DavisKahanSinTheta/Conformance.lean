/-
# Classical finite Davis--Kahan sin-Theta theorem

A focused comparator statement for the source-faithful Part III sin-Theta
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

/-- Davis--Kahan Part III sin-Theta theorem in every unitarily invariant norm. -/
theorem partIII_sinTheta_uiNorm
    (N : UnitarilyInvariantSeminorm 𝕜 E)
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (hVinv : ∀ x ∈ V, S x ∈ V)
    {c g : ℝ} (hg : 0 < g)
    (hU : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hV : ∀ x ∈ V, RCLike.re ⟪S x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    N ((V.starProjection ∘L U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (S - T) / g := by
  sorry

end DavisKahanTheory
end TauCeti