/-
# Classical finite Davis--Kahan tan-Theta theorem

A focused comparator statement for the pole-free per-vector Part III
tan-Theta endpoint. No dimension comparison between the trial and invariant
subspaces is assumed.
-/

import ForMathlib.Analysis.InnerProductSpace.UnitarilyInvariantNorm

/-!
## Comparator maintenance rule

The open proof below is a deliberate challenge placeholder. The implementation
lives in the ordinary library module imported by the paired leaderboard.
-/


namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Pole-free per-vector Davis--Kahan tan-Theta theorem. -/
theorem partIII_tanTheta_vector {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {Z V : Submodule 𝕜 E} [Z.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hVinv : ∀ x ∈ V, T x ∈ V)
    {α β δ ρ : ℝ} (hαβ : α ≤ β) (hδ : 0 < δ) (hρ0 : 0 ≤ ρ)
    (hZ : ∀ x ∈ Z, ((β - α) / 2 + δ) * ‖x‖
      ≤ ‖Z.starProjection (T x) - (((α + β) / 2 : ℝ) : 𝕜) • x‖)
    (hVa : ∀ x ∈ Vᗮ, α * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hVb : ∀ x ∈ Vᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ β * ‖x‖ ^ 2)
    (hρ : ∀ x ∈ Z, ‖T x - Z.starProjection (T x)‖ ≤ ρ * ‖x‖) :
    ∀ x ∈ Z, δ * ‖x - V.starProjection x‖ ≤ ρ * ‖V.starProjection x‖ := by
  sorry

end DavisKahanTheory
end ForMathlib
