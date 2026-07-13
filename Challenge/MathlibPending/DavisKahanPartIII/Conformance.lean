/-
# Classical finite Davis--Kahan Part III quartet (pending comparator challenge)

These are the four source-checked headline theorems: sin Theta and sin 2Theta
for every unitarily invariant norm, the pole-free per-vector tan Theta theorem,
and the sharp operator-norm tan 2Theta theorem with strict quarter-turn
avoidance.
-/

/-!
## Comparator maintenance rule

Every open proof below is a deliberate challenge placeholder. Do not fill
these proofs in this repository and do not count them as formalization debt. The
implementations live in the ordinary `ForMathlib` modules imported by the
paired `Leaderboard.lean`; Comparator checks statement identity and permitted
kernel dependencies.
-/

import ForMathlib.Analysis.InnerProductSpace.UnitarilyInvariantNorm

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace
open Module (finrank)

section SineTheorems

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
  {T S : E →ₗ[𝕜] E}

/-- Davis--Kahan Part III sin-Theta theorem in every unitarily invariant norm. -/
theorem partIII_sinTheta_uiNorm
    (N : UnitarilyInvariantNorm 𝕜 E)
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

/-- Davis--Kahan Part III sin-2Theta theorem in every unitarily invariant norm. -/
theorem partIII_sinTwoTheta_uiNorm
    (N : UnitarilyInvariantNorm 𝕜 E)
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

end SineTheorems

section TangentTheorems

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Pole-free per-vector Davis--Kahan tan-Theta theorem. -/
theorem partIII_tanTheta_vector {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {Z V : Submodule 𝕜 E} [Z.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hVinv : ∀ x ∈ V, T x ∈ V) (hdim : finrank 𝕜 Z = finrank 𝕜 V)
    {α β δ ρ : ℝ} (hαβ : α ≤ β) (hδ : 0 < δ) (hρ0 : 0 ≤ ρ)
    (hZ : ∀ x ∈ Z, ((β - α) / 2 + δ) * ‖x‖
      ≤ ‖Z.starProjection (T x) - (((α + β) / 2 : ℝ) : 𝕜) • x‖)
    (hVa : ∀ x ∈ Vᗮ, α * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hVb : ∀ x ∈ Vᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ β * ‖x‖ ^ 2)
    (hρ : ∀ x ∈ Z, ‖T x - Z.starProjection (T x)‖ ≤ ρ * ‖x‖) :
    ∀ x ∈ Z, δ * ‖x - V.starProjection x‖ ≤ ρ * ‖V.starProjection x‖ := by
  sorry

/-- Sharp operator-norm Davis--Kahan tan-2Theta theorem, including strict
quarter-turn avoidance. -/
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

end TangentTheorems
end DavisKahanTheory
end ForMathlib
