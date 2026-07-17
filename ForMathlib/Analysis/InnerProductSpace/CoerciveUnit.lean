/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/CoerciveUnit.lean`
(new file).

Formalized by Claude Fable 5 (claude-fable-5[1m]) while closing the graph
projection formula of the Davis–Kahan graph-subspace correspondence.  This is
the operator form of the Lax–Milgram lemma on a Hilbert space: a uniformly
coercive bounded operator is invertible in the algebra of bounded operators.
No self-adjointness is required — coercivity alone forces injectivity, a
closed range, and a trivial orthogonal complement of the range.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach

/-! # Coercive bounded operators are units

For a bounded operator `N` on a Hilbert space over `𝕜 = ℝ, ℂ` whose quadratic
form is uniformly coercive, `c * ‖z‖ ^ 2 ≤ re ⟪N z, z⟫` with `c > 0`, the
operator `N` is invertible in `E →L[𝕜] E`.  This is the operator-level
Lax–Milgram lemma; the inverse is then available through `Ring.inverse` or
through `IsUnit.unit`.
-/

namespace ForMathlib
namespace ContinuousLinearMap

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- A uniformly coercive bounded operator on a Hilbert space is bounded
below. -/
theorem norm_smul_le_norm_apply_of_coercive {N : E →L[𝕜] E} {c : ℝ}
    (hcoer : ∀ z, c * ‖z‖ ^ 2 ≤ RCLike.re ⟪N z, z⟫_𝕜) (z : E) :
    c * ‖z‖ ≤ ‖N z‖ := by
  rcases eq_or_ne z 0 with hz | hz
  · simp [hz]
  · have h1 : c * ‖z‖ ^ 2 ≤ RCLike.re ⟪N z, z⟫_𝕜 := hcoer z
    have h2 : RCLike.re ⟪N z, z⟫_𝕜 ≤ ‖N z‖ * ‖z‖ :=
      calc RCLike.re ⟪N z, z⟫_𝕜 ≤ ‖⟪N z, z⟫_𝕜‖ := RCLike.re_le_norm _
        _ ≤ ‖N z‖ * ‖z‖ := norm_inner_le_norm _ _
    have hzpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
    have h3 : c * ‖z‖ * ‖z‖ ≤ ‖N z‖ * ‖z‖ := by nlinarith
    exact le_of_mul_le_mul_right h3 hzpos

/-- Operator Lax–Milgram: a uniformly coercive bounded operator on a Hilbert
space is a unit of the algebra of bounded operators. -/
theorem isUnit_of_coercive {N : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ z, c * ‖z‖ ^ 2 ≤ RCLike.re ⟪N z, z⟫_𝕜) : IsUnit N := by
  have hlow := norm_smul_le_norm_apply_of_coercive hcoer
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  constructor
  · intro a b hab
    have h1 : N (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h2 := hlow (a - b)
    rw [h1, norm_zero] at h2
    have h3 : ‖a - b‖ ≤ 0 := by nlinarith [norm_nonneg (a - b)]
    rw [← sub_eq_zero]
    exact norm_le_zero_iff.mp h3
  · have hanti : AntilipschitzWith (Real.toNNReal c)⁻¹ N := by
      refine ContinuousLinearMap.antilipschitz_of_bound N ?_
      intro x
      have hcoe : (((Real.toNNReal c)⁻¹ : NNReal) : ℝ) = c⁻¹ := by
        rw [NNReal.coe_inv, Real.coe_toNNReal c hc.le]
      rw [hcoe, le_inv_mul_iff₀ hc]
      exact hlow x
    have hclosed :
        IsClosed ((LinearMap.range (N : E →ₗ[𝕜] E) : Submodule 𝕜 E) : Set E) := by
      rw [LinearMap.coe_range]
      exact hanti.isClosed_range N.uniformContinuous
    haveI : CompleteSpace (LinearMap.range (N : E →ₗ[𝕜] E)) :=
      hclosed.completeSpace_coe
    haveI : (LinearMap.range (N : E →ₗ[𝕜] E)).HasOrthogonalProjection :=
      Submodule.HasOrthogonalProjection.ofCompleteSpace _
    have hrange : LinearMap.range (N : E →ₗ[𝕜] E) = ⊤ := by
      rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
      intro z hz
      have h0 : ⟪N z, z⟫_𝕜 = 0 :=
        (Submodule.mem_orthogonal _ z).mp hz (N z)
          (LinearMap.mem_range.mpr ⟨z, rfl⟩)
      have h1 := hcoer z
      rw [h0, map_zero] at h1
      have h2 : ‖z‖ ^ 2 ≤ 0 := by nlinarith
      have h3 : ‖z‖ = 0 :=
        (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h2 (sq_nonneg _))
      exact norm_eq_zero.mp h3
    exact LinearMap.range_eq_top.mp hrange

end ContinuousLinearMap
end ForMathlib
