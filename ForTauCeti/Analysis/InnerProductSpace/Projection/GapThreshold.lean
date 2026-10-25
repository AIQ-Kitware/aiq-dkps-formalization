/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Principal-angle cutoffs and unitary commutators

A closed bound on the finite principal-angle list is equivalent to a
directed projection-gap bound. For a unitary image the symmetric gap is
the norm of the commutator with the original projection. These classical
identities convert angle-dependent transport criteria into norm tests.
-/

public section

noncomputable section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A closed physical angle bound on the finite list is equivalent to
the corresponding sine bound on the directed projection gap. -/
theorem finite_principalAngles_le_iff_directedProjectionGap_le
    [FiniteDimensional 𝕜 E] (U V : Submodule 𝕜 E)
    (theta : ℝ) (hθ : theta ∈ Set.Icc 0 (Real.pi / 2)) :
    (∀ i : Fin (Module.finrank 𝕜 U), U.principalAngles V i ≤ theta) ↔
      U.directedProjectionGap V ≤ Real.sin theta := by
  have hfinite : (∀ i : Fin (Module.finrank 𝕜 U), U.principalAngles V i ≤ theta) ↔
      ∀ i : ℕ, U.principalAngles V i ≤ theta := by
    constructor
    · intro h i
      by_cases hi : i < Module.finrank 𝕜 U
      · exact h ⟨i, hi⟩
      · rw [U.principalAngles_of_finrank_le V (Nat.le_of_not_gt hi)]
        exact hθ.1
    · intro h i
      exact h i
  rw [hfinite, ← U.principalSines_zero V, ← U.sin_principalAngles V 0]
  have hs := Real.strictMonoOn_sin.le_iff_le
    (show U.principalAngles V 0 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [U.principalAngles_nonneg V 0, Real.pi_pos],
        U.principalAngles_le_pi_div_two V 0⟩)
    (show theta ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  rw [hs]
  exact ⟨fun h => h 0, fun h i => (U.principalAngles_antitone V (Nat.zero_le i)).trans h⟩

/-- The gap from a projected subspace to its unitary image is exactly
the operator norm of the unitary's commutator with that projection. -/
theorem projectionGap_unitary_image_eq_commutator [CompleteSpace E]
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (A : E ≃ₗᵢ[𝕜] E) :
    K.projectionGap (K.map A.toLinearMap) =
      ‖(A : E →L[𝕜] E) * K.starProjection - K.starProjection * (A : E →L[𝕜] E)‖ := by
  let Q := (K.map A.toLinearMap).starProjection
  let U := Unitary.linearIsometryEquiv.symm A
  have hfac : (K.starProjection - Q) * (U : E →L[𝕜] E) =
      K.starProjection * (A : E →L[𝕜] E) - (A : E →L[𝕜] E) * K.starProjection := by
    ext x
    change K.starProjection (A x) - Q (A x) = K.starProjection (A x) - A (K.starProjection x)
    rw [show Q (A x) = A (K.starProjection x) by
      dsimp only [Q]
      rw [Submodule.starProjection_map_apply, A.symm_apply_apply]]
  have hn := CStarRing.norm_mul_coe_unitary (K.starProjection - Q) U
  rw [hfac, norm_sub_rev] at hn
  rw [projectionGap_def]
  exact hn.symm

end Submodule
