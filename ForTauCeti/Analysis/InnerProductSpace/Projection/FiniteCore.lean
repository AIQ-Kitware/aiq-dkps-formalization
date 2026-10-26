/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngleBlocks
public import ForTauCeti.Analysis.OperatorIdeal.OrthogonalExtension
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenFinite

/-!
# Principal-angle penalties on finite cores in Hilbert space

When the directed sine vanishes off a finite reducing core, its ambient
approximation-number penalty is exactly the accepted principal-angle sum
on that core. This comparison uses actual ambient operators and includes
zero and right angles. The ambient Hilbert space can be nonseparable.
-/

public section

noncomputable section

namespace Submodule

open TauCeti
open scoped ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The directed sine of a reducing pair is an orthogonal zero extension
whenever the two projections agree on the complementary block. -/
theorem sinThetaMap_eq_orthogonal_extension
    (K L M : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection]
    [(K.comap M.subtype).HasOrthogonalProjection]
    [(L.comap M.subtype).HasOrthogonalProjection]
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hL : M.IsReducing L.starProjection.toLinearMap)
    (heq : ∀ x ∈ Mᗮ, K.starProjection x = L.starProjection x) :
    K.sinThetaMap L = M.subtypeL ∘L
      ((K.comap M.subtype).sinThetaMap (L.comap M.subtype)) ∘L
        M.orthogonalProjectionOnto := by
  apply (ContinuousLinearMap.eq_orthogonal_extension_iff _ _ _ _).mpr
  constructor
  · intro x
    exact (sinThetaMap_comap_subtype_apply_of_invariant K L M
      hK.mem_invtSubmodule hL.mem_invtSubmodule x).symm
  · intro x hx
    rw [sinThetaMap_apply, starProjection_orthogonal]
    change K.starProjection x - L.starProjection (K.starProjection x) = 0
    have hPx : K.starProjection x ∈ Mᗮ := hK.orthogonal_mem_invtSubmodule hx
    rw [← heq _ hPx,
      K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem x), sub_self]

/-- Every zero-preserving ambient directed-sine penalty is exactly the
finite principal-angle penalty of a core off which the projections agree. -/
theorem tsum_sine_penalty_eq_principalAngle_sum_of_finite_core
    (K L M : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [FiniteDimensional 𝕜 M]
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hL : M.IsReducing L.starProjection.toLinearMap)
    (heq : ∀ x ∈ Mᗮ, K.starProjection x = L.starProjection x)
    (f : ℝ → ℝ≥0∞) (hf : f 0 = 0) :
    (∑' n, f (Real.arcsin ((K.sinThetaMap L).singularValue n : ℝ))) =
      ∑ i : Fin (Module.finrank 𝕜 (K.comap M.subtype)),
        f ((K.comap M.subtype).principalAngles (L.comap M.subtype) i) := by
  rw [sinThetaMap_eq_orthogonal_extension K L M hK hL heq]
  simp_rw [ContinuousLinearMap.singularValue_orthogonal_extension]
  rw [OperatorIdealFamily.tsum_singularValue_penalty_eq_sum _
    (fun s => f (Real.arcsin (s : ℝ))) (by simpa only [NNReal.coe_zero, Real.arcsin_zero] using hf)]
  simp_rw [ContinuousLinearMap.singularValue_eq_linearMap_singularValues]
  exact (sum_principalAngles_eq_sum_singularValues_arcsin _ _ f hf).symm

end Submodule
