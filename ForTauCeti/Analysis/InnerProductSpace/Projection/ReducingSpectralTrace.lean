/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.ReducingTrace
public import ForTauCeti.Analysis.InnerProductSpace.Projection.InvariantSubspace

/-!
# Intrinsic directed-sine trace decomposition on reducing projection pairs

Any common reducing subspace splits every zero-preserving spectral
penalty of the directed sine map into the penalties of the two actual
restricted projection pairs. Compact projection difference suffices;
the blocks, kernels and spectral sums may be infinite-dimensional.
This applies to exact scalar-phase angle costs without introducing
coordinates or assuming an ambient principal-plane decomposition.
-/

public section

noncomputable section

namespace Submodule

open scoped ENNReal NNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Exact intrinsic angle-penalty decomposition across a common
reducing subspace, using the actual restricted projection pairs.
Any nonnegative zero-preserving penalty is permitted. -/
theorem tsum_sine_penalty_eq_add_of_isReducing
    (K L M : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] [M.HasOrthogonalProjection]
    [(K.comap M.subtype).HasOrthogonalProjection]
    [(L.comap M.subtype).HasOrthogonalProjection]
    [(K.comap Mᗮ.subtype).HasOrthogonalProjection]
    [(L.comap Mᗮ.subtype).HasOrthogonalProjection]
    (hD : IsCompactOperator ((K.starProjection - L.starProjection) : E →L[𝕜] E))
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hL : M.IsReducing L.starProjection.toLinearMap)
    (f : ℝ≥0 → ℝ≥0∞) (hf : f 0 = 0) :
    (∑' n, f ((K.sinThetaMap L).singularValue n)) =
      (∑' n, f (((K.comap M.subtype).sinThetaMap
        (L.comap M.subtype)).singularValue n)) +
      ∑' n, f (((K.comap Mᗮ.subtype).sinThetaMap
        (L.comap Mᗮ.subtype)).singularValue n) := by
  let A := K.sinThetaMap L
  have hfactor : A = (K.starProjection - L.starProjection) ∘L K.starProjection := by
    ext x
    rw [show A x = Lᗮ.starProjection (K.starProjection x) from K.sinThetaMap_apply L x,
      starProjection_orthogonal]
    change K.starProjection x - L.starProjection (K.starProjection x) =
      K.starProjection (K.starProjection x) - L.starProjection (K.starProjection x)
    rw [K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem x)]
  have hAc : IsCompactOperator A := by
    rw [hfactor]
    exact hD.comp_clm K.starProjection
  have hred : M.IsReducing A.toLinearMap := by
    apply (M.isReducing_iff _).mpr
    constructor
    · intro x hx
      change K.sinThetaMap L x ∈ M
      rw [sinThetaMap_apply, starProjection_orthogonal]
      change K.starProjection x - L.starProjection (K.starProjection x) ∈ M
      exact M.sub_mem (hK.mem_invtSubmodule hx)
        (hL.mem_invtSubmodule (hK.mem_invtSubmodule hx))
    · intro x hx
      change K.sinThetaMap L x ∈ Mᗮ
      rw [sinThetaMap_apply, starProjection_orthogonal]
      change K.starProjection x - L.starProjection (K.starProjection x) ∈ Mᗮ
      exact Mᗮ.sub_mem (hK.orthogonal_mem_invtSubmodule hx)
        (hL.orthogonal_mem_invtSubmodule (hK.orthogonal_mem_invtSubmodule hx))
  have hcompress (N : Submodule 𝕜 E) [N.HasOrthogonalProjection]
      [(K.comap N.subtype).HasOrthogonalProjection]
      [(L.comap N.subtype).HasOrthogonalProjection]
      (hKN : ∀ x ∈ N, K.starProjection x ∈ N)
      (hLN : ∀ x ∈ N, L.starProjection x ∈ N) :
      N.orthogonalProjectionOnto ∘L A ∘L N.subtypeL =
        (K.comap N.subtype).sinThetaMap (L.comap N.subtype) := by
    apply ContinuousLinearMap.ext
    intro x
    have hpoint := K.sinThetaMap_comap_subtype_apply_of_invariant L N hKN hLN x
    change N.orthogonalProjectionOnto (K.sinThetaMap L (x : E)) =
      (K.comap N.subtype).sinThetaMap (L.comap N.subtype) x
    rw [← hpoint, N.orthogonalProjectionOnto_mem_subspace_eq_self]
  change (∑' n, f (A.singularValue n)) = _
  rw [A.tsum_singularValue_penalty_eq_add_of_isReducing hAc M hred f hf,
    hcompress M hK.mem_invtSubmodule hL.mem_invtSubmodule,
    hcompress Mᗮ hK.orthogonal_mem_invtSubmodule hL.orthogonal_mem_invtSubmodule]

end Submodule
