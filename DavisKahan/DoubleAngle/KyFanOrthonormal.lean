/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import DavisKahan.OperatorIdeal.ApproximationNumbers.Core

/-!
# The Ky Fan variational bound for approximation-number prefixes

The infinite-dimensional max–min counterpart of the finite rectangular Ky Fan
variational principle: for a bounded operator `K` between Hilbert spaces and
orthonormal families `u`, `v` of length `k`,

`re (∑ i, ⟪u i, K (v i)⟫) ≤ kyFanApproximationGauge k K`.

The finite principle (`re_sum_inner_map_le_rectangularKyFanSum`) requires both
spaces finite-dimensional.  The proof here compresses `K` to the spans of the
two families — a map between `k`-dimensional spaces — where the finite
principle and the finite bridge
`rectangularKyFanSum_eq_kyFanApproximationGauge` apply, and then transports
back along the ideal inequality `approximationSingularValue_comp_le`, using
that the orthogonal projection and the subspace inclusion are contractions.

This closes the max–min gap in the approximation-number layer; the natural
upstream home is `DavisKahan/OperatorIdeal/ApproximationNumbers/Core.lean`.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Ky Fan variational bound for approximation numbers.**  For orthonormal
families `u : Fin k → F` and `v : Fin k → E`, the paired coefficient sum of a
bounded operator is controlled by the `k`-th approximation-number prefix. -/
theorem re_sum_inner_map_le_kyFanApproximationGauge
    (K : E →L[𝕜] F) {k : ℕ} {u : Fin k → F} {v : Fin k → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    RCLike.re (∑ i, ⟪u i, K (v i)⟫_𝕜) ≤ kyFanApproximationGauge k K := by
  classical
  set L₁ : Submodule 𝕜 F := Submodule.span 𝕜 (Set.range u) with hL₁def
  set L₂ : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range v) with hL₂def
  haveI : FiniteDimensional 𝕜 L₁ :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range u)
  haveI : FiniteDimensional 𝕜 L₂ :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range v)
  haveI : CompleteSpace L₁ := FiniteDimensional.complete 𝕜 L₁
  haveI : CompleteSpace L₂ := FiniteDimensional.complete 𝕜 L₂
  set K' : L₂ →L[𝕜] L₁ :=
    L₁.orthogonalProjectionOnto ∘L K ∘L L₂.subtypeL with hK'def
  -- the corestricted families
  have humem : ∀ i, u i ∈ L₁ := fun i =>
    Submodule.subset_span (Set.mem_range_self i)
  have hvmem : ∀ i, v i ∈ L₂ := fun i =>
    Submodule.subset_span (Set.mem_range_self i)
  set u' : Fin k → L₁ := fun i => ⟨u i, humem i⟩ with hu'def
  set v' : Fin k → L₂ := fun i => ⟨v i, hvmem i⟩ with hv'def
  have hu' : Orthonormal 𝕜 u' := by
    rw [orthonormal_iff_ite] at hu ⊢
    intro i j
    simpa [u', Submodule.coe_inner] using hu i j
  have hv' : Orthonormal 𝕜 v' := by
    rw [orthonormal_iff_ite] at hv ⊢
    intro i j
    simpa [v', Submodule.coe_inner] using hv i j
  have hkle : k ≤ finrank 𝕜 L₂ := by
    have h := finrank_span_eq_card hv.linearIndependent
    rw [← hL₂def] at h
    simp [h]
  -- the compressed pairing agrees with the ambient pairing
  have hpair : ∀ i, ⟪u' i, K' (v' i)⟫_𝕜 = ⟪u i, K (v i)⟫_𝕜 := by
    intro i
    have hval : ((K' (v' i) : L₁) : F) = L₁.starProjection (K (v i)) := rfl
    rw [Submodule.coe_inner, hval, ← L₁.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (humem i)]
  -- finite Ky Fan principle on the compression
  have hfin : RCLike.re (∑ i, ⟪u' i, K' (v' i)⟫_𝕜) ≤
      DavisKahanTheory.RectangularUnitarilyInvariantNorm.rectangularKyFanSum
        k K'.toLinearMap :=
    DavisKahanTheory.RectangularUnitarilyInvariantNorm.re_sum_inner_map_le_rectangularKyFanSum
      hkle hu' hv'
  -- finite bridge to the approximation-number prefix
  have hK'id : K'.toLinearMap.toContinuousLinearMap = K' := by
    ext x; rfl
  have hbridge :
      DavisKahanTheory.RectangularUnitarilyInvariantNorm.rectangularKyFanSum
        k K'.toLinearMap = kyFanApproximationGauge k K' := by
    rw [rectangularKyFanSum_eq_kyFanApproximationGauge, hK'id]
  -- the compression does not increase approximation numbers
  have hmono : kyFanApproximationGauge k K' ≤ kyFanApproximationGauge k K := by
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    refine Finset.sum_le_sum fun n _ => ?_
    have hcomp := approximationSingularValue_comp_le n
      L₁.orthogonalProjectionOnto K L₂.subtypeL
    refine hcomp.trans ?_
    have h1 : ‖L₁.orthogonalProjectionOnto‖ ≤ 1 :=
      L₁.orthogonalProjectionOnto_norm_le
    have h2 : ‖L₂.subtypeL‖ ≤ 1 := L₂.norm_subtypeL_le
    have h0 := approximationSingularValue_nonneg n K
    calc ‖L₁.orthogonalProjectionOnto‖ * approximationSingularValue n K *
          ‖L₂.subtypeL‖
        ≤ 1 * approximationSingularValue n K * 1 := by
          refine mul_le_mul (mul_le_mul h1 le_rfl h0 zero_le_one) h2
            (norm_nonneg _) ?_
          positivity
      _ = approximationSingularValue n K := by ring
  calc RCLike.re (∑ i, ⟪u i, K (v i)⟫_𝕜)
      = RCLike.re (∑ i, ⟪u' i, K' (v' i)⟫_𝕜) := by
        congr 1
        exact Finset.sum_congr rfl fun i _ => (hpair i).symm
    _ ≤ DavisKahanTheory.RectangularUnitarilyInvariantNorm.rectangularKyFanSum
          k K'.toLinearMap := hfin
    _ = kyFanApproximationGauge k K' := hbridge
    _ ≤ kyFanApproximationGauge k K := hmono

omit [CompleteSpace E] [CompleteSpace F] in
/-- Witness form of the variational bound: pointwise lower bounds by paired
coefficients sum to at most the approximation-number prefix. -/
theorem sum_le_kyFanApproximationGauge_of_orthonormal
    (K : E →L[𝕜] F) {k : ℕ} {u : Fin k → F} {v : Fin k → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) {t : Fin k → ℝ}
    (ht : ∀ i, t i ≤ RCLike.re ⟪u i, K (v i)⟫_𝕜) :
    ∑ i, t i ≤ kyFanApproximationGauge k K := by
  refine le_trans ?_ (re_sum_inner_map_le_kyFanApproximationGauge K hu hv)
  rw [map_sum]
  exact Finset.sum_le_sum fun i _ => ht i

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti