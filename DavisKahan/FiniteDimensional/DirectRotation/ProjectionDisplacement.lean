/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.Majorization
import ForTauCeti.Analysis.InnerProductSpace.AngleGeometry

/-!
# Projection distance is a lower bound for unitary displacement

If an orthogonal or unitary map `W` carries `U` onto `V`, then for every
unitarily invariant seminorm `N` on finite-dimensional operators,

  `N (P_U - P_V) <= N (I - W)`.

This estimate needs neither equal ranks as a separate hypothesis (it follows
from the existence of `W`) nor an acute-angle bound.  The proof uses only
unitary invariance, the triangle inequality, and the reflection identity
`J_U = 2 P_U - I`.  In particular, there is no singular-value enumeration,
CS decomposition, or auxiliary minimizer construction.

The statement is useful for the proposed quantitative repair of Davis--Kahan
(1970), Proposition 4.4.  It is *not* the unproved upper bound for the direct
rotation; that requires an additional principal-plane comparison.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- If `W` carries `U` to `V`, the displacement of their projections is no
larger in any unitarily invariant seminorm than the full displacement of `W`.
No restriction on principal angles is necessary. -/
theorem projectionDifference_uiNorm_le_displacement
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    N (projection U - projection V) ≤ N (LinearMap.id - W.toLinearMap) := by
  let J : E →ₗ[𝕜] E := U.reflection.toLinearMap
  let K : E →ₗ[𝕜] E := V.reflection.toLinearMap
  let D : E →ₗ[𝕜] E := W.toLinearMap - LinearMap.id
  have hproj (x : E) :
      W (U.starProjection x) = V.starProjection (W x) := by
    have hx := LinearMap.congr_fun
      (projection_intertwines_of_map_eq U V W hmap) x
    simpa only [LinearMap.comp_apply, projection, ContinuousLinearMap.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe] using hx
  have hreflect (x : E) : V.reflection (W x) = W (U.reflection x) := by
    rw [Submodule.reflection_apply, Submodule.reflection_apply]
    simp only [map_sub, map_nsmul]
    rw [hproj x]
  have hcomm :
      (J - K) ∘ₗ W.toLinearMap = J ∘ₗ D - D ∘ₗ J := by
    ext x
    change U.reflection (W x) - V.reflection (W x) =
      U.reflection (W x - x) - (W (U.reflection x) - U.reflection x)
    rw [hreflect x, map_sub]
    abel
  have hJcast : J = (U.reflection : E →ₗ[𝕜] E) := by
    ext x
    rfl
  have hWcast : W.toLinearMap = (W : E →ₗ[𝕜] E) := by
    ext x
    rfl
  have hunitaryRight : N ((J - K) ∘ₗ W.toLinearMap) = N (J - K) := by
    rw [hWcast]
    exact N.map_comp_linearIsometryEquiv W _
  have hunitaryLeft : N (J ∘ₗ D) = N D := by
    rw [hJcast]
    exact N.map_linearIsometryEquiv_comp U.reflection _
  have hunitaryRightJ : N (D ∘ₗ J) = N D := by
    rw [hJcast]
    exact N.map_comp_linearIsometryEquiv U.reflection _
  have htriangle : N (J ∘ₗ D - D ∘ₗ J) ≤ N (J ∘ₗ D) + N (D ∘ₗ J) := by
    simpa only [sub_eq_add_neg, map_neg_eq_map N] using
      (map_add_le_add N (J ∘ₗ D) (-(D ∘ₗ J)))
  have hreflectionBound : N (J - K) ≤ 2 * N D := by
    calc
      N (J - K) = N ((J - K) ∘ₗ W.toLinearMap) := hunitaryRight.symm
      _ = N (J ∘ₗ D - D ∘ₗ J) := congrArg N hcomm
      _ ≤ N (J ∘ₗ D) + N (D ∘ₗ J) := htriangle
      _ = 2 * N D := by rw [hunitaryLeft, hunitaryRightJ]; ring
  have hreflections :
      (2 : 𝕜) • (projection U - projection V) = J - K := by
    ext x
    change (2 : 𝕜) • (U.starProjection x - V.starProjection x) =
      U.reflection x - V.reflection x
    simp only [Submodule.reflection_apply, smul_sub, two_smul]
    module
  have hscale : N (J - K) = 2 * N (projection U - projection V) := by
    rw [← hreflections, map_smul_eq_mul N, RCLike.norm_ofNat]
  have hneg : N D = N (LinearMap.id - W.toLinearMap) := by
    change N (W.toLinearMap - LinearMap.id) =
      N (LinearMap.id - W.toLinearMap)
    rw [show W.toLinearMap - LinearMap.id =
        -(LinearMap.id - W.toLinearMap) by abel, map_neg_eq_map N]
  rw [hscale, hneg] at hreflectionBound
  linarith

/-- The same estimate for the canonical positive full-space sine operator
`|P_U - P_V|`.  Unlike the directed sine, this operator counts both sides
of each nontrivial principal plane. -/
theorem sinAngleOperator_uiNorm_le_displacement
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    N (sinAngleOperator U V) ≤ N (LinearMap.id - W.toLinearMap) := by
  rw [← uiNorm_projection_sub_eq_sinAngleOperator N U V]
  exact projectionDifference_uiNorm_le_displacement N U V W hmap

/-- The lower bound for every Ky Fan partial sum, including the trace norm
when `k = finrank 𝕜 E`. -/
theorem projectionDifference_kyFanSum_le_displacement
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V)
    (k : ℕ) :
    kyFanSum k (projection U - projection V) ≤
      kyFanSum k (LinearMap.id - W.toLinearMap) := by
  rw [kyFanSum_eq_kyFan, kyFanSum_eq_kyFan]
  exact projectionDifference_uiNorm_le_displacement
    (UnitarilyInvariantSeminorm.kyFan 𝕜 E E k) U V W hmap

end DavisKahan.FiniteDimensional
end TauCeti
