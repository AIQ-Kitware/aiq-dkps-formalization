/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.AngleOperator

/-!
# Reflecting transports preserve principal sines

A self-adjoint unitary transporting one projection to another negates
their difference by conjugation. It therefore commutes with the square
and modulus of that difference. No finite-dimensional assumption is used.

## Provenance

This is classical projection algebra. The Lean proof is independently
written here using the accepted Tau Ceti angle operator and modulus APIs.
-/

public section

noncomputable section

namespace Submodule

open TauCeti ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Every reflecting transporter preserves the intrinsic sine angle
operator, including right-angle defects and common fixed directions. -/
theorem commute_sinAngleOperator_of_selfAdjoint_transport
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (R : E ≃ₗᵢ[𝕜] E) (hR : IsSelfAdjoint (R : E →L[𝕜] E))
    (htrans : (R : E →L[𝕜] E) * K.starProjection * star (R : E →L[𝕜] E) =
      L.starProjection) :
    Commute (R : E →L[𝕜] E) (K.sinAngleOperator L) := by
  have hRR (x : E) : R (R x) = x := by
    have h := congrArg (fun T : E →L[𝕜] E => T x)
      (Unitary.star_mul_self_of_mem (Unitary.linearIsometryEquiv.symm R).property)
    change star (R : E →L[𝕜] E) (R x) = x at h
    rwa [hR.star_eq] at h
  have hconj (x : E) : R (K.starProjection (R x)) = L.starProjection x := by
    have h := congrArg (fun T : E →L[𝕜] E => T x) htrans
    rwa [hR.star_eq] at h
  have hRP (x : E) : R (K.starProjection x) = L.starProjection (R x) := by
    simpa only [hRR] using hconj (R x)
  have hRQ (x : E) : R (L.starProjection x) = K.starProjection (R x) := by
    rw [← hconj, hRR]
  let D := K.starProjection - L.starProjection
  have hanti (x : E) : R (D x) = -D (R x) := by
    change R (K.starProjection x - L.starProjection x) =
      -(K.starProjection (R x) - L.starProjection (R x))
    rw [map_sub, hRP, hRQ]
    abel
  have hsq : Commute (R : E →L[𝕜] E) (D * D) := by
    apply ContinuousLinearMap.ext
    intro x
    change R (D (D x)) = D (D (R x))
    rw [hanti, hanti, map_neg, neg_neg]
  have hD : IsSelfAdjoint D :=
    (isSelfAdjoint_starProjection K).sub (isSelfAdjoint_starProjection L)
  rw [sinAngleOperator_def]
  apply commute_modulus_of_commute
  change Commute (R : E →L[𝕜] E) (D.adjoint ∘L D)
  simpa only [hD.adjoint_eq, ← ContinuousLinearMap.mul_def] using hsq

end Submodule
