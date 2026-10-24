/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Algebra.Star.StarProjection

/-!
# Equality of a compression with its commuting real part

If the Gram operator of a normal compression equals the square of its
self-adjoint real part, the skew part vanishes. The argument uses the
faithfulness of `star x * x`, without finite dimensionality or a trace.
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

private theorem skew_eq_zero_of_gram_eq_real_sq
    (L H : E →L[𝕜] E) (hL : IsSelfAdjoint L) (hH : star H = -H)
    (hcomm : Commute L H) (hgram : (L + H) * star (L + H) = L * L) : H = 0 := by
  have hexpand : (L + H) * star (L + H) = L * L - H * H := by
    rw [star_add, hL.star_eq, hH]
    calc
      _ = L * L - H * H + (H * L - L * H) := by noncomm_ring
      _ = _ := by rw [hcomm.eq, sub_self, add_zero]
  rw [hexpand] at hgram
  have hsq : H * H = 0 := sub_eq_self.mp hgram
  apply (star_mul_self_eq_zero (x := H)).mp
  rw [hH, neg_mul, hsq, neg_zero]

/-- A projection compression equals its commuting self-adjoint real part
when their Gram operators agree. -/
theorem compression_eq_of_gram_eq_real_sq
    (P R C : E →L[𝕜] E) (hP : IsStarProjection P) (hC : IsSelfAdjoint C)
    (hskew : star (R - C) = -(R - C)) (hCP : Commute C P) (hRC : Commute R C)
    (hgram : (P * R * P) * star (P * R * P) = (C * P) * (C * P)) :
    P * R * P = C * P := by
  let K := R - C
  let H := P * K * P
  let L := C * P
  have hPP : P * P = P := hP.isIdempotentElem.eq
  have hPstar : star P = P := hP.isSelfAdjoint.star_eq
  have hCK : Commute C K := hRC.symm.sub_right (Commute.refl C)
  have hCH : Commute C H := (hCP.mul_right hCK).mul_right hCP
  have hPH : Commute P H := by
    change P * (P * K * P) = (P * K * P) * P
    calc
      _ = (P * P) * K * P := by noncomm_ring
      _ = P * K * P := by rw [hPP]
      _ = (P * K) * (P * P) := by rw [hPP]
      _ = _ := by noncomm_ring
  have hLH : Commute L H := hCH.mul_left hPH
  have hL : IsSelfAdjoint L := by
    change star (C * P) = C * P
    rw [star_mul, hPstar, hC.star_eq]
    exact hCP.eq.symm
  have hH : star H = -H := by
    change star (P * K * P) = -(P * K * P)
    rw [star_mul, star_mul, hPstar, show star K = -K from hskew]
    noncomm_ring
  have hPCP : P * C * P = L := by
    change P * C * P = C * P
    rw [← hCP.eq, mul_assoc, hPP]
  have hcomp : P * R * P = L + H := by
    have hR : R = C + K := by dsimp [K]; abel
    rw [hR, mul_add, add_mul, hPCP]
  have hzero : H = 0 := skew_eq_zero_of_gram_eq_real_sq L H hL hH hLH (by
    rw [← hcomp]
    exact hgram)
  rw [hcomp, hzero, add_zero]

end TauCeti
