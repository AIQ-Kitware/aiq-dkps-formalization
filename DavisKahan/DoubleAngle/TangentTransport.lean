/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.DoubleAngle.AngleTransport
import DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedKyFan

/-!
# What the unbounded `tan 2Θ` block is

`unboundedReflectionTangent U Z = S · (C²)⁻¹ · C`, with `C = U.diagonalPart Z`
and `S = U.offDiagonalPart Z` the blocks of a self-adjoint involution `Z`
relative to `U ⊕ Uᗮ`.  Like the `sin 2Θ` block it is a proof vehicle, and the
question is what a symmetric ideal sees in it.

This module answers that, and the answer is not the same shape as the `sin 2Θ`
one.

`gram_unboundedReflectionTangent` shows the tangent's Gram operator is

`T⋆T = S² · (1 - S²)⁻¹`,

so the tangent is `S/√(1-S²)` in the functional calculus of the single
self-adjoint operator `S` -- exactly `tan` of the angle whose sine is `S`.  Two
elementary block identities do all the work, both consequences of `Z⋆ = Z` and
`Z² = 1`:

`C² + S² = 1`  and  `C S + S C = 0`.

The anticommutation is what makes `S²` commute with `C`, hence with `(C²)⁻¹`,
and the Gram computation collapses.

`starProjection_offDiagonal_sq` then identifies the `U` block of `S²` for the
reflection: it is `(sin 2Θ)²`, by the same `p r p r p = 4t² - 4t + p` identity
that drove `AngleTransport`.  So on `U` the tangent is `sin 2Θ / cos 2Θ`.

## Why this is a structure theorem and not an equality of gauges

`S` is block *off-diagonal*, so `S²` carries a `Uᗮ` block as well as the `U`
block, and `T` therefore has a `(1,2)` and a `(2,1)` block.  Its approximation
numbers are the two blocks' together.  The paper's `paperAbsTanTwoAngleOperatorC`
is a function of the angle operator and is supported on `U` alone.

That is a real difference, and it is why `AngleTransport`'s equality has no
counterpart here: the `sin 2Θ` block `P_U P_{Wᗮ}` is one-sided, this one is not.
The statements below say exactly what is true, and leave the comparison of the
two singular sequences open rather than asserting it.
-/

namespace TauCeti
namespace DavisKahan

open TauCeti.DavisKahan1970

universe v

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

section BlockAlgebra

variable {p p' z : E →L[𝕜] E}

private theorem block_sq_add
    (hp : p * p = p) (hp' : p' * p' = p') (hpp' : p * p' = 0) (hp'p : p' * p = 0)
    (hsum : p + p' = 1) (hz : z * z = 1) :
    (p * z * p + p' * z * p') * (p * z * p + p' * z * p')
      + (p * z * p' + p' * z * p) * (p * z * p' + p' * z * p) = 1 := by
  have a1 : ∀ x : E →L[𝕜] E, p * (p * x) = p * x := fun x => by rw [← mul_assoc, hp]
  have a2 : ∀ x : E →L[𝕜] E, p' * (p' * x) = p' * x := fun x => by rw [← mul_assoc, hp']
  have a3 : ∀ x : E →L[𝕜] E, p * (p' * x) = 0 := fun x => by
    rw [← mul_assoc, hpp', zero_mul]
  have a4 : ∀ x : E →L[𝕜] E, p' * (p * x) = 0 := fun x => by
    rw [← mul_assoc, hp'p, zero_mul]
  have hzz : ∀ x : E →L[𝕜] E, z * (z * x) = x := fun x => by rw [← mul_assoc, hz, one_mul]
  simp only [add_mul, mul_add, mul_assoc, a1, a2, a3, a4, mul_zero, add_zero, zero_add]
  calc p * (z * (p * (z * p))) + p' * (z * (p' * (z * p')))
        + (p' * (z * (p * (z * p'))) + p * (z * (p' * (z * p))))
      = p * (z * ((p + p') * (z * p))) + p' * (z * ((p' + p) * (z * p'))) := by
        simp only [add_mul, mul_add]; abel
    _ = p * (z * (z * p)) + p' * (z * (z * p')) := by
        rw [hsum, add_comm p' p, hsum]; simp
    _ = 1 := by rw [hzz, hzz, hp, hp', hsum]

private theorem block_anticomm
    (hp : p * p = p) (hp' : p' * p' = p') (hpp' : p * p' = 0) (hp'p : p' * p = 0)
    (hsum : p + p' = 1) (hz : z * z = 1) :
    (p * z * p + p' * z * p') * (p * z * p' + p' * z * p)
      + (p * z * p' + p' * z * p) * (p * z * p + p' * z * p') = 0 := by
  have a1 : ∀ x : E →L[𝕜] E, p * (p * x) = p * x := fun x => by rw [← mul_assoc, hp]
  have a2 : ∀ x : E →L[𝕜] E, p' * (p' * x) = p' * x := fun x => by rw [← mul_assoc, hp']
  have a3 : ∀ x : E →L[𝕜] E, p * (p' * x) = 0 := fun x => by
    rw [← mul_assoc, hpp', zero_mul]
  have a4 : ∀ x : E →L[𝕜] E, p' * (p * x) = 0 := fun x => by
    rw [← mul_assoc, hp'p, zero_mul]
  have hzz : ∀ x : E →L[𝕜] E, z * (z * x) = x := fun x => by rw [← mul_assoc, hz, one_mul]
  simp only [add_mul, mul_add, mul_assoc, a1, a2, a3, a4, mul_zero, add_zero, zero_add]
  calc p * (z * (p * (z * p'))) + p' * (z * (p' * (z * p)))
        + (p' * (z * (p * (z * p))) + p * (z * (p' * (z * p'))))
      = p * (z * ((p + p') * (z * p'))) + p' * (z * ((p' + p) * (z * p))) := by
        simp only [add_mul, mul_add]; abel
    _ = p * (z * (z * p')) + p' * (z * (z * p)) := by
        rw [hsum, add_comm p' p, hsum]; simp
    _ = 0 := by rw [hzz, hzz, hpp', hp'p]; abel

end BlockAlgebra


section Blocks

variable (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (Z : E →L[𝕜] E)

omit [CompleteSpace E] in
private theorem orthogonal_eq :
    Uᗮ.starProjection = (1 : E →L[𝕜] E) - U.starProjection := by
  ext x
  simp [Submodule.starProjection_orthogonal_apply]

omit [CompleteSpace E] in
private theorem proj_sq : U.starProjection * U.starProjection = U.starProjection := by
  ext x
  show U.starProjection (U.starProjection x) = U.starProjection x
  rw [Submodule.starProjection_eq_self_iff]
  exact U.starProjection_apply_mem x

omit [CompleteSpace E] in
private theorem proj_mul_orthogonal :
    U.starProjection * Uᗮ.starProjection = 0 := by
  rw [orthogonal_eq, mul_sub, mul_one, proj_sq, sub_self]

omit [CompleteSpace E] in
private theorem orthogonal_mul_proj :
    Uᗮ.starProjection * U.starProjection = 0 := by
  rw [orthogonal_eq, sub_mul, one_mul, proj_sq, sub_self]

omit [CompleteSpace E] in
private theorem orthogonal_sq :
    Uᗮ.starProjection * Uᗮ.starProjection = Uᗮ.starProjection := by
  rw [orthogonal_eq]
  have h := proj_sq (𝕜 := 𝕜) U
  noncomm_ring [h]

omit [CompleteSpace E] in
private theorem proj_add_orthogonal :
    U.starProjection + Uᗮ.starProjection = (1 : E →L[𝕜] E) := by
  rw [orthogonal_eq]; abel

/-- The diagonal part written as the two corner products. -/
theorem diagonalPart_eq_corners :
    U.diagonalPart Z
      = U.starProjection * Z * U.starProjection
        + Uᗮ.starProjection * Z * Uᗮ.starProjection := by
  rw [Submodule.diagonalPart_eq]
  rfl

/-- The off-diagonal part written as the two corner products. -/
theorem offDiagonalPart_eq_corners :
    U.offDiagonalPart Z
      = U.starProjection * Z * Uᗮ.starProjection
        + Uᗮ.starProjection * Z * U.starProjection := by
  have hsum := proj_add_orthogonal (𝕜 := 𝕜) U
  have hZ : Z = (U.starProjection + Uᗮ.starProjection) * Z
      * (U.starProjection + Uᗮ.starProjection) := by
    rw [hsum, one_mul, mul_one]
  rw [Submodule.offDiagonalPart_eq, diagonalPart_eq_corners]
  nth_rewrite 1 [hZ]
  noncomm_ring

end Blocks


section Identities

variable (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] {Z : E →L[𝕜] E}

/-- **`C² + S² = 1`.**  The blocks of a self-adjoint involution relative to
`U ⊕ Uᗮ` satisfy the Pythagorean identity: this is `Z² = 1` read on the diagonal. -/
theorem diagonalPart_sq_add_offDiagonalPart_sq (hZ : Z * Z = 1) :
    U.diagonalPart Z * U.diagonalPart Z
        + U.offDiagonalPart Z * U.offDiagonalPart Z = 1 := by
  rw [diagonalPart_eq_corners, offDiagonalPart_eq_corners]
  exact block_sq_add (proj_sq U) (orthogonal_sq U) (proj_mul_orthogonal U)
    (orthogonal_mul_proj U) (proj_add_orthogonal U) hZ

/-- **`C S + S C = 0`.**  The same identity read off the diagonal: the two blocks
of a self-adjoint involution anticommute. -/
theorem diagonalPart_anticommute_offDiagonalPart (hZ : Z * Z = 1) :
    U.diagonalPart Z * U.offDiagonalPart Z
        + U.offDiagonalPart Z * U.diagonalPart Z = 0 := by
  rw [diagonalPart_eq_corners, offDiagonalPart_eq_corners]
  exact block_anticomm (proj_sq U) (orthogonal_sq U) (proj_mul_orthogonal U)
    (orthogonal_mul_proj U) (proj_add_orthogonal U) hZ

/-- Anticommuting with `C` makes `S²` *commute* with `C`. -/
theorem offDiagonalPart_sq_commute_diagonalPart (hZ : Z * Z = 1) :
    U.offDiagonalPart Z * U.offDiagonalPart Z * U.diagonalPart Z
      = U.diagonalPart Z * (U.offDiagonalPart Z * U.offDiagonalPart Z) := by
  have h := diagonalPart_anticommute_offDiagonalPart U hZ
  have h1 : U.offDiagonalPart Z * U.diagonalPart Z
      = -(U.diagonalPart Z * U.offDiagonalPart Z) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
  calc U.offDiagonalPart Z * U.offDiagonalPart Z * U.diagonalPart Z
      = U.offDiagonalPart Z * (U.offDiagonalPart Z * U.diagonalPart Z) := by
        rw [mul_assoc]
    _ = U.offDiagonalPart Z * -(U.diagonalPart Z * U.offDiagonalPart Z) := by rw [h1]
    _ = -((U.offDiagonalPart Z * U.diagonalPart Z) * U.offDiagonalPart Z) := by
        noncomm_ring
    _ = -(-(U.diagonalPart Z * U.offDiagonalPart Z) * U.offDiagonalPart Z) := by rw [h1]
    _ = U.diagonalPart Z * (U.offDiagonalPart Z * U.offDiagonalPart Z) := by
        noncomm_ring


/-- The `U` corner of `S²`: only the `(1,2)(2,1)` product survives. -/
theorem corner_offDiagonalPart_sq (Z : E →L[𝕜] E) :
    U.starProjection * (U.offDiagonalPart Z * U.offDiagonalPart Z) * U.starProjection
      = U.starProjection * Z * Uᗮ.starProjection * Z * U.starProjection := by
  have a1 : ∀ x : E →L[𝕜] E, U.starProjection * (U.starProjection * x)
      = U.starProjection * x := fun x => by rw [← mul_assoc, proj_sq U]
  have a2 : ∀ x : E →L[𝕜] E, Uᗮ.starProjection * (Uᗮ.starProjection * x)
      = Uᗮ.starProjection * x := fun x => by rw [← mul_assoc, orthogonal_sq U]
  have a3 : ∀ x : E →L[𝕜] E, U.starProjection * (Uᗮ.starProjection * x) = 0 :=
    fun x => by rw [← mul_assoc, proj_mul_orthogonal U, zero_mul]
  have a4 : ∀ x : E →L[𝕜] E, Uᗮ.starProjection * (U.starProjection * x) = 0 :=
    fun x => by rw [← mul_assoc, orthogonal_mul_proj U, zero_mul]
  rw [offDiagonalPart_eq_corners]
  simp only [add_mul, mul_add, mul_assoc, a1, a2, a3, a4, mul_zero, zero_mul,
    add_zero, zero_add, proj_sq U]

private theorem commute_ring_inverse {A : Type*} [Ring A] {u x : A}
    (hu : IsUnit u) (h : x * u = u * x) :
    x * Ring.inverse u = Ring.inverse u * x := by
  have h1 : u * Ring.inverse u = 1 := Ring.mul_inverse_cancel u hu
  have h2 : Ring.inverse u * u = 1 := Ring.inverse_mul_cancel u hu
  calc x * Ring.inverse u
      = Ring.inverse u * u * (x * Ring.inverse u) := by rw [h2, one_mul]
    _ = Ring.inverse u * (u * x) * Ring.inverse u := by noncomm_ring
    _ = Ring.inverse u * (x * u) * Ring.inverse u := by rw [h]
    _ = Ring.inverse u * x * (u * Ring.inverse u) := by noncomm_ring
    _ = Ring.inverse u * x := by rw [h1, mul_one]

/-- **The Gram operator of the unbounded reflection tangent.**

`T⋆T = S² (1 - S²)⁻¹`, where `S` is the off-diagonal block.  So the tangent is a
function of `S` alone -- `S/√(1-S²)`, the tangent of the angle whose sine is `S`
-- and the diagonal block has cancelled out entirely.

Everything a unitarily invariant norm sees in `unboundedReflectionTangent` is
therefore determined by `S`. -/
theorem gram_unboundedReflectionTangent
    (hZsa : IsSelfAdjoint Z) (hZ : Z * Z = 1)
    (hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z)) :
    (unboundedReflectionTangent U Z).adjoint * unboundedReflectionTangent U Z
      = U.offDiagonalPart Z * U.offDiagonalPart Z *
          Ring.inverse (U.diagonalPart Z * U.diagonalPart Z) := by
  set C := U.diagonalPart Z with hCdef
  set S := U.offDiagonalPart Z with hSdef
  have hCsa : IsSelfAdjoint C := TauCeti.isSelfAdjoint_diagonalPart hZsa
  have hSsa : IsSelfAdjoint S := TauCeti.isSelfAdjoint_offDiagonalPart hZsa
  have hCCsa : star (C * C) = C * C := by
    rw [star_mul, hCsa.star_eq]
  have hJC : Ring.inverse (C * C) * (C * C) = 1 := Ring.inverse_mul_cancel _ hCC
  have hCJ : C * C * Ring.inverse (C * C) = 1 := Ring.mul_inverse_cancel _ hCC
  have hInvsa : star (Ring.inverse (C * C)) = Ring.inverse (C * C) := by
    have h2 := congrArg star hCJ
    rw [star_mul, hCCsa, star_one] at h2
    calc star (Ring.inverse (C * C))
        = star (Ring.inverse (C * C)) * (C * C * Ring.inverse (C * C)) := by
          rw [hCJ, mul_one]
      _ = star (Ring.inverse (C * C)) * (C * C) * Ring.inverse (C * C) :=
          (mul_assoc _ _ _).symm
      _ = Ring.inverse (C * C) := by rw [h2, one_mul]
  have hcomm : S * S * C = C * (S * S) :=
    offDiagonalPart_sq_commute_diagonalPart U hZ
  have hcommCC : S * S * (C * C) = C * C * (S * S) := by
    calc S * S * (C * C) = S * S * C * C := (mul_assoc _ _ _).symm
      _ = C * (S * S) * C := by rw [hcomm]
      _ = C * (S * S * C) := mul_assoc _ _ _
      _ = C * (C * (S * S)) := by rw [hcomm]
      _ = C * C * (S * S) := (mul_assoc _ _ _).symm
  have hcommInv : S * S * Ring.inverse (C * C)
      = Ring.inverse (C * C) * (S * S) := commute_ring_inverse hCC hcommCC
  have hCinv : C * Ring.inverse (C * C) = Ring.inverse (C * C) * C := by
    refine commute_ring_inverse hCC ?_
    rw [← mul_assoc]
  -- `C J J C = J`: the diagonal block cancels against the inverse of its square.
  have hCJJC : C * Ring.inverse (C * C) * (Ring.inverse (C * C) * C)
      = Ring.inverse (C * C) := by
    calc C * Ring.inverse (C * C) * (Ring.inverse (C * C) * C)
        = Ring.inverse (C * C) * C * (Ring.inverse (C * C) * C) := by rw [hCinv]
      _ = Ring.inverse (C * C) * (C * Ring.inverse (C * C)) * C := by
          simp only [mul_assoc]
      _ = Ring.inverse (C * C) * (Ring.inverse (C * C) * C) * C := by rw [hCinv]
      _ = Ring.inverse (C * C) * (Ring.inverse (C * C) * (C * C)) := by
          simp only [mul_assoc]
      _ = Ring.inverse (C * C) := by rw [hJC, mul_one]
  have hadj : (unboundedReflectionTangent U Z).adjoint
      = C * Ring.inverse (C * C) * S := by
    rw [unboundedReflectionTangent, ← ContinuousLinearMap.star_eq_adjoint,
      star_mul, star_mul, hCsa.star_eq, hSsa.star_eq, hInvsa, ← mul_assoc]
  rw [hadj, unboundedReflectionTangent]
  calc C * Ring.inverse (C * C) * S * (S * Ring.inverse (C * C) * C)
      = C * Ring.inverse (C * C) * (S * S * Ring.inverse (C * C) * C) := by
        simp only [mul_assoc]
    _ = C * Ring.inverse (C * C) * (Ring.inverse (C * C) * (S * S) * C) := by
        rw [hcommInv]
    _ = C * Ring.inverse (C * C) * (Ring.inverse (C * C) * (S * S * C)) := by
        simp only [mul_assoc]
    _ = C * Ring.inverse (C * C) * (Ring.inverse (C * C) * (C * (S * S))) := by
        rw [hcomm]
    _ = C * Ring.inverse (C * C) * (Ring.inverse (C * C) * C) * (S * S) := by
        simp only [mul_assoc]
    _ = Ring.inverse (C * C) * (S * S) := by rw [hCJJC]
    _ = S * S * Ring.inverse (C * C) := hcommInv.symm

/-- **The tangent's Gram operator, with the diagonal block eliminated.**

`T⋆T = S² (1 - S²)⁻¹`.  Combined with
`starProjection_offDiagonal_sq_reflection`, which identifies the `U` block of
`S²` as `(sin 2Θ)²`, this is the statement that the unbounded reflection tangent
is `sin 2Θ / cos 2Θ` there. -/
theorem gram_unboundedReflectionTangent_eq_offDiagonal
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] {Z : E →L[𝕜] E}
    (hZsa : IsSelfAdjoint Z) (hZ : Z * Z = 1)
    (hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z)) :
    (unboundedReflectionTangent U Z).adjoint * unboundedReflectionTangent U Z
      = U.offDiagonalPart Z * U.offDiagonalPart Z *
          Ring.inverse ((1 : E →L[𝕜] E)
            - U.offDiagonalPart Z * U.offDiagonalPart Z) := by
  have hpy : U.diagonalPart Z * U.diagonalPart Z
      = (1 : E →L[𝕜] E) - U.offDiagonalPart Z * U.offDiagonalPart Z := by
    rw [eq_sub_iff_add_eq]
    exact diagonalPart_sq_add_offDiagonalPart_sq U hZ
  rw [gram_unboundedReflectionTangent U hZsa hZ hCC, hpy]

end Identities

section Reflection

open TauCeti.DavisKahanExt

variable {Ec : Type v} [NormedAddCommGroup Ec] [InnerProductSpace ℂ Ec]
  [CompleteSpace Ec]

/-- **The `U` block of `S²` is `(sin 2Θ)²`.**

For the reflection in `V`, the off-diagonal block `S` of the reflection relative
to `U ⊕ Uᗮ` squares, on `U`, to the square of the paper's double-angle sine.
Together with `gram_unboundedReflectionTangent` this says the tangent is
`sin 2Θ / cos 2Θ` there: the `U` block of `T⋆T` is `sin²2Θ · (1 - sin²2Θ)⁻¹`. -/
theorem starProjection_offDiagonal_sq_reflection
    (U V : Submodule ℂ Ec) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.starProjection *
        (U.offDiagonalPart V.reflectionOperator *
          U.offDiagonalPart V.reflectionOperator) * U.starProjection
      = sinTwoAngleOperatorC U V * sinTwoAngleOperatorC U V := by
  rw [corner_offDiagonalPart_sq]
  have hRR : V.reflectionOperator * V.reflectionOperator = 1 :=
    V.reflectionOperator_involutive
  have hcompl : Uᗮ.starProjection = (1 : Ec →L[ℂ] Ec) - U.starProjection :=
    orthogonal_eq U
  have hangle : sinTwoAngleOperatorC U V * sinTwoAngleOperatorC U V
      = U.starProjection * ((reflectedU U V)ᗮ.starProjection) * U.starProjection := by
    rw [← sinAngleOperatorDirectedC_reflected_eq_sinTwoAngleOperatorC U V,
      sinAngleOperatorDirectedC_mul_self]
  rw [hangle, starProjection_orthogonal_eq (reflectedU U V), starProjection_reflectedU,
    hcompl]
  have hRform : (2 : Ec →L[ℂ] Ec) * V.starProjection - 1 = V.reflectionOperator := by
    rw [V.reflectionOperator_eq_two_smul_sub_id]
    ext x
    simp [two_smul]
  rw [hRform]
  have hpp : U.starProjection * U.starProjection = U.starProjection := proj_sq U
  calc U.starProjection * V.reflectionOperator *
        ((1 : Ec →L[ℂ] Ec) - U.starProjection) * V.reflectionOperator *
          U.starProjection
      = U.starProjection * (V.reflectionOperator * V.reflectionOperator) *
            U.starProjection
        - U.starProjection * V.reflectionOperator * U.starProjection *
            V.reflectionOperator * U.starProjection := by noncomm_ring
    _ = U.starProjection * ((1 : Ec →L[ℂ] Ec) -
            V.reflectionOperator * U.starProjection * V.reflectionOperator) *
          U.starProjection := by
        rw [hRR]; noncomm_ring

end Reflection

end DavisKahan
end TauCeti
