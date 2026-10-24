/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Tactic.NoncommRing

/-!
# A Hermitian direction detecting projection overlap

For star projections `A,B`, the element `A * B + B * A` has zero
compression to both complementary projections. Its compression to `A` is
`2 • (A * B * A)`, and the latter is nonzero precisely when `A * B` is
nonzero, provided the star operation is proper.

These elementary identities supply a direction supported on the large-phase
compressions in the constrained Schatten second-variation argument.
-/

public section

namespace TauCeti

variable {R : Type*} [Ring R] [StarRing R] {A B : R}

/-- The symmetrized product of self-adjoint elements is self-adjoint. -/
theorem isSelfAdjoint_projection_overlap
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (A * B + B * A) := by
  change star (A * B + B * A) = A * B + B * A
  simp only [star_add, star_mul, hA.star_eq, hB.star_eq, add_comm]

omit [StarRing R] in
/-- The compression of the symmetrized product to an idempotent. -/
theorem projection_overlap_compression (hA : IsIdempotentElem A) (B : R) :
    A * (A * B + B * A) * A = 2 • (A * B * A) := by
  calc
    A * (A * B + B * A) * A = (A * A) * B * A + A * B * (A * A) := by
      noncomm_ring
    _ = 2 • (A * B * A) := by rw [hA.eq]; simp only [two_nsmul, mul_assoc]

omit [StarRing R] in
/-- The complementary compression of the symmetrized product vanishes. -/
theorem projection_overlap_complement_compression (hA : IsIdempotentElem A) (B : R) :
    (1 - A) * (A * B + B * A) * (1 - A) = 0 := by
  calc
    (1 - A) * (A * B + B * A) * (1 - A) =
        ((1 - A) * A) * B * (1 - A) + (1 - A) * B * (A * (1 - A)) := by
      noncomm_ring
    _ = 0 := by rw [hA.one_sub_mul_self, hA.mul_one_sub_self]; simp

/-- In a proper star ring, zero compression of one star projection to
another is equivalent to orthogonality of their product. -/
theorem projection_compression_eq_zero_iff_mul_eq_zero [IsProperStar R]
    (hA : IsStarProjection A) (hB : IsStarProjection B) :
    A * B * A = 0 ↔ A * B = 0 := by
  constructor
  · intro hzero
    have hBA : B * A = 0 := by
      apply star_mul_self_eq_zero.1
      calc
        star (B * A) * (B * A) = A * B * A := by
          rw [star_mul, hA.isSelfAdjoint.star_eq, hB.isSelfAdjoint.star_eq]
          simp only [mul_assoc, hB.isIdempotentElem.mul_self_mul]
        _ = 0 := hzero
    have h := congrArg star hBA
    simpa only [star_mul, hA.isSelfAdjoint.star_eq, hB.isSelfAdjoint.star_eq, star_zero] using h
  · intro hzero
    rw [hzero, zero_mul]

end TauCeti
