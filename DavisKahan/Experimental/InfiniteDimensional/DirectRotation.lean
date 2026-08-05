/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.SpectralTheory.GraphSubspace
import DavisKahan.Experimental.InfiniteDimensional.DoubleAngle

/-!
# Infinite-dimensional direct rotations

Literature writeup: local TeX, Section 25.  The direct rotation is the
canonical unitary transporting one acute closed subspace to another.
-/


/-! ## Construction plan

Define `directRotation U V` as the unitary polar factor of
`Q P + Qperp Pperp` under the acute hypothesis.  First prove the positive
factor is invertible, then prove the polar factor maps `U` onto `V` and
intertwines the projections.  The symmetry, square, minimality, and
trigonometric formulas should be consequences of uniqueness of the acute
unitary and the operator-angle functional calculus, not separate choices.
-/


/-! ## Weak-agent execution plan: bounded direct rotation

Let `P,Q` be the two orthogonal projections and
`S := QP + QᗮPᗮ`.  Prove acuteness makes `S` bounded below, hence invertible.
Define the direct rotation as the unitary polar factor
`S (S* S)^(-1/2)`.  Add named lemmas for:

* `S P = Q S`;
* `S* S` commutes with `P`;
* the inverse square root commutes with `P`;
* the polar factor intertwines `P,Q`;
* reversal of the pair takes adjoints.

Prove mapping and square identities before any extremality theorem.  For the
operator-norm minimizer, reduce to the Halmos generic two-projection block and
prove the scalar fiber inequality.  Do not generalize that result to arbitrary
symmetric ideals without a separate majorization theorem.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-! The scalar-action and continuous-functional-calculus assumptions under which
`operatorAbsoluteValue` is defined in `SinTheta/General`.  Mathlib supplies the
last one for `𝕜 = ℂ`; see the discussion there. -/
variable [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
  [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]

attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

/-! ## Canonical intertwiner and its polar data

`operatorAbsoluteValue` is the absolute value from `SinTheta/General`, which is
now a real definition (`CFC.abs`) rather than a leaf obligation.  **Two former
leaf obligations of this file are therefore proved below rather than assumed**:
the square identity `|S|² = S⋆S` and the self-adjointness of `|S|`.  Both were
previously unprovable rather than merely unproved — an escaped `def` is an
opaque term, so nothing about it can be established.

The invertibility of the intertwiner and of its absolute value on acute pairs
were on that list until 2026-08-04 and are now proved: the Gram operator is
`1 - (P - Q)^2`, and acuteness *is* `‖P - Q‖ < 1`, so the Neumann series inverts
it.

`directRotation_sq` was on that list too, and — like the commutation lemma
below — did not belong there.  Both Gram operators of `S` equal `1 - (P - Q)^2`,
so `S` is **normal**; the square identity then reduces to two ring identities in
`P` and `Q` and one cancellation of a unit.  See the section on it below.  The
Halmos two-projection decomposition is now used by `directRotation_minimal`
alone, and there it is genuinely needed: the statement is an inequality between
operator norms, not an algebraic identity.

The commutation of the absolute value with the projection was on that list
until 2026-07-30 and did not belong there: it needs no polar decomposition and
no invertibility, only that `S⋆S` commutes with `P_U` and that `|S|` is a
functional calculus applied to `S⋆S`.  It is proved below.
-/

/-- The canonical intertwiner `S = P_V P_U + P_{Vᗮ} P_{Uᗮ}`. -/
noncomputable def canonicalIntertwiner (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  projection V ∘L projection U +
    complementaryProjection V ∘L complementaryProjection U

/-- The square of the absolute value is `S⋆S`.

Formerly a leaf obligation; it is now `CFC.abs_mul_abs` transported across
`ContinuousLinearMap.mul_def`, which identifies composition with the ring
multiplication of `E →L[𝕜] E`. -/
theorem operatorAbsoluteValue_sq (S : E →L[𝕜] E) :
    operatorAbsoluteValue S ∘L operatorAbsoluteValue S = star S ∘L S := by
  rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def,
    operatorAbsoluteValue_eq]
  exact CFC.abs_mul_abs S

/-- The absolute value is self-adjoint.

Formerly a leaf obligation; it now follows from nonnegativity in the Loewner
order, since a nonnegative element of a star-ordered ring is self-adjoint. -/
theorem operatorAbsoluteValue_isSelfAdjoint (S : E →L[𝕜] E) :
    IsSelfAdjoint (operatorAbsoluteValue S) :=
  (operatorAbsoluteValue_nonneg S).isSelfAdjoint

/-! ### Invertibility on acute pairs

Formerly four leaf obligations.  They are all one computation: the Gram operator
of `S = QP + Q'P'` is

`S⋆S = S S⋆ = 1 − (P − Q)²`,

so acuteness — which *is* `‖P − Q‖ < 1` — puts the Gram operator within distance
`‖P − Q‖² < 1` of the identity, where the Neumann series inverts it.  An element
of a monoid whose products with a fixed element are units on both sides is
itself a unit, so `S` and `|S|` follow. -/

/-- An element with a left inverse and a right inverse is a unit: the two
inverses coincide.  Stated for a bare monoid because both uses below — the
intertwiner against its adjoint, and its absolute value against itself — have
that shape. -/
private theorem isUnit_of_isUnit_mul_both {R : Type*} [Monoid R] {a b : R}
    (hl : IsUnit (b * a)) (hr : IsUnit (a * b)) : IsUnit a := by
  obtain ⟨u, hu⟩ := hl
  obtain ⟨v, hv⟩ := hr
  have hla : ((↑u⁻¹ : R) * b) * a = 1 := by
    rw [mul_assoc, ← hu, u.inv_mul]
  have har : a * (b * (↑v⁻¹ : R)) = 1 := by
    rw [← mul_assoc, ← hv, v.mul_inv]
  have hlr : (↑u⁻¹ : R) * b = b * (↑v⁻¹ : R) := by
    calc (↑u⁻¹ : R) * b = ((↑u⁻¹ : R) * b) * 1 := (mul_one _).symm
      _ = ((↑u⁻¹ : R) * b) * (a * (b * (↑v⁻¹ : R))) := by rw [har]
      _ = (((↑u⁻¹ : R) * b) * a) * (b * (↑v⁻¹ : R)) := (mul_assoc _ _ _).symm
      _ = 1 * (b * (↑v⁻¹ : R)) := by rw [hla]
      _ = b * (↑v⁻¹ : R) := one_mul _
  exact ⟨⟨a, (↑u⁻¹ : R) * b, by rw [hlr]; exact har, hla⟩, rfl⟩

/-- **The Gram operator of the canonical intertwiner is `1 − (P − Q)²`.**

Expanding `S⋆S = (PQ + P'Q')(QP + Q'P')` and using `QQ' = 0` leaves
`PQP + P'Q'P'`, which is Halmos's squared cosine. -/
theorem adjoint_mul_canonicalIntertwiner (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    star (canonicalIntertwiner U V) * canonicalIntertwiner U V =
      1 - (projection U - projection V) * (projection U - projection V) := by
  have hP : projection U * projection U = projection U :=
    U.isIdempotentElem_starProjection
  have hQ : projection V * projection V = projection V :=
    V.isIdempotentElem_starProjection
  have hQQ : ∀ X : E →L[𝕜] E, projection V * (projection V * X) = projection V * X :=
    fun X => by rw [← mul_assoc, hQ]
  have hPc : complementaryProjection U = 1 - projection U :=
    U.starProjection_orthogonal'
  have hQc : complementaryProjection V = 1 - projection V :=
    V.starProjection_orthogonal'
  rw [canonicalIntertwiner, hPc, hQc]
  simp only [← ContinuousLinearMap.mul_def, star_add, star_mul, star_sub, star_one,
    (isSelfAdjoint_starProjection U).star_eq, (isSelfAdjoint_starProjection V).star_eq]
  noncomm_ring [hP, hQ]
  simp only [hQQ]
  abel

/-- **The same on the other side**: `S S⋆ = 1 − (P − Q)²` as well, since
`(Q − P)² = (P − Q)²`. -/
theorem canonicalIntertwiner_mul_adjoint (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    canonicalIntertwiner U V * star (canonicalIntertwiner U V) =
      1 - (projection U - projection V) * (projection U - projection V) := by
  have hP : projection U * projection U = projection U :=
    U.isIdempotentElem_starProjection
  have hQ : projection V * projection V = projection V :=
    V.isIdempotentElem_starProjection
  have hPP : ∀ X : E →L[𝕜] E, projection U * (projection U * X) = projection U * X :=
    fun X => by rw [← mul_assoc, hP]
  have hPc : complementaryProjection U = 1 - projection U :=
    U.starProjection_orthogonal'
  have hQc : complementaryProjection V = 1 - projection V :=
    V.starProjection_orthogonal'
  rw [canonicalIntertwiner, hPc, hQc]
  simp only [← ContinuousLinearMap.mul_def, star_add, star_mul, star_sub, star_one,
    (isSelfAdjoint_starProjection U).star_eq, (isSelfAdjoint_starProjection V).star_eq]
  noncomm_ring [hP, hQ]
  simp only [hPP]
  abel

/-- **On an acute pair the Gram operator is a unit**, by the Neumann series:
`‖(P − Q)²‖ ≤ ‖P − Q‖² < 1`. -/
theorem isUnit_one_sub_projection_sub_sq (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    IsUnit (1 - (projection U - projection V) * (projection U - projection V) :
      E →L[𝕜] E) := by
  have hgap : ‖(projection U - projection V : E →L[𝕜] E)‖ < 1 := hacute
  have hnn : (0 : ℝ) ≤ ‖(projection U - projection V : E →L[𝕜] E)‖ := norm_nonneg _
  have hnorm : ‖((projection U - projection V) * (projection U - projection V) :
      E →L[𝕜] E)‖ < 1 := by
    refine lt_of_le_of_lt (norm_mul_le _ _) ?_
    nlinarith
  exact (Units.val_oneSub _ hnorm) ▸ (Units.oneSub _ hnorm).isUnit

/-- **On an acute pair the canonical intertwiner is a unit.** -/
theorem isUnit_canonicalIntertwiner (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : IsUnit (canonicalIntertwiner U V) :=
  isUnit_of_isUnit_mul_both
    ((adjoint_mul_canonicalIntertwiner U V) ▸
      isUnit_one_sub_projection_sub_sq U V hacute)
    ((canonicalIntertwiner_mul_adjoint U V) ▸
      isUnit_one_sub_projection_sub_sq U V hacute)

/-- **On an acute pair the absolute value of the canonical intertwiner is a
unit**, since `|S|² = S⋆S`. -/
theorem isUnit_operatorAbsoluteValue_canonicalIntertwiner (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    IsUnit (operatorAbsoluteValue (canonicalIntertwiner U V)) := by
  have hsq : operatorAbsoluteValue (canonicalIntertwiner U V) *
      operatorAbsoluteValue (canonicalIntertwiner U V) =
      1 - (projection U - projection V) * (projection U - projection V) := by
    rw [ContinuousLinearMap.mul_def, operatorAbsoluteValue_sq,
      ← ContinuousLinearMap.mul_def, adjoint_mul_canonicalIntertwiner]
  have h := hsq ▸ isUnit_one_sub_projection_sub_sq U V hacute
  exact isUnit_of_isUnit_mul_both h h

/-- On an acute pair the canonical intertwiner is a unit:
`S⋆S = 1 − (P − Q)²` is within distance `‖P − Q‖² < 1` of the identity. -/
noncomputable def canonicalIntertwinerUnit (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : (E →L[𝕜] E)ˣ :=
  (isUnit_canonicalIntertwiner U V hacute).unit

/-- The intertwiner unit carries the canonical intertwiner. -/
theorem coe_canonicalIntertwinerUnit (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    ((canonicalIntertwinerUnit U V hacute : (E →L[𝕜] E)ˣ) : E →L[𝕜] E) =
      canonicalIntertwiner U V :=
  (isUnit_canonicalIntertwiner U V hacute).unit_spec

/-- On an acute pair the absolute value of the canonical intertwiner is a
unit. -/
noncomputable def canonicalAbsoluteValueUnit (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : (E →L[𝕜] E)ˣ :=
  (isUnit_operatorAbsoluteValue_canonicalIntertwiner U V hacute).unit

/-- The absolute-value unit carries the absolute value of the canonical
intertwiner. -/
theorem coe_canonicalAbsoluteValueUnit (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    ((canonicalAbsoluteValueUnit U V hacute : (E →L[𝕜] E)ˣ) : E →L[𝕜] E) =
      operatorAbsoluteValue (canonicalIntertwiner U V) :=
  (isUnit_operatorAbsoluteValue_canonicalIntertwiner U V hacute).unit_spec

omit [CompleteSpace E] [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
  [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint] in
/-- The canonical intertwiner carries the source projection to the target
projection: `S P_U = P_V S`. -/
theorem canonicalIntertwiner_intertwines (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    canonicalIntertwiner U V ∘L projection U =
      projection V ∘L canonicalIntertwiner U V := by
  ext x
  have hPP : U.starProjection (U.starProjection x) = U.starProjection x :=
    U.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
  have hP'P : Uᗮ.starProjection (U.starProjection x) = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact Submodule.le_orthogonal_orthogonal U (U.starProjection_apply_mem x)
  have hQQ : V.starProjection (V.starProjection (U.starProjection x)) =
      V.starProjection (U.starProjection x) :=
    V.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem _)
  have hQQ' : V.starProjection
      (Vᗮ.starProjection (Uᗮ.starProjection x)) = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact Vᗮ.starProjection_apply_mem _
  simp only [canonicalIntertwiner, ContinuousLinearMap.comp_apply,
    add_apply, map_add]
  simp only [projection, complementaryProjection] at *
  rw [hPP, hP'P, map_zero, add_zero, hQQ, hQQ']
  rw [add_zero]

/-- **The absolute value of the canonical intertwiner commutes with the source
projection.**

The route is the one the leaf obligation this replaced already named: `S⋆S`
commutes with `P_U`, and `|S|` is a functional calculus applied to `S⋆S`, so it
inherits the commutation.

The first half is four rewrites of the intertwining relation `S P_U = P_V S`
(`canonicalIntertwiner_intertwines`) and its adjoint `P_U S⋆ = S⋆ P_V`:
`S⋆S P_U = S⋆ P_V S = P_U S⋆S`.  The second is `Commute.cfcₙ_nnreal`, since
`CFC.abs a` is by definition `CFC.sqrt (star a * a)`, itself `cfcₙ NNReal.sqrt`
of `star a * a` — so anything commuting with `S⋆S` commutes with `|S|`.

Note what is *not* needed: no polar decomposition, and no invertibility.  This
was grouped with the parked polar-decomposition campaign in the module header,
but only the neighbouring leaves belong there. -/
theorem canonicalAbsoluteValue_commutes_projection (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute (operatorAbsoluteValue (canonicalIntertwiner U V))
      (projection U) := by
  set S : E →L[𝕜] E := canonicalIntertwiner U V with hS
  have hint : S * projection U = projection V * S := by
    simpa only [ContinuousLinearMap.mul_def] using canonicalIntertwiner_intertwines U V
  have hstarU : star (projection U : E →L[𝕜] E) = projection U :=
    isSelfAdjoint_starProjection U
  have hstarV : star (projection V : E →L[𝕜] E) = projection V :=
    isSelfAdjoint_starProjection V
  have hadj : projection U * star S = star S * projection V := by
    have h := congrArg star hint
    rwa [star_mul, star_mul, hstarU, hstarV] at h
  have hcomm : Commute (star S * S) (projection U) := by
    show star S * S * projection U = projection U * (star S * S)
    calc star S * S * projection U = star S * (S * projection U) := by rw [mul_assoc]
      _ = star S * (projection V * S) := by rw [hint]
      _ = star S * projection V * S := by rw [mul_assoc]
      _ = projection U * star S * S := by rw [hadj]
      _ = projection U * (star S * S) := by rw [mul_assoc]
  exact hcomm.cfcₙ_nnreal _

/-- Canonical direct rotation.

Construction strategy: set

`S = P_V P_U + P_{Vᗮ} P_{Uᗮ}`.

For an acute pair, prove `S* S` is bounded below by a positive scalar.  Define
the direct rotation as the polar factor `S (S* S)^{-1/2}` using continuous
functional calculus.  This construction automatically yields a unitary that
intertwines the two projections and is stable under finite specialization. -/
noncomputable def directRotation (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : E →L[𝕜] E :=
  canonicalIntertwiner U V ∘L
    (↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E)

omit [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
  [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint] in
/-- A bounded operator with two-sided star inverse is unitary. -/
private theorem isUnitaryOperator_of_star_identities
    {W : E →L[𝕜] E}
    (hleft : star W ∘L W = 1) (hright : W ∘L star W = 1) :
    IsUnitaryOperator W := by
  constructor
  · intro x
    have happ := congrArg (fun T : E →L[𝕜] E => T x) hleft
    simp only [ContinuousLinearMap.comp_apply,
      one_apply_eq_self] at happ
    have hinner : ⟪W x, W x⟫_𝕜 = ⟪x, x⟫_𝕜 := by
      calc ⟪W x, W x⟫_𝕜
          = ⟪star W (W x), x⟫_𝕜 := by
            rw [ContinuousLinearMap.star_eq_adjoint,
              ContinuousLinearMap.adjoint_inner_left]
        _ = ⟪x, x⟫_𝕜 := by rw [happ]
    have hsq : ‖W x‖ ^ 2 = ‖x‖ ^ 2 := by
      have h1 := congrArg RCLike.re hinner
      rwa [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h1
    nlinarith [norm_nonneg (W x), norm_nonneg x, hsq,
      sq_nonneg (‖W x‖ - ‖x‖), sq_nonneg (‖W x‖ + ‖x‖)]
  · intro y
    refine ⟨star W y, ?_⟩
    have happ := congrArg (fun T : E →L[𝕜] E => T y) hright
    simpa only [ContinuousLinearMap.comp_apply,
      one_apply_eq_self] using happ

/-- The direct rotation is unitary. 

Lean proof route for a weaker agent:

1. For `S = QP+(I-Q)(I-P)`, show acuteness makes `S*S` bounded below and invertible.
2. Define the polar factor `W=S(S*S)^{-1/2}` and compute `W*W=I`.
3. Prove surjectivity from invertibility or similarly compute `WW*=I`.
4. Translate those identities to `IsUnitaryOperator`.


Ext-agent signature audit (GPT 5.6 High): Correct for acute pairs using the polar factor
of the canonical intertwiner.

Preferred dependency route: Construct the polar factor of `QP + QᗮPᗮ`; prove
intertwining before extremality, and use the Halmos decomposition only for the final
minimization theorem.
-/
theorem directRotation_unitary
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    IsUnitaryOperator (directRotation U V hacute) := by
  classical
  set S : E →L[𝕜] E := canonicalIntertwiner U V with hS
  set B : E →L[𝕜] E :=
    (↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E) with hB
  have hsq' : operatorAbsoluteValue S * operatorAbsoluteValue S =
      star S * S := operatorAbsoluteValue_sq S
  have hAself : star (operatorAbsoluteValue S) = operatorAbsoluteValue S :=
    (operatorAbsoluteValue_isSelfAdjoint S).star_eq
  have hAB : operatorAbsoluteValue S * B = 1 := by
    have h := (canonicalAbsoluteValueUnit U V hacute).mul_inv
    rwa [coe_canonicalAbsoluteValueUnit] at h
  have hBA : B * operatorAbsoluteValue S = 1 := by
    have h := (canonicalAbsoluteValueUnit U V hacute).inv_mul
    rwa [coe_canonicalAbsoluteValueUnit] at h
  have hstarB : star B = B := by
    have h1 : star B * operatorAbsoluteValue S = 1 := by
      have h := congrArg star hAB
      rwa [star_mul, hAself, star_one] at h
    calc star B = star B * (operatorAbsoluteValue S * B) := by
          rw [hAB, mul_one]
      _ = (star B * operatorAbsoluteValue S) * B := by rw [mul_assoc]
      _ = B := by rw [h1, one_mul]
  have hleft : star (directRotation U V hacute) ∘L
      directRotation U V hacute = 1 := by
    show star (S * B) * (S * B) = 1
    calc star (S * B) * (S * B)
        = star B * (star S * S) * B := by rw [star_mul]; noncomm_ring
      _ = star B * (operatorAbsoluteValue S * operatorAbsoluteValue S) *
            B := by rw [hsq']
      _ = B * (operatorAbsoluteValue S * operatorAbsoluteValue S) * B := by
          rw [hstarB]
      _ = (B * operatorAbsoluteValue S) * (operatorAbsoluteValue S * B) := by
          noncomm_ring
      _ = 1 := by rw [hBA, hAB, one_mul]
  have hunit : IsUnit (directRotation U V hacute) := by
    have h1 : IsUnit S := by
      rw [hS, ← coe_canonicalIntertwinerUnit U V hacute]
      exact (canonicalIntertwinerUnit U V hacute).isUnit
    have h2 : IsUnit B := by
      rw [hB]
      exact ((canonicalAbsoluteValueUnit U V hacute)⁻¹).isUnit
    exact h1.mul h2
  have hright : directRotation U V hacute ∘L
      star (directRotation U V hacute) = 1 := by
    have hinvW : star (directRotation U V hacute) = ↑hunit.unit⁻¹ := by
      have h1 : star (directRotation U V hacute) * ↑hunit.unit = 1 := by
        rw [hunit.unit_spec]
        exact hleft
      calc star (directRotation U V hacute)
          = star (directRotation U V hacute) *
              (↑hunit.unit * ↑hunit.unit⁻¹) := by
            rw [hunit.unit.mul_inv, mul_one]
        _ = (star (directRotation U V hacute) * ↑hunit.unit) *
              ↑hunit.unit⁻¹ := by rw [mul_assoc]
        _ = ↑hunit.unit⁻¹ := by rw [h1, one_mul]
    show directRotation U V hacute * star (directRotation U V hacute) = 1
    rw [hinvW]
    have h := hunit.unit.mul_inv
    rwa [hunit.unit_spec] at h
  exact isUnitaryOperator_of_star_identities hleft hright

/-- Intertwining of orthogonal projections. 

Lean proof route for a weaker agent:

1. Unfold the polar-factor construction of `directRotation`.
2. Prove the pre-polar operator `S = QP+(I-Q)(I-P)` satisfies `S P = Q S`.
3. Show `S*S` commutes with `P`; functional calculus then gives commutation of its inverse square root.
4. Reassemble to obtain `W P = Q W`.


Ext-agent signature audit (GPT 5.6 High): Correct; this is the foundational
direct-rotation theorem and should be proved before the range and square formulas.

Preferred dependency route: Construct the polar factor of `QP + QᗮPᗮ`; prove
intertwining before extremality, and use the Halmos decomposition only for the final
minimization theorem.
-/
theorem directRotation_intertwines
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    directRotation U V hacute ∘L projection U =
      projection V ∘L directRotation U V hacute := by
  have hS := canonicalIntertwiner_intertwines U V
  have hA := canonicalAbsoluteValue_commutes_projection U V
  have hAinv : Commute
      (↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E)
      (projection U) := by
    have hAu : Commute
        ((canonicalAbsoluteValueUnit U V hacute : (E →L[𝕜] E)ˣ) : E →L[𝕜] E)
        (projection U) := by
      rw [coe_canonicalAbsoluteValueUnit]
      exact hA
    exact hAu.units_inv_left
  ext x
  show canonicalIntertwiner U V
      ((↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E)
        (projection U x)) =
    projection V (canonicalIntertwiner U V
      ((↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E) x))
  have h1 : (↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E)
      (projection U x) = projection U
        ((↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E) x) := by
    have h := congrArg (fun T : E →L[𝕜] E => T x) hAinv.eq
    simpa only [mul_apply_eq_comp] using h
  have h2 : canonicalIntertwiner U V (projection U
      ((↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E) x)) =
    projection V (canonicalIntertwiner U V
      ((↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E) x)) := by
    have h := congrArg (fun T : E →L[𝕜] E => T
      ((↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E) x)) hS
    simpa only [ContinuousLinearMap.comp_apply] using h
  rw [h1, h2]

-- `directRotation_maps_subspace` stood here: the same statement as
-- `DavisKahan/FiniteDimensional/DirectRotation/Basic.lean`'s `directRotation_map_eq`,
-- under a different name, with a different proof, and with no consumer anywhere.  This
-- file does not import that one, which is why it grew its own; `--dup` matches
-- normalized statements and so was the only check that could see it.
/-! ### The square of the direct rotation

**This was parked as needing the Halmos two-projection decomposition — it does
not need it.**  The whole identity is symmetry algebra in the two symmetries
`J_U = 2P − 1` and `J_V = 2Q − 1`:

* `J_V J_U = 2S − 1`, a ring identity with no idempotency at all;
* `S` is **normal**, because the two Gram operators computed above are the *same*
  operator `1 − (P − Q)²`.  Normality is what makes `|S|` commute with `S`, and
  that is the only place a functional calculus enters;
* `S² = (2S − 1)(S⋆S)`, a ring identity modulo `P² = P`, `Q² = Q`.

Dividing the third by the invertible `S⋆S = |S|²` turns the polar factor's square
into `2S − 1`.  No reducing summands, no angle fibers, no scalar rotation
identity. -/

/-- **Polar cancellation in a bare monoid.**

If `a` commutes with the inverse of a unit `u`, and `a² = c u²`, then the "polar
factor" `a u⁻¹` squares to `c`.  Stated for a monoid because that is all the
direct-rotation square uses: the whole content is that `u⁻¹` can be moved past
`a` and then cancelled against `u`. -/
private theorem sq_mul_units_inv_eq {M : Type*} [Monoid M] {a c : M} {u : Mˣ}
    (hcomm : Commute ((↑u⁻¹ : M)) a) (hsq : a * a = c * ((u : M) * (u : M))) :
    a * (↑u⁻¹ : M) * (a * (↑u⁻¹ : M)) = c := by
  calc a * (↑u⁻¹ : M) * (a * (↑u⁻¹ : M))
      = a * ((↑u⁻¹ : M) * a) * (↑u⁻¹ : M) := by simp only [mul_assoc]
    _ = a * (a * (↑u⁻¹ : M)) * (↑u⁻¹ : M) := by rw [hcomm.eq]
    _ = a * a * ((↑u⁻¹ : M) * (↑u⁻¹ : M)) := by simp only [mul_assoc]
    _ = c * ((u : M) * (u : M)) * ((↑u⁻¹ : M) * (↑u⁻¹ : M)) := by rw [hsq]
    _ = c * ((u : M) * (((u : M) * (↑u⁻¹ : M)) * (↑u⁻¹ : M))) := by
        simp only [mul_assoc]
    _ = c := by rw [u.mul_inv, one_mul, u.mul_inv, mul_one]

/-- **The canonical intertwiner is normal.**

Both Gram operators were computed above and are literally the same operator
`1 − (P − Q)²`, so `S⋆S = S S⋆` needs no further work.  This is the fact that
lets the absolute value commute with `S` itself, not merely with `P_U`. -/
theorem canonicalIntertwiner_isStarNormal (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    star (canonicalIntertwiner U V) * canonicalIntertwiner U V =
      canonicalIntertwiner U V * star (canonicalIntertwiner U V) := by
  rw [adjoint_mul_canonicalIntertwiner, canonicalIntertwiner_mul_adjoint]

/-- **The absolute value commutes with the intertwiner itself.**

`S` is normal, so `S` commutes with `S⋆S`; the continuous functional calculus
transports that to `|S|`.  Compare `canonicalAbsoluteValue_commutes_projection`,
which is the same argument run against `P_U` instead of `S`. -/
theorem canonicalAbsoluteValue_commutes_canonicalIntertwiner (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute (operatorAbsoluteValue (canonicalIntertwiner U V))
      (canonicalIntertwiner U V) := by
  set S : E →L[𝕜] E := canonicalIntertwiner U V with hSdef
  have hcomm : Commute (star S * S) S := by
    show star S * S * S = S * (star S * S)
    calc star S * S * S = (S * star S) * S := by
          rw [hSdef, adjoint_mul_canonicalIntertwiner, canonicalIntertwiner_mul_adjoint]
      _ = S * (star S * S) := mul_assoc _ _ _
  exact hcomm.cfcₙ_nnreal _

omit [CompleteSpace E] [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
  [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint] in
/-- **The product of the two reflections is `2S − 1`.**

`J_V J_U = (2Q − 1)(2P − 1) = 4QP − 2P − 2Q + 1`, and `S = 2QP − P − Q + 1`, so
the two sides agree as *polynomials*: the identity needs neither idempotency nor
self-adjointness of the projections. -/
theorem reflectionOperator_mul_reflectionOperator_eq (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (V.reflectionOperator : E →L[𝕜] E) * U.reflectionOperator =
      canonicalIntertwiner U V + canonicalIntertwiner U V - 1 := by
  have hU : (U.reflectionOperator : E →L[𝕜] E) = projection U + projection U - 1 := by
    rw [Submodule.reflectionOperator_eq_two_smul_sub_id, two_smul]
    rfl
  have hV : (V.reflectionOperator : E →L[𝕜] E) = projection V + projection V - 1 := by
    rw [Submodule.reflectionOperator_eq_two_smul_sub_id, two_smul]
    rfl
  have hPc : complementaryProjection U = 1 - projection U :=
    U.starProjection_orthogonal'
  have hQc : complementaryProjection V = 1 - projection V :=
    V.starProjection_orthogonal'
  rw [hU, hV, canonicalIntertwiner, hPc, hQc]
  simp only [← ContinuousLinearMap.mul_def]
  noncomm_ring

/-- **The square identity for the intertwiner**: `S² = (2S − 1)(S⋆S)`.

With `S⋆S = 1 − (P − Q)²` this is a ring identity modulo `P² = P` and `Q² = Q`;
both sides normalise to `4QPQP − 2QPQ − 2PQP + QP + PQ − P − Q + 1`. -/
theorem canonicalIntertwiner_sq_eq (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    canonicalIntertwiner U V * canonicalIntertwiner U V =
      (canonicalIntertwiner U V + canonicalIntertwiner U V - 1) *
        (star (canonicalIntertwiner U V) * canonicalIntertwiner U V) := by
  have hP : projection U * projection U = projection U :=
    U.isIdempotentElem_starProjection
  have hQ : projection V * projection V = projection V :=
    V.isIdempotentElem_starProjection
  have hPP : ∀ X : E →L[𝕜] E, projection U * (projection U * X) = projection U * X :=
    fun X => by rw [← mul_assoc, hP]
  have hQQ : ∀ X : E →L[𝕜] E, projection V * (projection V * X) = projection V * X :=
    fun X => by rw [← mul_assoc, hQ]
  have hPc : complementaryProjection U = 1 - projection U :=
    U.starProjection_orthogonal'
  have hQc : complementaryProjection V = 1 - projection V :=
    V.starProjection_orthogonal'
  rw [adjoint_mul_canonicalIntertwiner, canonicalIntertwiner, hPc, hQc]
  simp only [← ContinuousLinearMap.mul_def]
  noncomm_ring [hP, hQ]
  simp only [hPP, hQQ]
  abel

/-- Square of the direct rotation is the product of reflections.

Proved from `canonicalIntertwiner_sq_eq` by cancelling the invertible Gram
operator: writing `W = S |S|⁻¹` and using that `|S|⁻¹` commutes with `S`,

`W² = S² (|S|²)⁻¹ = (2S − 1)(S⋆S)(S⋆S)⁻¹ = 2S − 1 = J_V J_U`.

Ext-agent signature audit (GPT 5.6 High): Correct with the stated reflection order for
the convention that the direct rotation maps `U` to `V`; verify the orientation on the
planar model before general assembly.
-/
theorem directRotation_sq
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    directRotation U V hacute ∘L directRotation U V hacute =
      reflectionOperator V ∘L reflectionOperator U := by
  -- `|S|` commutes with `S`, hence so does its inverse.
  have hcomm : Commute ((↑(canonicalAbsoluteValueUnit U V hacute)⁻¹ : E →L[𝕜] E))
      (canonicalIntertwiner U V) := by
    refine Commute.units_inv_left ?_
    rw [coe_canonicalAbsoluteValueUnit]
    exact canonicalAbsoluteValue_commutes_canonicalIntertwiner U V
  -- `|S|² = S⋆S`.
  have hAA : (↑(canonicalAbsoluteValueUnit U V hacute) : E →L[𝕜] E) *
      (↑(canonicalAbsoluteValueUnit U V hacute) : E →L[𝕜] E) =
      star (canonicalIntertwiner U V) * canonicalIntertwiner U V := by
    rw [coe_canonicalAbsoluteValueUnit, ContinuousLinearMap.mul_def,
      operatorAbsoluteValue_sq, ← ContinuousLinearMap.mul_def]
  -- `S² = (2S − 1) |S|²`.
  have hsq : canonicalIntertwiner U V * canonicalIntertwiner U V =
      (canonicalIntertwiner U V + canonicalIntertwiner U V - 1) *
        ((↑(canonicalAbsoluteValueUnit U V hacute) : E →L[𝕜] E) *
          (↑(canonicalAbsoluteValueUnit U V hacute) : E →L[𝕜] E)) := by
    rw [hAA]
    exact canonicalIntertwiner_sq_eq U V
  simp only [directRotation, ← ContinuousLinearMap.mul_def]
  rw [reflectionOperator_mul_reflectionOperator_eq]
  exact sq_mul_units_inv_eq hcomm hsq

/-! ### The direct rotation is the *principal* square root

`directRotation_sq` says `W² = J_V J_U`.  A unitary has many square roots, so on
its own that does not characterise `W`; Davis–Kahan 1970 Proposition 3.3 says
`W` is the **principal** one, i.e. the one whose Hermitian part is nonnegative.

That falls out of the same symmetry algebra, from a third ring identity:

`S + S⋆ = 2 S⋆S`.

Since `S⋆S = |S|²` and `|S|` commutes with both `S` and `S⋆`, dividing by `|S|`
gives `W + W⋆ = 2|S|`, which is nonnegative because `|S|` is, and invertible on
an acute pair because `|S|` is.  So the Hermitian part of `W` is not merely
nonnegative but bounded below: `W`'s spectrum misses the closed left half-plane
entirely, which is exactly the principal branch. -/

/-- **The Hermitian part of the intertwiner is its Gram operator**, doubled:
`S + S⋆ = 2 S⋆S`.

A ring identity modulo `P² = P` and `Q² = Q`: both sides normalise to
`2QP + 2PQ − 2P − 2Q + 2`. -/
theorem canonicalIntertwiner_add_adjoint_eq (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    canonicalIntertwiner U V + star (canonicalIntertwiner U V) =
      star (canonicalIntertwiner U V) * canonicalIntertwiner U V +
        star (canonicalIntertwiner U V) * canonicalIntertwiner U V := by
  have hP : projection U * projection U = projection U :=
    U.isIdempotentElem_starProjection
  have hQ : projection V * projection V = projection V :=
    V.isIdempotentElem_starProjection
  have hPc : complementaryProjection U = 1 - projection U :=
    U.starProjection_orthogonal'
  have hQc : complementaryProjection V = 1 - projection V :=
    V.starProjection_orthogonal'
  rw [adjoint_mul_canonicalIntertwiner, canonicalIntertwiner, hPc, hQc]
  simp only [← ContinuousLinearMap.mul_def, star_add, star_mul, star_sub, star_one,
    (isSelfAdjoint_starProjection U).star_eq, (isSelfAdjoint_starProjection V).star_eq]
  noncomm_ring [hP, hQ]

/-- **The absolute value commutes with the adjoint intertwiner too.**

Same argument as `canonicalAbsoluteValue_commutes_canonicalIntertwiner`, run on
`S⋆`: normality makes `S⋆` commute with `S⋆S`. -/
theorem canonicalAbsoluteValue_commutes_adjoint_canonicalIntertwiner (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute (operatorAbsoluteValue (canonicalIntertwiner U V))
      (star (canonicalIntertwiner U V)) := by
  set S : E →L[𝕜] E := canonicalIntertwiner U V with hSdef
  have hcomm : Commute (star S * S) (star S) := by
    show star S * S * star S = star S * (star S * S)
    calc star S * S * star S = star S * (S * star S) := mul_assoc _ _ _
      _ = star S * (star S * S) := by
          rw [hSdef, adjoint_mul_canonicalIntertwiner, canonicalIntertwiner_mul_adjoint]
  exact hcomm.cfcₙ_nnreal _

/-- **The Hermitian part of the direct rotation is `2|S|`.**

`W + W⋆ = |S|⁻¹(S + S⋆) = |S|⁻¹ · 2|S|² = 2|S|`.  This is Davis–Kahan 1970
Proposition 3.3's "principal": `W` is the square root of `J_V J_U` whose
Hermitian part is nonnegative. -/
theorem directRotation_add_adjoint
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    directRotation U V hacute + star (directRotation U V hacute) =
      operatorAbsoluteValue (canonicalIntertwiner U V) +
        operatorAbsoluteValue (canonicalIntertwiner U V) := by
  set S : E →L[𝕜] E := canonicalIntertwiner U V with hSdef
  set A : (E →L[𝕜] E)ˣ := canonicalAbsoluteValueUnit U V hacute with hAdef
  have hAcoe : ((A : (E →L[𝕜] E)ˣ) : E →L[𝕜] E) = operatorAbsoluteValue S :=
    coe_canonicalAbsoluteValueUnit U V hacute
  have hAstar : star ((A : (E →L[𝕜] E)ˣ) : E →L[𝕜] E) = (A : E →L[𝕜] E) := by
    rw [hAcoe]
    exact (operatorAbsoluteValue_isSelfAdjoint S).star_eq
  -- The inverse of a self-adjoint unit is self-adjoint.
  have hAinvstar : star ((↑A⁻¹ : E →L[𝕜] E)) = (↑A⁻¹ : E →L[𝕜] E) := by
    have h1 : (A : E →L[𝕜] E) * star ((↑A⁻¹ : E →L[𝕜] E)) = 1 := by
      have h := congrArg star (A.inv_mul)
      rwa [star_mul, hAstar, star_one] at h
    calc star ((↑A⁻¹ : E →L[𝕜] E))
        = 1 * star ((↑A⁻¹ : E →L[𝕜] E)) := (one_mul _).symm
      _ = ((↑A⁻¹ : E →L[𝕜] E) * (A : E →L[𝕜] E)) * star ((↑A⁻¹ : E →L[𝕜] E)) := by
          rw [A.inv_mul]
      _ = (↑A⁻¹ : E →L[𝕜] E) * ((A : E →L[𝕜] E) * star ((↑A⁻¹ : E →L[𝕜] E))) :=
          mul_assoc _ _ _
      _ = (↑A⁻¹ : E →L[𝕜] E) := by rw [h1, mul_one]
  -- `|S|⁻¹` commutes with `S` and with `S⋆`.
  have hcommS : Commute ((↑A⁻¹ : E →L[𝕜] E)) S := by
    refine Commute.units_inv_left ?_
    rw [hAcoe, hSdef]
    exact canonicalAbsoluteValue_commutes_canonicalIntertwiner U V
  have hcommSstar : Commute ((↑A⁻¹ : E →L[𝕜] E)) (star S) := by
    refine Commute.units_inv_left ?_
    rw [hAcoe, hSdef]
    exact canonicalAbsoluteValue_commutes_adjoint_canonicalIntertwiner U V
  have hAA : (A : E →L[𝕜] E) * (A : E →L[𝕜] E) = star S * S := by
    rw [hAcoe, ContinuousLinearMap.mul_def, operatorAbsoluteValue_sq,
      ← ContinuousLinearMap.mul_def]
  have hadd : S + star S = (A : E →L[𝕜] E) * (A : E →L[𝕜] E) +
      (A : E →L[𝕜] E) * (A : E →L[𝕜] E) := by
    rw [hAA, hSdef]
    exact canonicalIntertwiner_add_adjoint_eq U V
  have hW : star (S * (↑A⁻¹ : E →L[𝕜] E)) = (↑A⁻¹ : E →L[𝕜] E) * star S := by
    rw [star_mul, hAinvstar]
  rw [directRotation, ← ContinuousLinearMap.mul_def, ← hSdef, ← hAdef, hW, ← hAcoe]
  calc S * (↑A⁻¹ : E →L[𝕜] E) + (↑A⁻¹ : E →L[𝕜] E) * star S
      = (↑A⁻¹ : E →L[𝕜] E) * (S + star S) := by
        rw [mul_add, ← hcommS.eq]
    _ = (↑A⁻¹ : E →L[𝕜] E) *
          ((A : E →L[𝕜] E) * (A : E →L[𝕜] E) +
            (A : E →L[𝕜] E) * (A : E →L[𝕜] E)) := by rw [hadd]
    _ = (A : E →L[𝕜] E) + (A : E →L[𝕜] E) := by
        rw [mul_add, ← mul_assoc, A.inv_mul, one_mul]

/-- **The direct rotation has nonnegative Hermitian part** — it is the
*principal* square root of the reflection product, not merely a square root. -/
theorem nonneg_directRotation_add_adjoint
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    0 ≤ directRotation U V hacute + star (directRotation U V hacute) := by
  rw [directRotation_add_adjoint]
  exact add_nonneg (operatorAbsoluteValue_nonneg _) (operatorAbsoluteValue_nonneg _)

/-- **On an acute pair the Hermitian part is invertible**, so the spectrum of the
direct rotation misses the closed left half-plane: acuteness is what makes the
principal branch unambiguous. -/
theorem isUnit_directRotation_add_adjoint
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    IsUnit (directRotation U V hacute + star (directRotation U V hacute)) := by
  have hA : IsUnit (operatorAbsoluteValue (canonicalIntertwiner U V)) :=
    isUnit_operatorAbsoluteValue_canonicalIntertwiner U V hacute
  have htwo : IsUnit ((1 : E →L[𝕜] E) + 1) := by
    refine ⟨⟨(1 : E →L[𝕜] E) + 1, (2 : 𝕜)⁻¹ • (1 : E →L[𝕜] E), ?_, ?_⟩, rfl⟩
    · rw [mul_smul_comm, mul_one, ← two_smul 𝕜 (1 : E →L[𝕜] E), smul_smul,
        inv_mul_cancel₀ (two_ne_zero' 𝕜), one_smul]
    · rw [smul_mul_assoc, one_mul, ← two_smul 𝕜 (1 : E →L[𝕜] E), smul_smul,
        inv_mul_cancel₀ (two_ne_zero' 𝕜), one_smul]
  rw [directRotation_add_adjoint]
  have hfac : operatorAbsoluteValue (canonicalIntertwiner U V) +
      operatorAbsoluteValue (canonicalIntertwiner U V) =
      operatorAbsoluteValue (canonicalIntertwiner U V) * ((1 : E →L[𝕜] E) + 1) := by
    rw [mul_add, mul_one]
  rw [hfac]
  exact hA.mul htwo

/-- Direct rotation minimizes maximal displacement from the identity.

Proof strategy: reduce by the two-projection decomposition to scalar
`2 x 2` angle fibers.  On each generic fiber, every unitary carrying the first
line to the second has displacement at least that of the shorter rotation.
Take the supremum over the angle spectrum.  State and prove any necessary
angle restriction explicitly; do not infer an unrestricted extremal theorem
for arbitrary symmetric ideal gauges from the operator-norm result. 

Lean proof route for a weaker agent:

1. Reduce the pair of projections to the Halmos two-projection decomposition.
2. On each generic two-dimensional angle fiber, prove the shorter rotation minimizes `‖W-I‖` among unitaries sending the first line to the second.
3. Take the essential supremum over the angle spectrum and handle common/orthogonal summands separately.
4. Check that the stated acuteness hypothesis excludes the ambiguous `π/2` branch.


Ext-agent signature audit (GPT 5.6 High): Correct as an operator-norm extremal statement
for acute pairs. It must not be generalized automatically to every symmetric ideal
gauge.

Preferred dependency route: Construct the polar factor of `QP + QᗮPᗮ`; prove
intertwining before extremality, and use the Halmos decomposition only for the final
minimization theorem.
-/
theorem directRotation_minimal
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V)
    (W : E →L[𝕜] E) (hW : IsUnitaryOperator W)
    (hmap : U.map W.toLinearMap = V) :
    ‖directRotation U V hacute - ContinuousLinearMap.id 𝕜 E‖ ≤
      ‖W - ContinuousLinearMap.id 𝕜 E‖ :=
  -- **Leaf obligation.** Requires the Halmos two-projection decomposition
  -- framework (fiber norms, unitary transport constraint, scalar shorter
  -- rotation) — the parked polar-decomposition campaign; see the proof route
  -- above.
  sorry

end DavisKahanExt
end TauCeti