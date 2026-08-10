/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Geometry.Polar.DirectRotationSquare
import DavisKahan.SpectralTheory.Complexification.FormTransport
import ForTauCeti.Analysis.InnerProductSpace.Complexification.FunctionalCalculus

/-!
# The direct rotation of two **real** closed subspaces

Standing assumption 1 of Davis--Kahan 1970 is that the Hilbert space is "real or
complex", and Section 3 is written at that generality.  The repository's Section 3
development is built over `ℂ`, because the polar decomposition it runs on is
supplied by Mathlib's continuous functional calculus, which is registered on
Hilbert-space operators only over `ℂ`.  That is a *representation* restriction,
not a mathematical one, and this module removes it in arbitrary dimension.

## The descent, and why it is available

`spectraDirectRotation U V` is the polar factor of the canonical intertwiner
`S = P_V P_U + P_Vᗮ P_Uᗮ`.  When `U` and `V` are complexifications of real
subspaces, `S` is the complexification of the corresponding real operator, hence
fixed by the canonical conjugation.  In the acute case `|S|` is invertible, and

  `W |S| = S`,  `conj |S| = |conj S| = |S|`,  `conj S = S`

force `conj W = W` by cancelling the unit `|S|`.  So the direct rotation itself
lies in the fixed-point algebra of the conjugation and therefore **is** the
complexification of a bounded operator on the real space
(`TauCeti.RealComplexification.complexify_realPartOperator`).

The one input that was missing before 2026-08-09 is
`TauCeti.RealComplexification.conjugateOperator_modulus`: the canonical
conjugation commutes with the operator modulus, with no continuity side
condition.

## What is proved here

`directRotationR U V hacute` is a bounded operator on the real space, and every
clause of Propositions 3.1 and 3.3 and of Corollary 3.2 is proved *about it*, as
a statement over `ℝ`: it is orthogonal, it intertwines the two projections, it
carries `U` onto `V` and `Uᗮ` onto `Vᗮ`, its square is the ordered reflection
product, its two diagonal blocks are the positive Halmos cosine, its numerical
range is nonnegative, positivity of the two diagonal blocks characterises it,
and reversing the pair takes its transpose.

Membership statements are *concluded*, not assumed: `directRotationR_maps_subspace`
concludes `U.map W = V` rather than taking it as a hypothesis.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: Definition 3.1, Propositions 3.1
  and 3.3, Corollary 3.2, and standing assumption 1.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental

open TauCeti.RealComplexification
open TauCeti.DavisKahan.Experimental.Foundation.RealComplexification

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

variable (U V : Submodule ℝ E)
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-! ## Acuteness of a real pair -/

omit [CompleteSpace E] in
/-- Acuteness of a real pair is symmetric.  The complex statement of this fact
lives in a `ℂ`-only section, so the real case is proved here from the same
scalar-generic ingredient. -/
theorem IsUniformlyAcuteReal.symm {U V : Submodule ℝ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : IsUniformlyAcute U V) : IsUniformlyAcute V U := by
  show subspaceGap V U < 1
  rw [subspaceGap, Submodule.projectionGap_comm]
  exact h

omit [CompleteSpace E] in
/-- Acuteness of a real pair passes to the complexified pair. -/
theorem isUniformlyAcute_complexifySubmodule (h : IsUniformlyAcute U V) :
    IsUniformlyAcute (complexifySubmodule U) (complexifySubmodule V) :=
  (isUniformlyAcute_complexifySubmodule_iff U V).2 h

/-! ## The real canonical intertwiner -/

/-- The canonical pre-polar intertwiner `P_V P_U + P_Vᗮ P_Uᗮ` of a **real**
pair. -/
def canonicalIntertwinerR : E →L[ℝ] E :=
  projection V * projection U +
    complementaryProjection V * complementaryProjection U

omit [CompleteSpace E] in
/-- The complexified real intertwiner is the intertwiner of the complexified
pair. -/
@[simp]
theorem complexify_canonicalIntertwinerR :
    complexify (canonicalIntertwinerR U V) =
      spectraCanonicalIntertwiner (complexifySubmodule U) (complexifySubmodule V) := by
  have hmul : ∀ A B : E →L[ℝ] E, complexify (A * B) = complexify A * complexify B := by
    intro A B
    simpa only [ContinuousLinearMap.mul_def] using complexify_comp A B
  show complexify (V.starProjection * U.starProjection +
      Vᗮ.starProjection * Uᗮ.starProjection) =
    (complexifySubmodule V).starProjection * (complexifySubmodule U).starProjection +
      (complexifySubmodule V)ᗮ.starProjection * (complexifySubmodule U)ᗮ.starProjection
  rw [starProjection_complexifySubmodule, starProjection_complexifySubmodule,
    starProjection_complexifySubmodule_orthogonal,
    starProjection_complexifySubmodule_orthogonal, complexify_add, hmul, hmul]

omit [CompleteSpace E] in
/-- The complexified intertwiner is fixed by the canonical conjugation. -/
theorem conjugateOperator_spectraCanonicalIntertwiner_complexifySubmodule :
    conjugateOperator
        (spectraCanonicalIntertwiner (complexifySubmodule U) (complexifySubmodule V)) =
      spectraCanonicalIntertwiner (complexifySubmodule U) (complexifySubmodule V) := by
  rw [← complexify_canonicalIntertwinerR]
  exact conjugateOperator_complexify _

/-- The modulus of the complexified intertwiner is fixed by the canonical
conjugation. -/
theorem conjugateOperator_spectraCanonicalAbsoluteValue_complexifySubmodule :
    conjugateOperator
        (spectraOperatorAbsoluteValue
          (spectraCanonicalIntertwiner (complexifySubmodule U) (complexifySubmodule V))) =
      spectraOperatorAbsoluteValue
        (spectraCanonicalIntertwiner (complexifySubmodule U) (complexifySubmodule V)) :=
  conjugateOperator_modulus_of_fixed
    (conjugateOperator_spectraCanonicalIntertwiner_complexifySubmodule U V)

/-- The positive Halmos cosine `|S|` of a **real** pair. -/
def canonicalAbsoluteValueR : E →L[ℝ] E :=
  realPartOperator
    (spectraOperatorAbsoluteValue
      (spectraCanonicalIntertwiner (complexifySubmodule U) (complexifySubmodule V)))

/-- The complexified real Halmos cosine is the modulus of the complexified
intertwiner. -/
@[simp]
theorem complexify_canonicalAbsoluteValueR :
    complexify (canonicalAbsoluteValueR U V) =
      spectraOperatorAbsoluteValue
        (spectraCanonicalIntertwiner (complexifySubmodule U) (complexifySubmodule V)) :=
  complexify_realPartOperator
    (conjugateOperator_spectraCanonicalAbsoluteValue_complexifySubmodule U V)

/-! ## The real direct rotation -/

variable {U V}

omit [CompleteSpace E] in
/-- Cancelling an invertible conjugation-fixed right factor.  If `W C = S` with
`C` invertible and both `C` and `S` conjugation-fixed, then so is `W`. -/
private theorem conjugateOperator_of_mul_unit
    {W C S : RealComplexification E →L[ℂ] RealComplexification E}
    (hCunit : IsUnit C) (hWC : W * C = S)
    (hC : conjugateOperator C = C) (hS : conjugateOperator S = S) :
    conjugateOperator W = W := by
  refine hCunit.mul_right_cancel ?_
  calc
    conjugateOperator W * C = conjugateOperator W * conjugateOperator C := by rw [hC]
    _ = conjugateOperator (W * C) := (conjugateOperator_mul _ _).symm
    _ = conjugateOperator S := by rw [hWC]
    _ = S := hS
    _ = W * C := hWC.symm

/-- The complexified direct rotation of a real acute pair is fixed by the
canonical conjugation: cancel the invertible modulus in `W |S| = S`. -/
theorem conjugateOperator_spectraDirectRotation_complexifySubmodule
    (hacute : IsUniformlyAcute U V) :
    conjugateOperator
        (spectraDirectRotation (complexifySubmodule U) (complexifySubmodule V)
          (isUniformlyAcute_complexifySubmodule U V hacute)) =
      spectraDirectRotation (complexifySubmodule U) (complexifySubmodule V)
        (isUniformlyAcute_complexifySubmodule U V hacute) := by
  refine conjugateOperator_of_mul_unit
    (isUnit_spectraCanonicalAbsoluteValue _ _
      (isUniformlyAcute_complexifySubmodule U V hacute))
    (S := spectraCanonicalIntertwiner (complexifySubmodule U) (complexifySubmodule V))
    ?_
    (conjugateOperator_spectraCanonicalAbsoluteValue_complexifySubmodule U V)
    (conjugateOperator_spectraCanonicalIntertwiner_complexifySubmodule U V)
  simpa only [ContinuousLinearMap.mul_def] using
    spectraDirectRotation_decomposition (complexifySubmodule U) (complexifySubmodule V)
      (isUniformlyAcute_complexifySubmodule U V hacute)

variable (U V)

/-- **The direct rotation of a pair of real closed subspaces**, in arbitrary
dimension: a bounded operator on the real Hilbert space.

Davis--Kahan 1970, Definition 3.1 and Proposition 3.1, over `ℝ`. -/
def directRotationR (hacute : IsUniformlyAcute U V) : E →L[ℝ] E :=
  realPartOperator
    (spectraDirectRotation (complexifySubmodule U) (complexifySubmodule V)
      (isUniformlyAcute_complexifySubmodule U V hacute))

/-- The complexified real direct rotation is the complex direct rotation of the
complexified pair.  This is the identity that makes every clause below a
statement about the real operator. -/
@[simp]
theorem complexify_directRotationR (hacute : IsUniformlyAcute U V) :
    complexify (directRotationR U V hacute) =
      spectraDirectRotation (complexifySubmodule U) (complexifySubmodule V)
        (isUniformlyAcute_complexifySubmodule U V hacute) :=
  complexify_realPartOperator
    (conjugateOperator_spectraDirectRotation_complexifySubmodule hacute)

/-! ### Transport toolkit

`complexify` is an injective unital `⋆`-algebra map from the real bounded
operators to the operators on the complexification, so every *identity* below is
proved by complexifying it and citing the complex theorem. -/

omit [CompleteSpace E] in
/-- Complexification is multiplicative for the operator product. -/
theorem complexify_mul (A B : E →L[ℝ] E) :
    complexify (A * B) = complexify A * complexify B := by
  simpa only [ContinuousLinearMap.mul_def] using complexify_comp A B

omit [CompleteSpace E] in
/-- Complexification is unital. -/
theorem complexify_one : complexify (1 : E →L[ℝ] E) = 1 := complexify_id

/-- Complexification commutes with the adjoint written as `star`. -/
theorem complexify_star (A : E →L[ℝ] E) :
    complexify (star A) = star (complexify A) := by
  simpa only [ContinuousLinearMap.star_eq_adjoint] using complexify_adjoint A

omit [CompleteSpace E] in
/-- Complexification carries the real reflection to the reflection through the
complexified subspace. -/
@[simp]
theorem complexify_reflectionOperator :
    complexify U.reflectionOperator = (complexifySubmodule U).reflectionOperator := by
  rw [Submodule.reflectionOperator_eq_two_smul_sub_id,
    Submodule.reflectionOperator_eq_two_smul_sub_id, complexify_sub,
    complexify_real_smul, complexify_id, starProjection_complexifySubmodule]
  norm_num

omit [CompleteSpace E] in
/-- Complexification carries the real orthogonal projection to the projection
onto the complexified subspace. -/
@[simp]
theorem complexify_projection :
    complexify (projection U) = projection (complexifySubmodule U) :=
  (starProjection_complexifySubmodule U).symm

omit [CompleteSpace E] in
/-- Complexification carries the real complementary projection to the
complementary projection of the complexified subspace. -/
@[simp]
theorem complexify_complementaryProjection :
    complexify (complementaryProjection U) =
      complementaryProjection (complexifySubmodule U) :=
  (starProjection_complexifySubmodule_orthogonal U).symm

/-- Complexification carries an orthogonal operator to a unitary one. -/
theorem complexify_mem_unitary {W : E →L[ℝ] E} (hW : W ∈ unitary (E →L[ℝ] E)) :
    complexify W ∈
      unitary (RealComplexification E →L[ℂ] RealComplexification E) := by
  rw [Unitary.mem_iff] at hW ⊢
  refine ⟨?_, ?_⟩
  · rw [← complexify_star, ← complexify_mul, hW.1, complexify_one]
  · rw [← complexify_star, ← complexify_mul, hW.2, complexify_one]

/-- Complexification reflects orthogonality. -/
theorem mem_unitary_of_complexify {W : E →L[ℝ] E}
    (hW : complexify W ∈
      unitary (RealComplexification E →L[ℂ] RealComplexification E)) :
    W ∈ unitary (E →L[ℝ] E) := by
  rw [Unitary.mem_iff] at hW ⊢
  refine ⟨complexify_injective ?_, complexify_injective ?_⟩
  · rw [complexify_mul, complexify_star, complexify_one]; exact hW.1
  · rw [complexify_mul, complexify_star, complexify_one]; exact hW.2

omit [CompleteSpace E] in
/-- The real quadratic form is the complexified quadratic form on the real
copy. -/
theorem re_inner_complexify_ofReal (A : E →L[ℝ] E) (x : E) :
    Complex.re ⟪complexify A (ofReal x), ofReal x⟫_ℂ = ⟪A x, x⟫_ℝ := by
  have h := re_inner_complexify A (ofReal x)
  simp only [re_ofReal, im_ofReal, inner_zero_left, map_zero, add_zero] at h
  simpa only [RCLike.re_eq_complex_re] using h

omit [CompleteSpace E] in
/-- A nonnegative real quadratic form complexifies to a nonnegative one. -/
theorem re_inner_complexify_nonneg {A : E →L[ℝ] E}
    (h : ∀ x, 0 ≤ ⟪A x, x⟫_ℝ) (z : RealComplexification E) :
    0 ≤ Complex.re ⟪complexify A z, z⟫_ℂ := by
  have hz := re_inner_complexify A z
  rw [RCLike.re_eq_complex_re] at hz
  rw [hz]
  exact add_nonneg (h _) (h _)

omit [CompleteSpace E] in
/-- A quadratic form nonnegative on a real subspace complexifies to one
nonnegative on the complexified subspace. -/
theorem re_inner_complexify_nonneg_of_mem {A : E →L[ℝ] E} {W : Submodule ℝ E}
    (h : ∀ x ∈ W, 0 ≤ ⟪A x, x⟫_ℝ) {z : RealComplexification E}
    (hz : z ∈ complexifySubmodule W) :
    0 ≤ Complex.re ⟪complexify A z, z⟫_ℂ := by
  obtain ⟨hre, him⟩ := mem_complexifySubmodule.mp hz
  have hz' := re_inner_complexify A z
  rw [RCLike.re_eq_complex_re] at hz'
  rw [hz']
  exact add_nonneg (h _ hre) (h _ him)

/-! ### Proposition 3.1: the direct rotation is orthogonal and intertwines -/

/-- **The real direct rotation is orthogonal.** -/
theorem directRotationR_mem_unitary (hacute : IsUniformlyAcute U V) :
    directRotationR U V hacute ∈ unitary (E →L[ℝ] E) := by
  refine mem_unitary_of_complexify ?_
  rw [complexify_directRotationR]
  exact spectraDirectRotation_mem_unitary (complexifySubmodule U)
    (complexifySubmodule V) (isUniformlyAcute_complexifySubmodule U V hacute)

/-- The transpose is a left inverse of the real direct rotation. -/
theorem star_directRotationR_mul_self (hacute : IsUniformlyAcute U V) :
    star (directRotationR U V hacute) * directRotationR U V hacute = 1 :=
  Unitary.star_mul_self_of_mem (directRotationR_mem_unitary U V hacute)

/-- The transpose is a right inverse of the real direct rotation. -/
theorem directRotationR_mul_star_self (hacute : IsUniformlyAcute U V) :
    directRotationR U V hacute * star (directRotationR U V hacute) = 1 :=
  Unitary.mul_star_self_of_mem (directRotationR_mem_unitary U V hacute)

/-- The real direct rotation preserves norms. -/
theorem norm_directRotationR_apply (hacute : IsUniformlyAcute U V) (x : E) :
    ‖directRotationR U V hacute x‖ = ‖x‖ :=
  Unitary.norm_map
    (⟨directRotationR U V hacute, directRotationR_mem_unitary U V hacute⟩ :
      unitary (E →L[ℝ] E)) x

/-- The real direct rotation is surjective. -/
theorem directRotationR_surjective (hacute : IsUniformlyAcute U V) :
    Function.Surjective (directRotationR U V hacute) := by
  intro y
  refine ⟨star (directRotationR U V hacute) y, ?_⟩
  have h := congrArg (fun T : E →L[ℝ] E => T y) (directRotationR_mul_star_self U V hacute)
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using h

/-- The real direct rotation is injective. -/
theorem directRotationR_injective (hacute : IsUniformlyAcute U V) :
    Function.Injective (directRotationR U V hacute) := by
  intro x y hxy
  have hx := norm_directRotationR_apply U V hacute (x - y)
  rw [map_sub, hxy, sub_self, norm_zero] at hx
  exact sub_eq_zero.mp (norm_eq_zero.mp hx.symm)

/-- **The real direct rotation intertwines the two orthogonal projections.** -/
theorem directRotationR_intertwines (hacute : IsUniformlyAcute U V) :
    directRotationR U V hacute * projection U =
      projection V * directRotationR U V hacute := by
  refine complexify_injective ?_
  rw [complexify_mul, complexify_mul, complexify_directRotationR,
    complexify_projection, complexify_projection]
  exact spectraDirectRotation_intertwines _ _ _

/-- The real direct rotation intertwines the complementary projections. -/
theorem directRotationR_intertwines_complementary (hacute : IsUniformlyAcute U V) :
    directRotationR U V hacute * complementaryProjection U =
      complementaryProjection V * directRotationR U V hacute := by
  refine complexify_injective ?_
  rw [complexify_mul, complexify_mul, complexify_directRotationR,
    complexify_complementaryProjection, complexify_complementaryProjection]
  exact spectraDirectRotation_intertwines_complementary _ _ _

/-- Conjugating the source projection by the real direct rotation gives the
target projection. -/
theorem directRotationR_conjugates_projection (hacute : IsUniformlyAcute U V) :
    directRotationR U V hacute * projection U * star (directRotationR U V hacute) =
      projection V := by
  refine complexify_injective ?_
  rw [complexify_mul, complexify_mul, complexify_star, complexify_directRotationR,
    complexify_projection, complexify_projection]
  exact spectraDirectRotation_conjugates_projection _ _ _

/-- **The real direct rotation carries `U` onto `V`.**  The membership is
concluded, not assumed. -/
theorem directRotationR_maps_subspace (hacute : IsUniformlyAcute U V) :
    U.map (directRotationR U V hacute).toLinearMap = V := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    apply V.starProjection_eq_self_iff.mp
    have h := congrArg (fun T : E →L[ℝ] E => T x) (directRotationR_intertwines U V hacute)
    simp only [mul_apply_eq_comp] at h
    rw [U.starProjection_eq_self_iff.mpr hx] at h
    exact h.symm
  · intro y hy
    obtain ⟨x, rfl⟩ := directRotationR_surjective U V hacute y
    refine ⟨x, ?_, rfl⟩
    apply U.starProjection_eq_self_iff.mp
    apply directRotationR_injective U V hacute
    have h := congrArg (fun T : E →L[ℝ] E => T x) (directRotationR_intertwines U V hacute)
    simp only [mul_apply_eq_comp] at h
    rw [V.starProjection_eq_self_iff.mpr hy] at h
    exact h

/-- The real direct rotation carries `Uᗮ` onto `Vᗮ`. -/
theorem directRotationR_maps_orthogonalComplement (hacute : IsUniformlyAcute U V) :
    Uᗮ.map (directRotationR U V hacute).toLinearMap = Vᗮ := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    apply Vᗮ.starProjection_eq_self_iff.mp
    have h := congrArg (fun T : E →L[ℝ] E => T x)
      (directRotationR_intertwines_complementary U V hacute)
    simp only [mul_apply_eq_comp] at h
    rw [Uᗮ.starProjection_eq_self_iff.mpr hx] at h
    exact h.symm
  · intro y hy
    obtain ⟨x, rfl⟩ := directRotationR_surjective U V hacute y
    refine ⟨x, ?_, rfl⟩
    apply Uᗮ.starProjection_eq_self_iff.mp
    apply directRotationR_injective U V hacute
    have h := congrArg (fun T : E →L[ℝ] E => T x)
      (directRotationR_intertwines_complementary U V hacute)
    simp only [mul_apply_eq_comp] at h
    rw [Vᗮ.starProjection_eq_self_iff.mpr hy] at h
    exact h

/-! ### Proposition 3.3: the principal square root -/

/-- The real direct rotation intertwines the two reflections. -/
theorem directRotationR_intertwines_reflection (hacute : IsUniformlyAcute U V) :
    directRotationR U V hacute * U.reflectionOperator =
      V.reflectionOperator * directRotationR U V hacute := by
  refine complexify_injective ?_
  rw [complexify_mul, complexify_mul, complexify_directRotationR,
    complexify_reflectionOperator, complexify_reflectionOperator]
  exact spectraDirectRotation_intertwines_reflection _ _ _

/-- **Davis--Kahan 1970, Proposition 3.3, over `ℝ`, forward direction.**  The
square of the real direct rotation is the ordered product of the two
reflections. -/
theorem directRotationR_sq (hacute : IsUniformlyAcute U V) :
    directRotationR U V hacute * directRotationR U V hacute =
      V.reflectionOperator * U.reflectionOperator := by
  refine complexify_injective ?_
  rw [complexify_mul, complexify_mul, complexify_directRotationR,
    complexify_reflectionOperator, complexify_reflectionOperator]
  exact spectraDirectRotation_sq _ _ _

/-! ### The Hermitian part and the two diagonal blocks -/

/-- **The symmetric part of the real direct rotation is twice the positive
Halmos cosine.**  This is the "principal" clause of Proposition 3.3: the
symmetric part is nonnegative. -/
theorem directRotationR_add_star (hacute : IsUniformlyAcute U V) :
    directRotationR U V hacute + star (directRotationR U V hacute) =
      (2 : ℝ) • canonicalAbsoluteValueR U V := by
  refine complexify_injective ?_
  rw [complexify_add, complexify_star, complexify_real_smul,
    complexify_directRotationR, complexify_canonicalAbsoluteValueR]
  simpa using spectraDirectRotation_add_star_eq_two_smul_absoluteValue
    (complexifySubmodule U) (complexifySubmodule V)
    (isUniformlyAcute_complexifySubmodule U V hacute)

/-- **The source diagonal block of the real direct rotation is the positive
Halmos cosine.**  Proposition 3.1's block computation, over `ℝ`. -/
theorem projection_mul_directRotationR_mul_projection (hacute : IsUniformlyAcute U V) :
    projection U * directRotationR U V hacute * projection U =
      canonicalAbsoluteValueR U V * projection U := by
  refine complexify_injective ?_
  rw [complexify_mul, complexify_mul, complexify_mul, complexify_directRotationR,
    complexify_canonicalAbsoluteValueR, complexify_projection]
  exact projection_mul_spectraDirectRotation_mul_projection _ _ _

/-- The complementary diagonal block of the real direct rotation is the positive
Halmos cosine. -/
theorem complementaryProjection_mul_directRotationR_mul_complementaryProjection
    (hacute : IsUniformlyAcute U V) :
    complementaryProjection U * directRotationR U V hacute * complementaryProjection U =
      canonicalAbsoluteValueR U V * complementaryProjection U := by
  refine complexify_injective ?_
  rw [complexify_mul, complexify_mul, complexify_mul, complexify_directRotationR,
    complexify_canonicalAbsoluteValueR, complexify_complementaryProjection]
  exact complementaryProjection_mul_spectraDirectRotation_mul_complementaryProjection _ _ _

/-- **The numerical range of the real direct rotation is nonnegative.** -/
theorem directRotationR_real_inner_nonneg (hacute : IsUniformlyAcute U V) (x : E) :
    0 ≤ ⟪directRotationR U V hacute x, x⟫_ℝ := by
  rw [← re_inner_complexify_ofReal (directRotationR U V hacute) x,
    complexify_directRotationR]
  exact spectraDirectRotation_real_inner_nonneg _ _ _ _

/-! ### Proposition 3.1: uniqueness and the characterisation clause -/

/-- **Davis--Kahan 1970, Proposition 3.1, uniqueness clause, over `ℝ`.**  An
orthogonal square root of the reflection product with nonnegative numerical
range is the direct rotation. -/
theorem directRotationR_unique_of_sq (hacute : IsUniformlyAcute U V)
    (W : E →L[ℝ] E) (hWunit : W ∈ unitary (E →L[ℝ] E))
    (hsq : W * W = V.reflectionOperator * U.reflectionOperator)
    (hre : ∀ x, 0 ≤ ⟪W x, x⟫_ℝ) :
    W = directRotationR U V hacute := by
  refine complexify_injective ?_
  rw [complexify_directRotationR]
  refine spectraDirectRotation_unique_of_sq _ _ _ (complexify W)
    (complexify_mem_unitary hWunit) ?_ (re_inner_complexify_nonneg hre)
  rw [← complexify_mul, hsq, complexify_mul, complexify_reflectionOperator,
    complexify_reflectionOperator]

/-- **Davis--Kahan 1970, Proposition 3.1, characterisation clause, over `ℝ`.**
Nonnegativity of the two diagonal blocks characterises the direct rotation among
orthogonal square roots of the reflection product that intertwine the two
reflections. -/
theorem directRotationR_unique_of_diagonalBlocks (hacute : IsUniformlyAcute U V)
    (W : E →L[ℝ] E) (hWunit : W ∈ unitary (E →L[ℝ] E))
    (hsq : W * W = V.reflectionOperator * U.reflectionOperator)
    (hint : W * U.reflectionOperator = V.reflectionOperator * W)
    (hblockU : ∀ x ∈ U, 0 ≤ ⟪W x, x⟫_ℝ)
    (hblockUperp : ∀ x ∈ Uᗮ, 0 ≤ ⟪W x, x⟫_ℝ) :
    W = directRotationR U V hacute := by
  refine complexify_injective ?_
  rw [complexify_directRotationR]
  refine spectraDirectRotation_unique_of_diagonalBlocks _ _ _ (complexify W)
    (complexify_mem_unitary hWunit) ?_ ?_ ?_ ?_
  · rw [← complexify_mul, hsq, complexify_mul, complexify_reflectionOperator,
      complexify_reflectionOperator]
  · rw [← complexify_reflectionOperator, ← complexify_reflectionOperator,
      ← complexify_mul, ← complexify_mul, hint]
  · exact fun z hz => re_inner_complexify_nonneg_of_mem hblockU hz
  · refine fun z hz => re_inner_complexify_nonneg_of_mem hblockUperp ?_
    rwa [complexifySubmodule_orthogonal U]

/-- **Proposition 3.1's characterisation clause as a biconditional, over `ℝ`.** -/
theorem eq_directRotationR_iff_diagonalBlocks_nonneg (hacute : IsUniformlyAcute U V)
    (W : E →L[ℝ] E) :
    W = directRotationR U V hacute ↔
      W ∈ unitary (E →L[ℝ] E) ∧
        W * W = V.reflectionOperator * U.reflectionOperator ∧
        W * U.reflectionOperator = V.reflectionOperator * W ∧
        (∀ x ∈ U, 0 ≤ ⟪W x, x⟫_ℝ) ∧
        (∀ x ∈ Uᗮ, 0 ≤ ⟪W x, x⟫_ℝ) := by
  constructor
  · rintro rfl
    exact ⟨directRotationR_mem_unitary U V hacute, directRotationR_sq U V hacute,
      directRotationR_intertwines_reflection U V hacute,
      fun x _ => directRotationR_real_inner_nonneg U V hacute x,
      fun x _ => directRotationR_real_inner_nonneg U V hacute x⟩
  · rintro ⟨hWunit, hsq, hint, hblockU, hblockUperp⟩
    exact directRotationR_unique_of_diagonalBlocks U V hacute W hWunit hsq hint
      hblockU hblockUperp

/-! ### Corollary 3.2: reversal symmetry -/

/-- **Davis--Kahan 1970, Corollary 3.2, over `ℝ`.**  Reversing the ordered pair
transposes the direct rotation. -/
theorem directRotationR_reversal (hacute : IsUniformlyAcute U V) :
    directRotationR V U (IsUniformlyAcuteReal.symm hacute) =
      star (directRotationR U V hacute) := by
  refine complexify_injective ?_
  rw [complexify_star, complexify_directRotationR, complexify_directRotationR]
  exact spectraDirectRotation_reversal (complexifySubmodule U) (complexifySubmodule V)
    (isUniformlyAcute_complexifySubmodule U V hacute)

end

end Experimental
end DavisKahan
end TauCeti
