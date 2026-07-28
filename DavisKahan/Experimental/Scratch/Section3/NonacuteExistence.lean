/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Geometry.Polar.Section3Nonacute
import ForMathlib.Analysis.InnerProductSpace.CoerciveUnit

/-!
# Nonacute direct rotations: the crossed-defect necessity theorem

This scratch module isolates the hard converse direction in Davis--Kahan 1970,
Proposition 3.2.

The constructive direction already available in
`Geometry.Polar.Section3Nonacute` fills the crossed defect spaces
with a chosen unitary quarter-turn.  The missing converse is subtler: from the
paper's direct-rotation axioms one must recover a unitary equivalence

`U ∩ Vᗮ ≃ₗᵢ[ℂ] Uᗮ ∩ V`.

The key observation is that the crossed-block skew-adjointness makes the
Hermitian part `T + T⋆` block diagonal relative to `U ⊕ Uᗮ`, while the two
compression hypotheses make that Hermitian part nonnegative.  A source-defect
vector `x` is orthogonal to `T x`, because `T x ∈ V` and `x ∈ Vᗮ`; positivity
therefore forces `(T + T⋆) x = 0`.  The adjoint intertwining identity then gives
`T x ∈ Uᗮ`.  The dual argument sends the target defect back by `T⋆`.

This file is additive scratch work.  It intentionally does not edit the active
`MathAhead/HiddenFoundations/Section3Nonacute.lean` lane.
-/

open scoped InnerProductSpace

namespace TauCeti

open ForMathlib
namespace DavisKahan
namespace Experimental
namespace Scratch
namespace Section3

open Frontier
open SpectraBridge
open MathAhead.HiddenFoundations

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

private theorem re_inner_star_apply (T : H →L[ℂ] H) (x : H) :
    RCLike.re ⟪star T x, x⟫_ℂ = RCLike.re ⟪T x, x⟫_ℂ := by
  rw [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]
  exact inner_re_symm x (T x)

/-- The crossed-block axiom says that the Hermitian part of a paper direct
rotation has no off-diagonal blocks relative to `U ⊕ Uᗮ`. -/
theorem paperDirectRotation_hermitianPart_blockDiagonal
    (T : H →L[ℂ] H) (hT : IsPaperDirectRotation U V T) :
    T + star T =
      projection U * (T + star T) * projection U +
      complementaryProjection U * (T + star T) *
        complementaryProjection U := by
  let P : H →L[ℂ] H := projection U
  let Q : H →L[ℂ] H := complementaryProjection U
  let A : H →L[ℂ] H := T + star T
  have hPstar : star P = P := by
    exact (isSelfAdjoint_starProjection U).star_eq
  have hQstar : star Q = Q := by
    exact (isSelfAdjoint_starProjection Uᗮ).star_eq
  have hAstar : star A = A := by
    simp only [A, star_add, star_star, add_comm]
  have hQAP : Q * A * P = 0 := by
    calc
      Q * A * P = Q * T * P + Q * star T * P := by
        simp only [A, mul_add, add_mul]
      _ = -star (P * T * Q) + Q * star T * P := by
        simpa only [P, Q] using congrArg
          (fun S : H →L[ℂ] H => S + Q * star T * P)
          hT.crossed_blocks
      _ = -(Q * star T * P) + Q * star T * P := by
        rw [star_mul, star_mul, hQstar, hPstar, mul_assoc]
      _ = 0 := by abel
  have hPAQ : P * A * Q = 0 := by
    have h := congrArg star hQAP
    simpa only [star_mul, hPstar, hQstar, hAstar, star_zero,
      mul_assoc] using h
  have hPQ : P + Q = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    simpa only [P, Q, add_apply,
      one_apply_eq_self] using
      U.starProjection_add_starProjection_orthogonal x
  change A = P * A * P + Q * A * Q
  calc
    A = 1 * A * 1 := by simp
    _ = (P + Q) * A * (P + Q) := by rw [hPQ]
    _ = P * A * P + P * A * Q + Q * A * P + Q * A * Q := by
      noncomm_ring
    _ = P * A * P + Q * A * Q := by rw [hPAQ, hQAP]; noncomm_ring

/-- The Hermitian part of a paper direct rotation has a nonnegative quadratic
form on the whole Hilbert space. -/
theorem paperDirectRotation_hermitianPart_nonnegative
    (T : H →L[ℂ] H) (hT : IsPaperDirectRotation U V T) (x : H) :
    0 ≤ RCLike.re ⟪(T + star T) x, x⟫_ℂ := by
  let P : H →L[ℂ] H := projection U
  let Q : H →L[ℂ] H := complementaryProjection U
  let B : H →L[ℂ] H := P * T * P
  let C : H →L[ℂ] H := Q * T * Q
  have hPstar : star P = P := by
    exact (isSelfAdjoint_starProjection U).star_eq
  have hQstar : star Q = Q := by
    exact (isSelfAdjoint_starProjection Uᗮ).star_eq
  have hPB : P * (T + star T) * P = B + star B := by
    calc
      P * (T + star T) * P = P * T * P + P * star T * P := by
        simp only [mul_add, add_mul]
      _ = B + star B := by
        simp only [B, star_mul, hPstar, mul_assoc]
  have hQC : Q * (T + star T) * Q = C + star C := by
    calc
      Q * (T + star T) * Q = Q * T * Q + Q * star T * Q := by
        simp only [mul_add, add_mul]
      _ = C + star C := by
        simp only [C, star_mul, hQstar, mul_assoc]
  have hdiag : T + star T = (B + star B) + (C + star C) := by
    rw [paperDirectRotation_hermitianPart_blockDiagonal U V T hT,
      hPB, hQC]
  have hB : 0 ≤ RCLike.re ⟪B x, x⟫_ℂ := by
    rw [← inner_re_symm x (B x)]
    simpa only [B, P] using hT.source_compression_nonnegative x
  have hC : 0 ≤ RCLike.re ⟪C x, x⟫_ℂ := by
    rw [← inner_re_symm x (C x)]
    simpa only [C, Q] using hT.complement_compression_nonnegative x
  rw [hdiag]
  simp only [add_apply, inner_add_left, map_add,
    re_inner_star_apply]
  linarith

/-- For a paper direct rotation, vanishing numerical real part forces the
Hermitian part to annihilate the vector. -/
theorem paperDirectRotation_add_star_apply_eq_zero
    (T : H →L[ℂ] H) (hT : IsPaperDirectRotation U V T)
    {x : H} (hx : RCLike.re ⟪T x, x⟫_ℂ = 0) :
    (T + star T) x = 0 := by
  let A : H →L[ℂ] H := T + star T
  have hAstar : star A = A := by
    simp only [A, star_add, star_star, add_comm]
  have hAsym : (A : H →ₗ[ℂ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAstar
  have hApos : ∀ z : H, 0 ≤ RCLike.re ⟪A z, z⟫_ℂ := by
    intro z
    simpa only [A] using
      paperDirectRotation_hermitianPart_nonnegative U V T hT z
  have hAform : RCLike.re ⟪A x, x⟫_ℂ = 0 := by
    simp only [A, add_apply, inner_add_left, map_add,
      re_inner_star_apply, hx, add_zero]
  have hsq := ContinuousLinearMap.norm_apply_sq_le_of_positive
    hAsym hApos x
  rw [hAform, mul_zero] at hsq
  have hnormSq : ‖A x‖ ^ 2 = 0 :=
    le_antisymm hsq (sq_nonneg ‖A x‖)
  have hnorm : ‖A x‖ = 0 := sq_eq_zero_iff.mp hnormSq
  exact norm_eq_zero.mp hnorm

/-- A paper direct rotation maps the source crossed defect into the target
crossed defect.  This is the first missing membership obligation in the
production `crossedDefectEquivOfPaperDirectRotation` construction. -/
theorem paperDirectRotation_maps_sourceDefect
    (T : H →L[ℂ] H) (hT : IsPaperDirectRotation U V T)
    (x : halmosSourceDefect U V) :
    T (x : H) ∈ halmosTargetDefect U V := by
  rw [mem_halmosTargetDefect]
  have hPx : projection U (x : H) = x :=
    Submodule.starProjection_eq_self_iff.mpr x.property.1
  have hinter := DFunLike.congr_fun hT.intertwines (x : H)
  rw [mul_apply_eq_comp, mul_apply_eq_comp, hPx] at hinter
  have hTxV : T (x : H) ∈ V :=
    Submodule.starProjection_eq_self_iff.mp hinter.symm
  constructor
  · have hinner : ⟪T (x : H), (x : H)⟫_ℂ = 0 :=
      x.property.2 (T (x : H)) hTxV
    have hre : RCLike.re ⟪T (x : H), (x : H)⟫_ℂ = 0 := by
      rw [hinner, map_zero]
    have hsum := paperDirectRotation_add_star_apply_eq_zero U V T hT hre
    have hTneg : T (x : H) = -star T (x : H) := by
      apply eq_neg_of_add_eq_zero_left
      simpa only [add_apply] using hsum
    have hstar := congrArg star hT.intertwines
    have hrel : projection U * star T = star T * projection V := by
      simpa only [star_mul,
        (isSelfAdjoint_starProjection U).star_eq,
        (isSelfAdjoint_starProjection V).star_eq] using hstar
    have hVx : projection V (x : H) = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff V).mpr x.property.2
    have hPstarx : projection U (star T (x : H)) = 0 := by
      have h := DFunLike.congr_fun hrel (x : H)
      rw [mul_apply_eq_comp, mul_apply_eq_comp,
        hVx, map_zero] at h
      exact h
    have hPTx : projection U (T (x : H)) = 0 := by
      rw [hTneg, map_neg, hPstarx, neg_zero]
    exact (Submodule.starProjection_apply_eq_zero_iff U).mp hPTx
  · exact hTxV

/-- The adjoint of a paper direct rotation maps the target crossed defect back
into the source crossed defect.  This is the dual missing membership
obligation in the production construction. -/
theorem paperDirectRotation_adjoint_maps_targetDefect
    (T : H →L[ℂ] H) (hT : IsPaperDirectRotation U V T)
    (y : halmosTargetDefect U V) :
    star T (y : H) ∈ halmosSourceDefect U V := by
  rw [mem_halmosSourceDefect]
  have hstar := congrArg star hT.intertwines
  have hrel : projection U * star T = star T * projection V := by
    simpa only [star_mul,
      (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection V).star_eq] using hstar
  have hVy : projection V (y : H) = y :=
    Submodule.starProjection_eq_self_iff.mpr y.property.2
  have hstarTyU : star T (y : H) ∈ U := by
    have h := DFunLike.congr_fun hrel (y : H)
    rw [mul_apply_eq_comp, mul_apply_eq_comp, hVy] at h
    exact Submodule.starProjection_eq_self_iff.mp h
  constructor
  · exact hstarTyU
  · have hinner : ⟪star T (y : H), (y : H)⟫_ℂ = 0 :=
      y.property.1 (star T (y : H)) hstarTyU
    have hstarRe : RCLike.re ⟪star T (y : H), (y : H)⟫_ℂ = 0 := by
      rw [hinner, map_zero]
    have hre : RCLike.re ⟪T (y : H), (y : H)⟫_ℂ = 0 := by
      rw [← re_inner_star_apply T (y : H)]
      exact hstarRe
    have hsum := paperDirectRotation_add_star_apply_eq_zero U V T hT hre
    have hstarTneg : star T (y : H) = -T (y : H) := by
      apply eq_neg_of_add_eq_zero_right
      simpa only [add_apply] using hsum
    have hUy : projection U (y : H) = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff U).mpr y.property.1
    have hVTy : projection V (T (y : H)) = 0 := by
      have h := DFunLike.congr_fun hT.intertwines (y : H)
      rw [mul_apply_eq_comp, mul_apply_eq_comp,
        hUy, map_zero] at h
      exact h.symm
    have hVstarTy : projection V (star T (y : H)) = 0 := by
      rw [hstarTneg, map_neg, hVTy, neg_zero]
    exact (Submodule.starProjection_apply_eq_zero_iff V).mp hVstarTy

/-- The crossed-defect equivalence recovered from a paper direct rotation,
with both hard membership obligations discharged in this scratch module. -/
noncomputable def crossedDefectEquivOfPaperDirectRotationScratch
    (T : H →L[ℂ] H) (hT : IsPaperDirectRotation U V T) :
    halmosSourceDefect U V ≃ₗᵢ[ℂ] halmosTargetDefect U V where
  toFun x := ⟨T x, paperDirectRotation_maps_sourceDefect U V T hT x⟩
  invFun y := ⟨star T y,
    paperDirectRotation_adjoint_maps_targetDefect U V T hT y⟩
  left_inv x := by
    apply Subtype.ext
    have h := DFunLike.congr_fun hT.unitary_mem.1 (x : H)
    simpa only [mul_apply_eq_comp,
      one_apply_eq_self] using h
  right_inv y := by
    apply Subtype.ext
    have h := DFunLike.congr_fun hT.unitary_mem.2 (y : H)
    simpa only [mul_apply_eq_comp,
      one_apply_eq_self] using h
  map_add' x y := by
    apply Subtype.ext
    exact map_add T (x : H) (y : H)
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul T c (x : H)
  norm_map' x := by
    exact Unitary.norm_map ⟨T, hT.unitary_mem⟩ x

/-- Necessity half of Davis--Kahan Proposition 3.2. -/
theorem crossedDefectsEquivalent_of_paperDirectRotationScratch
    {T : H →L[ℂ] H} (hT : IsPaperDirectRotation U V T) :
    CrossedDefectsEquivalent U V :=
  ⟨crossedDefectEquivOfPaperDirectRotationScratch U V T hT⟩

/-- Complete scratch version of Davis--Kahan Proposition 3.2.  The forward
implication is the hard defect-transport theorem proved above; the reverse
implication uses the explicit polar-plus-quarter-turn construction already
present in the math-ahead layer. -/
theorem proposition3_2_nonacute_exists_iff_crossedDefectsEquivalent_scratch :
    (∃ T : H →L[ℂ] H, IsPaperDirectRotation U V T) ↔
      CrossedDefectsEquivalent U V := by
  constructor
  · rintro ⟨T, hT⟩
    exact crossedDefectsEquivalent_of_paperDirectRotationScratch U V hT
  · exact exists_paperDirectRotation_of_crossedDefectsEquivalent U V

end Section3
end Scratch
end Experimental
end DavisKahan
end TauCeti