/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.PairedPhase
public import ForTauCeti.Analysis.OperatorIdeal.OddModulusSplit
public import ForTauCeti.Analysis.OperatorIdeal.OffDiagonalTrace
public import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryCorrection
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# An explicit nuclear-optimal phase of completed direct rotation

Multiply completed direct rotation R by C+iS, where C and S are the
intrinsic cosine and sine. The resulting unitary still transports the
pair. Its displacement factors through the modulus split of the
self-adjoint imaginary part of R, which is odd under source reflection.
The exact native nuclear cost is the nuclear projection difference.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The common positive-angle phase C+iS is unitary on the entire
ambient Hilbert space, including fixed and right-angle directions. -/
theorem cosine_add_i_sine_mem_unitary_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] :
    Proposition35.section3CosAngleOperator K L + Complex.I • K.sinAngleOperator L ∈
      unitary (E →L[ℂ] E) := by
  let C := Proposition35.section3CosAngleOperator K L
  let S := K.sinAngleOperator L
  have hC := ((ContinuousLinearMap.nonneg_iff_isPositive).mp
    (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  have hS := (K.isPositive_sinAngleOperator L).isSelfAdjoint
  have hCS : Commute C S :=
    Proposition35.commute_sinAngleOperator_of_commute_section3CosAngleOperator K L C (Commute.refl C)
  have hpy : C * C + S * S = 1 :=
    Proposition35.section3CosAngleOperator_sq_add_sinAngleOperator_sq K L
  have hstar : star (C + Complex.I • S) = C - Complex.I • S := by
    rw [star_add, star_smul, hC.star_eq, hS.star_eq]
    simp [C, S, sub_eq_add_neg]
  have hprod : (Complex.I • S) * (Complex.I • S) = -(S * S) := by
    rw [smul_mul_smul_comm, Complex.I_mul_I, neg_one_smul]
  apply Unitary.mem_iff.mpr
  constructor <;> rw [hstar]
  · calc
      (C - Complex.I • S) * (C + Complex.I • S) = C * C + S * S := by
        simp only [sub_mul, mul_add]
        rw [hprod, mul_smul_comm, smul_mul_assoc, hCS.eq]
        module
      _ = 1 := hpy
  · calc
      (C + Complex.I • S) * (C - Complex.I • S) = C * C + S * S := by
        simp only [add_mul, mul_sub]
        rw [hprod, mul_smul_comm, smul_mul_assoc, hCS.eq]
        module
      _ = 1 := hpy

/-- The common nuclear phase fixes exactly the vectors on which the
projections agree. Unitarity converts a fixed-vector equation to its
adjoint equation; their difference forces the sine to vanish. -/
theorem cosine_add_i_sine_apply_eq_self_iff_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (x : E) :
    (Proposition35.section3CosAngleOperator K L + Complex.I • K.sinAngleOperator L) x = x ↔
      K.starProjection x = L.starProjection x := by
  let C := Proposition35.section3CosAngleOperator K L
  let S := K.sinAngleOperator L
  let F := C + Complex.I • S
  have hC := ((ContinuousLinearMap.nonneg_iff_isPositive).mp
    (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  have hS := (K.isPositive_sinAngleOperator L).isSelfAdjoint
  constructor
  · intro hx
    have hinv := congrArg (fun T : E →L[ℂ] E => T x)
      (Unitary.star_mul_self_of_mem (cosine_add_i_sine_mem_unitary_complex K L))
    change star F (F x) = x at hinv
    rw [hx] at hinv
    have hstar : star F = C - Complex.I • S := by
      change star (C + Complex.I • S) = C - Complex.I • S
      rw [star_add, star_smul, hC.star_eq, hS.star_eq]
      simp [C, S, sub_eq_add_neg]
    rw [hstar] at hinv
    change C x - Complex.I • S x = x at hinv
    change C x + Complex.I • S x = x at hx
    have hzero : (2 : ℂ) • (Complex.I • S x) = 0 := by
      calc
        _ = (C x + Complex.I • S x) - (C x - Complex.I • S x) := by module
        _ = 0 := by rw [hx, hinv, sub_self]
    have hSx : S x = 0 := by
      exact (smul_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left (by norm_num))).resolve_left
        Complex.I_ne_zero
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    rw [← K.norm_sinAngleOperator_apply L x, hSx, norm_zero]
  · intro hx
    have hSx : K.sinAngleOperator L x = 0 := by
      apply norm_eq_zero.mp
      rw [K.norm_sinAngleOperator_apply L x, hx, sub_self, norm_zero]
    have hCx := Proposition35.cosine_apply_of_sinAngleOperator_eigenvector K L 0
      ⟨le_rfl, by linarith [Real.pi_pos]⟩ x
      (by simpa only [Real.sin_zero, RCLike.ofReal_zero, zero_smul] using hSx)
    simp only [Real.cos_zero, RCLike.ofReal_one, one_smul] at hCx
    change C x + Complex.I • S x = x
    rw [hCx, hSx, smul_zero, add_zero]

/-- The actual imaginary part of completed rotation is self-adjoint,
has modulus equal to the intrinsic projection sine, and is reversed by
source reflection. No compactness or acuteness hypothesis is needed. -/
theorem nonacuteDirectRotation_imaginary_properties_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    let A := (-Complex.I) •
      (nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L)
    IsSelfAdjoint A ∧ A.modulus = K.sinAngleOperator L ∧
      K.reflection.conjStarAlgEquiv A = -A := by
  dsimp only
  let R := nonacuteDirectRotation K L D
  let C := Proposition35.section3CosAngleOperator K L
  let S := K.sinAngleOperator L
  let B := R - C
  let A := (-Complex.I) • B
  have hB : star B = -B := Proposition35.star_nonacuteDirectRotation_sub_cosine K L D
  have hA : IsSelfAdjoint A := by
    change star ((-Complex.I) • B) = (-Complex.I) • B
    rw [star_smul, show star (-Complex.I) = Complex.I by simp, hB, smul_neg, neg_smul]
  have hAA : A * A = -(B * B) := by
    dsimp only [A]
    rw [smul_mul_smul_comm]
    simp
  have hSS : S * S = -(B * B) := by
    have hc := Proposition35.section3CosAngleOperator_sq_add_sinAngleOperator_sq K L
    have hb := nonacuteDirectRotation_cosine_sq_sub_skew_sq K L D
    change C * C + S * S = 1 at hc
    change C * C - B * B = 1 at hb
    calc
      S * S = 1 - C * C := eq_sub_of_add_eq' hc
      _ = -(B * B) := by rw [← hb]; abel
  have hmod : A.modulus = S := by
    symm
    apply ContinuousLinearMap.eq_modulus_iff.mpr
    refine ⟨K.isPositive_sinAngleOperator L, ?_⟩
    change S * S = star A * A
    rw [hA.star_eq, hAA, hSS]
  have hoddB : K.reflection.conjStarAlgEquiv B = -B := by
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply]
    apply ContinuousLinearMap.ext
    intro x
    change K.reflection (B (K.reflection.symm x)) = -(B x)
    have h : B (K.reflection (K.reflection.symm x)) =
        -K.reflection (B (K.reflection.symm x)) :=
      nonacuteDirectRotation_skew_reflection K L D (K.reflection.symm x)
    rw [K.reflection.apply_symm_apply] at h
    simpa only [neg_neg] using (congrArg Neg.neg h).symm
  refine ⟨hA, hmod, ?_⟩
  change K.reflection.conjStarAlgEquiv ((-Complex.I) • B) = -((-Complex.I) • B)
  rw [map_smul, hoddB, smul_neg]

/-- The self-adjoint imaginary part of completed rotation interchanges
the source subspace and its orthogonal complement. Source-reflection
oddness gives the exact block equation without spectral assumptions. -/
theorem nonacuteDirectRotation_imaginary_mul_starProjection_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    let A := (-Complex.I) •
      (nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L)
    A * K.starProjection = (1 - K.starProjection) * A := by
  let A := (-Complex.I) •
    (nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L)
  have hodd := (nonacuteDirectRotation_imaginary_properties_complex K L D).2.2
  have hanti (x : E) : A (K.reflection x) = -K.reflection (A x) := by
    have h := congrArg (fun T : E →L[ℂ] E => T (K.reflection x)) hodd
    change K.reflection (A (K.reflection.symm (K.reflection x))) = -A (K.reflection x) at h
    rw [K.reflection.symm_apply_apply] at h
    simpa only [neg_neg] using congrArg Neg.neg h.symm
  apply ContinuousLinearMap.ext
  intro x
  change A (K.starProjection x) = A x - K.starProjection (A x)
  apply smul_right_injective E (by norm_num : (2 : ℂ) ≠ 0)
  change (2 : ℂ) • A (K.starProjection x) = (2 : ℂ) • (A x - K.starProjection (A x))
  rw [two_smul, two_smul]
  calc
    _ = A (K.reflection x) + A x := by
      rw [Submodule.reflection_apply, map_sub, map_nsmul]
      module
    _ = -K.reflection (A x) + A x := by rw [hanti]
    _ = _ := by rw [Submodule.reflection_apply]; module

/-- For an actual crossed-defect identification, the native Schatten
power of the ambient projection difference is twice the directed sine
power, for every finite real exponent at least one. Infinite values and
arbitrary Hilbert dimension are included. -/
theorem gauge_schatten_projection_sub_rpow_eq_twice_sine_complex
    (p : ℝ) (hp : 1 ≤ p)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    (OperatorIdealFamily.schatten ℂ p hp).gauge (K.starProjection - L.starProjection) ^ p =
      2 * (OperatorIdealFamily.schatten ℂ p hp).gauge (K.sinThetaMap L) ^ p := by
  let Φ := OperatorIdealFamily.schatten ℂ p hp
  let A := (-Complex.I) •
    (nonacuteDirectRotation K L D - Proposition35.section3CosAngleOperator K L)
  obtain ⟨hA, hmod, _⟩ := nonacuteDirectRotation_imaginary_properties_complex K L D
  have h := ContinuousLinearMap.gauge_schatten_rpow_eq_twice_of_selfAdjoint_offDiagonal
    p hp A K.starProjection hA (isStarProjection_starProjection (U := K))
    (nonacuteDirectRotation_imaginary_mul_starProjection_complex K L D)
  have hmodgauge (T : E →L[ℂ] E) : Φ.gauge T.modulus = Φ.gauge T := by
    simp only [Φ, OperatorIdealFamily.gauge_schatten, ContinuousLinearMap.singularValue_modulus]
  have hcostA : Φ.gauge A = Φ.gauge (K.starProjection - L.starProjection) := by
    rw [← hmodgauge A, hmod, Submodule.sinAngleOperator_def, hmodgauge]
  have hσ : (A * K.starProjection).singularValue = (K.sinThetaMap L).singularValue := by
    funext j
    apply ContinuousLinearMap.singularValue_eq_of_forall_norm_apply_eq
    intro x
    calc
      ‖(A * K.starProjection) x‖ = ‖A.modulus (K.starProjection x)‖ :=
        (A.norm_modulus_apply _).symm
      _ = ‖(K.sinAngleOperator L * K.starProjection) x‖ := by rw [hmod]; rfl
      _ = ‖(K.sinThetaMap L).modulus x‖ := by rw [K.sinAngleOperator_mul_starProjection L]
      _ = ‖K.sinThetaMap L x‖ := (K.sinThetaMap L).norm_modulus_apply x
  have hcostAP : Φ.gauge (A * K.starProjection) = Φ.gauge (K.sinThetaMap L) := by
    simp only [Φ, OperatorIdealFamily.gauge_schatten, hσ]
  change Φ.gauge A ^ p = 2 * Φ.gauge (A * K.starProjection) ^ p at h
  rwa [hcostA, hcostAP] at h

/-- The explicit common-branch complex phase of completed direct rotation. -/
@[expose]
def nuclearPhaseRotation_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) : E ≃ₗᵢ[ℂ] E :=
  Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D *
        (Proposition35.section3CosAngleOperator K L + Complex.I • K.sinAngleOperator L),
      mul_mem (nonacuteDirectRotation_mem_unitary K L D)
        (cosine_add_i_sine_mem_unitary_complex K L)⟩ : unitary (E →L[ℂ] E))

/-- The explicit nuclear phase transports the actual pair on the full
ambient Hilbert space. -/
theorem nuclearPhaseRotation_map_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    K.map (nuclearPhaseRotation_complex K L D).toLinearMap = L := by
  let C := Proposition35.section3CosAngleOperator K L
  let S := K.sinAngleOperator L
  let V := Unitary.linearIsometryEquiv
    (⟨C + Complex.I • S, cosine_add_i_sine_mem_unitary_complex K L⟩ : unitary (E →L[ℂ] E))
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ :
      unitary (E →L[ℂ] E))
  have hCP : Commute C K.starProjection :=
    Proposition35.section3CosAngleOperator_comm_projection K L
  have hSP : Commute S K.starProjection := (K.commute_starProjection_sinAngleOperator L).symm
  have hVmap : K.map V.toLinearMap = K :=
    (K.map_eq_self_iff_commute_starProjection V).mpr (hCP.add_left (hSP.smul_left Complex.I))
  have hRmap : K.map R.toLinearMap = L :=
    (K.map_eq_iff_intertwines_reflection L R).mpr (nonacuteDirectRotation_reflection_intertwines K L D)
  change K.map (R.toLinearMap.comp V.toLinearMap) = L
  rw [Submodule.map_comp, hVmap, hRmap]

/-- The correction from completed direct rotation to its common nuclear
phase has exactly the rank of the projection difference, as a cardinal.
Thus this explicit endpoint correction is finite rank exactly for
finite-rank projection pairs; it cannot have the strict-exponent finite
active cutoff on genuinely infinite-rank pairs. -/
theorem rank_nuclearPhaseRotation_sub_directRotation_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    ((nuclearPhaseRotation_complex K L D : E →L[ℂ] E) -
      nonacuteDirectRotation K L D).rank = (K.starProjection - L.starProjection).rank := by
  let A := ((nuclearPhaseRotation_complex K L D : E →L[ℂ] E) -
    nonacuteDirectRotation K L D).toLinearMap
  let B := (K.starProjection - L.starProjection).toLinearMap
  let R := Unitary.linearIsometryEquiv
    (⟨nonacuteDirectRotation K L D, nonacuteDirectRotation_mem_unitary K L D⟩ :
      unitary (E →L[ℂ] E))
  have hker : A.ker = B.ker := by
    ext x
    change (nuclearPhaseRotation_complex K L D) x - R x = 0 ↔
      K.starProjection x - L.starProjection x = 0
    rw [sub_eq_zero, sub_eq_zero]
    change R ((Proposition35.section3CosAngleOperator K L +
      Complex.I • K.sinAngleOperator L) x) = R x ↔ _
    rw [R.injective.eq_iff]
    exact cosine_add_i_sine_apply_eq_self_iff_complex K L x
  calc
    A.rank = Module.rank ℂ (E ⧸ A.ker) := A.quotKerEquivRange.rank_eq.symm
    _ = Module.rank ℂ (E ⧸ B.ker) := by rw [hker]
    _ = B.rank := B.quotKerEquivRange.rank_eq

/-- The displacement of the explicit nuclear phase is a unitary factor
times the equal-cost modulus split of the rotation's imaginary part. -/
theorem nuclearPhaseRotation_displacement_factor_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    let R := nonacuteDirectRotation K L D
    let C := Proposition35.section3CosAngleOperator K L
    let A := (-Complex.I) • (R - C)
    1 - (nuclearPhaseRotation_complex K L D : E →L[ℂ] E) =
      (-Complex.I) • (R * (A + K.sinAngleOperator L)) := by
  dsimp only
  let R := nonacuteDirectRotation K L D
  let C := Proposition35.section3CosAngleOperator K L
  let S := K.sinAngleOperator L
  let A := (-Complex.I) • (R - C)
  have hstarC : star R - C = -(R - C) := by
    have h := nonacuteDirectRotation_add_star_eq_two_cosine K L D
    change R + star R = C + C at h
    rw [show star R = C + C - R from eq_sub_of_add_eq' h]
    abel
  have hminus : (-Complex.I) • A = -(R - C) := by simp [A, smul_smul]
  have hfactor : star R - (C + Complex.I • S) = (-Complex.I) • (A + S) := by
    rw [smul_add, hminus, neg_smul, ← hstarC]
    abel
  change 1 - R * (C + Complex.I • S) = (-Complex.I) • (R * (A + S))
  calc
    _ = R * (star R - (C + Complex.I • S)) := by
      rw [mul_sub, Unitary.mul_star_self_of_mem (nonacuteDirectRotation_mem_unitary K L D)]
    _ = _ := by rw [hfactor, mul_smul_comm]

/-- **Exact unrestricted nuclear phase cost.** The literal native
nuclear displacement equals the nuclear projection difference, with
infinite values included. No compactness, summability or acuteness is assumed. -/
theorem gauge_nuclear_nuclearPhaseRotation_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
        (1 - (nuclearPhaseRotation_complex K L D : E →L[ℂ] E)) =
      (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
        (K.starProjection - L.starProjection) := by
  let Φ := OperatorIdealFamily.schatten ℂ 1 (by norm_num)
  let R := nonacuteDirectRotation K L D
  let S := K.sinAngleOperator L
  let A := (-Complex.I) • (R - Proposition35.section3CosAngleOperator K L)
  obtain ⟨hA, hmod, hodd⟩ := nonacuteDirectRotation_imaginary_properties_complex K L D
  have hsplit := ContinuousLinearMap.gauge_nuclear_modulus_add_of_unitary_odd
    A hA K.reflection hodd
  rw [hmod] at hsplit
  have hmodgauge (T : E →L[ℂ] E) : Φ.gauge T.modulus = Φ.gauge T := by
    simp only [Φ, OperatorIdealFamily.gauge_schatten, ContinuousLinearMap.singularValue_modulus]
  have hunitary : R ∈ unitary (E →L[ℂ] E) := nonacuteDirectRotation_mem_unitary K L D
  let R' := Unitary.linearIsometryEquiv (⟨R, hunitary⟩ : unitary (E →L[ℂ] E))
  calc
    Φ.gauge (1 - (nuclearPhaseRotation_complex K L D : E →L[ℂ] E)) =
        Φ.gauge (R * (A + S)) := by
      rw [nuclearPhaseRotation_displacement_factor_complex, Φ.gauge_smul, ← ofReal_norm]
      simp only [norm_neg, Complex.norm_I, ENNReal.ofReal_one, one_mul]
      rfl
    _ = Φ.gauge (A + S) := Φ.gauge_comp_linearIsometryEquiv_left _ R'
    _ = Φ.gauge A := by rw [add_comm A S]; exact hsplit
    _ = Φ.gauge S := (hmodgauge A).symm.trans (congrArg Φ.gauge hmod)
    _ = _ := by
      change Φ.gauge (K.sinAngleOperator L) = Φ.gauge (K.starProjection - L.starProjection)
      rw [Submodule.sinAngleOperator_def]
      exact hmodgauge _

/-- The explicit nuclear phase minimizes over every ambient unitary
transporter, including competitors of infinite native nuclear cost. -/
theorem nuclearPhaseRotation_isMin_complex
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (U : E ≃ₗᵢ[ℂ] E) (hmap : K.map U.toLinearMap = L) :
    (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge
        (1 - (nuclearPhaseRotation_complex K L D : E →L[ℂ] E)) ≤
      (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge (1 - (U : E →L[ℂ] E)) := by
  rw [gauge_nuclear_nuclearPhaseRotation_complex]
  exact (OperatorIdealFamily.schatten ℂ 1 (by norm_num)).gauge_projection_sub_le_unitary_displacement
    K L U hmap

end TauCeti.DavisKahan
