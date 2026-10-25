/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.Geometry.Polar.NonacuteCompression
public import DavisKahan.Geometry.Angle.CosineKernel
public import ForTauCeti.Analysis.InnerProductSpace.Projection.PairedPhase
public import ForTauCeti.Analysis.InnerProductSpace.AnticommutingInvolution

/-!
# The canonical rotation on reflection-paired phase eigenvectors

If a transporter has paired phases `alpha,-beta` with nonnegative acute
mean `theta`, every completed canonical rotation has phases `theta,-theta`
on those same vectors. The arbitrary right-angle completion is immaterial
on these positive-cosine vectors. No finite dimension is required.

The proof is classical polar geometry: the canonical intertwiner acts by
`cos(theta)*exp(i*theta)`, while its modulus acts by `cos(theta)>0`.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

/-- Every completed canonical rotation fixes every vector on which the
source and target projections agree. This is independent of the chosen
defect completion and holds over either scalar field in any Hilbert space. -/
theorem nonacuteDirectRotation_apply_eq_self_of_projections_eq
    {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace F]
    (K L : Submodule 𝕜 F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (x : F) (hx : K.starProjection x = L.starProjection x) :
    nonacuteDirectRotation K L D x = x := by
  have hS : K.sinAngleOperator L x = 0 := by
    apply norm_eq_zero.mp
    rw [K.norm_sinAngleOperator_apply L x, hx, sub_self, norm_zero]
  have hC := Proposition35.cosine_apply_of_sinAngleOperator_eigenvector K L 0
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ x
    (by simpa only [Real.sin_zero, RCLike.ofReal_zero, zero_smul] using hS)
  simp only [Real.cos_zero, RCLike.ofReal_one, one_smul] at hC
  have hQP : L.starProjection (K.starProjection x) = K.starProjection x := by
    rw [hx]
    exact Submodule.starProjection_eq_self_iff.mpr (L.starProjection_apply_mem x)
  have hA : spectraCanonicalIntertwiner K L x = x := by
    change L.starProjection (K.starProjection x) + Lᗮ.starProjection (Kᗮ.starProjection x) = x
    rw [Submodule.starProjection_orthogonal, Submodule.starProjection_orthogonal]
    change L.starProjection (K.starProjection x) +
      ((x - K.starProjection x) - L.starProjection (x - K.starProjection x)) = x
    rw [map_sub, hQP, ← hx]
    module
  have h := congrArg (fun A : F →L[𝕜] F => A x)
    (nonacuteDirectRotation_mul_cosine_eq_canonicalIntertwiner K L D)
  change nonacuteDirectRotation K L D (Proposition35.section3CosAngleOperator K L x) = _ at h
  rwa [hC, hA] at h

/-- Every completed canonical rotation preserves the intrinsic sine
angle operator, including its zero and right-angle sectors. -/
theorem nonacuteDirectRotation_comm_sinAngleOperator
    {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace F]
    (K L : Submodule 𝕜 F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    Commute (nonacuteDirectRotation K L D) (K.sinAngleOperator L) := by
  apply Proposition35.commute_sinAngleOperator_of_commute_section3CosAngleOperator
  rw [Proposition35.section3CosAngleOperator_eq_canonicalAbsoluteValue]
  exact nonacuteDirectRotation_comm_absoluteValue K L D

private theorem one_add_exp_twice (t : ℝ) :
    1 + Complex.exp (((2 * t : ℝ) : ℂ) * Complex.I) =
      (2 : ℂ) * (Real.cos t : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
  have hzero : Complex.exp (-(t : ℂ) * Complex.I) *
      Complex.exp ((t : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero]
  have hdouble : Complex.exp ((t : ℂ) * Complex.I) *
      Complex.exp ((t : ℂ) * Complex.I) =
        Complex.exp (((2 * t : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = Complex.exp (-(t : ℂ) * Complex.I) * Complex.exp ((t : ℂ) * Complex.I) +
        Complex.exp ((t : ℂ) * Complex.I) * Complex.exp ((t : ℂ) * Complex.I) := by
      rw [hzero, hdouble]
    _ = (Complex.exp ((t : ℂ) * Complex.I) + Complex.exp (-(t : ℂ) * Complex.I)) *
        Complex.exp ((t : ℂ) * Complex.I) := by ring
    _ = _ := by rw [← Complex.two_cos, ← Complex.ofReal_cos]

private theorem star_exp_phase (t : ℝ) :
    star (Complex.exp ((t : ℂ) * Complex.I)) =
      Complex.exp (((-t : ℝ) : ℂ) * Complex.I) := by
  change (starRingEnd ℂ) (Complex.exp ((t : ℂ) * Complex.I)) = _
  rw [← Complex.exp_conj]
  congr 1
  simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The canonical rotation has exactly the mean paired phases on any
reflection-paired transporter eigenvectors of nonnegative acute mean. This
holds for every defect completion on an arbitrary complex Hilbert space. -/
theorem nonacuteDirectRotation_apply_of_paired_phase_eigenvectors
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (T : E ≃ₗᵢ[ℂ] E) (hT : K.map T.toLinearMap = L)
    (v : E) (alpha beta : ℝ)
    (hTv : T v = Complex.exp ((alpha : ℂ) * Complex.I) • v)
    (hTJv : T (K.reflection v) =
      Complex.exp (((-beta : ℝ) : ℂ) * Complex.I) • K.reflection v)
    (hmean : (alpha + beta) / 2 ∈ Set.Ico 0 (Real.pi / 2)) :
    let theta := (alpha + beta) / 2
    nonacuteDirectRotation K L D v = Complex.exp ((theta : ℂ) * Complex.I) • v ∧
      nonacuteDirectRotation K L D (K.reflection v) =
        Complex.exp (((-theta : ℝ) : ℂ) * Complex.I) • K.reflection v := by
  let theta := (alpha + beta) / 2
  let R := nonacuteDirectRotation K L D
  let C := Proposition35.section3CosAngleOperator K L
  let A := spectraCanonicalIntertwiner K L
  have hS := Submodule.sinAngleOperator_apply_of_paired_phase_eigenvectors_complex
    K L T hT v alpha beta hTv hTJv ⟨hmean.1, hmean.2.le⟩
  have hCv : C v = (Real.cos theta : ℂ) • v :=
    Proposition35.cosine_apply_of_sinAngleOperator_eigenvector K L theta
      ⟨hmean.1, hmean.2.le⟩ v hS.1
  have hstar := unitary_star_apply_of_apply_eq_smul
    (Unitary.linearIsometryEquiv.symm T) _ (Complex.norm_exp_ofReal_mul_I (-beta))
    (K.reflection v) hTJv
  rw [Unitary.coe_symm_linearIsometryEquiv_apply, star_exp_phase, neg_neg] at hstar
  have hinv : T.symm (K.reflection v) =
      Complex.exp ((beta : ℂ) * Complex.I) • K.reflection v := by
    change (T.symm : E →L[ℂ] E) (K.reflection v) = _
    rw [← T.adjoint_eq_symm]
    exact hstar
  have hreflection : L.reflection (K.reflection v) =
      Complex.exp (((alpha + beta : ℝ) : ℂ) * Complex.I) • v := by
    have h := (K.map_eq_iff_intertwines_reflection L T).mp hT
      (T.symm (K.reflection v))
    rw [T.apply_symm_apply] at h
    rw [← h, hinv, map_smul, K.reflection_reflection, map_smul, hTv, smul_smul]
    congr 1
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hA2 := congrArg (fun B : E →L[ℂ] E => B v)
    (spectraCanonicalIntertwiner_add_self K L)
  change A v + A v = v + L.reflectionOperator (K.reflectionOperator v) at hA2
  rw [Submodule.reflectionOperator_apply_eq_reflection,
    Submodule.reflectionOperator_apply_eq_reflection, hreflection] at hA2
  have hsum : alpha + beta = 2 * theta := by dsimp [theta]; ring
  rw [hsum] at hA2
  have hright : v + Complex.exp (((2 * theta : ℝ) : ℂ) * Complex.I) • v =
      ((2 : ℂ) * (Real.cos theta : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)) • v := by
    calc
      _ = (1 + Complex.exp (((2 * theta : ℝ) : ℂ) * Complex.I)) • v := by
        rw [add_smul, one_smul]
      _ = _ := congrArg (fun z : ℂ => z • v) (one_add_exp_twice theta)
  have hAv : A v = ((Real.cos theta : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)) • v := by
    apply smul_right_injective E (by norm_num : (2 : ℂ) ≠ 0)
    change (2 : ℂ) • A v = (2 : ℂ) •
      (((Real.cos theta : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)) • v)
    calc
      _ = A v + A v := two_smul ℂ (A v)
      _ = _ := hA2.trans hright
      _ = _ := by rw [smul_smul]; congr 1; ring
  have hRC := congrArg (fun B : E →L[ℂ] E => B v)
    (nonacuteDirectRotation_mul_cosine_eq_canonicalIntertwiner K L D)
  change R (C v) = A v at hRC
  rw [hCv, map_smul, hAv] at hRC
  have hcos : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hmean.1, Real.pi_pos], hmean.2⟩
  have hRv : R v = Complex.exp ((theta : ℂ) * Complex.I) • v := by
    apply smul_right_injective E (Complex.ofReal_ne_zero.mpr hcos.ne')
    change (Real.cos theta : ℂ) • R v =
      (Real.cos theta : ℂ) • (Complex.exp ((theta : ℂ) * Complex.I) • v)
    simpa only [smul_smul] using hRC
  have hRstar := unitary_star_apply_of_apply_eq_smul
    (⟨R, nonacuteDirectRotation_mem_unitary K L D⟩ : unitary (E →L[ℂ] E))
    _ (Complex.norm_exp_ofReal_mul_I theta) v hRv
  change star R v = _ at hRstar
  rw [star_exp_phase] at hRstar
  refine ⟨hRv, ?_⟩
  rw [nonacuteDirectRotation_reflection_eq_reflection_star K L D, hRstar, map_smul]

end TauCeti.DavisKahan
