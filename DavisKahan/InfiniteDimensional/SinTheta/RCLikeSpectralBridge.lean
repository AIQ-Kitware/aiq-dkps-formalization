/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
module

public import DavisKahan.SinTheta.SpectralBridge
public import DavisKahan.InfiniteDimensional.SinTheta.Restriction
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import TauCeti.Analysis.InnerProductSpace.Adjoint

public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# `RCLike` spectral-bridge lemmas

The affine-shift estimates apply over any `RCLike` scalar field. For a
symmetric operator, a non-real shift and its adjoint are bounded below by
the absolute imaginary part of the parameter. TauCeti's invertibility
criterion then places the parameter in the resolvent set. The self-adjoint
spectral-radius bound uses the `RCLike` Rayleigh theorem.

A previously stated leaf `norm_le_of_normal_spectrum_norm_le` (normal-operator
norm/spectral-radius bound over `RCLike`) was **removed as false**: over `ℝ`
the rotation by `π/2` of the plane is star-normal with empty real spectrum, so
the claimed bound would force it to vanish.  Its only consumer needed the
self-adjoint case, which is `norm_le_of_selfAdjoint_spectrum_subset_closedBall`.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Recentering a Sylvester equation by a real scalar leaves the right-hand side
unchanged: `(A - c)X - X(B - c) = AX - XB`. -/
theorem centered_sylvester_equation
    (A : E →L[𝕜] E) (B : F →L[𝕜] F) (X C : F →L[𝕜] E) (c : ℝ)
    (hEq : A ∘L X - X ∘L B = C) :
    (A - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) ∘L X -
      X ∘L (B - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 F) = C := by
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id, ← hEq]
  abel

omit [CompleteSpace E] in
/-- A real scalar multiple of the identity is a symmetric operator. -/
theorem isSymmetric_real_smul_id (c : ℝ) :
    (((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E).IsSymmetric := fun x y => by
  simp [inner_smul_left, inner_smul_right, RCLike.conj_ofReal]

namespace RCLikeSpectralBridge

omit [CompleteSpace E] in
/-- The numerical range of a symmetric operator is real. -/
theorem im_inner_map_self_eq_zero
    {A : E →L[𝕜] E} (hA : A.IsSymmetric) (x : E) :
    RCLike.im ⟪A x, x⟫_𝕜 = 0 := by
  rw [← RCLike.conj_eq_iff_im, inner_conj_symm]
  exact (hA x x).symm

omit [CompleteSpace E] in
/-- A symmetric pencil at a spectral parameter with nonzero imaginary part is
bounded below by `|im z|`. -/
theorem abs_im_mul_norm_le_norm_sub_smul_apply
    {A : E →L[𝕜] E} (hA : A.IsSymmetric) (z : 𝕜) (x : E) :
    |RCLike.im z| * ‖x‖ ≤ ‖(A - z • ContinuousLinearMap.id 𝕜 E) x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hinner : ⟪(A - z • ContinuousLinearMap.id 𝕜 E) x, x⟫_𝕜 =
      ⟪A x, x⟫_𝕜 - (starRingEnd 𝕜) z * ((‖x‖ ^ 2 : ℝ) : 𝕜) := by
    simp only [sub_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_left, inner_smul_left]
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    ring
  have him : RCLike.im ⟪(A - z • ContinuousLinearMap.id 𝕜 E) x, x⟫_𝕜 =
      RCLike.im z * ‖x‖ ^ 2 := by
    rw [hinner, map_sub, im_inner_map_self_eq_zero hA, zero_sub, RCLike.mul_im]
    simp only [RCLike.ofReal_im, RCLike.ofReal_re, RCLike.conj_im,
      RCLike.conj_re, mul_zero, zero_add]
    ring
  have habs : |RCLike.im z| * ‖x‖ ^ 2 ≤
      ‖(A - z • ContinuousLinearMap.id 𝕜 E) x‖ * ‖x‖ := by
    calc |RCLike.im z| * ‖x‖ ^ 2
        = |RCLike.im z * ‖x‖ ^ 2| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖x‖ ^ 2)]
      _ = |RCLike.im ⟪(A - z • ContinuousLinearMap.id 𝕜 E) x, x⟫_𝕜| := by
          rw [him]
      _ ≤ ‖⟪(A - z • ContinuousLinearMap.id 𝕜 E) x, x⟫_𝕜‖ :=
          RCLike.abs_im_le_norm _
      _ ≤ ‖(A - z • ContinuousLinearMap.id 𝕜 E) x‖ * ‖x‖ :=
          norm_inner_le_norm _ _
  nlinarith [habs, hxpos, norm_nonneg ((A - z • ContinuousLinearMap.id 𝕜 E) x)]

/-- The star of the pencil is the pencil at the conjugate parameter. -/
theorem star_sub_smul
    {A : E →L[𝕜] E} (hA : A.IsSymmetric) (z : 𝕜) :
    star (A - z • ContinuousLinearMap.id 𝕜 E) =
      A - (starRingEnd 𝕜) z • ContinuousLinearMap.id 𝕜 E := by
  have hASA : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hid : star (ContinuousLinearMap.id 𝕜 E) = ContinuousLinearMap.id 𝕜 E := by
    show star (1 : E →L[𝕜] E) = (1 : E →L[𝕜] E)
    exact star_one _
  rw [star_sub, star_smul, hASA.star_eq, hid]
  rfl

/-- A symmetric pencil at a non-real parameter is invertible. -/
theorem isUnit_sub_smul_one_of_im_ne_zero
    {A : E →L[𝕜] E} (hA : A.IsSymmetric) {z : 𝕜}
    (hz : RCLike.im z ≠ 0) :
    IsUnit (A - z • ContinuousLinearMap.id 𝕜 E) := by
  let T := A - z • ContinuousLinearMap.id 𝕜 E
  have himpos : 0 < |RCLike.im z| := abs_pos.mpr hz
  have hTlow : ∀ x, ‖x‖ ≤ |RCLike.im z|⁻¹ * ‖T x‖ := fun x => by
    rw [le_inv_mul_iff₀ himpos]
    exact abs_im_mul_norm_le_norm_sub_smul_apply hA z x
  have hAdjLow : ∀ x, ‖x‖ ≤ |RCLike.im z|⁻¹ * ‖T.adjoint x‖ := fun x => by
    rw [le_inv_mul_iff₀ himpos, ← ContinuousLinearMap.star_eq_adjoint, show T = _ from rfl,
      star_sub_smul hA]
    have h := abs_im_mul_norm_le_norm_sub_smul_apply hA ((starRingEnd 𝕜) z) x
    rwa [RCLike.conj_im, abs_neg] at h
  exact (ContinuousLinearMap.isUnit_and_norm_ringInverse_le_of_forall_norm_le
    (inv_nonneg.mpr himpos.le) hTlow (ContinuousLinearMap.injective_of_forall_norm_le hAdjLow)).1

/-- For self-adjoint `A`, every point of `σ(A - c·1)` is real and comes from
`σ(A)`: non-real spectral parameters are excluded by
`isUnit_sub_smul_one_of_im_ne_zero`, and the affine spectral mapping is
`spectrum.sub_singleton_eq`.

This is the forward half; `mem_spectrum_sub_real_scalar_iff` below packages it
with the converse, which needs no self-adjointness. -/
theorem exists_mem_boundedRealSpectrum_of_mem_spectrum_sub_real_scalar
    {A : E →L[𝕜] E} (hA : A.IsSymmetric) {c : ℝ} {z : 𝕜}
    (hz : z ∈ spectrum 𝕜 (A - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E)) :
    ∃ r : ℝ, r ∈ boundedRealSpectrum A ∧ z = (((r - c : ℝ)) : 𝕜) := by
  have hpencil : A - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E =
      A - algebraMap 𝕜 (E →L[𝕜] E) ((c : ℝ) : 𝕜) := by
    congr 1
  rw [hpencil, ← spectrum.sub_singleton_eq] at hz
  obtain ⟨w, hw, v, hv, hzw⟩ := Set.mem_sub.mp hz
  rw [Set.mem_singleton_iff] at hv
  subst hv
  have him : RCLike.im w = 0 := by
    by_contra hne
    have hunit := isUnit_sub_smul_one_of_im_ne_zero hA hne
    have hnot : w ∉ spectrum 𝕜 A := by
      rw [spectrum.notMem_iff]
      have h := hunit.neg
      rw [neg_sub] at h
      have hpen2 : algebraMap 𝕜 (E →L[𝕜] E) w =
          w • ContinuousLinearMap.id 𝕜 E :=
        @Algebra.algebraMap_eq_smul_one 𝕜 (E →L[𝕜] E) _ _ _ w
      rw [hpen2]
      exact h
    exact hnot hw
  have hw_real : w = ((RCLike.re w : ℝ) : 𝕜) := by
    conv_lhs => rw [← RCLike.re_add_im w]
    rw [him]
    simp
  refine ⟨RCLike.re w, ?_, ?_⟩
  · rw [DavisKahanExt.boundedRealSpectrum_eq_realSpectrum]
    show ((RCLike.re w : ℝ) : 𝕜) ∈ spectrum 𝕜 A
    rw [← hw_real]
    exact hw
  · rw [← hzw, hw_real]
    push_cast
    ring

omit [CompleteSpace E] in
/-- The converse inclusion, which holds for **any** bounded operator: shifting a
real spectral point by `c` lands in the spectrum of the shifted pencil.

Self-adjointness is what makes the *forward* direction true — it is what forces
the spectrum of the pencil to be real — and it is not needed here.  Keeping the
two halves separate records that asymmetry instead of burying it in a hypothesis
the `iff` carries for only one of its directions. -/
theorem mem_spectrum_sub_real_scalar_of_mem_boundedRealSpectrum
    {A : E →L[𝕜] E} {c r : ℝ} (hr : r ∈ boundedRealSpectrum A) :
    (((r - c : ℝ)) : 𝕜) ∈
      spectrum 𝕜 (A - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) := by
  have hpencil : A - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E =
      A - algebraMap 𝕜 (E →L[𝕜] E) ((c : ℝ) : 𝕜) := by
    congr 1
  rw [hpencil, ← spectrum.sub_singleton_eq]
  refine Set.mem_sub.mpr ⟨((r : ℝ) : 𝕜), ?_, ((c : ℝ) : 𝕜), rfl, ?_⟩
  · rw [DavisKahanExt.boundedRealSpectrum_eq_realSpectrum] at hr
    exact hr
  · push_cast
    ring

/-- **The spectrum of the real pencil, as an actual `Iff`.**

`σ(A - c·1) = σ(A) - c`, in membership form.  The name previously sat on the
forward implication alone, which the naming rubric forbids: `_iff` asserts an
`Iff`.  The fix was to supply the converse rather than to weaken the name, since
the original docstring already claimed the equality. -/
theorem mem_spectrum_sub_real_scalar_iff
    {A : E →L[𝕜] E} (hA : A.IsSymmetric) {c : ℝ} {z : 𝕜} :
    z ∈ spectrum 𝕜 (A - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) ↔
      ∃ r : ℝ, r ∈ boundedRealSpectrum A ∧ z = (((r - c : ℝ)) : 𝕜) :=
  ⟨fun hz => exists_mem_boundedRealSpectrum_of_mem_spectrum_sub_real_scalar hA hz,
   fun ⟨_r, hr, hz⟩ => hz ▸ mem_spectrum_sub_real_scalar_of_mem_boundedRealSpectrum hr⟩

/-- A self-adjoint operator whose spectrum sits in the closed ball of radius `ρ`
has operator norm at most `ρ`.  Proof: its norm equals its spectral radius
(`RCLike` Rayleigh theorem), which is bounded by `ρ`. -/
theorem norm_le_of_selfAdjoint_spectrum_subset_closedBall
    {T : E →L[𝕜] E} (hSelf : T.IsSymmetric) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hspec : spectrum 𝕜 T ⊆ Metric.closedBall 0 ρ) : ‖T‖ ≤ ρ := by
  have hSA : IsSelfAdjoint T := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hSelf
  have hrad : spectralRadius 𝕜 T = ‖T‖₊ := ContinuousLinearMap.spectralRadius_eq_eNorm T hSA
  have hquasispec : quasispectrum 𝕜 T ⊆ Metric.closedBall 0 ρ := by
    intro z hz
    have hz' : z ∈ spectrum 𝕜 T ∪ {0} := by
      simpa only [quasispectrum_eq_spectrum_union_zero] using hz
    rcases hz' with hzspec | hzzero
    · exact hspec hzspec
    · have : z = 0 := by simpa using hzzero
      subst z
      simp [Metric.mem_closedBall, hρ]
  have hbound : spectralRadius 𝕜 T ≤ (ρ.toNNReal : ENNReal) := by
    refine iSup₂_le fun z hz => ?_
    have hzρ : ‖z‖ ≤ ρ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hquasispec hz
    have : ‖z‖₊ ≤ ρ.toNNReal := by
      rw [← NNReal.coe_le_coe, coe_nnNorm, Real.coe_toNNReal ρ hρ]; exact hzρ
    exact_mod_cast this
  rw [hrad] at hbound
  have hnn : ‖T‖₊ ≤ ρ.toNNReal := by exact_mod_cast hbound
  calc ‖T‖ = (‖T‖₊ : ℝ) := rfl
    _ ≤ (ρ.toNNReal : ℝ) := by exact_mod_cast hnn
    _ = ρ := Real.coe_toNNReal ρ hρ

end RCLikeSpectralBridge
end ExactSinTheta
end DavisKahan
end TauCeti
