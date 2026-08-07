/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.InfiniteDimensional.SinTheta.BoundedBorelProjectionComplex
import DavisKahan.InfiniteDimensional.SinTheta.Continuation.SelectedReduction

/-!
# Sharp form bounds on the spectral subspaces of an operator with a gap

If a bounded self-adjoint `B` has no spectrum in the open interval
`(alpha, alpha + delta)`, then its canonical spectral subspace for `Iic alpha`
carries the *sharp* form bound `re <B x, x> <= alpha ||x||^2`, and the
orthogonal complement carries `(alpha + delta) ||x||^2 <= re <B x, x>`.

Sharpness is the whole point.  The band estimate already in the Borel-calculus
layer (`norm_comp_boundedPVM_proj_sub_smul_le`) loses a factor of two, which is
fatal here: Davis--Kahan Section 8 feeds these two bounds straight into the
ordered-gap hypotheses of the quarter-angle theorem, and a lossy bound would
not close the gap at all.

The proof is the continuous functional calculus, made available by the gap
itself.  On the spectrum the indicator of `Iic alpha` *is* continuous, because
the gap makes `{t <= alpha}` relatively clopen there; concretely the affine
cutoff `spectralGapCutoff` agrees with the indicator on the spectrum.  So the
spectral projection is `cfcHom` of a continuous symbol, and each form bound is
the statement that a nonnegative continuous symbol has a nonnegative
functional-calculus image -- `(alpha - t) * chi(t)` for the low block and
`(t - alpha - delta) * (1 - chi(t))` for the high block.  Both are nonnegative
*on the spectrum* precisely because the open gap is empty.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace
open DavisKahan
open DavisKahan.Experimental
open DavisKahan.Experimental.Foundation

noncomputable section

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ### The cutoff symbol -/

/-- The affine cutoff that is `1` on `Iic alpha`, `0` on `Ici (alpha+delta)`,
and interpolates linearly in between. -/
def spectralGapCutoff (alpha delta t : ℝ) : ℝ :=
  max 0 (min 1 ((alpha + delta - t) / delta))

theorem continuous_spectralGapCutoff (alpha delta : ℝ) :
    Continuous (spectralGapCutoff alpha delta) := by
  unfold spectralGapCutoff
  fun_prop

theorem spectralGapCutoff_eq_one {alpha delta t : ℝ} (hdelta : 0 < delta)
    (ht : t ≤ alpha) : spectralGapCutoff alpha delta t = 1 := by
  have h1 : (1 : ℝ) ≤ (alpha + delta - t) / delta := by
    rw [le_div_iff₀ hdelta]
    linarith
  unfold spectralGapCutoff
  rw [min_eq_left h1, max_eq_right zero_le_one]

theorem spectralGapCutoff_eq_zero {alpha delta t : ℝ} (hdelta : 0 < delta)
    (ht : alpha + delta ≤ t) : spectralGapCutoff alpha delta t = 0 := by
  have h1 : (alpha + delta - t) / delta ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hdelta.le
  unfold spectralGapCutoff
  rw [max_eq_left (le_trans (min_le_right _ _) h1)]

/-! ### The symbol on the spectrum -/

variable (B : H →L[ℂ] H) (hB : IsSelfAdjointOperator B)

/-- The cutoff pulled back to the spectrum along the real-part coordinate. -/
def spectralGapSymbol (alpha delta : ℝ) : C(spectrum ℂ B, ℝ) :=
  ⟨fun w => spectralGapCutoff alpha delta (TauCeti.BorelCalculus.reCoord w),
    (continuous_spectralGapCutoff alpha delta).comp
      (Complex.continuous_re.comp continuous_subtype_val)⟩

@[simp] theorem spectralGapSymbol_apply (alpha delta : ℝ) (w : spectrum ℂ B) :
    spectralGapSymbol B alpha delta w =
      spectralGapCutoff alpha delta (TauCeti.BorelCalculus.reCoord w) := rfl

/-- The real-part coordinate of a spectral point is a point of the real
spectrum. -/
theorem reCoord_mem_realSpectrum (hB : IsSelfAdjointOperator B)
    (w : spectrum ℂ B) :
    TauCeti.BorelCalculus.reCoord w ∈ realSpectrum B := by
  have h := coe_reCoord B hB w
  change ((TauCeti.BorelCalculus.reCoord w : ℝ) : ℂ) ∈ spectrum ℂ B
  rw [h]
  exact w.2

/-- **With a gap, the spectral projection is a continuous functional
calculus.**  The affine cutoff agrees with the indicator of `Iic alpha` at
every point of the spectrum, so it computes the same projection. -/
theorem boundedSelfAdjointSpectralProjection_Iic_eq_cfcHom
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hgap : realSpectrum B ⊆ Set.Iic alpha ∪ Set.Ici (alpha + delta)) :
    boundedSelfAdjointSpectralProjection B hB (Set.Iic alpha) measurableSet_Iic =
      cfcHom ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB).isStarNormal
        (TauCeti.BorelCalculus.ofRealLM (spectralGapSymbol B alpha delta)) := by
  have h := boundedSelfAdjointSpectralProjection_eq_cfcL_of_agrees B hB
    (Set.Iic alpha) measurableSet_Iic
    (TauCeti.BorelCalculus.ofRealLM (spectralGapSymbol B alpha delta)) ?_
  · rw [h]
    rfl
  · intro w
    have hmem := hgap (reCoord_mem_realSpectrum B hB w)
    by_cases hw : w ∈ TauCeti.BorelCalculus.reCoord (T := B) ⁻¹' Set.Iic alpha
    · have hle : TauCeti.BorelCalculus.reCoord w ≤ alpha := hw
      rw [Set.indicator_of_mem hw]
      simp only [TauCeti.BorelCalculus.ofRealLM_apply, spectralGapSymbol_apply,
        spectralGapCutoff_eq_one hdelta hle]
      norm_num
    · have hgt : alpha < TauCeti.BorelCalculus.reCoord w := lt_of_not_ge hw
      have hhigh : alpha + delta ≤ TauCeti.BorelCalculus.reCoord w := by
        rcases hmem with hlow | hhigh
        · exact absurd (Set.mem_Iic.mp hlow) (not_le_of_gt hgt)
        · exact Set.mem_Ici.mp hhigh
      rw [Set.indicator_of_notMem hw]
      simp only [TauCeti.BorelCalculus.ofRealLM_apply, spectralGapSymbol_apply,
        spectralGapCutoff_eq_zero hdelta hhigh]
      norm_num

/-! ### The two sharp form bounds -/

/-- **Sharp upper form bound on the low spectral subspace.** -/
theorem re_inner_le_of_mem_boundedSelfAdjointSpectralSubspace_Iic
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hgap : realSpectrum B ⊆ Set.Iic alpha ∪ Set.Ici (alpha + delta))
    {x : H}
    (hx : x ∈ boundedSelfAdjointSpectralSubspace B hB (Set.Iic alpha)
      measurableSet_Iic) :
    RCLike.re ⟪B x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2 := by
  have hBsa : IsSelfAdjoint B :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB
  set E : H →L[ℂ] H :=
    boundedSelfAdjointSpectralProjection B hB (Set.Iic alpha) measurableSet_Iic
    with hEdef
  have hEx : E x = x := by
    rw [hEdef, boundedSelfAdjointSpectralProjection_eq_starProjection]
    exact Submodule.starProjection_eq_self_iff.mpr hx
  -- the nonnegative symbol
  set g : C(spectrum ℂ B, ℝ) :=
    ⟨fun w => (alpha - TauCeti.BorelCalculus.reCoord w) *
        spectralGapCutoff alpha delta (TauCeti.BorelCalculus.reCoord w),
      ((continuous_const.sub
        (Complex.continuous_re.comp continuous_subtype_val)).mul
        ((continuous_spectralGapCutoff alpha delta).comp
          (Complex.continuous_re.comp continuous_subtype_val)))⟩ with hgdef
  have hgnonneg : ∀ w : spectrum ℂ B, 0 ≤ g w := by
    intro w
    have hmem := hgap (reCoord_mem_realSpectrum B hB w)
    show 0 ≤ (alpha - TauCeti.BorelCalculus.reCoord w) *
      spectralGapCutoff alpha delta (TauCeti.BorelCalculus.reCoord w)
    rcases hmem with hlow | hhigh
    · rw [spectralGapCutoff_eq_one hdelta (Set.mem_Iic.mp hlow), mul_one]
      linarith [Set.mem_Iic.mp hlow]
    · rw [spectralGapCutoff_eq_zero hdelta (Set.mem_Ici.mp hhigh), mul_zero]
  have hpos := TauCeti.BorelCalculus.inner_cfcHom_ofReal_nonneg
    (a := B) hBsa.isStarNormal hgnonneg x
  have hsymbol :
      TauCeti.BorelCalculus.ofRealLM g =
        ((alpha : ℝ) : ℂ) •
            TauCeti.BorelCalculus.ofRealLM (spectralGapSymbol B alpha delta) -
          ((ContinuousMap.id ℂ).restrict (spectrum ℂ B)) *
            TauCeti.BorelCalculus.ofRealLM (spectralGapSymbol B alpha delta) := by
    ext w
    have hre := coe_reCoord B hB w
    simp only [TauCeti.BorelCalculus.ofRealLM_apply, hgdef, ContinuousMap.coe_mk,
      ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
      ContinuousMap.restrict_apply, ContinuousMap.id_apply, smul_eq_mul,
      spectralGapSymbol_apply]
    rw [← hre]
    push_cast
    ring
  rw [hsymbol, map_sub, map_smul, map_mul, cfcHom_id,
    ← boundedSelfAdjointSpectralProjection_Iic_eq_cfcHom B hB hdelta hgap] at hpos
  change 0 ≤ RCLike.re ⟪x, (((alpha : ℝ) : ℂ) • E - B * E) x⟫_ℂ at hpos
  have happly : (((alpha : ℝ) : ℂ) • E - B * E) x =
      ((alpha : ℝ) : ℂ) • x - B x := by
    simp only [sub_apply, smul_apply, mul_apply_eq_comp,
      ContinuousLinearMap.comp_apply, hEx]
  rw [happly, inner_sub_right, map_sub, inner_smul_right] at hpos
  have hxx : RCLike.re (((alpha : ℝ) : ℂ) * ⟪x, x⟫_ℂ) = alpha * ‖x‖ ^ 2 := by
    have hre : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, hre]
    ring
  have hswap : RCLike.re ⟪x, B x⟫_ℂ = RCLike.re ⟪B x, x⟫_ℂ := inner_re_symm x (B x)
  rw [hxx, hswap] at hpos
  linarith

/-- **Sharp lower form bound on the complementary spectral subspace.** -/
theorem le_re_inner_of_mem_boundedSelfAdjointSpectralSubspace_Iic_orthogonal
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hgap : realSpectrum B ⊆ Set.Iic alpha ∪ Set.Ici (alpha + delta))
    {x : H}
    (hx : x ∈ (boundedSelfAdjointSpectralSubspace B hB (Set.Iic alpha)
      measurableSet_Iic)ᗮ) :
    (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_ℂ := by
  have hBsa : IsSelfAdjoint B :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB
  set E : H →L[ℂ] H :=
    boundedSelfAdjointSpectralProjection B hB (Set.Iic alpha) measurableSet_Iic
    with hEdef
  have hEx : E x = 0 := by
    rw [hEdef, boundedSelfAdjointSpectralProjection_eq_starProjection]
    exact (Submodule.starProjection_apply_eq_zero_iff _).mpr hx
  set g : C(spectrum ℂ B, ℝ) :=
    ⟨fun w => (TauCeti.BorelCalculus.reCoord w - (alpha + delta)) *
        (1 - spectralGapCutoff alpha delta (TauCeti.BorelCalculus.reCoord w)),
      (((Complex.continuous_re.comp continuous_subtype_val).sub
        continuous_const).mul
        (continuous_const.sub
          ((continuous_spectralGapCutoff alpha delta).comp
            (Complex.continuous_re.comp continuous_subtype_val))))⟩ with hgdef
  have hgnonneg : ∀ w : spectrum ℂ B, 0 ≤ g w := by
    intro w
    have hmem := hgap (reCoord_mem_realSpectrum B hB w)
    show 0 ≤ (TauCeti.BorelCalculus.reCoord w - (alpha + delta)) *
      (1 - spectralGapCutoff alpha delta (TauCeti.BorelCalculus.reCoord w))
    rcases hmem with hlow | hhigh
    · rw [spectralGapCutoff_eq_one hdelta (Set.mem_Iic.mp hlow), sub_self, mul_zero]
    · rw [spectralGapCutoff_eq_zero hdelta (Set.mem_Ici.mp hhigh), sub_zero, mul_one]
      linarith [Set.mem_Ici.mp hhigh]
  have hpos := TauCeti.BorelCalculus.inner_cfcHom_ofReal_nonneg
    (a := B) hBsa.isStarNormal hgnonneg x
  have hsymbol :
      TauCeti.BorelCalculus.ofRealLM g =
        (((ContinuousMap.id ℂ).restrict (spectrum ℂ B)) -
            (((alpha + delta : ℝ) : ℂ)) • 1) *
          (1 - TauCeti.BorelCalculus.ofRealLM
            (spectralGapSymbol B alpha delta)) := by
    ext w
    have hre := coe_reCoord B hB w
    simp only [TauCeti.BorelCalculus.ofRealLM_apply, hgdef, ContinuousMap.coe_mk,
      ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
      ContinuousMap.one_apply, ContinuousMap.restrict_apply,
      ContinuousMap.id_apply, smul_eq_mul, spectralGapSymbol_apply]
    rw [← hre]
    push_cast
    ring
  rw [hsymbol, map_mul, map_sub, map_sub, map_smul, map_one, cfcHom_id,
    ← boundedSelfAdjointSpectralProjection_Iic_eq_cfcHom B hB hdelta hgap] at hpos
  change 0 ≤ RCLike.re
    ⟪x, ((B - ((alpha + delta : ℝ) : ℂ) • 1) * (1 - E)) x⟫_ℂ at hpos
  have happly : ((B - ((alpha + delta : ℝ) : ℂ) • 1) * (1 - E)) x =
      B x - ((alpha + delta : ℝ) : ℂ) • x := by
    simp only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply, sub_apply,
      smul_apply, one_apply_eq_self, hEx, sub_zero]
  rw [happly, inner_sub_right, map_sub, inner_smul_right] at hpos
  have hxx : RCLike.re (((alpha + delta : ℝ) : ℂ) * ⟪x, x⟫_ℂ) =
      (alpha + delta) * ‖x‖ ^ 2 := by
    have hre : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, hre]
    ring
  have hswap : RCLike.re ⟪x, B x⟫_ℂ = RCLike.re ⟪B x, x⟫_ℂ := inner_re_symm x (B x)
  rw [hxx, hswap] at hpos
  linarith

end

end DavisKahanExt
end TauCeti
