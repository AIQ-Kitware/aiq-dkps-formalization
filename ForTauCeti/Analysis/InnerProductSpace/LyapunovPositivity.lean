/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.PVM
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.InnerProductSpace.Coercive
public import TauCeti.Analysis.InnerProductSpace.Positive.Basic

/-!
# A Lyapunov positivity criterion

If `X` is self-adjoint, `G` is positive and injective, and the anticommutator
`X G + G X` is positive, then `X` is positive.

The invertible case is classical and immediate: conjugating by `G^(-1/2)` turns
the hypothesis into accretivity of an operator similar to `X`, and a self-adjoint
operator whose spectrum lies in the closed right half-plane is positive.  That
proof needs `G` bounded below, which is exactly what fails in the application.

The point of this module is that injectivity is enough.  The invertibility is
recovered from the *other* operator: on the spectral subspace where `X ≤ -β`, the
operator `-X` is bounded below by `β`, and running the classical argument there
forces the spectrum of the compression of `G` to lie in `{0}`. The
compression therefore vanishes, which injectivity forbids.
-/

public section

namespace TauCeti
namespace ContinuousLinearMap

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A positive invertible operator and a positive operator can have a
nonpositive anticommutator only if the latter operator is zero. -/
theorem eq_zero_of_anticommutator_nonpos {A K : H →L[ℂ] H}
    (hA : (0 : H →L[ℂ] H) ≤ A) (hAunit : IsUnit A) (hK : (0 : H →L[ℂ] H) ≤ K)
    (h : A * K + K * A ≤ 0) : K = 0 := by
  let B : H →L[ℂ] H := (1 / 2 : ℝ) • -(A * K + K * A)
  have hBnonneg : 0 ≤ B := smul_nonneg (by norm_num) (neg_nonneg.mpr h)
  have hB : B.LowerFormBoundOn ⊤ 0 := by
    rw [_root_.ContinuousLinearMap.lowerFormBoundOn_iff]
    intro v _
    rw [zero_mul]
    exact (_root_.ContinuousLinearMap.nonneg_iff_isPositive.mp hBnonneg).re_inner_nonneg_left v
  have hlyap : A * (-K) + star (-K) * A = B + B := by
    rw [star_neg, hK.isSelfAdjoint.star_eq, mul_neg, neg_mul, ← neg_add]
    dsimp only [B]
    rw [← add_smul]
    norm_num
  apply CFC.eq_zero_of_spectrum_subset_zero (R := ℝ) K _ hK.isSelfAdjoint
  intro r hr
  have hrC : (r : ℂ) ∈ spectrum ℂ K := by
    rw [← hK.isSelfAdjoint.spectrumRestricts.algebraMap_image]
    exact ⟨r, hr, rfl⟩
  have hneg : -(r : ℂ) ∈ spectrum ℂ (-K) := by
    simpa only [← spectrum.neg_eq, Set.mem_neg, neg_neg] using hrC
  have hre := _root_.ContinuousLinearMap.le_re_of_mem_spectrum_of_positive_lyapunov
    B A (-K) (hAunit.isStrictlyPositive hA) hlyap le_rfl hB hneg
  have hrle : r ≤ 0 := by
    simpa only [zero_div, Complex.neg_re, Complex.ofReal_re, neg_nonneg] using hre
  exact le_antisymm hrle (spectrum_nonneg_of_nonneg hK hr)

/-- **The Lyapunov positivity criterion.**

`X` self-adjoint, `G` positive and injective, and `X G + G X` positive together
force `X` positive.

Injectivity of `G` cannot be dropped: `X = diag(1, -1)` and `G = diag(1, 0)` have
`X G + G X = diag(2, 0) ≥ 0` with `X` indefinite.  But `G` is *not* assumed
bounded below, which is the whole point -- in the Davis--Kahan application `G` is
the inverse of an unbounded operator, so its spectrum reaches `0`.

The invertibility the classical argument wants is taken from `X` instead of from
`G`.  On the spectral subspace where `X ≤ -β` the operator `1 - P - X P` is
bounded below by `β/2`, and the compression of `G` there is annihilated by
`eq_zero_of_anticommutator_nonpos`; injectivity then forces that spectral
subspace to be trivial, for every `β > 0`. -/
theorem nonneg_of_lyapunov_nonneg {X G : H →L[ℂ] H}
    (hX : IsSelfAdjoint X) (hG : (0 : H →L[ℂ] H) ≤ G) (hGinj : Function.Injective G)
    (h : (0 : H →L[ℂ] H) ≤ X * G + G * X) : (0 : H →L[ℂ] H) ≤ X := by
  classical
  -- it is enough to bound the form below by `-β` for every small `β > 0`
  have hmain : ∀ β : ℝ, 0 < β → β ≤ 1 → ∀ x : H,
      -β * ‖x‖ ^ 2 ≤ RCLike.re ⟪X x, x⟫_ℂ := by
    intro β hβ hβ1 x
    let spectralMeasure :=
      (X.toLinearMap.toPMap ⊤).spectralPVM (LinearPMap.isSelfAdjoint_toPMap_top hX)
    set P : H →L[ℂ] H :=
      spectralMeasure.proj (Set.Iic (-β)) measurableSet_Iic with hPdef
    have hPsa : IsSelfAdjoint P :=
      spectralMeasure.isSelfAdjoint_proj _ _
    have hPidem : P * P = P :=
      spectralMeasure.proj_idem _ _
    have hPcomm : X * P = P * X :=
      TauCeti.BorelCalculus.boundedPVM_proj_comm hX (Set.Iic (-β)) measurableSet_Iic
    have hPbound (v : H) :
        RCLike.re ⟪X (P v), P v⟫_ℂ ≤ (-β / 2) * ‖P v‖ ^ 2 := by
      let Xpartial := X.toLinearMap.toPMap ⊤
      let p : Xpartial.domain := ⟨P v, by simp [Xpartial]⟩
      have hp : (p : H) ∈ P.range := LinearMap.mem_range_self P.toLinearMap v
      have hbound := (LinearPMap.isSelfAdjoint_toPMap_top hX)
        |>.re_inner_le_mul_norm_sq_of_mem_range_spectralPVM_proj
          measurableSet_Iic (α := -β / 2) (fun t ht => by
            have ht' : t ≤ -β := ht
            change t ≤ -β / 2
            linarith) (x := p) hp
      exact hbound
    -- pointwise consequences of `P` being a self-adjoint idempotent commuting with `X`
    have hadjP : ∀ y z : H, ⟪P y, z⟫_ℂ = ⟪y, P z⟫_ℂ :=
      hPsa.isSymmetric
    have hXP : X * P = P * (X * P) := by
      calc X * P = X * (P * P) := by rw [hPidem]
        _ = (X * P) * P := by noncomm_ring
        _ = (P * X) * P := by rw [hPcomm]
        _ = P * (X * P) := by noncomm_ring
    have hPXP : ∀ y : H, P (X (P y)) = X (P y) := by
      intro y
      have := congrArg (fun T : H →L[ℂ] H => T y) hXP.symm
      simpa using this
    -- the positive invertible operator
    set A : H →L[ℂ] H := 1 - P - X * P with hAdef
    have hAsa : IsSelfAdjoint A := by
      rw [hAdef]
      refine (IsSelfAdjoint.sub (IsSelfAdjoint.sub (IsSelfAdjoint.one _) hPsa) ?_)
      rw [_root_.IsSelfAdjoint, star_mul, hPsa.star_eq, hX.star_eq, ← hPcomm]
    have hAcoer : ∀ v : H, (β / 2) * ‖v‖ ^ 2 ≤ RCLike.re ⟪A v, v⟫_ℂ := by
      intro v
      have hPv : ⟪P v, v⟫_ℂ = ⟪P v, P v⟫_ℂ :=
        (hadjP v v).trans (spectralMeasure.inner_proj_eq_inner_proj_proj _ _ v v)
      have hXPv : ⟪(X * P) v, v⟫_ℂ = ⟪X (P v), P v⟫_ℂ := by
        change ⟪X (P v), v⟫_ℂ = _
        rw [← hPXP v, hadjP (X (P v)) v, hPXP v]
      have hself : RCLike.re ⟪P v, P v⟫_ℂ = ‖P v‖ ^ 2 :=
        inner_self_eq_norm_sq (𝕜 := ℂ) (P v)
      have hvv : RCLike.re ⟪v, v⟫_ℂ = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
      have hnorm : ‖P v‖ ≤ ‖v‖ := spectralMeasure.norm_proj_apply_le _ _ v
      have hb := hPbound v
      have hA : RCLike.re ⟪A v, v⟫_ℂ
          = ‖v‖ ^ 2 - ‖P v‖ ^ 2 - RCLike.re ⟪X (P v), P v⟫_ℂ := by
        rw [hAdef]
        simp only [sub_apply, inner_sub_left, map_sub]
        rw [show ((1 : H →L[ℂ] H)) v = v from rfl, hXPv, hPv, hself, hvv]
      have hnormsq : ‖P v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
        nlinarith [hnorm, norm_nonneg (P v), norm_nonneg v]
      rw [hA]
      nlinarith [hb, hnormsq, hβ, hβ1]
    have hAunit : IsUnit A :=
      _root_.ContinuousLinearMap.isUnit_of_coercive A (by positivity : 0 < β / 2) hAcoer
    have hAnonneg : (0 : H →L[ℂ] H) ≤ A := by
      rw [_root_.ContinuousLinearMap.nonneg_iff_isPositive]
      refine ⟨_root_.ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAsa, fun v => ?_⟩
      rw [_root_.ContinuousLinearMap.reApplyInnerSelf_apply]
      nlinarith [hAcoer v, norm_nonneg v, hβ]
    -- the compression of `G`
    set K : H →L[ℂ] H := P * G * P with hKdef
    have hKform : ∀ v : H, ⟪K v, v⟫_ℂ = ⟪G (P v), P v⟫_ℂ := by
      intro v
      change ⟪P (G (P v)), v⟫_ℂ = _
      rw [hadjP (G (P v)) v]
    have hKnonneg : 0 ≤ K := by
      simpa only [hKdef, hPsa.star_eq] using star_right_conjugate_nonneg hG P
    have hXK : X * K + K * X = P * (X * G + G * X) * P := by
      dsimp only [K]
      calc
        _ = (X * P) * G * P + P * G * (P * X) := by noncomm_ring
        _ = (P * X) * G * P + P * G * (X * P) :=
          congrArg₂ (· + ·) (congrArg (fun T => T * G * P) hPcomm)
            (congrArg (fun T => P * G * T) hPcomm.symm)
        _ = _ := by noncomm_ring
    have hAK : A * K + K * A = -(X * K + K * X) := by
      have hPK : P * K = K := by
        rw [hKdef]
        calc P * (P * G * P) = (P * P) * G * P := by noncomm_ring
          _ = P * G * P := by rw [hPidem]
      have hKP : K * P = K := by
        rw [hKdef]
        calc (P * G * P) * P = P * G * (P * P) := by noncomm_ring
          _ = P * G * P := by rw [hPidem]
      rw [hAdef]
      calc (1 - P - X * P) * K + K * (1 - P - X * P)
          = (K - P * K - X * (P * K)) + (K - K * P - (K * X) * P) := by noncomm_ring
        _ = -(X * K + K * X) := by
            rw [hPK, hKP]
            have hKXP : (K * X) * P = K * X := by
              calc (K * X) * P = K * (X * P) := by noncomm_ring
                _ = K * (P * X) := by rw [hPcomm]
                _ = (K * P) * X := by noncomm_ring
                _ = K * X := by rw [hKP]
            rw [hKXP]
            abel
    have hAKnonpos : A * K + K * A ≤ 0 := by
      rw [hAK, hXK]
      exact neg_nonpos.mpr (by
        simpa only [hPsa.star_eq] using star_right_conjugate_nonneg h P)
    have hK0 : K = 0 :=
      eq_zero_of_anticommutator_nonpos hAnonneg hAunit hKnonneg hAKnonpos
    -- injectivity kills the spectral subspace
    have hP0 : P x = 0 := by
      have hzero : ⟪G (P x), P x⟫_ℂ = 0 := by
        rw [← hKform, hK0]
        simp
      have hGpos := _root_.ContinuousLinearMap.nonneg_iff_isPositive.mp hG
      have hGP : G (P x) = 0 :=
        hGpos.toLinearMap.apply_eq_zero_of_inner_map_self_eq_zero hzero
      exact hGinj (hGP.trans (map_zero G).symm)
    have hfin := TauCeti.BorelCalculus.le_re_inner_of_boundedPVM_proj_Iic_eq_zero hX (-β)
      (show spectralMeasure.proj (Set.Iic (-β)) measurableSet_Iic x = 0
        from hP0)
    simpa [RCLike.re_to_complex] using hfin
  -- pass to the limit
  rw [_root_.ContinuousLinearMap.nonneg_iff_isPositive]
  refine ⟨_root_.ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hX, fun x => ?_⟩
  rw [_root_.ContinuousLinearMap.reApplyInnerSelf_apply]
  by_contra hc
  push Not at hc
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hc
  have hn : 0 < ‖x‖ ^ 2 := by positivity
  set r : ℝ := RCLike.re ⟪X x, x⟫_ℂ with hr
  set β : ℝ := min 1 (-r / (2 * ‖x‖ ^ 2)) with hβdef
  have hrneg : r < 0 := hc
  have hβpos : 0 < β := lt_min one_pos (div_pos (by linarith) (by positivity))
  have hβ1 : β ≤ 1 := min_le_left _ _
  have hβle : β ≤ -r / (2 * ‖x‖ ^ 2) := min_le_right _ _
  have hkey := hmain β hβpos hβ1 x
  have : -β * ‖x‖ ^ 2 ≥ r / 2 := by
    have hmul : β * ‖x‖ ^ 2 ≤ (-r / (2 * ‖x‖ ^ 2)) * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hβle (by positivity)
    have hsimp : (-r / (2 * ‖x‖ ^ 2)) * ‖x‖ ^ 2 = -r / 2 := by
      field_simp
    rw [hsimp] at hmul
    linarith
  linarith

end ContinuousLinearMap
end TauCeti
