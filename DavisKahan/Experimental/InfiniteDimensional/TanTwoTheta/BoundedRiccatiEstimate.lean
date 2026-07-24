/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Riccati.BoundedCore

/-!
# The near-singular-pair estimate for bounded tangent-two-theta

This leaf isolates the dimension-free analytic step in the sharp bounded
Riccati estimate.  A near norm-attaining right/left singular pair for a
contractive Riccati solution produces the factor `1 - s * t`; after sending
`s` to `t = ||X||` and the adjoint defect to zero this becomes
`1 - ||X||^2`.

The theorem is deliberately stated with shifted diagonal form bounds
`A0 <= 0` and `A1 >= d`.  A common real scalar shift leaves the Riccati
equation unchanged, so ordered spectral separation can be converted to this
normalization in a separate bridge leaf.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- A finite-error sharp Riccati estimate evaluated on a normalized
near-singular pair.  The error is exactly the defect in the adjoint singular
relation `X* y = t x`.

In the exact singular-pair case (`eta = 0`, `s = t`) the conclusion is

`d * t <= ||B01|| * (1 - t^2)`.
-/
theorem riccati_near_singular_pair_bound
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d t s eta : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hs0 : 0 ≤ s) (hst : s ≤ t)
    (hA0 : ∀ z : E0, RCLike.re ⟪H.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪H.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati H X)
    {x : E0} {y : E1}
    (hxnorm : ‖x‖ = 1) (hynorm : ‖y‖ = 1)
    (hXx : X x = (s : ℂ) • y)
    (hadj : ‖X.adjoint y - (t : ℂ) • x‖ ≤ eta) :
    d * s ≤ ‖H.B01‖ * (1 - s * t) +
      (‖H.A0‖ + s * ‖H.B01‖) * eta := by
  set e : E0 := X.adjoint y - (t : ℂ) • x with he
  have he_norm : ‖e‖ ≤ eta := by simpa [he] using hadj
  have hst1 : s * t < 1 := by
    have htt : t * t < 1 := by nlinarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hst ht0) htt
  have hA1lower : d * s ≤ s * RCLike.re ⟪H.A1 y, y⟫_ℂ := by
    have hy := hA1 y
    rw [hynorm, one_pow, mul_one] at hy
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hy hs0
  have hA0cross : RCLike.re ⟪H.A0 x, X.adjoint y⟫_ℂ ≤ ‖H.A0‖ * eta := by
    have hadj_expand : X.adjoint y = (t : ℂ) • x + e := by
      rw [he]
      abel
    rw [hadj_expand, inner_add_right, map_add]
    have hmain : RCLike.re ⟪H.A0 x, (t : ℂ) • x⟫_ℂ ≤ 0 := by
      rw [inner_smul_right, ← Complex.real_smul, RCLike.smul_re]
      exact mul_nonpos_of_nonneg_of_nonpos ht0 (hA0 x)
    have herr : RCLike.re ⟪H.A0 x, e⟫_ℂ ≤ ‖H.A0‖ * eta := by
      calc
        RCLike.re ⟪H.A0 x, e⟫_ℂ ≤ ‖⟪H.A0 x, e⟫_ℂ‖ := RCLike.re_le_norm _
        _ ≤ ‖H.A0 x‖ * ‖e‖ := norm_inner_le_norm _ _
        _ ≤ (‖H.A0‖ * ‖x‖) * ‖e‖ := by
          exact mul_le_mul_of_nonneg_right (H.A0.le_opNorm x) (norm_nonneg e)
        _ ≤ (‖H.A0‖ * ‖x‖) * eta := by
          exact mul_le_mul_of_nonneg_left he_norm
            (mul_nonneg (norm_nonneg H.A0) (norm_nonneg x))
        _ = ‖H.A0‖ * eta := by rw [hxnorm, mul_one]
    linarith
  have hleft_lower :
      d * s - ‖H.A0‖ * eta ≤
        RCLike.re ⟪H.A1 (X x) - X (H.A0 x), y⟫_ℂ := by
    have hA1exact :
        RCLike.re ⟪H.A1 (X x), y⟫_ℂ =
          s * RCLike.re ⟪H.A1 y, y⟫_ℂ := by
      rw [hXx, map_smul, inner_smul_left, Complex.conj_ofReal,
        ← Complex.real_smul, RCLike.smul_re]
    have hA0exact :
        RCLike.re ⟪X (H.A0 x), y⟫_ℂ =
          RCLike.re ⟪H.A0 x, X.adjoint y⟫_ℂ := by
      rw [ContinuousLinearMap.adjoint_inner_right]
    rw [inner_sub_left, map_sub, hA1exact, hA0exact]
    linarith
  have hpoint := (solvesRiccati_iff_pointwise H X).1 hX x
  have heq : H.A1 (X x) - X (H.A0 x) =
      X (H.B01 (X x)) - H.B10 x := by
    rw [map_add] at hpoint
    calc
      H.A1 (X x) - X (H.A0 x) =
          (H.B10 x + H.A1 (X x)) - (H.B10 x + X (H.A0 x)) := by abel
      _ = (X (H.A0 x) + X (H.B01 (X x))) -
          (H.B10 x + X (H.A0 x)) := by rw [hpoint]
      _ = X (H.B01 (X x)) - H.B10 x := by abel
  have hB10real :
      RCLike.re ⟪H.B10 x, y⟫_ℂ =
        RCLike.re ⟪H.B01 y, x⟫_ℂ := by
    rw [← RCLike.conj_re ⟪H.B10 x, y⟫_ℂ, inner_conj_symm,
      ← H.offDiagonalAdjoint x y]
  have hBexact :
      RCLike.re ⟪X (H.B01 (X x)) - H.B10 x, y⟫_ℂ =
        (s * t - 1) * RCLike.re ⟪H.B01 y, x⟫_ℂ +
          s * RCLike.re ⟪H.B01 y, e⟫_ℂ := by
    have hadj_expand : X.adjoint y = (t : ℂ) • x + e := by
      rw [he]
      abel
    have hXterm :
        RCLike.re ⟪X (H.B01 (X x)), y⟫_ℂ =
          s * (t * RCLike.re ⟪H.B01 y, x⟫_ℂ +
            RCLike.re ⟪H.B01 y, e⟫_ℂ) := by
      calc
        RCLike.re ⟪X (H.B01 (X x)), y⟫_ℂ =
            RCLike.re ⟪H.B01 (X x), X.adjoint y⟫_ℂ := by
              rw [ContinuousLinearMap.adjoint_inner_right]
        _ = s * RCLike.re ⟪H.B01 y, X.adjoint y⟫_ℂ := by
              rw [hXx, map_smul, inner_smul_left, Complex.conj_ofReal,
                ← Complex.real_smul, RCLike.smul_re]
        _ = s * (t * RCLike.re ⟪H.B01 y, x⟫_ℂ +
              RCLike.re ⟪H.B01 y, e⟫_ℂ) := by
              rw [hadj_expand, inner_add_right, map_add, inner_smul_right,
                ← Complex.real_smul, RCLike.smul_re]
    rw [inner_sub_left, map_sub, hXterm, hB10real]
    ring
  have hq : |RCLike.re ⟪H.B01 y, x⟫_ℂ| ≤ ‖H.B01‖ := by
    calc
      |RCLike.re ⟪H.B01 y, x⟫_ℂ| ≤ ‖⟪H.B01 y, x⟫_ℂ‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖H.B01 y‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ (‖H.B01‖ * ‖y‖) * ‖x‖ := by
        gcongr
        exact H.B01.le_opNorm y
      _ = ‖H.B01‖ := by rw [hynorm, hxnorm, mul_one, mul_one]
  have herrB : |RCLike.re ⟪H.B01 y, e⟫_ℂ| ≤ ‖H.B01‖ * eta := by
    calc
      |RCLike.re ⟪H.B01 y, e⟫_ℂ| ≤ ‖⟪H.B01 y, e⟫_ℂ‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖H.B01 y‖ * ‖e‖ := norm_inner_le_norm _ _
      _ ≤ (‖H.B01‖ * ‖y‖) * ‖e‖ := by
        exact mul_le_mul_of_nonneg_right (H.B01.le_opNorm y) (norm_nonneg e)
      _ ≤ (‖H.B01‖ * ‖y‖) * eta := by
        exact mul_le_mul_of_nonneg_left he_norm
          (mul_nonneg (norm_nonneg H.B01) (norm_nonneg y))
      _ = ‖H.B01‖ * eta := by rw [hynorm, mul_one]
  have hright_upper :
      RCLike.re ⟪X (H.B01 (X x)) - H.B10 x, y⟫_ℂ ≤
        ‖H.B01‖ * (1 - s * t) + s * ‖H.B01‖ * eta := by
    rw [hBexact]
    have hcoef : s * t - 1 ≤ 0 := by linarith
    have hfirst :
        (s * t - 1) * RCLike.re ⟪H.B01 y, x⟫_ℂ ≤
          ‖H.B01‖ * (1 - s * t) := by
      calc
        (s * t - 1) * RCLike.re ⟪H.B01 y, x⟫_ℂ
            ≤ |(s * t - 1) * RCLike.re ⟪H.B01 y, x⟫_ℂ| :=
              le_abs_self _
        _ = |s * t - 1| * |RCLike.re ⟪H.B01 y, x⟫_ℂ| := by
              rw [abs_mul]
        _ ≤ (1 - s * t) * ‖H.B01‖ := by
              rw [abs_of_nonpos hcoef, neg_sub]
              exact mul_le_mul_of_nonneg_left hq (by linarith)
        _ = ‖H.B01‖ * (1 - s * t) := mul_comm _ _
    have hsecond :
        s * RCLike.re ⟪H.B01 y, e⟫_ℂ ≤ s * ‖H.B01‖ * eta := by
      calc
        s * RCLike.re ⟪H.B01 y, e⟫_ℂ
            ≤ s * |RCLike.re ⟪H.B01 y, e⟫_ℂ| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) hs0
        _ ≤ s * (‖H.B01‖ * eta) :=
              mul_le_mul_of_nonneg_left herrB hs0
        _ = s * ‖H.B01‖ * eta := by ring
    linarith
  rw [heq] at hleft_lower
  have hmain : d * s - ‖H.A0‖ * eta ≤
      ‖H.B01‖ * (1 - s * t) + s * ‖H.B01‖ * eta :=
    hleft_lower.trans hright_upper
  nlinarith

end DavisKahanExt
end TauCeti