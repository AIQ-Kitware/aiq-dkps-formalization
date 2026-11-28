/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import TauCeti.Analysis.InnerProductSpace.DoubleAngle.Vector
public import TauCeti.Analysis.InnerProductSpace.DoubleAngle.QuarterAcute
public import DavisKahan.Geometry.Polar.DirectRotation
public import DavisKahan.InfiniteDimensional.Riccati.BoundedSpectralTransport
public import DavisKahan.SinTheta.FrameFactorization
public import DavisKahan.SpectralTheory.OperatorAngle

public section

open scoped ComplexOrder

open TauCeti.DavisKahan.Angle


/-!
# Dimension-free quarter-angle branch for the off-diagonal tan 2Theta theorem

The strict bounded endpoint consumes the accepted Tau Ceti proof from #27804.
The original Kitware authors and Apache-2.0 notices are retained. The local
non-strict and pointwise strict consequences remain for the unbounded source
theorem; they consume the native reflection polynomial and norm bound.

This is the missing arbitrary-Hilbert-space branch argument.  It does not use
an eigenvector attaining the norm of `(P_U-P_V)^2`.

Put `J = 2P_U-1`, `K = 2P_V-1`, center the two operators at the midpoint of
the common gap, and set

`B = J (A-c)` and `C = K (A+H-c)`.

The ordered form hypotheses make `B` and `C` strictly positive by the same
half-gap.  Off-diagonality gives the exact Lyapunov identity

`C (KJ) + (KJ)^* C = 2 B`.

Conjugating `KJ` by `C^(1/2)` therefore gives a strictly accretive operator.
Similarity transports the spectrum, while `KJ` is normal (indeed unitary), so
the continuous functional calculus turns the strict spectral half-plane bound
into a strict lower bound on `KJ + (KJ)^*`.  Finally

`KJ + JK = 2 - 4(P_U-P_V)^2`

gives `||P_U-P_V||^2 < 1/2`, i.e. the quarter-acute branch.
-/

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace
open TauCeti.DavisKahanExt
open TauCeti.DavisKahan

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

private theorem re_conj_real_mul (r : ℝ) (z : ℂ) :
    RCLike.re ((starRingEnd ℂ) (r : ℂ) * z) = r * RCLike.re z := by
  rw [Complex.conj_ofReal]
  simp

omit [CompleteSpace E] in
private theorem re_conj_real_mul_inner_self (r : ℝ) (x : E) :
    RCLike.re ((starRingEnd ℂ) (r : ℂ) * ⟪x, x⟫_ℂ) = r * ‖x‖ ^ 2 := by
  rw [re_conj_real_mul, inner_self_eq_norm_sq]

/-- Dimension-free strict quarter-angle branch from the paper's ordered form
hypotheses and full off-diagonality. -/
theorem isQuarterAcute_of_orderedFormGap
    (A H : E →L[ℂ] E)
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A)
    (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUperpLow : ∀ x ∈ Uᗮ,
      RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hVhigh : ∀ x ∈ V,
      b * ‖x‖ ^ 2 ≤ RCLike.re ⟪(A + H) x, x⟫_ℂ)
    (hVperpLow : ∀ x ∈ Vᗮ,
      RCLike.re ⟪(A + H) x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ)
    (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U) :
    IsQuarterAcute U V := by
  exact Submodule.projectionGap_lt_sqrt_two_div_two_of_orderedFormGap U V A H hA hH
    hAU hAplusH_V hab
    ((ContinuousLinearMap.lowerFormBoundOn_iff A U b).mpr hUhigh)
    ((ContinuousLinearMap.upperFormBoundOn_iff A Uᗮ a).mpr hUperpLow)
    ((ContinuousLinearMap.lowerFormBoundOn_iff (A + H) V b).mpr hVhigh)
    ((ContinuousLinearMap.upperFormBoundOn_iff (A + H) Vᗮ a).mpr hVperpLow)
    hHU hHUperp

/-! ### The non-strict quarter angle, and why it is stated separately

`isQuarterAcute_of_orderedFormGap` concludes `subspaceGap U V < √2/2`, strictly.
That is stronger than Davis and Kahan's printed `Θ ≤ π/4`, and the strictness is
paid for with the constant `α = δ / (1 + ‖C‖)`, which degenerates as `‖A‖ → ∞`.

The printed conclusion needs only the *non-strict* bound, and that follows from
the reflection product being positive with no constant at all.  Everything below
is the last third of the bounded proof with `α = 0`, extracted so that an
unbounded argument can reach the source conclusion without reproducing the part
that does not survive. -/

/-- **`Θ ≤ π/4` from a positive reflection product.**

Davis--Kahan's printed Section 8 conclusion, in projector form: if the real part
of `K J` is nonnegative -- equivalently `K J + J K ≥ 0` -- then
`‖P_U − P_V‖ ≤ √2/2`.

No constant appears anywhere, which is exactly why this survives to unbounded
scope where `isQuarterAcute_of_orderedFormGap`'s strict bound does not. -/
theorem subspaceGap_le_of_reflectionProduct_form_nonneg
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : ∀ x : E, 0 ≤ RCLike.re ⟪((V.reflection : E →L[ℂ] E) * (U.reflection : E →L[ℂ] E)
      + (U.reflection : E →L[ℂ] E) * (V.reflection : E →L[ℂ] E)) x, x⟫_ℂ) :
    U.projectionGap V ≤ Real.sqrt 2 / 2 := by
  obtain ⟨D, hDdef⟩ : ∃ D : E →L[ℂ] E, D = U.starProjection - V.starProjection := ⟨_, rfl⟩
  have hDstar : IsSelfAdjoint D := by
    rw [hDdef]
    exact (isSelfAdjoint_starProjection U).sub (isSelfAdjoint_starProjection V)
  have hpoint : ∀ x : E, ‖D x‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖x‖ ^ 2 := by
    intro x
    have hx := h x
    have hreflect : (V.reflection : E →L[ℂ] E) * (U.reflection : E →L[ℂ] E) +
        (U.reflection : E →L[ℂ] E) * (V.reflection : E →L[ℂ] E) =
        (2 : ℂ) • (1 : E →L[ℂ] E) -
          (4 : ℂ) • ((U.starProjection - V.starProjection) *
            (U.starProjection - V.starProjection)) :=
      U.reflection_mul_add_mul_reflection V
    rw [hreflect, ← hDdef] at hx
    have hval : ((2 : ℂ) • (1 : E →L[ℂ] E) - (4 : ℂ) • (D * D)) x
        = (2 : ℂ) • x - (4 : ℂ) • D (D x) := by
      simp only [sub_apply, smul_apply, one_apply_eq_self, mul_apply_eq_comp]
    rw [hval, inner_sub_left, map_sub, inner_smul_left, inner_smul_left] at hx
    have hDsq : RCLike.re ⟪D (D x), x⟫_ℂ = ‖D x‖ ^ 2 := by
      calc RCLike.re ⟪D (D x), x⟫_ℂ = RCLike.re ⟪(star D) (D x), x⟫_ℂ := by
            rw [hDstar.star_eq]
        _ = RCLike.re ⟪D x, D x⟫_ℂ := by
            rw [ContinuousLinearMap.star_eq_adjoint,
              ContinuousLinearMap.adjoint_inner_left]
        _ = ‖D x‖ ^ 2 := by rw [inner_self_eq_norm_sq]
    have htwo : RCLike.re ((starRingEnd ℂ) (2 : ℂ) * ⟪x, x⟫_ℂ) = 2 * ‖x‖ ^ 2 := by
      simpa using re_conj_real_mul_inner_self (E := E) 2 x
    have hfour : RCLike.re ((starRingEnd ℂ) (4 : ℂ) * ⟪D (D x), x⟫_ℂ) =
        4 * RCLike.re ⟪D (D x), x⟫_ℂ := re_conj_real_mul 4 ⟪D (D x), x⟫_ℂ
    rw [htwo, hfour, hDsq] at hx
    linarith
  have hDnorm : ‖D‖ ≤ Real.sqrt (1 / 2 : ℝ) :=
    ContinuousLinearMap.opNorm_le_sqrt_of_forall_sq_norm_le D hpoint
  have hsqrt : Real.sqrt (1 / 2 : ℝ) = Real.sqrt 2 / 2 := by
    rw [show (1 / 2 : ℝ) = 2 / 2 ^ 2 by norm_num, Real.sqrt_div' 2 (by norm_num),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Submodule.projectionGap_def]
  rw [← hDdef, ← hsqrt]
  exact hDnorm

/-- **The pointwise strict form.**  Where the reflection product's real part is
strictly positive on a vector, the projector difference is strictly below the
`√2/2` threshold *at that vector*.

This is the same computation as `hpoint` inside
`subspaceGap_le_of_reflectionProduct_form_nonneg`, kept strict.  A supremum
bound does not follow -- the strictness is pointwise and need not be uniform --
which is exactly the distinction Section 8 turns on at unbounded scope. -/
theorem norm_starProjection_sub_sq_lt_of_reflectionProduct_form_pos
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] {x : E}
    (h : 0 < RCLike.re ⟪((V.reflection : E →L[ℂ] E) * (U.reflection : E →L[ℂ] E)
      + (U.reflection : E →L[ℂ] E) * (V.reflection : E →L[ℂ] E)) x, x⟫_ℂ) :
    ‖U.starProjection x - V.starProjection x‖ ^ 2 < (1 / 2 : ℝ) * ‖x‖ ^ 2 := by
  obtain ⟨D, hDdef⟩ : ∃ D : E →L[ℂ] E, D = U.starProjection - V.starProjection := ⟨_, rfl⟩
  have hDstar : IsSelfAdjoint D := by
    rw [hDdef]
    exact (isSelfAdjoint_starProjection U).sub (isSelfAdjoint_starProjection V)
  have hDx : D x = U.starProjection x - V.starProjection x := by rw [hDdef]; rfl
  have hx := h
  have hreflect : (V.reflection : E →L[ℂ] E) * (U.reflection : E →L[ℂ] E) +
        (U.reflection : E →L[ℂ] E) * (V.reflection : E →L[ℂ] E) =
        (2 : ℂ) • (1 : E →L[ℂ] E) -
          (4 : ℂ) • ((U.starProjection - V.starProjection) *
            (U.starProjection - V.starProjection)) :=
      U.reflection_mul_add_mul_reflection V
  rw [hreflect, ← hDdef] at hx
  have hval : ((2 : ℂ) • (1 : E →L[ℂ] E) - (4 : ℂ) • (D * D)) x
      = (2 : ℂ) • x - (4 : ℂ) • D (D x) := by
    simp only [sub_apply, smul_apply, one_apply_eq_self, mul_apply_eq_comp]
  rw [hval, inner_sub_left, map_sub, inner_smul_left, inner_smul_left] at hx
  have hDsq : RCLike.re ⟪D (D x), x⟫_ℂ = ‖D x‖ ^ 2 := by
    calc RCLike.re ⟪D (D x), x⟫_ℂ = RCLike.re ⟪(star D) (D x), x⟫_ℂ := by
          rw [hDstar.star_eq]
      _ = RCLike.re ⟪D x, D x⟫_ℂ := by
          rw [ContinuousLinearMap.star_eq_adjoint,
            ContinuousLinearMap.adjoint_inner_left]
      _ = ‖D x‖ ^ 2 := by rw [inner_self_eq_norm_sq]
  have htwo : RCLike.re ((starRingEnd ℂ) (2 : ℂ) * ⟪x, x⟫_ℂ) = 2 * ‖x‖ ^ 2 := by
    simpa using re_conj_real_mul_inner_self (E := E) 2 x
  have hfour : RCLike.re ((starRingEnd ℂ) (4 : ℂ) * ⟪D (D x), x⟫_ℂ) =
      4 * RCLike.re ⟪D (D x), x⟫_ℂ := re_conj_real_mul 4 ⟪D (D x), x⟫_ℂ
  rw [htwo, hfour, hDsq] at hx
  rw [← hDx]
  linarith

/-- **`Θ ≤ π/4` in the printed angle form.** -/
theorem maximalAngle_le_pi_div_four_of_reflectionProduct_form_nonneg
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : ∀ x : E, 0 ≤ RCLike.re ⟪((V.reflection : E →L[ℂ] E) * (U.reflection : E →L[ℂ] E)
      + (U.reflection : E →L[ℂ] E) * (V.reflection : E →L[ℂ] E)) x, x⟫_ℂ) :
    TauCeti.DavisKahanExt.maximalAngle U V ≤ Real.pi / 4 := by
  have hle := subspaceGap_le_of_reflectionProduct_form_nonneg U V h
  have hpi : Real.arcsin (Real.sqrt 2 / 2) = Real.pi / 4 := by
    rw [← Real.sin_pi_div_four]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  calc TauCeti.DavisKahanExt.maximalAngle U V
      = Real.arcsin (U.projectionGap V) := rfl
    _ ≤ Real.arcsin (Real.sqrt 2 / 2) := Real.arcsin_le_arcsin hle
    _ = Real.pi / 4 := hpi

end

end DavisKahan
end TauCeti
