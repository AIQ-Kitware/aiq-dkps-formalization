/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.DoubleAngle.KyFanOrthonormal
import DavisKahan.DoubleAngle.TanTwoThetaKyFan
import DavisKahan.Experimental.InfiniteDimensional.TanTwoTheta.BoundedRiccatiEstimate

/-!
# Dimension-free paired-singular-family core for `tan 2Theta`

The existing finite-dimensional Section 7 proof obtains the sharp Ky Fan
inequality by summing the scalar Riccati identity over paired singular vectors.
The existing infinite-dimensional theorem compresses to a finite carrier and
therefore assumes that the invariant source subspace is finite-dimensional.

This scratch module removes the ambient finite-dimensionality assumption from
the *analytic summation step*.  It proves the sharp scalar coefficient estimate
for one exact singular pair of an arbitrary bounded Riccati solution, and then
sums it over any finite orthonormal exact singular family.  The result is the
hard dimension-free core needed by the source's arbitrary-unitarily-invariant-
norm argument.

The remaining spectral-selection bridge is deliberately explicit.  For a
compact graph coordinate it should be discharged by an ordered compact
singular system.  For a general bounded coordinate it requires simultaneous
approximate singular families and a limiting argument.  This module does not
hide that separate operator-theoretic obligation behind an axiom or `sorry`.
-/

open scoped InnerProductSpace BigOperators

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace Scratch
namespace Section7

open DavisKahanExt
open DavisKahanTheory
open ExactSinTheta

universe u v

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- A finite orthonormal family of exact left/right singular pairs of a bounded
operator.  No ambient finite-dimensionality or compactness is assumed. -/
structure ExactSingularFamily (X : E0 →L[ℂ] E1) (k : ℕ) where
  right : Fin k → E0
  left : Fin k → E1
  value : Fin k → ℝ
  right_orthonormal : Orthonormal ℂ right
  left_orthonormal : Orthonormal ℂ left
  value_nonneg : ∀ i, 0 ≤ value i
  apply_right : ∀ i, X (right i) = (value i : ℂ) • left i
  adjoint_apply_left : ∀ i, X.adjoint (left i) = (value i : ℂ) • right i

namespace ExactSingularFamily

variable {X : E0 →L[ℂ] E1} {k : ℕ}

@[simp] theorem norm_right (F : ExactSingularFamily X k) (i : Fin k) :
    ‖F.right i‖ = 1 :=
  F.right_orthonormal.norm_eq_one i

@[simp] theorem norm_left (F : ExactSingularFamily X k) (i : Fin k) :
    ‖F.left i‖ = 1 :=
  F.left_orthonormal.norm_eq_one i

/-- Negating one side of an orthonormal family preserves orthonormality. -/
theorem orthonormal_neg_right (F : ExactSingularFamily X k) :
    Orthonormal ℂ (fun i => -F.right i) := by
  have hright := F.right_orthonormal
  rw [orthonormal_iff_ite] at hright ⊢
  intro i j
  simpa using hright i j

end ExactSingularFamily

/-- The exact one-pair Riccati coefficient estimate underlying equation (7.6).

Compared with `riccati_near_singular_pair_bound`, this theorem retains the
matched coefficient of the off-diagonal block instead of replacing it by the
operator norm.  That retained coefficient is what can be summed by the Ky Fan
variational inequality. -/
theorem exactSingularPair_doubleAngleTangent_le_neg_re_inner
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d s : ℝ} (hd0 : 0 ≤ d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    {x : E0} {y : E1}
    (hxnorm : ‖x‖ = 1) (hynorm : ‖y‖ = 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hXx : X x = (s : ℂ) • y)
    (hXay : X.adjoint y = (s : ℂ) • x) :
    d * doubleAngleTangent s ≤
      2 * (-RCLike.re ⟪x, B.B01 y⟫_ℂ) := by
  have hden : 0 < 1 - s ^ 2 := by nlinarith
  have hA1lower : d * s ≤ s * RCLike.re ⟪B.A1 y, y⟫_ℂ := by
    have hy := hA1 y
    rw [hynorm, one_pow, mul_one] at hy
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hy hs0
  have hA1exact :
      RCLike.re ⟪B.A1 (X x), y⟫_ℂ =
        s * RCLike.re ⟪B.A1 y, y⟫_ℂ := by
    rw [hXx, map_smul, inner_smul_left, Complex.conj_ofReal,
      ← Complex.real_smul, RCLike.smul_re]
  have hA0exact :
      RCLike.re ⟪X (B.A0 x), y⟫_ℂ =
        s * RCLike.re ⟪B.A0 x, x⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hXay, inner_smul_right,
      ← Complex.real_smul, RCLike.smul_re]
  have hA0nonpos :
      s * RCLike.re ⟪B.A0 x, x⟫_ℂ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hs0 (hA0 x)
  have hleft : d * s ≤
      RCLike.re ⟪B.A1 (X x) - X (B.A0 x), y⟫_ℂ := by
    rw [inner_sub_left, map_sub, hA1exact, hA0exact]
    linarith
  have hpoint := (solvesRiccati_iff_pointwise B X).1 hX x
  have heq : B.A1 (X x) - X (B.A0 x) =
      X (B.B01 (X x)) - B.B10 x := by
    rw [map_add] at hpoint
    calc
      B.A1 (X x) - X (B.A0 x) =
          (B.B10 x + B.A1 (X x)) -
            (B.B10 x + X (B.A0 x)) := by abel
      _ = (X (B.A0 x) + X (B.B01 (X x))) -
            (B.B10 x + X (B.A0 x)) := by rw [hpoint]
      _ = X (B.B01 (X x)) - B.B10 x := by abel
  have hB10real :
      RCLike.re ⟪B.B10 x, y⟫_ℂ =
        RCLike.re ⟪x, B.B01 y⟫_ℂ := by
    calc
      RCLike.re ⟪B.B10 x, y⟫_ℂ =
          RCLike.re ⟪y, B.B10 x⟫_ℂ := inner_re_symm _ _
      _ = RCLike.re ⟪B.B01 y, x⟫_ℂ := by rw [B.offDiagonalAdjoint x y]
      _ = RCLike.re ⟪x, B.B01 y⟫_ℂ := inner_re_symm _ _
  have hXterm :
      RCLike.re ⟪X (B.B01 (X x)), y⟫_ℂ =
        s ^ 2 * RCLike.re ⟪x, B.B01 y⟫_ℂ := by
    calc
      RCLike.re ⟪X (B.B01 (X x)), y⟫_ℂ =
          RCLike.re ⟪B.B01 (X x), X.adjoint y⟫_ℂ := by
            rw [ContinuousLinearMap.adjoint_inner_right]
      _ = RCLike.re
          ⟪B.B01 ((s : ℂ) • y), (s : ℂ) • x⟫_ℂ := by
            rw [hXx, hXay]
      _ = s ^ 2 * RCLike.re ⟪x, B.B01 y⟫_ℂ := by
            simp only [map_smul, inner_smul_left, inner_smul_right,
              Complex.conj_ofReal]
            have hre : ∀ w : ℂ,
                RCLike.re ((s : ℂ) * w) = s * RCLike.re w := by
              intro w
              simp [RCLike.re_to_complex, Complex.mul_re]
            rw [hre, hre, inner_re_symm (B.B01 y) x]
            ring
  have hright :
      RCLike.re ⟪X (B.B01 (X x)) - B.B10 x, y⟫_ℂ =
        (s ^ 2 - 1) * RCLike.re ⟪x, B.B01 y⟫_ℂ := by
    rw [inner_sub_left, map_sub, hXterm, hB10real]
    ring
  rw [heq, hright] at hleft
  unfold doubleAngleTangent
  rw [show d * (2 * s / (1 - s ^ 2)) =
      (2 * (d * s)) / (1 - s ^ 2) by ring]
  rw [div_le_iff₀ hden]
  nlinarith

/-- Dimension-free finite-family form of the sharp `tan 2Theta` Ky Fan root.
The source and target Hilbert spaces may both be infinite-dimensional. -/
theorem kyFan_doubleAngleTangent_le_of_exactSingularFamily
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd0 : 0 ≤ d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    {k : ℕ} (F : ExactSingularFamily X k)
    (hcontractive : ∀ i, F.value i < 1) :
    d * ∑ i, doubleAngleTangent (F.value i) ≤
      2 * kyFanApproximationGauge k B.B01 := by
  have hpoint : ∀ i,
      d * doubleAngleTangent (F.value i) ≤
        2 * (-RCLike.re ⟪F.right i, B.B01 (F.left i)⟫_ℂ) := by
    intro i
    exact exactSingularPair_doubleAngleTangent_le_neg_re_inner B hd0 hA0 hA1
      hX (F.norm_right i) (F.norm_left i) (F.value_nonneg i)
      (hcontractive i) (F.apply_right i) (F.adjoint_apply_left i)
  have hsum :
      d * ∑ i, doubleAngleTangent (F.value i) ≤
        2 * ∑ i, (-RCLike.re ⟪F.right i, B.B01 (F.left i)⟫_ℂ) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hpoint i
  have hky :
      ∑ i, (-RCLike.re ⟪F.right i, B.B01 (F.left i)⟫_ℂ) ≤
        kyFanApproximationGauge k B.B01 := by
    apply sum_le_kyFanApproximationGauge_of_orthonormal
      B.B01 F.orthonormal_neg_right F.left_orthonormal
    intro i
    simp
  exact hsum.trans (mul_le_mul_of_nonneg_left hky (by norm_num))

/-- Exact-family attainment of the approximation singular values.  This is the
remaining spectral-selection interface after the dimension-free Riccati/Ky Fan
argument above.  It is automatic in finite dimensions; a compact-operator
implementation should construct it from an ordered compact singular system. -/
def HasExactApproximationSingularFamilies (X : E0 →L[ℂ] E1) : Prop :=
  ∀ k : ℕ, ∃ F : ExactSingularFamily X k,
    ∀ i : Fin k, F.value i = approximationSingularValue (i : ℕ) X

/-- Full approximation-number Ky Fan conclusion once exact leading singular
families are supplied.  This theorem contains no dimensional assumption; the
separate attainment interface records exactly what must be provided by the
compact spectral theorem (or replaced by an approximate-family limit in the
fully noncompact setting). -/
theorem kyFan_doubleAngleTangent_offDiagonal_le_of_exactFamilies
    (B : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d : ℝ} (hd0 : 0 ≤ d)
    (hA0 : ∀ z : E0, RCLike.re ⟪B.A0 z, z⟫_ℂ ≤ 0)
    (hA1 : ∀ z : E1, d * ‖z‖ ^ 2 ≤ RCLike.re ⟪B.A1 z, z⟫_ℂ)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati B X)
    (hX1 : approximationSingularValue 0 X < 1)
    (hfamilies : HasExactApproximationSingularFamilies X)
    (k : ℕ) :
    d * ∑ n ∈ Finset.range k,
        doubleAngleTangent (approximationSingularValue n X) ≤
      2 * kyFanApproximationGauge k B.B01 := by
  obtain ⟨F, hF⟩ := hfamilies k
  have hcontractive : ∀ i, F.value i < 1 := by
    intro i
    rw [hF i]
    exact lt_of_le_of_lt
      (approximationSingularValue_antitone X (Nat.zero_le (i : ℕ))) hX1
  have hcore := kyFan_doubleAngleTangent_le_of_exactSingularFamily
    B hd0 hA0 hA1 hX F hcontractive
  have hsum :
      (∑ i : Fin k, doubleAngleTangent (F.value i)) =
        ∑ n ∈ Finset.range k,
          doubleAngleTangent (approximationSingularValue n X) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun n => doubleAngleTangent (approximationSingularValue n X)) k]
    exact Finset.sum_congr rfl fun i _ => by rw [hF i]
  rwa [hsum] at hcore

end Section7
end Scratch
end Experimental
end DavisKahan
end TauCeti