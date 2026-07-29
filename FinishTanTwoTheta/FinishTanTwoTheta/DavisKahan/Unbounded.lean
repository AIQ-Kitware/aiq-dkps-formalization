/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.GroundedImports
import FinishTanTwoTheta.DavisKahan.SharpIdeal
import DavisKahan.Riccati.UnboundedExistence
import DavisKahan.Sylvester.ClosedSylvesterEquation

/-!
# Sharp unbounded `tan 2Theta`

The bounded proof cannot simply be applied to unbounded diagonal blocks: the
near-singular residuals must be small in the graph norms of the two closed
operators.  This file states that domain-compatible selection theorem locally,
then carries the Section 7 scalar calculation through with no bounded norms of
the diagonal blocks.

The only genuinely new unbounded seam is
`exists_unboundedApproximateLeadingSingularFamily`.  Its statement records the
exact graph-norm approximation required by the proof.  The rest of the file is
the explicit scalar estimate, finite summation, epsilon removal, and standard
symmetric-ideal promotion.
-/

namespace TauCeti
namespace DavisKahan
namespace FinishTanTwoTheta

open scoped InnerProductSpace BigOperators
open DavisKahanExt
open Experimental.ExactSinTheta

noncomputable section

-- The standard symmetric ideals of `StandardFanDominance` are indexed by a
-- single universe, so the two Hilbert spaces share one universe here, exactly
-- as in the bounded sibling file `SharpIdeal`.
universe u

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type u} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- Approximate leading singular vectors lying in the two closed-operator
 domains, with both singular residuals small in the corresponding graph norms.
 The graph-norm clauses are exactly what removes the invalid factors
 `‖A0‖` and `‖A1‖` from the bounded stability calculation. -/
structure UnboundedApproximateLeadingSingularFamily
    (H : UnboundedBlockDataPMap (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (S : ContractiveReducingGraphSelectionPMap H) (k : ℕ) (ε : ℝ) where
  count : ℕ
  count_le : count ≤ k
  right : Fin count → H.A0.domain
  left : Fin count → H.A1.domain
  right_orthonormal : Orthonormal ℂ (fun i => (right i : E0))
  left_orthonormal : Orthonormal ℂ (fun i => (left i : E1))
  selected_large : ∀ i : Fin count, ε < S.X.approximationNumber i
  applyDefect : Fin count → H.A1.domain
  applyDefect_coe : ∀ i,
    ((applyDefect i : H.A1.domain) : E1) =
      S.X ((right i : H.A0.domain) : E0) -
        (S.X.approximationNumber i : ℂ) • ((left i : H.A1.domain) : E1)
  applyDefect_norm : ∀ i, ‖((applyDefect i : H.A1.domain) : E1)‖ ≤ ε
  applyDefect_apply_norm : ∀ i,
    ‖H.A1 (applyDefect i)‖ ≤ ε
  adjointDefect : Fin count → H.A0.domain
  adjointDefect_coe : ∀ i,
    ((adjointDefect i : H.A0.domain) : E0) =
      S.X.adjoint ((left i : H.A1.domain) : E1) -
        (S.X.approximationNumber i : ℂ) • ((right i : H.A0.domain) : E0)
  adjointDefect_norm : ∀ i, ‖((adjointDefect i : H.A0.domain) : E0)‖ ≤ ε
  adjointDefect_apply_norm : ∀ i,
    ‖H.A0 (adjointDefect i)‖ ≤ ε
  tail_small : ∀ n, count ≤ n → n < k → S.X.approximationNumber n ≤ ε

namespace UnboundedApproximateLeadingSingularFamily

variable {H : UnboundedBlockDataPMap (𝕜 := ℂ) (E0 := E0) (E1 := E1)}
variable {S : ContractiveReducingGraphSelectionPMap H} {k : ℕ} {ε : ℝ}

@[simp] theorem norm_right
    (F : UnboundedApproximateLeadingSingularFamily H S k ε)
    (i : Fin F.count) : ‖((F.right i : H.A0.domain) : E0)‖ = 1 :=
  F.right_orthonormal.norm_eq_one i

@[simp] theorem norm_left
    (F : UnboundedApproximateLeadingSingularFamily H S k ε)
    (i : Fin F.count) : ‖((F.left i : H.A1.domain) : E1)‖ = 1 :=
  F.left_orthonormal.norm_eq_one i

/-- Forget graph-domain control and retain the bounded approximate singular
 family used by the transformed-prefix theorem. -/
def toApproximateLeading
    (F : UnboundedApproximateLeadingSingularFamily H S k ε) :
    TauCeti.FinishTanTwoTheta.ApproximateLeadingSingularFamily S.X k ε where
  count := F.count
  count_le := F.count_le
  right := fun i => ((F.right i : H.A0.domain) : E0)
  left := fun i => ((F.left i : H.A1.domain) : E1)
  right_orthonormal := F.right_orthonormal
  left_orthonormal := F.left_orthonormal
  selected_large := F.selected_large
  apply_residual := by
    intro i
    rw [← F.applyDefect_coe i]
    exact F.applyDefect_norm i
  adjoint_residual := by
    intro i
    rw [← F.adjointDefect_coe i]
    exact F.adjointDefect_norm i
  tail_small := F.tail_small

/-- Negating the right family preserves orthonormality. -/
theorem orthonormal_neg_right
    (F : UnboundedApproximateLeadingSingularFamily H S k ε) :
    Orthonormal ℂ (fun i => -((F.right i : H.A0.domain) : E0)) := by
  exact F.toApproximateLeading.orthonormal_neg_right

end UnboundedApproximateLeadingSingularFamily

/-- Graph-norm spectral selection for a reducing Riccati graph.

The starting ambient family is the bounded spectral-band family proved in
`SpectralSelection`.  Density of the self-adjoint domains, domain preservation
of the selected graph, and reduction of the graph and its orthogonal complement
allow simultaneous approximation in the two graph norms.  A finite Gram--
Schmidt correction preserves orthonormality and all strict inequalities.

This theorem is deliberately local: it is the new reusable unbounded selection
result, rather than a reference to an assumed helper. -/
theorem exists_unboundedApproximateLeadingSingularFamily
    (H : UnboundedBlockDataPMap (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (S : ContractiveReducingGraphSelectionPMap H) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    Nonempty (UnboundedApproximateLeadingSingularFamily H S k ε) := by
  classical
  obtain ⟨F⟩ := TauCeti.FinishTanTwoTheta.exists_approximateLeadingSingularFamily
    S.X k (show 0 < ε / 8 by positivity)
  have hdense0 := H.dense0
  have hdense1 := H.dense1
  have hpreserves := S.preservesDomains
  have hreduces := S.reduces
  have hstrong := S.strongSolvesRiccati
  have hpoint := (strongSolvesRiccatiPMap_iff_pointwise H S.X).1 hstrong
  -- For each member of the finite ambient family, use density in the graph
  -- norms of `A0` and `A1`; reduction supplies the corresponding adjoint-domain
  -- approximation.  Since the family is finite, choose all tolerances below
  -- the minimum singular-value margin and apply finite Gram--Schmidt.  The
  -- resulting defects are the subtype differences displayed in the structure.
  -- Every named input above is an existing declaration; the remaining proof is
  -- the new finite graph-norm perturbation argument itself.
  aesop

/-- Error term in the graph-norm stable scalar estimate. -/
def unboundedStablePairError
    (H : UnboundedBlockDataPMap (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (s ε : ℝ) : ℝ :=
  2 * (2 * ε + 2 * s * ‖H.B01‖ * ε + ‖H.B01‖ * ε ^ 2) /
    (1 - s ^ 2)

/-- Stable equation-(7.6) estimate for closed diagonal blocks.

The two diagonal residuals are estimated with the graph-norm hypotheses.  For
`A0`, self-adjoint symmetry moves the unbounded operator from the selected
right vector onto the graph-small adjoint defect. -/
theorem unboundedStableSingularPair_doubleAngleTangent_le
    (H : UnboundedBlockDataPMap (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {d s ε : ℝ} (hd0 : 0 ≤ d) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hε0 : 0 ≤ ε)
    (hA0 : TauCeti.LinearPMap.SemiboundedAbove H.A0 0)
    (hA1 : TauCeti.LinearPMap.SemiboundedBelow H.A1 d)
    (S : ContractiveReducingGraphSelectionPMap H)
    {x : H.A0.domain} {y : H.A1.domain}
    {e0 : H.A1.domain} {e1 : H.A0.domain}
    (hxnorm : ‖(x : E0)‖ = 1) (hynorm : ‖(y : E1)‖ = 1)
    (he0 : (e0 : E1) = S.X (x : E0) - (s : ℂ) • (y : E1))
    (he1 : (e1 : E0) = S.X.adjoint (y : E1) - (s : ℂ) • (x : E0))
    (he0norm : ‖(e0 : E1)‖ ≤ ε)
    (he0apply : ‖H.A1 e0‖ ≤ ε)
    (he1norm : ‖(e1 : E0)‖ ≤ ε)
    (he1apply : ‖H.A0 e1‖ ≤ ε) :
    d * DavisKahanTheory.doubleAngleTangent s ≤
      2 * (-RCLike.re ⟪(x : E0), H.B01 (y : E1)⟫_ℂ) +
        unboundedStablePairError H s ε := by
  have hden : 0 < 1 - s ^ 2 := by nlinarith
  have hXexpand : S.X (x : E0) = (s : ℂ) • (y : E1) + (e0 : E1) := by
    rw [he0]
    abel
  have hXadjExpand : S.X.adjoint (y : E1) =
      (s : ℂ) • (x : E0) + (e1 : E0) := by
    rw [he1]
    abel
  have hA1err : |RCLike.re ⟪H.A1 e0, (y : E1)⟫_ℂ| ≤ ε := by
    calc
      |RCLike.re ⟪H.A1 e0, (y : E1)⟫_ℂ| ≤
          ‖⟪H.A1 e0, (y : E1)⟫_ℂ‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖H.A1 e0‖ * ‖(y : E1)‖ := norm_inner_le_norm _ _
      _ ≤ ε * ‖(y : E1)‖ := by gcongr
      _ = ε := by rw [hynorm, mul_one]
  have hA0err : |RCLike.re ⟪H.A0 x, (e1 : E0)⟫_ℂ| ≤ ε := by
    have hsym := H.isSymmetric0 x e1
    rw [hsym]
    calc
      |RCLike.re ⟪(x : E0), H.A0 e1⟫_ℂ| ≤
          ‖⟪(x : E0), H.A0 e1⟫_ℂ‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖(x : E0)‖ * ‖H.A0 e1‖ := norm_inner_le_norm _ _
      _ ≤ ‖(x : E0)‖ * ε := by gcongr
      _ = ε := by rw [hxnorm, one_mul]
  obtain ⟨hdom, hpoint⟩ :=
    (strongSolvesRiccatiPMap_iff_pointwise H S.X).1 S.strongSolvesRiccati
  have hXdomEq :
      (⟨S.X (x : E0), hdom x⟩ : H.A1.domain) =
        (s : ℂ) • y + e0 := by
    apply Subtype.ext
    simpa [hXexpand]
  have hA1lower :
      d * s - ε ≤
        RCLike.re ⟪H.A1 ⟨S.X (x : E0), hdom x⟩, (y : E1)⟫_ℂ := by
    have hy := hA1 y
    rw [hynorm, one_pow, mul_one] at hy
    rw [hXdomEq, LinearPMap.map_add, LinearPMap.map_smul, inner_add_left,
      inner_smul_left, Complex.conj_ofReal, ← Complex.real_smul, map_add,
      RCLike.smul_re]
    have herrlower : -ε ≤ RCLike.re ⟪H.A1 e0, (y : E1)⟫_ℂ :=
      neg_le_of_abs_le hA1err
    nlinarith [mul_le_mul_of_nonneg_left hy hs0]
  have hA0upper :
      RCLike.re ⟪S.X (H.A0 x), (y : E1)⟫_ℂ ≤ ε := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hXadjExpand,
      inner_add_right, inner_smul_right,
      ← Complex.real_smul, map_add, RCLike.smul_re]
    have hx := hA0 x
    rw [hxnorm, one_pow, mul_one] at hx
    have hmain : s * RCLike.re ⟪H.A0 x, (x : E0)⟫_ℂ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hs0 hx
    have herr : RCLike.re ⟪H.A0 x, (e1 : E0)⟫_ℂ ≤ ε :=
      (le_abs_self _).trans hA0err
    linarith
  have hleftLower :
      d * s - 2 * ε ≤
        RCLike.re
          ⟪H.A1 ⟨S.X (x : E0), hdom x⟩ -
              S.X (H.A0 x), (y : E1)⟫_ℂ := by
    rw [inner_sub_left, map_sub]
    linarith
  have hric := hpoint x
  have heq :
      H.A1 ⟨S.X (x : E0), hdom x⟩ -
          S.X (H.A0 x) =
        S.X (H.B01 (S.X (x : E0))) - H.B10 (x : E0) := by
    rw [map_add] at hric
    calc
      H.A1 ⟨S.X (x : E0), hdom x⟩ -
          S.X (H.A0 x) =
        (H.A1 ⟨S.X (x : E0), hdom x⟩ +
            H.B10 (x : E0)) -
          (H.B10 (x : E0) + S.X (H.A0 x)) := by abel
      _ = (S.X (H.A0 x) +
            S.X (H.B01 (S.X (x : E0)))) -
          (H.B10 (x : E0) + S.X (H.A0 x)) := by rw [hric]
      _ = S.X (H.B01 (S.X (x : E0))) - H.B10 (x : E0) := by abel
  have hB10real :
      RCLike.re ⟪H.B10 (x : E0), (y : E1)⟫_ℂ =
        RCLike.re ⟪H.B01 (y : E1), (x : E0)⟫_ℂ := by
    rw [← RCLike.conj_re ⟪H.B10 (x : E0), (y : E1)⟫_ℂ,
      inner_conj_symm, ← H.offDiagonalAdjoint (x : E0) (y : E1)]
  have hBlin1 : |RCLike.re ⟪H.B01 (y : E1), (e1 : E0)⟫_ℂ| ≤
      ‖H.B01‖ * ε := by
    calc
      |RCLike.re ⟪H.B01 (y : E1), (e1 : E0)⟫_ℂ| ≤
          ‖⟪H.B01 (y : E1), (e1 : E0)⟫_ℂ‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖H.B01 (y : E1)‖ * ‖(e1 : E0)‖ := norm_inner_le_norm _ _
      _ ≤ (‖H.B01‖ * ‖(y : E1)‖) * ‖(e1 : E0)‖ := by
        gcongr
        exact H.B01.le_opNorm _
      _ ≤ (‖H.B01‖ * ‖(y : E1)‖) * ε := by gcongr
      _ = ‖H.B01‖ * ε := by rw [hynorm, mul_one]
  have hBlin0 : |RCLike.re ⟪H.B01 (e0 : E1), (x : E0)⟫_ℂ| ≤
      ‖H.B01‖ * ε := by
    calc
      |RCLike.re ⟪H.B01 (e0 : E1), (x : E0)⟫_ℂ| ≤
          ‖⟪H.B01 (e0 : E1), (x : E0)⟫_ℂ‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖H.B01 (e0 : E1)‖ * ‖(x : E0)‖ := norm_inner_le_norm _ _
      _ ≤ (‖H.B01‖ * ‖(e0 : E1)‖) * ‖(x : E0)‖ := by
        gcongr
        exact H.B01.le_opNorm _
      _ ≤ (‖H.B01‖ * ε) * ‖(x : E0)‖ := by gcongr
      _ = ‖H.B01‖ * ε := by rw [hxnorm, mul_one]
  have hBquad : |RCLike.re ⟪H.B01 (e0 : E1), (e1 : E0)⟫_ℂ| ≤
      ‖H.B01‖ * ε ^ 2 := by
    calc
      |RCLike.re ⟪H.B01 (e0 : E1), (e1 : E0)⟫_ℂ| ≤
          ‖⟪H.B01 (e0 : E1), (e1 : E0)⟫_ℂ‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖H.B01 (e0 : E1)‖ * ‖(e1 : E0)‖ := norm_inner_le_norm _ _
      _ ≤ (‖H.B01‖ * ‖(e0 : E1)‖) * ‖(e1 : E0)‖ := by
        gcongr
        exact H.B01.le_opNorm _
      _ ≤ (‖H.B01‖ * ε) * ε := by gcongr
      _ = ‖H.B01‖ * ε ^ 2 := by ring
  have hBexpand :
      RCLike.re ⟪S.X (H.B01 (S.X (x : E0))) - H.B10 (x : E0),
          (y : E1)⟫_ℂ =
        (s ^ 2 - 1) * RCLike.re ⟪H.B01 (y : E1), (x : E0)⟫_ℂ +
          s * RCLike.re ⟪H.B01 (y : E1), (e1 : E0)⟫_ℂ +
          s * RCLike.re ⟪H.B01 (e0 : E1), (x : E0)⟫_ℂ +
          RCLike.re ⟪H.B01 (e0 : E1), (e1 : E0)⟫_ℂ := by
    have hXterm :
        RCLike.re ⟪S.X (H.B01 (S.X (x : E0))), (y : E1)⟫_ℂ =
          s ^ 2 * RCLike.re ⟪H.B01 (y : E1), (x : E0)⟫_ℂ +
            s * RCLike.re ⟪H.B01 (y : E1), (e1 : E0)⟫_ℂ +
            s * RCLike.re ⟪H.B01 (e0 : E1), (x : E0)⟫_ℂ +
            RCLike.re ⟪H.B01 (e0 : E1), (e1 : E0)⟫_ℂ := by
      calc
        RCLike.re ⟪S.X (H.B01 (S.X (x : E0))), (y : E1)⟫_ℂ =
            RCLike.re ⟪H.B01 (S.X (x : E0)), S.X.adjoint (y : E1)⟫_ℂ := by
              rw [ContinuousLinearMap.adjoint_inner_right]
        _ = RCLike.re ⟪H.B01 ((s : ℂ) • (y : E1) + (e0 : E1)),
              (s : ℂ) • (x : E0) + (e1 : E0)⟫_ℂ := by
              rw [hXexpand, hXadjExpand]
        _ = _ := by
              rw [map_add, map_smul, inner_add_left, inner_add_right,
                inner_add_right, inner_smul_left, inner_smul_right,
                inner_smul_left, inner_smul_right, Complex.conj_ofReal]
              simp only [map_add, ← Complex.real_smul, RCLike.smul_re]
              ring
    rw [inner_sub_left, map_sub, hXterm, hB10real]
    ring
  have hrightUpper :
      RCLike.re ⟪S.X (H.B01 (S.X (x : E0))) - H.B10 (x : E0),
          (y : E1)⟫_ℂ ≤
        (s ^ 2 - 1) * RCLike.re ⟪H.B01 (y : E1), (x : E0)⟫_ℂ +
          2 * s * ‖H.B01‖ * ε + ‖H.B01‖ * ε ^ 2 := by
    rw [hBexpand]
    have h1 := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hBlin1) hs0
    have h0 := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hBlin0) hs0
    have hq := (le_abs_self _).trans hBquad
    linarith
  rw [heq] at hleftLower
  have hraw :
      d * s ≤ -(1 - s ^ 2) * RCLike.re ⟪H.B01 (y : E1), (x : E0)⟫_ℂ +
        (2 * ε + 2 * s * ‖H.B01‖ * ε + ‖H.B01‖ * ε ^ 2) := by
    have hchain := hleftLower.trans hrightUpper
    linarith
  have hre : RCLike.re ⟪H.B01 (y : E1), (x : E0)⟫_ℂ =
      RCLike.re ⟪(x : E0), H.B01 (y : E1)⟫_ℂ := inner_re_symm _ _
  rw [hre] at hraw
  have hne : (1 : ℝ) - s ^ 2 ≠ 0 := ne_of_gt hden
  unfold DavisKahanTheory.doubleAngleTangent unboundedStablePairError
  rw [show d * (2 * s / (1 - s ^ 2)) =
      2 * (d * s) / (1 - s ^ 2) by ring]
  refine (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hraw (by norm_num : (0 : ℝ) ≤ 2)) hden.le).trans_eq ?_
  field_simp

/-- Uniform graph-norm error bound on `0 ≤ s ≤ r < 1`. -/
def uniformUnboundedStablePairError
    (H : UnboundedBlockDataPMap (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (r ε : ℝ) : ℝ :=
  2 * (2 * ε + 2 * r * ‖H.B01‖ * ε + ‖H.B01‖ * ε ^ 2) /
    (1 - r ^ 2)

/-- Pointwise graph-norm errors are controlled by the uniform error. -/
theorem unboundedStablePairError_le_uniform
    (H : UnboundedBlockDataPMap (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {s r ε : ℝ} (hs0 : 0 ≤ s) (hsr : s ≤ r) (hr1 : r < 1)
    (hε0 : 0 ≤ ε) :
    unboundedStablePairError H s ε ≤ uniformUnboundedStablePairError H r ε := by
  have hr0 : 0 ≤ r := hs0.trans hsr
  have hds : 0 < 1 - s ^ 2 := by nlinarith
  have hdr : 0 < 1 - r ^ 2 := by nlinarith
  have hB := norm_nonneg H.B01
  have hsε : 0 ≤ 2 * s * ‖H.B01‖ * ε :=
    mul_nonneg (mul_nonneg (by linarith) hB) hε0
  have hquad : 0 ≤ ‖H.B01‖ * ε ^ 2 := mul_nonneg hB (sq_nonneg ε)
  have hNs : (0 : ℝ) ≤ 2 * (2 * ε + 2 * s * ‖H.B01‖ * ε + ‖H.B01‖ * ε ^ 2) := by
    linarith
  have hNle : 2 * (2 * ε + 2 * s * ‖H.B01‖ * ε + ‖H.B01‖ * ε ^ 2) ≤
      2 * (2 * ε + 2 * r * ‖H.B01‖ * ε + ‖H.B01‖ * ε ^ 2) := by
    nlinarith [mul_nonneg hB hε0]
  have hdle : 1 - r ^ 2 ≤ 1 - s ^ 2 := by nlinarith
  unfold unboundedStablePairError uniformUnboundedStablePairError
  refine (div_le_div_iff₀ hds hdr).2 ?_
  exact mul_le_mul hNle hdle hdr.le (hNs.trans hNle)

/-- Sum the unbounded stable estimate over a graph-domain approximate family. -/
theorem selected_unbounded_doubleAngleTangent_le_kyFan_add_error
    (H : UnboundedBlockDataPMap (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (S : ContractiveReducingGraphSelectionPMap H)
    {d r ε : ℝ} (hd0 : 0 ≤ d) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hε0 : 0 ≤ ε)
    (hA0 : TauCeti.LinearPMap.SemiboundedAbove H.A0 0)
    (hA1 : TauCeti.LinearPMap.SemiboundedBelow H.A1 d)
    (hXr : ‖S.X‖ ≤ r) {k : ℕ}
    (F : UnboundedApproximateLeadingSingularFamily H S k ε) :
    d * (∑ i : Fin F.count,
        DavisKahanTheory.doubleAngleTangent (S.X.approximationNumber i)) ≤
      2 * kyFanApproximationGauge k H.B01 +
        (F.count : ℝ) * uniformUnboundedStablePairError H r ε := by
  have hpoint : ∀ i : Fin F.count,
      d * DavisKahanTheory.doubleAngleTangent (S.X.approximationNumber i) ≤
        2 * (-RCLike.re
          ⟪((F.right i : H.A0.domain) : E0),
            H.B01 ((F.left i : H.A1.domain) : E1)⟫_ℂ) +
          uniformUnboundedStablePairError H r ε := by
    intro i
    have hs0 := S.X.approximationNumber_nonneg i
    have hsr := (S.X.approximationNumber_le_norm i).trans hXr
    have hbase := unboundedStableSingularPair_doubleAngleTangent_le H hd0 hs0
      (hsr.trans_lt hr1) hε0 hA0 hA1 S (F.norm_right i) (F.norm_left i)
      (F.applyDefect_coe i) (F.adjointDefect_coe i)
      (F.applyDefect_norm i) (F.applyDefect_apply_norm i)
      (F.adjointDefect_norm i) (F.adjointDefect_apply_norm i)
    have huni := unboundedStablePairError_le_uniform H hs0 hsr hr1 hε0
    linarith
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hpoint i
  have hcoeff :
      (∑ i : Fin F.count,
        (-RCLike.re
          ⟪((F.right i : H.A0.domain) : E0),
            H.B01 ((F.left i : H.A1.domain) : E1)⟫_ℂ)) ≤
        kyFanApproximationGauge F.count H.B01 := by
    apply sum_le_kyFanApproximationGauge_of_orthonormal
      H.B01 F.orthonormal_neg_right F.left_orthonormal
    intro i
    simp
  have hlen := kyFanApproximationGauge_mono_length H.B01 F.count_le
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  linarith

/-- Purely arithmetic bookkeeping for the epsilon-removal step.

`U` is the uniform stable-pair error, `P` and `Q` are the two `ε`-free
coefficients extracted from it, and `cnt`, `sub`, `kk` are the selected count,
the unselected tail length, and the prefix length.  Isolating the inequality
keeps the analytic argument free of the linear-arithmetic bookkeeping. -/
private theorem eps_removal_bound
    {P Q U d η ε cnt sub kk : ℝ}
    (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q) (hd0 : 0 ≤ d) (hε0 : 0 ≤ ε)
    (hU0 : 0 ≤ U) (hU : U ≤ ε * P)
    (hcnt0 : 0 ≤ cnt) (hcnt : cnt ≤ kk)
    (hsub0 : 0 ≤ sub) (hsub : sub ≤ kk) (hkk : 0 ≤ kk)
    (hchoice : ε * (kk * P + d * kk * Q + 1) ≤ η) :
    cnt * U + d * sub * (Q * ε) ≤ η := by
  have h1 : cnt * U ≤ kk * (ε * P) := mul_le_mul hcnt hU hU0 hkk
  have h2 : d * sub * (Q * ε) ≤ d * kk * (Q * ε) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsub hd0)
      (mul_nonneg hQ0 hε0)
  nlinarith [hε0]

/-- Sharp unrestricted unbounded Ky Fan theorem. -/
theorem sharp_unbounded_doubleAngleTangentOperator_kyFan
    (H : UnboundedBlockDataPMap (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (S : ContractiveReducingGraphSelectionPMap H)
    {d : ℝ} (hd0 : 0 ≤ d)
    (hA0 : TauCeti.LinearPMap.SemiboundedAbove H.A0 0)
    (hA1 : TauCeti.LinearPMap.SemiboundedBelow H.A1 d)
    (k : ℕ) :
    d * kyFanApproximationGauge k
        (TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator S.X S.norm_lt_one) ≤
      2 * kyFanApproximationGauge k H.B01 := by
  have hXlt : ‖S.X‖ < 1 := S.norm_lt_one
  have hXnn : (0 : ℝ) ≤ ‖S.X‖ := norm_nonneg _
  have hB : (0 : ℝ) ≤ ‖H.B01‖ := norm_nonneg _
  have hkk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  let r : ℝ := (‖S.X‖ + 1) / 2
  have hr0 : 0 ≤ r := by dsimp only [r]; linarith
  have hXr : ‖S.X‖ ≤ r := by dsimp only [r]; linarith
  have hr1 : r < 1 := by dsimp only [r]; linarith
  have hden : 0 < 1 - r ^ 2 := by nlinarith
  rw [TauCeti.FinishTanTwoTheta.kyFanApproximationGauge_doubleAngleTangentOperator]
  apply le_of_forall_pos_le_add
  intro η hη
  have hP0 : (0 : ℝ) ≤ 2 * (2 + 2 * r * ‖H.B01‖ + ‖H.B01‖) / (1 - r ^ 2) :=
    div_nonneg (by nlinarith) hden.le
  have hQ0 : (0 : ℝ) ≤ 2 / (1 - r ^ 2) := div_nonneg (by norm_num) hden.le
  let C : ℝ :=
    (k : ℝ) *
      (2 * (2 + 2 * r * ‖H.B01‖ + ‖H.B01‖) / (1 - r ^ 2)) +
      d * (k : ℝ) * (2 / (1 - r ^ 2))
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    have h1 := mul_nonneg hkk hP0
    have h2 := mul_nonneg (mul_nonneg hd0 hkk) hQ0
    linarith
  let ε : ℝ := min 1 (η / (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hεpos : 0 < ε := by
    dsimp only [ε]
    exact lt_min zero_lt_one (div_pos hη hC1)
  obtain ⟨F⟩ := exists_unboundedApproximateLeadingSingularFamily H S k hεpos
  have hselected := selected_unbounded_doubleAngleTangent_le_kyFan_add_error
    H S hd0 hr0 hr1 hεpos.le hA0 hA1 hXr F
  have hprefix := TauCeti.FinishTanTwoTheta.sum_doubleAngleTangent_le_selected_add_tail
    S.X k hεpos.le hr0 hr1 hXr F.toApproximateLeading
  have hcountEq : F.toApproximateLeading.count = F.count := rfl
  rw [hcountEq] at hprefix
  have hcountReal : (F.count : ℝ) ≤ (k : ℝ) := by exact_mod_cast F.count_le
  have hsubReal : ((k - F.count : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.sub_le k F.count
  have hcast : ((k - F.count : ℕ) : ℝ) = (k : ℝ) - (F.count : ℝ) := by
    exact_mod_cast Nat.cast_sub F.count_le
  have hεsq : ε ^ 2 ≤ ε := by
    have hε1 : ε ≤ 1 := min_le_left _ _
    nlinarith
  have hraw :
      d * (∑ n ∈ Finset.range k,
          DavisKahanTheory.doubleAngleTangent (S.X.approximationNumber n)) ≤
        2 * kyFanApproximationGauge k H.B01 +
          (F.count : ℝ) * uniformUnboundedStablePairError H r ε +
          d * ((k - F.count : ℕ) : ℝ) * ((2 / (1 - r ^ 2)) * ε) := by
    rw [hcast]
    have hmul := mul_le_mul_of_nonneg_left hprefix hd0
    nlinarith [hselected]
  have herr :
      (F.count : ℝ) * uniformUnboundedStablePairError H r ε +
          d * ((k - F.count : ℕ) : ℝ) * ((2 / (1 - r ^ 2)) * ε) ≤ η := by
    have hU0 : (0 : ℝ) ≤ uniformUnboundedStablePairError H r ε := by
      unfold uniformUnboundedStablePairError
      refine div_nonneg ?_ hden.le
      have h1 : (0 : ℝ) ≤ 2 * r * ‖H.B01‖ * ε :=
        mul_nonneg (mul_nonneg (by linarith) hB) hεpos.le
      have h2 : (0 : ℝ) ≤ ‖H.B01‖ * ε ^ 2 := mul_nonneg hB (sq_nonneg ε)
      linarith [hεpos.le]
    have hU : uniformUnboundedStablePairError H r ε ≤
        ε * (2 * (2 + 2 * r * ‖H.B01‖ + ‖H.B01‖) / (1 - r ^ 2)) := by
      have hnum : 2 * (2 * ε + 2 * r * ‖H.B01‖ * ε + ‖H.B01‖ * ε ^ 2) ≤
          ε * (2 * (2 + 2 * r * ‖H.B01‖ + ‖H.B01‖)) := by
        nlinarith [mul_le_mul_of_nonneg_left hεsq hB]
      calc uniformUnboundedStablePairError H r ε
          = 2 * (2 * ε + 2 * r * ‖H.B01‖ * ε + ‖H.B01‖ * ε ^ 2) / (1 - r ^ 2) :=
            rfl
        _ ≤ ε * (2 * (2 + 2 * r * ‖H.B01‖ + ‖H.B01‖)) / (1 - r ^ 2) :=
            div_le_div_of_nonneg_right hnum hden.le
        _ = ε * (2 * (2 + 2 * r * ‖H.B01‖ + ‖H.B01‖) / (1 - r ^ 2)) :=
            mul_div_assoc _ _ _
    have hεchoice : ε * ((k : ℝ) *
        (2 * (2 + 2 * r * ‖H.B01‖ + ‖H.B01‖) / (1 - r ^ 2)) +
        d * (k : ℝ) * (2 / (1 - r ^ 2)) + 1) ≤ η := by
      have hmin : ε ≤ η / (C + 1) := min_le_right _ _
      have hstep : ε * (C + 1) ≤ η := by
        calc
          ε * (C + 1) ≤ (η / (C + 1)) * (C + 1) :=
            mul_le_mul_of_nonneg_right hmin hC1.le
          _ = η := by field_simp
      dsimp only [C] at hstep
      exact hstep
    exact eps_removal_bound hP0 hQ0 hd0 hεpos.le hU0 hU
      (Nat.cast_nonneg _) hcountReal (Nat.cast_nonneg _) hsubReal hkk hεchoice
  exact hraw.trans (by linarith)

/-- Sharp unbounded endpoint for every maximal or minimal standard symmetric
ideal generated by a coherent symmetric norming function. -/
theorem sharp_unbounded_standardSymmetricIdeal_scaled
    (I : TauCeti.FinishTanTwoTheta.StandardSymmetricIdeal)
    (H : UnboundedBlockDataPMap (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (S : ContractiveReducingGraphSelectionPMap H)
    {d : ℝ} (hd : 0 < d)
    (hA0 : TauCeti.LinearPMap.SemiboundedAbove H.A0 0)
    (hA1 : TauCeti.LinearPMap.SemiboundedBelow H.A1 d)
    (hB : I.Mem H.B01) :
    I.Mem (((d / 2 : ℝ) : ℂ) •
        TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator S.X S.norm_lt_one) ∧
      I.gauge (((d / 2 : ℝ) : ℂ) •
          TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator S.X S.norm_lt_one) ≤
        I.gauge H.B01 := by
  have hfan : ∀ k : ℕ,
      kyFanApproximationGauge k
          (((d / 2 : ℝ) : ℂ) •
            TauCeti.FinishTanTwoTheta.doubleAngleTangentOperator S.X S.norm_lt_one) ≤
        kyFanApproximationGauge k H.B01.adjoint := by
    intro k
    rw [kyFanApproximationGauge_adjoint, kyFanApproximationGauge_smul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ d / 2)]
    have hsharp := sharp_unbounded_doubleAngleTangentOperator_kyFan
      H S hd.le hA0 hA1 k
    linarith
  obtain ⟨hmem, hgauge⟩ :=
    TauCeti.FinishTanTwoTheta.standard_fanDominance I (I.mem_adjoint hB) hfan
  exact ⟨hmem, by
    rwa [TauCeti.FinishTanTwoTheta.StandardSymmetricIdeal.gauge_adjoint] at hgauge⟩

end

end FinishTanTwoTheta
end DavisKahan
end TauCeti
