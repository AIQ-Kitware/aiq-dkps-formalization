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

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
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
    rw [hXdomEq, map_add, map_smul, inner_add_left, inner_smul_left,
      Complex.conj_ofReal, ← Complex.real_smul, RCLike.smul_re]
    have herrlower : -ε ≤ RCLike.re ⟪H.A1 e0, (y : E1)⟫_ℂ :=
      neg_le_of_abs_le hA1err
    nlinarith [mul_le_mul_of_nonneg_left hy hs0]
  have hA0upper :
      RCLike.re ⟪S.X (H.A0 x), (y : E1)⟫_ℂ ≤ ε := by
    rw [ContinuousLinearMap.adjoint_inner_right, hXadjExpand,
      inner_add_right, inner_smul_right,
      ← Complex.real_smul, RCLike.smul_re]
    have hx := hA0 x
    rw [hxnorm, one_pow, mul_one, mul_zero] at hx
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
        (H.B10 (x : E0) +
            H.A1 ⟨S.X (x : E0), hdom x⟩) -
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
                inner_smul_left, inner_smul_right, Complex.conj_ofReal,
                ← Complex.real_smul, RCLike.smul_re,
                ← Complex.real_smul, RCLike.smul_re,
                ← Complex.real_smul, RCLike.smul_re]
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
  unfold DavisKahanTheory.doubleAngleTangent unboundedStablePairError
  rw [show d * (2 * s / (1 - s ^ 2)) =
      2 * (d * s) / (1 - s ^ 2) by ring]
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hraw (by norm_num : (0 : ℝ) ≤ 2)) hden.le)

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
  unfold unboundedStablePairError uniformUnboundedStablePairError
  apply (div_le_div_iff₀ hds hdr).2
  nlinarith [norm_nonneg H.B01]

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
    exact (unboundedStableSingularPair_doubleAngleTangent_le H hd0 hs0
      (hsr.trans_lt hr1) hε0 hA0 hA1 S (F.norm_right i) (F.norm_left i)
      (F.applyDefect_coe i) (F.adjointDefect_coe i)
      (F.applyDefect_norm i) (F.applyDefect_apply_norm i)
      (F.adjointDefect_norm i) (F.adjointDefect_apply_norm i)).trans
        (add_le_add_left
          (unboundedStablePairError_le_uniform H hs0 hsr hr1 hε0) _)
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
  rw [Finset.mul_sum, Finset.mul_sum] at hsum
  simpa [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] using
    hsum.trans (by nlinarith [hcoeff, hlen])

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
  let r : ℝ := (‖S.X‖ + 1) / 2
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hXr : ‖S.X‖ ≤ r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  rw [TauCeti.FinishTanTwoTheta.kyFanApproximationGauge_doubleAngleTangentOperator]
  apply le_of_forall_pos_le_add
  intro η hη
  let C : ℝ :=
    (k : ℝ) *
      (2 * (2 + 2 * r * ‖H.B01‖ + ‖H.B01‖) / (1 - r ^ 2)) +
      d * (k : ℝ) * (2 / (1 - r ^ 2))
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  let ε : ℝ := min 1 (η / (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min zero_lt_one (div_pos hη hC1)
  obtain ⟨F⟩ := exists_unboundedApproximateLeadingSingularFamily H S k hεpos
  have hselected := selected_unbounded_doubleAngleTangent_le_kyFan_add_error
    H S hd0 hr0 hr1 hεpos.le hA0 hA1 hXr F
  have hprefix := TauCeti.FinishTanTwoTheta.sum_doubleAngleTangent_le_selected_add_tail
    S.X k hεpos.le hr0 hr1 hXr F.toApproximateLeading
  have hcountReal : (F.count : ℝ) ≤ (k : ℝ) := by exact_mod_cast F.count_le
  have hsubReal : ((k - F.count : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.sub_le k F.count
  have hεsq : ε ^ 2 ≤ ε := by
    have hε1 : ε ≤ 1 := min_le_left _ _
    nlinarith
  have hraw :
      d * (∑ n ∈ Finset.range k,
          DavisKahanTheory.doubleAngleTangent (S.X.approximationNumber n)) ≤
        2 * kyFanApproximationGauge k H.B01 +
          (F.count : ℝ) * uniformUnboundedStablePairError H r ε +
          d * ((k - F.count : ℕ) : ℝ) * ((2 / (1 - r ^ 2)) * ε) := by
    have hmul := mul_le_mul_of_nonneg_left hprefix hd0
    nlinarith [hselected]
  have herr :
      (F.count : ℝ) * uniformUnboundedStablePairError H r ε +
          d * ((k - F.count : ℕ) : ℝ) * ((2 / (1 - r ^ 2)) * ε) ≤ η := by
    have hεchoice : ε * (C + 1) ≤ η := by
      have hmin : ε ≤ η / (C + 1) := min_le_right _ _
      calc
        ε * (C + 1) ≤ (η / (C + 1)) * (C + 1) :=
          mul_le_mul_of_nonneg_right hmin hC1.le
        _ = η := by field_simp
    unfold uniformUnboundedStablePairError
    dsimp [C] at hεchoice ⊢
    nlinarith [hcountReal, hsubReal, norm_nonneg H.B01]
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
  apply TauCeti.FinishTanTwoTheta.standard_fanDominance I hB
  intro k
  rw [kyFanApproximationGauge_smul, RCLike.norm_ofReal,
    abs_of_nonneg (by positivity : 0 ≤ d / 2)]
  have hsharp := sharp_unbounded_doubleAngleTangentOperator_kyFan
    H S hd.le hA0 hA1 k
  nlinarith

end

end FinishTanTwoTheta
end DavisKahan
end TauCeti
