/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.GenuineBoundedTruncation
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.Bounded
import ForMathlib.Analysis.InnerProductSpace.CoerciveUnit

/-!
# Interface-parametric filled spectral truncations

This module rebuilds the filled bounded truncation used by the ordered
two-unbounded Sylvester argument over `GenuineSpectralCutoffInterface` and
`GenuineBoundedTruncationInterface`.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace
open scoped Topology
open Filter

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Fill the complement of an orthogonal spectral cutoff by a real scalar. -/
noncomputable def genuineFilledTruncation
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := H))
    (hA : A.IsSelfAdjoint)
    (Pcut : GenuineSpectralCutoffInterface A hA)
    (Tcut : GenuineBoundedTruncationInterface A hA Pcut)
    (a τ : ℝ) : H →L[𝕜] H :=
  Tcut.truncation τ +
    ((a : ℝ) : 𝕜) •
      (ContinuousLinearMap.id 𝕜 H - Pcut.cutoff τ)

/-- A filled truncation is symmetric. -/
theorem genuineFilledTruncation_isSymmetric
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := H))
    (hA : A.IsSelfAdjoint)
    (Pcut : GenuineSpectralCutoffInterface A hA)
    (Tcut : GenuineBoundedTruncationInterface A hA Pcut)
    (a τ : ℝ) :
    (genuineFilledTruncation A hA Pcut Tcut a τ).IsSymmetric := by
  have hT := Tcut.isSymmetric τ
  have hP := (Pcut.isOrthogonalProjection τ).2
  exact hT.add (LinearMap.IsSymmetric.smul (RCLike.conj_ofReal a)
    (LinearMap.IsSymmetric.id.sub hP))

/-- The complement of an orthogonal cutoff is orthogonal to its range, and
its squared norm completes the Pythagorean decomposition. -/
theorem genuineCutoff_complement_identities
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := H))
    (hA : A.IsSelfAdjoint)
    (Pcut : GenuineSpectralCutoffInterface A hA)
    (Tcut : GenuineBoundedTruncationInterface A hA Pcut)
    (τ : ℝ) (x : H) :
    let P := Pcut.cutoff τ
    ⟪P x, x - P x⟫_𝕜 = 0 ∧
      ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 = ‖x‖ ^ 2 := by
  let P := Pcut.cutoff τ
  have hP := Pcut.isOrthogonalProjection τ
  have hPP : P (P x) = P x := by
    have h := congrArg (fun T : H →L[𝕜] H => T x) hP.1
    simpa only [P, ContinuousLinearMap.comp_apply] using h
  have hPQ : P (x - P x) = 0 := by
    rw [map_sub, hPP, sub_self]
  have horth : ⟪P x, x - P x⟫_𝕜 = 0 := by
    calc
      ⟪P x, x - P x⟫_𝕜 = ⟪x, P (x - P x)⟫_𝕜 := hP.2 x (x - P x)
      _ = 0 := by simp only [hPQ, inner_zero_right]
  refine ⟨horth, ?_⟩
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (P x) (x - P x) horth
  rw [show P x + (x - P x) = x by abel] at h
  rw [sq, sq, sq]
  linarith

/-- A filled truncation commutes with its cutoff, and either compression
recovers the bounded truncation. -/
theorem genuineFilledTruncation_commutes_cutoff
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := H))
    (hA : A.IsSelfAdjoint)
    (Pcut : GenuineSpectralCutoffInterface A hA)
    (Tcut : GenuineBoundedTruncationInterface A hA Pcut)
    (a τ : ℝ) :
    genuineFilledTruncation A hA Pcut Tcut a τ ∘L Pcut.cutoff τ =
        Tcut.truncation τ ∧
      Pcut.cutoff τ ∘L genuineFilledTruncation A hA Pcut Tcut a τ =
        Tcut.truncation τ := by
  let P := Pcut.cutoff τ
  let T := Tcut.truncation τ
  have hP := (Pcut.isOrthogonalProjection τ).1
  have hT := Tcut.commutes_cutoff τ
  constructor
  · ext x
    have hPP := congrArg (fun S : H →L[𝕜] H => S x) hP
    have hTP := congrArg (fun S : H →L[𝕜] H => S x) hT.1
    change T (P x) + ((a : ℝ) : 𝕜) • (P x - P (P x)) = T x
    rw [show T (P x) = T x by
      simpa only [P, T, ContinuousLinearMap.comp_apply] using hTP]
    rw [show P (P x) = P x by
      simpa only [P, ContinuousLinearMap.comp_apply] using hPP]
    simp
  · ext x
    have hPP := congrArg (fun S : H →L[𝕜] H => S x) hP
    have hPT := congrArg (fun S : H →L[𝕜] H => S x) hT.2
    change P (T x + ((a : ℝ) : 𝕜) • (x - P x)) = T x
    rw [map_add, map_smul, map_sub]
    rw [show P (T x) = T x by
      simpa only [P, T, ContinuousLinearMap.comp_apply] using hPT]
    rw [show P (P x) = P x by
      simpa only [P, ContinuousLinearMap.comp_apply] using hPP]
    simp

/-- On a cutoff vector, a filled truncation agrees with the original closed
operator. -/
theorem genuineFilledTruncation_eq_on_cutoff
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := H))
    (hA : A.IsSelfAdjoint)
    (Pcut : GenuineSpectralCutoffInterface A hA)
    (Tcut : GenuineBoundedTruncationInterface A hA Pcut)
    (a τ : ℝ) (x : H) :
    ∃ hx : Pcut.cutoff τ x ∈ A.domain,
      genuineFilledTruncation A hA Pcut Tcut a τ (Pcut.cutoff τ x) =
        A.toLinearMap ⟨Pcut.cutoff τ x, hx⟩ := by
  obtain ⟨hx, hTx⟩ := Tcut.eq_on_cutoff τ x
  refine ⟨hx, ?_⟩
  have hcomp := (genuineFilledTruncation_commutes_cutoff
    A hA Pcut Tcut a τ).1
  have happly := congrArg (fun S : H →L[𝕜] H => S x) hcomp
  calc
    genuineFilledTruncation A hA Pcut Tcut a τ (Pcut.cutoff τ x) =
        Tcut.truncation τ x := by
      simpa only [ContinuousLinearMap.comp_apply] using happly
    _ = A.toLinearMap ⟨Pcut.cutoff τ x, hx⟩ := hTx

/-- For a fixed fill value, filled truncations converge strongly to the closed
operator on its domain. -/
theorem genuineFilledTruncation_tendsto_on_domain
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := H))
    (hA : A.IsSelfAdjoint)
    (Pcut : GenuineSpectralCutoffInterface A hA)
    (Tcut : GenuineBoundedTruncationInterface A hA Pcut)
    (a : ℝ) (x : A.domain) :
    Tendsto
      (fun τ : ℝ => genuineFilledTruncation A hA Pcut Tcut a τ (x : H))
      atTop (𝓝 (A.toLinearMap x)) := by
  have hT := Tcut.tendsto_on_domain x
  have hP := Pcut.tendsto_identity (x : H)
  have hQ : Tendsto (fun τ : ℝ => (x : H) - Pcut.cutoff τ (x : H))
      atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (x : H)) (f := atTop (α := ℝ))).sub hP
    simpa only [sub_self] using h
  have ha : Tendsto (fun _ : ℝ => ((a : ℝ) : 𝕜)) atTop
      (𝓝 ((a : ℝ) : 𝕜)) := tendsto_const_nhds
  have hfill : Tendsto
      (fun τ : ℝ => Tcut.truncation τ (x : H) +
        ((a : ℝ) : 𝕜) • ((x : H) - Pcut.cutoff τ (x : H)))
      atTop (𝓝 (A.toLinearMap x)) := by
    have h := hT.add (ha.smul hQ)
    simpa only [smul_zero, add_zero] using h
  have hfun :
      (fun τ : ℝ => genuineFilledTruncation A hA Pcut Tcut a τ (x : H)) =
        fun τ : ℝ => Tcut.truncation τ (x : H) +
          ((a : ℝ) : 𝕜) • ((x : H) - Pcut.cutoff τ (x : H)) := by
    funext τ
    simp only [genuineFilledTruncation, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  rw [hfun]
  exact hfill

/-- A lower form bound on a cutoff range becomes a global lower bound after
filling the orthogonal complement by the same scalar. -/
theorem genuineFilledTruncation_lowerBound
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := H))
    (hA : A.IsSelfAdjoint)
    (Pcut : GenuineSpectralCutoffInterface A hA)
    (Tcut : GenuineBoundedTruncationInterface A hA Pcut)
    {a τ : ℝ} (hτ : 0 ≤ τ)
    (ha : SemiboundedBelow A a) :
    ∀ x, a * ‖x‖ ^ 2 ≤
      RCLike.re ⟪genuineFilledTruncation A hA Pcut Tcut a τ x, x⟫_𝕜 := by
  intro x
  let P := Pcut.cutoff τ
  let T := Tcut.truncation τ
  have hproj := genuineCutoff_complement_identities A hA Pcut Tcut τ x
  have hcomm := Tcut.commutes_cutoff τ
  have hPT : P (T x) = T x := by
    have h := congrArg (fun S : H →L[𝕜] H => S x) hcomm.2
    simpa only [P, T, ContinuousLinearMap.comp_apply] using h
  have hPP : P (P x) = P x := by
    have h := congrArg (fun S : H →L[𝕜] H => S x)
      (Pcut.isOrthogonalProjection τ).1
    simpa only [P, ContinuousLinearMap.comp_apply] using h
  have hPQ : P (x - P x) = 0 := by rw [map_sub, hPP, sub_self]
  have hTorth : ⟪T x, x - P x⟫_𝕜 = 0 := by
    calc
      ⟪T x, x - P x⟫_𝕜 = ⟪P (T x), x - P x⟫_𝕜 := by rw [hPT]
      _ = ⟪T x, P (x - P x)⟫_𝕜 :=
        (Pcut.isOrthogonalProjection τ).2 (T x) (x - P x)
      _ = 0 := by simp only [hPQ, inner_zero_right]
  have hQorth : ⟪x - P x, P x⟫_𝕜 = 0 := by
    rw [← inner_conj_symm, hproj.1, map_zero]
  have hx : x = P x + (x - P x) := by abel
  have hTinner : RCLike.re ⟪T x, x⟫_𝕜 =
      RCLike.re ⟪T x, P x⟫_𝕜 := by
    calc
      RCLike.re ⟪T x, x⟫_𝕜 =
          RCLike.re ⟪T x, P x + (x - P x)⟫_𝕜 :=
        congrArg RCLike.re (congrArg (fun y => ⟪T x, y⟫_𝕜) hx)
      _ = RCLike.re ⟪T x, P x⟫_𝕜 := by
        rw [inner_add_right, map_add, hTorth, map_zero, add_zero]
  have hQinner : RCLike.re ⟪x - P x, x⟫_𝕜 = ‖x - P x‖ ^ 2 := by
    calc
      RCLike.re ⟪x - P x, x⟫_𝕜 =
          RCLike.re ⟪x - P x, P x + (x - P x)⟫_𝕜 :=
        congrArg RCLike.re (congrArg (fun y => ⟪x - P x, y⟫_𝕜) hx)
      _ = ‖x - P x‖ ^ 2 := by
        rw [inner_add_right, map_add, hQorth, map_zero, zero_add,
          inner_self_eq_norm_sq]
  have hcut := Tcut.lowerBound ha hτ x
  change a * ‖x‖ ^ 2 ≤
    RCLike.re ⟪T x + ((a : ℝ) : 𝕜) • (x - P x), x⟫_𝕜
  rw [inner_add_left, map_add, inner_smul_left, RCLike.conj_ofReal,
    RCLike.re_ofReal_mul, hTinner, hQinner]
  rw [← hproj.2]
  linarith

/-- An upper form bound on a cutoff range becomes a global upper bound after
filling the orthogonal complement by the same scalar. -/
theorem genuineFilledTruncation_upperBound
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := H))
    (hA : A.IsSelfAdjoint)
    (Pcut : GenuineSpectralCutoffInterface A hA)
    (Tcut : GenuineBoundedTruncationInterface A hA Pcut)
    {a τ : ℝ} (hτ : 0 ≤ τ)
    (ha : SemiboundedAbove A a) :
    ∀ x, RCLike.re ⟪genuineFilledTruncation A hA Pcut Tcut a τ x, x⟫_𝕜 ≤
      a * ‖x‖ ^ 2 := by
  intro x
  let P := Pcut.cutoff τ
  let T := Tcut.truncation τ
  have hproj := genuineCutoff_complement_identities A hA Pcut Tcut τ x
  have hcomm := Tcut.commutes_cutoff τ
  have hPT : P (T x) = T x := by
    have h := congrArg (fun S : H →L[𝕜] H => S x) hcomm.2
    simpa only [P, T, ContinuousLinearMap.comp_apply] using h
  have hPP : P (P x) = P x := by
    have h := congrArg (fun S : H →L[𝕜] H => S x)
      (Pcut.isOrthogonalProjection τ).1
    simpa only [P, ContinuousLinearMap.comp_apply] using h
  have hPQ : P (x - P x) = 0 := by rw [map_sub, hPP, sub_self]
  have hTorth : ⟪T x, x - P x⟫_𝕜 = 0 := by
    calc
      ⟪T x, x - P x⟫_𝕜 = ⟪P (T x), x - P x⟫_𝕜 := by rw [hPT]
      _ = ⟪T x, P (x - P x)⟫_𝕜 :=
        (Pcut.isOrthogonalProjection τ).2 (T x) (x - P x)
      _ = 0 := by simp only [hPQ, inner_zero_right]
  have hQorth : ⟪x - P x, P x⟫_𝕜 = 0 := by
    rw [← inner_conj_symm, hproj.1, map_zero]
  have hx : x = P x + (x - P x) := by abel
  have hTinner : RCLike.re ⟪T x, x⟫_𝕜 =
      RCLike.re ⟪T x, P x⟫_𝕜 := by
    calc
      RCLike.re ⟪T x, x⟫_𝕜 =
          RCLike.re ⟪T x, P x + (x - P x)⟫_𝕜 :=
        congrArg RCLike.re (congrArg (fun y => ⟪T x, y⟫_𝕜) hx)
      _ = RCLike.re ⟪T x, P x⟫_𝕜 := by
        rw [inner_add_right, map_add, hTorth, map_zero, add_zero]
  have hQinner : RCLike.re ⟪x - P x, x⟫_𝕜 = ‖x - P x‖ ^ 2 := by
    calc
      RCLike.re ⟪x - P x, x⟫_𝕜 =
          RCLike.re ⟪x - P x, P x + (x - P x)⟫_𝕜 :=
        congrArg RCLike.re (congrArg (fun y => ⟪x - P x, y⟫_𝕜) hx)
      _ = ‖x - P x‖ ^ 2 := by
        rw [inner_add_right, map_add, hQorth, map_zero, zero_add,
          inner_self_eq_norm_sq]
  have hcut := Tcut.upperBound ha hτ x
  change RCLike.re ⟪T x + ((a : ℝ) : 𝕜) • (x - P x), x⟫_𝕜 ≤
    a * ‖x‖ ^ 2
  rw [inner_add_left, map_add, inner_smul_left, RCLike.conj_ofReal,
    RCLike.re_ofReal_mul, hTinner, hQinner]
  rw [← hproj.2]
  linarith

/-- A coercive bounded operator supplies explicit inverse data with the sharp
inverse norm bound. -/
theorem boundedInverseData_of_coercive_direct
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {A : H →L[𝕜] H} {a : ℝ} (ha : 0 < a)
    (hcoer : ∀ x, a * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜) :
    ∃ hInv : BoundedInverseData A, ‖hInv.inv‖ ≤ a⁻¹ := by
  have hunit : IsUnit A :=
    ForMathlib.ContinuousLinearMap.isUnit_of_coercive ha hcoer
  let J : H →L[𝕜] H := Ring.inverse A
  have hJA : J ∘L A = ContinuousLinearMap.id 𝕜 H := by
    exact Ring.inverse_mul_cancel A hunit
  have hAJ : A ∘L J = ContinuousLinearMap.id 𝕜 H := by
    exact Ring.mul_inverse_cancel A hunit
  let hInv : BoundedInverseData A := ⟨J, hJA, hAJ⟩
  refine ⟨hInv, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound J (inv_nonneg.mpr ha.le) ?_
  intro y
  have hlow := ForMathlib.ContinuousLinearMap.norm_smul_le_norm_apply_of_coercive
    hcoer (J y)
  have hJy : A (J y) = y := by
    have h := congrArg (fun T : H →L[𝕜] H => T y) hAJ
    simpa only [J, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h
  rw [hJy] at hlow
  calc
    ‖J y‖ ≤ ‖y‖ / a := (le_div_iff₀ ha).2 (by simpa [mul_comm] using hlow)
    _ = a⁻¹ * ‖y‖ := by rw [div_eq_mul_inv, mul_comm]

/-- The negative-semidefinite shift of a bounded symmetric operator becomes a
norm-bounded positive operator after adding its operator norm. -/
theorem norm_add_opNorm_id_le_of_nonpos_direct
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {B : H →L[𝕜] H} (hBsym : B.IsSymmetric)
    (hBnonpos : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ 0) :
    ‖B + ((‖B‖ : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 H‖ ≤ ‖B‖ := by
  refine ForMathlib.ContinuousLinearMap.norm_le_of_abs_re_inner_map_self_le
    ?_ (norm_nonneg B) ?_
  · exact hBsym.add (LinearMap.IsSymmetric.smul
      (RCLike.conj_ofReal ‖B‖) LinearMap.IsSymmetric.id)
  · intro x
    have habs : |RCLike.re ⟪B x, x⟫_𝕜| ≤ ‖B‖ * ‖x‖ ^ 2 := by
      calc
        |RCLike.re ⟪B x, x⟫_𝕜| ≤ ‖⟪B x, x⟫_𝕜‖ := RCLike.abs_re_le_norm _
        _ ≤ ‖B x‖ * ‖x‖ := norm_inner_le_norm _ _
        _ ≤ (‖B‖ * ‖x‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (B.le_opNorm x) (norm_nonneg x)
        _ = ‖B‖ * ‖x‖ ^ 2 := by ring
    have hlower : -(‖B‖ * ‖x‖ ^ 2) ≤ RCLike.re ⟪B x, x⟫_𝕜 :=
      (abs_le.mp habs).1
    have hupper := hBnonpos x
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
      inner_add_left, map_add, inner_smul_left, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    rw [abs_of_nonneg]
    · linarith
    · linarith


end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
