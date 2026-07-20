/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.ApproximationNumbers
import DavisKahan.Experimental.InfiniteDimensional.Core.UnboundedSpectral
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.Bounded
import ForMathlib.Analysis.InnerProductSpace.CoerciveUnit

/-!
# Fully unbounded Sylvester estimates

This module combines two routes to Davis--Kahan Theorem 5.2.  The
Laplace-semigroup route yields the final theorem from ordinary rectangular
Banach ideal laws.  The spectral-cutoff route follows the paper through finite
Ky Fan estimates and therefore uses `KyFanDominantIdealFamily`; that stronger
property is not derived from the ordinary ideal laws.
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

abbrev ClosedOperatorOnE :=
  ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)
abbrev ClosedOperatorOnF :=
  ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)

/-- Fill the complement of an orthogonal spectral cutoff by a real scalar. -/
noncomputable def filledSpectralTruncation
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := H))
    (hA : A.IsSelfAdjoint) (a τ : ℝ) : H →L[𝕜] H :=
  boundedSpectralTruncation A hA τ +
    ((a : ℝ) : 𝕜) •
      (ContinuousLinearMap.id 𝕜 H - spectralCutoff A hA τ)

/-- A filled truncation is symmetric. -/
theorem filledSpectralTruncation_isSymmetric
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := H))
    (hA : A.IsSelfAdjoint) (a τ : ℝ) :
    (filledSpectralTruncation A hA a τ).IsSymmetric := by
  have hT := boundedSpectralTruncation_isSymmetric A hA τ
  have hP := (spectralCutoff_isOrthogonalProjection A hA τ).2
  exact hT.add (LinearMap.IsSymmetric.smul (RCLike.conj_ofReal a)
    (LinearMap.IsSymmetric.id.sub hP))

/-- The complement of an orthogonal cutoff is orthogonal to its range, and
its squared norm completes the Pythagorean decomposition. -/
theorem spectralCutoff_complement_identities
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := H))
    (hA : A.IsSelfAdjoint) (τ : ℝ) (x : H) :
    let P := spectralCutoff A hA τ
    ⟪P x, x - P x⟫_𝕜 = 0 ∧
      ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 = ‖x‖ ^ 2 := by
  let P := spectralCutoff A hA τ
  have hP := spectralCutoff_isOrthogonalProjection A hA τ
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

/-- A lower form bound on a cutoff range becomes a global lower bound after
filling the orthogonal complement by the same scalar. -/
theorem filledSpectralTruncation_lowerBound
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := H))
    (hA : A.IsSelfAdjoint) {a τ : ℝ} (hτ : 0 ≤ τ)
    (ha : SemiboundedBelow A a) :
    ∀ x, a * ‖x‖ ^ 2 ≤
      RCLike.re ⟪filledSpectralTruncation A hA a τ x, x⟫_𝕜 := by
  intro x
  let P := spectralCutoff A hA τ
  let T := boundedSpectralTruncation A hA τ
  have hproj := spectralCutoff_complement_identities A hA τ x
  have hcomm := boundedSpectralTruncation_commutes_cutoff A hA τ
  have hPT : P (T x) = T x := by
    have h := congrArg (fun S : H →L[𝕜] H => S x) hcomm.2
    simpa only [P, T, ContinuousLinearMap.comp_apply] using h
  have hPP : P (P x) = P x := by
    have h := congrArg (fun S : H →L[𝕜] H => S x)
      (spectralCutoff_isOrthogonalProjection A hA τ).1
    simpa only [P, ContinuousLinearMap.comp_apply] using h
  have hPQ : P (x - P x) = 0 := by rw [map_sub, hPP, sub_self]
  have hTorth : ⟪T x, x - P x⟫_𝕜 = 0 := by
    calc
      ⟪T x, x - P x⟫_𝕜 = ⟪P (T x), x - P x⟫_𝕜 := by rw [hPT]
      _ = ⟪T x, P (x - P x)⟫_𝕜 :=
        (spectralCutoff_isOrthogonalProjection A hA τ).2 (T x) (x - P x)
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
  have hcut := boundedSpectralTruncation_lowerBound A hA ha hτ x
  change a * ‖x‖ ^ 2 ≤
    RCLike.re ⟪T x + ((a : ℝ) : 𝕜) • (x - P x), x⟫_𝕜
  rw [inner_add_left, map_add, inner_smul_left, RCLike.conj_ofReal,
    RCLike.re_ofReal_mul, hTinner, hQinner]
  rw [← hproj.2]
  linarith

/-- An upper form bound on a cutoff range becomes a global upper bound after
filling the orthogonal complement by the same scalar. -/
theorem filledSpectralTruncation_upperBound
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := H))
    (hA : A.IsSelfAdjoint) {a τ : ℝ} (hτ : 0 ≤ τ)
    (ha : SemiboundedAbove A a) :
    ∀ x, RCLike.re ⟪filledSpectralTruncation A hA a τ x, x⟫_𝕜 ≤
      a * ‖x‖ ^ 2 := by
  intro x
  let P := spectralCutoff A hA τ
  let T := boundedSpectralTruncation A hA τ
  have hproj := spectralCutoff_complement_identities A hA τ x
  have hcomm := boundedSpectralTruncation_commutes_cutoff A hA τ
  have hPT : P (T x) = T x := by
    have h := congrArg (fun S : H →L[𝕜] H => S x) hcomm.2
    simpa only [P, T, ContinuousLinearMap.comp_apply] using h
  have hPP : P (P x) = P x := by
    have h := congrArg (fun S : H →L[𝕜] H => S x)
      (spectralCutoff_isOrthogonalProjection A hA τ).1
    simpa only [P, ContinuousLinearMap.comp_apply] using h
  have hPQ : P (x - P x) = 0 := by rw [map_sub, hPP, sub_self]
  have hTorth : ⟪T x, x - P x⟫_𝕜 = 0 := by
    calc
      ⟪T x, x - P x⟫_𝕜 = ⟪P (T x), x - P x⟫_𝕜 := by rw [hPT]
      _ = ⟪T x, P (x - P x)⟫_𝕜 :=
        (spectralCutoff_isOrthogonalProjection A hA τ).2 (T x) (x - P x)
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
  have hcut := boundedSpectralTruncation_upperBound A hA ha hτ x
  change RCLike.re ⟪T x + ((a : ℝ) : 𝕜) • (x - P x), x⟫_𝕜 ≤
    a * ‖x‖ ^ 2
  rw [inner_add_left, map_add, inner_smul_left, RCLike.conj_ofReal,
    RCLike.re_ofReal_mul, hTinner, hQinner]
  rw [← hproj.2]
  linarith

/-- A coercive bounded operator supplies explicit inverse data with the sharp
inverse norm bound. -/
theorem boundedInverseData_of_coercive
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
theorem norm_add_opNorm_id_le_of_nonpos
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

/-- Spectral cutoff converts the right block to a bounded Sylvester equation. -/
theorem spectralCutoff_sylvester_equation
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (_hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E}
    (hEq : HasClosedSylvesterEquation A B X C)
    (τ : ℝ) :
    HasUnboundedBoundedSylvesterEquation A
      (boundedSpectralTruncation B hB τ)
      (X ∘L spectralCutoff B hB τ)
      (C ∘L spectralCutoff B hB τ) := by
  let P : F →L[𝕜] F := spectralCutoff B hB τ
  let T : F →L[𝕜] F := boundedSpectralTruncation B hB τ
  have hPdom : ∀ x : F, P x ∈ B.domain := by
    intro x
    exact spectralCutoff_range_le_domain B hB τ ⟨x, rfl⟩
  have hmap : A.MapsDomainTo
      (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded T)
      (X ∘L P) := by
    intro x
    change X (P (x : F)) ∈ A.domain
    exact hEq.mapsTo_domain ⟨P (x : F), hPdom (x : F)⟩
  refine ⟨hmap, ?_⟩
  intro x
  have hPT : P (T (x : F)) = T (x : F) := by
    have hcomm := congrArg (fun S : F →L[𝕜] F => S (x : F))
      (boundedSpectralTruncation_commutes_cutoff B hB τ).2
    simpa only [P, T, ContinuousLinearMap.comp_apply] using hcomm
  obtain ⟨hxP, hT⟩ :=
    boundedSpectralTruncation_eq_on_cutoff B hB τ (x : F)
  have heq := hEq.equation
    ⟨P (x : F), by simpa only [P] using hxP⟩
  change
    A.toLinearMap
        ⟨X (P (x : F)), hmap x⟩ -
      X (P (T (x : F))) = C (P (x : F))
  rw [hPT]
  rw [show T (x : F) =
    B.toLinearMap ⟨P (x : F), hPdom (x : F)⟩ by
      simpa only [P, T] using hT]
  exact heq

section ApproximationNumberEndpointAssumptions

variable [HasApproximationNumberStrongCutoff.{u, v, 0} 𝕜]
variable [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜]

/-- Finite Ky Fan inequalities for all right spectral cutoffs pass to the
original operators.  This is the topological limit step in the two-unbounded
ordered Sylvester argument; the remaining analytic input is the corresponding
inequality for each bounded truncation. -/
theorem kyFanApproximationGauge_le_of_spectralCutoff_le
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {δ : ℝ} (k : ℕ)
    (hcut : ∀ τ : ℝ, 0 ≤ τ →
      δ * kyFanApproximationGauge k
          (X ∘L spectralCutoff B hB τ) ≤
        kyFanApproximationGauge k
          (C ∘L spectralCutoff B hB τ)) :
    δ * kyFanApproximationGauge k X ≤
      kyFanApproximationGauge k C := by
  have hPproj : ∀ τ : ℝ,
      IsOrthogonalProjectionMap (spectralCutoff B hB τ) := by
    intro τ
    exact spectralCutoff_isOrthogonalProjection B hB τ
  have hPstrong : StronglyTendsto
      (fun τ : ℝ => spectralCutoff B hB τ) atTop
      (ContinuousLinearMap.id 𝕜 F) := by
    intro x
    simpa using spectralCutoff_tendsto_identity B hB x
  have hX := kyFanApproximationGauge_comp_strongProjection_tendsto
    hPproj hPstrong k X
  have hC := kyFanApproximationGauge_comp_strongProjection_tendsto
    hPproj hPstrong k C
  have hcutEventually : ∀ᶠ τ : ℝ in atTop,
      δ * kyFanApproximationGauge k
          (X ∘L spectralCutoff B hB τ) ≤
        kyFanApproximationGauge k
          (C ∘L spectralCutoff B hB τ) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact hcut τ hτ
  exact le_of_tendsto_of_tendsto
    (tendsto_const_nhds.mul hX) hC hcutEventually

/-- Finite Ky Fan gauges also converge under strong orthogonal cutoffs on
the target side. -/
theorem kyFanApproximationGauge_left_comp_strongProjection_tendsto
    {ι : Type} {P : ι → E →L[𝕜] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E))
    (k : ℕ) (K : F →L[𝕜] E) :
    Tendsto
      (fun i => kyFanApproximationGauge k (P i ∘L K))
      l (𝓝 (kyFanApproximationGauge k K)) := by
  have hright := kyFanApproximationGauge_comp_strongProjection_tendsto
    hPproj hP k K.adjoint
  have hpoint : ∀ i,
      kyFanApproximationGauge k (P i ∘L K) =
        kyFanApproximationGauge k (K.adjoint ∘L P i) := by
    intro i
    rw [← kyFanApproximationGauge_adjoint k (P i ∘L K)]
    simp only [ContinuousLinearMap.adjoint_comp]
    rw [(hPproj i).2.clm_adjoint_eq]
  have hlimit : kyFanApproximationGauge k K =
      kyFanApproximationGauge k K.adjoint := by
    symm
    exact kyFanApproximationGauge_adjoint k K
  simpa only [hpoint, hlimit] using hright

/-- Left-cutoff finite Ky Fan inequalities pass to the original operators. -/
theorem kyFanApproximationGauge_le_of_leftSpectralCutoff_le
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    (hA : A.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {δ : ℝ} (k : ℕ)
    (hcut : ∀ τ : ℝ, 0 ≤ τ →
      δ * kyFanApproximationGauge k
          (spectralCutoff A hA τ ∘L X) ≤
        kyFanApproximationGauge k
          (spectralCutoff A hA τ ∘L C)) :
    δ * kyFanApproximationGauge k X ≤
      kyFanApproximationGauge k C := by
  have hPproj : ∀ τ : ℝ,
      IsOrthogonalProjectionMap (spectralCutoff A hA τ) := by
    intro τ
    exact spectralCutoff_isOrthogonalProjection A hA τ
  have hPstrong : StronglyTendsto
      (fun τ : ℝ => spectralCutoff A hA τ) atTop
      (ContinuousLinearMap.id 𝕜 E) := by
    intro x
    simpa using spectralCutoff_tendsto_identity A hA x
  have hX := kyFanApproximationGauge_left_comp_strongProjection_tendsto
    hPproj hPstrong k X
  have hC := kyFanApproximationGauge_left_comp_strongProjection_tendsto
    hPproj hPstrong k C
  have hcutEventually : ∀ᶠ τ : ℝ in atTop,
      δ * kyFanApproximationGauge k
          (spectralCutoff A hA τ ∘L X) ≤
        kyFanApproximationGauge k
          (spectralCutoff A hA τ ∘L C) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact hcut τ hτ
  exact le_of_tendsto_of_tendsto
    (tendsto_const_nhds.mul hX) hC hcutEventually

/-- Double spectral cutoff turns a domain-aware equation into an ordinary
bounded equation between the filled truncations. -/
theorem doubleCutoff_filled_sylvester_equation
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E}
    (hEq : HasClosedSylvesterEquation A B X C)
    (a b τA τB : ℝ) :
    filledSpectralTruncation A hA a τA ∘L
        (spectralCutoff A hA τA ∘L X ∘L spectralCutoff B hB τB) -
      (spectralCutoff A hA τA ∘L X ∘L spectralCutoff B hB τB) ∘L
        filledSpectralTruncation B hB b τB =
      spectralCutoff A hA τA ∘L C ∘L spectralCutoff B hB τB := by
  let PA : E →L[𝕜] E := spectralCutoff A hA τA
  let PB : F →L[𝕜] F := spectralCutoff B hB τB
  let TA : E →L[𝕜] E := boundedSpectralTruncation A hA τA
  let TB : F →L[𝕜] F := boundedSpectralTruncation B hB τB
  have hPAidem := (spectralCutoff_isOrthogonalProjection A hA τA).1
  have hPBidem := (spectralCutoff_isOrthogonalProjection B hB τB).1
  have hTAcomm := boundedSpectralTruncation_commutes_cutoff A hA τA
  have hTBcomm := boundedSpectralTruncation_commutes_cutoff B hB τB
  ext x
  have hPBdom : PB x ∈ B.domain :=
    spectralCutoff_range_le_domain B hB τB ⟨x, rfl⟩
  have hXdom : X (PB x) ∈ A.domain :=
    hEq.mapsTo_domain ⟨PB x, hPBdom⟩
  obtain ⟨hPAxdom, hAcomm⟩ :=
    spectralCutoff_commutes_on_domain A hA τA ⟨X (PB x), hXdom⟩
  obtain ⟨_hPAcutdom, hTAcut⟩ :=
    boundedSpectralTruncation_eq_on_cutoff A hA τA (X (PB x))
  obtain ⟨_hPBcutdom, hTBcut⟩ :=
    boundedSpectralTruncation_eq_on_cutoff B hB τB x
  have hPAPAx : PA (PA (X (PB x))) = PA (X (PB x)) := by
    have h := congrArg (fun S : E →L[𝕜] E => S (X (PB x))) hPAidem
    simpa only [PA, ContinuousLinearMap.comp_apply] using h
  have hPBPBx : PB (PB x) = PB x := by
    have h := congrArg (fun S : F →L[𝕜] F => S x) hPBidem
    simpa only [PB, ContinuousLinearMap.comp_apply] using h
  have hTAPA : TA (PA (X (PB x))) = TA (X (PB x)) := by
    have h := congrArg (fun S : E →L[𝕜] E => S (X (PB x))) hTAcomm.1
    simpa only [TA, PA, ContinuousLinearMap.comp_apply] using h
  have hPBTB : PB (TB x) = TB x := by
    have h := congrArg (fun S : F →L[𝕜] F => S x) hTBcomm.2
    simpa only [PB, TB, ContinuousLinearMap.comp_apply] using h
  have hPBFilled :
      PB (filledSpectralTruncation B hB b τB x) = TB x := by
    change PB (TB x + ((b : ℝ) : 𝕜) • (x - PB x)) = TB x
    rw [map_add, map_smul, hPBTB, map_sub, hPBPBx, sub_self, smul_zero,
      add_zero]
  have hAFilled :
      filledSpectralTruncation A hA a τA (PA (X (PB x))) =
        PA (A.toLinearMap ⟨X (PB x), hXdom⟩) := by
    change TA (PA (X (PB x))) +
        ((a : ℝ) : 𝕜) • (PA (X (PB x)) - PA (PA (X (PB x)))) =
      PA (A.toLinearMap ⟨X (PB x), hXdom⟩)
    rw [hTAPA, hPAPAx, sub_self, smul_zero, add_zero]
    rw [hTAcut]
    exact hAcomm
  have heq := hEq.equation ⟨PB x, hPBdom⟩
  have heqPA := congrArg PA heq
  change
    filledSpectralTruncation A hA a τA (PA (X (PB x))) -
      PA (X (PB (filledSpectralTruncation B hB b τB x))) =
        PA (C (PB x))
  rw [hAFilled, hPBFilled]
  rw [show TB x = B.toLinearMap ⟨PB x, hPBdom⟩ by
    simpa only [TB, PB] using hTBcut]
  simpa only [map_sub] using heqPA

/-- Pointwise cutoff estimates for every finite Ky Fan gauge imply the full
family of Ky Fan inequalities used by Fan dominance. -/
theorem all_kyFanApproximationGauge_le_of_spectralCutoff_le
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {δ : ℝ}
    (hcut : ∀ τ : ℝ, 0 ≤ τ → ∀ k : ℕ,
      δ * kyFanApproximationGauge k
          (X ∘L spectralCutoff B hB τ) ≤
        kyFanApproximationGauge k
          (C ∘L spectralCutoff B hB τ)) :
    ∀ k, δ * kyFanApproximationGauge k X ≤
      kyFanApproximationGauge k C := by
  intro k
  exact kyFanApproximationGauge_le_of_spectralCutoff_le hB k
    (fun τ hτ => hcut τ hτ k)

/-- Ky Fan estimate obtained from bounded spectral truncations. -/
theorem kyFan_unbounded_sylvester_le_of_semibounded
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : SemiboundedBelow A (c + δ))
    (hBc : SemiboundedAbove B c)
    (hEq : HasClosedSylvesterEquation A B X C) :
    ∀ k, δ * kyFanApproximationGauge k X
      ≤ kyFanApproximationGauge k C := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [kyFanApproximationGauge]
  have hk : 0 < k := Nat.pos_of_ne_zero hk0
  apply kyFanApproximationGauge_le_of_leftSpectralCutoff_le hA k
  intro τA hτA
  apply kyFanApproximationGauge_le_of_spectralCutoff_le hB k
  intro τB hτB
  let PA : E →L[𝕜] E := spectralCutoff A hA τA
  let PB : F →L[𝕜] F := spectralCutoff B hB τB
  let AF : E →L[𝕜] E := filledSpectralTruncation A hA (c + δ) τA
  let BF : F →L[𝕜] F := filledSpectralTruncation B hB c τB
  let Xc : F →L[𝕜] E := PA ∘L X ∘L PB
  let Cc : F →L[𝕜] E := PA ∘L C ∘L PB
  have hAFsym : AF.IsSymmetric :=
    filledSpectralTruncation_isSymmetric A hA (c + δ) τA
  have hBFsym : BF.IsSymmetric :=
    filledSpectralTruncation_isSymmetric B hB c τB
  have hAFlower : ∀ x, (c + δ) * ‖x‖ ^ 2 ≤
      RCLike.re ⟪AF x, x⟫_𝕜 :=
    filledSpectralTruncation_lowerBound A hA hτA hAc
  have hBFupper : ∀ x, RCLike.re ⟪BF x, x⟫_𝕜 ≤
      c * ‖x‖ ^ 2 :=
    filledSpectralTruncation_upperBound B hB hτB hBc
  have hEqCut : AF ∘L Xc - Xc ∘L BF = Cc := by
    simpa only [AF, BF, Xc, Cc] using
      doubleCutoff_filled_sylvester_equation hA hB hEq
        (c + δ) c τA τB
  let B0 : F →L[𝕜] F :=
    BF - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 F
  let ρ : ℝ := ‖B0‖
  let m : ℝ := c - ρ
  let A1 : E →L[𝕜] E :=
    AF - ((m : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E
  let B1 : F →L[𝕜] F :=
    BF - ((m : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 F
  have hρ : 0 ≤ ρ := norm_nonneg B0
  have hB0sym : B0.IsSymmetric := by
    exact hBFsym.sub (LinearMap.IsSymmetric.smul
      (RCLike.conj_ofReal c) LinearMap.IsSymmetric.id)
  have hB0nonpos : ∀ x, RCLike.re ⟪B0 x, x⟫_𝕜 ≤ 0 := by
    intro x
    have h := hBFupper x
    simp only [B0, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
      inner_sub_left, map_sub, inner_smul_left, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    linarith
  have hB1eq : B1 = B0 + ((ρ : ℝ) : 𝕜) •
      ContinuousLinearMap.id 𝕜 F := by
    ext x
    simp only [B1, B0, m, sub_apply, add_apply, smul_apply,
      ContinuousLinearMap.id_apply]
    module
  have hB1norm : ‖B1‖ ≤ ρ := by
    rw [hB1eq]
    exact norm_add_opNorm_id_le_of_nonpos hB0sym hB0nonpos
  have hA1coer : ∀ x, (ρ + δ) * ‖x‖ ^ 2 ≤
      RCLike.re ⟪A1 x, x⟫_𝕜 := by
    intro x
    have h := hAFlower x
    have hshift : RCLike.re ⟪A1 x, x⟫_𝕜 =
        RCLike.re ⟪AF x, x⟫_𝕜 - m * ‖x‖ ^ 2 := by
      simp only [A1, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
        inner_sub_left, inner_smul_left, RCLike.conj_ofReal, map_sub,
        RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    rw [hshift]
    dsimp [m]
    linarith
  have hρδ : 0 < ρ + δ := by linarith
  obtain ⟨hA1inv, hA1invNorm⟩ :=
    boundedInverseData_of_coercive hρδ hA1coer
  have hEqShift : A1 ∘L Xc - Xc ∘L B1 = Cc := by
    ext x
    have hraw := congrArg (fun T : F →L[𝕜] E => T x) hEqCut
    simp only [A1, B1, ContinuousLinearMap.comp_apply, sub_apply,
      smul_apply, ContinuousLinearMap.id_apply, map_sub, map_smul] at hraw ⊢
    calc
      AF (Xc x) - ((m : ℝ) : 𝕜) • Xc x -
          (Xc (BF x) - ((m : ℝ) : 𝕜) • Xc x) =
        AF (Xc x) - Xc (BF x) := by module
      _ = Cc x := hraw
  have hmain := sylvester_mem_and_gauge_le_of_bound_inverse
    (KyFanDominantIdealFamily.kyFan (𝕜 := 𝕜) k hk).toRectangularSymmetricIdealFamily
    hA1inv B1 hρ hδ hA1invNorm hB1norm hEqShift
      (KyFanDominantIdealFamily.kyFan_mem (𝕜 := 𝕜) k hk Cc)
  rw [KyFanDominantIdealFamily.kyFan_gauge (𝕜 := 𝕜) k hk Xc,
    KyFanDominantIdealFamily.kyFan_gauge (𝕜 := 𝕜) k hk Cc] at hmain
  simpa only [Xc, Cc, PA, PB, ContinuousLinearMap.comp_assoc] using hmain.2

/-- The opposite ordered orientation, obtained by adjointing and swapping the
two closed blocks. -/
theorem kyFan_unbounded_sylvester_le_of_semibounded_swapped
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : SemiboundedAbove A c)
    (hBc : SemiboundedBelow B (c + δ))
    (hEq : HasClosedSylvesterEquation A B X C) :
    ∀ k, δ * kyFanApproximationGauge k X
      ≤ kyFanApproximationGauge k C := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [kyFanApproximationGauge]
  have hk : 0 < k := Nat.pos_of_ne_zero hk0
  apply kyFanApproximationGauge_le_of_leftSpectralCutoff_le hA k
  intro τA hτA
  apply kyFanApproximationGauge_le_of_spectralCutoff_le hB k
  intro τB hτB
  let PA : E →L[𝕜] E := spectralCutoff A hA τA
  let PB : F →L[𝕜] F := spectralCutoff B hB τB
  let AF : E →L[𝕜] E := filledSpectralTruncation A hA c τA
  let BF : F →L[𝕜] F := filledSpectralTruncation B hB (c + δ) τB
  let Xc : F →L[𝕜] E := PA ∘L X ∘L PB
  let Cc : F →L[𝕜] E := PA ∘L C ∘L PB
  have hAFsym : AF.IsSymmetric :=
    filledSpectralTruncation_isSymmetric A hA c τA
  have hBFsym : BF.IsSymmetric :=
    filledSpectralTruncation_isSymmetric B hB (c + δ) τB
  have hAFupper : ∀ x, RCLike.re ⟪AF x, x⟫_𝕜 ≤
      c * ‖x‖ ^ 2 :=
    filledSpectralTruncation_upperBound A hA hτA hAc
  have hBFlower : ∀ x, (c + δ) * ‖x‖ ^ 2 ≤
      RCLike.re ⟪BF x, x⟫_𝕜 :=
    filledSpectralTruncation_lowerBound B hB hτB hBc
  have hEqCut : AF ∘L Xc - Xc ∘L BF = Cc := by
    simpa only [AF, BF, Xc, Cc] using
      doubleCutoff_filled_sylvester_equation hA hB hEq
        c (c + δ) τA τB
  let A0 : E →L[𝕜] E :=
    AF - ((c : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E
  let ρ : ℝ := ‖A0‖
  let m : ℝ := c - ρ
  let A1 : E →L[𝕜] E :=
    AF - ((m : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E
  let B1 : F →L[𝕜] F :=
    BF - ((m : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 F
  have hρ : 0 ≤ ρ := norm_nonneg A0
  have hA0sym : A0.IsSymmetric := by
    exact hAFsym.sub (LinearMap.IsSymmetric.smul
      (RCLike.conj_ofReal c) LinearMap.IsSymmetric.id)
  have hA0nonpos : ∀ x, RCLike.re ⟪A0 x, x⟫_𝕜 ≤ 0 := by
    intro x
    have h := hAFupper x
    simp only [A0, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
      inner_sub_left, map_sub, inner_smul_left, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    linarith
  have hA1eq : A1 = A0 + ((ρ : ℝ) : 𝕜) •
      ContinuousLinearMap.id 𝕜 E := by
    ext x
    simp only [A1, A0, m, sub_apply, add_apply, smul_apply,
      ContinuousLinearMap.id_apply]
    module
  have hA1norm : ‖A1‖ ≤ ρ := by
    rw [hA1eq]
    exact norm_add_opNorm_id_le_of_nonpos hA0sym hA0nonpos
  have hB1coer : ∀ x, (ρ + δ) * ‖x‖ ^ 2 ≤
      RCLike.re ⟪B1 x, x⟫_𝕜 := by
    intro x
    have h := hBFlower x
    have hshift : RCLike.re ⟪B1 x, x⟫_𝕜 =
        RCLike.re ⟪BF x, x⟫_𝕜 - m * ‖x‖ ^ 2 := by
      simp only [B1, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
        inner_sub_left, inner_smul_left, RCLike.conj_ofReal, map_sub,
        RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    rw [hshift]
    dsimp [m]
    linarith
  have hρδ : 0 < ρ + δ := by linarith
  obtain ⟨hB1inv, hB1invNorm⟩ :=
    boundedInverseData_of_coercive hρδ hB1coer
  have hEqShift : A1 ∘L Xc - Xc ∘L B1 = Cc := by
    ext x
    have hraw := congrArg (fun T : F →L[𝕜] E => T x) hEqCut
    simp only [A1, B1, ContinuousLinearMap.comp_apply, sub_apply,
      smul_apply, ContinuousLinearMap.id_apply, map_sub, map_smul] at hraw ⊢
    calc
      AF (Xc x) - ((m : ℝ) : 𝕜) • Xc x -
          (Xc (BF x) - ((m : ℝ) : 𝕜) • Xc x) =
        AF (Xc x) - Xc (BF x) := by module
      _ = Cc x := hraw
  have hmain := sylvester_mem_and_gauge_le_of_bound_inverse_swapped
    (KyFanDominantIdealFamily.kyFan (𝕜 := 𝕜) k hk).toRectangularSymmetricIdealFamily
    hB1inv A1 hρ hδ hB1invNorm hA1norm hEqShift
      (KyFanDominantIdealFamily.kyFan_mem (𝕜 := 𝕜) k hk Cc)
  rw [KyFanDominantIdealFamily.kyFan_gauge (𝕜 := 𝕜) k hk Xc,
    KyFanDominantIdealFamily.kyFan_gauge (𝕜 := 𝕜) k hk Cc] at hmain
  simpa only [Xc, Cc, PA, PB, ContinuousLinearMap.comp_assoc] using hmain.2

/-- Ideal membership of the Sylvester solution from ordered cutoff estimates. -/
theorem unbounded_sylvester_mem_of_semibounded_viaKyFan
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : SemiboundedBelow A (c + δ))
    (hBc : SemiboundedAbove B c)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.toRectangularSymmetricIdealFamily.Mem C) :
    N.toRectangularSymmetricIdealFamily.Mem X := by
  exact (mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    N hδ hC
      (kyFan_unbounded_sylvester_le_of_semibounded
        hA hB hδ hAc hBc hEq)).1

/-- Davis--Kahan Theorem 5.2 in the lower-left/upper-right orientation. -/
theorem unbounded_sylvester_mem_and_gauge_le_viaKyFan
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : SemiboundedBelow A (c + δ))
    (hBc : SemiboundedAbove B c)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.toRectangularSymmetricIdealFamily.Mem C) :
    N.toRectangularSymmetricIdealFamily.Mem X ∧ δ * N.toRectangularSymmetricIdealFamily.gauge X ≤ N.toRectangularSymmetricIdealFamily.gauge C := by
  exact mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    N hδ hC
      (kyFan_unbounded_sylvester_le_of_semibounded
        hA hB hδ hAc hBc hEq)

/-- Davis--Kahan Theorem 5.2 in the upper-left/lower-right orientation. -/
theorem unbounded_sylvester_mem_and_gauge_le_swapped_viaKyFan
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : SemiboundedAbove A c)
    (hBc : SemiboundedBelow B (c + δ))
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.toRectangularSymmetricIdealFamily.Mem C) :
    N.toRectangularSymmetricIdealFamily.Mem X ∧ δ * N.toRectangularSymmetricIdealFamily.gauge X ≤ N.toRectangularSymmetricIdealFamily.gauge C := by
  exact mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    N hδ hC
      (kyFan_unbounded_sylvester_le_of_semibounded_swapped
        hA hB hδ hAc hBc hEq)

/-- Exact interval/exterior form with one bounded spectral block and one
possibly unbounded exterior block.  This theorem only needs the ordinary
rectangular ideal interface. -/
theorem unbounded_sylvester_mem_and_gauge_le_of_intervalExteriorGap
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {β α δ : ℝ}
    (hβα : β ≤ α) (hδ : 0 < δ)
    (hgap : UnboundedIntervalExteriorGap A B β α δ)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge C := by
  let c : ℝ := (β + α) / 2
  let ρ : ℝ := (α - β) / 2
  let c𝕜 : 𝕜 := (c : 𝕜)
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    linarith
  rcases hgap with hgap | hgap
  · -- The interval block is on the left and the exterior block is on the right.
    obtain ⟨R, hRnorm⟩ :=
      boundedRealization_of_spectrumIn_Icc A hA hβα hgap.1
    obtain ⟨hBinv, hBinvNorm⟩ :=
      boundedInverse_of_spectrumOutside B hB hβα hδ hgap.2
    let S : E →L[𝕜] E :=
      R.operator - c𝕜 • ContinuousLinearMap.id 𝕜 E
    have hSnorm : ‖S‖ ≤ ρ := by
      simpa only [S, c𝕜, c, ρ] using hRnorm
    have hdom : ∀ z : F, hBinv.inv z ∈ B.domain := by
      intro z
      exact hBinv.inv_mapsTo_domain z
    have hres : ∀ z : F,
        B.toLinearMap ⟨hBinv.inv z, hdom z⟩ - c𝕜 • hBinv.inv z = z := by
      intro z
      have hz := hBinv.apply_inv z
      change B.toLinearMap ⟨hBinv.inv z, hdom z⟩ +
          (-(c𝕜 • ContinuousLinearMap.id 𝕜 F)) (hBinv.inv z) = z at hz
      simpa [sub_eq_add_neg] using hz
    have hEq' : ∀ y : B.domain,
        S (X (y : F)) -
          (X (B.toLinearMap y) - c𝕜 • X (y : F)) = C (y : F) := by
      intro y
      have heq := hEq.equation y
      have hagree := R.agrees ⟨X (y : F), hEq.mapsTo_domain y⟩
      simp only [S, sub_apply, smul_apply, ContinuousLinearMap.id_apply]
      rw [hagree, ← heq]
      abel
    exact mem_and_gauge_le_of_boundedLeft_exteriorRight
      N hρ hδ hSnorm hdom hres hBinvNorm hEq' hC
  · -- The exterior block is on the left and the interval block is on the right.
    obtain ⟨R, hRnorm⟩ :=
      boundedRealization_of_spectrumIn_Icc B hB hβα hgap.1
    obtain ⟨hAinv, hAinvNorm⟩ :=
      boundedInverse_of_spectrumOutside A hA hβα hδ hgap.2
    let T : F →L[𝕜] F := R.operator
    let S : F →L[𝕜] F :=
      T - c𝕜 • ContinuousLinearMap.id 𝕜 F
    have hSnorm : ‖S‖ ≤ ρ := by
      simpa only [S, T, c𝕜, c, ρ] using hRnorm
    have hEqT : HasUnboundedBoundedSylvesterEquation A T X C := by
      exact closedSylvesterEquation_boundedRealization hEq R.agrees
    let A' : ClosedOperatorOnE (𝕜 := 𝕜) (E := E) :=
      A.addBounded (-(c𝕜 • ContinuousLinearMap.id 𝕜 E))
    have hA'apply : ∀ x : A.domain,
        A'.toLinearMap x = A.toLinearMap x - c𝕜 • (x : E) := by
      intro x
      change A.toLinearMap x +
          (-(c𝕜 • ContinuousLinearMap.id 𝕜 E)) (x : E) =
        A.toLinearMap x - c𝕜 • (x : E)
      simp [sub_eq_add_neg]
    have hEq' : HasUnboundedBoundedSylvesterEquation A' S X C := by
      refine ⟨fun x => hEqT.mapsTo_domain x, fun x => ?_⟩
      have h1 := hEqT.equation x
      have h2 : A'.toLinearMap
          ⟨X (x : F), hEqT.mapsTo_domain x⟩ =
          A.toLinearMap ⟨X (x : F), hEqT.mapsTo_domain x⟩ -
            c𝕜 • X (x : F) :=
        hA'apply ⟨X (x : F), hEqT.mapsTo_domain x⟩
      have h3 : X (S (x : F)) = X (T (x : F)) - c𝕜 • X (x : F) := by
        simp only [S, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
          map_sub, map_smul]
      change A'.toLinearMap ⟨X (x : F), hEqT.mapsTo_domain x⟩ -
        X (S (x : F)) = C (x : F)
      rw [h2, h3, ← h1]
      abel
    exact sylvester_mem_and_gauge_le_of_unbounded_bound_inverse
      N hAinv S hρ hδ hAinvNorm hSnorm hEq' hC

/-- All source-faithful unbounded gap configurations needed by the `sin Θ`
endpoint.  The ordered constructors allow both diagonal blocks to be genuinely
unbounded; the interval/exterior constructor has a bounded spectral block. -/
inductive UnboundedSylvesterGap
    (A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E))
    (B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F))
    (δ : ℝ) : Prop where
  | intervalExterior
      {β α : ℝ}
      (hβα : β ≤ α)
      (hgap : UnboundedIntervalExteriorGap A B β α δ)
  | leftAboveRightBelow
      (c : ℝ)
      (hA : SemiboundedBelow A (c + δ))
      (hB : SemiboundedAbove B c)
  | leftBelowRightAbove
      (c : ℝ)
      (hA : SemiboundedAbove A c)
      (hB : SemiboundedBelow B (c + δ))

/-- Complete unified unbounded Sylvester estimate.  The finite-interval branch
uses the one-unbounded theorem; the two ordered branches use the paper's
spectral-cutoff and finite-Ky-Fan argument.  The stronger family is the precise
abstraction needed for this passage and is not derived from ordinary ideal
laws. -/
theorem unbounded_sylvester_mem_and_gauge_le_of_gap
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : UnboundedSylvesterGap A B δ)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.toRectangularSymmetricIdealFamily.Mem C) :
    N.toRectangularSymmetricIdealFamily.Mem X ∧
      δ * N.toRectangularSymmetricIdealFamily.gauge X ≤
        N.toRectangularSymmetricIdealFamily.gauge C := by
  cases hgap with
  | intervalExterior hβα hgap =>
      exact unbounded_sylvester_mem_and_gauge_le_of_intervalExteriorGap
        N.toRectangularSymmetricIdealFamily hA hB hβα hδ hgap hEq hC
  | leftAboveRightBelow c hAc hBc =>
      exact unbounded_sylvester_mem_and_gauge_le_viaKyFan
        N hA hB hδ hAc hBc hEq hC
  | leftBelowRightAbove c hAc hBc =>
      exact unbounded_sylvester_mem_and_gauge_le_swapped_viaKyFan
        N hA hB hδ hAc hBc hEq hC

/-- Canonical source-facing Section 5 engine consumed by the general sine
 theorem.  The scoped name emphasizes that bounded Sylvester estimates are
 specializations or independent alternatives rather than the root theorem. -/
theorem davisKahan1970_sylvester
    (N : UnitaryInvariantIdealFamily (𝕜 := 𝕜))
    {A : ClosedOperatorOnE (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperatorOnF (𝕜 := 𝕜) (F := F)}
    (hA : A.IsSelfAdjoint) (hB : B.IsSelfAdjoint)
    {X C : F →L[𝕜] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : UnboundedSylvesterGap A B δ)
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.toRectangularSymmetricIdealFamily.Mem C) :
    N.toRectangularSymmetricIdealFamily.Mem X ∧
      δ * N.toRectangularSymmetricIdealFamily.gauge X ≤
        N.toRectangularSymmetricIdealFamily.gauge C :=
  unbounded_sylvester_mem_and_gauge_le_of_gap N hA hB hδ hgap hEq hC

end ApproximationNumberEndpointAssumptions

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
